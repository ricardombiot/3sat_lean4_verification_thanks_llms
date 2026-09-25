-- lean/improves_bin/AbsSatBin/GraphPath/Model/AggressiveReview.lean
import AbsSatBin.GraphPath.Model.AddNode

/-!
# The aggressive consistency review (Julia `agressive_consistence_filter!`)

The base review looks at one node at a time: its coverage, and the union of its neighbours' owner
tables. It never asks whether two owners of a node can lie on a path **together**. On the Tseitin
formula over the Petersen graph (report v114) that is exactly what goes wrong: three pins are
compatible two by two and not all three, and the base review leaves a valid state with no chain.

The author's filter (`graph_path_filter.jl`, 14-sept-2026) checks every owner pair:

* for each step from `current_step - 2` down to `1`, and each node `x` of that step,
* for each owner `w` of `x` at those same steps that is still a valid node,
* if at some step `w` has owners and none of them is an owner of `x`, then no path contains both:
  `w` stops owning `x` and `x` stops owning `w`,
* and `x` is removed if it is no longer a valid node.

Changes are seen immediately by the checks that follow, as in the Julia loop. This module mirrors
it on `GPathM` and places it **inside the review**: the base review runs to its fixpoint, then one
aggressive sweep, and again while the sweep removes anything (`reviewAgg`).

Proved, which is what a review has to earn to join the conservation law:

* `pruned_reviewAgg` — it only removes (a `Pruned` narrowing);
* `ChainSound_reviewAgg` — **it loses no solution**: two nodes of one sound chain share, at every
  step, the chain's own node, so the sweep never separates them, and chain nodes stay valid.

`ReviewOk R` names those two facts for any review `R`, with instances for the base `review` and for
`reviewAgg`; `filterAllR` / `upFilteringR` are the machine's filter and `up` over such a review. The
conservation law of `ConservationFilter` is stated for them, so the machine with the aggressive
review inherits it.
-/

namespace AbsSatBin.GraphPath.Model.AggressiveReview

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM

-- ============================================================
-- The sweep
-- ============================================================

/-- Julia `intersect!` followed by `is_valid`, for two valid nodes: at every step where `w` has
owners, some owner of `x` at that step is also an owner of `w`. -/
def sharesEveryStep (cs : Int) (xo wo : List PathNodeId) : Bool :=
  (intRange 0 (cs - 1)).all (fun k => !hasStepEntry wo k || (ownersAt xo k).any (fun r => wo.contains r))

/-- An owner list with `w` removed, as an intersection list: every other owner is in it, and a
sentinel at `w`'s step makes `intersectOwners` drop `w` itself. -/
def dropList (os : List PathNodeId) (w : PathNodeId) : List PathNodeId :=
  os.filter (fun q => q != w) ++ [{ id := { step := w.id.step, index := w.id.index + 1 }, parent_id := w.parent_id }]

/-- `w` stops owning `x` and `x` stops owning `w`. -/
def dropOwnerPair (g : GPathM) (x w : PathNodeId) (xo wo : List PathNodeId) : GPathM :=
  updateAt (updateAt g x (uniMap (dropList xo w))) w (uniMap (dropList wo x))

/-- One owner pair of `x`, checked against the tables as they stand (Julia, 14-sept-2026):

* **asymmetric** (`symmetric_entry`): `w` is a valid owner of `x` but `x` is not an owner of `w` —
  `w` stops owning `x`, in that direction only;
* **inconsistent**: the entry is symmetric but the two tables share nothing at some step — both
  directions go.

The sweep only calls it with `w` among `x`'s current owners; the `contains` tests make that explicit,
so that a pair that fires always removes something (`AggFixpoint.aggPair_eqOrLt`). -/
def aggPair (g : GPathM) (x w : PathNodeId) : GPathM :=
  match g.node? x, g.node? w with
  | some nx, some nw =>
    if nx.owners.contains w && isValidNode g nw && !nw.owners.contains x then
      updateAt g x (uniMap (dropList nx.owners w))
    else if nx.owners.contains w && isValidNode g nw && !sharesEveryStep g.current_step nx.owners nw.owners then
      dropOwnerPair g x w nx.owners nw.owners
    else g
  | _, _ => g

/-- The owners of `x` at step `kw`, read from the current state. -/
def ownersAtNow (g : GPathM) (x : PathNodeId) (kw : Int) : List PathNodeId :=
  ownersAt (ownersOf g x) kw

/-- One node: every owner pair at steps `current_step - 1 … 0`, then remove `x` if invalid. -/
def aggNode (g : GPathM) (x : PathNodeId) : GPathM :=
  match g.node? x with
  | none => g
  | some nx =>
    let g₁ :=
      if isValidNode g nx then
        (intRange 0 (g.current_step - 1)).reverse.foldl
          (fun g kw => (ownersAtNow g x kw).foldl (fun g w => aggPair g x w) g) g
      else g
    match g₁.node? x with
    | none => g₁
    | some n₁ => if isValidNode g₁ n₁ then g₁ else removeNode g₁ x

/-- **The sweep** (`agressive_consistence_filter!`): every step, `current_step - 1 … 0`, the nodes of
each step in order, each against the state left by the previous ones. -/
def aggSweep (g : GPathM) : GPathM :=
  if isValid g then
    (intRange 0 (g.current_step - 1)).reverse.foldl
      (fun g k => ((g.line k).map (·.id)).foldl aggNode g) g
  else g

/-- **The review with the aggressive sweep**: base review to its fixpoint, one sweep, and again while
the sweep removes something.

When the sweep removes nothing the result is the base review's own fixpoint `g₁` (the sweep's output
has the same measure, so nothing was taken out). Returning `g₁` rather than the sweep's output makes
**every result of `reviewAgg` a result of `review`** (`reviewAggFuel_form`), so everything proved
about review fixpoints applies to it unchanged. -/
def reviewAggFuel : Nat → GPathM → GPathM
  | 0, g => review g
  | fuel + 1, g =>
    let g₁ := review g
    if isValid g₁ then
      let g₂ := aggSweep g₁
      if measure g₂ < measure g₁ then reviewAggFuel fuel g₂ else g₁
    else g₁

def reviewAgg (g : GPathM) : GPathM := reviewAggFuel (measure g + 1) g

/-- Pins, then the aggressive review. -/
def filterAllAgg (g : GPathM) (reqs : List NodeId) : GPathM :=
  reviewAgg (reqs.foldl filterRequire g)

-- ============================================================
-- It only removes
-- ============================================================

private theorem pruned_foldl' {β : Type} (f : GPathM → β → GPathM) (h : ∀ g b, Pruned g (f g b)) :
    ∀ (l : List β) (g : GPathM), Pruned g (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g; exact Pruned.refl g
  | cons b rest ih => intro g; exact Pruned.trans (h g b) (ih (f g b))

theorem pruned_updateAt_uniMap (g : GPathM) (id : PathNodeId) (B : List PathNodeId) :
    Pruned g (updateAt g id (uniMap B)) :=
  pruned_updateAt g id (uniMap B) (uniMap_id B)
    (fun _ _ hq => (List.mem_filter.mp hq).1) (fun _ _ hp => hp)

theorem pruned_aggPair (g : GPathM) (x w : PathNodeId) : Pruned g (aggPair g x w) := by
  unfold aggPair
  split
  · split
    · exact pruned_updateAt_uniMap _ _ _
    · split
      · exact Pruned.trans (pruned_updateAt_uniMap _ _ _) (pruned_updateAt_uniMap _ _ _)
      · exact Pruned.refl g
  · exact Pruned.refl g

theorem pruned_aggNode (g : GPathM) (x : PathNodeId) : Pruned g (aggNode g x) := by
  unfold aggNode
  split
  · exact Pruned.refl g
  · have h₁ : ∀ g₁ : GPathM, Pruned g g₁ → Pruned g
        (match g₁.node? x with
          | none => g₁
          | some n₁ => if isValidNode g₁ n₁ then g₁ else removeNode g₁ x) := by
      intro g₁ hg₁
      split
      · exact hg₁
      · split
        · exact hg₁
        · exact Pruned.trans hg₁ (pruned_removeNode _ _)
    apply h₁
    split
    · exact pruned_foldl' _ (fun g kw => pruned_foldl' _ (fun g w => pruned_aggPair g x w) _ g) _ g
    · exact Pruned.refl g

theorem pruned_aggSweep (g : GPathM) : Pruned g (aggSweep g) := by
  unfold aggSweep
  split
  · exact pruned_foldl' _ (fun g k => pruned_foldl' _ pruned_aggNode _ g) _ g
  · exact Pruned.refl g

theorem pruned_reviewAggFuel : ∀ (fuel : Nat) (g : GPathM), Pruned g (reviewAggFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact pruned_review g
  | succ n ih =>
    intro g
    simp only [reviewAggFuel]
    split
    · split
      · exact Pruned.trans (pruned_review g) (Pruned.trans (pruned_aggSweep _) (ih _))
      · exact pruned_review g
    · exact pruned_review g

theorem pruned_reviewAgg (g : GPathM) : Pruned g (reviewAgg g) := pruned_reviewAggFuel _ g

theorem pruned_filterAllAgg (g : GPathM) (reqs : List NodeId) : Pruned g (filterAllAgg g reqs) :=
  Pruned.trans (pruned_foldl filterRequire pruned_filterRequire reqs g) (pruned_reviewAgg _)

-- ============================================================
-- It loses no solution
-- ============================================================

private theorem chain_foldl {β : Type} (f : GPathM → β → GPathM) (sel : Int → PathNodeId)
    (h : ∀ g b, ChainSound g sel → ChainSound (f g b) sel) :
    ∀ (l : List β) (g : GPathM), ChainSound g sel → ChainSound (l.foldl f g) sel := by
  intro l
  induction l with
  | nil => intro g hg; exact hg
  | cons b rest ih => intro g hg; exact ih (f g b) (h g b hg)

/-- A chain node's table contains every node of the chain. -/
theorem chain_mem_owners (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (j : Int) (hj0 : 0 ≤ j) (hj : j < g.current_step) (n : PNodeM) (hn : g.node? (sel j) = some n)
    (i : Int) (hi0 : 0 ≤ i) (hi : i < g.current_step) : sel i ∈ n.owners := by
  rcases int_eq_or_ne i j with hij | hij
  · subst hij
    have hs := h.self_owned i hi0 hi
    simp only [ownersOf, hn] at hs
    exact hs
  · have ho := h.chain.2.1 i j hi0 hj0 hi hj hij
    simp only [ownersOf, hn, ownersAt, List.mem_filter] at ho
    exact ho.1

/-- **Two nodes of one chain always share every step.** -/
theorem sharesEveryStep_of_chain (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (i j : Int) (hi0 : 0 ≤ i) (hi : i < g.current_step) (hj0 : 0 ≤ j) (hj : j < g.current_step)
    (nx nw : PNodeM) (hx : g.node? (sel i) = some nx) (hw : g.node? (sel j) = some nw) :
    sharesEveryStep g.current_step nx.owners nw.owners = true := by
  unfold sharesEveryStep
  rw [List.all_eq_true]
  intro k hk
  have hk0 := mem_intRange_lower hk
  have hk1 := mem_intRange_upper hk
  have hkx := chain_mem_owners g sel h i hi0 hi nx hx k hk0 (by omega)
  have hkw := chain_mem_owners g sel h j hj0 hj nw hw k hk0 (by omega)
  have hstep := (h.chain.1.1 k hk0 (by omega)).2
  have hany : (ownersAt nx.owners k).any (fun r => nw.owners.contains r) = true :=
    List.any_eq_true.mpr ⟨sel k, List.mem_filter.mpr ⟨hkx, beq_iff_eq.mpr hstep⟩,
      List.elem_eq_true_of_mem hkw⟩
  rw [hany, Bool.or_true]

theorem mem_dropList (os : List PathNodeId) (w q : PathNodeId) (hq : q ∈ os) (hne : q ≠ w) :
    q ∈ dropList os w :=
  List.mem_append_left _ (List.mem_filter.mpr ⟨hq, bne_iff_ne.mpr hne⟩)

theorem ChainSound_aggPair (g : GPathM) (x w : PathNodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (aggPair g x w) sel := by
  unfold aggPair
  split
  · next nx nw hx hw =>
    split
    · next hasym =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hasym
      -- `x` and `w` are not both on the chain: chain nodes own each other
      refine ChainSound_updateAt_gen g x _ sel h ?_
      intro j hj0 hj hjx i hi0 hi
      have hnx : g.node? (sel j) = some nx := by rw [hjx]; exact hx
      refine mem_dropList _ w _ (chain_mem_owners g sel h j hj0 hj nx hnx i hi0 hi) ?_
      intro hiw
      have hw' : g.node? (sel i) = some nw := by rw [hiw]; exact hw
      have hmem := chain_mem_owners g sel h i hi0 hi nw hw' j hj0 hj
      rw [hjx] at hmem
      have hc : nw.owners.contains x = true := List.elem_eq_true_of_mem hmem
      rw [hasym.2] at hc
      exact Bool.noConfusion hc
    split
    · next hcond =>
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      -- `x` and `w` are not both on the chain
      have hnot : ∀ i j, 0 ≤ i → i < g.current_step → 0 ≤ j → j < g.current_step →
          sel i = x → sel j = w → False := by
        intro i j hi0 hi hj0 hj hix hjw
        have hx' : g.node? (sel i) = some nx := by rw [hix]; exact hx
        have hw' : g.node? (sel j) = some nw := by rw [hjw]; exact hw
        have := sharesEveryStep_of_chain g sel h i j hi0 hi hj0 hj nx nw hx' hw'
        rw [hcond.2] at this
        exact Bool.noConfusion this
      have h₁ : ChainSound (updateAt g x (uniMap (dropList nx.owners w))) sel := by
        refine ChainSound_updateAt_gen g x _ sel h ?_
        intro j hj0 hj hjx i hi0 hi
        have hnx : g.node? (sel j) = some nx := by rw [hjx]; exact hx
        refine mem_dropList _ w _ (chain_mem_owners g sel h j hj0 hj nx hnx i hi0 hi) ?_
        intro hiw
        exact hnot j i hj0 hj hi0 hi hjx hiw
      refine ChainSound_updateAt_gen _ w _ sel h₁ ?_
      intro j hj0 hj hjw i hi0 hi
      have hj' : j < g.current_step := hj
      have hi' : i < g.current_step := hi
      have hnw : g.node? (sel j) = some nw := by rw [hjw]; exact hw
      refine mem_dropList _ x _ (chain_mem_owners g sel h j hj0 hj' nw hnw i hi0 hi') ?_
      intro hix
      exact hnot i j hi0 hi' hj0 hj' hix hjw
    · exact h
  · exact h

theorem ChainSound_aggNode (g : GPathM) (x : PathNodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (aggNode g x) sel := by
  unfold aggNode
  split
  · exact h
  · have hfin : ∀ g₁ : GPathM, ChainSound g₁ sel → ChainSound
        (match g₁.node? x with
          | none => g₁
          | some n₁ => if isValidNode g₁ n₁ then g₁ else removeNode g₁ x) sel := by
      intro g₁ hg₁
      split
      · exact hg₁
      · next n₁ hn₁ =>
        split
        · exact hg₁
        · next hinv =>
          refine ChainSound_removeNode g₁ x sel hg₁ ?_
          intro k hk0 hk hkx
          have hn' : g₁.node? (sel k) = some n₁ := by rw [hkx]; exact hn₁
          exact hinv (isValidNode_of_chain g₁ sel hg₁ k n₁ hn' hk0 hk)
    apply hfin
    split
    · exact chain_foldl _ sel
        (fun g kw hg => chain_foldl _ sel (fun g w hg => ChainSound_aggPair g x w sel hg) _ g hg)
        _ g h
    · exact h

theorem ChainSound_aggSweep (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (aggSweep g) sel := by
  unfold aggSweep
  split
  · exact chain_foldl _ sel
      (fun g k hg => chain_foldl _ sel (fun g x hg => ChainSound_aggNode g x sel hg) _ g hg) _ g h
  · exact h

theorem ChainSound_reviewAggFuel : ∀ (fuel : Nat) (g : GPathM) (sel : Int → PathNodeId),
    ChainSound g sel → ChainSound (reviewAggFuel fuel g) sel := by
  intro fuel
  induction fuel with
  | zero => intro g sel h; exact ChainSound_review g sel h
  | succ n ih =>
    intro g sel h
    simp only [reviewAggFuel]
    have h₁ := ChainSound_review g sel h
    split
    · split
      · exact ih _ sel (ChainSound_aggSweep _ sel h₁)
      · exact h₁
    · exact h₁

/-- **The aggressive review loses no solution.** -/
theorem ChainSound_reviewAgg (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (reviewAgg g) sel :=
  ChainSound_reviewAggFuel _ g sel h

/-- A chain through the pins survives pins and the aggressive review. -/
theorem ChainSound_filterAllAgg (g : GPathM) (reqs : List NodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (hreqs : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    ChainSound (filterAllAgg g reqs) sel :=
  ChainSound_reviewAgg _ sel (ChainSound_foldl_filterRequire reqs g sel h hreqs)

-- ============================================================
-- Any review with these two properties can drive the machine
-- ============================================================

/-- **What a review has to earn to drive the machine**: it only removes, and it loses no sound
chain. The conservation law (`ConservationFilter`) is proved once for any such review. -/
class ReviewOk (R : GPathM → GPathM) : Prop where
  pruned : ∀ g, Pruned g (R g)
  keeps : ∀ g sel, ChainSound g sel → ChainSound (R g) sel

instance reviewOk_review : ReviewOk review :=
  ⟨pruned_review, fun g sel h => ChainSound_review g sel h⟩

instance reviewOk_reviewAgg : ReviewOk reviewAgg :=
  ⟨pruned_reviewAgg, fun g sel h => ChainSound_reviewAgg g sel h⟩

/-- Pins, then the review `R`. -/
def filterAllR (R : GPathM → GPathM) (g : GPathM) (reqs : List NodeId) : GPathM :=
  R (reqs.foldl filterRequire g)

/-- Pins, the review `R`, then `up` (which skips the windows `forb`, and after a skipped window
runs the plain `review`, as Julia's `do_up!`). -/
def upFilteringR (R : GPathM → GPathM) (g : GPathM) (reqs : List NodeId) (d : NodeId)
    (title : String) (forb : PathNodeId → Bool) : GPathM :=
  up (filterAllR R g reqs) d title forb

theorem filterAllR_review (g : GPathM) (reqs : List NodeId) :
    filterAllR review g reqs = filterAll g reqs := rfl

theorem upFilteringR_review (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String) (forb : PathNodeId → Bool) :
    upFilteringR review g reqs d title forb = upFiltering g reqs d title forb := rfl

theorem filterAllR_reviewAgg (g : GPathM) (reqs : List NodeId) :
    filterAllR reviewAgg g reqs = filterAllAgg g reqs := rfl

theorem pruned_filterAllR (R : GPathM → GPathM) [ReviewOk R] (g : GPathM) (reqs : List NodeId) :
    Pruned g (filterAllR R g reqs) :=
  Pruned.trans (pruned_foldl filterRequire pruned_filterRequire reqs g) (ReviewOk.pruned _)

theorem ChainSound_filterAllR (R : GPathM → GPathM) [ReviewOk R] (g : GPathM)
    (reqs : List NodeId) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hreqs : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    ChainSound (filterAllR R g reqs) sel :=
  ReviewOk.keeps _ sel (ChainSound_foldl_filterRequire reqs g sel h hreqs)

/-- `ChainSound_upFiltering`, for any review that earns `ReviewOk`. -/
theorem ChainSound_upFilteringR (R : GPathM → GPathM) [ReviewOk R] (g : GPathM)
    (reqs : List NodeId) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hvalid : isValid (filterAllR R g reqs) = true)
    (hd : d.step = (filterAllR R g reqs).current_step)
    (hbelow : ∀ n ∈ (filterAllR R g reqs).nodes, n.id.id.step < (filterAllR R g reqs).current_step)
    (hmok : MachineOk (filterAllR R g reqs))
    (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hreqs : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req)
    (hf : forb (extendPid (filterAllR R g reqs) d sel) = false) :
    ChainSound (upFilteringR R g reqs d title forb) (extend (filterAllR R g reqs) d sel) := by
  have hadd := ChainSound_addNode _ d title forb hd hbelow hmok sel
    (ChainSound_filterAllR R g reqs sel h hreqs) hf
  simp only [upFilteringR, up, hvalid, if_true]
  split
  · exact ChainSound_review _ _ hadd
  · exact hadd

/-- info: 'AbsSatBin.GraphPath.Model.AggressiveReview.pruned_filterAllAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pruned_filterAllAgg

/-- info: 'AbsSatBin.GraphPath.Model.AggressiveReview.ChainSound_filterAllAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_filterAllAgg

end AbsSatBin.GraphPath.Model.AggressiveReview
