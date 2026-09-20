-- lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean
import AbsSat.GraphPath.Model.HereditaryValid

/-!
# `ImprovesCima`: the review with the rule of the top

Route C leaves one thing open: the witnesses the review hands for a pair must lie in the table of the
side the pair's chain names (`HereditaryValid.ChainClosureAt`). Probes `chainside2`, `history` and
`chainfam` never saw it fail (2.8 M pairs, 0 failures), but nothing in the current review forces it.

This module adds a rule that does force it. It is the `Improves` machine with one more sweep inside the
review, run at a union by key, where the sides that built the union are still at hand:

> **The rule of the top.** Keep an entry `a → b` only if **some** top `t` is good for it: a chain of
> common owners of `a` and `b` reaches `t`, the side of `t` carries `a → b` in its own table, and at
> every step there is a witness `z` that the same side carries with both ends.

The rule asks for one good top, not for all of them. A genuine path hands one over — its own top, with
its own nodes as witnesses and as the chain — so the rule never removes a pair of a genuine path, and
that is what keeps the machine from losing solutions.

The sweep only removes entries, and a genuine path is never touched: its own nodes are the chain and the
witnesses, and the side of any top it reaches carries all of its pairs.

What is proved here: the rule's shape (`cimaPair` drops at most one entry pair), and that the sweep only
removes (`keeps_cimaSweep`, `pruned_cimaSweep`). The two core statements — no solution is lost, and a
support survives — are stated as `ConservesChains` and `KeepsSupports`, the next targets.
-/

namespace AbsSat.GraphPath.Model.ImprovesCima

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview (dropList dropOwnerPair)
open AbsSat.GraphPath.Model.ReaderAgg (Keeps)
open AbsSat.GraphPath.Model.AggressiveReview (reviewAgg ChainSound_reviewAgg)

-- ============================================================
-- What a side carries
-- ============================================================

open AbsSat.GraphPath.Model.EmbeddedSupport (Rel)

/-- Both directions of an owner table give the pair as a relation of that state. -/
theorem rel_of_owners (S : GPathM) (a b : PathNodeId)
    (h1 : (ownersOf S a).contains b = true) (h2 : (ownersOf S b).contains a = true) :
    Rel S a b ∧ Rel S b a := by
  unfold ownersOf at h1 h2
  cases ha : S.node? a with
  | none => rw [ha] at h1; exact absurd h1 (by rw [List.contains_iff_mem]; exact fun h => nomatch h)
  | some na =>
    cases hb : S.node? b with
    | none => rw [hb] at h2; exact absurd h2 (by rw [List.contains_iff_mem]; exact fun h => nomatch h)
    | some nb =>
      rw [ha] at h1; rw [hb] at h2
      exact ⟨⟨na, ha, List.contains_iff_mem.mp h1, ⟨nb, hb⟩⟩,
        ⟨nb, hb, List.contains_iff_mem.mp h2, ⟨na, ha⟩⟩⟩

/-- **Does a side of the top carry the entry?** The top of a side exists only in that side, so this asks
exactly what its own table says about the pair, in both directions. -/
def carries (sides : List GPathM) (t a b : PathNodeId) : Bool :=
  sides.any (fun S => (S.node? t).isSome && (ownersOf S a).contains b && (ownersOf S b).contains a)

/-- **The second bridge**: a side that holds the top and carries the pair in its table makes `carries`
true. -/
theorem carries_of_side (sides : List GPathM) (S : GPathM) (hS : S ∈ sides) (t a b : PathNodeId)
    (ht : (S.node? t).isSome = true) (h1 : Rel S a b) (h2 : Rel S b a) :
    carries sides t a b = true := by
  have how : ∀ x y, Rel S x y → (ownersOf S x).contains y = true := by
    intro x y hxy
    obtain ⟨m, hm, hy, _⟩ := hxy
    unfold ownersOf; rw [hm]; exact List.contains_iff_mem.mpr hy
  exact List.any_eq_true.mpr ⟨S, hS, by simp only [ht, how a b h1, how b a h2, Bool.and_self]⟩

/-- **Is `b` a parent of `a` in the side that holds `t`?** The top of a side exists only in that side, so
this reads the parent links of that one side. -/
def linkedIn (sides : List GPathM) (t a b : PathNodeId) : Bool :=
  sides.any (fun S => (S.node? t).isSome &&
    (match S.node? a with | none => false | some na => na.parents.contains b))

-- ============================================================
-- The sweep, for any test on an entry
-- ============================================================

/-- **The rule of the top, for one entry.** If some top the pair's chain reaches has a side that does not
carry the pair, the two stop owning each other. -/
def prunePair (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (x w : PathNodeId) : GPathM :=
  match g.node? x, g.node? w with
  | some nx, some nw =>
    if nx.owners.contains w && !test g x w then
      dropOwnerPair g x w nx.owners nw.owners
    else g
  | _, _ => g

def pruneNode (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (x : PathNodeId) : GPathM :=
  match g.node? x with
  | none => g
  | some nx => nx.owners.foldl (fun g w => prunePair test g x w) g

/-- The sweep: every node, from the last step down. -/
def pruneSweep (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) : GPathM :=
  if isValid g then
    (intRange 0 (g.current_step - 1)).reverse.foldl
      (fun g k => ((g.line k).map (·.id)).foldl (pruneNode test) g) g
  else g

-- ============================================================
-- The sweep only removes
-- ============================================================

theorem keeps_prunePair (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (x w : PathNodeId) :
    Keeps g (prunePair test g x w) := by
  unfold prunePair
  split
  · split
    · exact Keeps.trans (ReaderAgg.keeps_updateAt_uniMap _ _ _)
        (ReaderAgg.keeps_updateAt_uniMap _ _ _)
    · exact Keeps.refl g
  · exact Keeps.refl g

theorem keeps_pruneNode (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (x : PathNodeId) :
    Keeps g (pruneNode test g x) := by
  unfold pruneNode
  cases hx : g.node? x with
  | none => exact Keeps.refl g
  | some nx => exact ReaderAgg.keeps_foldl _ (fun g w => keeps_prunePair test g x w) _ _

theorem keeps_pruneSweep (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) : Keeps g (pruneSweep test g) := by
  unfold pruneSweep
  split
  · exact ReaderAgg.keeps_foldl _
      (fun g k => ReaderAgg.keeps_foldl _ (fun g x => keeps_pruneNode test g x) _ _) _ _
  · exact Keeps.refl g

-- ============================================================
-- The core: no solution is lost
-- ============================================================

open AbsSat.GraphPath.Model.AggressiveReview (mem_dropList chain_mem_owners)

/-- **One entry: the rule never separates two nodes of a sound chain** whose reached tops the sides
carry. Off the chain it only removes, as every drop does. -/
theorem ChainSound_prunePair (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (x w : PathNodeId)
    (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hcar : ∀ i j, 0 ≤ i → i < g.current_step → 0 ≤ j → j < g.current_step → sel i = x → sel j = w →
      test g x w = true) :
    ChainSound (prunePair test g x w) sel := by
  unfold prunePair
  split
  · next nx nw hx hw =>
    split
    · next hcond =>
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hnot : ∀ i j, 0 ≤ i → i < g.current_step → 0 ≤ j → j < g.current_step →
          sel i = x → sel j = w → False := by
        intro i j hi0 hi hj0 hj hix hjw
        have := hcar i j hi0 hi hj0 hj hix hjw
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
      have hnw : g.node? (sel j) = some nw := by rw [hjw]; exact hw
      refine mem_dropList _ x _ (chain_mem_owners g sel h j hj0 hj nw hnw i hi0 hi) ?_
      intro hix
      exact hnot i j hi0 hi hj0 hj hix hjw
    · exact h
  · exact h

/-- The rule's hypothesis, robust along the sweep: at every narrowing the sweep can reach, the tops a
chain pair reaches are carried by their sides. -/
def TestC (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ g', Keeps g g' → ChainSound g' sel → ∀ i j, 0 ≤ i → i < g'.current_step → 0 ≤ j →
    j < g'.current_step → test g' (sel i) (sel j) = true

theorem ChainSound_pruneNode (test : GPathM → PathNodeId → PathNodeId → Bool) (g g₀ : GPathM) (x : PathNodeId)
    (sel : Int → PathNodeId) (hk : Keeps g₀ g) (h : ChainSound g sel) (hC : TestC test g₀ sel) :
    ChainSound (pruneNode test g x) sel ∧ Keeps g₀ (pruneNode test g x) := by
  refine ⟨?_, Keeps.trans hk (keeps_pruneNode test g x)⟩
  unfold pruneNode
  split
  · exact h
  · next nx _ =>
    refine BranchLines.foldl_inv (fun g' w => prunePair test g' x w)
      (fun g' => ChainSound g' sel ∧ Keeps g₀ g') nx.owners ?_ g ⟨h, hk⟩ |>.1
    intro g' w _ hg'
    refine ⟨ChainSound_prunePair test g' x w sel hg'.1 ?_, Keeps.trans hg'.2 (keeps_prunePair _ _ _ _)⟩
    intro i j hi0 hi hj0 hj hix hjw
    have := hC g' hg'.2 hg'.1 i j hi0 hi hj0 hj
    rw [hix, hjw] at this
    exact this

/-- **The sweep loses no solution.** -/
theorem ChainSound_pruneSweep (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (hC : TestC test g sel) : ChainSound (pruneSweep test g) sel := by
  unfold pruneSweep
  split
  · refine BranchLines.foldl_inv
      (fun g' k => ((g'.line k).map (·.id)).foldl (pruneNode test) g')
      (fun g' => ChainSound g' sel ∧ Keeps g g') _ ?_ g ⟨h, Keeps.refl g⟩ |>.1
    intro g' k _ hg'
    refine BranchLines.foldl_inv (pruneNode test) (fun g'' => ChainSound g'' sel ∧ Keeps g g'')
      _ ?_ g' hg'
    intro g'' x _ hg''
    exact ChainSound_pruneNode test g'' g x sel hg''.2 hg''.1 hC
  · exact h

-- ============================================================
-- The core: a support survives
-- ============================================================

open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk Sup_updateAt)

variable {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- **One entry: the rule never drops a pair of a support** whose reached tops the sides carry. -/
theorem Sup_prunePair (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (h : Sup g S R) (x w : PathNodeId)
    (hcar : R x w → test g x w = true) :
    Sup (prunePair test g x w) S R := by
  unfold prunePair
  split
  · next nx nw hx hw =>
    split
    · next hcond =>
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hnxw : ¬ R x w := fun hr => by
        rw [hcar hr] at hcond
        exact Bool.noConfusion hcond.2
      have hnwx : ¬ R w x := fun hr => hnxw (h.sym w x hr)
      have hb1 : S x → ∀ v, R x v → v ∈ dropList nx.owners w := fun _ v hr =>
        AggressiveReview.mem_dropList _ w v (h.own x v nx hr hx) (fun he => hnxw (he ▸ hr))
      have hb2 : S w → ∀ v, R w v → v ∈ dropList nw.owners x := fun _ v hr =>
        AggressiveReview.mem_dropList _ x v (h.own w v nw hr hw) (fun he => hnwx (he ▸ hr))
      exact Sup_updateAt _ w _ hb2 (Sup_updateAt g x _ hb1 h)
    · exact h
  · exact h

theorem SMP_prunePair (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (hs : Sons.SMP g) (x w : PathNodeId) :
    Sons.SMP (prunePair test g x w) := by
  unfold prunePair
  split
  · split
    · exact Sons.SMP_updateAt _ w _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (Sons.SMP_updateAt g x _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hs)
    · exact hs
  · exact hs

theorem AOk_prunePair (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (h : AOk g S R) (x w : PathNodeId)
    (hcar : R x w → test g x w = true) :
    AOk (prunePair test g x w) S R :=
  ⟨Sup_prunePair test g h.sup x w hcar, SMP_prunePair test g h.smp x w,
    Parents.NotRoot_of_pruned (keeps_prunePair test g x w).1 h.nr⟩

/-- The rule's hypothesis for a support, robust along the sweep. -/
def TestR (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (R : PathNodeId → PathNodeId → Prop) : Prop :=
  ∀ g', Keeps g g' → ∀ x v, R x v → test g' x v = true

theorem AOk_pruneNode (test : GPathM → PathNodeId → PathNodeId → Bool) (g g₀ : GPathM) (x : PathNodeId) (hk : Keeps g₀ g)
    (h : AOk g S R) (hC : TestR test g₀ R) : AOk (pruneNode test g x) S R ∧ Keeps g₀ (pruneNode test g x) := by
  refine ⟨?_, Keeps.trans hk (keeps_pruneNode test g x)⟩
  unfold pruneNode
  split
  · exact h
  · next nx _ =>
    refine BranchLines.foldl_inv (fun g' w => prunePair test g' x w)
      (fun g' => AOk g' S R ∧ Keeps g₀ g') nx.owners ?_ g ⟨h, hk⟩ |>.1
    intro g' w _ hg'
    exact ⟨AOk_prunePair test g' hg'.1 x w (fun hr => hC g' hg'.2 x w hr),
      Keeps.trans hg'.2 (keeps_prunePair _ _ _ _)⟩

/-- **A support survives the sweep.** The rule only drops pairs whose chain reaches a top the sides do
not carry, and a support's pairs are carried by hypothesis; everything else it removes leaves the support
where it was. -/
theorem AOk_pruneSweep (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (h : AOk g S R) (hC : TestR test g R) :
    AOk (pruneSweep test g) S R := by
  unfold pruneSweep
  split
  · refine BranchLines.foldl_inv
      (fun g' k => ((g'.line k).map (·.id)).foldl (pruneNode test) g')
      (fun g' => AOk g' S R ∧ Keeps g g') _ ?_ g ⟨h, Keeps.refl g⟩ |>.1
    intro g' k _ hg'
    refine BranchLines.foldl_inv (pruneNode test) (fun g'' => AOk g'' S R ∧ Keeps g g'')
      _ ?_ g' hg'
    intro g'' x _ hg''
    exact AOk_pruneNode test g'' g x hg''.2 hg''.1 hC
  · exact h

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.ChainSound_pruneSweep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_pruneSweep

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.AOk_pruneSweep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AOk_pruneSweep


-- ============================================================
-- The fixpoint: at the end, every entry has a good top
-- ============================================================

open AbsSat.GraphPath.Model.AggFixpoint (EqOrLt eqOrLt_foldl foldl_noProgress weight_drop_lt
  weight_uniMap_le measure_updateAt_uniMap_lt mem_reverse_intRange)

theorem prunePair_eqOrLt (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (x w : PathNodeId) :
    EqOrLt g (prunePair test g x w) := by
  unfold prunePair
  split
  · next nx nw hx hw =>
    split
    · next hcond =>
      have hmem : w ∈ nx.owners := by
        simp only [Bool.and_eq_true] at hcond
        exact List.contains_iff_mem.mp hcond.1
      refine Or.inr (Nat.lt_of_le_of_lt ?_
        (measure_updateAt_uniMap_lt g x _ nx hx (weight_drop_lt nx w hmem)))
      exact GPathM.measure_updateAt_le _ w _ (fun n => weight_uniMap_le _ n)
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem measure_prunePair_lt (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (x w : PathNodeId) (nx nw : PNodeM)
    (hx : g.node? x = some nx) (hw : g.node? w = some nw) (hmem : w ∈ nx.owners)
    (hfire : test g x w = false) :
    GPathM.measure (prunePair test g x w) < GPathM.measure g := by
  have hcw : nx.owners.contains w = true := List.contains_iff_mem.mpr hmem
  have heq : prunePair test g x w = dropOwnerPair g x w nx.owners nw.owners := by
    unfold prunePair
    rw [hx, hw]
    simp only [hcw, hfire, Bool.not_false, Bool.and_self, if_pos]
  rw [heq]
  refine Nat.lt_of_le_of_lt ?_ (measure_updateAt_uniMap_lt g x _ nx hx (weight_drop_lt nx w hmem))
  exact GPathM.measure_updateAt_le _ w _ (fun n => weight_uniMap_le _ n)

/-- **The test the rule leaves behind**: every live entry has a good top. -/
def TestOk (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) : Prop :=
  ∀ x nx w, g.node? x = some nx → (g.node? w).isSome = true →
    0 ≤ x.id.step → x.id.step < g.current_step →
    0 ≤ w.id.step → w.id.step < g.current_step →
    w ∈ nx.owners → test g x w = true

/-- **If the sweep does not lower the measure of a valid state, the state passes the test.** -/
theorem testOk_of_noProgress (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (hv : isValid g = true)
    (hnp : ¬ GPathM.measure (pruneSweep test g) < GPathM.measure g) : TestOk test g := by
  intro x nx w hx hw hx1 hx2 hw1 hw2 hmem
  cases hok : test g x w with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨nw, hnw⟩ := Option.isSome_iff_exists.mp hw
    have hsweep : pruneSweep test g = (intRange 0 (g.current_step - 1)).reverse.foldl
        (fun g k => ((g.line k).map (·.id)).foldl (pruneNode test) g) g := by
      unfold pruneSweep
      rw [if_pos hv]
    rw [hsweep] at hnp
    have hnodeEq : ∀ g' (x' : PathNodeId), EqOrLt g' (pruneNode test g' x') := by
      intro g' x'
      unfold pruneNode
      split
      · exact Or.inl rfl
      · next nx' _ => exact eqOrLt_foldl _ (fun g'' w' => prunePair_eqOrLt test g'' x' w') _ g'
    have houter := foldl_noProgress _
      (fun g' k => eqOrLt_foldl _ (fun g'' x' => hnodeEq g'' x') _ g') _ g hnp x.id.step
      (mem_reverse_intRange hx1 (by omega))
    have hline : x ∈ (g.line x.id.step).map (·.id) := mem_line_of_node? g x nx hx _ rfl
    have hinner := foldl_noProgress _ (fun g' x' => hnodeEq g' x') _ g
      (by rw [houter]; exact Nat.lt_irrefl _) x hline
    have hfold : nx.owners.foldl (fun g' w' => prunePair test g' x w') g = g := by
      have : pruneNode test g x = nx.owners.foldl (fun g' w' => prunePair test g' x w') g := by
        unfold pruneNode; rw [hx]
      rw [← this]; exact hinner
    have hpair := foldl_noProgress _ (fun g' w' => prunePair_eqOrLt test g' x w') _ g
      (by rw [hfold]; exact Nat.lt_irrefl _) w hmem
    have hlt := measure_prunePair_lt test g x w nx nw hx hnw hmem hok
    rw [hpair] at hlt
    exact Nat.lt_irrefl _ hlt

-- ============================================================
-- The invariants of a state survive the rule
-- ============================================================

theorem PMS_prunePair (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (hs : Sons.PMS g) (x w : PathNodeId) :
    Sons.PMS (prunePair test g x w) := by
  unfold prunePair
  split
  · split
    · exact Sons.PMS_updateAt _ w _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (Sons.PMS_updateAt g x _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hs)
    · exact hs
  · exact hs

theorem SN_prunePair (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (hs : Sons.SN g) (x w : PathNodeId) :
    Sons.SN (prunePair test g x w) := by
  unfold prunePair
  split
  · split
    · exact Sons.SN_updateAt _ w _ (fun _ => rfl) (fun _ => rfl)
        (Sons.SN_updateAt g x _ (fun _ => rfl) (fun _ => rfl) hs)
    · exact hs
  · exact hs

theorem SMP_pruneNode (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (hs : Sons.SMP g) (x : PathNodeId) :
    Sons.SMP (pruneNode test g x) := by
  unfold pruneNode
  split
  · exact hs
  · next nx _ =>
    exact BranchLines.foldl_inv (fun g' w => prunePair test g' x w) (fun g' => Sons.SMP g')
      nx.owners (fun g' w _ hg' => SMP_prunePair test g' hg' x w) g hs

theorem PMS_pruneNode (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (hs : Sons.PMS g) (x : PathNodeId) :
    Sons.PMS (pruneNode test g x) := by
  unfold pruneNode
  split
  · exact hs
  · next nx _ =>
    exact BranchLines.foldl_inv (fun g' w => prunePair test g' x w) (fun g' => Sons.PMS g')
      nx.owners (fun g' w _ hg' => PMS_prunePair test g' hg' x w) g hs

theorem SN_pruneNode (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (hs : Sons.SN g) (x : PathNodeId) :
    Sons.SN (pruneNode test g x) := by
  unfold pruneNode
  split
  · exact hs
  · next nx _ =>
    exact BranchLines.foldl_inv (fun g' w => prunePair test g' x w) (fun g' => Sons.SN g')
      nx.owners (fun g' w _ hg' => SN_prunePair test g' hg' x w) g hs

theorem sons_pruneSweep (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (hsmp : Sons.SMP g) (hpms : Sons.PMS g)
    (hsn : Sons.SN g) :
    Sons.SMP (pruneSweep test g) ∧ Sons.PMS (pruneSweep test g) ∧ Sons.SN (pruneSweep test g) := by
  unfold pruneSweep
  split
  · refine BranchLines.foldl_inv
      (fun g' k => ((g'.line k).map (·.id)).foldl (pruneNode test) g')
      (fun g' => Sons.SMP g' ∧ Sons.PMS g' ∧ Sons.SN g') _ ?_ g ⟨hsmp, hpms, hsn⟩
    intro g' k _ hg'
    refine BranchLines.foldl_inv (pruneNode test) (fun g'' => Sons.SMP g'' ∧ Sons.PMS g'' ∧ Sons.SN g'')
      _ ?_ g' hg'
    intro g'' x _ hg''
    exact ⟨SMP_pruneNode test g'' hg''.1 x, PMS_pruneNode test g'' hg''.2.1 x,
      SN_pruneNode test g'' hg''.2.2 x⟩
  · exact ⟨hsmp, hpms, hsn⟩

-- ============================================================
-- The family a top names: the union restricted to its side
-- ============================================================

/-- **The test of the restriction.** The side of `t` carries the entry in both directions, and on
neighbouring steps it links it as parent and son. It does not look at the state at all, so the sweep
settles it in one pass. -/
def restTest (sides : List GPathM) (t : PathNodeId) (_g : GPathM) (a b : PathNodeId) : Bool :=
  carries sides t a b && carries sides t b a &&
    (!(b.id.step + 1 == a.id.step) || linkedIn sides t a b) &&
    (!(a.id.step + 1 == b.id.step) || linkedIn sides t b a)

def restFuel (sides : List GPathM) (t : PathNodeId) : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    let g₂ := pruneSweep (restTest sides t) g
    if GPathM.measure g₂ < GPathM.measure g then restFuel sides t fuel g₂ else g

def restAll (sides : List GPathM) (t : PathNodeId) (g : GPathM) : GPathM :=
  restFuel sides t (GPathM.measure g + 1) g

/-- **The family the top `t` names**: the union cut down to what the side of `t` carries, and then
reviewed to its fixpoint. What is left is a state of the machine's own kind — so it has a support
anchored at its top — whose entries are all entries of that one side. -/
def famFix (sides : List GPathM) (t : PathNodeId) (g : GPathM) : GPathM :=
  reviewAgg (restAll sides t g)

theorem keeps_restFuel (sides : List GPathM) (t : PathNodeId) :
    ∀ (fuel : Nat) (g : GPathM), Keeps g (restFuel sides t fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Keeps.refl g
  | succ n ih =>
    intro g
    simp only [restFuel]
    split
    · exact Keeps.trans (keeps_pruneSweep _ g) (ih _)
    · exact Keeps.refl g

theorem keeps_restAll (sides : List GPathM) (t : PathNodeId) (g : GPathM) :
    Keeps g (restAll sides t g) := keeps_restFuel sides t _ g

theorem keeps_famFix (sides : List GPathM) (t : PathNodeId) (g : GPathM) :
    Keeps g (famFix sides t g) :=
  Keeps.trans (keeps_restAll sides t g) (ReaderAggRun.keeps_reviewAggFuel _ _)

/-- **The family keeps a chain the side carries.** The restriction only drops what the side does not
carry, so a chain that lives in the side is never touched, and the review keeps it too. -/
theorem ChainSound_restFuel (sides : List GPathM) (t : PathNodeId) (sel : Int → PathNodeId) :
    ∀ (fuel : Nat) (g : GPathM), ChainSound g sel →
      (∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step →
        restTest sides t g (sel p) (sel q) = true) →
      ChainSound (restFuel sides t fuel g) sel := by
  intro fuel
  induction fuel with
  | zero => intro g h _; exact h
  | succ n ih =>
    intro g h hT
    simp only [restFuel]
    split
    · refine ih _ (ChainSound_pruneSweep _ g sel h (fun g' hk _ p q hp0 hp hq0 hq => ?_)) ?_
      · exact hT p q hp0 (by rw [← hk.1.step_eq]; exact hp) hq0 (by rw [← hk.1.step_eq]; exact hq)
      · intro p q hp0 hp hq0 hq
        have he := (keeps_pruneSweep (restTest sides t) g).1.step_eq
        exact hT p q hp0 (by rw [← he]; exact hp) hq0 (by rw [← he]; exact hq)
    · exact h

theorem ChainSound_famFix (sides : List GPathM) (t : PathNodeId) (sel : Int → PathNodeId)
    (g : GPathM) (h : ChainSound g sel)
    (hT : ∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step →
      restTest sides t g (sel p) (sel q) = true) :
    ChainSound (famFix sides t g) sel :=
  ChainSound_reviewAgg _ sel (ChainSound_restFuel sides t sel _ g h hT)

/-- **The restriction settles.** When the sweep no longer removes anything from a live state, every
entry left passes the test — it is an entry of the side of `t`, linked as parent and son where the steps
are neighbours. -/
theorem restOk_restFuel (sides : List GPathM) (t : PathNodeId) :
    ∀ (fuel : Nat) (g : GPathM), GPathM.measure g < fuel →
      isValid (restFuel sides t fuel g) = true →
      TestOk (restTest sides t) (restFuel sides t fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro g hm hv
    simp only [restFuel] at hv ⊢
    split at hv
    · next hlt =>
      rw [if_pos hlt]
      exact ih _ (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hm)) hv
    · next hnlt =>
      rw [if_neg hnlt]
      exact testOk_of_noProgress _ g hv hnlt

theorem restOk_restAll (sides : List GPathM) (t : PathNodeId) (g : GPathM)
    (hv : isValid (restAll sides t g) = true) : TestOk (restTest sides t) (restAll sides t g) :=
  restOk_restFuel sides t _ g (Nat.lt_succ_self _) hv

/-- **Every entry the family keeps is an entry of the side of `t`.** The review that follows the
restriction only removes, so what it leaves still passes the test. -/
theorem restTest_of_famFix (sides : List GPathM) (t : PathNodeId) (g : GPathM)
    (hnd : ((restAll sides t g).nodes.map (·.id)).Nodup)
    (hv : isValid (famFix sides t g) = true)
    (a b : PathNodeId) (h : Rel (famFix sides t g) a b)
    (ha0 : 0 ≤ a.id.step) (ha1 : a.id.step < g.current_step)
    (hb0 : 0 ≤ b.id.step) (hb1 : b.id.step < g.current_step) :
    restTest sides t g a b = true := by
  have hprF : Pruned (restAll sides t g) (famFix sides t g) :=
    (ReaderAggRun.keeps_reviewAggFuel _ (restAll sides t g)).1
  have hvR : isValid (restAll sides t g) = true := PinExact.isValid_of_pruned_valid hprF hv
  have hR : Rel (restAll sides t g) a b := PinDeath.rel_of_pruned _ _ hnd hprF a b h
  obtain ⟨n, hn, hmem, nb, hnb⟩ := hR
  have hcs : (restAll sides t g).current_step = g.current_step := (keeps_restAll sides t g).1.step_eq
  exact restOk_restAll sides t g hvR a n b hn (by rw [hnb]; rfl) ha0 (by rw [hcs]; exact ha1)
    hb0 (by rw [hcs]; exact hb1) hmem

/-- The sons invariants survive the restriction. -/
theorem sons_restFuel (sides : List GPathM) (t : PathNodeId) :
    ∀ (fuel : Nat) (g : GPathM), Sons.SMP g → Sons.PMS g → Sons.SN g →
      Sons.SMP (restFuel sides t fuel g) ∧ Sons.PMS (restFuel sides t fuel g) ∧
        Sons.SN (restFuel sides t fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h1 h2 h3; exact ⟨h1, h2, h3⟩
  | succ n ih =>
    intro g h1 h2 h3
    simp only [restFuel]
    split
    · obtain ⟨a, b, c⟩ := sons_pruneSweep (restTest sides t) g h1 h2 h3
      exact ih _ a b c
    · exact ⟨h1, h2, h3⟩

theorem sons_restAll (sides : List GPathM) (t : PathNodeId) (g : GPathM)
    (h1 : Sons.SMP g) (h2 : Sons.PMS g) (h3 : Sons.SN g) :
    Sons.SMP (restAll sides t g) ∧ Sons.PMS (restAll sides t g) ∧ Sons.SN (restAll sides t g) :=
  sons_restFuel sides t _ g h1 h2 h3

/-- **The family is a state of the machine's own kind.** It is the review of a narrowing, so it carries
the reader's context and the sons invariants, and therefore the adjacency its support needs. -/
theorem adj_famFix (sides : List GPathM) (t : PathNodeId) (g : GPathM)
    (hrc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g)
    (hv : isValid (famFix sides t g) = true) :
    AdjacentOwners.Adj (famFix sides t g) ∧ Sons.SMP (famFix sides t g) := by
  obtain ⟨s1, s2, s3⟩ := sons_restAll sides t g hsmp hpms hsn
  have hrc0 : Reader.RCtx (restAll sides t g) := ReaderAgg.RCtx_of_keeps (keeps_restAll sides t g) hrc
  have hform : famFix sides t g = AggressiveReview.filterAllAgg (restAll sides t g) [] := rfl
  refine ⟨AdjacentOwners.adj_of_readable _ ?_ hv ?_ ?_, ?_⟩
  · exact ⟨restAll sides t g, [], hrc0, hform⟩
  · rw [hform]; exact AggInvariants.PMS_filterAllAgg _ [] s2
  · rw [hform]; exact AggInvariants.SN_filterAllAgg _ [] s3
  · rw [hform]; exact AnchoredSurvive.SMP_filterAllAgg _ s1 hrc0.shape.notroot []

/-- **The family has a support: its own tables.** It is a review fixpoint, so `LinkedChain.sup_self`
applies with no further hypothesis. -/
theorem sup_famFix (sides : List GPathM) (t : PathNodeId) (g : GPathM)
    (hrc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g)
    (hv : isValid (famFix sides t g) = true) :
    AnchoredSurvive.Sup (famFix sides t g) (EmbeddedSupport.Mem (famFix sides t g))
      (Rel (famFix sides t g)) := by
  obtain ⟨hadj, hsm⟩ := adj_famFix sides t g hrc hsmp hpms hsn hv
  exact LinkedChain.sup_self _ hadj (AggFixpoint.aggOk_reviewAgg _ hv) hsm

/-- **The rule of the top, for one top.** The entry stays alive in the family that `t` names, and that
family is a live state. -/
def goodFor (sides : List GPathM) (g : GPathM) (t a b : PathNodeId) : Bool :=
  isValid (famFix sides t g) &&
    (ownersOf (famFix sides t g) a).contains b && (ownersOf (famFix sides t g) b).contains a

/-- **The rule of the top.** An entry stays only if some top is good for it. A genuine path gives one:
its own top, with its own nodes as witnesses. -/
def cimaOk (sides : List GPathM) (g : GPathM) (a b : PathNodeId) : Bool :=
  ((g.line (g.current_step - 1)).map (·.id)).any (fun t => goodFor sides g t a b)

-- ============================================================
-- The rule of the top as one instance of that sweep
-- ============================================================

/-- The rule of the top, for one entry, one node, and the whole state. -/
abbrev cimaPair (sides : List GPathM) : GPathM → PathNodeId → PathNodeId → GPathM :=
  prunePair (cimaOk sides)

abbrev cimaNode (sides : List GPathM) : GPathM → PathNodeId → GPathM := pruneNode (cimaOk sides)

abbrev cimaSweep (sides : List GPathM) : GPathM → GPathM := pruneSweep (cimaOk sides)

/-- The rule's hypothesis for a chain, and for a support. -/
abbrev Carried (sides : List GPathM) : GPathM → (Int → PathNodeId) → Prop := TestC (cimaOk sides)

abbrev CarriedR (sides : List GPathM) : GPathM → (PathNodeId → PathNodeId → Prop) → Prop :=
  TestR (cimaOk sides)

/-- **The test the rule leaves behind**: every live entry has a good top. -/
abbrev CimaOk (sides : List GPathM) : GPathM → Prop := TestOk (cimaOk sides)

theorem keeps_cimaPair (sides : List GPathM) (g : GPathM) (x w : PathNodeId) :
    Keeps g (cimaPair sides g x w) := keeps_prunePair _ g x w

theorem keeps_cimaSweep (sides : List GPathM) (g : GPathM) : Keeps g (cimaSweep sides g) :=
  keeps_pruneSweep _ g

theorem ChainSound_cimaSweep (sides : List GPathM) (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (hC : Carried sides g sel) : ChainSound (cimaSweep sides g) sel :=
  ChainSound_pruneSweep _ g sel h hC

theorem AOk_cimaSweep (sides : List GPathM) (g : GPathM) (h : AOk g S R) (hC : CarriedR sides g R) :
    AOk (cimaSweep sides g) S R := AOk_pruneSweep _ g h hC

theorem cimaOk_of_noProgress (sides : List GPathM) (g : GPathM) (hv : isValid g = true)
    (hnp : ¬ GPathM.measure (cimaSweep sides g) < GPathM.measure g) : CimaOk sides g :=
  testOk_of_noProgress _ g hv hnp

-- ============================================================
-- The review of a union: the aggressive review and the rule, to their fixpoint
-- ============================================================

open AbsSat.GraphPath.Model.AnchoredSurvive (AOk_filterAllAgg)

/-- The review a union gets: the aggressive review to its fixpoint, one sweep of the rule, and again
while the sweep removes something. Same shape as `reviewAgg`, so everything proved about review
fixpoints still applies to the state it returns. -/
def reviewCimaFuel (sides : List GPathM) : Nat → GPathM → GPathM
  | 0, g => reviewAgg g
  | fuel + 1, g =>
    let g₁ := reviewAgg g
    if isValid g₁ then
      let g₂ := cimaSweep sides g₁
      if measure g₂ < measure g₁ then reviewCimaFuel sides fuel g₂ else g₁
    else g₁

def reviewCima (sides : List GPathM) (g : GPathM) : GPathM := reviewCimaFuel sides (measure g + 1) g

/-- Pins, then that review: the filter of a union in `ImprovesCima`. -/
def filterAllCima (sides : List GPathM) (g : GPathM) (reqs : List NodeId) : GPathM :=
  reviewCima sides (reqs.foldl filterRequire g)

-- ============================================================
-- What the review of a union earns
-- ============================================================

theorem keeps_reviewCimaFuel (sides : List GPathM) :
    ∀ (fuel : Nat) (g : GPathM), Keeps g (reviewCimaFuel sides fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact ReaderAggRun.keeps_reviewAggFuel _ g
  | succ n ih =>
    intro g
    simp only [reviewCimaFuel]
    split
    · split
      · exact Keeps.trans (ReaderAggRun.keeps_reviewAggFuel _ g)
          (Keeps.trans (keeps_cimaSweep sides _) (ih _))
      · exact ReaderAggRun.keeps_reviewAggFuel _ g
    · exact ReaderAggRun.keeps_reviewAggFuel _ g

theorem keeps_reviewCima (sides : List GPathM) (g : GPathM) : Keeps g (reviewCima sides g) :=
  keeps_reviewCimaFuel sides _ g

theorem keeps_filterAllCima (sides : List GPathM) (g : GPathM) (reqs : List NodeId) :
    Keeps g (filterAllCima sides g reqs) :=
  Keeps.trans (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire reqs g) (keeps_reviewCima _ _)

/-- **The new review is a narrowing of the old one.** Its first move is the aggressive review, and every
later move only removes. So everything proved of a state of `Improves` transports to the same state of
`ImprovesCima` whenever it survives a narrowing. -/
theorem keeps_agg_reviewCimaFuel (sides : List GPathM) : ∀ (fuel : Nat) (g : GPathM),
    Keeps (reviewAgg g) (reviewCimaFuel sides fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Keeps.refl _
  | succ n ih =>
    intro g
    simp only [reviewCimaFuel]
    split
    · split
      · exact Keeps.trans (keeps_cimaSweep sides _)
          (Keeps.trans (ReaderAggRun.keeps_reviewAggFuel _ _) (ih _))
      · exact Keeps.refl _
    · exact Keeps.refl _

theorem keeps_agg_reviewCima (sides : List GPathM) (g : GPathM) :
    Keeps (reviewAgg g) (reviewCima sides g) :=
  keeps_agg_reviewCimaFuel sides _ g

theorem keeps_agg_filterAllCima (sides : List GPathM) (g : GPathM) (reqs : List NodeId) :
    Keeps (AggressiveReview.filterAllAgg g reqs) (filterAllCima sides g reqs) :=
  keeps_agg_reviewCima sides (reqs.foldl filterRequire g)

/-- **The review of a union loses no solution**, given the rule's hypothesis along the way. -/
theorem ChainSound_reviewCimaFuel (sides : List GPathM) (sel : Int → PathNodeId) :
    ∀ (fuel : Nat) (g g₀ : GPathM), Keeps g₀ g → ChainSound g sel → Carried sides g₀ sel →
      ChainSound (reviewCimaFuel sides fuel g) sel := by
  intro fuel
  induction fuel with
  | zero => intro g g₀ _ h _; exact ChainSound_reviewAgg g sel h
  | succ n ih =>
    intro g g₀ hk h hC
    simp only [reviewCimaFuel]
    have h₁ : ChainSound (reviewAgg g) sel := ChainSound_reviewAgg g sel h
    have hk₁ : Keeps g₀ (reviewAgg g) := Keeps.trans hk (ReaderAggRun.keeps_reviewAggFuel _ g)
    split
    · split
      · refine ih _ g₀ (Keeps.trans hk₁ (keeps_cimaSweep sides _)) ?_ hC
        exact ChainSound_cimaSweep sides _ sel h₁
          (fun g' hk' hsc' i j => hC g' (Keeps.trans hk₁ hk') hsc' i j)
      · exact h₁
    · exact h₁

theorem ChainSound_reviewCima (sides : List GPathM) (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (hC : Carried sides g sel) : ChainSound (reviewCima sides g) sel :=
  ChainSound_reviewCimaFuel sides sel _ g g (Keeps.refl g) h hC

/-- **A support survives the review of a union**, given the rule's hypothesis along the way. -/
theorem AOk_reviewCimaFuel (sides : List GPathM) :
    ∀ (fuel : Nat) (g g₀ : GPathM), Keeps g₀ g → AOk g S R → CarriedR sides g₀ R →
      AOk (reviewCimaFuel sides fuel g) S R := by
  intro fuel
  induction fuel with
  | zero => intro g g₀ _ h _; exact AnchoredSurvive.AOk_reviewAggFuel _ g h
  | succ n ih =>
    intro g g₀ hk h hC
    simp only [reviewCimaFuel]
    have h₁ : AOk (reviewAgg g) S R := AnchoredSurvive.AOk_reviewAggFuel _ g h
    have hk₁ : Keeps g₀ (reviewAgg g) := Keeps.trans hk (ReaderAggRun.keeps_reviewAggFuel _ g)
    split
    · split
      · refine ih _ g₀ (Keeps.trans hk₁ (keeps_cimaSweep sides _)) ?_ hC
        exact AOk_cimaSweep sides _ h₁ (fun g' hk' x v hr => hC g' (Keeps.trans hk₁ hk') x v hr)
      · exact h₁
    · exact h₁

/-- **A support survives the pins and the review of a union.** -/
theorem AOk_filterAllCima (sides : List GPathM) (g : GPathM) (h : AOk g S R) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r)
    (hC : CarriedR sides g R) : AOk (filterAllCima sides g reqs) S R := by
  refine AOk_reviewCimaFuel sides _ _ g ?_ ?_ ?_
  · exact ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire reqs g
  · have main : ∀ (l : List NodeId), (∀ r ∈ l, ∀ p, S p → p.id.step = r.step → p.id = r) →
        ∀ h' : GPathM, AOk h' S R → AOk (l.foldl filterRequire h') S R := by
      intro l
      induction l with
      | nil => intro _ h' hw; exact hw
      | cons x xs ih =>
        intro hx h' hw
        simp only [List.foldl_cons]
        exact ih (fun r hr => hx r (List.mem_cons_of_mem _ hr)) _
          (AnchoredSurvive.AOk_filterRequire h' hw x (hx x List.mem_cons_self))
    exact main reqs hpin g h
  · exact hC


-- ============================================================
-- A genuine path always has a good top
-- ============================================================

/-- Any two nodes of a sound chain own each other. -/
theorem rel_of_chainSound (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (p q : Int) (hp0 : 0 ≤ p) (hp : p < g.current_step) (hq0 : 0 ≤ q) (hq : q < g.current_step) :
    Rel g (sel p) (sel q) := by
  obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 p hp0 hp).1
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 q hq0 hq).1
  refine ⟨np, hnp, ?_, nq, hnq⟩
  by_cases hpq : p = q
  · subst hpq
    have hs := h.self_owned p hp0 hp
    simpa [ownersOf, hnp] using hs
  · have hown := h.chain.2.1 q p hq0 hp0 hq hp (fun he => hpq (by omega))
    have hmem := List.mem_filter.mp hown
    simpa [ownersOf, hnp] using hmem.1

/-- **A genuine path always has a good top**: its own. The chain lives in one side, so the side carries
all of its pairs and links them as parents and sons; the restriction to that side never touches it, the
review keeps it, and a state that holds a sound chain is live. -/
theorem cimaOk_of_chain (sides : List GPathM) (g S : GPathM) (hS : S ∈ sides)
    (hcsS : S.current_step = g.current_step) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hSc : ChainSound S sel) (hcs : 0 < g.current_step)
    (i j : Int) (hi0 : 0 ≤ i)
    (hi : i < g.current_step) (hj0 : 0 ≤ j) (hj : j < g.current_step) :
    cimaOk sides g (sel i) (sel j) = true := by
  have htop0 : (0 : Int) ≤ g.current_step - 1 := by omega
  have htop1 : g.current_step - 1 < g.current_step := by omega
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 _ htop0 htop1).1
  have hmemTop : sel (g.current_step - 1) ∈ (g.line (g.current_step - 1)).map (·.id) :=
    mem_line_of_node? g _ nt hnt _ (h.chain.1.1 _ htop0 htop1).2
  refine List.any_eq_true.mpr ⟨sel (g.current_step - 1), hmemTop, ?_⟩
  have hSb : ∀ p : Int, 0 ≤ p → p < g.current_step → p < S.current_step := by
    intro p hp0 hp; rw [hcsS]; exact hp
  -- the side carries every pair of the chain
  have hcarS : ∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step →
      carries sides (sel (g.current_step - 1)) (sel p) (sel q) = true := by
    intro p q hp0 hp hq0 hq
    refine carries_of_side sides S hS _ _ _ ?_
      (rel_of_chainSound S sel hSc p q hp0 (hSb p hp0 hp) hq0 (hSb q hq0 hq))
      (rel_of_chainSound S sel hSc q p hq0 (hSb q hq0 hq) hp0 (hSb p hp0 hp))
    exact (hSc.chain.1.1 _ htop0 (hSb _ htop0 htop1)).1
  -- and links the neighbouring ones as parent and son
  have hstepEq : ∀ p : Int, 0 ≤ p → p < g.current_step → (sel p).id.step = p :=
    fun p hp0 hp => (h.chain.1.1 p hp0 hp).2
  have hlinkS : ∀ p : Int, 0 ≤ p → p + 1 < g.current_step →
      linkedIn sides (sel (g.current_step - 1)) (sel (p + 1)) (sel p) = true := by
    intro p hp0 hp
    obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp
      (hSc.chain.1.1 (p + 1) (by omega) (hSb _ (by omega) hp)).1
    have hpar : sel p ∈ ni.parents := by
      have hl := hSc.chain.1.2 p hp0 (by rw [hcsS]; exact hp)
      rw [hni] at hl; simpa using hl
    refine List.any_eq_true.mpr ⟨S, hS, ?_⟩
    simp only [(hSc.chain.1.1 _ htop0 (hSb _ htop0 htop1)).1, hni,
      List.contains_iff_mem.mpr hpar, Bool.and_self]
  have hT : ∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step →
      restTest sides (sel (g.current_step - 1)) g (sel p) (sel q) = true := by
    intro p q hp0 hp hq0 hq
    have hlk : ∀ u v : Int, 0 ≤ u → u < g.current_step → 0 ≤ v → v < g.current_step →
        ((sel v).id.step + 1 == (sel u).id.step) = true →
        linkedIn sides (sel (g.current_step - 1)) (sel u) (sel v) = true := by
      intro u v hu0 hu hv0 hv he
      have huv : v + 1 = u := by
        have := eq_of_beq he
        rw [hstepEq u hu0 hu, hstepEq v hv0 hv] at this; omega
      rw [← huv]; exact hlinkS v hv0 (by omega)
    have c1 : (!((sel q).id.step + 1 == (sel p).id.step) ||
        linkedIn sides (sel (g.current_step - 1)) (sel p) (sel q)) = true := by
      cases he : ((sel q).id.step + 1 == (sel p).id.step) with
      | false => rfl
      | true => rw [hlk p q hp0 hp hq0 hq he]; rfl
    have c2 : (!((sel p).id.step + 1 == (sel q).id.step) ||
        linkedIn sides (sel (g.current_step - 1)) (sel q) (sel p)) = true := by
      cases he : ((sel p).id.step + 1 == (sel q).id.step) with
      | false => rfl
      | true => rw [hlk q p hq0 hq hp0 hp he]; rfl
    simp only [restTest, hcarS p q hp0 hp hq0 hq, hcarS q p hq0 hq hp0 hp, c1, c2,
      Bool.and_true]
  have hCS : ChainSound (famFix sides (sel (g.current_step - 1)) g) sel :=
    ChainSound_famFix sides _ sel g h hT
  have hcsF : (famFix sides (sel (g.current_step - 1)) g).current_step = g.current_step :=
    (keeps_famFix sides _ g).1.step_eq
  have how : ∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step →
      (ownersOf (famFix sides (sel (g.current_step - 1)) g) (sel p)).contains (sel q) = true := by
    intro p q hp0 hp hq0 hq
    obtain ⟨np, hnp, hmem, _⟩ := rel_of_chainSound _ sel hCS p q hp0 (by rw [hcsF]; exact hp) hq0
      (by rw [hcsF]; exact hq)
    unfold ownersOf; rw [hnp]; exact List.contains_iff_mem.mpr hmem
  simp only [goodFor, PickInduction.isValid_of_ChainG _ sel hCS.chain,
    how i j hi0 hi hj0 hj, how j i hj0 hj hi0 hi, Bool.and_self]

/-- **The rule's hypothesis holds for a genuine path**: while the path survives, its own top stays
good. -/
theorem carried_of_side (sides : List GPathM) (g S : GPathM) (hS : S ∈ sides)
    (sel : Int → PathNodeId) (hSc : ChainSound S sel)
    (hcsS : S.current_step = g.current_step) (hcs : 0 < g.current_step) : Carried sides g sel := by
  intro g' hk hsc i j hi0 hi hj0 hj
  have hstep : g'.current_step = g.current_step := hk.1.step_eq
  refine cimaOk_of_chain sides g' S hS (by rw [hstep]; exact hcsS) sel hsc hSc ?_ i j hi0 hi hj0 hj
  rw [hstep]; exact hcs

/-- **Every valid result of the review of a union passes the rule.** Same shape as the aggressive
review's fixpoint: the loop only stops when the sweep removes nothing, and then the test holds. -/
theorem cimaOk_reviewCimaFuel (sides : List GPathM) : ∀ (fuel : Nat) (g : GPathM),
    GPathM.measure g < fuel → isValid (reviewCimaFuel sides fuel g) = true →
    CimaOk sides (reviewCimaFuel sides fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro g hm hv
    have hle : GPathM.measure (reviewAgg g) ≤ GPathM.measure g :=
      ReaderAgg.measure_reviewAggFuel_le _ g
    simp only [reviewCimaFuel] at hv ⊢
    split at hv
    · next hv₁ =>
      rw [if_pos hv₁]
      split at hv
      · next hlt =>
        rw [if_pos hlt]
        exact ih _ (Nat.lt_of_lt_of_le hlt (Nat.le_trans hle (Nat.le_of_lt_succ hm))) hv
      · next hnlt =>
        rw [if_neg hnlt]
        exact cimaOk_of_noProgress sides _ hv₁ hnlt
    · next hv₁ => exact absurd hv hv₁

theorem cimaOk_reviewCima (sides : List GPathM) (g : GPathM)
    (hv : isValid (reviewCima sides g) = true) : CimaOk sides (reviewCima sides g) :=
  cimaOk_reviewCimaFuel sides _ g (Nat.lt_succ_self _) hv

/-- **And so does the whole filter of a union**: pins, then that review. -/
theorem cimaOk_filterAllCima (sides : List GPathM) (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAllCima sides g reqs) = true) :
    CimaOk sides (filterAllCima sides g reqs) :=
  cimaOk_reviewCima sides _ hv

-- ============================================================
-- The machine: the line advance with the sides
-- ============================================================

open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves (pureAdvanceW)
open AbsSat.GraphPath.Model.BranchLines (sent)

variable (φ : Cnf)

/-- The sides that build the union of key `p`: the valid sends of the line into `p`. -/
def sidesOf (L : PureLine) (p : NodeId) : List GPathM :=
  L.filterMap (fun kv =>
    if (mapSons φ kv.1.step kv.1.index).contains p && isValid (sent φ kv.2 p) then
      some (sent φ kv.2 p)
    else none)

/-- **One line of `ImprovesCima`**: the line of `Improves`, and then, per key, the review of the union
with the rule of the top, which reads the sides that built it. -/
def advanceCima (L : PureLine) : PureLine :=
  (pureAdvanceW φ L).map (fun kv => (kv.1, reviewCima (sidesOf φ L kv.1) kv.2))

def stepsCima : Nat → PureLine → PureLine
  | 0, L => L
  | n + 1, L => stepsCima n (advanceCima φ L)

/-- The whole run. An empty result is the UNSAT answer, as in `Improves`. -/
def runCima : PureLine := stepsCima φ (stepCount φ - 1).toNat (pureInit φ)

/-- Each state of a line of `ImprovesCima` is a narrowing of the same state in `Improves`. -/
theorem keeps_advanceCima (L : PureLine) (kv : NodeId × GPathM) (hkv : kv ∈ advanceCima φ L) :
    ∃ g, (kv.1, g) ∈ pureAdvanceW φ L ∧ Keeps g kv.2 := by
  obtain ⟨kv', hkv', he⟩ := List.mem_map.mp hkv
  refine ⟨kv'.2, ?_, ?_⟩
  · rw [show kv.1 = kv'.1 from by rw [← he]]; exact hkv'
  · rw [← he]; exact keeps_reviewCima _ _

/-- **The review of a union loses no solution.** A chain that is sound in the union and in one of its
sides survives the pins and the whole review: the rule never touches it, because its own top is good. -/
theorem ChainSound_reviewCima_of_side (sides : List GPathM) (g S : GPathM) (hS : S ∈ sides)
    (sel : Int → PathNodeId) (h : ChainSound g sel) (hSc : ChainSound S sel)
    (hcsS : S.current_step = g.current_step)
    (hcs : 0 < g.current_step) : ChainSound (reviewCima sides g) sel :=
  ChainSound_reviewCima sides g sel h (carried_of_side sides g S hS sel hSc hcsS hcs)

theorem SMP_cimaPair (sides : List GPathM) (g : GPathM) (hs : Sons.SMP g) (x w : PathNodeId) :
    Sons.SMP (cimaPair sides g x w) := SMP_prunePair _ g hs x w

theorem sons_cimaSweep (sides : List GPathM) (g : GPathM) (hsmp : Sons.SMP g) (hpms : Sons.PMS g)
    (hsn : Sons.SN g) :
    Sons.SMP (cimaSweep sides g) ∧ Sons.PMS (cimaSweep sides g) ∧ Sons.SN (cimaSweep sides g) :=
  sons_pruneSweep _ g hsmp hpms hsn

-- ============================================================
-- The top names the side
-- ============================================================

open AbsSat.GraphPath.Model.ReaderAggRun (MInv)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.PinHistory (branchLine branchLine_inv)
open AbsSat.GraphPath.Model.PinDeath (topOf)

/-- **The only node a send has at its new step is its own top.** -/
theorem sent_top (m : Nat) (kv : NodeId × GPathM) (hsok : StateOkF φ m kv)
    (hmkv : MInv φ kv.2) (d : NodeId) (hv : isValid (sent φ kv.2 d) = true)
    (n' : PNodeM) (hn' : n' ∈ (sent φ kv.2 d).nodes) (hs : n'.id.id.step = (m : Int) + 1) :
    n'.id = topOf d kv.1 := by
  have hvF := ClauseReview.valid_pinned φ kv.2 d hv
  have heq : sent φ kv.2 d = addNode (ClauseReview.pinnedAt φ kv.2 d) d "" := by
    rw [ClauseReview.sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  have hprF : Pruned kv.2 (ClauseReview.pinnedAt φ kv.2 d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (AggressiveReview.pruned_filterAllAgg _ _)
  have hcsF : (ClauseReview.pinnedAt φ kv.2 d).current_step = (m : Int) + 1 := by
    rw [hprF.step_eq, hsok.step]
  have hmpF : (ClauseReview.pinnedAt φ kv.2 d).map_parent = some kv.1 := by
    rw [hprF.map_parent_eq, hsok.par]
  have hRF : ReaderAgg.ReadableAgg (ClauseReview.pinnedAt φ kv.2 d) :=
    ⟨_, _, ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmkv.rctx, rfl⟩
  have hbelow : ∀ x ∈ (ClauseReview.pinnedAt φ kv.2 d).nodes,
      x.id.id.step < (ClauseReview.pinnedAt φ kv.2 d).current_step :=
    (ReaderAgg.RCtx_of_readableAgg _ hRF).below
  rw [heq] at hn'
  have htop := RunNoBorrow.tops_addNode (ClauseReview.pinnedAt φ kv.2 d) d "" hbelow n' hn'
    (by rw [hcsF]; exact hs)
  rw [htop, hmpF]; rfl

/-- **The top names the side.** A side of a union that holds the top `⟨p, key⟩` of the key `key` IS the
send of that key: the send has exactly one node at the new step, its own top, and the keys of a line are
distinct. This is what lets the rule read one single table: every `carries` a good top grants speaks of
the same side. -/
theorem side_of_top (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId)
    (hps : p.step = (m : Int) + 1)
    (S : GPathM) (hS : S ∈ sidesOf φ (branchLine φ P m) p)
    (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m)
    (ht : (S.node? (topOf p kv.1)).isSome = true) :
    S = sent φ kv.2 p := by
  have hl := branchLine_inv φ hwf P m
  obtain ⟨kv', hkv', hfe⟩ := List.mem_filterMap.mp hS
  by_cases hc : ((mapSons φ kv'.1.step kv'.1.index).contains p && isValid (sent φ kv'.2 p)) = true
  · rw [if_pos hc] at hfe
    have hSe : S = sent φ kv'.2 p := by injection hfe with h; exact h.symm
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ht
    have hnid : n.id = topOf p kv.1 := node?_id_eq _ _ n hn
    have hmem : n ∈ S.nodes := List.mem_of_find?_eq_some hn
    rw [hSe] at hmem
    have hstep : n.id.id.step = (m : Int) + 1 := by rw [hnid]; exact hps
    have hv' : isValid (sent φ kv'.2 p) = true := by
      simp only [Bool.and_eq_true] at hc; exact hc.2
    have hkeys : kv'.1 = kv.1 := by
      have := sent_top φ m kv' (hl.1.2 kv' hkv') (hl.2 kv' hkv') p hv' n hmem hstep
      rw [hnid] at this
      have : topOf p kv.1 = topOf p kv'.1 := this
      simpa [topOf] using this.symm
    rw [hSe, PureDriver.key_inj _ hl.1.1 kv' hkv' kv hkv hkeys]
  · rw [if_neg hc] at hfe; contradiction

/-- **What a good top hands over, in the side's own table.** Because the top names the side, every pair
the rule certifies with `carries` is a pair of that one side — which is exactly what the support of the
side's send needs. -/
theorem carries_in_side (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m)
    (a b : PathNodeId)
    (hc : carries (sidesOf φ (branchLine φ P m) p) (topOf p kv.1) a b = true) :
    Rel (sent φ kv.2 p) a b ∧ Rel (sent φ kv.2 p) b a := by
  obtain ⟨S, hS, hcond⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true] at hcond
  have hSe := side_of_top φ hwf P m p hps S hS kv hkv hcond.1.1
  rw [hSe] at hcond
  exact rel_of_owners _ a b hcond.1.2 hcond.2

/-- **From a live entry at the fixpoint to a good top.** Reading `cimaOk` backwards: the top is a node of
the last line, and `fam_closure` then gives the whole closure for it. -/
theorem top_of_cimaOk (sides : List GPathM) (g : GPathM) (a b : PathNodeId)
    (hok : cimaOk sides g a b = true) :
    ∃ t, t.id.step = g.current_step - 1 ∧ goodFor sides g t a b = true := by
  simp only [cimaOk] at hok
  obtain ⟨t, ht, hgood⟩ := List.any_eq_true.mp hok
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ht
  exact ⟨n.id, eq_of_beq (List.mem_filter.mp hn).2, hgood⟩

/-- **The parent link the side holds.** Same reading as `carries_in_side`, for the parent lists: what
the test keeps on neighbouring steps is a parent link of that one side. -/
theorem linked_in_side (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m)
    (a b : PathNodeId)
    (hl : linkedIn (sidesOf φ (branchLine φ P m) p) (topOf p kv.1) a b = true) :
    ∃ na, (sent φ kv.2 p).node? a = some na ∧ b ∈ na.parents := by
  obtain ⟨S, hS, hcond⟩ := List.any_eq_true.mp hl
  simp only [Bool.and_eq_true] at hcond
  have hSe := side_of_top φ hwf P m p hps S hS kv hkv hcond.1
  rw [hSe] at hcond
  cases hsa : (sent φ kv.2 p).node? a with
  | none => rw [hsa] at hcond; exact (Bool.false_ne_true hcond.2).elim
  | some na => rw [hsa] at hcond; exact ⟨na, rfl, List.contains_iff_mem.mp hcond.2⟩

/-- **What the family of a top gives, read in the side.** Every entry the family keeps is an entry of
the side's send, both ways; and on neighbouring steps it is one of its parent links. -/
theorem side_of_famFix (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m)
    (g : GPathM) (hnd : ((restAll (sidesOf φ (branchLine φ P m) p) (topOf p kv.1) g).nodes.map
      (·.id)).Nodup)
    (hv : isValid (famFix (sidesOf φ (branchLine φ P m) p) (topOf p kv.1) g) = true)
    (a b : PathNodeId) (h : Rel (famFix (sidesOf φ (branchLine φ P m) p) (topOf p kv.1) g) a b)
    (ha0 : 0 ≤ a.id.step) (ha1 : a.id.step < g.current_step)
    (hb0 : 0 ≤ b.id.step) (hb1 : b.id.step < g.current_step) :
    Rel (sent φ kv.2 p) a b ∧ Rel (sent φ kv.2 p) b a ∧
      (b.id.step + 1 = a.id.step → ∃ na, (sent φ kv.2 p).node? a = some na ∧ b ∈ na.parents) := by
  have ht := restTest_of_famFix _ _ g hnd hv a b h ha0 ha1 hb0 hb1
  simp only [restTest, Bool.and_eq_true] at ht
  refine ⟨(carries_in_side φ hwf P m p hps kv hkv a b ht.1.1.1).1,
    (carries_in_side φ hwf P m p hps kv hkv a b ht.1.1.1).2, fun hstep => ?_⟩
  have hbe : (b.id.step + 1 == a.id.step) = true := beq_iff_eq.mpr hstep
  have := ht.1.2
  rw [hbe] at this
  exact linked_in_side φ hwf P m p hps kv hkv a b (by simpa using this)

-- ============================================================
-- The support of the side, assembled
-- ============================================================

/-- **The family is a support of the side's send.** Everything about the family itself — cover,
aggregation, symmetry — is its own support, because it is a review fixpoint. Everything that speaks of
the side — that its pairs are the side's, that a parent of the family is a parent of the side — is what
the restriction test guarantees. Putting the two together gives a support of the send. -/
theorem sup_of_famSide (Y S : GPathM)
    (hY : AnchoredSurvive.Sup Y (EmbeddedSupport.Mem Y) (Rel Y))
    (hadj : AdjacentOwners.Adj Y) (hcs : Y.current_step = S.current_step)
    (hside : ∀ a b, Rel Y a b → Rel S a b ∧ Rel S b a ∧
      (b.id.step + 1 = a.id.step → ∃ na, S.node? a = some na ∧ b ∈ na.parents))
    (hgow : ∀ q n, S.node? q = some n → ∀ z ∈ n.owners, 0 ≤ z.id.step →
      z.id.step < S.current_step → z ∈ S.gowners) :
    AnchoredSurvive.Sup S (EmbeddedSupport.Mem Y) (Rel Y) := by
  have hbnd : ∀ q, EmbeddedSupport.Mem Y q → 0 ≤ q.id.step ∧ q.id.step < S.current_step := by
    intro q hq
    have := EmbeddedSupport.mem_bounds Y hadj hq
    rw [hcs] at this; exact this
  have hone : ∀ q, EmbeddedSupport.Mem Y q → ∃ v, Rel Y q v := by
    intro q hq
    obtain ⟨v, hv, _⟩ := hY.cov q hq 0 (Int.le_refl 0)
      (by have := EmbeddedSupport.mem_bounds Y hadj hq; omega)
    exact ⟨v, hv⟩
  refine ⟨?_, ?_, hbnd, hY.dom, ?_, ?_, ?_, ?_, ?_, hY.sym, ?_⟩
  · intro q hq
    obtain ⟨v, hv⟩ := hone q hq
    obtain ⟨n, hn, hmem, _⟩ := (hside q v hv).2.1
    exact hgow v n hn q hmem (hbnd q hq).1 (hbnd q hq).2
  · intro q hq
    obtain ⟨v, hv⟩ := hone q hq
    obtain ⟨n, hn, _, _⟩ := (hside q v hv).1
    rw [hn]; rfl
  · intro x v n hr hn
    obtain ⟨n', hn', hmem, _⟩ := (hside x v hr).1
    rw [hn] at hn'; cases hn'; exact hmem
  · intro x hx l hl0 hl1
    exact hY.cov x hx l hl0 (by rw [hcs]; exact hl1)
  · intro x d hx hn hroot v hr
    obtain ⟨dY, hdY⟩ := id hx
    obtain ⟨c, hcpar, h1, h2, h3⟩ := hY.par x dY hx hdY hroot v hr
    have hstep : c.id.step + 1 = x.id.step := by
      have hid : dY.id = x := node?_id_eq Y x dY hdY
      have := hadj.rc.shape.pbelow dY (List.mem_of_find?_eq_some hdY) c hcpar
      rw [hid] at this; omega
    obtain ⟨na, hna, hmem⟩ := (hside x c h1).2.2 hstep
    rw [hn] at hna; cases hna
    exact ⟨c, hmem, h1, h2, h3⟩
  · intro x hx hne v hr
    obtain ⟨c, mY, hmY, hxpar, h1, h2, h3⟩ := hY.son x hx (by rw [hcs]; exact hne) v hr
    have hstep : x.id.step + 1 = c.id.step := by
      have hid : mY.id = c := node?_id_eq Y c mY hmY
      have := hadj.rc.shape.pbelow mY (List.mem_of_find?_eq_some hmY) x hxpar
      rw [hid] at this; omega
    obtain ⟨mc, hmc, hmem⟩ := (hside c x h2).2.2 hstep
    exact ⟨c, mc, hmc, hmem, h1, h2, h3⟩
  · intro x v hr l hl0 hl1
    exact hY.agg x v hr l hl0 (by rw [hcs]; exact hl1)
  · intro x c d h1 h2 hstep hn
    obtain ⟨na, hna, hmem⟩ := (hside x c h1).2.2 hstep
    rw [hn] at hna; cases hna; exact hmem

/-! **What is left for the verdict of `ImprovesCima`.** The review of a union leaves every live entry
with a good top (`cimaOk_filterAllCima`), that is: alive in the family the top names, which is a live
state of the machine's own kind whose entries are entries of that one side. What remains is to read the
support out of it — `LinkedChain.sup_self` gives the support of that family, and the restriction test
carries it over to the side's send — and to close `HereditaryValid.ChainClosureAt` with it. -/
/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.AOk_filterAllCima' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AOk_filterAllCima

end AbsSat.GraphPath.Model.ImprovesCima
