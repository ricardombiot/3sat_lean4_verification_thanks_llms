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

-- ============================================================
-- The chain of common owners, computed
-- ============================================================

/-- The nodes of step `k` that own both `a` and `b`, both ways. -/
def commonAt (g : GPathM) (a b : PathNodeId) (k : Int) : List PathNodeId :=
  ((g.line k).map (·.id)).filter (fun c =>
    (ownersOf g c).contains a && (ownersOf g c).contains b &&
      (ownersOf g a).contains c && (ownersOf g b).contains c)

/-- One step of the chain: `c` can carry on upwards when one of the nodes already reached is a son of
`c` — read from that node's parents, which a narrowing only shrinks — and the two own each other. -/
def climbs (g : GPathM) (up : List PathNodeId) (c : PathNodeId) : Bool :=
  up.any (fun s => match g.node? s with
    | some ns => ns.parents.contains c && (ownersOf g c).contains s && (ownersOf g s).contains c
    | none => false)

/-- The nodes that reach the top `t` by a chain of common owners, `n` steps below the last one. -/
def climbTo (g : GPathM) (a b t : PathNodeId) : Nat → List PathNodeId
  | 0 => if (commonAt g a b (g.current_step - 1)).contains t then [t] else []
  | n + 1 =>
    (commonAt g a b (g.current_step - 1 - ((n : Int) + 1))).filter
      (fun c => climbs g (climbTo g a b t n) c)

/-- Does a chain of common owners of `a` and `b` reach the top `t`, starting at `a`? -/
def reaches (g : GPathM) (a b t : PathNodeId) : Bool :=
  (climbTo g a b t (g.current_step - 1 - a.id.step).toNat).contains a

/-- The tops such a chain reaches. -/
def reachTops (g : GPathM) (a b : PathNodeId) : List PathNodeId :=
  ((g.line (g.current_step - 1)).map (·.id)).filter (fun t => reaches g a b t)

-- ============================================================
-- The first bridge: an explicit chain is found by the search
-- ============================================================

open AbsSat.GraphPath.Model.EmbeddedSupport (Rel)
open AbsSat.GraphPath.Model.PinDeath (ChainUp2)

theorem mem_commonAt (g : GPathM) (a b c : PathNodeId) (n : PNodeM) (hn : g.node? c = some n)
    (h1 : Rel g c a) (h2 : Rel g c b) (h3 : Rel g a c) (h4 : Rel g b c) :
    c ∈ commonAt g a b c.id.step := by
  have hmem : c ∈ (g.line c.id.step).map (·.id) := mem_line_of_node? g c n hn _ rfl
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  have how : ∀ x y, Rel g x y → (ownersOf g x).contains y = true := by
    intro x y hxy
    obtain ⟨m, hm, hy, _⟩ := hxy
    unfold ownersOf; rw [hm]; exact List.contains_iff_mem.mpr hy
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨how c a h1, how c b h2⟩, how a c h3⟩, how b c h4⟩

/-- **The search finds an explicit chain.** If a chain of common owners of `a` and `b`, linked by
parents, goes from `c` up to the top `t`, the search the rule runs reaches `t` from `c`. -/
theorem climbTo_of_chain (g : GPathM) (a b t : PathNodeId) :
    ∀ (c : PathNodeId), ChainUp2 g a b c t → ∀ nc, g.node? c = some nc →
      Rel g c a → Rel g c b → Rel g a c → Rel g b c →
      c ∈ climbTo g a b t (g.current_step - 1 - c.id.step).toNat := by
  intro c hchain
  induction hchain with
  | top t' h =>
    intro nc hnc h1 h2 h3 h4
    have hz : (g.current_step - 1 - t'.id.step).toNat = 0 := by rw [h]; simp
    rw [hz]
    have hmem : t' ∈ commonAt g a b (g.current_step - 1) := by
      rw [← h]; exact mem_commonAt g a b t' nc hnc h1 h2 h3 h4
    show t' ∈ (if (commonAt g a b (g.current_step - 1)).contains t' then [t'] else [])
    rw [if_pos (List.contains_iff_mem.mpr hmem)]
    exact List.mem_singleton_self _
  | link c s t' ns hns hpar hstep hc0 hs1 hc hc' ha hz h1 h2 h3 h4 h3' h4' hrest ih =>
    intro nc hnc hca hcb hac hbc
    have hIH := ih ns hns h3 h4 h3' h4'
    have hidx : (g.current_step - 1 - c.id.step).toNat
        = (g.current_step - 1 - s.id.step).toNat + 1 := by omega
    rw [hidx]
    show c ∈ (commonAt g a b (g.current_step - 1 - (((g.current_step - 1 - s.id.step).toNat : Int) + 1))).filter
      (fun c' => climbs g (climbTo g a b t' (g.current_step - 1 - s.id.step).toNat) c')
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · have : g.current_step - 1 - (((g.current_step - 1 - s.id.step).toNat : Int) + 1) = c.id.step := by
        omega
      rw [this]
      exact mem_commonAt g a b c nc hnc hca hcb hac hbc
    · refine List.any_eq_true.mpr ⟨s, hIH, ?_⟩
      have how : ∀ x y, Rel g x y → (ownersOf g x).contains y = true := by
        intro x y hxy
        obtain ⟨m, hm, hy, _⟩ := hxy
        unfold ownersOf; rw [hm]; exact List.contains_iff_mem.mpr hy
      simp only [hns, Bool.and_eq_true]
      exact ⟨⟨List.contains_iff_mem.mpr hpar, how c s h1⟩, how s c h2⟩

/-- **A chain from `a` makes its top reachable.** -/
theorem reaches_of_chain (g : GPathM) (a b t : PathNodeId) (h : ChainUp2 g a b a t)
    (na : PNodeM) (hna : g.node? a = some na) (h1 : Rel g a a) (h2 : Rel g a b) (h3 : Rel g b a) :
    reaches g a b t = true :=
  List.contains_iff_mem.mpr (climbTo_of_chain g a b t a h na hna h1 h2 h1 h3)

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

/-- The witness of every step: a common owner of `a` and `b` that the side of `t` carries with both. -/
def stepOk (sides : List GPathM) (g : GPathM) (t a b : PathNodeId) : Bool :=
  (intRange 0 (g.current_step - 1)).all (fun k =>
    ((g.line k).map (·.id)).any (fun z =>
      (ownersOf g a).contains z && (ownersOf g b).contains z &&
        (ownersOf g z).contains a && (ownersOf g z).contains b &&
        carries sides t a z && carries sides t b z))

/-- A parent of `a` the side of `t` carries with `a` and with `b`. -/
def parOk (sides : List GPathM) (g : GPathM) (t a b : PathNodeId) : Bool :=
  a.parent_id.isNone ||
    (ownersOf g a).any (fun c => c.id.step + 1 == a.id.step &&
      carries sides t a c && carries sides t c a && carries sides t c b &&
      (ownersOf g c).contains a)

/-- A son of `a` the side of `t` carries with `a` and with `b`. -/
def sonOk (sides : List GPathM) (g : GPathM) (t a b : PathNodeId) : Bool :=
  a.id.step == g.current_step - 1 ||
    (ownersOf g a).any (fun c => a.id.step + 1 == c.id.step &&
      carries sides t a c && carries sides t c a && carries sides t c b &&
      (ownersOf g c).contains a)

/-- On neighbouring steps, the side of `t` links the pair as parent and son. -/
def linkOk (sides : List GPathM) (_g : GPathM) (t a b : PathNodeId) : Bool :=
  !(b.id.step + 1 == a.id.step) ||
    sides.any (fun S => (S.node? t).isSome &&
      (match S.node? a with | none => false | some na => na.parents.contains b))

/-- Is the entry good for the top `t`: a chain of common owners reaches `t`, a side of `t` carries the
entry, and the closure the verdict asks for holds with witnesses the same side carries. -/
def goodFor (sides : List GPathM) (g : GPathM) (t a b : PathNodeId) : Bool :=
  reaches g a b t && carries sides t a b && stepOk sides g t a b &&
    parOk sides g t a b && sonOk sides g t a b && linkOk sides g t a b

/-- **The rule of the top.** An entry stays only if some top is good for it. A genuine path gives one:
its own top, with its own nodes as witnesses. -/
def cimaOk (sides : List GPathM) (g : GPathM) (a b : PathNodeId) : Bool :=
  ((g.line (g.current_step - 1)).map (·.id)).any (fun t => goodFor sides g t a b)

-- ============================================================
-- The sweep
-- ============================================================

/-- **The rule of the top, for one entry.** If some top the pair's chain reaches has a side that does not
carry the pair, the two stop owning each other. -/
def cimaPair (sides : List GPathM) (g : GPathM) (x w : PathNodeId) : GPathM :=
  match g.node? x, g.node? w with
  | some nx, some nw =>
    if nx.owners.contains w && !cimaOk sides g x w then
      dropOwnerPair g x w nx.owners nw.owners
    else g
  | _, _ => g

def cimaNode (sides : List GPathM) (g : GPathM) (x : PathNodeId) : GPathM :=
  match g.node? x with
  | none => g
  | some nx => nx.owners.foldl (fun g w => cimaPair sides g x w) g

/-- The sweep: every node, from the last step down. -/
def cimaSweep (sides : List GPathM) (g : GPathM) : GPathM :=
  if isValid g then
    (intRange 0 (g.current_step - 1)).reverse.foldl
      (fun g k => ((g.line k).map (·.id)).foldl (cimaNode sides) g) g
  else g

-- ============================================================
-- The sweep only removes
-- ============================================================

theorem keeps_cimaPair (sides : List GPathM) (g : GPathM) (x w : PathNodeId) :
    Keeps g (cimaPair sides g x w) := by
  unfold cimaPair
  split
  · split
    · exact Keeps.trans (ReaderAgg.keeps_updateAt_uniMap _ _ _)
        (ReaderAgg.keeps_updateAt_uniMap _ _ _)
    · exact Keeps.refl g
  · exact Keeps.refl g

theorem keeps_cimaNode (sides : List GPathM) (g : GPathM) (x : PathNodeId) :
    Keeps g (cimaNode sides g x) := by
  unfold cimaNode
  cases hx : g.node? x with
  | none => exact Keeps.refl g
  | some nx => exact ReaderAgg.keeps_foldl _ (fun g w => keeps_cimaPair sides g x w) _ _

theorem keeps_cimaSweep (sides : List GPathM) (g : GPathM) : Keeps g (cimaSweep sides g) := by
  unfold cimaSweep
  split
  · exact ReaderAgg.keeps_foldl _
      (fun g k => ReaderAgg.keeps_foldl _ (fun g x => keeps_cimaNode sides g x) _ _) _ _
  · exact Keeps.refl g

-- ============================================================
-- The core: no solution is lost
-- ============================================================

open AbsSat.GraphPath.Model.AggressiveReview (mem_dropList chain_mem_owners)

/-- **One entry: the rule never separates two nodes of a sound chain** whose reached tops the sides
carry. Off the chain it only removes, as every drop does. -/
theorem ChainSound_cimaPair (sides : List GPathM) (g : GPathM) (x w : PathNodeId)
    (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hcar : ∀ i j, 0 ≤ i → i < g.current_step → 0 ≤ j → j < g.current_step → sel i = x → sel j = w →
      cimaOk sides g x w = true) :
    ChainSound (cimaPair sides g x w) sel := by
  unfold cimaPair
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
def Carried (sides : List GPathM) (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ g', Keeps g g' → ChainSound g' sel → ∀ i j, 0 ≤ i → i < g'.current_step → 0 ≤ j →
    j < g'.current_step → cimaOk sides g' (sel i) (sel j) = true

theorem ChainSound_cimaNode (sides : List GPathM) (g g₀ : GPathM) (x : PathNodeId)
    (sel : Int → PathNodeId) (hk : Keeps g₀ g) (h : ChainSound g sel) (hC : Carried sides g₀ sel) :
    ChainSound (cimaNode sides g x) sel ∧ Keeps g₀ (cimaNode sides g x) := by
  refine ⟨?_, Keeps.trans hk (keeps_cimaNode sides g x)⟩
  unfold cimaNode
  split
  · exact h
  · next nx _ =>
    refine BranchLines.foldl_inv (fun g' w => cimaPair sides g' x w)
      (fun g' => ChainSound g' sel ∧ Keeps g₀ g') nx.owners ?_ g ⟨h, hk⟩ |>.1
    intro g' w _ hg'
    refine ⟨ChainSound_cimaPair sides g' x w sel hg'.1 ?_, Keeps.trans hg'.2 (keeps_cimaPair _ _ _ _)⟩
    intro i j hi0 hi hj0 hj hix hjw
    have := hC g' hg'.2 hg'.1 i j hi0 hi hj0 hj
    rw [hix, hjw] at this
    exact this

/-- **The sweep loses no solution.** -/
theorem ChainSound_cimaSweep (sides : List GPathM) (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (hC : Carried sides g sel) : ChainSound (cimaSweep sides g) sel := by
  unfold cimaSweep
  split
  · refine BranchLines.foldl_inv
      (fun g' k => ((g'.line k).map (·.id)).foldl (cimaNode sides) g')
      (fun g' => ChainSound g' sel ∧ Keeps g g') _ ?_ g ⟨h, Keeps.refl g⟩ |>.1
    intro g' k _ hg'
    refine BranchLines.foldl_inv (cimaNode sides) (fun g'' => ChainSound g'' sel ∧ Keeps g g'')
      _ ?_ g' hg'
    intro g'' x _ hg''
    exact ChainSound_cimaNode sides g'' g x sel hg''.2 hg''.1 hC
  · exact h

-- ============================================================
-- The core: a support survives
-- ============================================================

open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk Sup_updateAt)

variable {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- **One entry: the rule never drops a pair of a support** whose reached tops the sides carry. -/
theorem Sup_cimaPair (sides : List GPathM) (g : GPathM) (h : Sup g S R) (x w : PathNodeId)
    (hcar : R x w → cimaOk sides g x w = true) :
    Sup (cimaPair sides g x w) S R := by
  unfold cimaPair
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

theorem SMP_cimaPair (sides : List GPathM) (g : GPathM) (hs : Sons.SMP g) (x w : PathNodeId) :
    Sons.SMP (cimaPair sides g x w) := by
  unfold cimaPair
  split
  · split
    · exact Sons.SMP_updateAt _ w _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (Sons.SMP_updateAt g x _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hs)
    · exact hs
  · exact hs

theorem AOk_cimaPair (sides : List GPathM) (g : GPathM) (h : AOk g S R) (x w : PathNodeId)
    (hcar : R x w → cimaOk sides g x w = true) :
    AOk (cimaPair sides g x w) S R :=
  ⟨Sup_cimaPair sides g h.sup x w hcar, SMP_cimaPair sides g h.smp x w,
    Parents.NotRoot_of_pruned (keeps_cimaPair sides g x w).1 h.nr⟩

/-- The rule's hypothesis for a support, robust along the sweep. -/
def CarriedR (sides : List GPathM) (g : GPathM) (R : PathNodeId → PathNodeId → Prop) : Prop :=
  ∀ g', Keeps g g' → ∀ x v, R x v → cimaOk sides g' x v = true

theorem AOk_cimaNode (sides : List GPathM) (g g₀ : GPathM) (x : PathNodeId) (hk : Keeps g₀ g)
    (h : AOk g S R) (hC : CarriedR sides g₀ R) : AOk (cimaNode sides g x) S R ∧ Keeps g₀ (cimaNode sides g x) := by
  refine ⟨?_, Keeps.trans hk (keeps_cimaNode sides g x)⟩
  unfold cimaNode
  split
  · exact h
  · next nx _ =>
    refine BranchLines.foldl_inv (fun g' w => cimaPair sides g' x w)
      (fun g' => AOk g' S R ∧ Keeps g₀ g') nx.owners ?_ g ⟨h, hk⟩ |>.1
    intro g' w _ hg'
    exact ⟨AOk_cimaPair sides g' hg'.1 x w (fun hr => hC g' hg'.2 x w hr),
      Keeps.trans hg'.2 (keeps_cimaPair _ _ _ _)⟩

/-- **A support survives the sweep.** The rule only drops pairs whose chain reaches a top the sides do
not carry, and a support's pairs are carried by hypothesis; everything else it removes leaves the support
where it was. -/
theorem AOk_cimaSweep (sides : List GPathM) (g : GPathM) (h : AOk g S R) (hC : CarriedR sides g R) :
    AOk (cimaSweep sides g) S R := by
  unfold cimaSweep
  split
  · refine BranchLines.foldl_inv
      (fun g' k => ((g'.line k).map (·.id)).foldl (cimaNode sides) g')
      (fun g' => AOk g' S R ∧ Keeps g g') _ ?_ g ⟨h, Keeps.refl g⟩ |>.1
    intro g' k _ hg'
    refine BranchLines.foldl_inv (cimaNode sides) (fun g'' => AOk g'' S R ∧ Keeps g g'')
      _ ?_ g' hg'
    intro g'' x _ hg''
    exact AOk_cimaNode sides g'' g x hg''.2 hg''.1 hC
  · exact h

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.ChainSound_cimaSweep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_cimaSweep

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.AOk_cimaSweep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AOk_cimaSweep


-- ============================================================
-- The fixpoint: at the end, every entry has a good top
-- ============================================================

open AbsSat.GraphPath.Model.AggFixpoint (EqOrLt eqOrLt_foldl foldl_noProgress weight_drop_lt
  weight_uniMap_le measure_updateAt_uniMap_lt mem_reverse_intRange)

theorem cimaPair_eqOrLt (sides : List GPathM) (g : GPathM) (x w : PathNodeId) :
    EqOrLt g (cimaPair sides g x w) := by
  unfold cimaPair
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

theorem measure_cimaPair_lt (sides : List GPathM) (g : GPathM) (x w : PathNodeId) (nx nw : PNodeM)
    (hx : g.node? x = some nx) (hw : g.node? w = some nw) (hmem : w ∈ nx.owners)
    (hfire : cimaOk sides g x w = false) :
    GPathM.measure (cimaPair sides g x w) < GPathM.measure g := by
  have hcw : nx.owners.contains w = true := List.contains_iff_mem.mpr hmem
  have heq : cimaPair sides g x w = dropOwnerPair g x w nx.owners nw.owners := by
    unfold cimaPair
    rw [hx, hw]
    simp only [hcw, hfire, Bool.not_false, Bool.and_self, if_pos]
  rw [heq]
  refine Nat.lt_of_le_of_lt ?_ (measure_updateAt_uniMap_lt g x _ nx hx (weight_drop_lt nx w hmem))
  exact GPathM.measure_updateAt_le _ w _ (fun n => weight_uniMap_le _ n)

/-- **The test the rule leaves behind**: every live entry has a good top. -/
def CimaOk (sides : List GPathM) (g : GPathM) : Prop :=
  ∀ x nx w, g.node? x = some nx → (g.node? w).isSome = true →
    0 ≤ x.id.step → x.id.step < g.current_step →
    0 ≤ w.id.step → w.id.step < g.current_step →
    w ∈ nx.owners → cimaOk sides g x w = true

/-- **If the sweep does not lower the measure of a valid state, the state passes the test.** -/
theorem cimaOk_of_noProgress (sides : List GPathM) (g : GPathM) (hv : isValid g = true)
    (hnp : ¬ GPathM.measure (cimaSweep sides g) < GPathM.measure g) : CimaOk sides g := by
  intro x nx w hx hw hx1 hx2 hw1 hw2 hmem
  cases hok : cimaOk sides g x w with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨nw, hnw⟩ := Option.isSome_iff_exists.mp hw
    have hsweep : cimaSweep sides g = (intRange 0 (g.current_step - 1)).reverse.foldl
        (fun g k => ((g.line k).map (·.id)).foldl (cimaNode sides) g) g := by
      unfold cimaSweep
      rw [if_pos hv]
    rw [hsweep] at hnp
    have hnodeEq : ∀ g' (x' : PathNodeId), EqOrLt g' (cimaNode sides g' x') := by
      intro g' x'
      unfold cimaNode
      split
      · exact Or.inl rfl
      · next nx' _ => exact eqOrLt_foldl _ (fun g'' w' => cimaPair_eqOrLt sides g'' x' w') _ g'
    have houter := foldl_noProgress _
      (fun g' k => eqOrLt_foldl _ (fun g'' x' => hnodeEq g'' x') _ g') _ g hnp x.id.step
      (mem_reverse_intRange hx1 (by omega))
    have hline : x ∈ (g.line x.id.step).map (·.id) := mem_line_of_node? g x nx hx _ rfl
    have hinner := foldl_noProgress _ (fun g' x' => hnodeEq g' x') _ g
      (by rw [houter]; exact Nat.lt_irrefl _) x hline
    have hfold : nx.owners.foldl (fun g' w' => cimaPair sides g' x w') g = g := by
      have : cimaNode sides g x = nx.owners.foldl (fun g' w' => cimaPair sides g' x w') g := by
        unfold cimaNode; rw [hx]
      rw [← this]; exact hinner
    have hpair := foldl_noProgress _ (fun g' w' => cimaPair_eqOrLt sides g' x w') _ g
      (by rw [hfold]; exact Nat.lt_irrefl _) w hmem
    have hlt := measure_cimaPair_lt sides g x w nx nw hx hnw hmem hok
    rw [hpair] at hlt
    exact Nat.lt_irrefl _ hlt

-- ============================================================
-- The review of a union: the aggressive review and the rule, to their fixpoint
-- ============================================================

open AbsSat.GraphPath.Model.AggressiveReview (reviewAgg ChainSound_reviewAgg)
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

/-- **A sound chain is a chain of common owners up to its own top.** -/
theorem chainUp2_of_chainSound (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hcs : 0 < g.current_step) (i j : Int) (hi0 : 0 ≤ i) (hj0 : 0 ≤ j) (hj : j < g.current_step) :
    ∀ (n : Nat) (c : Int), c = g.current_step - 1 - (n : Int) → i ≤ c → 0 ≤ c →
      ChainUp2 g (sel i) (sel j) (sel c) (sel (g.current_step - 1)) := by
  intro n
  induction n with
  | zero =>
    intro c hc _ _
    have : c = g.current_step - 1 := by omega
    rw [this]
    exact ChainUp2.top _ (h.chain.1.1 (g.current_step - 1) (by omega) (by omega)).2
  | succ n ih =>
    intro c hc hic hc0
    have hlt : c + 1 = g.current_step - 1 - (n : Int) := by omega
    have hb : c < g.current_step := by omega
    have hb1 : c + 1 < g.current_step := by omega
    have hrest := ih (c + 1) hlt (by omega) (by omega)
    obtain ⟨ns, hns⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 (c + 1) (by omega) hb1).1
    have hpar : sel c ∈ ns.parents := by
      have := h.chain.1.2 c hc0 hb1
      rw [hns] at this; simpa using this
    have hstep : (sel c).id.step + 1 = (sel (c + 1)).id.step := by
      rw [(h.chain.1.1 c hc0 hb).2, (h.chain.1.1 (c + 1) (by omega) hb1).2]
    have how : ∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step → p ≠ q →
        Rel g (sel p) (sel q) := by
      intro p q hp0 hp hq0 hq hne
      obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 p hp0 hp).1
      obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 q hq0 hq).1
      refine ⟨np, hnp, ?_, nq, hnq⟩
      have hown := h.chain.2.1 q p hq0 hp0 hq hp (Ne.symm hne)
      have hmem := List.mem_filter.mp hown
      simpa [ownersOf, hnp] using hmem.1
    have hself : ∀ p : Int, 0 ≤ p → p < g.current_step → Rel g (sel p) (sel p) := by
      intro p hp0 hp
      obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 p hp0 hp).1
      refine ⟨np, hnp, ?_, np, hnp⟩
      have hs := h.self_owned p hp0 hp
      simpa [ownersOf, hnp] using hs
    have hrel : ∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step →
        Rel g (sel p) (sel q) := by
      intro p q hp0 hp hq0 hq
      by_cases hpq : p = q
      · rw [hpq]; exact hself q hq0 hq
      · exact how p q hp0 hp hq0 hq hpq
    exact ChainUp2.link (sel c) (sel (c + 1)) _ ns hns hpar hstep
      (by rw [(h.chain.1.1 c hc0 hb).2]; omega) (by rw [(h.chain.1.1 (c+1) (by omega) hb1).2]; omega)
      (hrel c i hc0 hb hi0 (by omega)) (hrel c j hc0 hb hj0 hj)
      (hrel i c hi0 (by omega) hc0 hb) (hrel j c hj0 hj hc0 hb)
      (hrel c (c+1) hc0 hb (by omega) hb1) (hrel (c+1) c (by omega) hb1 hc0 hb)
      (hrel (c+1) i (by omega) hb1 hi0 (by omega)) (hrel (c+1) j (by omega) hb1 hj0 hj)
      (hrel i (c+1) hi0 (by omega) (by omega) hb1) (hrel j (c+1) hj0 hj (by omega) hb1)
      hrest

/-- **A genuine path has a good top.** A chain that is sound in the union and in one of its sides makes
its own top good for every pair of the chain: the chain itself reaches the top, the side carries all its
pairs, and its own nodes are the witnesses. -/
theorem cimaOk_of_chain (sides : List GPathM) (g S : GPathM) (hS : S ∈ sides)
    (hcsS : S.current_step = g.current_step) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hSc : ChainSound S sel) (hroot : (sel 0).parent_id.isNone = true) (hcs : 0 < g.current_step)
    (i j : Int) (hi0 : 0 ≤ i)
    (hi : i < g.current_step) (hj0 : 0 ≤ j) (hj : j < g.current_step) :
    cimaOk sides g (sel i) (sel j) = true := by
  have htop0 : (0 : Int) ≤ g.current_step - 1 := by omega
  have htop1 : g.current_step - 1 < g.current_step := by omega
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 _ htop0 htop1).1
  have hmemTop : sel (g.current_step - 1) ∈ (g.line (g.current_step - 1)).map (·.id) :=
    mem_line_of_node? g _ nt hnt _ (h.chain.1.1 _ htop0 htop1).2
  refine List.any_eq_true.mpr ⟨sel (g.current_step - 1), hmemTop, ?_⟩
  -- the side's own relations
  have hcarS : ∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step →
      carries sides (sel (g.current_step - 1)) (sel p) (sel q) = true := by
    intro p q hp0 hp hq0 hq
    refine carries_of_side sides S hS _ _ _ ?_
      (rel_of_chainSound S sel hSc p q hp0 (by rw [hcsS]; exact hp) hq0 (by rw [hcsS]; exact hq))
      (rel_of_chainSound S sel hSc q p hq0 (by rw [hcsS]; exact hq) hp0 (by rw [hcsS]; exact hp))
    exact (hSc.chain.1.1 _ htop0 (by rw [hcsS]; exact htop1)).1
  -- the chain reaches its own top
  have hreach : reaches g (sel i) (sel j) (sel (g.current_step - 1)) = true := by
    obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 i hi0 hi).1
    refine reaches_of_chain g _ _ _ ?_ ni hni (rel_of_chainSound g sel h i i hi0 hi hi0 hi)
      (rel_of_chainSound g sel h i j hi0 hi hj0 hj) (rel_of_chainSound g sel h j i hj0 hj hi0 hi)
    exact chainUp2_of_chainSound g sel h hcs i j hi0 hj0 hj (g.current_step - 1 - i).toNat i
      (by omega) (Int.le_refl _) hi0
  have how : ∀ p q : Int, 0 ≤ p → p < g.current_step → 0 ≤ q → q < g.current_step →
      (ownersOf g (sel p)).contains (sel q) = true := by
    intro p q hp0 hp hq0 hq
    obtain ⟨np, hnp, hmem, _⟩ := rel_of_chainSound g sel h p q hp0 hp hq0 hq
    unfold ownersOf; rw [hnp]; exact List.contains_iff_mem.mpr hmem
  have hsteps : stepOk sides g (sel (g.current_step - 1)) (sel i) (sel j) = true := by
    refine List.all_eq_true.mpr (fun k hk => ?_)
    obtain ⟨hk0, hk1⟩ := PickInduction.intRange_bounds hk
    have hkk : k < g.current_step := by omega
    obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 k hk0 hkk).1
    refine List.any_eq_true.mpr ⟨sel k, mem_line_of_node? g _ nk hnk _ (h.chain.1.1 k hk0 hkk).2, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨how i k hi0 hi hk0 hkk, how j k hj0 hj hk0 hkk⟩, how k i hk0 hkk hi0 hi⟩,
      how k j hk0 hkk hj0 hj⟩, hcarS i k hi0 hi hk0 hkk⟩, hcarS j k hj0 hj hk0 hkk⟩
  have hstepEq : ∀ p : Int, 0 ≤ p → p < g.current_step → (sel p).id.step = p :=
    fun p hp0 hp => (h.chain.1.1 p hp0 hp).2
  have hpar : parOk sides g (sel (g.current_step - 1)) (sel i) (sel j) = true := by
    by_cases h0 : i = 0
    · refine (Bool.or_eq_true _ _).mpr (Or.inl ?_)
      rw [h0]; exact hroot
    · refine (Bool.or_eq_true _ _).mpr (Or.inr ?_)
      have hi1 : 0 ≤ i - 1 := by omega
      have hi2 : i - 1 < g.current_step := by omega
      obtain ⟨ni, hni, hmem, _⟩ := rel_of_chainSound g sel h i (i - 1) hi0 hi hi1 hi2
      refine List.any_eq_true.mpr ⟨sel (i - 1), by unfold ownersOf; rw [hni]; exact hmem, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨by rw [hstepEq (i-1) hi1 hi2, hstepEq i hi0 hi]; omega,
        hcarS i (i-1) hi0 hi hi1 hi2⟩, hcarS (i-1) i hi1 hi2 hi0 hi⟩,
        hcarS (i-1) j hi1 hi2 hj0 hj⟩, how (i-1) i hi1 hi2 hi0 hi⟩
  have hson : sonOk sides g (sel (g.current_step - 1)) (sel i) (sel j) = true := by
    by_cases hl : i = g.current_step - 1
    · refine (Bool.or_eq_true _ _).mpr (Or.inl ?_)
      have he : (sel i).id.step = g.current_step - 1 := by rw [hstepEq i hi0 hi, hl]
      exact beq_iff_eq.mpr he
    · refine (Bool.or_eq_true _ _).mpr (Or.inr ?_)
      have hi1 : 0 ≤ i + 1 := by omega
      have hi2 : i + 1 < g.current_step := by omega
      obtain ⟨ni, hni, hmem, _⟩ := rel_of_chainSound g sel h i (i + 1) hi0 hi hi1 hi2
      refine List.any_eq_true.mpr ⟨sel (i + 1), by unfold ownersOf; rw [hni]; exact hmem, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨by rw [hstepEq (i+1) hi1 hi2, hstepEq i hi0 hi],
        hcarS i (i+1) hi0 hi hi1 hi2⟩, hcarS (i+1) i hi1 hi2 hi0 hi⟩,
        hcarS (i+1) j hi1 hi2 hj0 hj⟩, how (i+1) i hi1 hi2 hi0 hi⟩
  have hlink : linkOk sides g (sel (g.current_step - 1)) (sel i) (sel j) = true := by
    by_cases hne : (sel j).id.step + 1 = (sel i).id.step
    · refine (Bool.or_eq_true _ _).mpr (Or.inr ?_)
      have hji : j + 1 = i := by
        rw [hstepEq i hi0 hi, hstepEq j hj0 hj] at hne; omega
      obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp
        (hSc.chain.1.1 i hi0 (by rw [hcsS]; exact hi)).1
      have hpar' : sel j ∈ ni.parents := by
        have hlink := hSc.chain.1.2 j hj0 (by rw [hcsS]; omega)
        rw [hji] at hlink
        rw [hni] at hlink
        simpa using hlink
      refine List.any_eq_true.mpr ⟨S, hS, ?_⟩
      simp only [hni, Bool.and_eq_true]
      exact ⟨(hSc.chain.1.1 _ htop0 (by rw [hcsS]; exact htop1)).1,
        List.contains_iff_mem.mpr hpar'⟩
    · refine (Bool.or_eq_true _ _).mpr (Or.inl ?_)
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
      exact hne
  simp only [goodFor, hreach, hcarS i j hi0 hi hj0 hj, hsteps, hpar, hson, hlink, Bool.and_self]

/-- **The rule's hypothesis holds for a genuine path**: while the path survives, its own top stays
good. -/
theorem carried_of_side (sides : List GPathM) (g S : GPathM) (hS : S ∈ sides)
    (sel : Int → PathNodeId) (hSc : ChainSound S sel) (hroot : (sel 0).parent_id.isNone = true)
    (hcsS : S.current_step = g.current_step) (hcs : 0 < g.current_step) : Carried sides g sel := by
  intro g' hk hsc i j hi0 hi hj0 hj
  have hstep : g'.current_step = g.current_step := hk.1.step_eq
  refine cimaOk_of_chain sides g' S hS (by rw [hstep]; exact hcsS) sel hsc hSc hroot ?_ i j hi0 hi hj0 hj
  rw [hstep]; exact hcs

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
    (hroot : (sel 0).parent_id.isNone = true) (hcsS : S.current_step = g.current_step)
    (hcs : 0 < g.current_step) : ChainSound (reviewCima sides g) sel :=
  ChainSound_reviewCima sides g sel h (carried_of_side sides g S hS sel hSc hroot hcsS hcs)

-- ============================================================
-- The invariants of a state survive the rule
-- ============================================================

theorem PMS_cimaPair (sides : List GPathM) (g : GPathM) (hs : Sons.PMS g) (x w : PathNodeId) :
    Sons.PMS (cimaPair sides g x w) := by
  unfold cimaPair
  split
  · split
    · exact Sons.PMS_updateAt _ w _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (Sons.PMS_updateAt g x _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hs)
    · exact hs
  · exact hs

theorem SN_cimaPair (sides : List GPathM) (g : GPathM) (hs : Sons.SN g) (x w : PathNodeId) :
    Sons.SN (cimaPair sides g x w) := by
  unfold cimaPair
  split
  · split
    · exact Sons.SN_updateAt _ w _ (fun _ => rfl) (fun _ => rfl)
        (Sons.SN_updateAt g x _ (fun _ => rfl) (fun _ => rfl) hs)
    · exact hs
  · exact hs

theorem SMP_cimaNode (sides : List GPathM) (g : GPathM) (hs : Sons.SMP g) (x : PathNodeId) :
    Sons.SMP (cimaNode sides g x) := by
  unfold cimaNode
  split
  · exact hs
  · next nx _ =>
    exact BranchLines.foldl_inv (fun g' w => cimaPair sides g' x w) (fun g' => Sons.SMP g')
      nx.owners (fun g' w _ hg' => SMP_cimaPair sides g' hg' x w) g hs

theorem PMS_cimaNode (sides : List GPathM) (g : GPathM) (hs : Sons.PMS g) (x : PathNodeId) :
    Sons.PMS (cimaNode sides g x) := by
  unfold cimaNode
  split
  · exact hs
  · next nx _ =>
    exact BranchLines.foldl_inv (fun g' w => cimaPair sides g' x w) (fun g' => Sons.PMS g')
      nx.owners (fun g' w _ hg' => PMS_cimaPair sides g' hg' x w) g hs

theorem SN_cimaNode (sides : List GPathM) (g : GPathM) (hs : Sons.SN g) (x : PathNodeId) :
    Sons.SN (cimaNode sides g x) := by
  unfold cimaNode
  split
  · exact hs
  · next nx _ =>
    exact BranchLines.foldl_inv (fun g' w => cimaPair sides g' x w) (fun g' => Sons.SN g')
      nx.owners (fun g' w _ hg' => SN_cimaPair sides g' hg' x w) g hs

theorem sons_cimaSweep (sides : List GPathM) (g : GPathM) (hsmp : Sons.SMP g) (hpms : Sons.PMS g)
    (hsn : Sons.SN g) :
    Sons.SMP (cimaSweep sides g) ∧ Sons.PMS (cimaSweep sides g) ∧ Sons.SN (cimaSweep sides g) := by
  unfold cimaSweep
  split
  · refine BranchLines.foldl_inv
      (fun g' k => ((g'.line k).map (·.id)).foldl (cimaNode sides) g')
      (fun g' => Sons.SMP g' ∧ Sons.PMS g' ∧ Sons.SN g') _ ?_ g ⟨hsmp, hpms, hsn⟩
    intro g' k _ hg'
    refine BranchLines.foldl_inv (cimaNode sides) (fun g'' => Sons.SMP g'' ∧ Sons.PMS g'' ∧ Sons.SN g'')
      _ ?_ g' hg'
    intro g'' x _ hg''
    exact ⟨SMP_cimaNode sides g'' hg''.1 x, PMS_cimaNode sides g'' hg''.2.1 x,
      SN_cimaNode sides g'' hg''.2.2 x⟩
  · exact ⟨hsmp, hpms, hsn⟩

/-- **The family a good top names, at the fixpoint**: the live entries the side of `t` carries. The rule
leaves it closed under the witness of every step — the `cov` and `agg` rules of a support. -/
def FamAt (sides : List GPathM) (g : GPathM) (t a b : PathNodeId) : Prop :=
  Rel g a b ∧ carries sides t a b = true

/-- **From the fixpoint to the closure.** At a state the sweep no longer shrinks, every entry with a good
top `t` has, at every step, a witness that the side of `t` carries with both ends — which is what `cov`
and `agg` of the support ask for. -/
theorem fam_witness (sides : List GPathM) (g : GPathM) (t a b : PathNodeId)
    (hgood : goodFor sides g t a b = true) (l : Int) (hl0 : 0 ≤ l) (hl1 : l < g.current_step) :
    ∃ z, z.id.step = l ∧ (ownersOf g a).contains z = true ∧ (ownersOf g b).contains z = true ∧
      (ownersOf g z).contains a = true ∧ (ownersOf g z).contains b = true ∧
      carries sides t a z = true ∧ carries sides t b z = true := by
  simp only [goodFor, Bool.and_eq_true] at hgood
  have hall : stepOk sides g t a b = true := hgood.1.1.1.2
  simp only [stepOk] at hall
  have hk := List.all_eq_true.mp hall l (mem_intRange hl0 (by omega))
  obtain ⟨z, hz, hcond⟩ := List.any_eq_true.mp hk
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hz
  simp only [Bool.and_eq_true] at hcond
  exact ⟨n.id, eq_of_beq (List.mem_filter.mp hn).2, hcond.1.1.1.1.1, hcond.1.1.1.1.2,
    hcond.1.1.1.2, hcond.1.1.2, hcond.1.2, hcond.2⟩

/-- **What is left for the verdict of `ImprovesCima`.** The review of a union leaves every entry with a
good top (`cimaOk_of_noProgress`), so the family the top names is closed. Two bridges are missing:

* `reachTops` accepts an explicit chain: a path's own nodes make its top reachable;
* a side carries the pairs of the paths that reach its top (branch completeness, already proved for
  `Improves`, to be carried over).

With them, a genuine path always has a good top, so `Carried` holds and the machine loses no solution;
and `HereditaryValid.ChainClosureAt` follows from `CimaOk`, which closes the verdict through route C. -/
def Bridges : Prop :=
  (∀ (g : GPathM) (a b t : PathNodeId), t.id.step = g.current_step - 1 →
      PinDeath.ChainUp2 g a b a t → t ∈ reachTops g a b) ∧
  (∀ (sides : List GPathM) (t a b : PathNodeId), (∃ S ∈ sides, (S.node? t).isSome = true ∧
      EmbeddedSupport.Rel S a b ∧ EmbeddedSupport.Rel S b a) → carries sides t a b = true)

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.AOk_filterAllCima' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AOk_filterAllCima

end AbsSat.GraphPath.Model.ImprovesCima
