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

/-- The rule's hypothesis for a support, robust along the sweep. As with a chain (`TestC`), the test is
only asked for where the support is still there: the sweep keeps it as it goes. -/
def TestR (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM)
    (Sc : PathNodeId → Prop) (Rl : PathNodeId → PathNodeId → Prop) : Prop :=
  ∀ g', Keeps g g' → AOk g' Sc Rl → ∀ x v, Rl x v → test g' x v = true

theorem AOk_pruneNode (test : GPathM → PathNodeId → PathNodeId → Bool) (g g₀ : GPathM) (x : PathNodeId) (hk : Keeps g₀ g)
    (h : AOk g S R) (hC : TestR test g₀ S R) : AOk (pruneNode test g x) S R ∧ Keeps g₀ (pruneNode test g x) := by
  refine ⟨?_, Keeps.trans hk (keeps_pruneNode test g x)⟩
  unfold pruneNode
  split
  · exact h
  · next nx _ =>
    refine BranchLines.foldl_inv (fun g' w => prunePair test g' x w)
      (fun g' => AOk g' S R ∧ Keeps g₀ g') nx.owners ?_ g ⟨h, hk⟩ |>.1
    intro g' w _ hg'
    exact ⟨AOk_prunePair test g' hg'.1 x w (fun hr => hC g' hg'.2 hg'.1 x w hr),
      Keeps.trans hg'.2 (keeps_prunePair _ _ _ _)⟩

/-- **A support survives the sweep.** The rule only drops pairs whose chain reaches a top the sides do
not carry, and a support's pairs are carried by hypothesis; everything else it removes leaves the support
where it was. -/
theorem AOk_pruneSweep (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM) (h : AOk g S R) (hC : TestR test g S R) :
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

-- ============================================================
-- The sweep carries the chains, so the hypothesis can be asked where the sweep is
-- ============================================================

/-- A family of chains, all still sound in the state. -/
def ChainsOk (C : (Int → PathNodeId) → Prop) (g : GPathM) : Prop := ∀ sel, C sel → ChainSound g sel

/-- **The rule's hypothesis for a support, asked only where the sweep can actually be.** Same as
`TestR`, but the narrowing is also known to hold the chains. The sweep carries them (`ChainSound_prunePair`
at every step), so nothing is ever asked of a state the sweep cannot reach — which is exactly the slack
`TestR` had. -/
def TestRC (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM)
    (C : (Int → PathNodeId) → Prop) (Sc : PathNodeId → Prop)
    (Rl : PathNodeId → PathNodeId → Prop) : Prop :=
  ∀ g', Keeps g g' → ChainsOk C g' → AOk g' Sc Rl → ∀ x v, Rl x v → test g' x v = true

theorem testRC_of_testR (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM)
    (C : (Int → PathNodeId) → Prop) (h : TestR test g S R) : TestRC test g C S R :=
  fun g' hk _ hA x v hr => h g' hk hA x v hr

theorem AOk_pruneNodeC (test : GPathM → PathNodeId → PathNodeId → Bool) (g g₀ : GPathM)
    (x : PathNodeId) (C : (Int → PathNodeId) → Prop) (hk : Keeps g₀ g)
    (h : AOk g S R) (hch : ChainsOk C g)
    (hCc : ∀ sel, C sel → TestC test g₀ sel) (hR : TestRC test g₀ C S R) :
    (AOk (pruneNode test g x) S R ∧ ChainsOk C (pruneNode test g x)) ∧
      Keeps g₀ (pruneNode test g x) := by
  refine ⟨?_, Keeps.trans hk (keeps_pruneNode test g x)⟩
  unfold pruneNode
  split
  · exact ⟨h, hch⟩
  · next nx _ =>
    refine BranchLines.foldl_inv (fun g' w => prunePair test g' x w)
      (fun g' => (AOk g' S R ∧ ChainsOk C g') ∧ Keeps g₀ g') nx.owners ?_ g ⟨⟨h, hch⟩, hk⟩ |>.1
    intro g' w _ hg'
    refine ⟨⟨AOk_prunePair test g' hg'.1.1 x w
        (fun hr => hR g' hg'.2 hg'.1.2 hg'.1.1 x w hr), ?_⟩,
      Keeps.trans hg'.2 (keeps_prunePair _ _ _ _)⟩
    intro sel hsel
    refine ChainSound_prunePair test g' x w sel (hg'.1.2 sel hsel) ?_
    intro i j hi0 hi hj0 hj hix hjw
    have hp := hCc sel hsel g' hg'.2 (hg'.1.2 sel hsel) i j hi0 hi hj0 hj
    rw [hix, hjw] at hp
    exact hp

/-- **A support survives the sweep, and so do the chains.** -/
theorem AOk_pruneSweepC (test : GPathM → PathNodeId → PathNodeId → Bool) (g : GPathM)
    (C : (Int → PathNodeId) → Prop) (h : AOk g S R) (hch : ChainsOk C g)
    (hCc : ∀ sel, C sel → TestC test g sel) (hR : TestRC test g C S R) :
    AOk (pruneSweep test g) S R ∧ ChainsOk C (pruneSweep test g) := by
  unfold pruneSweep
  split
  · refine BranchLines.foldl_inv
      (fun g' k => ((g'.line k).map (·.id)).foldl (pruneNode test) g')
      (fun g' => (AOk g' S R ∧ ChainsOk C g') ∧ Keeps g g') _ ?_ g ⟨⟨h, hch⟩, Keeps.refl g⟩ |>.1
    intro g' k _ hg'
    refine BranchLines.foldl_inv (pruneNode test)
      (fun g'' => (AOk g'' S R ∧ ChainsOk C g'') ∧ Keeps g g'') _ ?_ g' hg'
    intro g'' x _ hg''
    exact AOk_pruneNodeC test g'' g x C hg''.2 hg''.1.1 hg''.1.2 hCc hR
  · exact ⟨h, hch⟩

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

/-- A support whose pairs the side of `t` carries survives the restriction to that side. -/
theorem AOk_restFuel (sides : List GPathM) (t : PathNodeId) :
    ∀ (fuel : Nat) (g : GPathM), AOk g S R → (∀ x v, R x v → restTest sides t g x v = true) →
      AOk (restFuel sides t fuel g) S R := by
  intro fuel
  induction fuel with
  | zero => intro g h _; exact h
  | succ n ih =>
    intro g h hR
    simp only [restFuel]
    split
    · exact ih _ (AOk_pruneSweep _ g h (fun g' _ _ x v hr => hR x v hr)) (fun x v hr => hR x v hr)
    · exact h

theorem AOk_famFix (sides : List GPathM) (t : PathNodeId) (g : GPathM) (h : AOk g S R)
    (hR : ∀ x v, R x v → restTest sides t g x v = true) : AOk (famFix sides t g) S R :=
  AnchoredSurvive.AOk_reviewAggFuel _ _ (AOk_restFuel sides t _ g h hR)

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

abbrev CarriedR (sides : List GPathM) : GPathM → (PathNodeId → Prop) →
    (PathNodeId → PathNodeId → Prop) → Prop :=
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

theorem AOk_cimaSweep (sides : List GPathM) (g : GPathM) (h : AOk g S R) (hC : CarriedR sides g S R) :
    AOk (cimaSweep sides g) S R := AOk_pruneSweep _ g h hC

theorem cimaOk_of_noProgress (sides : List GPathM) (g : GPathM) (hv : isValid g = true)
    (hnp : ¬ GPathM.measure (cimaSweep sides g) < GPathM.measure g) : CimaOk sides g :=
  testOk_of_noProgress _ g hv hnp

/-- Any two nodes of a sound chain own each other; a node owns itself. -/
theorem chain_owns (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (i j : Int) (hi0 : 0 ≤ i) (hi1 : i < g.current_step) (hj0 : 0 ≤ j)
    (hj1 : j < g.current_step) : sel j ∈ ownersOf g (sel i) :=
  if he : i = j then (by rw [he]; exact h.self_owned j hj0 hj1)
  else (List.mem_filter.mp (h.chain.2.1 j i hj0 hi0 hj1 hi1 (fun hc => he hc.symm))).1

/-- The chain's node one step below is a parent of the node above. -/
theorem chain_parent (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (k : Int) (n : PNodeM) (h0 : 0 ≤ k) (h1 : k + 1 < g.current_step)
    (hn : g.node? (sel (k + 1)) = some n) : sel k ∈ n.parents := by
  have := h.chain.1.2 k h0 h1
  rw [hn] at this; exact this

/-- The chain's node at step `k` is at step `k`. -/
theorem chain_step (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (k : Int) (h0 : 0 ≤ k) (h1 : k < g.current_step) : (sel k).id.step = k :=
  (h.chain.1.1 k h0 h1).2

/-- **A chain of a side passes the restriction test of its own top.** The side owns every pair of the
chain in both directions, and holds the chain's parent links; and the top the test speaks of is the
chain's own node at the last step, which the side holds too. Nothing is computed and nothing is chosen:
the chain is the certificate of its own side. -/
theorem restTest_of_chain (sides : List GPathM) (S : GPathM) (hS : S ∈ sides)
    (sel : Int → PathNodeId) (hsc : ChainSound S sel)
    (kt : Int) (hkt0 : 0 ≤ kt) (hkt1 : kt < S.current_step) (g : GPathM)
    (p q : Int) (hp0 : 0 ≤ p) (hp1 : p < S.current_step) (hq0 : 0 ≤ q) (hq1 : q < S.current_step) :
    restTest sides (sel kt) g (sel p) (sel q) = true := by
  have hnt : (S.node? (sel kt)).isSome = true := (hsc.chain.1.1 kt hkt0 hkt1).1
  have hcar : ∀ u w : Int, 0 ≤ u → u < S.current_step → 0 ≤ w → w < S.current_step →
      carries sides (sel kt) (sel u) (sel w) = true := by
    intro u w hu0 hu1 hw0 hw1
    refine List.any_eq_true.mpr ⟨S, hS, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨hnt, List.contains_iff_mem.mpr (chain_owns S sel hsc u w hu0 hu1 hw0 hw1)⟩,
      List.contains_iff_mem.mpr (chain_owns S sel hsc w u hw0 hw1 hu0 hu1)⟩
  have hlk : ∀ u w : Int, 0 ≤ u → u < S.current_step → 0 ≤ w → w + 1 = u →
      linkedIn sides (sel kt) (sel u) (sel w) = true := by
    intro u w hu0 hu1 hw0 he
    refine List.any_eq_true.mpr ⟨S, hS, ?_⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hsc.chain.1.1 u hu0 hu1).1
    simp only [hn, Bool.and_eq_true]
    refine ⟨hnt, List.contains_iff_mem.mpr (chain_parent S sel hsc w n hw0 ?_ ?_)⟩
    · rw [he]; exact hu1
    · rw [he]; exact hn
  simp only [restTest, Bool.and_eq_true]
  refine ⟨⟨⟨hcar p q hp0 hp1 hq0 hq1, hcar q p hq0 hq1 hp0 hp1⟩, ?_⟩, ?_⟩
  · cases hb : ((sel q).id.step + 1 == (sel p).id.step) with
    | false => simp only [Bool.not_false, Bool.true_or]
    | true =>
      rw [chain_step S sel hsc q hq0 hq1, chain_step S sel hsc p hp0 hp1] at hb
      simp only [Bool.not_true, Bool.false_or]
      exact hlk p q hp0 hp1 hq0 (eq_of_beq hb)
  · cases hb : ((sel p).id.step + 1 == (sel q).id.step) with
    | false => simp only [Bool.not_false, Bool.true_or]
    | true =>
      rw [chain_step S sel hsc p hp0 hp1, chain_step S sel hsc q hq0 hq1] at hb
      simp only [Bool.not_true, Bool.false_or]
      exact hlk q p hq0 hq1 hp0 (eq_of_beq hb)

/-- **A chain carries over to any state that holds its pairs.** If every pair of a sound chain is a
relation of `Sd`, its parent links are `Sd`'s, and its nodes are global owners there, then the chain is
sound in `Sd` too. The cover, the aggregation and the sons come from the chain's own shape and from
`Sd`'s sons invariant; nothing else is needed. This is the chain's version of `sup_transfer`. -/
theorem chainSound_transfer (F Sd : GPathM) (sel : Int → PathNodeId) (h : ChainSound F sel)
    (hcs : Sd.current_step = F.current_step) (hsmp : Sons.SMP Sd)
    (hrel : ∀ i j, 0 ≤ i → i < F.current_step → 0 ≤ j → j < F.current_step →
      Rel Sd (sel i) (sel j))
    (hgow : ∀ i, 0 ≤ i → i < F.current_step → sel i ∈ Sd.gowners)
    (hpar : ∀ i, 0 ≤ i → i + 1 < F.current_step →
      ∃ n, Sd.node? (sel (i + 1)) = some n ∧ sel i ∈ n.parents) :
    ChainSound Sd sel := by
  have hst : ∀ k, 0 ≤ k → k < F.current_step → (sel k).id.step = k := chain_step F sel h
  have hown : ∀ i j, 0 ≤ i → i < F.current_step → 0 ≤ j → j < F.current_step →
      sel j ∈ ownersOf Sd (sel i) := by
    intro i j hi0 hi1 hj0 hj1
    obtain ⟨m, hm, hmem, _⟩ := hrel i j hi0 hi1 hj0 hj1
    unfold ownersOf; rw [hm]; exact hmem
  refine ⟨⟨⟨fun k h0 h1 => ?_, fun k h0 h1 => ?_⟩, fun i j hi0 hj0 hi1 hj1 _ => ?_,
    fun k h0 h1 => ?_⟩, fun k h0 h1 => ?_, fun k h0 h1 => ?_,
    ⟨h.root_shape.1, fun k hk0 hk1 => h.root_shape.2 k hk0 (by rw [← hcs]; exact hk1)⟩⟩
  · rw [hcs] at h1
    obtain ⟨m, hm, _, _⟩ := hrel k k h0 h1 h0 h1
    exact ⟨by rw [hm]; rfl, hst k h0 h1⟩
  · rw [hcs] at h1
    obtain ⟨n, hn, hmem⟩ := hpar k h0 (by omega)
    rw [hn]; exact hmem
  · rw [hcs] at hi1 hj1
    exact List.mem_filter.mpr ⟨hown j i hj0 hj1 hi0 hi1, beq_iff_eq.mpr (hst i hi0 hi1)⟩
  · rw [hcs] at h1; exact hgow k h0 h1
  · rw [hcs] at h1; exact hown k k h0 h1 h0 h1
  · rw [hcs] at h1
    obtain ⟨n, hn, hmem⟩ := hpar k h0 (by omega)
    obtain ⟨m, hm, _, _⟩ := hrel k k h0 (by omega) h0 (by omega)
    have hres := hsmp n (List.mem_of_find?_eq_some hn) (sel k) hmem m
      (List.mem_of_find?_eq_some hm) (node?_id_eq _ _ m hm)
    unfold sonsOf; rw [hm, ← node?_id_eq _ _ n hn]; exact hres

/-- **A sound chain is a support.** Everything `Sup` asks for, a chain hands over from its own shape:
the cover and the aggregation are the chain's node at that step, the parent and the son are its
neighbours, and the links are its own. This is what lets the descent exhibit a sub-support without
computing anything. -/
theorem sup_of_chainSound (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    Sup g (fun p => ∃ k, 0 ≤ k ∧ k < g.current_step ∧ p = sel k)
      (fun x v => ∃ i j, 0 ≤ i ∧ i < g.current_step ∧ 0 ≤ j ∧ j < g.current_step ∧
        x = sel i ∧ v = sel j) := by
  have hst : ∀ k, 0 ≤ k → k < g.current_step → (sel k).id.step = k := chain_step g sel h
  have hnd : ∀ k, 0 ≤ k → k < g.current_step → (g.node? (sel k)).isSome = true :=
    fun k h0 h1 => (h.chain.1.1 k h0 h1).1
  have howns : ∀ i j, 0 ≤ i → i < g.current_step → 0 ≤ j → j < g.current_step →
      sel j ∈ ownersOf g (sel i) := fun i j => chain_owns g sel h i j
  have hpr : ∀ k, 0 ≤ k → k + 1 < g.current_step →
      sel k ∈ ((g.node? (sel (k + 1))).map PNodeM.parents).getD [] := h.chain.1.2
  have hprn : ∀ k n, 0 ≤ k → k + 1 < g.current_step → g.node? (sel (k + 1)) = some n →
      sel k ∈ n.parents := fun k n => chain_parent g sel h k n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨k, h0, h1, rfl⟩; exact h.chain.2.2 k h0 h1
  · rintro p ⟨k, h0, h1, rfl⟩; exact hnd k h0 h1
  · rintro p ⟨k, h0, h1, rfl⟩; rw [hst k h0 h1]; exact ⟨h0, h1⟩
  · rintro x v ⟨i, j, hi0, hi1, hj0, hj1, rfl, rfl⟩
    exact ⟨⟨i, hi0, hi1, rfl⟩, ⟨j, hj0, hj1, rfl⟩⟩
  · rintro x v n ⟨i, j, hi0, hi1, hj0, hj1, rfl, rfl⟩ hn
    have hm := howns i j hi0 hi1 hj0 hj1
    unfold ownersOf at hm; rw [hn] at hm; exact hm
  · rintro x ⟨i, hi0, hi1, rfl⟩ l hl0 hl1
    exact ⟨sel l, ⟨i, l, hi0, hi1, hl0, hl1, rfl, rfl⟩, hst l hl0 hl1⟩
  · rintro x d ⟨i, hi0, hi1, rfl⟩ hn hroot v ⟨i', j', hi0', hi1', hj0', hj1', hxe, rfl⟩
    have hine : i ≠ 0 := fun he => hroot (by rw [he]; exact h.root_shape.1)
    clear hroot
    have hipos : 0 < i := by
      rcases Int.lt_or_lt_of_ne hine with hlt | hgt
      · exact absurd hlt (Int.not_lt.mpr hi0)
      · exact hgt
    clear hine
    have hsucc : i - 1 + 1 = i := by omega
    refine ⟨sel (i - 1), ?_, ⟨i, i - 1, hi0, hi1, by omega, by omega, rfl, rfl⟩,
      ⟨i - 1, i, by omega, by omega, hi0, hi1, rfl, rfl⟩,
      ⟨i - 1, j', by omega, by omega, hj0', hj1', rfl, rfl⟩⟩
    have := hpr (i - 1) (by omega) (by omega)
    rw [hsucc, hn] at this; exact this
  · rintro x ⟨i, hi0, hi1, rfl⟩ hne v ⟨i', j', hi0', hi1', hj0', hj1', hxe, rfl⟩
    rw [hst i hi0 hi1] at hne
    have hi2 : i + 1 < g.current_step := by
      rcases Int.lt_or_lt_of_ne hne with hlt | hgt
      · omega
      · omega
    clear hne
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hnd (i + 1) (by omega) hi2)
    exact ⟨sel (i + 1), n, hn, hprn i n hi0 hi2 hn,
      ⟨i, i + 1, hi0, hi1, by omega, hi2, rfl, rfl⟩,
      ⟨i + 1, i, by omega, hi2, hi0, hi1, rfl, rfl⟩,
      ⟨i + 1, j', by omega, hi2, hj0', hj1', rfl, rfl⟩⟩
  · rintro x v ⟨i, j, hi0, hi1, hj0, hj1, rfl, rfl⟩ l hl0 hl1
    exact ⟨sel l, ⟨i, l, hi0, hi1, hl0, hl1, rfl, rfl⟩,
      ⟨j, l, hj0, hj1, hl0, hl1, rfl, rfl⟩, hst l hl0 hl1⟩
  · rintro x v ⟨i, j, hi0, hi1, hj0, hj1, rfl, rfl⟩
    exact ⟨j, i, hj0, hj1, hi0, hi1, rfl, rfl⟩
  · rintro x c d ⟨i, j, hi0, hi1, hj0, hj1, rfl, rfl⟩ _ hstep hn
    rw [hst i hi0 hi1, hst j hj0 hj1] at hstep
    have hlt : j + 1 < g.current_step := by rw [hstep]; exact hi1
    have := hpr j hj0 hlt
    rw [hstep, hn] at this; exact this

/-- **The rule's hypothesis for a support, per pair.** `cimaOk` is existential over the tops, so the
sweep never asks for one single side for the whole support: it is enough that **each pair** of the
support sits in *some* sub-support that *some* side carries. Each pair may name its own side and its own
sub-support. -/
theorem carriedR_of_pair (sides : List GPathM) (g : GPathM)
    (h : ∀ g', Keeps g g' → AOk g' S R → ∀ x v, R x v →
      ∃ (S' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop) (t : PathNodeId),
        t.id.step = g.current_step - 1 ∧ S' t ∧ R' x v ∧ AOk g' S' R' ∧
        (∀ a b, R' a b → restTest sides t g a b = true)) :
    CarriedR sides g S R := by
  intro g' hk hA x v hr
  obtain ⟨S', R', t, ht, hSt, hrxv, hA', hR'⟩ := h g' hk hA x v hr
  have hcs : g'.current_step = g.current_step := hk.1.step_eq
  have hA2 : AOk (famFix sides t g') S' R' := AOk_famFix sides t g' hA' (fun a b hab => hR' a b hab)
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp (hA'.sup.node t hSt)
  refine List.any_eq_true.mpr ⟨t, mem_line_of_node? g' t nt hnt _ (by rw [hcs]; exact ht), ?_⟩
  have hown : ∀ a b, R' a b → (ownersOf (famFix sides t g') a).contains b = true := by
    intro a b hab
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hA2.sup.node a (hA2.sup.dom a b hab).1)
    unfold ownersOf; rw [hn]
    exact List.contains_iff_mem.mpr (hA2.sup.own a b n hab hn)
  simp only [goodFor, hown x v hrxv, hown v x (hA2.sup.sym x v hrxv),
    SupportSplit.valid_of_sup _ _ _ hA2.sup t hSt, Bool.and_self]

/-- **The rule's hypothesis, for a support carried by one side.** If every pair of a support is carried
by the side of a top `t` of the state — and linked as parent and son where the steps are neighbours —
then the support passes the rule wherever it is still standing. The reason is the same one the machine
runs on: the restriction to that side never touches the support, the review keeps it, so the family of
`t` is a live state that still holds every pair of the support. -/
theorem carriedR_of_side (sides : List GPathM) (g : GPathM) (t : PathNodeId)
    (ht : t.id.step = g.current_step - 1) (hSt : S t)
    (hR : ∀ x v, R x v → restTest sides t g x v = true) :
    CarriedR sides g S R :=
  carriedR_of_pair sides g (fun _ _ hA _ _ hr => ⟨S, R, t, ht, hSt, hr, hA, hR⟩)

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

/-- The sons invariants survive the whole review of a union. -/
theorem sons_reviewCimaFuel (sides : List GPathM) : ∀ (fuel : Nat) (g : GPathM),
    Sons.SMP g → Sons.PMS g → Sons.SN g → Parents.NotRoot g →
    Sons.SMP (reviewCimaFuel sides fuel g) ∧ Sons.PMS (reviewCimaFuel sides fuel g) ∧
      Sons.SN (reviewCimaFuel sides fuel g) := by
  have hagg : ∀ g : GPathM, Sons.SMP g → Sons.PMS g → Sons.SN g → Parents.NotRoot g →
      Sons.SMP (reviewAgg g) ∧ Sons.PMS (reviewAgg g) ∧ Sons.SN (reviewAgg g) := by
    intro g h1 h2 h3 h4
    exact ⟨AnchoredSurvive.SMP_filterAllAgg g h1 h4 [], AggInvariants.PMS_filterAllAgg g [] h2,
      AggInvariants.SN_filterAllAgg g [] h3⟩
  intro fuel
  induction fuel with
  | zero => intro g h1 h2 h3 h4; exact hagg g h1 h2 h3 h4
  | succ n ih =>
    intro g h1 h2 h3 h4
    obtain ⟨a1, a2, a3⟩ := hagg g h1 h2 h3 h4
    have a4 : Parents.NotRoot (reviewAgg g) :=
      Parents.NotRoot_of_pruned (ReaderAggRun.keeps_reviewAggFuel _ g).1 h4
    simp only [reviewCimaFuel]
    split
    · split
      · obtain ⟨b1, b2, b3⟩ := sons_pruneSweep (cimaOk sides) (reviewAgg g) a1 a2 a3
        exact ih _ b1 b2 b3 (Parents.NotRoot_of_pruned (keeps_cimaSweep sides _).1 a4)
      · exact ⟨a1, a2, a3⟩
    · exact ⟨a1, a2, a3⟩

theorem sons_filterAllCima (sides : List GPathM) (g : GPathM) (reqs : List NodeId)
    (h1 : Sons.SMP g) (h2 : Sons.PMS g) (h3 : Sons.SN g) (h4 : Parents.NotRoot g) :
    Sons.SMP (filterAllCima sides g reqs) ∧ Sons.PMS (filterAllCima sides g reqs) ∧
      Sons.SN (filterAllCima sides g reqs) := by
  refine sons_reviewCimaFuel sides _ _ ?_ ?_ ?_ ?_
  · exact BranchLines.foldl_inv filterRequire Sons.SMP reqs
      (fun g' r _ hg' => Sons.SMP_filterRequire g' r hg') g h1
  · exact BranchLines.foldl_inv filterRequire Sons.PMS reqs
      (fun g' r _ hg' => Sons.PMS_filterRequire g' r hg') g h2
  · exact BranchLines.foldl_inv filterRequire Sons.SN reqs
      (fun g' r _ hg' => Sons.SN_filterRequire g' r hg') g h3
  · exact Parents.NotRoot_of_pruned
      (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire reqs g).1 h4

/-- **Every result of the review of a union is a result of the aggressive review.** The loop always
hands back the aggressive review of some narrowing, so everything proved about review fixpoints applies
to it unchanged — the test of the aggressive review, the adjacency, and its own support. -/
theorem reviewCimaFuel_form (sides : List GPathM) : ∀ (fuel : Nat) (g : GPathM),
    ∃ g₀, Keeps g g₀ ∧ reviewCimaFuel sides fuel g = reviewAgg g₀ := by
  intro fuel
  induction fuel with
  | zero => intro g; exact ⟨g, Keeps.refl g, rfl⟩
  | succ n ih =>
    intro g
    simp only [reviewCimaFuel]
    split
    · split
      · obtain ⟨g₀, hk, he⟩ := ih (cimaSweep sides (reviewAgg g))
        exact ⟨g₀, Keeps.trans (Keeps.trans (ReaderAggRun.keeps_reviewAggFuel _ g)
          (keeps_cimaSweep sides _)) hk, he⟩
      · exact ⟨g, Keeps.refl g, rfl⟩
    · exact ⟨g, Keeps.refl g, rfl⟩

theorem filterAllCima_form (sides : List GPathM) (g : GPathM) (reqs : List NodeId) :
    ∃ g₀, Keeps g g₀ ∧ filterAllCima sides g reqs = reviewAgg g₀ := by
  obtain ⟨g₀, hk, he⟩ := reviewCimaFuel_form sides _ (reqs.foldl filterRequire g)
  exact ⟨g₀, Keeps.trans (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire reqs g) hk, he⟩

/-- **The filtered union of `ImprovesCima` is a state of the machine's own kind**, with its adjacency
and its own support. -/
theorem sup_filterAllCima (sides : List GPathM) (g : GPathM) (reqs : List NodeId)
    (hrc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g)
    (hnr : Parents.NotRoot g) (hv : isValid (filterAllCima sides g reqs) = true) :
    AdjacentOwners.Adj (filterAllCima sides g reqs) ∧
      AnchoredSurvive.Sup (filterAllCima sides g reqs)
        (EmbeddedSupport.Mem (filterAllCima sides g reqs)) (Rel (filterAllCima sides g reqs)) := by
  obtain ⟨g₀, hk, he⟩ := filterAllCima_form sides g reqs
  obtain ⟨s1, s2, s3⟩ := sons_filterAllCima sides g reqs hsmp hpms hsn hnr
  have hform : filterAllCima sides g reqs = AggressiveReview.filterAllAgg g₀ [] := he
  have hR : ReaderAgg.ReadableAgg (filterAllCima sides g reqs) :=
    ⟨g₀, [], ReaderAgg.RCtx_of_keeps hk hrc, hform⟩
  have hadj := AdjacentOwners.adj_of_readable _ hR hv s2 s3
  refine ⟨hadj, LinkedChain.sup_self _ hadj ?_ s1⟩
  rw [he]
  exact AggFixpoint.aggOk_reviewAgg g₀ (by rw [← he]; exact hv)

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
    ∀ (fuel : Nat) (g g₀ : GPathM), Keeps g₀ g → AOk g S R → CarriedR sides g₀ S R →
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
        exact AOk_cimaSweep sides _ h₁ (fun g' hk' hA x v hr => hC g' (Keeps.trans hk₁ hk') hA x v hr)
      · exact h₁
    · exact h₁


/-- The rule's hypothesis for a support, with the chains, and for a chain. -/
abbrev CarriedRC (sides : List GPathM) : GPathM → ((Int → PathNodeId) → Prop) →
    (PathNodeId → Prop) → (PathNodeId → PathNodeId → Prop) → Prop :=
  TestRC (cimaOk sides)

/-- **The whole review of a union carries a support and its chains.** -/
theorem AOk_reviewCimaFuelC (sides : List GPathM) (C : (Int → PathNodeId) → Prop) :
    ∀ (fuel : Nat) (g g₀ : GPathM), Keeps g₀ g → AOk g S R → ChainsOk C g →
      (∀ sel, C sel → Carried sides g₀ sel) → CarriedRC sides g₀ C S R →
      AOk (reviewCimaFuel sides fuel g) S R ∧ ChainsOk C (reviewCimaFuel sides fuel g) := by
  intro fuel
  induction fuel with
  | zero =>
    intro g g₀ _ h hch _ _
    exact ⟨AnchoredSurvive.AOk_reviewAggFuel _ g h,
      fun sel hsel => ChainSound_reviewAgg g sel (hch sel hsel)⟩
  | succ n ih =>
    intro g g₀ hk h hch hCc hC
    simp only [reviewCimaFuel]
    have h₁ : AOk (reviewAgg g) S R := AnchoredSurvive.AOk_reviewAggFuel _ g h
    have hch₁ : ChainsOk C (reviewAgg g) :=
      fun sel hsel => ChainSound_reviewAgg g sel (hch sel hsel)
    have hk₁ : Keeps g₀ (reviewAgg g) := Keeps.trans hk (ReaderAggRun.keeps_reviewAggFuel _ g)
    split
    · split
      · obtain ⟨hA2, hch2⟩ := AOk_pruneSweepC (cimaOk sides) (reviewAgg g) C h₁ hch₁
          (fun sel hsel g' hk' hsc' i j => hCc sel hsel g' (Keeps.trans hk₁ hk') hsc' i j)
          (fun g' hk' hchg' hA x v hr => hC g' (Keeps.trans hk₁ hk') hchg' hA x v hr)
        exact ih _ g₀ (Keeps.trans hk₁ (keeps_cimaSweep sides _)) hA2 hch2 hCc hC
      · exact ⟨h₁, hch₁⟩
    · exact ⟨h₁, hch₁⟩

/-- **A support and its chains survive the pins and the review of a union.** -/
theorem AOk_filterAllCimaC (sides : List GPathM) (g : GPathM) (C : (Int → PathNodeId) → Prop)
    (h : AOk g S R) (hch : ChainsOk C g) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r)
    (hpinC : ∀ r ∈ reqs, ∀ sel, C sel → 0 ≤ r.step → r.step < g.current_step →
      (sel r.step).id = r)
    (hCc : ∀ sel, C sel → Carried sides g sel)
    (hC : CarriedRC sides g C S R) : AOk (filterAllCima sides g reqs) S R := by
  have main : ∀ (l : List NodeId), (∀ r ∈ l, ∀ p, S p → p.id.step = r.step → p.id = r) →
      ∀ h' : GPathM, AOk h' S R → AOk (l.foldl filterRequire h') S R := by
    intro l
    induction l with
    | nil => intro _ h' hw; exact hw
    | cons x xs ih =>
      intro hx h' hw
      simp only [List.foldl_cons]
      exact ih (fun r hr => hx r (List.mem_cons_of_mem _ hr)) _
        (AnchoredSurvive.AOk_filterRequire h' hw x (hx x List.mem_cons_self))
  have mainC : ∀ (l : List NodeId),
      (∀ r ∈ l, ∀ sel, C sel → 0 ≤ r.step → r.step < g.current_step → (sel r.step).id = r) →
      ∀ h' : GPathM, h'.current_step = g.current_step → ChainsOk C h' →
        ChainsOk C (l.foldl filterRequire h') := by
    intro l
    induction l with
    | nil => intro _ h' _ hw; exact hw
    | cons x xs ih =>
      intro hx h' hcs hw
      simp only [List.foldl_cons]
      refine ih (fun r hr => hx r (List.mem_cons_of_mem _ hr)) _
        ((ReaderAgg.keeps_filterRequire h' x).1.step_eq.symm.trans hcs) ?_
      intro sel hsel
      exact ChainSound_filterRequire h' x sel (hw sel hsel)
        (fun h0 h1 => hx x List.mem_cons_self sel hsel h0 (by rw [← hcs]; exact h1))
  exact (AOk_reviewCimaFuelC sides C _ _ g
    (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire reqs g)
    (main reqs hpin g h) (mainC reqs hpinC g rfl hch) hCc hC).1

/-- **A support survives the pins and the review of a union.** -/
theorem AOk_filterAllCima (sides : List GPathM) (g : GPathM) (h : AOk g S R) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r)
    (hC : CarriedR sides g S R) : AOk (filterAllCima sides g reqs) S R := by
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
with the rule of the top, which reads the sides that built it. A key whose state the rule leaves dead is
dropped, exactly as the driver of `Improves` drops a send that does not survive: a dead state is the
UNSAT answer for that key and has no business in the line. -/
def advanceCima (L : PureLine) : PureLine :=
  ((pureAdvanceW φ L).map (fun kv => (kv.1, reviewCima (sidesOf φ L kv.1) kv.2))).filter
    (fun kv => isValid kv.2)

def stepsCima : Nat → PureLine → PureLine
  | 0, L => L
  | n + 1, L => stepsCima n (advanceCima φ L)

/-- The whole run. An empty result is the UNSAT answer, as in `Improves`. -/
def runCima : PureLine := stepsCima φ (stepCount φ - 1).toNat (pureInit φ)

/-- The run, advanced from the back: one more line is one more advance of the line so far. -/
theorem stepsCima_succ : ∀ (n : Nat) (L : PureLine),
    stepsCima φ (n + 1) L = advanceCima φ (stepsCima φ n L)
  | 0, _ => rfl
  | n + 1, L => stepsCima_succ n (advanceCima φ L)

/-- **Every state of a line of `ImprovesCima` is alive.** -/
theorem valid_of_mem_advanceCima (L : PureLine) (kv : NodeId × GPathM)
    (hkv : kv ∈ advanceCima φ L) : isValid kv.2 = true := (List.mem_filter.mp hkv).2

/-- **The keys of a line of `ImprovesCima` are the keys of the line of `Improves` that survive.** -/
theorem mem_advanceCima (L : PureLine) (kv : NodeId × GPathM) (hkv : kv ∈ advanceCima φ L) :
    ∃ g, (kv.1, g) ∈ pureAdvanceW φ L ∧ kv.2 = reviewCima (sidesOf φ L kv.1) g := by
  obtain ⟨kv', hkv', he⟩ := List.mem_map.mp (List.mem_filter.mp hkv).1
  exact ⟨kv'.2, by rw [show kv.1 = kv'.1 from by rw [← he]]; exact hkv',
    by rw [← he]⟩


/-- **A live state of `ImprovesCima` is a machine state.** The review only narrows, so everything but
one clause comes from `MInv_of_keeps`; and the clause that does not — that the owners of a node are
nodes — comes from the review's own shape: the result is an aggressive-review fixpoint, where an owner
is a global owner and a global owner is a node. -/
theorem MInv_reviewCima (sides : List GPathM) (g : GPathM) (hm : ReaderAggRun.MInv φ g)
    (hv : isValid (reviewCima sides g) = true) : ReaderAggRun.MInv φ (reviewCima sides g) := by
  obtain ⟨g₀, hk0, hform⟩ := reviewCimaFuel_form sides (measure g + 1) g
  have hform' : reviewCima sides g = reviewAgg g₀ := hform
  have hk : Keeps g (reviewCima sides g) := keeps_reviewCima sides g
  obtain ⟨s1, s2, s3⟩ :=
    sons_reviewCimaFuel sides (measure g + 1) g hm.smp hm.pms hm.sn hm.rctx.shape.notroot
  refine ReaderAggRun.MInv_of_keeps φ hk hm s1 s2 s3 ?_
  intro n hn q hq
  obtain ⟨n0, hn0, _, hsub, _⟩ := hk.1.nodes_derived n hn
  obtain ⟨n1, hn1, hid1⟩ := hm.own n0 hn0 q (hsub q hq)
  have hq0 : 0 ≤ q.id.step := by rw [← hid1]; exact hm.rctx.snn n1 hn1
  have hstep : (reviewCima sides g).current_step = g.current_step := hk.1.step_eq
  have hq1 : q.id.step < (reviewCima sides g).current_step := by
    rw [hstep, ← hid1]; exact hm.rctx.below n1 hn1
  have hRF : ReaderAgg.ReadableAgg (reviewCima sides g) :=
    ⟨g₀, [], ReaderAgg.RCtx_of_keeps hk0 hm.rctx, hform'⟩
  have rcF := ReaderAgg.RCtx_of_readableAgg _ hRF
  have ctxF := Reader.Ctx_of_readable _ (ReaderAgg.readable_of_readableAgg _ hRF) hv
  exact rcF.gn q (ctxF.ownGow n.id n (node?_of_mem rcF.nodup n hn) q hq hq0 hq1)


/-- **A line of `ImprovesCima` is a line of the machine.** Same keys as the line of `Improves` minus
the ones the rule kills, each state a narrowing of the corresponding one, and each one alive because
the dead ones were dropped. -/
theorem LineInv_advanceCima (hwf : WF φ) (k : Int) (L : PureLine)
    (hl : ReaderAggRun.LineInv φ k L) : ReaderAggRun.LineInv φ (k + 1) (advanceCima φ L) := by
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf k L hl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : ((advanceCima φ L).map (fun kv => kv.1)).Sublist
        (((pureAdvanceW φ L).map
          (fun kv => (kv.1, reviewCima (sidesOf φ L kv.1) kv.2))).map (fun kv => kv.1)) :=
      List.Sublist.map _ List.filter_sublist
    rw [List.map_map] at h1
    exact List.Nodup.sublist h1 hadv.1.1
  · intro kv hkv
    obtain ⟨g, hmem, he⟩ := mem_advanceCima φ L kv hkv
    have hsok := hadv.1.2 (kv.1, g) hmem
    have hk : Keeps g kv.2 := by rw [he]; exact keeps_reviewCima _ _
    exact ⟨hsok.onMap, ConservationCore.ShapeOk_of_pruned hk.1 hsok.shape,
      by rw [hk.1.step_eq]; exact hsok.step,
      by rw [hk.1.map_parent_eq]; exact hsok.par,
      valid_of_mem_advanceCima φ L kv hkv⟩
  · intro kv hkv
    obtain ⟨g, hmem, he⟩ := mem_advanceCima φ L kv hkv
    rw [he]
    exact MInv_reviewCima φ _ g (hadv.2 (kv.1, g) hmem)
      (by rw [← he]; exact valid_of_mem_advanceCima φ L kv hkv)

/-- **Every line of the run satisfies it.** -/
theorem LineInv_stepsCima (hwf : WF φ) :
    ∀ m : Nat, ReaderAggRun.LineInv φ (m : Int) (stepsCima φ m (pureInit φ)) := by
  intro m
  induction m with
  | zero => exact ReaderAggRun.LineInv_init φ hwf
  | succ n ih =>
    rw [stepsCima_succ]
    have := LineInv_advanceCima φ hwf (n : Int) _ ih
    rwa [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by push_cast; omega] at this


/-- Each state of a line of `ImprovesCima` is a narrowing of the same state in `Improves`. -/
theorem keeps_advanceCima (L : PureLine) (kv : NodeId × GPathM) (hkv : kv ∈ advanceCima φ L) :
    ∃ g, (kv.1, g) ∈ pureAdvanceW φ L ∧ Keeps g kv.2 := by
  obtain ⟨kv', hkv', he⟩ := List.mem_map.mp (List.mem_filter.mp hkv).1
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

set_option maxHeartbeats 1000000 in
/-- **`ImprovesCima` loses no partial solution.** For an assignment satisfying the clauses below the
step, the line of the run with the rule holds, at the assignment's node, a state carrying the
assignment's partial branch as a sound chain.

The induction is the one the rule was built for: the branch reaches the send of the previous state
(`keepsBranch_Fsac_below`, `chainSound_up_of_prunedR`), the send is alive because a chain makes its
state alive (`isValid_of_ChainG`), the send grows into the union by key (`full_reach`,
`ChainSound_of_grown`), and **the rule does not touch it**, because the send is one of the sides
(`ChainSound_reviewCima_of_side`). -/
theorem cima_chain_below (a : AbsSat.Cnf.Assign) (hwf : WF φ) :
    ∀ (n : Nat), (n : Int) + 1 ≤ stepCount φ → ConservationPrefix.SatBelow φ a ((n : Int) + 1) →
      ∃ g, (selOfAssign φ a (n : Int), g) ∈ stepsCima φ n (pureInit φ) ∧
        g.current_step = (n : Int) + 1 ∧
        ∃ sel, ChainSound g sel ∧
          ∀ k, 0 ≤ k → k < (n : Int) + 1 →
            (sel k).id = selOfAssign φ a k ∧ ConservationCore.SelParent φ a (sel k) := by
  intro n
  induction n with
  | zero =>
    intro hle hs
    have hle1 : (1 : Int) ≤ stepCount φ := by exact_mod_cast hle
    have hs1 : ConservationPrefix.SatBelow φ a 1 := by exact_mod_cast hs
    obtain ⟨g, hmem, hcs, rest⟩ :=
      ConservationPrefix.pureStepsW_chain_below φ a hwf 1 (by omega) hle1 hs1
    have h0 : (1 : Int) - 1 = ((0 : Nat) : Int) := by omega
    rw [h0] at hmem
    exact ⟨g, hmem, by rw [hcs]; simp, rest⟩
  | succ m ih =>
    intro hle hs
    have hlecast : (m : Int) + 2 ≤ stepCount φ := by omega
    have hs2 : ConservationPrefix.SatBelow φ a ((m : Int) + 2) := by exact_mod_cast hs
    obtain ⟨g, hmem, hcs, sel, hsc, hids⟩ :=
      ih (by omega) (ConservationPrefix.satBelow_mono hs2 (by omega))
    have hL := LineInv_stepsCima φ hwf m
    have hsok : ConservationFilter.StateOkF φ (m : Int) (selOfAssign φ a (m : Int), g) :=
      hL.1.2 _ hmem
    obtain ⟨d, hdd⟩ : ∃ d, d = selOfAssign φ a ((m : Int) + 1) := ⟨_, rfl⟩
    have hd0 : d = selOfAssign φ a g.current_step := by rw [hdd, hcs]
    have hson : d ∈ mapSons φ (selOfAssign φ a (m : Int)).step (selOfAssign φ a (m : Int)).index := by
      rw [hdd, selOfAssign_step]
      exact ConservationPrefix.selOfAssign_son_below φ a (m : Int) hs2 (by omega) (by omega)
    have hids' : ∀ k, 0 ≤ k → k < g.current_step →
        (sel k).id = selOfAssign φ a k ∧ ConservationCore.SelParent φ a (sel k) := by
      intro k h0 h1; exact hids k h0 (by rw [hcs] at h1; exact h1)
    have hkeep := ConservationPrefix.keepsBranch_Fsac_below φ a ((m : Int) + 2) hs2 0 d g sel hsc
      hids' hd0 (by omega)
    have hmp : g.map_parent = none ∨ ∃ j, g.map_parent = some (selOfAssign φ a j) :=
      Or.inr ⟨(m : Int), hsok.par⟩
    obtain ⟨sel', hsc', hcur, hids2⟩ :=
      ConservationCore.chainSound_up_of_prunedR φ a reviewAgg hwf g _
        (ConservationFilter.prunes_Fsac φ 0 _ g) hsok.shape hmp sel hkeep hids' ""
    have hsend : sent φ g d = AggressiveReview.upFilteringR reviewAgg
        (ConservationFilter.Fsac φ 0 d g)
        (reqOfCnf φ (selOfAssign φ a g.current_step)) (selOfAssign φ a g.current_step) "" := by
      rw [← hd0]; rfl
    have hscS : ChainSound (sent φ g d) sel' := by rw [hsend]; exact hsc'
    have hvS : isValid (sent φ g d) = true :=
      PickInduction.isValid_of_ChainG _ sel' hscS.chain
    obtain ⟨J, hJ, hgr⟩ := BranchLines.full_reach φ hwf (m : Int) _ hL
      (selOfAssign φ a (m : Int), g) hmem d hson hvS
    have hscJ : ChainSound J sel' := ChainSound_of_grown hgr sel' hscS
    have hcsS : (sent φ g d).current_step = (m : Int) + 2 := by
      rw [hsend, hcur, hcs]; omega
    have hcsJ : J.current_step = (m : Int) + 2 := by rw [hgr.step_eq, hcsS]
    have hcond : ((mapSons φ (selOfAssign φ a (m : Int)).step
        (selOfAssign φ a (m : Int)).index).contains d && isValid (sent φ g d)) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨List.contains_iff_mem.mpr hson, hvS⟩
    have hSmem : sent φ g d ∈ sidesOf φ (stepsCima φ m (pureInit φ)) d := by
      refine List.mem_filterMap.mpr ⟨(selOfAssign φ a (m : Int), g), hmem, ?_⟩
      rw [if_pos hcond]
    have hscC := ChainSound_reviewCima_of_side
      (sidesOf φ (stepsCima φ m (pureInit φ)) d) J _ hSmem sel' hscJ hscS
      (by rw [hcsS, hcsJ]) (by rw [hcsJ]; omega)
    refine ⟨_, ?_, ?_, sel', hscC, ?_⟩
    · rw [stepsCima_succ, show ((m + 1 : Nat) : Int) = (m : Int) + 1 by push_cast; omega, ← hdd]
      exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(d, J), hJ, rfl⟩,
        PickInduction.isValid_of_ChainG _ sel' hscC.chain⟩
    · rw [(keeps_reviewCima _ J).1.step_eq, hcsJ]; push_cast; omega
    · intro k h0 h1
      exact hids2 k h0 (by rw [hcs]; push_cast at h1; omega)

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
theorem side_of_top (_hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1)
    (S : GPathM) (hS : S ∈ sidesOf φ (L) p)
    (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (ht : (S.node? (topOf p kv.1)).isSome = true) :
    S = sent φ kv.2 p := by
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
      have := sent_top φ m kv' (hLI.1.2 kv' hkv') (hLI.2 kv' hkv') p hv' n hmem hstep
      rw [hnid] at this
      have : topOf p kv.1 = topOf p kv'.1 := this
      simpa [topOf] using this.symm
    rw [hSe, PureDriver.key_inj _ hLI.1.1 kv' hkv' kv hkv hkeys]
  · rw [if_neg hc] at hfe; contradiction

/-- **A side is a send.** Reading `sidesOf` backwards: every side is the valid send of a key of the
line into `p`. -/
theorem side_is_send (L : PureLine) (m : Nat) (_hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (S : GPathM) (hS : S ∈ sidesOf φ (L) p) :
    ∃ kv ∈ L, S = sent φ kv.2 p ∧ isValid (sent φ kv.2 p) = true := by
  obtain ⟨kv', hkv', hfe⟩ := List.mem_filterMap.mp hS
  by_cases hc : ((mapSons φ kv'.1.step kv'.1.index).contains p && isValid (sent φ kv'.2 p)) = true
  · rw [if_pos hc] at hfe
    simp only [Bool.and_eq_true] at hc
    exact ⟨kv', hkv', by injection hfe with h; exact h.symm, hc.2⟩
  · rw [if_neg hc] at hfe; contradiction

/-- **A live family names a real top.** The family keeps at least one entry, that entry is carried by a
side, and the side holds `t`; a side is a send, and a send has one node at the new step — its own top.
So the `t` the rule produced is the top of a key of the line, with nothing assumed about it but its
step. -/
theorem top_of_famFix (_hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (X : GPathM) (hrc : Reader.RCtx X) (hsmp : Sons.SMP X) (hpms : Sons.PMS X) (hsn : Sons.SN X)
    (hcsX : X.current_step = (m : Int) + 2) (t : PathNodeId)
    (hts : t.id.step = X.current_step - 1)
    (hv : isValid (famFix (sidesOf φ (L) p) t X) = true) :
    ∃ kv ∈ L, t = topOf p kv.1 ∧ isValid (sent φ kv.2 p) = true := by
  have hcsF : (famFix (sidesOf φ (L) p) t X).current_step = X.current_step :=
    (keeps_famFix _ _ X).1.step_eq
  have hm0 : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
  have hsup := sup_famFix (sidesOf φ (L) p) t X hrc hsmp hpms hsn hv
  have hadj := (adj_famFix (sidesOf φ (L) p) t X hrc hsmp hpms hsn hv).1
  have hv0 := hv
  simp only [isValid, List.all_eq_true] at hv0
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp
    (hv0 0 (mem_intRange (Int.le_refl 0) (by rw [hcsF, hcsX]; omega)))
  obtain ⟨n, hn, hnid⟩ := hadj.rc.gn q hq
  have hmq : EmbeddedSupport.Mem (famFix (sidesOf φ (L) p) t X) q :=
    ⟨n, by rw [← hnid]; exact node?_of_mem hadj.rc.nodup n hn⟩
  obtain ⟨v, hrel, hvs⟩ := hsup.cov q hmq 0 (Int.le_refl 0) (by rw [hcsF, hcsX]; omega)
  have hqz : q.id.step = 0 := eq_of_beq hqs
  have ht := restTest_of_famFix (sidesOf φ (L) p) t X
    (ReaderAgg.RCtx_of_keeps (keeps_restAll _ t X) hrc).nodup hv q v hrel
    (by rw [hqz]; omega) (by rw [hqz, hcsX]; omega) (by rw [hvs]; omega)
    (by rw [hvs, hcsX]; omega)
  simp only [restTest, Bool.and_eq_true] at ht
  obtain ⟨S, hS, hcond⟩ := List.any_eq_true.mp ht.1.1.1
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨kv', hkv', hSe, hvS⟩ := side_is_send φ L m hLI p S hS
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp hcond.1.1
  rw [hSe] at hnt
  have hid : nt.id = t := node?_id_eq _ _ nt hnt
  have htop := sent_top φ m kv' (hLI.1.2 kv' hkv') (hLI.2 kv' hkv') p hvS nt
    (List.mem_of_find?_eq_some hnt) (by rw [hid, hts, hcsX]; omega)
  exact ⟨kv', hkv', by rw [← hid]; exact htop, hvS⟩

/-- **What a good top hands over, in the side's own table.** Because the top names the side, every pair
the rule certifies with `carries` is a pair of that one side — which is exactly what the support of the
side's send needs. -/
theorem carries_in_side (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (a b : PathNodeId)
    (hc : carries (sidesOf φ (L) p) (topOf p kv.1) a b = true) :
    Rel (sent φ kv.2 p) a b ∧ Rel (sent φ kv.2 p) b a := by
  obtain ⟨S, hS, hcond⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true] at hcond
  have hSe := side_of_top φ hwf L m hLI p hps S hS kv hkv hcond.1.1
  rw [hSe] at hcond
  exact rel_of_owners _ a b hcond.1.2 hcond.2

/-- **From a live entry at the fixpoint to a good top.** Reading `cimaOk` backwards: the top is a node of
the last line, and `fam_closure` then gives the whole closure for it. -/
theorem top_of_cimaOk (sides : List GPathM) (g : GPathM) (a b : PathNodeId)
    (hok : cimaOk sides g a b = true) :
    ∃ t ∈ ((g.line (g.current_step - 1)).map (·.id)), goodFor sides g t a b = true := by
  simp only [cimaOk] at hok
  exact List.any_eq_true.mp hok

/-- A node named by a line is at that step. -/
theorem step_of_mem_line (F : GPathM) (l : Int) (t : PathNodeId)
    (h : t ∈ ((F.line l).map (·.id))) : t.id.step = l := by
  obtain ⟨n, hn, hid⟩ := List.mem_map.mp h
  rw [← hid]; exact eq_of_beq (List.mem_filter.mp hn).2

/-- **The parent link the side holds.** Same reading as `carries_in_side`, for the parent lists: what
the test keeps on neighbouring steps is a parent link of that one side. -/
theorem linked_in_side (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (a b : PathNodeId)
    (hl : linkedIn (sidesOf φ (L) p) (topOf p kv.1) a b = true) :
    ∃ na, (sent φ kv.2 p).node? a = some na ∧ b ∈ na.parents := by
  obtain ⟨S, hS, hcond⟩ := List.any_eq_true.mp hl
  simp only [Bool.and_eq_true] at hcond
  have hSe := side_of_top φ hwf L m hLI p hps S hS kv hkv hcond.1
  rw [hSe] at hcond
  cases hsa : (sent φ kv.2 p).node? a with
  | none => rw [hsa] at hcond; exact (Bool.false_ne_true hcond.2).elim
  | some na => rw [hsa] at hcond; exact ⟨na, rfl, List.contains_iff_mem.mp hcond.2⟩

/-- **What the family of a top gives, read in the side.** Every entry the family keeps is an entry of
the side's send, both ways; and on neighbouring steps it is one of its parent links. -/
theorem side_of_famFix (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (g : GPathM) (hnd : ((restAll (sidesOf φ (L) p) (topOf p kv.1) g).nodes.map
      (·.id)).Nodup)
    (hv : isValid (famFix (sidesOf φ (L) p) (topOf p kv.1) g) = true)
    (a b : PathNodeId) (h : Rel (famFix (sidesOf φ (L) p) (topOf p kv.1) g) a b)
    (ha0 : 0 ≤ a.id.step) (ha1 : a.id.step < g.current_step)
    (hb0 : 0 ≤ b.id.step) (hb1 : b.id.step < g.current_step) :
    Rel (sent φ kv.2 p) a b ∧ Rel (sent φ kv.2 p) b a ∧
      (b.id.step + 1 = a.id.step → ∃ na, (sent φ kv.2 p).node? a = some na ∧ b ∈ na.parents) := by
  have ht := restTest_of_famFix _ _ g hnd hv a b h ha0 ha1 hb0 hb1
  simp only [restTest, Bool.and_eq_true] at ht
  refine ⟨(carries_in_side φ hwf L m hLI p hps kv hkv a b ht.1.1.1).1,
    (carries_in_side φ hwf L m hLI p hps kv hkv a b ht.1.1.1).2, fun hstep => ?_⟩
  have hbe : (b.id.step + 1 == a.id.step) = true := beq_iff_eq.mpr hstep
  have := ht.1.2
  rw [hbe] at this
  exact linked_in_side φ hwf L m hLI p hps kv hkv a b (by simpa using this)

-- ============================================================
-- Cable 1: when one end is a side's top, the rule certifies that top
-- ============================================================

/-- **The rule cannot certify another top.** If the entry the rule keeps has a side's top `⟨p, key⟩` as
one end, the side that carries it holds that node, so it is the send of that key (`side_of_top`); and a
send has exactly one node at the new step, its own top (`sent_top`). So the top the rule certifies is
the one we are reading. -/
theorem cert_top_of_top (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (hsok : StateOkF φ m kv) (hmkv : MInv φ kv.2) (hvS : isValid (sent φ kv.2 p) = true)
    (X : GPathM) (hcsX : X.current_step = (m : Int) + 2)
    (hrc : Reader.RCtx X) (hsmp : Sons.SMP X) (hpms : Sons.PMS X) (hsn : Sons.SN X)
    (t₂ v : PathNodeId) (hts : t₂.id.step = X.current_step - 1)
    (hgood : goodFor (sidesOf φ (L) p) X t₂ (topOf p kv.1) v = true) :
    t₂ = topOf p kv.1 := by
  simp only [goodFor, Bool.and_eq_true] at hgood
  have hvY : isValid (famFix (sidesOf φ (L) p) t₂ X) = true := hgood.1.1
  have hrel : Rel (famFix (sidesOf φ (L) p) t₂ X) (topOf p kv.1) v :=
    (rel_of_owners _ _ v hgood.1.2 hgood.2).1
  have hadj := (adj_famFix (sidesOf φ (L) p) t₂ X hrc hsmp hpms hsn hvY).1
  have hcsY : (famFix (sidesOf φ (L) p) t₂ X).current_step = X.current_step :=
    (keeps_famFix _ t₂ X).1.step_eq
  have hm0 : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
  have hbv : 0 ≤ v.id.step ∧ v.id.step < X.current_step := by
    obtain ⟨_, _, _, hv2⟩ := hrel
    have := EmbeddedSupport.mem_bounds _ hadj hv2
    rw [hcsY] at this; exact this
  have ht : restTest (sidesOf φ (L) p) t₂ X (topOf p kv.1) v = true :=
    restTest_of_famFix _ t₂ X
      (ReaderAgg.RCtx_of_keeps (keeps_restAll _ t₂ X) hrc).nodup hvY _ v hrel
      (by rw [show (topOf p kv.1).id.step = p.step from rfl, hps]; omega)
      (by rw [show (topOf p kv.1).id.step = p.step from rfl, hps, hcsX]; omega) hbv.1 hbv.2
  simp only [restTest, Bool.and_eq_true] at ht
  obtain ⟨S₂, hS₂, hcond⟩ := List.any_eq_true.mp ht.1.1.1
  simp only [Bool.and_eq_true] at hcond
  have htnode : (S₂.node? (topOf p kv.1)).isSome = true := by
    unfold ownersOf at hcond
    cases hq : S₂.node? (topOf p kv.1) with
    | none => rw [hq] at hcond; exact nomatch List.contains_iff_mem.mp hcond.1.2
    | some _ => rfl
  have hSe := side_of_top φ hwf L m hLI p hps S₂ hS₂ kv hkv htnode
  obtain ⟨n₂, hn₂⟩ := Option.isSome_iff_exists.mp hcond.1.1
  rw [hSe] at hn₂
  have hid : n₂.id = t₂ := node?_id_eq _ _ n₂ hn₂
  have hstep : n₂.id.id.step = (m : Int) + 1 := by rw [hid, hts, hcsX]; omega
  have := sent_top φ m kv hsok hmkv p hvS n₂ (List.mem_of_find?_eq_some hn₂) hstep
  rw [← hid]; exact this

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

/-- **The side's pinned send stays live.** With the family as its support, the send survives the pins:
the family's nodes are nodes of the pinned union, so they respect the pins, and a support that survives
them leaves the state live. This is the conclusion `HereditaryValid.TopValidAt` asks for. -/
theorem valid_pinned_of_famSide (Y S : GPathM) (Q : List NodeId) (t : PathNodeId)
    (hY : AnchoredSurvive.Sup Y (EmbeddedSupport.Mem Y) (Rel Y))
    (hadj : AdjacentOwners.Adj Y) (hcs : Y.current_step = S.current_step)
    (hside : ∀ a b, Rel Y a b → Rel S a b ∧ Rel S b a ∧
      (b.id.step + 1 = a.id.step → ∃ na, S.node? a = some na ∧ b ∈ na.parents))
    (hgow : ∀ q n, S.node? q = some n → ∀ z ∈ n.owners, 0 ≤ z.id.step →
      z.id.step < S.current_step → z ∈ S.gowners)
    (hmemY : EmbeddedSupport.Mem Y t)
    (hsmpS : Sons.SMP S) (hnrS : Parents.NotRoot S)
    (hpin : ∀ r ∈ Q, ∀ x, EmbeddedSupport.Mem Y x → x.id.step = r.step → x.id = r) :
    isValid (AggressiveReview.filterAllAgg S Q) = true :=
  SupportSplit.valid_of_sup _ _ _
    (AnchoredSurvive.AOk_filterAllAgg S ⟨sup_of_famSide Y S hY hadj hcs hside hgow, hsmpS, hnrS⟩
      Q hpin).sup t hmemY

/-- **From one good top to the side's pinned send.** Everything the rule leaves is here: the family is
live, it holds the top, it is a support of the send, and its nodes are nodes of the pinned union, so
they respect the pins. -/
theorem valid_pinned_of_goodFor (sides : List GPathM) (X S : GPathM) (Q : List NodeId)
    (t v : PathNodeId)
    (hrc : Reader.RCtx X) (hsmp : Sons.SMP X) (hpms : Sons.PMS X) (hsn : Sons.SN X)
    (hcsXS : X.current_step = S.current_step)
    (hside : ∀ a b, Rel (famFix sides t X) a b → 0 ≤ a.id.step → a.id.step < X.current_step →
      0 ≤ b.id.step → b.id.step < X.current_step →
      Rel S a b ∧ Rel S b a ∧
        (b.id.step + 1 = a.id.step → ∃ na, S.node? a = some na ∧ b ∈ na.parents))
    (hgow : ∀ q n, S.node? q = some n → ∀ z ∈ n.owners, 0 ≤ z.id.step →
      z.id.step < S.current_step → z ∈ S.gowners)
    (hpinX : ∀ r ∈ Q, ∀ x, EmbeddedSupport.Mem X x → x.id.step = r.step → x.id = r)
    (hsmpS : Sons.SMP S) (hnrS : Parents.NotRoot S)
    (hgood : goodFor sides X t t v = true) :
    isValid (AggressiveReview.filterAllAgg S Q) = true := by
  simp only [goodFor, Bool.and_eq_true] at hgood
  have hvY : isValid (famFix sides t X) = true := hgood.1.1
  have hrel : Rel (famFix sides t X) t v :=
    (rel_of_owners _ t v hgood.1.2 hgood.2).1
  have hcsY : (famFix sides t X).current_step = X.current_step := (keeps_famFix sides t X).1.step_eq
  have hadj := (adj_famFix sides t X hrc hsmp hpms hsn hvY).1
  have hbnd : ∀ x, EmbeddedSupport.Mem (famFix sides t X) x →
      0 ≤ x.id.step ∧ x.id.step < X.current_step := by
    intro x hx
    have := EmbeddedSupport.mem_bounds _ hadj hx
    rw [hcsY] at this; exact this
  have hmemX : ∀ x, EmbeddedSupport.Mem (famFix sides t X) x → EmbeddedSupport.Mem X x := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    obtain ⟨n0, hn0, hid, _, _⟩ :=
      (keeps_famFix sides t X).1.nodes_derived n (List.mem_of_find?_eq_some hn)
    exact ⟨n0, by rw [← node?_id_eq _ x n hn, hid]; exact node?_of_mem hrc.nodup n0 hn0⟩
  refine valid_pinned_of_famSide (famFix sides t X) S Q t
    (sup_famFix sides t X hrc hsmp hpms hsn hvY) hadj (by rw [hcsY]; exact hcsXS) ?_ hgow
    (by obtain ⟨n, hn, _, _⟩ := hrel; exact ⟨n, hn⟩)
    hsmpS hnrS ?_
  · intro a b hab
    have hab' := hab
    obtain ⟨na, hna, _, hmb⟩ := hab'
    have ha := hbnd a ⟨na, hna⟩
    have hb := hbnd b hmb
    exact hside a b hab ha.1 ha.2 hb.1 hb.2
  · intro r hr x hx hs
    exact hpinX r hr x (hmemX x hx) hs

-- ============================================================
-- Cables 2 and 3: the verdict of a union, for the new machine
-- ============================================================

/-- **The side's pinned send stays live, for `ImprovesCima`.** This is `HereditaryValid.TopValidAt` for
the new machine, with no hypothesis left:

* the filtered union is a state of the machine's own kind (`sup_filterAllCima`), so the live top hangs
  on something;
* that entry has a good top, and since one end is the side's own top, it can only be that one
  (`cert_top_of_top`);
* its family is then a support of the side's send, and the send survives the pins
  (`valid_pinned_of_goodFor`). -/
theorem topValid_cima (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId) (J : GPathM)
    (hsJ : StateOkF φ ((m : Int) + 1) (p, J)) (hmJ : MInv φ J) (Q : List NodeId)
    (hvX : isValid (filterAllCima (sidesOf φ (L) p) J Q) = true)
    (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (hson : p ∈ mapSons φ kv.1.step kv.1.index) (hvS : isValid (sent φ kv.2 p) = true)
    (hmem : EmbeddedSupport.Mem (filterAllCima (sidesOf φ (L) p) J Q)
      (topOf p kv.1)) :
    isValid (AggressiveReview.filterAllAgg (sent φ kv.2 p) Q) = true := by
  have hps : p.step = (m : Int) + 1 := mapNodes_step φ _ p hsJ.onMap
  have hsok : StateOkF φ m kv := hLI.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hLI.2 kv hkv
  have hmS := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv p hson hvS
  have hsS := ConservationFilter.StateOkF_sent φ (ConservationFilter.Fsac φ 0) reviewAgg
    (ConservationFilter.prunes_Fsac φ 0) m kv hsok p hson hvS
  have hsS' : (sent φ kv.2 p).current_step = (m : Int) + 1 + 1 := hsS.step
  have hcsS : (sent φ kv.2 p).current_step = (m : Int) + 2 := by omega
  -- the invariants of the filtered union
  have hkJX : Keeps J (filterAllCima (sidesOf φ (L) p) J Q) :=
    keeps_filterAllCima _ J Q
  have hrcX := ReaderAgg.RCtx_of_keeps hkJX hmJ.rctx
  obtain ⟨s1, s2, s3⟩ := sons_filterAllCima (sidesOf φ (L) p) J Q hmJ.smp hmJ.pms
    hmJ.sn hmJ.rctx.shape.notroot
  have hcsX : (filterAllCima (sidesOf φ (L) p) J Q).current_step = (m : Int) + 2 := by
    rw [hkJX.1.step_eq, hsJ.step]; omega
  obtain ⟨hadjX, hsupX⟩ := sup_filterAllCima (sidesOf φ (L) p) J Q hmJ.rctx hmJ.smp
    hmJ.pms hmJ.sn hmJ.rctx.shape.notroot hvX
  have hm0 : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
  -- the live top hangs on something, and the rule gives that entry a good top
  obtain ⟨v, hrelv, _⟩ := hsupX.cov (topOf p kv.1) hmem 0 (Int.le_refl 0) (by rw [hcsX]; omega)
  obtain ⟨nt, hnt, hmemv, hmv⟩ := id hrelv
  have hbv := EmbeddedSupport.mem_bounds _ hadjX hmv
  obtain ⟨nv, hnv⟩ := hmv
  have hok := cimaOk_filterAllCima (sidesOf φ (L) p) J Q hvX (topOf p kv.1) nt v hnt
    (by rw [hnv]; rfl)
    (by rw [show (topOf p kv.1).id.step = p.step from rfl, hps]; omega)
    (by rw [show (topOf p kv.1).id.step = p.step from rfl, hps, hcsX]; omega)
    hbv.1 hbv.2 hmemv
  obtain ⟨t₂, htm, hgood⟩ := top_of_cimaOk _ _ (topOf p kv.1) v hok
  have hts : t₂.id.step = (filterAllCima (sidesOf φ (L) p) J Q).current_step - 1 :=
    step_of_mem_line _ _ t₂ htm
  rw [cert_top_of_top φ hwf L m hLI p hps kv hkv hsok hmkv hvS _ hcsX hrcX s1 s2 s3 t₂ v hts hgood]
    at hgood
  -- and its family is a support of the side's send
  have hvY : isValid (famFix (sidesOf φ (L) p) (topOf p kv.1)
      (filterAllCima (sidesOf φ (L) p) J Q)) = true := by
    simp only [goodFor, Bool.and_eq_true] at hgood; exact hgood.1.1
  refine valid_pinned_of_goodFor (sidesOf φ (L) p) _ (sent φ kv.2 p) Q
    (topOf p kv.1) v hrcX s1 s2 s3 (by rw [hcsX, hcsS]) ?_
    (PinDeath.sent_ownGow φ hwf m kv hsok hmkv p hson hvS) ?_ hmS.smp hmS.rctx.shape.notroot hgood
  · intro a b hab ha0 ha1 hb0 hb1
    exact side_of_famFix φ hwf L m hLI p hps kv hkv _
      (ReaderAgg.RCtx_of_keeps (keeps_restAll _ _ _) hrcX).nodup hvY a b hab ha0 ha1 hb0 hb1
  · intro r hr x hx hs
    exact ReaderAggRun.filterAllAgg_cleans J Q r hr x
      ((keeps_agg_filterAllCima (sidesOf φ (L) p) J Q).1.gowners_sub x
        (hsupX.gow x hx)) hs


/-- **The descent, with the rule.** The same step as `HereditaryValid.pinned_source_validL` — a valid
pinned send has a valid pinned source — but closing with the filter of `ImprovesCima` instead of the
plain review. The support it hands down is the part of the pinned send below its top; the rule keeps it
as long as one side of the source carries its pairs, which `carriedR_of_side` turns into the rule's
hypothesis. -/
theorem pinned_source_validCima (sides : List GPathM) (hwf : WF φ) (k : Int) (key : NodeId)
    (G : GPathM) (hsG : ConservationFilter.StateOkF φ k (key, G)) (hmG : MInv φ G) (d : NodeId)
    (hd : d ∈ mapSons φ key.step key.index) (hval : isValid (sent φ G d) = true) (Q : List NodeId)
    (hvY : isValid (AggressiveReview.filterAllAgg (sent φ G d) Q) = true)
    (t : PathNodeId) (ht : t.id.step = G.current_step - 1)
    (hSt : EmbeddedSupport.Mem (AggressiveReview.filterAllAgg (sent φ G d) Q) t ∧
      t.id.step < k + 1)
    (hR : ∀ x v, (Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧ x.id.step < k + 1 ∧
      v.id.step < k + 1) → restTest sides t G x v = true) :
    isValid (filterAllCima sides G
      ((reqOfCnf φ d ++ Q).filter (fun q => decide (q.step < k + 1)))) = true := by
  obtain ⟨hA, hpin, z, hz⟩ :=
    HereditaryValid.pinned_source_support φ hwf k key G hsG hmG d hd hval Q hvY
  exact SupportSplit.valid_of_sup _ _ _
    (AOk_filterAllCima sides G hA _ hpin (carriedR_of_side sides G t ht hSt hR)).sup z hz

/-- **What the descent still asks for, named.** The support the descent hands down — the part of the
pinned send below its top — must be carried by **one** side of the source, with its top alive in it.

This is the same shape as the property the rule already forces at a union, one line below: there, the
top names the side and the family is computed, so it holds by construction (`topValid_cima`). Here the
support comes down from above and the side has to be found. Per entry it is granted (the state passed
the rule, so every live entry has a good top); what is asked is one single side for the whole support,
which is the step the review cannot take pair by pair. -/
def SideSupportAt (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId) (Q : List NodeId) :
    Prop :=
  ∃ t, t.id.step = G.current_step - 1 ∧
    (EmbeddedSupport.Mem (AggressiveReview.filterAllAgg (sent φ G d) Q) t ∧ t.id.step < k + 1) ∧
    ∀ x v, (Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧ x.id.step < k + 1 ∧
      v.id.step < k + 1) → restTest sides t G x v = true

/-- **The descent with the rule, under that property alone.** -/
theorem pinned_source_valid_of_sideSupport (sides : List GPathM) (hwf : WF φ) (k : Int)
    (key : NodeId) (G : GPathM) (hsG : ConservationFilter.StateOkF φ k (key, G)) (hmG : MInv φ G)
    (d : NodeId) (hd : d ∈ mapSons φ key.step key.index) (hval : isValid (sent φ G d) = true)
    (Q : List NodeId) (hvY : isValid (AggressiveReview.filterAllAgg (sent φ G d) Q) = true)
    (hS : SideSupportAt φ sides k G d Q) :
    isValid (filterAllCima sides G
      ((reqOfCnf φ d ++ Q).filter (fun q => decide (q.step < k + 1)))) = true := by
  obtain ⟨t, ht, hSt, hR⟩ := hS
  exact pinned_source_validCima φ sides hwf k key G hsG hmG d hd hval Q hvY t ht hSt hR

-- ============================================================
-- The shape of a family: a cone over its top
-- ============================================================


/-- **What the descent actually asks for.** Not one side for the whole support — the rule's test is
existential over the tops, so the sweep is content if **each pair** of the support is held by some
sub-support that some side carries. Different pairs may name different sides.

This is strictly weaker than `SideSupportAt`, and it is the shape the rule already grants one line
below: the state passed the rule, so every live entry has a good top whose family is a support inside
that top's side. -/
def PairSideAt (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId) (Q : List NodeId) : Prop :=
  ∀ g', Keeps G g' →
    AOk g' (fun p => EmbeddedSupport.Mem (AggressiveReview.filterAllAgg (sent φ G d) Q) p ∧
              p.id.step < k + 1)
           (fun x v => Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧
              x.id.step < k + 1 ∧ v.id.step < k + 1) →
    ∀ x v, (Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧
        x.id.step < k + 1 ∧ v.id.step < k + 1) →
      ∃ (S' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop) (t : PathNodeId),
        t.id.step = G.current_step - 1 ∧ S' t ∧ R' x v ∧ AOk g' S' R' ∧
        (∀ a b, R' a b → restTest sides t G a b = true)

/-- **The descent with the rule, under the per-pair property alone.** -/
theorem pinned_source_valid_of_pairSide (sides : List GPathM) (hwf : WF φ) (k : Int)
    (key : NodeId) (G : GPathM) (hsG : ConservationFilter.StateOkF φ k (key, G)) (hmG : MInv φ G)
    (d : NodeId) (hd : d ∈ mapSons φ key.step key.index) (hval : isValid (sent φ G d) = true)
    (Q : List NodeId) (hvY : isValid (AggressiveReview.filterAllAgg (sent φ G d) Q) = true)
    (hP : PairSideAt φ sides k G d Q) :
    isValid (filterAllCima sides G
      ((reqOfCnf φ d ++ Q).filter (fun q => decide (q.step < k + 1)))) = true := by
  obtain ⟨hA, hpin, z, hz⟩ :=
    HereditaryValid.pinned_source_support φ hwf k key G hsG hmG d hd hval Q hvY
  exact SupportSplit.valid_of_sup _ _ _
    (AOk_filterAllCima sides G hA _ hpin (carriedR_of_pair sides G hP)).sup z hz

/-- **The old form is the special case where every pair names the same side.** -/
theorem pairSide_of_sideSupport (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId)
    (Q : List NodeId) (h : SideSupportAt φ sides k G d Q) : PairSideAt φ sides k G d Q := by
  obtain ⟨t, ht, hSt, hR⟩ := h
  exact fun _ _ hA x v hr => ⟨_, _, t, ht, hSt, hr, hA, hR⟩


/-- **The descent, in the currency this project measures: one chain per pair.** At every narrowing where
the descent's support still lives, each of its pairs lies on a sound chain of that narrowing, and one
side carries the whole chain. The side is not quantified: it is the chain's own node at the last step,
which is the top that names it.

This is `PairChain` — "every owner pair lies on a chain" — localized to the descent, and it is what the
rule of the top already grants entry by entry one line below. -/
def ChainSideAt (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId) (Q : List NodeId) : Prop :=
  ∀ g', Keeps G g' →
    AOk g' (fun p => EmbeddedSupport.Mem (AggressiveReview.filterAllAgg (sent φ G d) Q) p ∧
              p.id.step < k + 1)
           (fun x v => Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧
              x.id.step < k + 1 ∧ v.id.step < k + 1) →
    ∀ x v, (Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧
        x.id.step < k + 1 ∧ v.id.step < k + 1) →
      ∃ (sel : Int → PathNodeId) (i j : Int), ChainSound g' sel ∧
        0 ≤ i ∧ i < g'.current_step ∧ 0 ≤ j ∧ j < g'.current_step ∧ x = sel i ∧ v = sel j ∧
        ∀ a b, (∃ p q, 0 ≤ p ∧ p < g'.current_step ∧ 0 ≤ q ∧ q < g'.current_step ∧
            a = sel p ∧ b = sel q) →
          restTest sides (sel (G.current_step - 1)) G a b = true

/-- **A chain per pair is enough for the descent.** The chain is the sub-support (`sup_of_chainSound`),
and its own top is the side that carries it. -/
theorem pairSide_of_chainSide (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId)
    (Q : List NodeId) (hcs : 0 < G.current_step) (h : ChainSideAt φ sides k G d Q) :
    PairSideAt φ sides k G d Q := by
  intro g' hk hA x v hr
  obtain ⟨sel, i, j, hsc, hi0, hi1, hj0, hj1, hxe, hve, hcar⟩ := h g' hk hA x v hr
  have hcs' : g'.current_step = G.current_step := hk.1.step_eq
  refine ⟨_, _, sel (G.current_step - 1), ?_, ⟨G.current_step - 1, by omega, by omega, rfl⟩,
    ⟨i, j, hi0, hi1, hj0, hj1, hxe, hve⟩,
    ⟨sup_of_chainSound g' sel hsc, hA.smp, hA.nr⟩, hcar⟩
  exact (hsc.chain.1.1 (G.current_step - 1) (by omega) (by omega)).2


/-- **The descent's obligation, in its final form.** Every pair of the support lies on a chain that is
sound **both** in the narrowing and in one side. Nothing else: no top to find, no side to choose, no
support to compute. This is the pair of hypotheses the rule already consumes everywhere else
(`carried_of_side`, `ChainSound_reviewCima_of_side`). -/
def SideChainAt (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId) (Q : List NodeId) :
    Prop :=
  ∀ g', Keeps G g' →
    AOk g' (fun p => EmbeddedSupport.Mem (AggressiveReview.filterAllAgg (sent φ G d) Q) p ∧
              p.id.step < k + 1)
           (fun x v => Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧
              x.id.step < k + 1 ∧ v.id.step < k + 1) →
    ∀ x v, (Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧
        x.id.step < k + 1 ∧ v.id.step < k + 1) →
      ∃ (sel : Int → PathNodeId) (Sd : GPathM) (i j : Int), Sd ∈ sides ∧
        Sd.current_step = G.current_step ∧ ChainSound g' sel ∧ ChainSound Sd sel ∧
        0 ≤ i ∧ i < g'.current_step ∧ 0 ≤ j ∧ j < g'.current_step ∧ x = sel i ∧ v = sel j

/-- **A chain sound in one side is all the descent needs.** -/
theorem chainSide_of_sideChain (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId)
    (Q : List NodeId) (hcs : 0 < G.current_step) (h : SideChainAt φ sides k G d Q) :
    ChainSideAt φ sides k G d Q := by
  intro g' hk hA x v hr
  obtain ⟨sel, Sd, i, j, hS, hcsS, hsc, hscS, hi0, hi1, hj0, hj1, hxe, hve⟩ := h g' hk hA x v hr
  have hcs' : g'.current_step = G.current_step := hk.1.step_eq
  refine ⟨sel, i, j, hsc, hi0, hi1, hj0, hj1, hxe, hve, ?_⟩
  rintro a b ⟨p, q, hp0, hp1, hq0, hq1, rfl, rfl⟩
  exact restTest_of_chain sides Sd hS sel hscS (G.current_step - 1) (by omega) (by omega) G
    p q hp0 (by omega) hq0 (by omega)

/-- **The descent, straight from a chain in one side.** -/
theorem pinned_source_valid_of_sideChain (sides : List GPathM) (hwf : WF φ) (k : Int)
    (key : NodeId) (G : GPathM) (hsG : ConservationFilter.StateOkF φ k (key, G)) (hmG : MInv φ G)
    (d : NodeId) (hd : d ∈ mapSons φ key.step key.index) (hval : isValid (sent φ G d) = true)
    (Q : List NodeId) (hvY : isValid (AggressiveReview.filterAllAgg (sent φ G d) Q) = true)
    (hcs : 0 < G.current_step) (h : SideChainAt φ sides k G d Q) :
    isValid (filterAllCima sides G
      ((reqOfCnf φ d ++ Q).filter (fun q => decide (q.step < k + 1)))) = true :=
  pinned_source_valid_of_pairSide φ sides hwf k key G hsG hmG d hd hval Q hvY
    (pairSide_of_chainSide φ sides k G d Q hcs (chainSide_of_sideChain φ sides k G d Q hcs h))



/-- **A chain of a family is a chain of its side.** Every pair it uses is a pair of the side
(`side_of_famFix`), its parent links are the side's, and a node of a send that owns something is a
global owner there (`sent_ownGow`). So the second half of `CimaChain` — "sound in one side" — is not a
condition at all: it comes free with the chain. -/
theorem chainSound_side_of_famFix (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (hsok : ConservationFilter.StateOkF φ m kv) (hmkv : MInv φ kv.2)
    (hson : p ∈ mapSons φ kv.1.step kv.1.index) (hvS : isValid (sent φ kv.2 p) = true)
    (g : GPathM) (hrc : Reader.RCtx g)
    (hcsg : g.current_step = (m : Int) + 2)
    (hv : isValid (famFix (sidesOf φ (L) p) (topOf p kv.1) g) = true)
    (sel : Int → PathNodeId)
    (hsc : ChainSound (famFix (sidesOf φ (L) p) (topOf p kv.1) g) sel) :
    ChainSound (sent φ kv.2 p) sel := by
  have hcsF : (famFix (sidesOf φ (L) p) (topOf p kv.1) g).current_step =
      g.current_step := (keeps_famFix _ _ g).1.step_eq
  have hsS := ConservationFilter.StateOkF_sent φ (ConservationFilter.Fsac φ 0) reviewAgg
    (ConservationFilter.prunes_Fsac φ 0) m kv hsok p hson hvS
  have hsS' : (sent φ kv.2 p).current_step = (m : Int) + 1 + 1 := hsS.step
  have hcsS : (sent φ kv.2 p).current_step = g.current_step := by rw [hsS', hcsg]; omega
  have hmS := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv p hson hvS
  have hnd := (ReaderAgg.RCtx_of_keeps (keeps_restAll
    (sidesOf φ (L) p) (topOf p kv.1) g) hrc).nodup
  have hst := chain_step _ sel hsc
  have hside : ∀ i j, 0 ≤ i →
      i < (famFix (sidesOf φ (L) p) (topOf p kv.1) g).current_step → 0 ≤ j →
      j < (famFix (sidesOf φ (L) p) (topOf p kv.1) g).current_step →
      Rel (sent φ kv.2 p) (sel i) (sel j) ∧ Rel (sent φ kv.2 p) (sel j) (sel i) ∧
        ((sel j).id.step + 1 = (sel i).id.step →
          ∃ na, (sent φ kv.2 p).node? (sel i) = some na ∧ sel j ∈ na.parents) := by
    intro i j hi0 hi1 hj0 hj1
    exact side_of_famFix φ hwf L m hLI p hps kv hkv g hnd hv (sel i) (sel j)
      (rel_of_chainSound _ sel hsc i j hi0 hi1 hj0 hj1)
      (by rw [hst i hi0 hi1]; exact hi0) (by rw [hst i hi0 hi1, ← hcsF]; exact hi1)
      (by rw [hst j hj0 hj1]; exact hj0) (by rw [hst j hj0 hj1, ← hcsF]; exact hj1)
  refine chainSound_transfer _ _ sel hsc (by rw [hcsS, hcsF]) hmS.smp
    (fun i j hi0 hi1 hj0 hj1 => (hside i j hi0 hi1 hj0 hj1).1) (fun i h0 h1 => ?_)
    (fun i h0 h1 => ?_)
  · obtain ⟨n, hn, hmem, _⟩ := (hside i i h0 h1 h0 h1).1
    exact PinDeath.sent_ownGow φ hwf m kv hsok hmkv p hson hvS (sel i) n hn (sel i) hmem
      (by rw [hst i h0 h1]; exact h0) (by rw [hst i h0 h1, hcsS, ← hcsF]; exact h1)
  · have hi1 : i < (famFix (sidesOf φ (L) p) (topOf p kv.1) g).current_step := by
      omega
    exact (hside (i + 1) i (by omega) h1 h0 hi1).2.2
      (by rw [hst i h0 hi1, hst (i + 1) (by omega) h1])


/-- **A chain that lives in a side keeps its state alive, rule and all.** Everything the state needs is
the chain itself: the chain is the support (`sup_of_chainSound`), its own side answers the rule at every
narrowing the sweep reaches (`carried_of_side`, `cimaOk_of_chain`), and a support with a member makes a
state valid (`valid_of_sup`). No send, no descent and no choice: a state carrying one chain of one side
survives the pins the chain respects and the whole review with the rule. -/
theorem valid_filterAllCima_of_chain (sides : List GPathM) (G : GPathM) (hmG : ReaderAggRun.MInv φ G)
    (hcs : 0 < G.current_step) (reqs : List NodeId) (sel : Int → PathNodeId)
    (Sd : GPathM) (hSd : Sd ∈ sides) (hcsSd : Sd.current_step = G.current_step)
    (hscG : ChainSound G sel) (hscSd : ChainSound Sd sel)
    (hpins : ∀ r ∈ reqs, 0 ≤ r.step → r.step < G.current_step → (sel r.step).id = r) :
    isValid (filterAllCima sides G reqs) = true := by
  have hst := chain_step G sel hscG
  have hA : AOk G (fun p => ∃ k, 0 ≤ k ∧ k < G.current_step ∧ p = sel k)
      (fun x v => ∃ i j, 0 ≤ i ∧ i < G.current_step ∧ 0 ≤ j ∧ j < G.current_step ∧
        x = sel i ∧ v = sel j) :=
    ⟨sup_of_chainSound G sel hscG, hmG.smp, hmG.rctx.shape.notroot⟩
  refine SupportSplit.valid_of_sup _ _ _
    (AOk_filterAllCimaC sides G (fun s => s = sel) hA (fun s hs => by rw [hs]; exact hscG) reqs
      ?_ ?_ (fun s hs => by rw [hs]; exact carried_of_side sides G Sd hSd sel hscSd hcsSd hcs)
      ?_).sup (sel 0) ⟨0, Int.le_refl 0, hcs, rfl⟩
  · rintro r hr p ⟨i, hi0, hi1, rfl⟩ hstep
    rw [hst i hi0 hi1] at hstep
    rw [hstep] at hi0 hi1 ⊢
    exact hpins r hr hi0 hi1
  · intro r hr s hs h0 h1
    rw [hs]; exact hpins r hr h0 h1
  · rintro g' hk hch _ x v ⟨i, j, hi0, hi1, hj0, hj1, rfl, rfl⟩
    have hcs' : g'.current_step = G.current_step := hk.1.step_eq
    exact cimaOk_of_chain sides g' Sd hSd (by rw [hcs']; exact hcsSd) sel (hch sel rfl) hscSd
      (by rw [hcs']; exact hcs) i j hi0 (by omega) hj0 (by omega)

-- ============================================================
-- The rule, as a single sentence about the filter
-- ============================================================

/-- The filtered union of `ImprovesCima` is a readable state of the base reader: the review's result is
an aggressive-review fixpoint of a narrowing. -/
theorem readableAgg_filterAllCima (sides : List GPathM) (g : GPathM) (reqs : List NodeId)
    (hrc : Reader.RCtx g) : ReaderAgg.ReadableAgg (filterAllCima sides g reqs) := by
  obtain ⟨g₀, hk, he⟩ := filterAllCima_form sides g reqs
  exact ⟨g₀, [], ReaderAgg.RCtx_of_keeps hk hrc, he⟩

/-- **The rule never kills a live state.** At a union by key, whatever the pins, if the state survives
the plain review it survives the review with the rule.

This is everything that is left of the verdict of `ImprovesCima`, said in one line about the filter's
behaviour — no families, no tops, no supports. -/
def RulePreservesValidity (L : PureLine) : Prop :=
  ∀ (p : NodeId) (J : GPathM), (p, J) ∈ pureAdvanceW φ L → ∀ Q : List NodeId,
    isValid (AggressiveReview.filterAllAgg J Q) = true →
    isValid (filterAllCima (sidesOf φ L p) J Q) = true

/-- **From it, validity is never borrowed.** The rule keeps the state alive, a live state has a side
with its top alive (`side_top_alive_of`), and for that side the rule's own theorem gives the pinned send
(`topValid_cima`). -/
theorem validSide_of_rulePreserves (hwf : WF φ) (m : Nat)
    (h : RulePreservesValidity φ (branchLine φ [] m)) : HereditaryValid.ValidSideAt φ m := by
  intro p J hJ Q _ hvX
  have hl := branchLine_inv φ hwf [] m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ := hadv.1.2 _ hJ
  have hmJ := hadv.2 _ hJ
  have hvC : isValid (filterAllCima (sidesOf φ (branchLine φ [] m) p) J Q) = true :=
    h p J hJ Q hvX
  obtain ⟨kv, hkv, hson, hvS, hmem⟩ := HereditaryValid.side_top_alive_of φ hwf [] m p J hJ _
    (keeps_filterAllCima _ J Q).1 (readableAgg_filterAllCima _ J Q hmJ.rctx) hvC
  exact ⟨kv, hkv, hson, hvS,
    topValid_cima φ hwf (branchLine φ [] m) m hl p J hsJ hmJ Q hvC kv hkv hson hvS hmem⟩


/-- **And nothing is lost in the translation.** If the union has a genuine path through the pins, the
rule keeps it alive: the path is a chain of the union (`line_complete`) and of the side its top names
(`advance_top_node`, `send_complete`), and a chain of a side keeps its state alive
(`valid_filterAllCima_of_chain`).

So `RulePreservesValidity` is not a stronger demand than the verdict — it is the verdict, said about
the filter. -/
theorem rulePreserves_of_genuine (hwf : WF φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (p : NodeId) (J : GPathM) (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ [] m))
    (Q : List NodeId) (sel : Int → PathNodeId)
    (hgen : RunNoBorrow.Genuine φ ((m : Int) + 2) sel)
    (htop : (sel ((m : Int) + 1)).id = p)
    (hpass : ∀ r ∈ Q, 0 ≤ r.step → r.step < (m : Int) + 2 → (sel r.step).id = r) :
    isValid (filterAllCima (sidesOf φ (branchLine φ [] m) p) J Q) = true := by
  have hl := branchLine_inv φ hwf [] m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ := hadv.1.2 _ hJ
  have hmJ := hadv.2 _ hJ
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  -- the path is a chain of the union
  have hmemJ : (p, J) ∈ PureDriverImproves.pureStepsW φ (m + 1) (pureInit φ) := by
    rw [RunHistory.pureStepsW_succ, ← PinHistory.branchLine_nil φ m]; exact hJ
  have hscJ : ChainSound J sel := by
    refine RunNoBorrow.line_complete φ hwf (m + 1) (by push_cast; omega) (p, J) hmemJ sel ?_ ?_
    · have : ((m + 1 : Nat) : Int) + 1 = (m : Int) + 2 := by push_cast; omega
      rw [this]; exact hgen
    · show (sel ((m + 1 : Nat) : Int)).id = p
      rw [show ((m + 1 : Nat) : Int) = (m : Int) + 1 by push_cast; omega]; exact htop
  -- its top node names a side, which is therefore alive
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp
    (hscJ.chain.1.1 ((m : Int) + 1) (by omega) (by rw [hcsJ]; omega)).1
  obtain ⟨kv, hkv, hson, hvS, htn, _⟩ := PinDeath.advance_top_node φ hwf [] m p J hJ nt
    (List.mem_of_find?_eq_some hnt)
    (by rw [node?_id_eq _ _ nt hnt,
      (hscJ.chain.1.1 ((m : Int) + 1) (by omega) (by rw [hcsJ]; omega)).2])
  have hid : nt.id = sel ((m : Int) + 1) := node?_id_eq _ _ nt hnt
  -- the path is a chain of that side
  have hsrc : (sel (m : Int)).id = kv.1 := by
    obtain ⟨a, _, hsel⟩ := hgen
    have h1 := (hsel ((m : Int) + 1) (by omega) (by omega)).2
    have h2 := (hsel (m : Int) (by omega) (by omega)).1
    have heq : sel ((m : Int) + 1) = topOf p kv.1 := hid.symm.trans htn
    have h3 : (sel ((m : Int) + 1)).parent_id = some kv.1 := by rw [heq]; rfl
    rw [h1] at h3
    rw [h2]
    rw [if_neg (by omega)] at h3
    have : selOfAssign φ a ((m : Int) + 1 - 1) = kv.1 := by
      injection h3
    rw [show (m : Int) + 1 - 1 = (m : Int) by omega] at this
    exact this
  have hkv' : kv ∈ PureDriverImproves.pureStepsW φ m (pureInit φ) := by
    rw [← PinHistory.branchLine_nil φ m]; exact hkv
  have hscS : ChainSound (sent φ kv.2 p) sel :=
    RunNoBorrow.send_complete φ hwf m hm kv hkv' p hson hvS sel hgen hsrc htop
  have hSmem : sent φ kv.2 p ∈ sidesOf φ (branchLine φ [] m) p := by
    refine List.mem_filterMap.mpr ⟨kv, hkv, ?_⟩
    rw [if_pos (by
      simp only [Bool.and_eq_true]
      exact ⟨List.contains_iff_mem.mpr hson, hvS⟩)]
  have hcsS : (sent φ kv.2 p).current_step = J.current_step := by
    have hsS := ConservationFilter.StateOkF_sent φ (ConservationFilter.Fsac φ 0) reviewAgg
      (ConservationFilter.prunes_Fsac φ 0) m kv (hl.1.2 kv hkv) p hson hvS
    have hsS' : (sent φ kv.2 p).current_step = (m : Int) + 1 + 1 := hsS.step
    rw [hsS', hcsJ]; omega
  exact valid_filterAllCima_of_chain φ _ J hmJ (by rw [hcsJ]; omega) Q sel _ hSmem hcsS hscJ hscS
    (fun r hr h0 h1 => hpass r hr h0 (by rw [hcsJ] at h1; exact h1))


/-- **A live pinned union contains a chain.** This is all that is left of the verdict: the two other
halves of `RulePreservesValidity` are already paid. That the chain lives in one side is free — a chain
of a machine state is a genuine path (`genuine_of_chain`) and a send holds every genuine path through
its source (`send_complete`). That it respects the pins is free too — a chain of a pinned state has its
nodes among the global owners, and pinning leaves only the pin there. -/
def PinnedUnionInhabited (L : PureLine) : Prop :=
  ∀ (p : NodeId) (J : GPathM), (p, J) ∈ pureAdvanceW φ L → ∀ Q : List NodeId,
    isValid (AggressiveReview.filterAllAgg J Q) = true →
    ∃ sel, ChainSound (AggressiveReview.filterAllAgg J Q) sel

/-- **One chain of the live pinned union is enough for the rule to keep it.** -/
theorem rulePreserves_of_chain (hwf : WF φ) (m : Nat)
    (p : NodeId) (J : GPathM) (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ [] m))
    (Q : List NodeId) (sel : Int → PathNodeId)
    (hsc : ChainSound (AggressiveReview.filterAllAgg J Q) sel) :
    isValid (filterAllCima (sidesOf φ (branchLine φ [] m) p) J Q) = true := by
  have hl := branchLine_inv φ hwf [] m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ := hadv.1.2 _ hJ
  have hmJ := hadv.2 _ hJ
  have hm : (m : Int) + 2 ≤ stepCount φ := by
    have := PinVar.lt_of_mapNodes φ _ p hsJ.onMap; omega
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  have hcsX : (AggressiveReview.filterAllAgg J Q).current_step = (m : Int) + 2 := by
    rw [(AggressiveReview.pruned_filterAllAgg J Q).step_eq, hcsJ]
  -- the chain of the pinned union is a chain of the union
  have hscJ : ChainSound J sel := SubsetSemantics.ChainSound_of_pruned
    (AggressiveReview.pruned_filterAllAgg J Q) hmJ.rctx.nodup hmJ.smp sel hsc
  -- and a chain of a machine state is a genuine path
  have hgen := RunNoBorrow.genuine_of_chain φ hwf m J hmJ hcsJ (by omega) sel hscJ
  -- its node at the new step is the union's key
  have htop : (sel ((m : Int) + 1)).id = p := by
    obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp
      (hscJ.chain.1.1 ((m : Int) + 1) (by omega) (by rw [hcsJ]; omega)).1
    obtain ⟨kv, _, _, _, htn, _⟩ := PinDeath.advance_top_node φ hwf [] m p J hJ nt
      (List.mem_of_find?_eq_some hnt)
      (by rw [node?_id_eq _ _ nt hnt,
        (hscJ.chain.1.1 ((m : Int) + 1) (by omega) (by rw [hcsJ]; omega)).2])
    rw [← node?_id_eq _ _ nt hnt, htn]; rfl
  -- and it respects the pins, because it lives in the pinned state
  have hpass : ∀ r ∈ Q, 0 ≤ r.step → r.step < (m : Int) + 2 → (sel r.step).id = r := by
    intro r hr h0 h1
    exact ReaderAggRun.filterAllAgg_cleans J Q r hr (sel r.step)
      (hsc.chain.2.2 r.step h0 (by rw [hcsX]; exact h1))
      ((hsc.chain.1.1 r.step h0 (by rw [hcsX]; exact h1)).2)
  exact rulePreserves_of_genuine φ hwf m hm p J hJ Q sel hgen htop hpass

/-- **The reduction.** Everything the rule needs is that a live pinned union be inhabited. -/
theorem rulePreserves_of_inhabited (hwf : WF φ) (m : Nat)
    (h : PinnedUnionInhabited φ (branchLine φ [] m)) :
    RulePreservesValidity φ (branchLine φ [] m) := by
  intro p J hJ Q hv
  obtain ⟨sel, hsc⟩ := h p J hJ Q hv
  exact rulePreserves_of_chain φ hwf m p J hJ Q sel hsc

/-- **The verdict of `ImprovesCima`, from that one sentence.** -/
theorem sat_of_rulePreserves (hwf : WF φ)
    (h : ∀ m : Nat, RulePreservesValidity φ (branchLine φ [] m))
    (kv : NodeId × GPathM) (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (AggressiveReview.filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  HereditaryValid.sat_of_validSideOnly φ hwf
    (fun m => validSide_of_rulePreserves φ hwf m (h m)) kv hkv hv

/-- **The verdict of `ImprovesCima`, from that alone.** Every live pinned union of the machine holds a
chain — and nothing else. -/
theorem sat_of_pinnedUnionInhabited (hwf : WF φ)
    (h : ∀ m : Nat, PinnedUnionInhabited φ (branchLine φ [] m))
    (kv : NodeId × GPathM) (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (AggressiveReview.filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_rulePreserves φ hwf (fun m => rulePreserves_of_inhabited φ hwf m (h m)) kv hkv hv

/-- **The chains the descent may use**: sound in the source state, sound in one of its sides, and
compatible with the pins. Nothing here mentions a narrowing — the sweep carries them. -/
def CimaChain (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId) (Q : List NodeId)
    (sel : Int → PathNodeId) : Prop :=
  ChainSound G sel ∧
  (∃ Sd ∈ sides, Sd.current_step = G.current_step ∧ ChainSound Sd sel) ∧
  ∀ r ∈ (reqOfCnf φ d ++ Q).filter (fun q => decide (q.step < k + 1)),
    0 ≤ r.step → r.step < G.current_step → (sel r.step).id = r


/-- **A chain of the family is a chain the descent can use.** Of the three things `CimaChain` asks —
sound in the source, sound in one side, compatible with the pins — the first two come free from a chain
of the family: the family is a narrowing of the source, and its chains are its side's
(`chainSound_side_of_famFix`). Only the pins remain. -/
theorem cimaChain_of_famChain (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (hsok : ConservationFilter.StateOkF φ m kv) (hmkv : MInv φ kv.2)
    (hson : p ∈ mapSons φ kv.1.step kv.1.index) (hvS : isValid (sent φ kv.2 p) = true)
    (G : GPathM) (hrc : Reader.RCtx G) (hsmpG : Sons.SMP G)
    (hcsG : G.current_step = (m : Int) + 2) (k : Int) (d : NodeId) (Q : List NodeId)
    (hv : isValid (famFix (sidesOf φ (L) p) (topOf p kv.1) G) = true)
    (sel : Int → PathNodeId)
    (hsc : ChainSound (famFix (sidesOf φ (L) p) (topOf p kv.1) G) sel)
    (hpins : ∀ r ∈ (reqOfCnf φ d ++ Q).filter (fun q => decide (q.step < k + 1)),
      0 ≤ r.step → r.step < G.current_step → (sel r.step).id = r) :
    CimaChain φ (sidesOf φ (L) p) k G d Q sel := by
  have hsS := ConservationFilter.StateOkF_sent φ (ConservationFilter.Fsac φ 0) reviewAgg
    (ConservationFilter.prunes_Fsac φ 0) m kv hsok p hson hvS
  have hsS' : (sent φ kv.2 p).current_step = (m : Int) + 1 + 1 := hsS.step
  have hcsS : (sent φ kv.2 p).current_step = G.current_step := by rw [hsS', hcsG]; omega
  refine ⟨SubsetSemantics.ChainSound_of_pruned (keeps_famFix _ _ G).1 hrc.nodup hsmpG sel hsc,
    ⟨sent φ kv.2 p, ?_, hcsS,
      chainSound_side_of_famFix φ hwf L m hLI p hps kv hkv hsok hmkv hson hvS G hrc hcsG hv sel hsc⟩,
    hpins⟩
  refine List.mem_filterMap.mpr ⟨kv, hkv, ?_⟩
  rw [if_pos (by
    simp only [Bool.and_eq_true]
    exact ⟨List.contains_iff_mem.mpr hson, hvS⟩)]

/-- **The descent's obligation, in its tight form.** Every pair of the support lies on such a chain.
The quantifier over narrowings is gone: the chain is asked of the source state only, because
`AOk_filterAllCimaC` carries both the support and the chains through the pins and the whole review. -/
def SideChainG (sides : List GPathM) (k : Int) (G : GPathM) (d : NodeId) (Q : List NodeId) : Prop :=
  ∀ x v, (Rel (AggressiveReview.filterAllAgg (sent φ G d) Q) x v ∧
      x.id.step < k + 1 ∧ v.id.step < k + 1) →
    ∃ (sel : Int → PathNodeId) (i j : Int), CimaChain φ sides k G d Q sel ∧
      0 ≤ i ∧ i < G.current_step ∧ 0 ≤ j ∧ j < G.current_step ∧ x = sel i ∧ v = sel j

/-- **The descent, from chains of the source state alone.** -/
theorem pinned_source_valid_of_sideChainG (sides : List GPathM) (hwf : WF φ) (k : Int)
    (key : NodeId) (G : GPathM) (hsG : ConservationFilter.StateOkF φ k (key, G)) (hmG : MInv φ G)
    (d : NodeId) (hd : d ∈ mapSons φ key.step key.index) (hval : isValid (sent φ G d) = true)
    (Q : List NodeId) (hvY : isValid (AggressiveReview.filterAllAgg (sent φ G d) Q) = true)
    (hcs : 0 < G.current_step) (h : SideChainG φ sides k G d Q) :
    isValid (filterAllCima sides G
      ((reqOfCnf φ d ++ Q).filter (fun q => decide (q.step < k + 1)))) = true := by
  obtain ⟨hA, hpin, z, hz⟩ :=
    HereditaryValid.pinned_source_support φ hwf k key G hsG hmG d hd hval Q hvY
  refine SupportSplit.valid_of_sup _ _ _
    (AOk_filterAllCimaC sides G (CimaChain φ sides k G d Q) hA (fun sel hsel => hsel.1) _ hpin
      (fun r hr sel hsel h0 h1 => hsel.2.2 r hr h0 h1) (fun sel hsel => ?_) (fun g' hk hchg' _ x v hr => ?_)).sup z hz
  · obtain ⟨Sd, hS, hcsS, hscS⟩ := hsel.2.1
    exact carried_of_side sides G Sd hS sel hscS hcsS hcs
  · obtain ⟨sel, i, j, hsel, hi0, hi1, hj0, hj1, hxe, hve⟩ := h x v hr
    obtain ⟨Sd, hS, hcsS, hscS⟩ := hsel.2.1
    have hcs' : g'.current_step = G.current_step := hk.1.step_eq
    rw [hxe, hve]
    exact cimaOk_of_chain sides g' Sd hS (by rw [hcs']; exact hcsS) sel (hchg' sel hsel) hscS
      (by rw [hcs']; exact hcs) i j hi0 (by omega) hj0 (by omega)

/-- **Every node of a family is a node of the side.** A node of the family has, by its own support, a
partner at every step; the pair is an entry of the side, so the node is one of the side's. -/
theorem mem_side_of_famFix (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (g : GPathM) (hrc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g)
    (hcsg : g.current_step = (m : Int) + 2)
    (hv : isValid (famFix (sidesOf φ (L) p) (topOf p kv.1) g) = true)
    (z : PathNodeId)
    (hz : EmbeddedSupport.Mem (famFix (sidesOf φ (L) p) (topOf p kv.1) g) z) :
    EmbeddedSupport.Mem (sent φ kv.2 p) z := by
  have hcsF : (famFix (sidesOf φ (L) p) (topOf p kv.1) g).current_step =
      g.current_step := (keeps_famFix _ _ g).1.step_eq
  have hm0 : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
  have hsup := sup_famFix _ (topOf p kv.1) g hrc hsmp hpms hsn hv
  have hadj := (adj_famFix _ (topOf p kv.1) g hrc hsmp hpms hsn hv).1
  obtain ⟨v, hrel, _⟩ := hsup.cov z hz 0 (Int.le_refl 0) (by rw [hcsF, hcsg]; omega)
  have hbz := EmbeddedSupport.mem_bounds _ hadj hz
  have hbv := EmbeddedSupport.mem_bounds _ hadj (hsup.dom z v hrel).2
  rw [hcsF] at hbz hbv
  obtain ⟨n, hn, _, _⟩ := (side_of_famFix φ hwf L m hLI p hps kv hkv g
    (ReaderAgg.RCtx_of_keeps (keeps_restAll _ _ _) hrc).nodup hv z v hrel hbz.1 hbz.2 hbv.1
    hbv.2).1
  exact ⟨n, hn⟩

-- ============================================================
-- What a chain still asks for, in a state of the machine's kind
-- ============================================================

/-- **Everything a sound chain asks for, except that its nodes own each other.** In a state of the
machine's own kind — a review fixpoint with the reader's context — a linked selection is a sound chain
as soon as it is pairwise owned: the global owners, the self-ownership, the son link and the root all
come out of the state's own invariants. -/
theorem chainSound_of_pairwise (F : GPathM) (hadj : AdjacentOwners.Adj F)
    (hok : AggFixpoint.AggOk F) (hsmp : Sons.SMP F) (hcs : 0 < F.current_step)
    (sel : Int → PathNodeId)
    (hic : IsChain F sel) (hpw : PairwiseOwned F sel) : ChainSound F sel := by
  have hsup := LinkedChain.sup_self F hadj hok hsmp
  have hnode : ∀ k, 0 ≤ k → k < F.current_step → ∃ n, F.node? (sel k) = some n := by
    intro k h0 h1; exact Option.isSome_iff_exists.mp (hic.1 k h0 h1).1
  have hmem : ∀ k, 0 ≤ k → k < F.current_step → EmbeddedSupport.Mem F (sel k) := by
    intro k h0 h1; obtain ⟨n, hn⟩ := hnode k h0 h1; exact ⟨n, hn⟩
  have hself : ∀ k, 0 ≤ k → k < F.current_step → sel k ∈ ownersOf F (sel k) := by
    intro k h0 h1
    obtain ⟨v, hv, hvs⟩ := hsup.cov (sel k) (hmem k h0 h1) k h0 h1
    obtain ⟨n, hn, hmemv, _⟩ := hv
    have hid : n.id = sel k := node?_id_eq F (sel k) n hn
    have := hadj.rc.oos n (List.mem_of_find?_eq_some hn) v hmemv
      (by rw [hid, (hic.1 k h0 h1).2]; exact hvs)
    rw [hid] at this
    unfold ownersOf; rw [hn, ← this]; exact hmemv
  refine ⟨⟨hic, hpw, fun k h0 h1 => hsup.gow (sel k) (hmem k h0 h1)⟩, hself, ?_, ?_, ?_⟩
  · intro k h0 h1
    obtain ⟨n, hn⟩ := hnode (k + 1) (by omega) h1
    obtain ⟨n', hn'⟩ := hnode k h0 (by omega)
    have hpar : sel k ∈ n.parents := by
      have := hic.2 k h0 h1; rw [hn] at this; simpa using this
    have := hsmp n (List.mem_of_find?_eq_some hn) (sel k) hpar n'
      (List.mem_of_find?_eq_some hn') (node?_id_eq F (sel k) n' hn')
    unfold sonsOf; rw [hn']
    rw [node?_id_eq F (sel (k + 1)) n hn] at this
    exact this
  · obtain ⟨n, hn⟩ := hnode 0 (Int.le_refl 0) hcs
    have hz : n.id.id.step = 0 := by
      rw [node?_id_eq F (sel 0) n hn, (hic.1 0 (Int.le_refl 0) hcs).2]
    have hr := hadj.rc.rootz n (List.mem_of_find?_eq_some hn) hz
    rw [node?_id_eq F (sel 0) n hn] at hr
    exact hr
  · intro k h0 h1
    obtain ⟨n, hn⟩ := hnode k (by omega) h1
    have := hadj.rc.shape.notroot n (List.mem_of_find?_eq_some hn)
      (by rw [node?_id_eq F (sel k) n hn, (hic.1 k (by omega) h1).2]; exact h0)
    rw [node?_id_eq F (sel k) n hn] at this
    exact this

/-- **Pairwise ownership already carries the links.** In a review fixpoint, two members of the support
that own each other on neighbouring steps are a parent link (`Sup.link`). So a selection that picks one
node per step and is pairwise owned is a linked chain for free — `IsChain` asks for nothing more. -/
theorem isChain_of_pairwise (F : GPathM) (hadj : AdjacentOwners.Adj F)
    (hok : AggFixpoint.AggOk F) (hsmp : Sons.SMP F) (sel : Int → PathNodeId)
    (hnode : ∀ k, 0 ≤ k → k < F.current_step → (F.node? (sel k)).isSome = true ∧ (sel k).id.step = k)
    (hpw : PairwiseOwned F sel) : IsChain F sel := by
  have hsup := LinkedChain.sup_self F hadj hok hsmp
  have hrel : ∀ i j, 0 ≤ i → 0 ≤ j → i < F.current_step → j < F.current_step → i ≠ j →
      Rel F (sel j) (sel i) := by
    intro i j hi0 hj0 hi hj hne
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hnode j hj0 hj).1
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp (hnode i hi0 hi).1
    have hmem := hpw i j hi0 hj0 hi hj hne
    have : sel i ∈ ownersOf F (sel j) := (List.mem_filter.mp hmem).1
    unfold ownersOf at this; rw [hn] at this
    exact ⟨n, hn, this, n', hn'⟩
  refine ⟨hnode, fun k h0 h1 => ?_⟩
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hnode (k + 1) (by omega) h1).1
  have hlink := hsup.link (sel (k + 1)) (sel k)
    d (hrel k (k + 1) h0 (by omega) (by omega) h1 (by omega))
    (hrel (k + 1) k (by omega) h0 h1 (by omega) (by omega))
    (by rw [(hnode k h0 (by omega)).2, (hnode (k + 1) (by omega) h1).2]) hd
  rw [hd]; simpa using hlink

-- ============================================================
-- The triangle filter, inside the family
-- ============================================================

/-- **The nodes of a step that every chosen node owns, and that own every chosen node.** This is the
author's `filter_triangle_nodes!` read as a set: the owners common to everything picked so far. His rule
marks the state invalid when this runs empty; here it is what the pick reads from. -/
def commonWith (F : GPathM) (L : List PathNodeId) (l : Int) : List PathNodeId :=
  ((F.line l).map (·.id)).filter (fun z =>
    L.all (fun y => (ownersOf F z).contains y && (ownersOf F y).contains z))

theorem mem_commonWith (F : GPathM) (hnd : NodupIds F) (L : List PathNodeId) (l : Int)
    (z : PathNodeId) (h : z ∈ commonWith F L l) :
    z.id.step = l ∧ (F.node? z).isSome = true ∧
      ∀ y ∈ L, (ownersOf F z).contains y = true ∧ (ownersOf F y).contains z = true := by
  obtain ⟨hline, hall⟩ := List.mem_filter.mp h
  obtain ⟨n, hn, hid⟩ := List.mem_map.mp hline
  refine ⟨by rw [← hid]; exact eq_of_beq (List.mem_filter.mp hn).2, ?_, fun y hy => ?_⟩
  · rw [← hid, node?_of_mem hnd n (List.mem_filter.mp hn).1]; rfl
  · have := List.all_eq_true.mp hall y hy
    simp only [Bool.and_eq_true] at this
    exact this

/-- Building a member of `commonWith` from the relations. -/
theorem mem_commonWith_mk (F : GPathM) (L : List PathNodeId) (l : Int) (z : PathNodeId)
    (n : PNodeM) (hn : F.node? z = some n) (hl : z.id.step = l)
    (h : ∀ y ∈ L, Rel F z y ∧ Rel F y z) : z ∈ commonWith F L l := by
  refine List.mem_filter.mpr ⟨mem_line_of_node? F z n hn l hl, List.all_eq_true.mpr (fun y hy => ?_)⟩
  obtain ⟨h1, h2⟩ := h y hy
  obtain ⟨m, hm, hmem, _⟩ := h1
  obtain ⟨m', hm', hmem', _⟩ := h2
  simp only [Bool.and_eq_true]
  constructor
  · unfold ownersOf; rw [hm]; exact List.contains_iff_mem.mpr hmem
  · unfold ownersOf; rw [hm']; exact List.contains_iff_mem.mpr hmem'

/-- **The picks, from the top down.** At each round, the first node the triangle filter still allows:
one that every node already picked owns, and that owns them all. -/
def triPicks (F : GPathM) : Nat → List PathNodeId
  | 0 => []
  | n + 1 =>
    match commonWith F (triPicks F n) (F.current_step - 1 - (n : Int)) with
    | [] => triPicks F n
    | z :: _ => z :: triPicks F n

/-- **The author's filter never fires**: at every step there is still a node common to everything
picked so far. This is `filter_triangle_nodes!` read as a hypothesis instead of as a test. -/
def TriOk (F : GPathM) : Prop :=
  ∀ n : Nat, (n : Int) < F.current_step →
    commonWith F (triPicks F n) (F.current_step - 1 - (n : Int)) ≠ []

def dummyId : PathNodeId := { id := { step := 0, index := 0 }, parent_id := none }

def triSel (F : GPathM) (k : Int) : PathNodeId :=
  match triPicks F (F.current_step - k).toNat with
  | [] => dummyId
  | z :: _ => z

theorem triPicks_mono (F : GPathM) :
    ∀ (n m : Nat), n ≤ m → ∀ y ∈ triPicks F n, y ∈ triPicks F m := by
  intro n m
  induction m with
  | zero => intro h y hy; rw [Nat.le_zero.mp h] at hy; exact hy
  | succ k ih =>
    intro h y hy
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hk := ih (by omega) y hy
      show y ∈ triPicks F (k + 1)
      unfold triPicks
      split
      · exact hk
      · exact List.mem_cons_of_mem _ hk
    · rw [show n = k + 1 from by omega] at hy; exact hy

/-- **What the picks are**, as long as the triangle filter never fires: one node per step, from the top
down, each of them a node of the state, and all of them owning each other. -/
theorem triPicks_inv (F : GPathM) (hnd : NodupIds F) (hT : TriOk F) :
    ∀ n : Nat, (n : Int) ≤ F.current_step →
      (0 < n → ∃ z L, triPicks F n = z :: L ∧ z.id.step = F.current_step - (n : Int)) ∧
      (∀ y ∈ triPicks F n, (F.node? y).isSome = true) ∧
      (∀ x ∈ triPicks F n, ∀ y ∈ triPicks F n, x ≠ y →
        (ownersOf F x).contains y = true ∧ (ownersOf F y).contains x = true) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨fun h => absurd h (by omega), fun y hy => absurd hy List.not_mem_nil,
      fun x hx => absurd hx List.not_mem_nil⟩
  | succ k ih =>
    intro hk
    obtain ⟨_, hnodes, hmut⟩ := ih (by push_cast at hk ⊢; omega)
    have hne := hT k (by push_cast at hk; omega)
    cases hc : commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) with
    | nil => exact absurd hc hne
    | cons z rest =>
      have hzmem : z ∈ commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) := by
        rw [hc]; exact List.mem_cons_self
      obtain ⟨hzs, hzn, hzall⟩ := mem_commonWith F hnd _ _ z hzmem
      have hstep : triPicks F (k + 1) = z :: triPicks F k := by
        show (match commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) with
          | [] => triPicks F k | z :: _ => z :: triPicks F k) = _
        rw [hc]
      rw [hstep]
      refine ⟨fun _ => ⟨z, triPicks F k, rfl, by rw [hzs]; push_cast; omega⟩, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hzn
        · exact hnodes y hy'
      · intro x hx y hy hxy
        rcases List.mem_cons.mp hx with rfl | hx'
        · rcases List.mem_cons.mp hy with rfl | hy'
          · exact absurd rfl hxy
          · exact hzall y hy'
        · rcases List.mem_cons.mp hy with rfl | hy'
          · exact ⟨(hzall x hx').2, (hzall x hx').1⟩
          · exact hmut x hx' y hy' hxy

/-- The picks are at most as many as the rounds, they are nodes, and they own each other — all of it
without assuming the filter never fires. -/
theorem triPicks_facts (F : GPathM) (hnd : NodupIds F) :
    ∀ n : Nat, (triPicks F n).length ≤ n ∧
      (∀ y ∈ triPicks F n, (F.node? y).isSome = true) ∧
      (∀ x ∈ triPicks F n, ∀ y ∈ triPicks F n, x ≠ y →
        (ownersOf F x).contains y = true ∧ (ownersOf F y).contains x = true) := by
  intro n
  induction n with
  | zero => exact ⟨Nat.le_refl 0, fun y hy => absurd hy List.not_mem_nil,
      fun x hx => absurd hx List.not_mem_nil⟩
  | succ k ih =>
    obtain ⟨hlen, hnodes, hmut⟩ := ih
    cases hc : commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) with
    | nil =>
      have hstep : triPicks F (k + 1) = triPicks F k := by
        show (match commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) with
          | [] => triPicks F k | z :: _ => z :: triPicks F k) = _
        rw [hc]
      rw [hstep]
      exact ⟨Nat.le_succ_of_le hlen, hnodes, hmut⟩
    | cons z rest =>
      have hzmem : z ∈ commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) := by
        rw [hc]; exact List.mem_cons_self
      obtain ⟨_, hzn, hzall⟩ := mem_commonWith F hnd _ _ z hzmem
      have hstep : triPicks F (k + 1) = z :: triPicks F k := by
        show (match commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) with
          | [] => triPicks F k | z :: _ => z :: triPicks F k) = _
        rw [hc]
      rw [hstep]
      refine ⟨by simpa using Nat.succ_le_succ hlen, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hzn
        · exact hnodes y hy'
      · intro x hx y hy hxy
        rcases List.mem_cons.mp hx with rfl | hx'
        · rcases List.mem_cons.mp hy with rfl | hy'
          · exact absurd rfl hxy
          · exact hzall y hy'
        · rcases List.mem_cons.mp hy with rfl | hy'
          · exact ⟨(hzall x hx').2, (hzall x hx').1⟩
          · exact hmut x hx' y hy' hxy

/-- **What the first three picks hand over, as a witness.** Same three cases as below, but keeping the
node it builds: a node of the state, at the step asked for, related both ways to everything picked. -/
theorem common_exists (F : GPathM) (hadj : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F)
    (hsmp : Sons.SMP F) (hv : isValid F = true) (L : List PathNodeId) (hlen : L.length ≤ 2)
    (hnodes : ∀ y ∈ L, (F.node? y).isSome = true)
    (hmut : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      (ownersOf F x).contains y = true ∧ (ownersOf F y).contains x = true)
    (l : Int) (h0 : 0 ≤ l) (h1 : l < F.current_step) :
    ∃ z n, F.node? z = some n ∧ z.id.step = l ∧ ∀ y ∈ L, Rel F z y ∧ Rel F y z := by
  have hsup := LinkedChain.sup_self F hadj hok hsmp
  have hmemOf : ∀ a b, Rel F a b → EmbeddedSupport.Mem F a := fun a b h => (hsup.dom a b h).1
  rcases L with _ | ⟨a, L1⟩
  ·
    have hv' := hv
    simp only [isValid, List.all_eq_true] at hv'
    obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (hv' l (mem_intRange h0 (by omega)))
    obtain ⟨n, hn, hnid⟩ := hadj.rc.gn q hq
    have hnq : F.node? q = some n := by rw [← hnid]; exact node?_of_mem hadj.rc.nodup n hn
    exact ⟨q, n, hnq, eq_of_beq hqs, fun y hy => absurd hy List.not_mem_nil⟩
  rcases L1 with _ | ⟨b, L2⟩
  ·
    obtain ⟨na, hna⟩ := Option.isSome_iff_exists.mp (hnodes a List.mem_cons_self)
    obtain ⟨v, hrel, hvs⟩ := hsup.cov a ⟨na, hna⟩ l h0 h1
    obtain ⟨nv, hnv⟩ := hmemOf v a (hsup.sym a v hrel)
    exact ⟨v, nv, hnv, hvs, fun y hy => by
      rw [List.mem_singleton.mp hy]; exact ⟨hsup.sym a v hrel, hrel⟩⟩
  rcases L2 with _ | ⟨c, L3⟩
  ·
    by_cases hab : a = b
    · obtain ⟨na, hna⟩ := Option.isSome_iff_exists.mp (hnodes a List.mem_cons_self)
      obtain ⟨v, hrel, hvs⟩ := hsup.cov a ⟨na, hna⟩ l h0 h1
      obtain ⟨nv, hnv⟩ := hmemOf v a (hsup.sym a v hrel)
      exact ⟨v, nv, hnv, hvs, fun y hy => by
        rcases List.mem_cons.mp hy with he | hy'
        · rw [he]; exact ⟨hsup.sym a v hrel, hrel⟩
        · rw [List.mem_singleton.mp hy', ← hab]; exact ⟨hsup.sym a v hrel, hrel⟩⟩
    · obtain ⟨hc1, hc2⟩ := hmut a List.mem_cons_self b (List.mem_cons_of_mem _ List.mem_cons_self) hab
      obtain ⟨hrab, _⟩ := rel_of_owners F a b hc1 hc2
      obtain ⟨z, hza, hzb, hzs⟩ := hsup.agg a b hrab l h0 h1
      obtain ⟨nz, hnz⟩ := hmemOf z a (hsup.sym a z hza)
      exact ⟨z, nz, hnz, hzs, fun y hy => by
        rcases List.mem_cons.mp hy with he | hy'
        · rw [he]; exact ⟨hsup.sym a z hza, hza⟩
        · rw [List.mem_singleton.mp hy']; exact ⟨hsup.sym b z hzb, hzb⟩⟩
  · exact absurd hlen (by simp)

/-- **The filter cannot fire on the first three picks.** With none picked, any node of the step will do
and the state is live; with one, its own cover gives a partner at every step; with two, they own each
other, so the aggressive review gives them a common owner at every step. The first time the filter can
fire is when there are three nodes to agree with. -/
theorem commonWith_small (F : GPathM) (hadj : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F)
    (hsmp : Sons.SMP F) (hv : isValid F = true) (L : List PathNodeId) (hlen : L.length ≤ 2)
    (hnodes : ∀ y ∈ L, (F.node? y).isSome = true)
    (hmut : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      (ownersOf F x).contains y = true ∧ (ownersOf F y).contains x = true)
    (l : Int) (h0 : 0 ≤ l) (h1 : l < F.current_step) : commonWith F L l ≠ [] := by
  obtain ⟨z, n, hn, hzs, hrel⟩ := common_exists F hadj hok hsmp hv L hlen hnodes hmut l h0 h1
  have hmem := mem_commonWith_mk F L l z n hn hzs hrel
  intro he; rw [he] at hmem; exact absurd hmem List.not_mem_nil

/-- **The filter is proved for the first three rounds.** -/
theorem triOk_low (F : GPathM) (hadj : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F)
    (hsmp : Sons.SMP F) (hv : isValid F = true) :
    ∀ n : Nat, n ≤ 2 → (n : Int) < F.current_step →
      commonWith F (triPicks F n) (F.current_step - 1 - (n : Int)) ≠ [] := by
  intro n hn2 hn
  obtain ⟨hlen, hnodes, hmut⟩ := triPicks_facts F hadj.rc.nodup n
  exact commonWith_small F hadj hok hsmp hv _ (Nat.le_trans hlen hn2) hnodes hmut _
    (by omega) (by omega)

/-- **So the filter only has content from the fourth pick on**: three nodes already chosen, and a fourth
step to agree on. -/
def TriOkHigh (F : GPathM) : Prop :=
  ∀ n : Nat, 3 ≤ n → (n : Int) < F.current_step →
    commonWith F (triPicks F n) (F.current_step - 1 - (n : Int)) ≠ []

theorem triOk_of_high (F : GPathM) (hadj : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F)
    (hsmp : Sons.SMP F) (hv : isValid F = true) (h : TriOkHigh F) : TriOk F := by
  intro n hn
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · exact triOk_low F hadj hok hsmp hv n (by omega) hn
  · exact h n hge hn

/-- **A family hangs on its top.** Two facts about the cone: every member is related both ways to the
centre `c`, and the centre is the only member at the last step. -/
def ConeAt (F : GPathM) (c : PathNodeId) : Prop :=
  (∀ z, EmbeddedSupport.Mem F z → Rel F z c ∧ Rel F c z) ∧
  (∀ z, EmbeddedSupport.Mem F z → z.id.step = F.current_step - 1 → z = c)

/-- **The centre of a cone is free.** Anything the state hands over is a member, so it is already
related to `c`: a list made of at most two nodes plus the centre never empties the intersection. -/
theorem commonWith_cone (F : GPathM) (hadj : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F)
    (hsmp : Sons.SMP F) (hv : isValid F = true) (c : PathNodeId)
    (hcone : ∀ z, EmbeddedSupport.Mem F z → Rel F z c ∧ Rel F c z)
    (L L' : List PathNodeId) (hsub : ∀ y ∈ L, y ∈ L' ∨ y = c) (hlen : L'.length ≤ 2)
    (hnodes : ∀ y ∈ L', (F.node? y).isSome = true)
    (hmut : ∀ x ∈ L', ∀ y ∈ L', x ≠ y →
      (ownersOf F x).contains y = true ∧ (ownersOf F y).contains x = true)
    (l : Int) (h0 : 0 ≤ l) (h1 : l < F.current_step) : commonWith F L l ≠ [] := by
  obtain ⟨z, n, hn, hzs, hrel⟩ := common_exists F hadj hok hsmp hv L' hlen hnodes hmut l h0 h1
  have hmem := mem_commonWith_mk F L l z n hn hzs (fun y hy => by
    rcases hsub y hy with hy' | hyc
    · exact hrel y hy'
    · rw [hyc]; exact hcone z ⟨n, hn⟩)
  intro he; rw [he] at hmem; exact absurd hmem List.not_mem_nil

/-- **The cone's centre asks for nothing.** Every node of the state is already related to the centre
both ways, so adding it to the picked list does not remove a single candidate. The author's filter
therefore never reads the top: at round `n` it is really intersecting over `n - 1` nodes, which is why
the first round it can fire is the fifth and not the fourth. -/
theorem commonWith_drop_cone (F : GPathM) (hnd : NodupIds F) (c : PathNodeId)
    (hcone : ∀ z, EmbeddedSupport.Mem F z → Rel F z c ∧ Rel F c z)
    (L : List PathNodeId) (l : Int) : commonWith F (L ++ [c]) l = commonWith F L l := by
  unfold commonWith
  refine List.filter_congr (fun z hz => ?_)
  obtain ⟨n, hn, hid⟩ := List.mem_map.mp hz
  have hnz : F.node? z = some n := by rw [← hid]; exact node?_of_mem hnd n (List.mem_filter.mp hn).1
  obtain ⟨h1, h2⟩ := hcone z ⟨n, hnz⟩
  have hc : ((ownersOf F z).contains c && (ownersOf F c).contains z) = true := by
    obtain ⟨m, hm, hmem, _⟩ := h1
    obtain ⟨m', hm', hmem', _⟩ := h2
    simp only [Bool.and_eq_true]
    exact ⟨by unfold ownersOf; rw [hm]; exact List.contains_iff_mem.mpr hmem,
      by unfold ownersOf; rw [hm']; exact List.contains_iff_mem.mpr hmem'⟩
  simp only [List.all_append, List.all_cons, List.all_nil, hc, Bool.and_true]

/-- **The centre is always picked first.** The first round reads the last step, and the cone has exactly
one node there; so from then on every pick list ends in the centre. -/
theorem triPicks_cone (F : GPathM) (hadj : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F)
    (hsmp : Sons.SMP F) (hv : isValid F = true) (hcs : 0 < F.current_step)
    (c : PathNodeId) (hcone : ConeAt F c) :
    ∀ n : Nat, 1 ≤ n → ∃ L', triPicks F n = L' ++ [c] ∧ L'.length + 1 ≤ n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hne := triOk_low F hadj hok hsmp hv 0 (by omega) (by push_cast; omega)
      cases hc : commonWith F (triPicks F 0) (F.current_step - 1 - ((0 : Nat) : Int)) with
      | nil => exact absurd hc hne
      | cons z rest =>
        have hstep : triPicks F 1 = z :: triPicks F 0 := by
          show (match commonWith F (triPicks F 0) (F.current_step - 1 - ((0 : Nat) : Int)) with
            | [] => triPicks F 0 | z :: _ => z :: triPicks F 0) = _
          rw [hc]
        have hzmem : z ∈ commonWith F (triPicks F 0) (F.current_step - 1 - ((0 : Nat) : Int)) := by
          rw [hc]; exact List.mem_cons_self
        obtain ⟨hzs, hzn, _⟩ := mem_commonWith F hadj.rc.nodup _ _ z hzmem
        have hzc : z = c :=
          hcone.2 z (Option.isSome_iff_exists.mp hzn) (by rw [hzs]; push_cast; omega)
        exact ⟨[], by rw [hstep, hzc]; rfl, by omega⟩
    · obtain ⟨L', hL', hlen⟩ := ih hk
      cases hc : commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) with
      | nil =>
        have hstep : triPicks F (k + 1) = triPicks F k := by
          show (match commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) with
            | [] => triPicks F k | z :: _ => z :: triPicks F k) = _
          rw [hc]
        exact ⟨L', by rw [hstep, hL'], by omega⟩
      | cons z rest =>
        have hstep : triPicks F (k + 1) = z :: triPicks F k := by
          show (match commonWith F (triPicks F k) (F.current_step - 1 - (k : Int)) with
            | [] => triPicks F k | z :: _ => z :: triPicks F k) = _
          rw [hc]
        exact ⟨z :: L', by rw [hstep, hL']; rfl, by simp only [List.length_cons]; omega⟩

/-- **What the filter really reads at round `n`.** The pick list is `n` long, but its last element is
the cone's centre and asks for nothing, so the intersection is over the other `n - 1`. -/
theorem triPicks_cone_drop (F : GPathM) (hadj : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F)
    (hsmp : Sons.SMP F) (hv : isValid F = true) (hcs : 0 < F.current_step)
    (c : PathNodeId) (hcone : ConeAt F c) (n : Nat) (hn : 1 ≤ n) :
    ∃ L', triPicks F n = L' ++ [c] ∧ L'.length + 1 ≤ n ∧
      ∀ l, commonWith F (triPicks F n) l = commonWith F L' l := by
  obtain ⟨L', hL', hlen⟩ := triPicks_cone F hadj hok hsmp hv hcs c hcone n hn
  exact ⟨L', hL', hlen, fun l => by
    rw [hL']; exact commonWith_drop_cone F hadj.rc.nodup c hcone.1 L' l⟩

/-- **In a cone the filter only has content from the fifth pick on.** Three of the four already picked
must agree, and one of them is always the centre, which agrees with everything. -/
def TriOkCone (F : GPathM) : Prop :=
  ∀ n : Nat, 4 ≤ n → (n : Int) < F.current_step →
    commonWith F (triPicks F n) (F.current_step - 1 - (n : Int)) ≠ []

theorem triOk_of_cone (F : GPathM) (hadj : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F)
    (hsmp : Sons.SMP F) (hv : isValid F = true) (c : PathNodeId) (hcone : ConeAt F c)
    (h : TriOkCone F) : TriOk F := by
  intro n hn
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact triOk_low F hadj hok hsmp hv 0 (by omega) hn
    · have hcs : 0 < F.current_step := by
        have h1 : (0 : Int) < (n : Int) := by exact_mod_cast hpos
        omega
      obtain ⟨L', hL', hlen⟩ := triPicks_cone F hadj hok hsmp hv hcs c hcone n hpos
      obtain ⟨_, hnodes, hmut⟩ := triPicks_facts F hadj.rc.nodup n
      refine commonWith_cone F hadj hok hsmp hv c hcone.1 (triPicks F n) L' ?_ (by omega) ?_ ?_ _
        (by omega) (by omega)
      · intro y hy
        rw [hL'] at hy
        rcases List.mem_append.mp hy with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (List.mem_singleton.mp h2)
      · intro y hy; exact hnodes y (by rw [hL']; exact List.mem_append_left _ hy)
      · intro x hx y hy hxy
        exact hmut x (by rw [hL']; exact List.mem_append_left _ hx)
          y (by rw [hL']; exact List.mem_append_left _ hy) hxy
  · exact h n hge hn

/-- **One node at the last step makes the cone.** Every member has, by its own support, a partner at
the last step; if the only member there is `t`, that partner is `t`. So the whole family hangs on `t`
with nothing else assumed about the sides. -/
theorem coneAt_of_topSingle (sides : List GPathM) (t : PathNodeId) (g : GPathM)
    (hrc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g)
    (hcs : 0 < g.current_step) (hv : isValid (famFix sides t g) = true)
    (hsingle : ∀ z, EmbeddedSupport.Mem (famFix sides t g) z →
      z.id.step = (famFix sides t g).current_step - 1 → z = t) :
    ConeAt (famFix sides t g) t := by
  have hcsF : (famFix sides t g).current_step = g.current_step := (keeps_famFix _ _ g).1.step_eq
  have hsup := sup_famFix sides t g hrc hsmp hpms hsn hv
  refine ⟨fun z hz => ?_, hsingle⟩
  obtain ⟨v, hrel, hvs⟩ := hsup.cov z hz ((famFix sides t g).current_step - 1)
    (by rw [hcsF]; omega) (by omega)
  have hvt : v = t := hsingle v (hsup.dom z v hrel).2 hvs
  rw [hvt] at hrel
  exact ⟨hrel, hsup.sym _ _ hrel⟩

/-- **The only node a real family has at the last step is its top**, and so the family is a cone. -/
theorem coneAt_famFix (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (hsok : ConservationFilter.StateOkF φ m kv) (hmkv : MInv φ kv.2)
    (hvS : isValid (sent φ kv.2 p) = true)
    (g : GPathM) (hrc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g)
    (hcsg : g.current_step = (m : Int) + 2)
    (hv : isValid (famFix (sidesOf φ (L) p) (topOf p kv.1) g) = true) :
    ConeAt (famFix (sidesOf φ (L) p) (topOf p kv.1) g) (topOf p kv.1) := by
  have hcsF : (famFix (sidesOf φ (L) p) (topOf p kv.1) g).current_step =
      g.current_step := (keeps_famFix _ _ g).1.step_eq
  refine coneAt_of_topSingle _ _ g hrc hsmp hpms hsn (by omega) hv (fun z hz hzs => ?_)
  obtain ⟨n, hn⟩ := mem_side_of_famFix φ hwf L m hLI p hps kv hkv g hrc hsmp hpms hsn hcsg hv z hz
  have hid : n.id = z := node?_id_eq _ _ n hn
  rw [← hid]
  exact sent_top φ m kv hsok hmkv p hvS n (List.mem_of_find?_eq_some hn)
    (by rw [hid, hzs, hcsF, hcsg]; omega)

/-- **So a real family only asks the author's filter from the fifth pick on.** -/
theorem triOk_of_coneHigh_famFix (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (hsok : ConservationFilter.StateOkF φ m kv) (hmkv : MInv φ kv.2)
    (hvS : isValid (sent φ kv.2 p) = true)
    (g : GPathM) (hrc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g)
    (hcsg : g.current_step = (m : Int) + 2)
    (hv : isValid (famFix (sidesOf φ (L) p) (topOf p kv.1) g) = true)
    (h : TriOkCone (famFix (sidesOf φ (L) p) (topOf p kv.1) g)) :
    TriOk (famFix (sidesOf φ (L) p) (topOf p kv.1) g) := by
  obtain ⟨hadj, hsm⟩ :=
    adj_famFix (sidesOf φ (L) p) (topOf p kv.1) g hrc hsmp hpms hsn hv
  exact triOk_of_cone _ hadj (AggFixpoint.aggOk_reviewAgg _ hv) hsm hv _
    (coneAt_famFix φ hwf L m hLI p hps kv hkv hsok hmkv hvS g hrc hsmp hpms hsn hcsg hv) h

/-- **The pick at a step**, and what it is. -/
theorem triSel_spec (F : GPathM) (hnd : NodupIds F) (hT : TriOk F) (k : Int) (h0 : 0 ≤ k)
    (h1 : k < F.current_step) :
    (F.node? (triSel F k)).isSome = true ∧ (triSel F k).id.step = k ∧
      triSel F k ∈ triPicks F (F.current_step - k).toNat := by
  have hnn : ((F.current_step - k).toNat : Int) = F.current_step - k := Int.toNat_of_nonneg (by omega)
  obtain ⟨hhead, hnodes, _⟩ := triPicks_inv F hnd hT (F.current_step - k).toNat (by omega)
  obtain ⟨z, L, heq, hzs⟩ := hhead (by omega)
  have hsel : triSel F k = z := by
    show (match triPicks F (F.current_step - k).toNat with
      | [] => dummyId | z :: _ => z) = z
    rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsel]; exact hnodes z (by rw [heq]; exact List.mem_cons_self)
  · rw [hsel, hzs, hnn]; omega
  · rw [hsel, heq]; exact List.mem_cons_self

/-- **The picks own each other.** -/
theorem pairwise_triSel (F : GPathM) (hnd : NodupIds F) (hT : TriOk F) :
    PairwiseOwned F (triSel F) := by
  intro i j hi0 hj0 hi hj hne
  have hni : ((F.current_step - i).toNat : Int) = F.current_step - i :=
    Int.toNat_of_nonneg (by omega)
  have hnj : ((F.current_step - j).toNat : Int) = F.current_step - j :=
    Int.toNat_of_nonneg (by omega)
  obtain ⟨_, hsi, hmi⟩ := triSel_spec F hnd hT i hi0 hi
  obtain ⟨_, hsj, hmj⟩ := triSel_spec F hnd hT j hj0 hj
  have hdiff : triSel F j ≠ triSel F i := by
    intro he; rw [he, hsi] at hsj; exact hne hsj
  refine List.mem_filter.mpr ⟨List.contains_iff_mem.mp ?_, beq_iff_eq.mpr hsi⟩
  rcases Int.lt_or_lt_of_ne hne with hlt | hlt
  · obtain ⟨_, _, hmut⟩ := triPicks_inv F hnd hT (F.current_step - i).toNat (by omega)
    have h2 := triPicks_mono F (F.current_step - j).toNat (F.current_step - i).toNat
      (by omega) _ hmj
    exact (hmut _ h2 _ hmi hdiff).1
  · obtain ⟨_, _, hmut⟩ := triPicks_inv F hnd hT (F.current_step - j).toNat (by omega)
    have h1 := triPicks_mono F (F.current_step - i).toNat (F.current_step - j).toNat
      (by omega) _ hmi
    exact (hmut _ hmj _ h1 hdiff).1

-- ============================================================
-- The verdict, straight from the family
-- ============================================================

/-- **A live family carries a sound chain.** The narrowest class this project has ever put the old
obligation on: not any valid state, but the family of a top — a review fixpoint every one of whose
entries belongs to a single side. -/
def FamHasChain (sides : List GPathM) (g : GPathM) : Prop :=
  ∀ t : PathNodeId, Reader.RCtx g → Sons.SMP g → Sons.PMS g → Sons.SN g →
    0 < g.current_step → isValid (famFix sides t g) = true →
    t ∈ ((g.line (g.current_step - 1)).map (·.id)) →
    ∃ sel, ChainSound (famFix sides t g) sel

/-- **And what is left of it, with nothing else attached**: the family has one node per step, and those
nodes own each other. No links and no other condition: the links follow (`isChain_of_pairwise`) and so
does everything else a sound chain asks for (`chainSound_of_pairwise`). -/
def FamPairwise (sides : List GPathM) (g : GPathM) : Prop :=
  ∀ t : PathNodeId, Reader.RCtx g → Sons.SMP g → Sons.PMS g → Sons.SN g →
    0 < g.current_step → isValid (famFix sides t g) = true →
    t ∈ ((g.line (g.current_step - 1)).map (·.id)) →
    ∃ sel, (∀ k, 0 ≤ k → k < (famFix sides t g).current_step →
        ((famFix sides t g).node? (sel k)).isSome = true ∧ (sel k).id.step = k) ∧
      PairwiseOwned (famFix sides t g) sel

theorem famHasChain_of_pairwise (sides : List GPathM) (g : GPathM) (h : FamPairwise sides g) :
    FamHasChain sides g := by
  intro t hrc hsmp hpms hsn hcs hv hts
  obtain ⟨sel, hnode, hpw⟩ := h t hrc hsmp hpms hsn hcs hv hts
  obtain ⟨hadj, hsm⟩ := adj_famFix sides t g hrc hsmp hpms hsn hv
  have hok := AggFixpoint.aggOk_reviewAgg _ hv
  refine ⟨sel, chainSound_of_pairwise _ hadj hok hsm ?_ sel
    (isChain_of_pairwise _ hadj hok hsm sel hnode hpw) hpw⟩
  rw [(keeps_famFix sides t g).1.step_eq]; exact hcs

/-- **The author's triangle filter, as the hypothesis on a family.** While picking one node per step
from the top down, the nodes common to everything picked so far never run out. This is
`filter_triangle_nodes!`: it computes exactly that intersection and marks the state invalid when it
empties. -/
def FamTriOk (sides : List GPathM) (g : GPathM) : Prop :=
  ∀ t : PathNodeId, Reader.RCtx g → Sons.SMP g → Sons.PMS g → Sons.SN g →
    0 < g.current_step → isValid (famFix sides t g) = true →
    t ∈ ((g.line (g.current_step - 1)).map (·.id)) →
    TriOk (famFix sides t g)

/-- **The last step of a family has one node: its top.** This is the structural half of the cone, and
it is what the real sides give (`coneAt_famFix`). -/
def FamTopSingle (sides : List GPathM) (g : GPathM) : Prop :=
  ∀ t : PathNodeId, Reader.RCtx g → Sons.SMP g → Sons.PMS g → Sons.SN g →
    0 < g.current_step → isValid (famFix sides t g) = true →
    t ∈ ((g.line (g.current_step - 1)).map (·.id)) →
      ∀ z, EmbeddedSupport.Mem (famFix sides t g) z →
        z.id.step = (famFix sides t g).current_step - 1 → z = t

/-- **The author's filter on a family, from the fifth pick on.** The first four are now proved: three
of them by pairwise consistency, the fourth because one of the picks is always the top of the cone. -/
def FamTriOkCone (sides : List GPathM) (g : GPathM) : Prop :=
  ∀ t : PathNodeId, Reader.RCtx g → Sons.SMP g → Sons.PMS g → Sons.SN g →
    0 < g.current_step → isValid (famFix sides t g) = true →
    t ∈ ((g.line (g.current_step - 1)).map (·.id)) →
    TriOkCone (famFix sides t g)

/-- **The reduction.** The filter on a family, in full, follows from the filter from the fifth pick on
plus the fact that the family's last step holds only its top. -/
theorem famTriOk_of_cone (sides : List GPathM) (g : GPathM) (hs : FamTopSingle sides g)
    (h : FamTriOkCone sides g) : FamTriOk sides g := by
  intro t hrc hsmp hpms hsn hcs hv hts
  obtain ⟨hadj, hsm⟩ := adj_famFix sides t g hrc hsmp hpms hsn hv
  exact triOk_of_cone _ hadj (AggFixpoint.aggOk_reviewAgg _ hv) hsm hv t
    (coneAt_of_topSingle sides t g hrc hsmp hpms hsn hcs hv
      (hs t hrc hsmp hpms hsn hcs hv hts))
    (h t hrc hsmp hpms hsn hcs hv hts)

/-- **From the filter to the pairwise selection.** The picks are the chain: one node per step, and each
new one is taken from the nodes that own, and are owned by, everything picked before. -/
theorem famPairwise_of_triOk (sides : List GPathM) (g : GPathM) (h : FamTriOk sides g) :
    FamPairwise sides g := by
  intro t hrc hsmp hpms hsn hcs hv hts
  have hnd : NodupIds (famFix sides t g) :=
    (adj_famFix sides t g hrc hsmp hpms hsn hv).1.rc.nodup
  have hTo := h t hrc hsmp hpms hsn hcs hv hts
  refine ⟨triSel (famFix sides t g), fun k h0 h1 => ?_, pairwise_triSel _ hnd hTo⟩
  obtain ⟨hn, hs, _⟩ := triSel_spec _ hnd hTo k h0 h1
  exact ⟨hn, hs⟩

/-- **The verdict of `ImprovesCima`, straight from that.** No induction along the lines and no descent:
the filtered state of the last line has a live entry, the rule gives it a good top, the family of that
top carries a chain, the chain is a chain of the state itself, and a chain of a machine state is a
genuine path (`genuine_of_chain`, no hypotheses) — that is, a model of the formula. -/
theorem sat_of_famHasChain (sides : List GPathM) (hwf : WF φ)
    (m : Nat) (J : GPathM) (hF : FamHasChain sides (filterAllCima sides J []))
    (hmJ : MInv φ J) (hcs : J.current_step = (m : Int) + 2)
    (hle : (m : Int) + 2 = stepCount φ)
    (hvX : isValid (filterAllCima sides J []) = true) : Satisfiable φ := by
  have hkJX : Keeps J (filterAllCima sides J []) := keeps_filterAllCima _ J []
  have hrcX := ReaderAgg.RCtx_of_keeps hkJX hmJ.rctx
  have hcsX : (filterAllCima sides J []).current_step = (m : Int) + 2 := by
    rw [hkJX.1.step_eq, hcs]
  obtain ⟨hadjX, hsupX⟩ := sup_filterAllCima sides J [] hmJ.rctx hmJ.smp hmJ.pms hmJ.sn
    hmJ.rctx.shape.notroot hvX
  obtain ⟨s1, s2, s3⟩ := sons_filterAllCima sides J [] hmJ.smp hmJ.pms hmJ.sn
    hmJ.rctx.shape.notroot
  -- a live entry of the filtered state
  have hm0 : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
  have hv0 := hvX
  simp only [isValid, List.all_eq_true] at hv0
  obtain ⟨q, hq, _⟩ := List.any_eq_true.mp
    (hv0 0 (mem_intRange (Int.le_refl 0) (by rw [hcsX]; omega)))
  obtain ⟨nq, hnq, hnqid⟩ := hrcX.gn q hq
  have hmq : EmbeddedSupport.Mem (filterAllCima sides J []) q :=
    ⟨nq, by rw [← hnqid]; exact node?_of_mem hrcX.nodup nq hnq⟩
  obtain ⟨v, hrel, _⟩ := hsupX.cov q hmq 0 (Int.le_refl 0) (by rw [hcsX]; omega)
  -- the rule gives it a good top, whose family is live
  obtain ⟨nq', hnq', hmemv, hmv⟩ := id hrel
  have hbq := EmbeddedSupport.mem_bounds _ hadjX hmq
  have hbv := EmbeddedSupport.mem_bounds _ hadjX hmv
  obtain ⟨nv, hnv⟩ := hmv
  obtain ⟨t, htm, hgood⟩ := top_of_cimaOk sides _ q v
    (cimaOk_filterAllCima sides J [] hvX q nq' v hnq' (by rw [hnv]; rfl) hbq.1 hbq.2 hbv.1 hbv.2
      hmemv)
  have hvF : isValid (famFix sides t (filterAllCima sides J [])) = true := by
    simp only [goodFor, Bool.and_eq_true] at hgood; exact hgood.1.1
  -- the family's chain is a chain of the state, and a chain of a state is a genuine path
  obtain ⟨sel, hsc⟩ := hF t hrcX s1 s2 s3 (by rw [hcsX]; omega) hvF htm
  have hprJ : Pruned J (famFix sides t (filterAllCima sides J [])) :=
    (Keeps.trans hkJX (keeps_famFix sides t _)).1
  have hscJ := SubsetSemantics.ChainSound_of_pruned hprJ hmJ.rctx.nodup hmJ.smp sel hsc
  obtain ⟨a, hsat, _⟩ := RunNoBorrow.genuine_of_chain φ hwf m J hmJ hcs (by rw [hcs]; omega) sel hscJ
  refine ⟨a, fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  exact hsat i hi (by
    have h1 : clauseStep φ i = 2 * (φ.nVars : Int) + 1 + (i : Int) := rfl
    have h2 : stepCount φ = 2 * (φ.nVars : Int) + (φ.clauses.length : Int) + 2 := rfl
    omega)

/-- **The verdict of `ImprovesCima` under the author's triangle filter alone.** Everything else is
proved: the rule gives a good top, its family is a live state of the machine's own kind, the picks of
the filter are a chain, a chain of the state is a genuine path, and that is a model. -/
theorem sat_of_famTriOk (sides : List GPathM) (hwf : WF φ)
    (m : Nat) (J : GPathM) (hT : FamTriOk sides (filterAllCima sides J []))
    (hmJ : MInv φ J) (hcs : J.current_step = (m : Int) + 2)
    (hle : (m : Int) + 2 = stepCount φ)
    (hvX : isValid (filterAllCima sides J []) = true) : Satisfiable φ :=
  sat_of_famHasChain φ sides hwf m J
    (famHasChain_of_pairwise sides _ (famPairwise_of_triOk sides _ hT)) hmJ hcs hle hvX

/-- **The verdict of `ImprovesCima`, with the cone taken out of the filter.** The author's triangle
filter is only asked from the fifth pick on; the first four are proved, and the last step of a family
holding only its top is what the real sides give. -/
theorem sat_of_famTriOkCone (sides : List GPathM) (hwf : WF φ)
    (m : Nat) (J : GPathM) (hs : FamTopSingle sides (filterAllCima sides J []))
    (hT : FamTriOkCone sides (filterAllCima sides J []))
    (hmJ : MInv φ J) (hcs : J.current_step = (m : Int) + 2)
    (hle : (m : Int) + 2 = stepCount φ)
    (hvX : isValid (filterAllCima sides J []) = true) : Satisfiable φ :=
  sat_of_famTriOk φ sides hwf m J (famTriOk_of_cone sides _ hs hT) hmJ hcs hle hvX

/-- **The structural half, discharged for the real sides.** A live family names a real top
(`top_of_famFix`), and the family of a real top is a cone (`coneAt_famFix`). So `FamTopSingle` is not a
hypothesis of the machine at all. -/
theorem famTopSingle_sides (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (X : GPathM) (hcsX : X.current_step = (m : Int) + 2) :
    FamTopSingle (sidesOf φ (L) p) X := by
  intro t hrc hsmp hpms hsn _ hv htm
  obtain ⟨kv, hkv, he, hvS⟩ := top_of_famFix φ hwf L m hLI p X hrc hsmp hpms hsn hcsX t
    (step_of_mem_line X _ t htm) hv
  subst he
  exact (coneAt_famFix φ hwf L m hLI p hps kv hkv (hLI.1.2 kv hkv) (hLI.2 kv hkv) hvS X hrc hsmp hpms hsn
    hcsX hv).2

/-- **The verdict of `ImprovesCima` on a real union, under the author's filter from the fifth pick on.**
Nothing else is assumed: the sides are the machine's own, the cone is proved, and the first four picks
are proved. -/
theorem sat_of_famTriOkConeSides (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (J : GPathM)
    (hT : FamTriOkCone (sidesOf φ (L) p)
      (filterAllCima (sidesOf φ (L) p) J []))
    (hmJ : MInv φ J) (hcs : J.current_step = (m : Int) + 2)
    (hle : (m : Int) + 2 = stepCount φ)
    (hvX : isValid (filterAllCima (sidesOf φ (L) p) J []) = true) :
    Satisfiable φ := by
  have hcsX : (filterAllCima (sidesOf φ (L) p) J []).current_step = (m : Int) + 2 := by
    rw [(keeps_filterAllCima _ J []).1.step_eq, hcs]
  exact sat_of_famTriOkCone φ _ hwf m J (famTopSingle_sides φ hwf L m hLI p hps _ hcsX) hT hmJ hcs hle hvX

-- ============================================================
-- The author's filter as a computation, and a verdict proved per run
-- ============================================================

/-- **The filter, run.** The greedy descent of `filter_triangle_nodes!`, bounded by the number of
steps: at every round the nodes common to everything picked so far must not be empty. This is a
`Bool`, computed in one pass per step — not a hypothesis. -/
def triOkB (F : GPathM) : Bool :=
  (List.range F.current_step.toNat).all (fun n =>
    !(commonWith F (triPicks F n) (F.current_step - 1 - (n : Int))).isEmpty)

theorem triOk_of_triOkB (F : GPathM) (h : triOkB F = true) : TriOk F := by
  intro n hn
  have h1 := List.all_eq_true.mp h n (List.mem_range.mpr (by omega))
  intro he
  rw [he] at h1
  exact absurd h1 (by simp)

/-- **The filter on a union**: for every top of the last line whose family is live, the descent inside
that family runs to the bottom. Finitely many tops, one pass each. -/
def famTriOkB (sides : List GPathM) (g : GPathM) : Bool :=
  ((g.line (g.current_step - 1)).map (·.id)).all (fun t =>
    !(isValid (famFix sides t g)) || triOkB (famFix sides t g))

theorem famTriOk_of_B (sides : List GPathM) (g : GPathM) (h : famTriOkB sides g = true) :
    FamTriOk sides g := by
  intro t _ _ _ _ _ hv htm
  have h1 := List.all_eq_true.mp h t htm
  rw [hv] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  exact triOk_of_triOkB _ h1

/-- **The verdict of `ImprovesCima`, proved by running the filter.** No hypothesis at all: if the
author's triangle filter passes on the filtered union of the last line, the formula is satisfiable.
What used to be an open statement about the machine is now a test the machine performs. -/
theorem sat_of_filterCheck (sides : List GPathM) (hwf : WF φ) (m : Nat) (J : GPathM)
    (hcheck : famTriOkB sides (filterAllCima sides J []) = true)
    (hmJ : MInv φ J) (hcs : J.current_step = (m : Int) + 2)
    (hle : (m : Int) + 2 = stepCount φ)
    (hvX : isValid (filterAllCima sides J []) = true) : Satisfiable φ :=
  sat_of_famTriOk φ sides hwf m J (famTriOk_of_B sides _ hcheck) hmJ hcs hle hvX

/-- **The same test, with the first four rounds skipped.** They are proved (`triOk_of_cone`), so the
machine need not run them. -/
def triOkConeB (F : GPathM) : Bool :=
  (List.range F.current_step.toNat).all (fun n =>
    decide (n < 4) || !(commonWith F (triPicks F n) (F.current_step - 1 - (n : Int))).isEmpty)

theorem triOkCone_of_B (F : GPathM) (h : triOkConeB F = true) : TriOkCone F := by
  intro n hn4 hn
  have h1 := List.all_eq_true.mp h n (List.mem_range.mpr (by omega))
  rw [decide_eq_false (by omega : ¬ (n < 4))] at h1
  simp only [Bool.false_or] at h1
  intro he
  rw [he] at h1
  exact absurd h1 (by simp)

def famTriOkConeB (sides : List GPathM) (g : GPathM) : Bool :=
  ((g.line (g.current_step - 1)).map (·.id)).all (fun t =>
    !(isValid (famFix sides t g)) || triOkConeB (famFix sides t g))

theorem famTriOkCone_of_B (sides : List GPathM) (g : GPathM) (h : famTriOkConeB sides g = true) :
    FamTriOkCone sides g := by
  intro t _ _ _ _ _ hv htm
  have h1 := List.all_eq_true.mp h t htm
  rw [hv] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  exact triOkCone_of_B _ h1

/-- **The verdict, running the shortened filter on a real union.** The cone pays for the first four
rounds; the machine runs the rest. -/
theorem sat_of_filterCheckCone (hwf : WF φ) (L : PureLine) (m : Nat) (hLI : ReaderAggRun.LineInv φ (m : Int) L) (p : NodeId)
    (hps : p.step = (m : Int) + 1) (J : GPathM)
    (hcheck : famTriOkConeB (sidesOf φ (L) p)
      (filterAllCima (sidesOf φ (L) p) J []) = true)
    (hmJ : MInv φ J) (hcs : J.current_step = (m : Int) + 2)
    (hle : (m : Int) + 2 = stepCount φ)
    (hvX : isValid (filterAllCima (sidesOf φ (L) p) J []) = true) :
    Satisfiable φ := by
  have hcsX : (filterAllCima (sidesOf φ (L) p) J []).current_step = (m : Int) + 2 := by
    rw [(keeps_filterAllCima _ J []).1.step_eq, hcs]
  exact sat_of_famTriOkCone φ _ hwf m J (famTopSingle_sides φ hwf L m hLI p hps _ hcsX)
    (famTriOkCone_of_B _ _ hcheck) hmJ hcs hle hvX

/-! **What is left for the verdict of `ImprovesCima`.** The review of a union leaves every live entry
with a good top (`cimaOk_filterAllCima`), that is: alive in the family the top names, which is a live
state of the machine's own kind whose entries are entries of that one side. What remains is to read the
support out of it — `LinkedChain.sup_self` gives the support of that family, and the restriction test
carries it over to the side's send — and to close `HereditaryValid.ChainClosureAt` with it. -/
/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.AOk_filterAllCima' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AOk_filterAllCima

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.sat_of_famTriOkConeSides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_famTriOkConeSides

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.famTopSingle_sides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms famTopSingle_sides

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.sat_of_filterCheck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_filterCheck

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.sat_of_filterCheckCone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_filterCheckCone

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.sup_of_chainSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sup_of_chainSound

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.pinned_source_valid_of_pairSide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinned_source_valid_of_pairSide

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.pairSide_of_chainSide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairSide_of_chainSide

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.restTest_of_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms restTest_of_chain

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.pinned_source_valid_of_sideChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinned_source_valid_of_sideChain

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.AOk_filterAllCimaC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AOk_filterAllCimaC

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.pinned_source_valid_of_sideChainG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinned_source_valid_of_sideChainG

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.chainSound_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_transfer

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.cimaChain_of_famChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cimaChain_of_famChain

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.MInv_reviewCima' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MInv_reviewCima

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.LineInv_stepsCima' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LineInv_stepsCima

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.cima_chain_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cima_chain_below

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.valid_filterAllCima_of_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valid_filterAllCima_of_chain

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.sat_of_rulePreserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_rulePreserves

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.rulePreserves_of_genuine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rulePreserves_of_genuine

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.sat_of_pinnedUnionInhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinnedUnionInhabited

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.coneAt_famFix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms coneAt_famFix

end AbsSat.GraphPath.Model.ImprovesCima
