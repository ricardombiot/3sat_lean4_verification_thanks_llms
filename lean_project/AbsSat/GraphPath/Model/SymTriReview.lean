-- lean_project/AbsSat/GraphPath/Model/SymTriReview.lean
import AbsSat.GraphPath.Model.SymReview
import AbsSat.GraphPath.Model.FabricAdd

/-!
# The two corrections, joined: the symmetric review with the triangle pass

v64 added the mirror step, because the coherence pass breaks the symmetry of
the owner tables (`--symreview`: 63 violations over 3.070 construction states
against 0 for the symmetric machine). v69 added `triClean`, because case 17
held eighteen owner entries that no solution explains and the review never
looks at a pair.

**Each machine has one of the two and not the other.** `reviewSym` carries
symmetry and knows nothing of the triangle; `reviewTri` delivers the triangle
and, being built on the original `review`, loses symmetry. v88's `TableCtx` —
the hypothesis under which the whole valid state *is* a fabric — asks for both
at once, so neither machine satisfies it.

This module builds the one that does:

```
reviewSymTri = the symmetric review to its fixpoint, then a triangle sweep,
               and again, until the sweep stops removing anything
```

and proves the three things a machine has to earn:

* **it loses no solution** — `ChainSound_reviewSymTri`, from v64's
  `ChainSound_reviewSym` and v69's `ChainSound_triClean`;
* **it keeps the tables symmetric** — `OwnSymmetric_reviewSymTri`;
* **it delivers the triangle** — `TriProp_reviewSymTri`, which needed the
  measure bounds for the symmetric review (`measure_reviewSym_le` below; they
  did not exist).

What it does **not** yet carry is the fixpoint bookkeeping that `Fuel.lean`
does for the original review: `CoherentParents` and `OwnersGlobal` are proved
for `review`, not for `reviewSym`. Those are the two remaining fields of
`TableCtx`, and they are accounting of exactly the kind `Fuel.lean` already
contains.
-/

namespace AbsSat.GraphPath.Model.SymTriReview

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.SymReview
open AbsSat.GraphPath.Model.TriReview

-- ============================================================
-- The symmetric review never grows the measure
-- ============================================================

private theorem measure_foldl_le {β : Type} (f : GPathM → β → GPathM)
    (h : ∀ g b, GPathM.measure (f g b) ≤ GPathM.measure g) :
    ∀ (l : List β) (g : GPathM), GPathM.measure (l.foldl f g) ≤ GPathM.measure g := by
  intro l
  induction l with
  | nil => intro g; exact Nat.le_refl _
  | cons b bs ih =>
    intro g
    simp only [List.foldl_cons]
    exact Nat.le_trans (ih (f g b)) (h g b)

private theorem weight_symMap_le (d : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (symMap d id m).weight ≤ m.weight := by
  unfold symMap
  split
  · exact Nat.le_refl _
  · have := List.length_filter_le (fun q => q != id) m.owners
    simp only [PNodeM.weight]
    omega

private theorem weight_inter_le (b : List PathNodeId) (n : PNodeM) :
    ({ n with owners := intersectOwners n.owners b } : PNodeM).weight ≤ n.weight := by
  have := List.length_filter_le
    (fun q => !hasStepEntry b q.id.step || b.contains q) n.owners
  simp only [PNodeM.weight, intersectOwners]
  omega

/-- **The mirror step never grows the measure.** It only ever filters tables. -/
theorem measure_symmetrize_le (g : GPathM) (id : PathNodeId) :
    GPathM.measure (symmetrize g id) ≤ GPathM.measure g := by
  unfold symmetrize
  split
  · exact Nat.le_refl _
  · next d _ =>
    simp only [GPathM.measure]
    refine Nat.add_le_add (Nat.le_refl _) ?_
    rw [List.map_map]
    exact FabricAdd.sum_map_le _ _ (fun m => weight_symMap_le d id m) g.nodes

theorem measure_reviewNodeSym_le (nb : PNodeM → List PathNodeId) (id : PathNodeId)
    (g : GPathM) : GPathM.measure (reviewNodeSym g nb id) ≤ GPathM.measure g := by
  simp only [reviewNodeSym]
  split
  · exact Nat.le_refl _
  · next d _ =>
    split
    · have h₁ : GPathM.measure (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) ≤
            GPathM.measure g :=
        measure_updateAt_le g id _ (weight_inter_le _)
      have h₂ := Nat.le_trans (measure_symmetrize_le _ id) h₁
      have h₃ := Nat.le_trans (measure_unlinkIncompatible_le _ id) h₂
      split
      · exact h₃
      · exact Nat.le_trans (measure_removeNode_le _ id) h₃
    · exact measure_removeNode_le g id

theorem measure_cleanInvalidGoSym_le (ids : List PathNodeId) :
    ∀ g : GPathM, GPathM.measure (cleanInvalidGoSym g ids) ≤ GPathM.measure g := by
  induction ids with
  | nil => intro g; exact Nat.le_refl _
  | cons id rest ih =>
    intro g
    simp only [cleanInvalidGoSym]
    split
    · exact Nat.le_trans (ih g) (Nat.le_refl _)
    · next d _ =>
      have h₁ : GPathM.measure (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners g.gowners })) ≤
            GPathM.measure g :=
        measure_updateAt_le g id _ (weight_inter_le _)
      have h₂ := Nat.le_trans (measure_symmetrize_le _ id) h₁
      have h₃ := Nat.le_trans (measure_unlinkIncompatible_le _ id) h₂
      split
      · exact Nat.le_trans (ih _) h₃
      · exact Nat.le_trans (ih _) (Nat.le_trans (measure_removeNode_le _ id) h₃)

theorem measure_cleanInvalidSym_le (g : GPathM) :
    GPathM.measure (cleanInvalidSym g) ≤ GPathM.measure g :=
  measure_cleanInvalidGoSym_le _ g

theorem measure_reviewLineSym_le (nb : PNodeM → List PathNodeId) (k : Int) (g : GPathM) :
    GPathM.measure (reviewLineSym g nb k) ≤ GPathM.measure g :=
  measure_foldl_le (fun g id => reviewNodeSym g nb id)
    (fun g id => measure_reviewNodeSym_le nb id g) _ g

theorem measure_reviewStepsSym_le (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, GPathM.measure (reviewStepsSym g nb ks) ≤ GPathM.measure g := by
  induction ks with
  | nil => intro g; exact Nat.le_refl _
  | cons k ks ih =>
    intro g
    simp only [reviewStepsSym]
    split
    · exact Nat.le_trans (ih _) (measure_reviewLineSym_le nb k g)
    · exact Nat.le_refl _

theorem measure_reviewPassSym_le (g : GPathM) :
    GPathM.measure (reviewPassSym g) ≤ GPathM.measure g := by
  simp only [reviewPassSym, reviewSonsSym, reviewParentsSym]
  exact Nat.le_trans (measure_reviewStepsSym_le _ _ _)
    (Nat.le_trans (measure_reviewStepsSym_le _ _ _) (measure_cleanInvalidSym_le g))

theorem measure_reviewFuelSym_le : ∀ (fuel : Nat) (g : GPathM),
    GPathM.measure (reviewFuelSym fuel g) ≤ GPathM.measure g := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Nat.le_refl _
  | succ f ih =>
    intro g
    simp only [reviewFuelSym]
    if hval : isValid g = true then
      if hlt : GPathM.measure (reviewPassSym g) < GPathM.measure g then
        simp only [if_pos hval, if_pos hlt]
        exact Nat.le_trans (ih _) (Nat.le_of_lt hlt)
      else
        simp only [if_pos hval, if_neg hlt]
        exact measure_reviewPassSym_le g
    else
      simp only [if_neg hval]
      exact Nat.le_refl _

/-- **The symmetric review never grows the measure.** The bound `reviewTri`'s
loop needed for the original review, now for the symmetric one. -/
theorem measure_reviewSym_le (g : GPathM) :
    GPathM.measure (reviewSym g) ≤ GPathM.measure g :=
  measure_reviewFuelSym_le _ g

-- ============================================================
-- The joined machine
-- ============================================================

/-- The symmetric review to its fixpoint, then a triangle sweep, and again
until the sweep stops removing anything. -/
def reviewSymTriFuel : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    let g₁ := reviewSym g
    if isValid g₁ then
      let g₂ := triClean g₁
      if GPathM.measure g₂ < GPathM.measure g₁ then reviewSymTriFuel fuel g₂ else g₁
    else g₁

def reviewSymTri (g : GPathM) : GPathM := reviewSymTriFuel (GPathM.measure g + 1) g

def filterAllSymTri (g : GPathM) (reqs : List NodeId) : GPathM :=
  reviewSymTri (reqs.foldl filterRequire g)

def upFilteringSymTri (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String) : GPathM :=
  up (filterAllSymTri g reqs) d title

/-- One reading step on the joined machine: pin by owners, then review. -/
def readStepSymTri (g : GPathM) (r : PathNodeId) : GPathM :=
  reviewSymTri (pinOwners g r)

-- ============================================================
-- It loses no solution
-- ============================================================

theorem ChainSound_reviewSymTriFuel :
    ∀ (fuel : Nat) (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      ChainSound (reviewSymTriFuel fuel g) sel := by
  intro fuel
  induction fuel with
  | zero => intro g sel h; exact h
  | succ f ih =>
    intro g sel h
    have h₁ := ChainSound_reviewSym g sel h
    simp only [reviewSymTriFuel]
    split
    · split
      · exact ih _ sel (ChainSound_triClean _ sel h₁)
      · exact h₁
    · exact h₁

/-- **The joined machine loses no solution.** Both halves are already known to:
the symmetric review by v64, the triangle sweep by v69. -/
theorem ChainSound_reviewSymTri (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (reviewSymTri g) sel :=
  ChainSound_reviewSymTriFuel _ g sel h

theorem ChainSound_filterAllSymTri (g : GPathM) (reqs : List NodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (hreqs : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    ChainSound (filterAllSymTri g reqs) sel :=
  ChainSound_reviewSymTri _ sel (ChainSound_foldl_filterRequire reqs g sel h hreqs)

-- ============================================================
-- It keeps the tables symmetric
-- ============================================================

theorem OwnSymmetric_reviewSymTriFuel :
    ∀ (fuel : Nat) (g : GPathM), Threaded.OwnSymmetric g →
      Threaded.OwnSymmetric (reviewSymTriFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    have h₁ := OwnSymmetric_reviewSym g h
    simp only [reviewSymTriFuel]
    split
    · split
      · exact ih _ (FabricAdd.OwnSymmetric_triClean _ h₁)
      · exact h₁
    · exact h₁

/-- **The joined machine keeps the tables symmetric.** v64 for the review, and
`OwnSymmetric_triClean` for the sweep — whose test asks for a node in *both*
tables, and so cannot break symmetry. -/
theorem OwnSymmetric_reviewSymTri (g : GPathM) (h : Threaded.OwnSymmetric g) :
    Threaded.OwnSymmetric (reviewSymTri g) :=
  OwnSymmetric_reviewSymTriFuel _ g h

theorem OwnSymmetric_filterAllSymTri (g : GPathM) (reqs : List NodeId)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (filterAllSymTri g reqs) :=
  OwnSymmetric_reviewSymTri _ (OwnSymmetric_foldl_filterRequire reqs g h)

theorem OwnSymmetric_readStepSymTri (g : GPathM) (r : PathNodeId)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (readStepSymTri g r) :=
  OwnSymmetric_reviewSymTri _ (OwnSymmetric_pinOwners g r h)

-- ============================================================
-- It delivers the triangle
-- ============================================================

theorem TriProp_reviewSymTriFuel :
    ∀ (fuel : Nat) (g : GPathM), GPathM.measure g ≤ fuel →
      isValid (reviewSymTriFuel fuel g) = true →
      FabricAdd.TriProp (reviewSymTriFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero =>
    intro g hm hv
    simp only [reviewSymTriFuel] at hv ⊢
    intro a na b nb _ _ _ l hl0 hl
    have hgow : g.gowners = [] := by
      simp only [GPathM.measure] at hm
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hk : l ∈ intRange 0 (g.current_step - 1) := mem_intRange hl0 (by omega)
    have hstep := List.all_eq_true.mp hv l hk
    simp only [hasStepEntry, hgow, List.any_nil] at hstep
    exact absurd hstep (by simp)
  | succ f ih =>
    intro g hm hv
    simp only [reviewSymTriFuel] at hv ⊢
    if hval : isValid (reviewSym g) = true then
      if hlt : GPathM.measure (triClean (reviewSym g)) < GPathM.measure (reviewSym g) then
        simp only [if_pos hval, if_pos hlt] at hv ⊢
        exact ih _ (by have := measure_reviewSym_le g; omega) hv
      else
        simp only [if_pos hval, if_neg hlt] at hv ⊢
        exact FabricAdd.TriProp_of_triClean_fixpoint _
          (FabricAdd.triClean_eq_of_measure_ge _ (by omega))
    else
      simp only [if_neg hval] at hv ⊢
      exact absurd hv hval

/-- **The joined machine delivers the triangle.** Same reading as v85: at a
fixpoint of `triClean`, an entry survived *because* the sweep's own test held,
and that test is `TriProp`. -/
theorem TriProp_reviewSymTri (g : GPathM) (hv : isValid (reviewSymTri g) = true) :
    FabricAdd.TriProp (reviewSymTri g) :=
  TriProp_reviewSymTriFuel _ g (Nat.le_succ _) hv

-- ============================================================
-- And it prunes only
-- ============================================================

/-! `Pruned.lean` stops at the original review. The mirror step needs the same
five lines, and then the chain repeats. -/

private theorem symMap_props (d : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (symMap d id m).id = m.id ∧ (∀ q ∈ (symMap d id m).owners, q ∈ m.owners) ∧
    (∀ p ∈ (symMap d id m).parents, p ∈ m.parents) := by
  unfold symMap
  split
  · exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  · exact ⟨rfl, fun q hq => (List.mem_filter.mp hq).1, fun _ h => h⟩

theorem pruned_symmetrize (g : GPathM) (id : PathNodeId) : Pruned g (symmetrize g id) := by
  unfold symmetrize
  split
  · exact Pruned.refl g
  · next d _ =>
    refine ⟨rfl, rfl, fun q hq => hq, ?_⟩
    intro n' hn'
    obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hn'
    obtain ⟨h1, h2, h3⟩ := symMap_props d id m
    exact ⟨m, hm, by rw [← hEq]; exact h1, by rw [← hEq]; exact h2, by rw [← hEq]; exact h3⟩

theorem pruned_reviewNodeSym (nb : PNodeM → List PathNodeId) (id : PathNodeId)
    (g : GPathM) : Pruned g (reviewNodeSym g nb id) := by
  simp only [reviewNodeSym]
  split
  · exact Pruned.refl g
  · next d _ =>
    split
    · have h₁ : Pruned g (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) :=
        pruned_updateAt g id _ (fun _ => rfl)
          (fun _ q hq => (List.mem_filter.mp hq).1) (fun _ _ hp => hp)
      have h₂ := Pruned.trans h₁ (pruned_symmetrize _ id)
      have h₃ := Pruned.trans h₂ (pruned_unlinkIncompatible _ id)
      split
      · exact h₃
      · exact Pruned.trans h₃ (pruned_removeNode _ id)
    · exact pruned_removeNode g id

theorem pruned_cleanInvalidGoSym (ids : List PathNodeId) :
    ∀ g : GPathM, Pruned g (cleanInvalidGoSym g ids) := by
  induction ids with
  | nil => intro g; exact Pruned.refl g
  | cons id rest ih =>
    intro g
    simp only [cleanInvalidGoSym]
    split
    · exact ih g
    · next d _ =>
      refine Pruned.trans ?_ (ih _)
      have h₁ : Pruned g (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners g.gowners })) :=
        pruned_updateAt g id _ (fun _ => rfl)
          (fun _ q hq => (List.mem_filter.mp hq).1) (fun _ _ hp => hp)
      have h₂ := Pruned.trans h₁ (pruned_symmetrize _ id)
      have h₃ := Pruned.trans h₂ (pruned_unlinkIncompatible _ id)
      split
      · exact h₃
      · exact Pruned.trans h₃ (pruned_removeNode _ id)

theorem pruned_cleanInvalidSym (g : GPathM) : Pruned g (cleanInvalidSym g) :=
  pruned_cleanInvalidGoSym _ g

theorem pruned_reviewLineSym (nb : PNodeM → List PathNodeId) (k : Int) (g : GPathM) :
    Pruned g (reviewLineSym g nb k) :=
  pruned_foldl (fun g id => reviewNodeSym g nb id)
    (fun g id => pruned_reviewNodeSym nb id g) _ g

theorem pruned_reviewStepsSym (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, Pruned g (reviewStepsSym g nb ks) := by
  induction ks with
  | nil => intro g; exact Pruned.refl g
  | cons k ks ih =>
    intro g
    simp only [reviewStepsSym]
    split
    · exact Pruned.trans (pruned_reviewLineSym nb k g) (ih _)
    · exact Pruned.refl g

theorem pruned_reviewPassSym (g : GPathM) : Pruned g (reviewPassSym g) := by
  simp only [reviewPassSym, reviewSonsSym, reviewParentsSym]
  exact Pruned.trans (pruned_cleanInvalidSym g)
    (Pruned.trans (pruned_reviewStepsSym _ _ _) (pruned_reviewStepsSym _ _ _))

theorem pruned_reviewFuelSym : ∀ (fuel : Nat) (g : GPathM),
    Pruned g (reviewFuelSym fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Pruned.refl g
  | succ f ih =>
    intro g
    simp only [reviewFuelSym]
    split
    · split
      · exact Pruned.trans (pruned_reviewPassSym g) (ih _)
      · exact pruned_reviewPassSym g
    · exact Pruned.refl g

theorem pruned_reviewSym (g : GPathM) : Pruned g (reviewSym g) :=
  pruned_reviewFuelSym _ g


theorem pruned_reviewSymTriFuel : ∀ (fuel : Nat) (g : GPathM),
    Pruned g (reviewSymTriFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Pruned.refl g
  | succ f ih =>
    intro g
    simp only [reviewSymTriFuel]
    split
    · split
      · exact Pruned.trans
          (Pruned.trans (pruned_reviewSym g) (FabricAdd.pruned_triClean _)) (ih _)
      · exact pruned_reviewSym g
    · exact pruned_reviewSym g

theorem pruned_reviewSymTri (g : GPathM) : Pruned g (reviewSymTri g) :=
  pruned_reviewSymTriFuel _ g

/-- **And so `OOS` comes for free.** A node's owners at its own step contain
nothing but the node; the invariant only ever needs the state to shrink, and
`pruned_reviewSymTri` says it does. -/
theorem OOS_reviewSymTri (g : GPathM) (h : SelfOwn.OOS g) : SelfOwn.OOS (reviewSymTri g) :=
  SelfOwn.OOS_of_pruned (pruned_reviewSymTri g) h

theorem OOS_filterAllSymTri (g : GPathM) (reqs : List NodeId) (h : SelfOwn.OOS g) :
    SelfOwn.OOS (filterAllSymTri g reqs) :=
  OOS_reviewSymTri _ (by
    have : Pruned g (reqs.foldl filterRequire g) :=
      pruned_foldl filterRequire pruned_filterRequire reqs g
    exact SelfOwn.OOS_of_pruned this h)

/-- The pins survive the joined review, as they survive the other two. -/
theorem gowners_compat_filterAllSymTri (g : GPathM) (reqs : List NodeId) :
    ∀ q ∈ (filterAllSymTri g reqs).gowners, FabricAdd.Compat reqs q := fun q hq =>
  FabricAdd.gowners_foldl_compat reqs g q
    ((pruned_reviewSymTri (reqs.foldl filterRequire g)).gowners_sub q hq)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.measure_reviewSym_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms measure_reviewSym_le

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.ChainSound_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.OwnSymmetric_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.TriProp_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TriProp_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.pruned_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pruned_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.OOS_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OOS_reviewSymTri

end AbsSat.GraphPath.Model.SymTriReview
