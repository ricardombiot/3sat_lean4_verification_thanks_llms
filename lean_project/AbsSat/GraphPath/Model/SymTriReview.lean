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
-- The fixpoint theory for the symmetric review
-- ============================================================

/-! `Fuel.lean` proves, for the original review, that a state the loop leaves
valid is a genuine **fixpoint of the pass** — not merely a point where the
measure stopped moving — and reads two per-node facts off it:

* `review_owners_within_gowners` — the owners are already inside the global
  owners (`OwnersGlobal`);
* `review_owners_coherent_parents` — and already coherent with the parents'
  union (`CoherentParents`).

Those are the two fields v88's `TableCtx` still lacked. The symmetric review
runs the same shapes with one extra operation, the mirror step, wedged between
the intersection and the unlink — so the whole chain repeats with
`symmetrize_eq_self` added at each joint. -/

private theorem map_eq_self_of {α : Type} (l : List α) (f : α → α)
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem map_eq_self_pointwise {α : Type} (l : List α) (f : α → α)
    (h : l.map f = l) : ∀ a ∈ l, f a = a := by
  induction l with
  | nil => intro a ha; exact absurd ha List.not_mem_nil
  | cons a as ih =>
    simp only [List.map_cons, List.cons.injEq] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h.1
    · exact ih h.2 x hx'

private theorem inter_eq_self_of_weight (b : List PathNodeId) (n : PNodeM)
    (h : PNodeM.weight { n with owners := intersectOwners n.owners b } = PNodeM.weight n) :
    { n with owners := intersectOwners n.owners b } = n := by
  have hlen : n.owners.length ≤ (intersectOwners n.owners b).length := by
    simp only [PNodeM.weight] at h; omega
  have : intersectOwners n.owners b = n.owners :=
    FabricAdd.filter_eq_self_of_length _ _ hlen
  rw [this]

private theorem symMap_eq_self_of_weight (d : PNodeM) (id : PathNodeId) (m : PNodeM)
    (h : PNodeM.weight (symMap d id m) = PNodeM.weight m) : symMap d id m = m := by
  unfold symMap at h ⊢
  cases hc : (m.id == id || d.owners.contains m.id) with
  | true => simp
  | false =>
    simp only [hc, Bool.false_eq_true, if_false] at h ⊢
    have hlen : m.owners.length ≤ (m.owners.filter (fun q => q != id)).length := by
      simp only [PNodeM.weight] at h; omega
    rw [FabricAdd.filter_eq_self_of_length _ _ hlen]

/-- **The mirror step at the fixpoint is the identity.** -/
theorem symmetrize_eq_self (g : GPathM) (id : PathNodeId)
    (h : GPathM.measure (symmetrize g id) = GPathM.measure g) : symmetrize g id = g := by
  cases hn : g.node? id with
  | none => simp [symmetrize, hn]
  | some d =>
    have hshape : symmetrize g id = { g with nodes := g.nodes.map (symMap d id) } := by
      simp only [symmetrize, hn]
    rw [hshape] at h ⊢
    simp only [GPathM.measure] at h
    rw [List.map_map] at h
    have hpt := FabricAdd.sum_eq_pointwise (PNodeM.weight ∘ symMap d id) PNodeM.weight
      (fun m => weight_symMap_le d id m) g.nodes (by omega)
    have hmap : g.nodes.map (symMap d id) = g.nodes :=
      map_eq_self_of _ _ (fun m hm => symMap_eq_self_of_weight d id m (hpt m hm))
    rw [hmap]

private theorem exists_id_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, (f n).id = n.id) (i : PathNodeId) (h : ∃ n ∈ g.nodes, n.id = i) :
    ∃ n ∈ (updateAt g id f).nodes, n.id = i := by
  obtain ⟨n, hn, hid⟩ := h
  refine ⟨(fun n => match n.id == id with | true => f n | false => n) n, ?_, ?_⟩
  · simp only [updateAt, updateAtGo]
    exact List.mem_map_of_mem hn
  · cases hb : n.id == id
    · simp only [hb]; exact hid
    · simp only [hb]; rw [hf]; exact hid

private theorem exists_id_symmetrize (g : GPathM) (j i : PathNodeId)
    (h : ∃ n ∈ g.nodes, n.id = i) : ∃ n ∈ (symmetrize g j).nodes, n.id = i := by
  unfold symmetrize
  split
  · exact h
  · next d _ =>
    obtain ⟨n, hn, hid⟩ := h
    exact ⟨symMap d j n, List.mem_map_of_mem hn, by rw [(symMap_props d j n).1]; exact hid⟩

private theorem exists_id_unlink (g : GPathM) (j i : PathNodeId)
    (h : ∃ n ∈ g.nodes, n.id = i) : ∃ n ∈ (unlinkIncompatible g j).nodes, n.id = i := by
  unfold GPathM.unlinkIncompatible
  split
  · exact h
  · next n₀ _ =>
    obtain ⟨n, hn, hid⟩ := h
    exact ⟨unlinkMap n₀ j n, List.mem_map_of_mem hn, by rw [unlinkMap_id]; exact hid⟩

/-- The tail both symmetric passes end with: intersect, mirror, unlink, and
drop the node if that left it invalid. -/
def symIntersectOrDrop (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (d : PNodeM) : GPathM :=
  if isValidNode
      (unlinkIncompatible (symmetrize
        (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id) id)
      (relink (intersectOwners d.owners b) d) then
    unlinkIncompatible (symmetrize
      (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id) id
  else
    removeNode (unlinkIncompatible (symmetrize
      (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id) id) id

theorem measure_symIntersectOrDrop_le (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (d : PNodeM) : GPathM.measure (symIntersectOrDrop g id b d) ≤ GPathM.measure g := by
  have h1 : GPathM.measure (updateAt g id
      (fun n => { n with owners := intersectOwners n.owners b })) ≤ GPathM.measure g :=
    measure_updateAt_le g id _ (weight_inter_le b)
  have h2 := Nat.le_trans (measure_symmetrize_le _ id) h1
  have h3 := Nat.le_trans (measure_unlinkIncompatible_le _ id) h2
  unfold symIntersectOrDrop
  split
  · exact h3
  · exact Nat.le_trans (measure_removeNode_le _ id) h3

/-- **At the fixpoint the tail is the identity, in all three of its stages.**
The drop branch is unreachable: removing a node that is actually there
strictly shrinks the measure. -/
theorem symIntersectOrDrop_valid_branch (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (d : PNodeM) (hd_mem : d ∈ g.nodes) (hd_id : d.id = id)
    (h : GPathM.measure (symIntersectOrDrop g id b d) = GPathM.measure g) :
    updateAt g id (fun n => { n with owners := intersectOwners n.owners b }) = g ∧
      symmetrize g id = g ∧ unlinkIncompatible g id = g ∧
      isValidNode g (relink (intersectOwners d.owners b) d) = true := by
  have hupd_le : GPathM.measure (updateAt g id
      (fun n => { n with owners := intersectOwners n.owners b })) ≤ GPathM.measure g :=
    measure_updateAt_le g id _ (weight_inter_le b)
  have hsym_le := measure_symmetrize_le
    (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id
  have hunl_le := measure_unlinkIncompatible_le
    (symmetrize (updateAt g id
      (fun n => { n with owners := intersectOwners n.owners b })) id) id
  obtain ⟨n, hn, hn_id⟩ : ∃ n ∈ (unlinkIncompatible (symmetrize (updateAt g id
      (fun n => { n with owners := intersectOwners n.owners b })) id) id).nodes, n.id = id :=
    exists_id_unlink _ id id (exists_id_symmetrize _ id id
      (exists_id_updateAt g id (fun n => { n with owners := intersectOwners n.owners b })
        (fun _ => rfl) id ⟨d, hd_mem, hd_id⟩))
  have hlt := measure_removeNode_lt _ id n hn hn_id
  unfold symIntersectOrDrop at h
  split at h
  · next hv =>
    have h1 : GPathM.measure (updateAt g id
        (fun n => { n with owners := intersectOwners n.owners b })) = GPathM.measure g := by
      omega
    have hupd : updateAt g id (fun n => { n with owners := intersectOwners n.owners b }) = g :=
      updateAt_eq_self g id _ (weight_inter_le b) (fun n => inter_eq_self_of_weight b n) h1
    rw [hupd] at h hv hsym_le hunl_le
    have hsy : symmetrize g id = g := symmetrize_eq_self g id (by omega)
    rw [hsy] at h hv hunl_le
    have hunl : unlinkIncompatible g id = g := unlinkIncompatible_eq_self g id (by omega)
    rw [hunl] at hv
    exact ⟨hupd, hsy, hunl, hv⟩
  · exact absurd h (Nat.ne_of_lt
      (Nat.lt_of_lt_of_le hlt (Nat.le_trans hunl_le (Nat.le_trans hsym_le hupd_le))))

theorem symIntersectOrDrop_eq_self (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (d : PNodeM) (hd_mem : d ∈ g.nodes) (hd_id : d.id = id)
    (h : GPathM.measure (symIntersectOrDrop g id b d) = GPathM.measure g) :
    symIntersectOrDrop g id b d = g := by
  obtain ⟨hupd, hsy, hunl, hv⟩ := symIntersectOrDrop_valid_branch g id b d hd_mem hd_id h
  unfold symIntersectOrDrop
  rw [hupd, hsy, hunl, if_pos hv]

-- ------------------------------------------------------------
-- `cleanInvalidSym` at the fixpoint
-- ------------------------------------------------------------

def cleanStepSym (g : GPathM) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some d => symIntersectOrDrop g id g.gowners d

theorem cleanInvalidGoSym_cons (g : GPathM) (id : PathNodeId) (rest : List PathNodeId) :
    cleanInvalidGoSym g (id :: rest) = cleanInvalidGoSym (cleanStepSym g id) rest := by
  cases hnode : g.node? id <;>
    simp [cleanInvalidGoSym, cleanStepSym, symIntersectOrDrop, hnode]

theorem measure_cleanStepSym_le (g : GPathM) (id : PathNodeId) :
    GPathM.measure (cleanStepSym g id) ≤ GPathM.measure g := by
  simp only [cleanStepSym]
  split
  · exact Nat.le_refl _
  · exact measure_symIntersectOrDrop_le _ _ _ _

theorem cleanStepSym_eq_self (g : GPathM) (id : PathNodeId)
    (h : GPathM.measure (cleanStepSym g id) = GPathM.measure g) : cleanStepSym g id = g := by
  cases hnode : g.node? id with
  | none => simp [cleanStepSym, hnode]
  | some d =>
    simp only [cleanStepSym, hnode] at h ⊢
    exact symIntersectOrDrop_eq_self g id g.gowners d
      (List.mem_of_find?_eq_some hnode) (node?_id_eq g id d hnode) h

theorem cleanInvalidGoSym_steps_eq_self (ids : List PathNodeId) :
    ∀ g : GPathM, GPathM.measure (cleanInvalidGoSym g ids) = GPathM.measure g →
      ∀ id ∈ ids, cleanStepSym g id = g := by
  induction ids with
  | nil => intro g _ id hid; exact absurd hid List.not_mem_nil
  | cons id rest ih =>
    intro g heq id' hid'
    rw [cleanInvalidGoSym_cons] at heq
    have h₁ := measure_cleanStepSym_le g id
    have h₂ := measure_cleanInvalidGoSym_le rest (cleanStepSym g id)
    have hfix : cleanStepSym g id = g := cleanStepSym_eq_self g id (by omega)
    rw [hfix] at heq
    rcases List.mem_cons.mp hid' with rfl | hid''
    · exact hfix
    · exact ih g heq id' hid''

theorem cleanInvalidGoSym_eq_self (ids : List PathNodeId) :
    ∀ g : GPathM, GPathM.measure (cleanInvalidGoSym g ids) = GPathM.measure g →
      cleanInvalidGoSym g ids = g := by
  induction ids with
  | nil => intro g _; simp [cleanInvalidGoSym]
  | cons id rest ih =>
    intro g heq
    rw [cleanInvalidGoSym_cons] at heq ⊢
    have h₁ := measure_cleanStepSym_le g id
    have h₂ := measure_cleanInvalidGoSym_le rest (cleanStepSym g id)
    have hfix : cleanStepSym g id = g := cleanStepSym_eq_self g id (by omega)
    rw [hfix] at heq ⊢
    exact ih g heq

theorem cleanInvalidSym_eq_self (g : GPathM)
    (h : GPathM.measure (cleanInvalidSym g) = GPathM.measure g) : cleanInvalidSym g = g :=
  cleanInvalidGoSym_eq_self _ g h

-- ------------------------------------------------------------
-- The coherence passes at the fixpoint
-- ------------------------------------------------------------

theorem reviewNodeSym_shape (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId)
    (d : PNodeM) (hd : g.node? id = some d) :
    reviewNodeSym g nb id =
      if isValidNode g d then symIntersectOrDrop g id (unionOwnersOf g (nb d)) d
      else removeNode g id := by
  simp [reviewNodeSym, hd, symIntersectOrDrop]

theorem reviewNodeSym_eq_self (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId)
    (h : GPathM.measure (reviewNodeSym g nb id) = GPathM.measure g) :
    reviewNodeSym g nb id = g := by
  cases hnode : g.node? id with
  | none => simp [reviewNodeSym, hnode]
  | some d =>
    have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hnode
    have hd_id : d.id = id := node?_id_eq g id d hnode
    rw [reviewNodeSym_shape g nb id d hnode] at h ⊢
    split at h
    · next hvalid =>
      rw [if_pos hvalid]
      exact symIntersectOrDrop_eq_self g id _ d hd_mem hd_id h
    · next hvalid =>
      rw [if_neg hvalid]
      exact absurd h (Nat.ne_of_lt (measure_removeNode_lt g id d hd_mem hd_id))

private theorem foldl_eq_self {β : Type} (f : GPathM → β → GPathM)
    (hle : ∀ g b, GPathM.measure (f g b) ≤ GPathM.measure g)
    (hid : ∀ g b, GPathM.measure (f g b) = GPathM.measure g → f g b = g) :
    ∀ (l : List β) (g : GPathM),
      GPathM.measure (l.foldl f g) = GPathM.measure g → l.foldl f g = g := by
  intro l
  induction l with
  | nil => intro g _; simp
  | cons b bs ih =>
    intro g heq
    simp only [List.foldl_cons] at heq ⊢
    have h₁ := hle g b
    have h₂ := measure_foldl_le f hle bs (f g b)
    have hstep : GPathM.measure (f g b) = GPathM.measure g := by omega
    rw [hid g b hstep] at heq ⊢
    exact ih g heq

private theorem foldl_steps_eq_self {β : Type} (f : GPathM → β → GPathM)
    (hle : ∀ g b, GPathM.measure (f g b) ≤ GPathM.measure g)
    (hid : ∀ g b, GPathM.measure (f g b) = GPathM.measure g → f g b = g) :
    ∀ (l : List β) (g : GPathM), GPathM.measure (l.foldl f g) = GPathM.measure g →
      ∀ b ∈ l, f g b = g := by
  intro l
  induction l with
  | nil => intro g _ b hb; exact absurd hb List.not_mem_nil
  | cons b bs ih =>
    intro g heq b' hb'
    simp only [List.foldl_cons] at heq
    have h₁ := hle g b
    have h₂ := measure_foldl_le f hle bs (f g b)
    have hfix : f g b = g := hid g b (by omega)
    rw [hfix] at heq
    rcases List.mem_cons.mp hb' with rfl | hb''
    · exact hfix
    · exact ih g heq b' hb''

theorem reviewLineSym_eq_self (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int)
    (h : GPathM.measure (reviewLineSym g nb k) = GPathM.measure g) : reviewLineSym g nb k = g :=
  foldl_eq_self (fun g id => reviewNodeSym g nb id)
    (fun g id => measure_reviewNodeSym_le nb id g)
    (fun g id => reviewNodeSym_eq_self g nb id) _ g h

theorem reviewLineSym_nodes_eq_self (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int)
    (h : GPathM.measure (reviewLineSym g nb k) = GPathM.measure g) :
    ∀ id ∈ ((g.line k).map (·.id)), reviewNodeSym g nb id = g :=
  foldl_steps_eq_self (fun g id => reviewNodeSym g nb id)
    (fun g id => measure_reviewNodeSym_le nb id g)
    (fun g id => reviewNodeSym_eq_self g nb id) _ g h

theorem reviewStepsSym_eq_self (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, GPathM.measure (reviewStepsSym g nb ks) = GPathM.measure g →
      reviewStepsSym g nb ks = g := by
  induction ks with
  | nil => intro g _; simp [reviewStepsSym]
  | cons k ks ih =>
    intro g heq
    simp only [reviewStepsSym] at heq ⊢
    split at heq
    · next hv =>
      rw [if_pos hv]
      have h₁ := measure_reviewLineSym_le nb k g
      have h₂ := measure_reviewStepsSym_le nb ks (reviewLineSym g nb k)
      have hline : GPathM.measure (reviewLineSym g nb k) = GPathM.measure g := by omega
      rw [reviewLineSym_eq_self g nb k hline] at heq ⊢
      exact ih g heq
    · next hv => rw [if_neg hv]

theorem reviewStepsSym_lines_eq_self (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, isValid g = true →
      GPathM.measure (reviewStepsSym g nb ks) = GPathM.measure g →
      ∀ k ∈ ks, reviewLineSym g nb k = g := by
  induction ks with
  | nil => intro g _ _ k hk; exact absurd hk List.not_mem_nil
  | cons k ks ih =>
    intro g hvalid heq k' hk'
    simp only [reviewStepsSym] at heq
    rw [if_pos hvalid] at heq
    have h₁ := measure_reviewLineSym_le nb k g
    have h₂ := measure_reviewStepsSym_le nb ks (reviewLineSym g nb k)
    have hfix : reviewLineSym g nb k = g := reviewLineSym_eq_self g nb k (by omega)
    rw [hfix] at heq
    rcases List.mem_cons.mp hk' with rfl | hk''
    · exact hfix
    · exact ih g hvalid heq k' hk''

theorem measure_reviewParentsSym_le (g : GPathM) :
    GPathM.measure (reviewParentsSym g) ≤ GPathM.measure g :=
  measure_reviewStepsSym_le _ _ g

theorem measure_reviewSonsSym_le (g : GPathM) :
    GPathM.measure (reviewSonsSym g) ≤ GPathM.measure g :=
  measure_reviewStepsSym_le _ _ g

theorem reviewParentsSym_eq_self (g : GPathM)
    (h : GPathM.measure (reviewParentsSym g) = GPathM.measure g) : reviewParentsSym g = g :=
  reviewStepsSym_eq_self _ _ g h

theorem reviewSonsSym_eq_self (g : GPathM)
    (h : GPathM.measure (reviewSonsSym g) = GPathM.measure g) : reviewSonsSym g = g :=
  reviewStepsSym_eq_self _ _ g h

theorem reviewPassSym_eq_self (g : GPathM)
    (h : GPathM.measure (reviewPassSym g) = GPathM.measure g) : reviewPassSym g = g := by
  have h₁ := measure_cleanInvalidSym_le g
  have h₂ := measure_reviewParentsSym_le (cleanInvalidSym g)
  have h₃ := measure_reviewSonsSym_le (reviewParentsSym (cleanInvalidSym g))
  simp only [reviewPassSym] at h ⊢
  have hclean : GPathM.measure (cleanInvalidSym g) = GPathM.measure g := by omega
  rw [cleanInvalidSym_eq_self g hclean] at h ⊢
  have h₂' := measure_reviewParentsSym_le g
  have h₃' := measure_reviewSonsSym_le (reviewParentsSym g)
  have hpar : GPathM.measure (reviewParentsSym g) = GPathM.measure g := by omega
  rw [reviewParentsSym_eq_self g hpar] at h ⊢
  exact reviewSonsSym_eq_self g h

/-- The three stages of a fixpoint pass are each the identity. -/
theorem reviewPassSym_stages_eq_self (g : GPathM)
    (h : GPathM.measure (reviewPassSym g) = GPathM.measure g) :
    cleanInvalidSym g = g ∧ reviewParentsSym g = g ∧ reviewSonsSym g = g := by
  have h₁ := measure_cleanInvalidSym_le g
  have h₂ := measure_reviewParentsSym_le (cleanInvalidSym g)
  have h₃ := measure_reviewSonsSym_le (reviewParentsSym (cleanInvalidSym g))
  simp only [reviewPassSym] at h
  have hclean : cleanInvalidSym g = g := cleanInvalidSym_eq_self g (by omega)
  rw [hclean] at h h₂ h₃
  have h₃' := measure_reviewSonsSym_le (reviewParentsSym g)
  have hpar : reviewParentsSym g = g := reviewParentsSym_eq_self g (by omega)
  rw [hpar] at h
  exact ⟨hclean, hpar, reviewSonsSym_eq_self g h⟩

-- ------------------------------------------------------------
-- The loop really reaches a fixpoint of the pass
-- ------------------------------------------------------------

theorem reviewFuelSym_fixpoint : ∀ (fuel : Nat) (g : GPathM), GPathM.measure g < fuel →
    isValid (reviewFuelSym fuel g) = true →
    reviewPassSym (reviewFuelSym fuel g) = reviewFuelSym fuel g := by
  intro fuel
  induction fuel with
  | zero => intro g hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro g hlt hvalid
    simp only [reviewFuelSym] at hvalid ⊢
    split at hvalid
    · next hv =>
      rw [if_pos hv]
      split at hvalid
      · next hdec =>
        rw [if_pos hdec]
        exact ih (reviewPassSym g) (by omega) hvalid
      · next hdec =>
        rw [if_neg hdec]
        have hle := measure_reviewPassSym_le g
        have hfix : reviewPassSym g = g := reviewPassSym_eq_self g (by omega)
        simp only [hfix]
    · next hv =>
      rw [if_neg hv]
      exact absurd hvalid hv

/-- **The symmetric review is a genuine fixpoint of its pass**, on the states
it leaves valid. -/
theorem reviewPassSym_reviewSym (g : GPathM) (h : isValid (reviewSym g) = true) :
    reviewPassSym (reviewSym g) = reviewSym g :=
  reviewFuelSym_fixpoint (GPathM.measure g + 1) g (Nat.lt_succ_self _) h

-- ------------------------------------------------------------
-- And so the two per-node facts
-- ------------------------------------------------------------

private theorem updateAt_pointwise (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (h : updateAt g id f = g) (d : PNodeM) (hd : d ∈ g.nodes) (hd_id : d.id = id) :
    f d = d := by
  have hmap : updateAtGo id f g.nodes = g.nodes := congrArg GPathM.nodes h
  rw [updateAtGo] at hmap
  have hpt := map_eq_self_pointwise g.nodes _ hmap d hd
  have hbeq : (d.id == id) = true := by rw [hd_id]; exact beq_iff_eq.mpr rfl
  simpa [hbeq] using hpt

theorem cleanStepSym_owners_fixed (g : GPathM) (id : PathNodeId) (d : PNodeM)
    (hd : g.node? id = some d)
    (h : GPathM.measure (cleanStepSym g id) = GPathM.measure g) :
    intersectOwners d.owners g.gowners = d.owners := by
  have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq g id d hd
  have hstep : GPathM.measure (symIntersectOrDrop g id g.gowners d) = GPathM.measure g := by
    simpa [cleanStepSym, hd] using h
  obtain ⟨hupd, _, _, _⟩ :=
    symIntersectOrDrop_valid_branch g id g.gowners d hd_mem hd_id hstep
  exact congrArg PNodeM.owners (updateAt_pointwise g id _ hupd d hd_mem hd_id)

theorem reviewNodeSym_owners_fixed (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) (d : PNodeM) (hd : g.node? id = some d)
    (h : GPathM.measure (reviewNodeSym g nb id) = GPathM.measure g) :
    intersectOwners d.owners (unionOwnersOf g (nb d)) = d.owners := by
  have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq g id d hd
  rw [reviewNodeSym_shape g nb id d hd] at h
  split at h
  · obtain ⟨hupd, _, _, _⟩ :=
      symIntersectOrDrop_valid_branch g id (unionOwnersOf g (nb d)) d hd_mem hd_id h
    exact congrArg PNodeM.owners (updateAt_pointwise g id _ hupd d hd_mem hd_id)
  · exact absurd h (Nat.ne_of_lt (measure_removeNode_lt g id d hd_mem hd_id))

/-- At the fixpoint, a node reached by `cleanInvalidGoSym` passed
`isValidNode`. -/
theorem cleanStepSym_node_valid (g : GPathM) (id : PathNodeId) (d : PNodeM)
    (hd : g.node? id = some d)
    (h : GPathM.measure (cleanStepSym g id) = GPathM.measure g) :
    isValidNode g d = true := by
  have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq g id d hd
  have hstep : GPathM.measure (symIntersectOrDrop g id g.gowners d) = GPathM.measure g := by
    simpa [cleanStepSym, hd] using h
  obtain ⟨hupd, _, hunl, hvalid⟩ :=
    symIntersectOrDrop_valid_branch g id g.gowners d hd_mem hd_id hstep
  have hfix : { d with owners := intersectOwners d.owners g.gowners } = d :=
    updateAt_pointwise g id _ hupd d hd_mem hd_id
  have hrel : relink (intersectOwners d.owners g.gowners) d = d := by
    show relinkSelf { d with owners := intersectOwners d.owners g.gowners } = d
    rw [hfix]; exact relinkSelf_eq_self_of_fixed g id d hd hunl
  rwa [hrel] at hvalid

/-- The `cleanInvalidSym` step for any node the symmetric review still exposes
was itself the identity — the shared first half of the per-node results. -/
theorem reviewSym_cleanStep_fixed (g : GPathM) (h : isValid (reviewSym g) = true)
    (id : PathNodeId) (d : PNodeM) (hd : (reviewSym g).node? id = some d) :
    cleanStepSym (reviewSym g) id = reviewSym g := by
  have hfix : reviewPassSym (reviewSym g) = reviewSym g := reviewPassSym_reviewSym g h
  obtain ⟨hclean, _, _⟩ := reviewPassSym_stages_eq_self (reviewSym g) (by rw [hfix])
  have hd_mem : d ∈ (reviewSym g).nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq _ id d hd
  have hid_mem : id ∈ (reviewSym g).nodes.map (·.id) := by
    have hmem := List.mem_map_of_mem (f := fun n : PNodeM => n.id) hd_mem
    rwa [hd_id] at hmem
  exact cleanInvalidGoSym_steps_eq_self _ (reviewSym g) (by rw [show
    cleanInvalidGoSym (reviewSym g) ((reviewSym g).nodes.map (·.id)) = reviewSym g from hclean])
    id hid_mem

/-- **Every node the symmetric review leaves passes `isValidNode`.** -/
theorem reviewSym_node_valid (g : GPathM) (h : isValid (reviewSym g) = true)
    (id : PathNodeId) (d : PNodeM) (hd : (reviewSym g).node? id = some d) :
    isValidNode (reviewSym g) d = true :=
  cleanStepSym_node_valid (reviewSym g) id d hd (by rw [reviewSym_cleanStep_fixed g h id d hd])

/-- **`OwnersGlobal` for the symmetric review** — the first of v88's two
missing fields, in `intersectOwners`' form. -/
theorem reviewSym_owners_within_gowners (g : GPathM) (h : isValid (reviewSym g) = true)
    (id : PathNodeId) (d : PNodeM) (hd : (reviewSym g).node? id = some d) :
    intersectOwners d.owners (reviewSym g).gowners = d.owners :=
  cleanStepSym_owners_fixed _ id d hd (by rw [reviewSym_cleanStep_fixed g h id d hd])

/-- **`CoherentParents` for the symmetric review** — the second. -/
theorem reviewSym_owners_coherent_parents (g : GPathM) (h : isValid (reviewSym g) = true)
    (k : Int) (hk : k ∈ intRange 1 ((reviewSym g).current_step - 1))
    (id : PathNodeId) (hid : id ∈ (((reviewSym g).line k).map (·.id)))
    (d : PNodeM) (hd : (reviewSym g).node? id = some d) :
    intersectOwners d.owners (unionOwnersOf (reviewSym g) d.parents) = d.owners := by
  have hfix : reviewPassSym (reviewSym g) = reviewSym g := reviewPassSym_reviewSym g h
  obtain ⟨_, hpar, _⟩ := reviewPassSym_stages_eq_self (reviewSym g) (by rw [hfix])
  have hpar' : reviewStepsSym (reviewSym g) (·.parents)
      (intRange 1 ((reviewSym g).current_step - 1)) = reviewSym g := hpar
  have hline : reviewLineSym (reviewSym g) (·.parents) k = reviewSym g :=
    reviewStepsSym_lines_eq_self _ _ (reviewSym g) h (by rw [hpar']) k hk
  have hnode : reviewNodeSym (reviewSym g) (·.parents) id = reviewSym g :=
    reviewLineSym_nodes_eq_self (reviewSym g) _ k (by rw [hline]) id hid
  exact reviewNodeSym_owners_fixed (reviewSym g) _ id d hd (by rw [hnode])

/-- **`CoherentSons` for the symmetric review** — the same for the bottom-up
pass, whose step range is one narrower. -/
theorem reviewSym_owners_coherent_sons (g : GPathM) (h : isValid (reviewSym g) = true)
    (k : Int) (hk : k ∈ intRange 0 ((reviewSym g).current_step - 2))
    (id : PathNodeId) (hid : id ∈ (((reviewSym g).line k).map (·.id)))
    (d : PNodeM) (hd : (reviewSym g).node? id = some d) :
    intersectOwners d.owners (unionOwnersOf (reviewSym g) d.sons) = d.owners := by
  have hfix : reviewPassSym (reviewSym g) = reviewSym g := reviewPassSym_reviewSym g h
  obtain ⟨_, _, hsons⟩ := reviewPassSym_stages_eq_self (reviewSym g) (by rw [hfix])
  have hsons' : reviewStepsSym (reviewSym g) (·.sons)
      (intRange 0 ((reviewSym g).current_step - 2)).reverse = reviewSym g := hsons
  have hline : reviewLineSym (reviewSym g) (·.sons) k = reviewSym g :=
    reviewStepsSym_lines_eq_self _ _ (reviewSym g) h (by rw [hsons']) k (List.mem_reverse.mpr hk)
  have hnode : reviewNodeSym (reviewSym g) (·.sons) id = reviewSym g :=
    reviewLineSym_nodes_eq_self (reviewSym g) _ k (by rw [hline]) id hid
  exact reviewNodeSym_owners_fixed (reviewSym g) _ id d hd (by rw [hnode])

-- ============================================================
-- The two fields, in the shape `TableCtx` wants
-- ============================================================

/-- The line a node sits on holds its id. -/
private theorem mem_line_ids (g : GPathM) (p : PathNodeId) (d : PNodeM)
    (hd : g.node? p = some d) : p ∈ ((g.line p.id.step).map (·.id)) := by
  have hmem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hid : d.id = p := node?_id_eq g p d hd
  have hline : d ∈ g.line p.id.step :=
    List.mem_filter.mpr ⟨hmem, by rw [hid]; exact beq_iff_eq.mpr rfl⟩
  have := List.mem_map_of_mem (f := fun n : PNodeM => n.id) hline
  rwa [hid] at this

/-- **`OwnersGlobal` for the symmetric review.** -/
theorem OwnersGlobal_reviewSym (g : GPathM) (hv : isValid (reviewSym g) = true) :
    FabricAdd.OwnersGlobal (reviewSym g) := fun r n hn w hw hl0 hl =>
  owners_mem_gowners (reviewSym g) n (reviewSym_owners_within_gowners g hv r n hn) w hw
    (hasStepEntry_of_isValid (reviewSym g) hv w.id.step hl0 hl)

/-- **`CoherentParents` for the symmetric review.** -/
theorem CoherentParents_reviewSym (g : GPathM) (hv : isValid (reviewSym g) = true) :
    FabricAdd.CoherentParents (reviewSym g) := by
  intro p n hn hp0 hptop
  exact reviewSym_owners_coherent_parents g hv p.id.step (mem_intRange hp0 (by omega))
    p (mem_line_ids _ p n hn) n hn

/-- The `cohSons` field of `TableCtx`, for the symmetric review. -/
theorem CoherentSons_reviewSym (g : GPathM) (hv : isValid (reviewSym g) = true) :
    ∀ p n, (reviewSym g).node? p = some n → 0 ≤ p.id.step →
      p.id.step < (reviewSym g).current_step - 1 →
      intersectOwners n.owners (unionOwnersOf (reviewSym g) n.sons) = n.owners := by
  intro p n hn hp0 hptop
  exact reviewSym_owners_coherent_sons g hv p.id.step (mem_intRange hp0 (by omega))
    p (mem_line_ids _ p n hn) n hn

-- ============================================================
-- And they transfer to the joined machine
-- ============================================================

/-- **Every state the joined loop returns is a symmetric-review fixpoint.**
The loop only ever exits by handing back `reviewSym h`: the triangle branch
either recurses on a strictly smaller state or stops on `reviewSym g` itself,
and the fuel — `measure g + 1` — never runs out, because each round loses at
least one unit of measure. -/
theorem reviewSymTriFuel_eq_reviewSym : ∀ (fuel : Nat) (g : GPathM),
    GPathM.measure g < fuel → ∃ h, reviewSymTriFuel fuel g = reviewSym h := by
  intro fuel
  induction fuel with
  | zero => intro g hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ f ih =>
    intro g hlt
    simp only [reviewSymTriFuel]
    if hval : isValid (reviewSym g) = true then
      if hdec : GPathM.measure (triClean (reviewSym g)) < GPathM.measure (reviewSym g) then
        simp only [if_pos hval, if_pos hdec]
        exact ih _ (by have := measure_reviewSym_le g; omega)
      else
        simp only [if_pos hval, if_neg hdec]
        exact ⟨g, rfl⟩
    else
      simp only [if_neg hval]
      exact ⟨g, rfl⟩

theorem reviewSymTri_eq_reviewSym (g : GPathM) : ∃ h, reviewSymTri g = reviewSym h :=
  reviewSymTriFuel_eq_reviewSym _ g (Nat.lt_succ_self _)

/-- **`OwnersGlobal` for the joined machine.** -/
theorem OwnersGlobal_reviewSymTri (g : GPathM) (hv : isValid (reviewSymTri g) = true) :
    FabricAdd.OwnersGlobal (reviewSymTri g) := by
  obtain ⟨h, he⟩ := reviewSymTri_eq_reviewSym g
  rw [he] at hv ⊢
  exact OwnersGlobal_reviewSym h hv

/-- **`CoherentParents` for the joined machine.** -/
theorem CoherentParents_reviewSymTri (g : GPathM) (hv : isValid (reviewSymTri g) = true) :
    FabricAdd.CoherentParents (reviewSymTri g) := by
  obtain ⟨h, he⟩ := reviewSymTri_eq_reviewSym g
  rw [he] at hv ⊢
  exact CoherentParents_reviewSym h hv

/-- **Node validity for the joined machine.** -/
theorem node_valid_reviewSymTri (g : GPathM) (hv : isValid (reviewSymTri g) = true) :
    ∀ p n, (reviewSymTri g).node? p = some n → isValidNode (reviewSymTri g) n = true := by
  obtain ⟨h, he⟩ := reviewSymTri_eq_reviewSym g
  rw [he] at hv ⊢
  exact fun p n hn => reviewSym_node_valid h hv p n hn

/-- **Self-ownership for the joined machine** — the `selfown` field, from
`OOS` and node validity. -/
theorem selfOwn_reviewSymTri (g : GPathM) (hv : isValid (reviewSymTri g) = true)
    (hoos : SelfOwn.OOS g) :
    ∀ p n, (reviewSymTri g).node? p = some n → 0 ≤ p.id.step →
      p.id.step < (reviewSymTri g).current_step → p ∈ n.owners := fun p n hn hl0 hl =>
  FabricAdd.self_mem_owners _ (OOS_reviewSymTri g hoos) p n hn
    (node_valid_reviewSymTri g hv p n hn) hl0 hl

/-- **`CoherentSons` for the joined machine.** -/
theorem CoherentSons_reviewSymTri (g : GPathM) (hv : isValid (reviewSymTri g) = true) :
    ∀ p n, (reviewSymTri g).node? p = some n → 0 ≤ p.id.step →
      p.id.step < (reviewSymTri g).current_step - 1 →
      intersectOwners n.owners (unionOwnersOf (reviewSymTri g) n.sons) = n.owners := by
  obtain ⟨h, he⟩ := reviewSymTri_eq_reviewSym g
  rw [he] at hv ⊢
  exact CoherentSons_reviewSym h hv

-- ============================================================
-- The shape of the graph: the seven structural fields
-- ============================================================

/-! The fields v90 left open say nothing about owners — they are facts about
the **shape** of the graph, and the project already has each of them as a named
property: `Parents.PBelow` (a parent sits one step below), `Parents.PN` (and is
a node), `Parents.NotRoot` (a node above step 0 has a parent id), `Sons.SAbove`,
`Sons.SN`, `Sons.PMS` (a son's parent table holds its parent back), and
`isValidNode` itself for *having* a parent and a son.

Two of them come free from `pruned_reviewSymTri`. The other four need their
chains carried through the symmetric review, and the chains only differ from
the originals by the mirror step — which is a **relabelling of the node list
that keeps ids, parents and sons**, exactly like the triangle sweep. So one
combinator serves both, and each property costs four short lemmas. -/

private theorem symMap_id' (d : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (symMap d id m).id = m.id := by unfold symMap; split <;> rfl

private theorem symMap_parents (d : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (symMap d id m).parents = m.parents := by unfold symMap; split <;> rfl

private theorem symMap_sons (d : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (symMap d id m).sons = m.sons := by unfold symMap; split <;> rfl

/-- What a property has to survive to survive the whole symmetric review with
the triangle: a link-preserving relabelling of the nodes (the mirror step and
the triangle sweep), the owners intersection, the unlink, and the drop. -/
structure LinkStable (P : GPathM → Prop) : Prop where
  map : ∀ (g : GPathM) (F : PNodeM → PNodeM), (∀ n, (F n).id = n.id) →
    (∀ n, (F n).parents = n.parents) → (∀ n, (F n).sons = n.sons) → P g →
    P { g with nodes := g.nodes.map F }
  upd : ∀ (g : GPathM) (id : PathNodeId) (b : List PathNodeId), P g →
    P (updateAt g id (fun n => { n with owners := intersectOwners n.owners b }))
  unl : ∀ (g : GPathM) (id : PathNodeId), P g → P (unlinkIncompatible g id)
  rem : ∀ (g : GPathM) (id : PathNodeId), P g → P (removeNode g id)

namespace LinkStable

variable {P : GPathM → Prop}

theorem symmetrize' (hs : LinkStable P) (g : GPathM) (id : PathNodeId) (h : P g) :
    P (symmetrize g id) := by
  unfold symmetrize
  split
  · exact h
  · next d _ =>
    exact hs.map g (symMap d id) (symMap_id' d id) (symMap_parents d id)
      (symMap_sons d id) h

theorem triClean' (hs : LinkStable P) (g : GPathM) (h : P g) : P (triClean g) :=
  hs.map g (triMap g) (triMap_id g) (triMap_parents g) (triMap_sons g) h

theorem reviewNodeSym' (hs : LinkStable P) (nb : PNodeM → List PathNodeId) (id : PathNodeId)
    (g : GPathM) (h : P g) : P (reviewNodeSym g nb id) := by
  simp only [reviewNodeSym]
  split
  · exact h
  · next d _ =>
    split
    · have h₃ := hs.unl _ id (hs.symmetrize' _ id (hs.upd g id (unionOwnersOf g (nb d)) h))
      split
      · exact h₃
      · exact hs.rem _ id h₃
    · exact hs.rem g id h

theorem cleanInvalidGoSym' (hs : LinkStable P) (ids : List PathNodeId) :
    ∀ g : GPathM, P g → P (cleanInvalidGoSym g ids) := by
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGoSym]
    split
    · exact ih g h
    · next d _ =>
      have h₃ := hs.unl _ id (hs.symmetrize' _ id (hs.upd g id g.gowners h))
      split
      · exact ih _ h₃
      · exact ih _ (hs.rem _ id h₃)

theorem cleanInvalidSym' (hs : LinkStable P) (g : GPathM) (h : P g) : P (cleanInvalidSym g) :=
  hs.cleanInvalidGoSym' _ g h

theorem foldl' (_hs : LinkStable P) {β : Type} (f : GPathM → β → GPathM)
    (hf : ∀ g b, P g → P (f g b)) : ∀ (l : List β) (g : GPathM), P g → P (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons b bs ih => intro g h; simp only [List.foldl_cons]; exact ih _ (hf g b h)

theorem reviewLineSym' (hs : LinkStable P) (nb : PNodeM → List PathNodeId) (k : Int)
    (g : GPathM) (h : P g) : P (reviewLineSym g nb k) :=
  hs.foldl' (fun g id => reviewNodeSym g nb id) (fun g id => hs.reviewNodeSym' nb id g) _ g h

theorem reviewStepsSym' (hs : LinkStable P) (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, P g → P (reviewStepsSym g nb ks) := by
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    simp only [reviewStepsSym]
    split
    · exact ih _ (hs.reviewLineSym' nb k g h)
    · exact h

theorem reviewPassSym' (hs : LinkStable P) (g : GPathM) (h : P g) : P (reviewPassSym g) := by
  simp only [reviewPassSym, reviewSonsSym, reviewParentsSym]
  exact hs.reviewStepsSym' _ _ _ (hs.reviewStepsSym' _ _ _ (hs.cleanInvalidSym' g h))

theorem reviewFuelSym' (hs : LinkStable P) : ∀ (fuel : Nat) (g : GPathM),
    P g → P (reviewFuelSym fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewFuelSym]
    split
    · split
      · exact ih _ (hs.reviewPassSym' g h)
      · exact hs.reviewPassSym' g h
    · exact h

theorem reviewSym' (hs : LinkStable P) (g : GPathM) (h : P g) : P (reviewSym g) :=
  hs.reviewFuelSym' _ g h

theorem reviewSymTriFuel' (hs : LinkStable P) : ∀ (fuel : Nat) (g : GPathM),
    P g → P (reviewSymTriFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewSymTriFuel]
    split
    · split
      · exact ih _ (hs.triClean' _ (hs.reviewSym' g h))
      · exact hs.reviewSym' g h
    · exact hs.reviewSym' g h

/-- **Anything link-stable survives the joined machine.** -/
theorem reviewSymTri' (hs : LinkStable P) (g : GPathM) (h : P g) : P (reviewSymTri g) :=
  hs.reviewSymTriFuel' _ g h

end LinkStable

-- ------------------------------------------------------------
-- The four properties that need the combinator
-- ------------------------------------------------------------

theorem linkStable_PN : LinkStable Parents.PN where
  map := by
    intro g F hid hpar _ h n' hn' p hp
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
    rw [← hEq, hpar] at hp
    obtain ⟨m, hm, hmid⟩ := h n hn p hp
    exact ⟨F m, List.mem_map_of_mem hm, by rw [hid]; exact hmid⟩
  upd := fun g id b h => Parents.PN_updateAt g id _ (fun _ => rfl) (fun _ => rfl) h
  unl := fun g id h => Parents.PN_unlinkIncompatible g id h
  rem := fun g id h => Parents.PN_removeNode g id h

theorem linkStable_SN : LinkStable Sons.SN where
  map := by
    intro g F hid _ hson h n' hn' s hs
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
    rw [← hEq, hson] at hs
    obtain ⟨m, hm, hmid⟩ := h n hn s hs
    exact ⟨F m, List.mem_map_of_mem hm, by rw [hid]; exact hmid⟩
  upd := fun g id b h => Sons.SN_updateAt g id _ (fun _ => rfl) (fun _ => rfl) h
  unl := fun g id h => Sons.SN_unlinkIncompatible g id h
  rem := fun g id h => Sons.SN_removeNode g id h

theorem linkStable_PMS : LinkStable Sons.PMS where
  map := by
    intro g F hid hpar hson h n' hn' s hs m' hm' hmid
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
    obtain ⟨m, hm, hmEq⟩ := List.mem_map.mp hm'
    rw [← hEq, hson] at hs
    rw [← hmEq, hid] at hmid
    rw [← hEq, hid, ← hmEq, hpar]
    exact h n hn s hs m hm hmid
  upd := fun g id b h => Sons.PMS_updateAt g id _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) h
  unl := fun g id h => Sons.PMS_unlinkIncompatible g id h
  rem := fun g id h => Sons.PMS_removeNode g id h

theorem linkStable_GN : LinkStable GownersNodes.GN where
  map := by
    intro g F hid _ _ h q hq
    obtain ⟨n, hn, hnid⟩ := h q hq
    exact ⟨F n, List.mem_map_of_mem hn, by rw [hid]; exact hnid⟩
  upd := fun g id b h => GownersNodes.GN_updateAt g id _ (fun _ => rfl) h
  unl := fun g id h => GownersNodes.GN_unlinkIncompatible g id h
  rem := fun g id h => GownersNodes.GN_removeNode g id h

theorem linkStable_SAbove : LinkStable Sons.SAbove where
  map := by
    intro g F hid _ hson h n' hn' s hs
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
    rw [← hEq, hson] at hs
    rw [← hEq, hid]
    exact h n hn s hs
  upd := fun g id b h => Sons.SAbove_owners_updateAt g id b h
  unl := fun g id h => Sons.SAbove_unlinkIncompatible g id h
  rem := fun g id h => Sons.SAbove_removeNode g id h

-- ------------------------------------------------------------
-- `isValidNode` gives the two "there is one" fields
-- ------------------------------------------------------------

theorem have_parents_of_isValidNode (g : GPathM) (n : PNodeM) (h : isValidNode g n = true)
    (hroot : n.id.parent_id.isNone = false) : n.parents ≠ [] := by
  intro hnil
  simp only [isValidNode, hroot, hnil] at h
  split at h <;> simp_all

theorem have_sons_of_isValidNode (g : GPathM) (n : PNodeM) (h : isValidNode g n = true)
    (hlast : (n.id.id.step == g.current_step - 1) = false) : n.sons ≠ [] := by
  intro hnil
  simp only [isValidNode, hlast, hnil] at h
  split at h <;> simp_all

-- ============================================================
-- `TableCtx`, complete, for the joined machine
-- ============================================================

/-- **All eleven fields at once.** Given the invariants the construction
already carries — `OOS`, symmetry, and the six shape properties — a state the
joined machine leaves valid satisfies `TableCtx` entire.

With `Fabric_whole` (v88) that says, of a concrete machine and not of a
hypothesis: **at a valid fixpoint of the symmetric review with the triangle,
the state is a fabric — all nine clauses.** -/
theorem TableCtx_reviewSymTri (g : GPathM) (hv : isValid (reviewSymTri g) = true)
    (hoos : SelfOwn.OOS g) (hsym : Threaded.OwnSymmetric g)
    (hpn : Parents.PN g) (hpb : Parents.PBelow g) (hnr : Parents.NotRoot g)
    (hsn : Sons.SN g) (hsa : Sons.SAbove g) (hpms : Sons.PMS g) :
    FabricAdd.TableCtx (reviewSymTri g) := by
  have G := reviewSymTri g
  have hpr := pruned_reviewSymTri g
  have hPN : Parents.PN (reviewSymTri g) := linkStable_PN.reviewSymTri' g hpn
  have hSN : Sons.SN (reviewSymTri g) := linkStable_SN.reviewSymTri' g hsn
  have hSA : Sons.SAbove (reviewSymTri g) := linkStable_SAbove.reviewSymTri' g hsa
  have hPMS : Sons.PMS (reviewSymTri g) := linkStable_PMS.reviewSymTri' g hpms
  have hPB : Parents.PBelow (reviewSymTri g) := Parents.PBelow_of_pruned hpr hpb
  have hNR : Parents.NotRoot (reviewSymTri g) := Parents.NotRoot_of_pruned hpr hnr
  have hval := node_valid_reviewSymTri g hv
  refine { oos := OOS_reviewSymTri g hoos
           coh := CoherentParents_reviewSymTri g hv
           sym := OwnSymmetric_reviewSymTri g hsym
           tri := TriProp_reviewSymTri g hv
           selfown := selfOwn_reviewSymTri g hv hoos
           cohSons := CoherentSons_reviewSymTri g hv
           level := ?_, parnode := ?_, hasparent := ?_
           sonlevel := ?_, sonnode := ?_, hasson := ?_, smp := ?_ }
  · intro p n hn c hc
    have hid : n.id = p := node?_id_eq _ p n hn
    have := hPB n (List.mem_of_find?_eq_some hn) c hc
    rw [hid] at this; exact this
  · intro p n hn c hc
    exact (GownersNodes.hasNode_iff _ c).mp (hPN n (List.mem_of_find?_eq_some hn) c hc)
  · intro p n hn hp0
    have hid : n.id = p := node?_id_eq _ p n hn
    have hne : n.id.parent_id ≠ none :=
      hNR n (List.mem_of_find?_eq_some hn) (by rw [hid]; omega)
    have hroot : n.id.parent_id.isNone = false := by
      cases hpi : n.id.parent_id with
      | none => exact absurd hpi hne
      | some _ => rfl
    exact have_parents_of_isValidNode _ n (hval p n hn) hroot
  · intro p n hn c hc
    have hid : n.id = p := node?_id_eq _ p n hn
    have := hSA n (List.mem_of_find?_eq_some hn) c hc
    rw [hid] at this; exact this
  · intro p n hn c hc
    exact (GownersNodes.hasNode_iff _ c).mp (hSN n (List.mem_of_find?_eq_some hn) c hc)
  · intro p n hn htop
    have hid : n.id = p := node?_id_eq _ p n hn
    refine have_sons_of_isValidNode _ n (hval p n hn) ?_
    refine beq_eq_false_of_ne _ _ ?_
    rw [hid]; omega
  · intro p n c m hn hm hc
    have hid : n.id = p := node?_id_eq _ p n hn
    have hmid : m.id = c := node?_id_eq _ c m hm
    have := hPMS n (List.mem_of_find?_eq_some hn) c hc m (List.mem_of_find?_eq_some hm) hmid
    rw [hid] at this; exact this

/-- **And so the state is a fabric, entire.** `Fabric_whole` instantiated on
the joined machine: the members are the nodes in range, the tables are their
own owners, and every one of the nine clauses is a theorem. -/
theorem Fabric_whole_reviewSymTri (g : GPathM) (hv : isValid (reviewSymTri g) = true)
    (hoos : SelfOwn.OOS g) (hsym : Threaded.OwnSymmetric g)
    (hpn : Parents.PN g) (hpb : Parents.PBelow g) (hnr : Parents.NotRoot g)
    (hsn : Sons.SN g) (hsa : Sons.SAbove g) (hpms : Sons.PMS g)
    (hgn : GownersNodes.GN g)
    (hrootstep : ∀ p : PathNodeId, p.parent_id ≠ none → 1 ≤ p.id.step) :
    Fabric.Fabric (reviewSymTri g)
      (fun p => ((reviewSymTri g).node? p).isSome = true ∧ 0 ≤ p.id.step ∧
                p.id.step < (reviewSymTri g).current_step)
      (fun p v => (((reviewSymTri g).node? v).isSome = true ∧ 0 ≤ v.id.step ∧
                   v.id.step < (reviewSymTri g).current_step) ∧
                  ∃ np, (reviewSymTri g).node? p = some np ∧ v ∈ np.owners) :=
  FabricAdd.Fabric_whole _
    (TableCtx_reviewSymTri g hv hoos hsym hpn hpb hnr hsn hsa hpms)
    (OwnersGlobal_reviewSymTri g hv)
    (linkStable_GN.reviewSymTri' g hgn)
    (node_valid_reviewSymTri g hv)
    hrootstep

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

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.reviewPassSym_reviewSym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reviewPassSym_reviewSym

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.OwnersGlobal_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnersGlobal_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.CoherentParents_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CoherentParents_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.CoherentSons_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CoherentSons_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.selfOwn_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selfOwn_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.linkStable_PN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linkStable_PN

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.TableCtx_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TableCtx_reviewSymTri

/-- info: 'AbsSat.GraphPath.Model.SymTriReview.Fabric_whole_reviewSymTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_whole_reviewSymTri

end AbsSat.GraphPath.Model.SymTriReview
