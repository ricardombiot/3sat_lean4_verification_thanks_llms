-- lean_project/AbsSat/GraphPath/Model/Fuel.lean
import AbsSat.GraphPath.Model.GPathM

/-!
Phase F2 of `docs/plans/espejo_gpathm_lema_L1.md`: the review loop is honest.

* **F2.a** (`measure_reviewPass_le`): one review pass never increases the
  measure — every sub-operation is a `filter`-shaped pruning. This is what
  makes the fuel loop's recursion condition (`measure g' < measure g`)
  meaningful: passes can only walk the measure downward.
* **F2.b** (`review_stable`): `measure g + 1` units of fuel always reach the
  loop's exit — giving `reviewFuel` more fuel than `review` uses changes
  nothing. So `review` *is* the fixpoint of the loop, independently of the
  fuel bookkeeping.

F2.c (the pass is the identity at the fixpoint, i.e. `reviewPass (review g)`
does not merely keep the measure but keeps the graph) is deliberately
deferred: only lemma L6 of the bridge consumes it, and it needs the
"equal-length filter is the identity" family of lemmas threaded through every
sub-operation. It is tracked in the plan (§8, fase F2) and must land before
L6 — nothing in F3-F5 depends on it.
-/

namespace AbsSat.GraphPath.Model

open AbsSat.Utils.Alias

namespace GPathM

-- ============================================================
-- Generic list arithmetic helpers
-- ============================================================

private theorem sum_map_le {α : Type} (l : List α) (f h : α → Nat)
    (hle : ∀ a ∈ l, f a ≤ h a) : (l.map f).sum ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hle a List.mem_cons_self)
      (ih (fun x hx => hle x (List.mem_cons_of_mem _ hx)))

private theorem sum_map_filter_le {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) :
    ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.filter_cons]
    split
    · simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _
    · simp only [List.map_cons, List.sum_cons]
      exact Nat.le_trans ih (Nat.le_add_left _ _)

-- ============================================================
-- Per-operation measure bounds
-- ============================================================

theorem intersectOwners_length_le (a b : List PathNodeId) :
    (intersectOwners a b).length ≤ a.length :=
  List.length_filter_le _ _

/-- Shrinking a node's owners cannot raise its weight. -/
private theorem weight_intersect_le (b : List PathNodeId) (n : PNodeM) :
    PNodeM.weight { n with owners := intersectOwners n.owners b } ≤ PNodeM.weight n := by
  simp only [PNodeM.weight]
  have h := intersectOwners_length_le n.owners b
  omega

private theorem weight_unlink_le (id : PathNodeId) (n : PNodeM) :
    PNodeM.weight
      { n with
        parents := n.parents.filter (fun p => p != id),
        sons := n.sons.filter (fun s => s != id) } ≤ PNodeM.weight n := by
  simp only [PNodeM.weight]
  have h1 := List.length_filter_le (fun p => p != id) n.parents
  have h2 := List.length_filter_le (fun s => s != id) n.sons
  omega

private theorem measure_updateAtGo_le (id : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, PNodeM.weight (f n) ≤ PNodeM.weight n) :
    ∀ ns : List PNodeM,
      ((updateAtGo id f ns).map PNodeM.weight).sum ≤ (ns.map PNodeM.weight).sum := by
  intro ns
  rw [updateAtGo, List.map_map]
  induction ns with
  | nil => simp
  | cons n rest ih =>
    simp [List.map_cons, List.sum_cons]
    have h_wt : PNodeM.weight (match n.id == id with | true => f n | false => n) ≤ PNodeM.weight n := by
      cases n.id == id
      · exact Nat.le_refl _
      · exact hf n
    exact Nat.add_le_add h_wt ih

theorem measure_updateAt_le (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, PNodeM.weight (f n) ≤ n.weight) :
    measure (updateAt g id f) ≤ measure g := by
  simp only [measure, updateAt]
  exact Nat.add_le_add_left (measure_updateAtGo_le id f hf g.nodes) _

theorem measure_removeNode_le (g : GPathM) (id : PathNodeId) :
    measure (removeNode g id) ≤ measure g := by
  simp only [measure, removeNode]
  apply Nat.add_le_add
  · exact List.length_filter_le _ _
  · rw [List.map_map]
    apply Nat.le_trans
      (sum_map_le _ _ PNodeM.weight (fun n _ => weight_unlink_le id n))
    exact sum_map_filter_le _ _ _

-- ============================================================
-- Measure bounds for the review pass
-- ============================================================

theorem measure_cleanInvalidGo_le (ids : List PathNodeId) :
    ∀ g : GPathM, measure (cleanInvalidGo g ids) ≤ measure g := by
  induction ids with
  | nil => intro g; simp [cleanInvalidGo]
  | cons id rest ih =>
    intro g
    simp only [cleanInvalidGo]
    split
    · exact ih g
    · next d _ =>
      apply Nat.le_trans (ih _)
      have h₁ :
          measure (updateAt g id
            (fun n => { n with owners := intersectOwners n.owners g.gowners })) ≤
            measure g :=
        measure_updateAt_le g id _ (weight_intersect_le g.gowners)
      split
      · exact h₁
      · exact Nat.le_trans (measure_removeNode_le _ id) h₁

theorem measure_cleanInvalid_le (g : GPathM) : measure (cleanInvalid g) ≤ measure g :=
  measure_cleanInvalidGo_le _ g

theorem measure_reviewNode_le (nb : PNodeM → List PathNodeId) (id : PathNodeId)
    (g : GPathM) : measure (reviewNode g nb id) ≤ measure g := by
  simp only [reviewNode]
  split
  · exact Nat.le_refl _
  · next d _ =>
    split
    · have h₁ :
          measure (updateAt g id
            (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) ≤
            measure g :=
        measure_updateAt_le g id _ (weight_intersect_le _)
      split
      · exact h₁
      · exact Nat.le_trans (measure_removeNode_le _ id) h₁
    · exact measure_removeNode_le g id

private theorem measure_foldl_le {β : Type} (f : GPathM → β → GPathM)
    (h : ∀ g b, measure (f g b) ≤ measure g) :
    ∀ (l : List β) (g : GPathM), measure (l.foldl f g) ≤ measure g := by
  intro l
  induction l with
  | nil => intro g; simp
  | cons b bs ih =>
    intro g
    simp only [List.foldl_cons]
    exact Nat.le_trans (ih (f g b)) (h g b)

theorem measure_reviewLine_le (nb : PNodeM → List PathNodeId) (k : Int) (g : GPathM) :
    measure (reviewLine g nb k) ≤ measure g :=
  measure_foldl_le (fun g id => reviewNode g nb id)
    (fun g id => measure_reviewNode_le nb id g) _ g

theorem measure_reviewSteps_le (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, measure (reviewSteps g nb ks) ≤ measure g := by
  induction ks with
  | nil => intro g; simp [reviewSteps]
  | cons k ks ih =>
    intro g
    simp only [reviewSteps]
    split
    · exact Nat.le_trans (ih _) (measure_reviewLine_le nb k g)
    · exact Nat.le_refl _

theorem measure_reviewParents_le (g : GPathM) : measure (reviewParents g) ≤ measure g :=
  measure_reviewSteps_le _ _ g

theorem measure_reviewSons_le (g : GPathM) : measure (reviewSons g) ≤ measure g :=
  measure_reviewSteps_le _ _ g

/-- **F2.a** — one review pass never increases the measure. -/
theorem measure_reviewPass_le (g : GPathM) : measure (reviewPass g) ≤ measure g := by
  simp only [reviewPass]
  exact Nat.le_trans (measure_reviewSons_le _)
    (Nat.le_trans (measure_reviewParents_le _) (measure_cleanInvalid_le g))

-- ============================================================
-- F2.b — fuel sufficiency
-- ============================================================

private theorem reviewFuel_sufficient :
    ∀ (k fuel : Nat) (g : GPathM), measure g < k → measure g + 1 ≤ fuel →
      reviewFuel fuel g = reviewFuel (measure g + 1) g := by
  intro k
  induction k with
  | zero => intro fuel g hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    intro fuel g hk hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [reviewFuel]
    split
    · split
      · next hdec =>
        have hm' : measure (reviewPass g) < measure g := hdec
        rw [ih f (reviewPass g) (by omega) (by omega),
            ih (measure g) (reviewPass g) (by omega) (by omega)]
      · rfl
    · rfl

/-- **F2.b** — any fuel at or above `measure g + 1` computes `review g`: the
loop has genuinely reached its exit condition within that budget, so `review`
is the loop's fixpoint regardless of fuel accounting. -/
theorem review_stable (g : GPathM) (fuel : Nat) (h : measure g + 1 ≤ fuel) :
    reviewFuel fuel g = review g :=
  reviewFuel_sufficient (measure g + 1) fuel g (Nat.lt_succ_self _) h

end GPathM

end AbsSat.GraphPath.Model
