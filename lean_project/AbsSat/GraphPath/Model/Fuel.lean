-- lean_project/AbsSat/GraphPath/Model/Fuel.lean
import AbsSat.GraphPath.Model.GPathM
import AbsSat.GraphPath.Model.Pruned

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

* **F2.c** (`reviewPass_review`): the pass is the *identity* at the fixpoint,
  not merely measure-preserving. This is the "equal-length filter is the
  identity" family threaded through every sub-operation: each one only ever
  filters, so preserving the measure forces every filter to have kept its
  whole input and makes every `removeNode` branch unreachable.
* **F2.c, per-node** (`review_node_valid`, `review_owners_coherent_parents`,
  `review_owners_coherent_sons`): the postcondition L6 will actually pull on —
  after `review`, every node the machine can look up passes `is_valid_node`,
  and its owners are already coherent with the union of its parents' and of
  its sons' owners. Read off the fixpoint by noting that every step of the
  walk was itself the identity, so each visited node must have taken the
  valid branch.

All three are axiom-free; the `#guard_msgs` pins at the end of this file fail
the build if any project axiom ever enters the closure of F2.a/F2.b/F2.c.
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

private theorem weight_relinkBy_le (ow : List PathNodeId) (m : PNodeM) :
    PNodeM.weight { m with parents := m.parents.filter (fun p => ow.contains p),
                           sons := m.sons.filter (fun s => ow.contains s) }
      ≤ PNodeM.weight m := by
  have h1 := List.length_filter_le (fun p => ow.contains p) m.parents
  have h2 := List.length_filter_le (fun p => ow.contains p) m.sons
  have hw : PNodeM.weight { m with parents := m.parents.filter (fun p => ow.contains p),
                                   sons := m.sons.filter (fun s => ow.contains s) }
      = 1 + (m.parents.filter (fun p => ow.contains p)).length
          + (m.sons.filter (fun p => ow.contains p)).length + m.owners.length := rfl
  have hw2 : PNodeM.weight m = 1 + m.parents.length + m.sons.length + m.owners.length := rfl
  rw [hw, hw2]
  omega

private theorem weight_relinkSelf_le (n : PNodeM) :
    PNodeM.weight (relinkSelf n) ≤ PNodeM.weight n := weight_relinkBy_le n.owners n

private theorem weight_unlinkMap_le (n : PNodeM) (id : PathNodeId) (m : PNodeM) :
    PNodeM.weight (unlinkMap n id m) ≤ PNodeM.weight m := by
  unfold GPathM.unlinkMap
  split
  · exact weight_relinkBy_le n.owners m
  · split
    · exact Nat.le_refl _
    · exact weight_unlink_le id m

/-- Unlinking incompatible neighbours cannot raise the measure. -/
theorem measure_unlinkIncompatible_le (g : GPathM) (id : PathNodeId) :
    measure (unlinkIncompatible g id) ≤ measure g := by
  unfold GPathM.unlinkIncompatible
  split
  · exact Nat.le_refl _
  · next n _ =>
    simp only [measure]
    refine Nat.add_le_add (Nat.le_refl _) ?_
    rw [List.map_map]
    exact sum_map_le _ _ PNodeM.weight (fun m _ => weight_unlinkMap_le n id m)

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
      have h₂ := Nat.le_trans (measure_unlinkIncompatible_le _ id) h₁
      split
      · exact h₂
      · exact Nat.le_trans (measure_removeNode_le _ id) h₂

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
      have h₂ := Nat.le_trans (measure_unlinkIncompatible_le _ id) h₁
      split
      · exact h₂
      · exact Nat.le_trans (measure_removeNode_le _ id) h₂
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

-- ============================================================
-- F2.c — generic: a length-preserving filter is the identity
-- ============================================================

private theorem filter_eq_self_of_length {α : Type} (l : List α) (p : α → Bool)
    (h : (l.filter p).length = l.length) : l.filter p = l :=
  List.filter_eq_self.mpr (List.length_filter_eq_length_iff.mp h)

/-- Pointwise saturation: if `f ≤ h` on every element and the two sums agree,
then `f = h` on every element. -/
private theorem sum_map_eq_pointwise {α : Type} (l : List α) (f h : α → Nat)
    (hle : ∀ a ∈ l, f a ≤ h a) (hsum : (l.map f).sum = (l.map h).sum) :
    ∀ a ∈ l, f a = h a := by
  induction l with
  | nil => intro a ha; exact absurd ha (List.not_mem_nil)
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons] at hsum
    have hhead : f a ≤ h a := hle a List.mem_cons_self
    have htail : ∀ x ∈ as, f x ≤ h x := fun x hx => hle x (List.mem_cons_of_mem _ hx)
    have hsums : (as.map f).sum ≤ (as.map h).sum := sum_map_le as f h htail
    have hfa : f a = h a := by omega
    have htails : (as.map f).sum = (as.map h).sum := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hfa
    · exact ih htail htails x hx'

private theorem map_eq_self_of {α : Type} (l : List α) (f : α → α)
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

-- ============================================================
-- Weight level: a weight-preserving owners intersection is the identity
-- ============================================================

private theorem intersect_eq_self_of_weight (b : List PathNodeId) (n : PNodeM)
    (h : PNodeM.weight { n with owners := intersectOwners n.owners b } = PNodeM.weight n) :
    { n with owners := intersectOwners n.owners b } = n := by
  have hlen : (intersectOwners n.owners b).length = n.owners.length := by
    simp only [PNodeM.weight] at h
    omega
  have : intersectOwners n.owners b = n.owners :=
    filter_eq_self_of_length _ _ hlen
  rw [this]


private theorem relinkBy_eq_self_of_weight (ow : List PathNodeId) (m : PNodeM)
    (h : PNodeM.weight { m with parents := m.parents.filter (fun p => ow.contains p),
                                sons := m.sons.filter (fun s => ow.contains s) }
        = PNodeM.weight m) :
    { m with parents := m.parents.filter (fun p => ow.contains p),
             sons := m.sons.filter (fun s => ow.contains s) } = m := by
  have h1 := List.length_filter_le (fun p => ow.contains p) m.parents
  have h2 := List.length_filter_le (fun p => ow.contains p) m.sons
  have hw : PNodeM.weight { m with parents := m.parents.filter (fun p => ow.contains p),
                                   sons := m.sons.filter (fun s => ow.contains s) }
      = 1 + (m.parents.filter (fun p => ow.contains p)).length
          + (m.sons.filter (fun p => ow.contains p)).length + m.owners.length := rfl
  have hw2 : PNodeM.weight m = 1 + m.parents.length + m.sons.length + m.owners.length := rfl
  rw [hw, hw2] at h
  have hp : (m.parents.filter (fun p => ow.contains p)).length = m.parents.length := by omega
  have hs : (m.sons.filter (fun p => ow.contains p)).length = m.sons.length := by omega
  show { m with parents := m.parents.filter (fun p => ow.contains p),
                sons := m.sons.filter (fun p => ow.contains p) } = m
  rw [filter_eq_self_of_length _ _ hp, filter_eq_self_of_length _ _ hs]

private theorem relinkSelf_eq_self_of_weight (n : PNodeM)
    (h : PNodeM.weight (relinkSelf n) = PNodeM.weight n) : relinkSelf n = n :=
  relinkBy_eq_self_of_weight n.owners n h

private theorem unlink_eq_self_of_weight (id : PathNodeId) (m : PNodeM)
    (h : PNodeM.weight { m with parents := m.parents.filter (fun p => p != id),
                                sons := m.sons.filter (fun s => s != id) }
        = PNodeM.weight m) :
    { m with parents := m.parents.filter (fun p => p != id),
             sons := m.sons.filter (fun s => s != id) } = m := by
  have h1 := List.length_filter_le (fun p => p != id) m.parents
  have h2 := List.length_filter_le (fun p => p != id) m.sons
  have hw : PNodeM.weight { m with parents := m.parents.filter (fun p => p != id),
                                   sons := m.sons.filter (fun s => s != id) }
      = 1 + (m.parents.filter (fun p => p != id)).length
          + (m.sons.filter (fun p => p != id)).length + m.owners.length := rfl
  have hw2 : PNodeM.weight m = 1 + m.parents.length + m.sons.length + m.owners.length := rfl
  rw [hw, hw2] at h
  have hp : (m.parents.filter (fun p => p != id)).length = m.parents.length := by omega
  have hs : (m.sons.filter (fun p => p != id)).length = m.sons.length := by omega
  show { m with parents := m.parents.filter (fun p => p != id),
                sons := m.sons.filter (fun p => p != id) } = m
  rw [filter_eq_self_of_length _ _ hp, filter_eq_self_of_length _ _ hs]

private theorem unlinkMap_eq_self_of_weight (n : PNodeM) (id : PathNodeId) (m : PNodeM)
    (h : PNodeM.weight (unlinkMap n id m) = PNodeM.weight m) : unlinkMap n id m = m := by
  unfold GPathM.unlinkMap at h ⊢
  split at h
  · next hc => rw [if_pos hc]; exact relinkBy_eq_self_of_weight n.owners m h
  · next hc =>
    rw [if_neg hc]
    split at h
    · next hc2 => rw [if_pos hc2]
    · next hc2 => rw [if_neg hc2]; exact unlink_eq_self_of_weight id m h

/-- At the fixpoint the unlink is the identity: it only filters, so preserving
the measure means it removed nothing. -/
theorem unlinkIncompatible_eq_self (g : GPathM) (id : PathNodeId)
    (h : measure (unlinkIncompatible g id) = measure g) : unlinkIncompatible g id = g := by
  cases hn : g.node? id with
  | none => simp only [GPathM.unlinkIncompatible, hn]
  | some n =>
    have hshape : unlinkIncompatible g id = { g with nodes := g.nodes.map (unlinkMap n id) } := by
      simp only [GPathM.unlinkIncompatible, hn]
    rw [hshape] at h ⊢
    have hsum : (g.nodes.map (PNodeM.weight ∘ unlinkMap n id)).sum
        = (g.nodes.map PNodeM.weight).sum := by
      simp only [measure] at h
      rw [List.map_map] at h
      omega
    have hpt := sum_map_eq_pointwise g.nodes (PNodeM.weight ∘ unlinkMap n id) PNodeM.weight
      (fun m _ => weight_unlinkMap_le n id m) hsum
    have hmap : g.nodes.map (unlinkMap n id) = g.nodes :=
      map_eq_self_of _ _ (fun m hm => unlinkMap_eq_self_of_weight n id m (hpt m hm))
    rw [hmap]

private theorem map_pointwise_of_eq {α : Type} (l : List α) (f : α → α)
    (h : l.map f = l) : ∀ a ∈ l, f a = a := by
  induction l with
  | nil => intro a ha; exact absurd ha List.not_mem_nil
  | cons a as ih =>
    simp only [List.map_cons, List.cons.injEq] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h.1
    · exact ih h.2 x hx'

theorem unlinkIncompatible_pointwise (g : GPathM) (id : PathNodeId) (n : PNodeM)
    (hn : g.node? id = some n) (h : unlinkIncompatible g id = g)
    (m : PNodeM) (hm : m ∈ g.nodes) : unlinkMap n id m = m := by
  have hshape : unlinkIncompatible g id = { g with nodes := g.nodes.map (unlinkMap n id) } := by
    simp only [GPathM.unlinkIncompatible, hn]
  rw [hshape] at h
  have hmap : g.nodes.map (unlinkMap n id) = g.nodes := congrArg GPathM.nodes h
  exact map_pointwise_of_eq _ _ hmap m hm

/-- **The owners/parents bridge, at the fixpoint.** A node's links are already
inside its owners: the unlink had nothing to do. -/
theorem relinkSelf_eq_self_of_fixed (g : GPathM) (id : PathNodeId) (d : PNodeM)
    (hd : g.node? id = some d) (h : unlinkIncompatible g id = g) : relinkSelf d = d := by
  have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq g id d hd
  have hpt := unlinkIncompatible_pointwise g id d hd h d hd_mem
  unfold GPathM.unlinkMap at hpt
  rw [if_pos (by rw [hd_id]; exact beq_iff_eq.mpr rfl)] at hpt
  exact hpt

-- ============================================================
-- updateAt: weight-preserving update is the identity
-- ============================================================

private theorem updateAtGo_eq_self (id : PathNodeId) (f : PNodeM → PNodeM)
    (hle : ∀ n, PNodeM.weight (f n) ≤ PNodeM.weight n)
    (hid : ∀ n, PNodeM.weight (f n) = PNodeM.weight n → f n = n)
    (ns : List PNodeM)
    (hsum : ((updateAtGo id f ns).map PNodeM.weight).sum = (ns.map PNodeM.weight).sum) :
    updateAtGo id f ns = ns := by
  rw [updateAtGo] at hsum ⊢
  rw [List.map_map] at hsum
  apply map_eq_self_of
  have hle' : ∀ a ∈ ns,
      (PNodeM.weight ∘ (fun n => match n.id == id with | true => f n | false => n)) a
        ≤ PNodeM.weight a := by
    intro a _
    simp only [Function.comp]
    cases a.id == id
    · exact Nat.le_refl _
    · exact hle a
  have hpt := sum_map_eq_pointwise ns _ PNodeM.weight hle' hsum
  intro a ha
  have := hpt a ha
  simp only [Function.comp] at this ⊢
  cases h : a.id == id
  · rfl
  · rw [h] at this; exact hid a this

theorem updateAt_eq_self (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hle : ∀ n, PNodeM.weight (f n) ≤ PNodeM.weight n)
    (hid : ∀ n, PNodeM.weight (f n) = PNodeM.weight n → f n = n)
    (h : measure (updateAt g id f) = measure g) : updateAt g id f = g := by
  have hsum : ((updateAtGo id f g.nodes).map PNodeM.weight).sum
      = (g.nodes.map PNodeM.weight).sum := by
    simp only [measure, updateAt] at h
    omega
  simp only [updateAt, updateAtGo_eq_self id f hle hid g.nodes hsum]

-- ============================================================
-- removeNode strictly shrinks the measure when the node is there
-- ============================================================

private theorem sum_map_filter_lt {α : Type} (l : List α) (p : α → Bool) (f : α → Nat)
    (a : α) (ha : a ∈ l) (hp : p a = false) (hf : 0 < f a) :
    ((l.filter p).map f).sum < (l.map f).sum := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons x xs ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [hp]
      simp only [Bool.false_eq_true, if_false]
      have := sum_map_filter_le xs p f
      omega
    · split
      · simp only [List.map_cons, List.sum_cons]
        have := ih ha'
        omega
      · have := ih ha'
        have hle := sum_map_filter_le xs p f
        omega

theorem measure_removeNode_lt (g : GPathM) (id : PathNodeId) (d : PNodeM)
    (hmem : d ∈ g.nodes) (hid : d.id = id) : measure (removeNode g id) < measure g := by
  have hp : (d.id != id) = false := by simp [hid]
  have hw : 0 < PNodeM.weight d := by simp only [PNodeM.weight]; omega
  have hlt : (((g.nodes.filter (fun n => n.id != id))).map PNodeM.weight).sum
      < (g.nodes.map PNodeM.weight).sum :=
    sum_map_filter_lt g.nodes _ PNodeM.weight d hmem hp hw
  have hunlink :
      (((g.nodes.filter (fun n => n.id != id)).map (fun n =>
          { n with
            parents := n.parents.filter (fun p => p != id),
            sons := n.sons.filter (fun s => s != id) })).map PNodeM.weight).sum
        ≤ ((g.nodes.filter (fun n => n.id != id)).map PNodeM.weight).sum := by
    rw [List.map_map]
    exact sum_map_le _ _ PNodeM.weight (fun n _ => weight_unlink_le id n)
  have hgow : (g.gowners.filter (fun q => q != id)).length ≤ g.gowners.length :=
    List.length_filter_le _ _
  simp only [measure, removeNode]
  omega

/-- An id-preserving update leaves some node carrying the id behind, so the
`removeNode` branch of a review step always has something to remove. -/
private theorem exists_mem_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, (f n).id = n.id) (d : PNodeM) (hd : d ∈ g.nodes) :
    ∃ n ∈ (updateAt g id f).nodes, n.id = d.id := by
  refine ⟨(fun n => match n.id == id with | true => f n | false => n) d, ?_, ?_⟩
  · simp only [updateAt, updateAtGo]
    exact List.mem_map_of_mem hd
  · cases h : d.id == id <;> simp [h, hf]

-- ============================================================
-- F2.c: the shared "intersect owners, drop if that broke the node" tail
-- ============================================================

/-- The body both `cleanInvalidGo` and `reviewNode` end with: intersect the
node's owners against `b`, then physically drop the node if that left it
invalid. Factoring it out lets one lemma serve both passes. -/
def intersectOrDrop (g : GPathM) (id : PathNodeId) (b : List PathNodeId) (d : PNodeM) : GPathM :=
  if isValidNode
      (unlinkIncompatible
        (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id)
      (relink (intersectOwners d.owners b) d) then
    unlinkIncompatible
      (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id
  else
    removeNode (unlinkIncompatible
      (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id) id

theorem measure_intersectOrDrop_le (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (d : PNodeM) : measure (intersectOrDrop g id b d) ≤ measure g := by
  have hupd : measure (updateAt g id
      (fun n => { n with owners := intersectOwners n.owners b })) ≤ measure g :=
    measure_updateAt_le g id _ (weight_intersect_le b)
  have hupd2 := Nat.le_trans (measure_unlinkIncompatible_le _ id) hupd
  unfold intersectOrDrop
  split
  · exact hupd2
  · exact Nat.le_trans (measure_removeNode_le _ id) hupd2

/-- At the fixpoint the tail is the identity: the intersection kept every
owner, and the drop branch is unreachable because removing a node that is
actually there strictly shrinks the measure. -/
theorem intersectOrDrop_eq_self (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (d : PNodeM) (hd_mem : d ∈ g.nodes) (hd_id : d.id = id)
    (h : measure (intersectOrDrop g id b d) = measure g) : intersectOrDrop g id b d = g := by
  have hle_f : ∀ n, PNodeM.weight { n with owners := intersectOwners n.owners b }
      ≤ PNodeM.weight n := weight_intersect_le b
  have hid_f : ∀ n, PNodeM.weight { n with owners := intersectOwners n.owners b }
      = PNodeM.weight n → { n with owners := intersectOwners n.owners b } = n :=
    fun n => intersect_eq_self_of_weight b n
  have hupd_le : measure (updateAt g id
      (fun n => { n with owners := intersectOwners n.owners b })) ≤ measure g :=
    measure_updateAt_le g id _ hle_f
  have hunl_le := measure_unlinkIncompatible_le
    (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id
  obtain ⟨n, hn, hn_id⟩ :
      ∃ n ∈ (unlinkIncompatible (updateAt g id
        (fun n => { n with owners := intersectOwners n.owners b })) id).nodes, n.id = id := by
    obtain ⟨n, hn, hn_id⟩ :=
      exists_mem_updateAt g id (fun n => { n with owners := intersectOwners n.owners b })
        (fun _ => rfl) d hd_mem
    have hid' : n.id = id := by rw [hn_id]; exact hd_id
    unfold GPathM.unlinkIncompatible
    split
    · exact ⟨n, hn, hid'⟩
    · next n₀ _ =>
      exact ⟨unlinkMap n₀ id n, List.mem_map_of_mem hn, by rw [unlinkMap_id]; exact hid'⟩
  have hlt := measure_removeNode_lt _ id n hn hn_id
  unfold intersectOrDrop at h ⊢
  split at h
  · next hv =>
    rw [if_pos hv]
    have h1 : measure (updateAt g id
        (fun n => { n with owners := intersectOwners n.owners b })) = measure g := by omega
    have h2 : updateAt g id (fun n => { n with owners := intersectOwners n.owners b }) = g :=
      updateAt_eq_self g id _ hle_f hid_f h1
    rw [h2] at h ⊢
    exact unlinkIncompatible_eq_self g id h
  · next hv =>
    rw [if_neg hv]
    exact absurd h (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt (Nat.le_trans hunl_le hupd_le)))

-- ============================================================
-- F2.c, step 1: cleanInvalid at the fixpoint
-- ============================================================

/-- One `cleanInvalidGo` step, factored out so the induction can reason about
it in isolation. `cleanInvalidGo_cons` ties it back to the definition. -/
def cleanStep (g : GPathM) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some d => intersectOrDrop g id g.gowners d

theorem cleanInvalidGo_cons (g : GPathM) (id : PathNodeId) (rest : List PathNodeId) :
    cleanInvalidGo g (id :: rest) = cleanInvalidGo (cleanStep g id) rest := by
  cases hnode : g.node? id <;> simp [cleanInvalidGo, cleanStep, intersectOrDrop, hnode]

theorem measure_cleanStep_le (g : GPathM) (id : PathNodeId) :
    measure (cleanStep g id) ≤ measure g := by
  simp only [cleanStep]
  split
  · exact Nat.le_refl _
  · exact measure_intersectOrDrop_le _ _ _ _

theorem cleanStep_eq_self (g : GPathM) (id : PathNodeId)
    (h : measure (cleanStep g id) = measure g) : cleanStep g id = g := by
  cases hnode : g.node? id with
  | none => simp [cleanStep, hnode]
  | some d =>
    simp only [cleanStep, hnode] at h ⊢
    exact intersectOrDrop_eq_self g id g.gowners d
      (List.mem_of_find?_eq_some hnode) (node?_id_eq g id d hnode) h

theorem cleanInvalidGo_eq_self (ids : List PathNodeId) :
    ∀ g : GPathM, measure (cleanInvalidGo g ids) = measure g → cleanInvalidGo g ids = g := by
  induction ids with
  | nil => intro g _; simp [cleanInvalidGo]
  | cons id rest ih =>
    intro g heq
    rw [cleanInvalidGo_cons] at heq ⊢
    have h₁ := measure_cleanStep_le g id
    have h₂ := measure_cleanInvalidGo_le rest (cleanStep g id)
    have hstep : measure (cleanStep g id) = measure g := by omega
    rw [cleanStep_eq_self g id hstep] at heq ⊢
    exact ih g heq

theorem cleanInvalid_eq_self (g : GPathM) (h : measure (cleanInvalid g) = measure g) :
    cleanInvalid g = g :=
  cleanInvalidGo_eq_self _ g h

-- ============================================================
-- F2.c, step 2: the coherence passes at the fixpoint
-- ============================================================

theorem reviewNode_eq_self (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId)
    (h : measure (reviewNode g nb id) = measure g) : reviewNode g nb id = g := by
  cases hnode : g.node? id with
  | none => simp [reviewNode, hnode]
  | some d =>
    have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hnode
    have hd_id : d.id = id := node?_id_eq g id d hnode
    have hshape : reviewNode g nb id =
        if isValidNode g d then intersectOrDrop g id (unionOwnersOf g (nb d)) d
        else removeNode g id := by
      simp [reviewNode, hnode, intersectOrDrop]
    rw [hshape] at h ⊢
    split at h
    · next hvalid =>
      rw [if_pos hvalid]
      exact intersectOrDrop_eq_self g id _ d hd_mem hd_id h
    · next hvalid =>
      -- the node was already invalid, so it is dropped: strictly smaller
      rw [if_neg hvalid]
      have hlt := measure_removeNode_lt g id d hd_mem hd_id
      exact absurd h (Nat.ne_of_lt hlt)

private theorem foldl_eq_self {β : Type} (f : GPathM → β → GPathM)
    (hle : ∀ g b, measure (f g b) ≤ measure g)
    (hid : ∀ g b, measure (f g b) = measure g → f g b = g) :
    ∀ (l : List β) (g : GPathM), measure (l.foldl f g) = measure g → l.foldl f g = g := by
  intro l
  induction l with
  | nil => intro g _; simp
  | cons b bs ih =>
    intro g heq
    simp only [List.foldl_cons] at heq ⊢
    have h₁ := hle g b
    have h₂ := measure_foldl_le f hle bs (f g b)
    have hstep : measure (f g b) = measure g := by omega
    rw [hid g b hstep] at heq ⊢
    exact ih g heq

theorem reviewLine_eq_self (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int)
    (h : measure (reviewLine g nb k) = measure g) : reviewLine g nb k = g :=
  foldl_eq_self (fun g id => reviewNode g nb id)
    (fun g id => measure_reviewNode_le nb id g)
    (fun g id => reviewNode_eq_self g nb id) _ g h

theorem reviewSteps_eq_self (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, measure (reviewSteps g nb ks) = measure g → reviewSteps g nb ks = g := by
  induction ks with
  | nil => intro g _; simp [reviewSteps]
  | cons k ks ih =>
    intro g heq
    simp only [reviewSteps] at heq ⊢
    split at heq
    · next hv =>
      rw [if_pos hv]
      have h₁ := measure_reviewLine_le nb k g
      have h₂ := measure_reviewSteps_le nb ks (reviewLine g nb k)
      have hline : measure (reviewLine g nb k) = measure g := by omega
      rw [reviewLine_eq_self g nb k hline] at heq ⊢
      exact ih g heq
    · next hv => rw [if_neg hv]

theorem reviewParents_eq_self (g : GPathM) (h : measure (reviewParents g) = measure g) :
    reviewParents g = g :=
  reviewSteps_eq_self _ _ g h

theorem reviewSons_eq_self (g : GPathM) (h : measure (reviewSons g) = measure g) :
    reviewSons g = g :=
  reviewSteps_eq_self _ _ g h

-- ============================================================
-- F2.c — the pass is the identity at the fixpoint
-- ============================================================

/-- A measure-preserving review pass changed nothing at all. This is the
"equal-length filter is the identity" thread pulled through every
sub-operation: each one only ever filters, so preserving the measure forces
every filter to have kept its whole input and every `removeNode` branch to be
unreachable. -/
theorem reviewPass_eq_self (g : GPathM) (h : measure (reviewPass g) = measure g) :
    reviewPass g = g := by
  have h₁ := measure_cleanInvalid_le g
  have h₂ := measure_reviewParents_le (cleanInvalid g)
  have h₃ := measure_reviewSons_le (reviewParents (cleanInvalid g))
  simp only [reviewPass] at h ⊢
  have hclean : measure (cleanInvalid g) = measure g := by omega
  rw [cleanInvalid_eq_self g hclean] at h ⊢
  have h₂' := measure_reviewParents_le g
  have h₃' := measure_reviewSons_le (reviewParents g)
  have hpar : measure (reviewParents g) = measure g := by omega
  rw [reviewParents_eq_self g hpar] at h ⊢
  exact reviewSons_eq_self g h

theorem reviewFuel_fixpoint : ∀ (fuel : Nat) (g : GPathM), measure g < fuel →
    isValid (reviewFuel fuel g) = true →
    reviewPass (reviewFuel fuel g) = reviewFuel fuel g := by
  intro fuel
  induction fuel with
  | zero => intro g hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro g hlt hvalid
    simp only [reviewFuel] at hvalid ⊢
    split at hvalid
    · next hv =>
      rw [if_pos hv]
      split at hvalid
      · next hdec =>
        rw [if_pos hdec]
        exact ih (reviewPass g) (by omega) hvalid
      · next hdec =>
        rw [if_neg hdec]
        have hle := measure_reviewPass_le g
        have hfix : reviewPass g = g := reviewPass_eq_self g (by omega)
        simp only [hfix]
    · next hv =>
      rw [if_neg hv]
      exact absurd hvalid hv

/-- **F2.c** — `review` really is a fixpoint of `reviewPass`, not merely a
point where the measure stopped moving. Only lemma L6 of the bridge consumes
this.

The `isValid` side condition is not an artefact: when the graph is already
invalid the loop bails out *without* running a pass, and `cleanInvalid` (which
`reviewPass` runs unconditionally) can still prune. So an invalid graph is an
exit of the loop but need not be a fixpoint of the pass. -/
theorem reviewPass_review (g : GPathM) (h : isValid (review g) = true) :
    reviewPass (review g) = review g :=
  reviewFuel_fixpoint (measure g + 1) g (Nat.lt_succ_self _) h

/-- `review` is idempotent on the graphs it leaves valid — the form L6 will
actually use. -/
theorem review_idempotent (g : GPathM) (h : isValid (review g) = true) :
    review (review g) = review g := by
  have hfix : reviewPass (review g) = review g := reviewPass_review g h
  show reviewFuel (measure (review g) + 1) (review g) = review g
  simp only [reviewFuel]
  rw [if_pos h, hfix, if_neg (by omega)]

-- ============================================================
-- F2.c, per-node form: supporting lemmas
-- ============================================================

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

/-- A fixpoint `updateAt` left every node carrying `id` untouched. -/
private theorem updateAt_pointwise (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (h : updateAt g id f = g) (d : PNodeM) (hd : d ∈ g.nodes) (hd_id : d.id = id) :
    f d = d := by
  have hmap : updateAtGo id f g.nodes = g.nodes := congrArg GPathM.nodes h
  rw [updateAtGo] at hmap
  have hpt := map_eq_self_pointwise g.nodes _ hmap d hd
  have hbeq : (d.id == id) = true := by rw [hd_id]; exact beq_self_eq_true id
  simpa [hbeq] using hpt

/-- At the fixpoint the surviving branch is the *valid* one: the owners
intersection was the identity, and the node passed `isValidNode`. -/
theorem intersectOrDrop_valid_branch (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (d : PNodeM) (hd_mem : d ∈ g.nodes) (hd_id : d.id = id)
    (h : measure (intersectOrDrop g id b d) = measure g) :
    updateAt g id (fun n => { n with owners := intersectOwners n.owners b }) = g ∧
      unlinkIncompatible g id = g ∧
      isValidNode g (relink (intersectOwners d.owners b) d) = true := by
  have hle_f : ∀ n, PNodeM.weight { n with owners := intersectOwners n.owners b }
      ≤ PNodeM.weight n := weight_intersect_le b
  have hid_f : ∀ n, PNodeM.weight { n with owners := intersectOwners n.owners b }
      = PNodeM.weight n → { n with owners := intersectOwners n.owners b } = n :=
    fun n => intersect_eq_self_of_weight b n
  have hupd_le : measure (updateAt g id
      (fun n => { n with owners := intersectOwners n.owners b })) ≤ measure g :=
    measure_updateAt_le g id _ hle_f
  have hunl_le := measure_unlinkIncompatible_le
    (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) id
  obtain ⟨n, hn, hn_id⟩ :
      ∃ n ∈ (unlinkIncompatible (updateAt g id
        (fun n => { n with owners := intersectOwners n.owners b })) id).nodes, n.id = id := by
    obtain ⟨n, hn, hn_id⟩ :=
      exists_mem_updateAt g id (fun n => { n with owners := intersectOwners n.owners b })
        (fun _ => rfl) d hd_mem
    have hid' : n.id = id := by rw [hn_id]; exact hd_id
    unfold GPathM.unlinkIncompatible
    split
    · exact ⟨n, hn, hid'⟩
    · next n₀ _ =>
      exact ⟨unlinkMap n₀ id n, List.mem_map_of_mem hn, by rw [unlinkMap_id]; exact hid'⟩
  have hlt := measure_removeNode_lt _ id n hn hn_id
  unfold intersectOrDrop at h
  split at h
  · next hv =>
    have h1 : measure (updateAt g id
        (fun n => { n with owners := intersectOwners n.owners b })) = measure g := by omega
    have hupd : updateAt g id (fun n => { n with owners := intersectOwners n.owners b }) = g :=
      updateAt_eq_self g id _ hle_f hid_f h1
    have hunl : unlinkIncompatible g id = g := by
      rw [hupd] at h; exact unlinkIncompatible_eq_self g id h
    refine ⟨hupd, hunl, ?_⟩
    rw [hupd, hunl] at hv
    exact hv
  · exact absurd h (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt (Nat.le_trans hunl_le hupd_le)))

/-- Every step of a fixpoint `cleanInvalidGo` walk was itself the identity,
and on the *original* graph — the intermediate states never moved. -/
theorem cleanInvalidGo_steps_eq_self (ids : List PathNodeId) :
    ∀ g : GPathM, measure (cleanInvalidGo g ids) = measure g →
      ∀ id ∈ ids, cleanStep g id = g := by
  induction ids with
  | nil => intro g _ id hid; exact absurd hid List.not_mem_nil
  | cons id rest ih =>
    intro g heq id' hid'
    rw [cleanInvalidGo_cons] at heq
    have h₁ := measure_cleanStep_le g id
    have h₂ := measure_cleanInvalidGo_le rest (cleanStep g id)
    have hfix : cleanStep g id = g := cleanStep_eq_self g id (by omega)
    rw [hfix] at heq
    rcases List.mem_cons.mp hid' with rfl | hid''
    · exact hfix
    · exact ih g heq id' hid''

private theorem foldl_steps_eq_self {β : Type} (f : GPathM → β → GPathM)
    (hle : ∀ g b, measure (f g b) ≤ measure g)
    (hid : ∀ g b, measure (f g b) = measure g → f g b = g) :
    ∀ (l : List β) (g : GPathM), measure (l.foldl f g) = measure g →
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

theorem reviewLine_nodes_eq_self (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int)
    (h : measure (reviewLine g nb k) = measure g) :
    ∀ id ∈ ((g.line k).map (·.id)), reviewNode g nb id = g :=
  foldl_steps_eq_self (fun g id => reviewNode g nb id)
    (fun g id => measure_reviewNode_le nb id g)
    (fun g id => reviewNode_eq_self g nb id) _ g h

theorem reviewSteps_lines_eq_self (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, isValid g = true → measure (reviewSteps g nb ks) = measure g →
      ∀ k ∈ ks, reviewLine g nb k = g := by
  induction ks with
  | nil => intro g _ _ k hk; exact absurd hk List.not_mem_nil
  | cons k ks ih =>
    intro g hvalid heq k' hk'
    simp only [reviewSteps] at heq
    rw [if_pos hvalid] at heq
    have h₁ := measure_reviewLine_le nb k g
    have h₂ := measure_reviewSteps_le nb ks (reviewLine g nb k)
    have hfix : reviewLine g nb k = g := reviewLine_eq_self g nb k (by omega)
    rw [hfix] at heq
    rcases List.mem_cons.mp hk' with rfl | hk''
    · exact hfix
    · exact ih g hvalid heq k' hk''

/-- At the fixpoint, a node reached by `cleanInvalidGo` passed `isValidNode`. -/
theorem cleanStep_node_valid (g : GPathM) (id : PathNodeId) (d : PNodeM)
    (hd : g.node? id = some d) (h : measure (cleanStep g id) = measure g) :
    isValidNode g d = true := by
  have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq g id d hd
  have hstep : measure (intersectOrDrop g id g.gowners d) = measure g := by
    simpa [cleanStep, hd] using h
  obtain ⟨hupd, hunl, hvalid⟩ := intersectOrDrop_valid_branch g id g.gowners d hd_mem hd_id hstep
  have hfix : { d with owners := intersectOwners d.owners g.gowners } = d :=
    updateAt_pointwise g id _ hupd d hd_mem hd_id
  have hrel : relink (intersectOwners d.owners g.gowners) d = d := by
    show relinkSelf { d with owners := intersectOwners d.owners g.gowners } = d
    rw [hfix]; exact relinkSelf_eq_self_of_fixed g id d hd hunl
  rwa [hrel] at hvalid

/-- At the fixpoint, a node reached by `cleanInvalidGo` had its owners already
contained in the global owners: intersecting against them was the identity. -/
theorem cleanStep_owners_fixed (g : GPathM) (id : PathNodeId) (d : PNodeM)
    (hd : g.node? id = some d) (h : measure (cleanStep g id) = measure g) :
    intersectOwners d.owners g.gowners = d.owners := by
  have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq g id d hd
  have hstep : measure (intersectOrDrop g id g.gowners d) = measure g := by
    simpa [cleanStep, hd] using h
  obtain ⟨hupd, _, _⟩ := intersectOrDrop_valid_branch g id g.gowners d hd_mem hd_id hstep
  have hfix : { d with owners := intersectOwners d.owners g.gowners } = d :=
    updateAt_pointwise g id _ hupd d hd_mem hd_id
  exact congrArg PNodeM.owners hfix

/-- At the fixpoint, a node reached by a coherence pass had its owners already
consistent with the union of its neighbours' owners: the intersection against
that union was the identity. -/
theorem reviewNode_owners_fixed (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) (d : PNodeM) (hd : g.node? id = some d)
    (h : measure (reviewNode g nb id) = measure g) :
    intersectOwners d.owners (unionOwnersOf g (nb d)) = d.owners := by
  have hd_mem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq g id d hd
  have hshape : reviewNode g nb id =
      if isValidNode g d then intersectOrDrop g id (unionOwnersOf g (nb d)) d
      else removeNode g id := by
    simp [reviewNode, hd, intersectOrDrop]
  rw [hshape] at h
  split at h
  · next hv =>
    obtain ⟨hupd, _⟩ :=
      intersectOrDrop_valid_branch g id (unionOwnersOf g (nb d)) d hd_mem hd_id h
    have hfix : { d with owners := intersectOwners d.owners (unionOwnersOf g (nb d)) } = d :=
      updateAt_pointwise g id _ hupd d hd_mem hd_id
    exact congrArg PNodeM.owners hfix
  · next hv =>
    have hlt := measure_removeNode_lt g id d hd_mem hd_id
    exact absurd h (Nat.ne_of_lt hlt)

/-- The three stages of a fixpoint pass are each the identity. -/
theorem reviewPass_stages_eq_self (g : GPathM) (h : measure (reviewPass g) = measure g) :
    cleanInvalid g = g ∧ reviewParents g = g ∧ reviewSons g = g := by
  have h₁ := measure_cleanInvalid_le g
  have h₂ := measure_reviewParents_le (cleanInvalid g)
  have h₃ := measure_reviewSons_le (reviewParents (cleanInvalid g))
  simp only [reviewPass] at h
  have hclean : cleanInvalid g = g := cleanInvalid_eq_self g (by omega)
  rw [hclean] at h h₂ h₃
  have h₃' := measure_reviewSons_le (reviewParents g)
  have hpar : reviewParents g = g := reviewParents_eq_self g (by omega)
  rw [hpar] at h
  exact ⟨hclean, hpar, reviewSons_eq_self g h⟩

-- ============================================================
-- F2.c, per-node form (the plan's §4 postcondition)
-- ============================================================

/-- The `cleanInvalid` step for any node `review` still exposes was itself the
identity — the shared first half of the per-node results below. -/
theorem review_cleanStep_fixed (g : GPathM) (h : isValid (review g) = true)
    (id : PathNodeId) (d : PNodeM) (hd : (review g).node? id = some d) :
    cleanStep (review g) id = review g := by
  have hfix : reviewPass (review g) = review g := reviewPass_review g h
  obtain ⟨hclean, _, _⟩ := reviewPass_stages_eq_self (review g) (by rw [hfix])
  have hd_mem : d ∈ (review g).nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = id := node?_id_eq _ id d hd
  have hid_mem : id ∈ (review g).nodes.map (·.id) := by
    have hmem := List.mem_map_of_mem (f := fun n : PNodeM => n.id) hd_mem
    rwa [hd_id] at hmem
  have hgo : cleanInvalidGo (review g) ((review g).nodes.map (·.id)) = review g := hclean
  exact cleanInvalidGo_steps_eq_self _ (review g) (by rw [hgo]) id hid_mem

/-- **F2.c (per-node), part 1** — after `review`, every node the machine can
still look up passes `is_valid_node`.

Stated over `node?` rather than over `∈ nodes` on purpose: `node?` takes the
*first* match, and nothing in this model forces node ids to be unique, so a
shadowed duplicate is a node the machine itself can never reach. Every lookup
in `GPathM` (and in the executable) goes through `node?`. -/
theorem review_node_valid (g : GPathM) (h : isValid (review g) = true)
    (id : PathNodeId) (d : PNodeM) (hd : (review g).node? id = some d) :
    isValidNode (review g) d = true :=
  cleanStep_node_valid (review g) id d hd (by rw [review_cleanStep_fixed g h id d hd])

/-- **F2.c (per-node), part 3** — after `review`, a node's owners are already
contained in the *global* owners, in `intersectOwners`' sense. Together with
`isValid` (which guarantees the global owners do mention every step below
`current_step`) this upgrades to plain membership: see
`Filter.lean`'s `owners_mem_gowners`. -/
theorem review_owners_within_gowners (g : GPathM) (h : isValid (review g) = true)
    (id : PathNodeId) (d : PNodeM) (hd : (review g).node? id = some d) :
    intersectOwners d.owners (review g).gowners = d.owners :=
  cleanStep_owners_fixed (review g) id d hd (by rw [review_cleanStep_fixed g h id d hd])

/-- **F2.c (per-node), part 2a** — after `review`, a node's owners are already
coherent with the union of its *parents'* owners: intersecting against that
union changes nothing.

"Coherent" is `intersectOwners`' own notion, which is what the algorithm
means by it: an owner at a step where the union has no entry at all is left
untouched; where the union does have entries, only its members survive. -/
theorem review_owners_coherent_parents (g : GPathM) (h : isValid (review g) = true)
    (k : Int) (hk : k ∈ intRange 1 ((review g).current_step - 1))
    (id : PathNodeId) (hid : id ∈ (((review g).line k).map (·.id)))
    (d : PNodeM) (hd : (review g).node? id = some d) :
    intersectOwners d.owners (unionOwnersOf (review g) d.parents) = d.owners := by
  have hfix : reviewPass (review g) = review g := reviewPass_review g h
  obtain ⟨_, hpar, _⟩ := reviewPass_stages_eq_self (review g) (by rw [hfix])
  have hsteps : reviewSteps (review g) (·.parents)
      (intRange 1 ((review g).current_step - 1)) = review g := hpar
  have hline : reviewLine (review g) (·.parents) k = review g :=
    reviewSteps_lines_eq_self _ _ (review g) h (by rw [hsteps]) k hk
  have hnode : reviewNode (review g) (·.parents) id = review g :=
    reviewLine_nodes_eq_self (review g) _ k (by rw [hline]) id hid
  exact reviewNode_owners_fixed (review g) _ id d hd (by rw [hnode])

/-- **F2.c (per-node), part 2b** — the same for the *sons'* owners. Note the
narrower step range: the bottom-up pass walks `1 .. current_step - 2`. -/
theorem review_owners_coherent_sons (g : GPathM) (h : isValid (review g) = true)
    (k : Int) (hk : k ∈ intRange 0 ((review g).current_step - 2))
    (id : PathNodeId) (hid : id ∈ (((review g).line k).map (·.id)))
    (d : PNodeM) (hd : (review g).node? id = some d) :
    intersectOwners d.owners (unionOwnersOf (review g) d.sons) = d.owners := by
  have hfix : reviewPass (review g) = review g := reviewPass_review g h
  obtain ⟨_, _, hsons⟩ := reviewPass_stages_eq_self (review g) (by rw [hfix])
  have hsteps : reviewSteps (review g) (·.sons)
      (intRange 0 ((review g).current_step - 2)).reverse = review g := hsons
  have hline : reviewLine (review g) (·.sons) k = review g :=
    reviewSteps_lines_eq_self _ _ (review g) h (by rw [hsteps]) k (List.mem_reverse.mpr hk)
  have hnode : reviewNode (review g) (·.sons) id = review g :=
    reviewLine_nodes_eq_self (review g) _ k (by rw [hline]) id hid
  exact reviewNode_owners_fixed (review g) _ id d hd (by rw [hnode])

-- ============================================================
-- Axiom guards: the build fails if any project axiom ever enters
-- the closure of the three F2 results (only Lean's built-in
-- propext/Quot.sound are allowed).
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.GPathM.measure_reviewPass_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms measure_reviewPass_le

/-- info: 'AbsSat.GraphPath.Model.GPathM.review_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_stable

/-- info: 'AbsSat.GraphPath.Model.GPathM.reviewPass_review' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reviewPass_review

/-- info: 'AbsSat.GraphPath.Model.GPathM.review_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_idempotent

/-- info: 'AbsSat.GraphPath.Model.GPathM.review_node_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_node_valid

/-- info: 'AbsSat.GraphPath.Model.GPathM.review_owners_within_gowners' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_owners_within_gowners

/-- info: 'AbsSat.GraphPath.Model.GPathM.review_owners_coherent_parents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_owners_coherent_parents

/-- info: 'AbsSat.GraphPath.Model.GPathM.review_owners_coherent_sons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_owners_coherent_sons

end GPathM

end AbsSat.GraphPath.Model
