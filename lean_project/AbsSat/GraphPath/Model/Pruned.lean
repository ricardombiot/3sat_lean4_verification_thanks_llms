-- lean_project/AbsSat/GraphPath/Model/Pruned.lean
import AbsSat.GraphPath.Model.GPathM

/-!
The `Pruned` relation: `Pruned g g'` says `g'` was obtained from `g` by
operations that only *narrow* — the current step is unchanged, the global
owners of `g'` are a subset of `g`'s, and every node of `g'` descends from a
node of `g` with the same id, a subset of its owners and a subset of its
parent links.

Every review/filter operation of `GPathM` lands in this relation, and the
relation is reflexive and transitive, so the whole review loop does too.
This is the machinery that replaces the F5 axioms A1–A5 with proofs (plan
§7.2): a property that is (a) about node ids and owner membership only and
(b) stable under narrowing transfers across any `Pruned` edge for free.

The proofs use exactly the `simp only [f]` + `split` technique validated in
`Fuel.lean` on the same `|`-defined functions.
-/

namespace AbsSat.GraphPath.Model

open AbsSat.Utils.Alias

structure Pruned (g g' : GPathM) : Prop where
  step_eq : g'.current_step = g.current_step
  map_parent_eq : g'.map_parent = g.map_parent
  gowners_sub : ∀ q ∈ g'.gowners, q ∈ g.gowners
  nodes_derived : ∀ n' ∈ g'.nodes, ∃ n ∈ g.nodes, n'.id = n.id ∧
    (∀ q ∈ n'.owners, q ∈ n.owners) ∧ (∀ p ∈ n'.parents, p ∈ n.parents)

namespace Pruned

protected theorem refl (g : GPathM) : Pruned g g where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n hn := ⟨n, hn, rfl, fun _ hq => hq, fun _ hp => hp⟩

protected theorem trans {g₁ g₂ g₃ : GPathM} (h₁₂ : Pruned g₁ g₂) (h₂₃ : Pruned g₂ g₃) :
    Pruned g₁ g₃ where
  step_eq := h₂₃.step_eq.trans h₁₂.step_eq
  map_parent_eq := h₂₃.map_parent_eq.trans h₁₂.map_parent_eq
  gowners_sub q hq := h₁₂.gowners_sub q (h₂₃.gowners_sub q hq)
  nodes_derived n₃ hn₃ := by
    obtain ⟨n₂, hn₂, hid₂, hown₂, hpar₂⟩ := h₂₃.nodes_derived n₃ hn₃
    obtain ⟨n₁, hn₁, hid₁, hown₁, hpar₁⟩ := h₁₂.nodes_derived n₂ hn₂
    exact ⟨n₁, hn₁, hid₂.trans hid₁, fun q hq => hown₁ q (hown₂ q hq),
      fun p hp => hpar₁ p (hpar₂ p hp)⟩

end Pruned

namespace GPathM

-- ============================================================
-- Primitive operations
-- ============================================================

/-- Pointwise behavior of the `updateAtGo` transformer: it either leaves the
node alone or applies `f`, so id preservation and owner narrowing lift. -/
private theorem updateAtGo_point (id : PathNodeId) (f : PNodeM → PNodeM)
    (hid : ∀ n, (f n).id = n.id)
    (hown : ∀ n, ∀ q ∈ (f n).owners, q ∈ n.owners)
    (hpar : ∀ n, ∀ p ∈ (f n).parents, p ∈ n.parents) (n : PNodeM) :
    (match n.id == id with | true => f n | false => n).id = n.id ∧
    (∀ q ∈ (match n.id == id with | true => f n | false => n).owners, q ∈ n.owners) ∧
    (∀ p ∈ (match n.id == id with | true => f n | false => n).parents, p ∈ n.parents) := by
  cases n.id == id
  · exact ⟨rfl, fun _ hq => hq, fun _ hp => hp⟩
  · exact ⟨hid n, hown n, hpar n⟩

theorem pruned_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hid : ∀ n, (f n).id = n.id)
    (hown : ∀ n, ∀ q ∈ (f n).owners, q ∈ n.owners)
    (hpar : ∀ n, ∀ p ∈ (f n).parents, p ∈ n.parents) :
    Pruned g (updateAt g id f) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n' hn' := by
    simp only [updateAt, updateAtGo] at hn'
    rcases List.mem_map.mp hn' with ⟨n, hn, hEq⟩
    subst hEq
    obtain ⟨h1, h2, h3⟩ := updateAtGo_point id f hid hown hpar n
    exact ⟨n, hn, h1, h2, h3⟩

theorem pruned_removeNode (g : GPathM) (id : PathNodeId) :
    Pruned g (removeNode g id) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n' hn' := by
    dsimp only [removeNode] at hn'
    rcases List.mem_map.mp hn' with ⟨n, hn, hEq⟩
    subst hEq
    exact ⟨n, (List.mem_filter.mp hn).1, rfl, fun _ hq => hq,
      fun _ hp => (List.mem_filter.mp hp).1⟩

theorem pruned_filterRequire (g : GPathM) (req : NodeId) :
    Pruned g (filterRequire g req) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n hn := ⟨n, hn, rfl, fun _ hq => hq, fun _ hp => hp⟩

theorem pruned_foldl {β : Type} (f : GPathM → β → GPathM)
    (h : ∀ g b, Pruned g (f g b)) :
    ∀ (l : List β) (g : GPathM), Pruned g (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g; exact Pruned.refl g
  | cons b bs ih =>
    intro g
    simp only [List.foldl_cons]
    exact Pruned.trans (h g b) (ih (f g b))

-- ============================================================
-- The review pass
-- ============================================================

theorem unlinkMap_id (n : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (unlinkMap n id m).id = m.id := by
  unfold GPathM.unlinkMap; split
  · rfl
  · split <;> rfl

theorem unlinkMap_owners (n : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (unlinkMap n id m).owners = m.owners := by
  unfold GPathM.unlinkMap; split
  · rfl
  · split <;> rfl

theorem pruned_unlinkIncompatible (g : GPathM) (id : PathNodeId) :
    Pruned g (unlinkIncompatible g id) := by
  unfold GPathM.unlinkIncompatible
  split
  · exact Pruned.refl g
  · next n _ =>
    refine ⟨rfl, rfl, fun q hq => hq, ?_⟩
    intro n' hn'
    obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hn'
    refine ⟨m, hm, ?_, ?_, ?_⟩
    · rw [← hEq]; exact unlinkMap_id n id m
    · rw [← hEq, unlinkMap_owners]; intro q hq; exact hq
    · rw [← hEq]; unfold GPathM.unlinkMap; split
      · intro p hp; exact (List.mem_filter.mp hp).1
      · split
        · intro p hp; exact hp
        · intro p hp; exact (List.mem_filter.mp hp).1

theorem pruned_cleanInvalidGo (ids : List PathNodeId) :
    ∀ g : GPathM, Pruned g (cleanInvalidGo g ids) := by
  induction ids with
  | nil => intro g; exact Pruned.refl g
  | cons id rest ih =>
    intro g
    simp only [cleanInvalidGo]
    split
    · exact ih g
    · next d _ =>
      refine Pruned.trans ?_ (ih _)
      have h₁ : Pruned g (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners g.gowners })) :=
        pruned_updateAt g id _ (fun _ => rfl)
          (fun _ q hq => (List.mem_filter.mp hq).1) (fun _ _ hp => hp)
      have h₂ := Pruned.trans h₁ (pruned_unlinkIncompatible _ id)
      split
      · exact h₂
      · exact Pruned.trans h₂ (pruned_removeNode _ id)

theorem pruned_cleanInvalid (g : GPathM) : Pruned g (cleanInvalid g) :=
  pruned_cleanInvalidGo _ g

-- ============================================================
-- The mirror (review simétrico, 2026-09-24)
-- ============================================================

theorem mirrorMap_id (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM) :
    (mirrorMap x rem m).id = m.id := by
  unfold GPathM.mirrorMap; split <;> rfl

theorem mirrorMap_parents (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM) :
    (mirrorMap x rem m).parents = m.parents := by
  unfold GPathM.mirrorMap; split <;> rfl

theorem mirrorMap_sons (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM) :
    (mirrorMap x rem m).sons = m.sons := by
  unfold GPathM.mirrorMap; split <;> rfl

theorem mirrorMap_title (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM) :
    (mirrorMap x rem m).title = m.title := by
  unfold GPathM.mirrorMap; split <;> rfl

theorem mirrorMap_owners_sub (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM) :
    ∀ q ∈ (mirrorMap x rem m).owners, q ∈ m.owners := by
  unfold GPathM.mirrorMap; split
  · intro q hq; exact (List.mem_filter.mp hq).1
  · intro q hq; exact hq

/-- The mirror keeps every entry other than `x`. -/
theorem mirrorMap_owners_keep (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM)
    (q : PathNodeId) (hq : q ∈ m.owners) (hqx : q ≠ x) : q ∈ (mirrorMap x rem m).owners := by
  unfold GPathM.mirrorMap; split
  · exact List.mem_filter.mpr ⟨hq, bne_iff_ne.mpr hqx⟩
  · exact hq

/-- A node that is not among the removed ids is untouched. -/
theorem mirrorMap_of_not (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM)
    (h : rem.contains m.id = false) : mirrorMap x rem m = m := by
  unfold GPathM.mirrorMap; rw [h]; rfl

theorem pruned_mirrorDrop (g : GPathM) (x : PathNodeId) (rem : List PathNodeId) :
    Pruned g (mirrorDrop g x rem) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n' hn' := by
    obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hn'
    subst hEq
    exact ⟨m, hm, mirrorMap_id x rem m, mirrorMap_owners_sub x rem m,
      fun p hp => by rw [mirrorMap_parents] at hp; exact hp⟩

theorem pruned_reviewNode (nb : PNodeM → List PathNodeId) (id : PathNodeId)
    (g : GPathM) : Pruned g (reviewNode g nb id) := by
  simp only [reviewNode]
  split
  · exact Pruned.refl g
  · next d _ =>
    split
    · have h₁ : Pruned g (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) :=
        pruned_updateAt g id _ (fun _ => rfl)
          (fun _ q hq => (List.mem_filter.mp hq).1) (fun _ _ hp => hp)
      have h₂ := Pruned.trans (Pruned.trans h₁ (pruned_mirrorDrop _ id
        (cutRemoved d (unionOwnersOf g (nb d))))) (pruned_unlinkIncompatible _ id)
      split
      · exact h₂
      · exact Pruned.trans h₂ (pruned_removeNode _ id)
    · exact pruned_removeNode g id

theorem pruned_reviewLine (nb : PNodeM → List PathNodeId) (k : Int) (g : GPathM) :
    Pruned g (reviewLine g nb k) :=
  pruned_foldl (fun g id => reviewNode g nb id)
    (fun g id => pruned_reviewNode nb id g) _ g

theorem pruned_reviewSteps (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, Pruned g (reviewSteps g nb ks) := by
  induction ks with
  | nil => intro g; exact Pruned.refl g
  | cons k ks ih =>
    intro g
    simp only [reviewSteps]
    split
    · exact Pruned.trans (pruned_reviewLine nb k g) (ih _)
    · exact Pruned.refl g

theorem pruned_reviewParents (g : GPathM) : Pruned g (reviewParents g) :=
  pruned_reviewSteps _ _ g

theorem pruned_reviewSons (g : GPathM) : Pruned g (reviewSons g) :=
  pruned_reviewSteps _ _ g

theorem cutNode_id (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    (cutNode gow g n).id = n.id := rfl

theorem cutNode_owners_sub (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    ∀ q ∈ (cutNode gow g n).owners, q ∈ n.owners :=
  fun _ hq => (List.mem_filter.mp hq).1

theorem cutNode_parents_sub (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    ∀ p ∈ (cutNode gow g n).parents, p ∈ n.parents :=
  fun _ hp => (List.mem_filter.mp hp).1

theorem cutNode_sons_sub (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    ∀ s ∈ (cutNode gow g n).sons, s ∈ n.sons :=
  fun _ hs => (List.mem_filter.mp hs).1

theorem pruned_purgeStep (g : GPathM) (id : PathNodeId) : Pruned g (purgeStep g id) := by
  unfold purgeStep
  split
  · exact Pruned.refl g
  · split
    · exact Pruned.refl g
    · exact pruned_removeNode g id

theorem pruned_purgeRound (g : GPathM) : Pruned g (purgeRound g) := by
  exact pruned_foldl purgeStep pruned_purgeStep _ g

theorem pruned_purgeFuel : ∀ (fuel : Nat) (g : GPathM), Pruned g (purgeFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Pruned.refl g
  | succ n ih =>
    intro g
    simp only [purgeFuel]
    split
    · split
      · exact Pruned.trans (pruned_purgeRound g) (ih _)
      · exact pruned_purgeRound g
    · exact Pruned.refl g

theorem pruned_cutAll (g : GPathM) : Pruned g (cutAll g) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n' hn' := by
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
    subst hEq
    exact ⟨n, hn, rfl, cutNode_owners_sub _ _ n, cutNode_parents_sub _ _ n⟩

theorem pruned_cleanInvalid₂ (g : GPathM) : Pruned g (cleanInvalid₂ g) :=
  Pruned.trans (pruned_purgeFuel _ g) (pruned_cutAll _)

theorem pruned_reviewPass (g : GPathM) : Pruned g (reviewPass g) := by
  simp only [reviewPass]
  exact Pruned.trans (pruned_cleanInvalid₂ g)
    (Pruned.trans (pruned_reviewParents _) (pruned_reviewSons _))

theorem pruned_reviewFuel : ∀ (fuel : Nat) (g : GPathM), Pruned g (reviewFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Pruned.refl g
  | succ f ih =>
    intro g
    simp only [reviewFuel]
    split
    · split
      · exact Pruned.trans (pruned_reviewPass g) (ih _)
      · exact pruned_reviewPass g
    · exact Pruned.refl g

theorem pruned_review (g : GPathM) : Pruned g (review g) :=
  pruned_reviewFuel _ g

theorem pruned_filterAll (g : GPathM) (reqs : List NodeId) :
    Pruned g (filterAll g reqs) :=
  Pruned.trans (pruned_foldl _ pruned_filterRequire reqs g) (pruned_review _)

-- ============================================================
-- node? facts (previously axioms A6/A7 — one-liners)
-- ============================================================

theorem node?_mem (g : GPathM) (pid : PathNodeId) (h : (g.node? pid).isSome) :
    (g.node? pid).get h ∈ g.nodes :=
  List.mem_of_find?_eq_some (Option.some_get h).symm

theorem node?_id_eq (g : GPathM) (pid : PathNodeId) (n : PNodeM)
    (h : g.node? pid = some n) : n.id = pid := by
  have h' : g.nodes.find? (fun m => m.id == pid) = some n := h
  have hp := List.find?_some h'
  exact eq_of_beq hp

/-- `node?` follows a node through the mirror (the mirror keeps every id). -/
theorem mirrorDrop_node? (g : GPathM) (x : PathNodeId) (rem : List PathNodeId)
    (pid : PathNodeId) (n : PNodeM) (hn : g.node? pid = some n) :
    (mirrorDrop g x rem).node? pid = some (mirrorMap x rem n) := by
  have hp : (fun m : PNodeM => (mirrorMap x rem m).id == pid) = (fun m : PNodeM => m.id == pid) := by
    funext m; rw [mirrorMap_id]
  show List.find? _ (g.nodes.map (mirrorMap x rem)) = _
  simp only [List.find?_map, Function.comp_def, hp]
  rw [show g.nodes.find? (fun m : PNodeM => m.id == pid) = some n from hn]
  rfl

/-- ... and back: a node of the mirrored graph comes from a node of `g`. -/
theorem mirrorDrop_node?_inv (g : GPathM) (x : PathNodeId) (rem : List PathNodeId)
    (pid : PathNodeId) (n' : PNodeM) (hn' : (mirrorDrop g x rem).node? pid = some n') :
    ∃ n, g.node? pid = some n ∧ n' = mirrorMap x rem n := by
  cases hn : g.node? pid with
  | none =>
    have hp : (fun m : PNodeM => (mirrorMap x rem m).id == pid) = (fun m : PNodeM => m.id == pid) := by
      funext m; rw [mirrorMap_id]
    have : (mirrorDrop g x rem).node? pid = none := by
      show List.find? _ (g.nodes.map (mirrorMap x rem)) = _
      simp only [List.find?_map, Function.comp_def, hp]
      rw [show g.nodes.find? (fun m : PNodeM => m.id == pid) = none from hn]
      rfl
    rw [this] at hn'; exact absurd hn' (by simp)
  | some n =>
    rw [mirrorDrop_node? g x rem pid n hn] at hn'
    exact ⟨n, rfl, (Option.some.inj hn').symm⟩

/-- **What the cut removes**: an owner that is not in the cut. -/
theorem mem_cutRemoved (n : PNodeM) (B : List PathNodeId) (q : PathNodeId) :
    q ∈ cutRemoved n B ↔ q ∈ n.owners ∧ q ∉ intersectOwners n.owners B := by
  unfold cutRemoved intersectOwners
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
  constructor
  · intro ⟨hq, hs, hc⟩
    refine ⟨hq, fun ⟨_, h⟩ => ?_⟩
    rcases h with h | h
    · rw [hs] at h; exact Bool.noConfusion h
    · rw [hc] at h; exact Bool.noConfusion h
  · intro ⟨hq, hn⟩
    refine ⟨hq, ?_, ?_⟩
    · cases hs : hasStepEntry B q.id.step with
      | true => rfl
      | false => exact absurd ⟨hq, Or.inl hs⟩ hn
    · cases hc : B.contains q with
      | false => rfl
      | true => exact absurd ⟨hq, Or.inr hc⟩ hn

/-- An owner the cut keeps is not among the removed ones. -/
theorem not_mem_cutRemoved (n : PNodeM) (B : List PathNodeId) (q : PathNodeId)
    (h : q ∈ n.owners → q ∈ intersectOwners n.owners B) : (cutRemoved n B).contains q = false := by
  cases hc : (cutRemoved n B).contains q with
  | false => rfl
  | true =>
    obtain ⟨hq, hnot⟩ := (mem_cutRemoved n B q).mp (List.contains_iff_mem.mp hc)
    exact absurd (h hq) hnot

/-- Removed owners were owners. -/
theorem mem_of_cutRemoved (n : PNodeM) (B : List PathNodeId) (q : PathNodeId)
    (h : q ∈ cutRemoved n B) : q ∈ n.owners := ((mem_cutRemoved n B q).mp h).1

end GPathM

end AbsSat.GraphPath.Model
