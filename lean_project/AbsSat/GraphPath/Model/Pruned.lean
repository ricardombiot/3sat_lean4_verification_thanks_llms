-- lean_project/AbsSat/GraphPath/Model/Pruned.lean
import AbsSat.GraphPath.Model.GPathM

/-!
The `Pruned` relation: `Pruned g g'` says `g'` was obtained from `g` by
operations that only *narrow* — the current step is unchanged, the global
owners of `g'` are a subset of `g`'s, and every node of `g'` descends from a
node of `g` with the same id and a subset of its owners.

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
  gowners_sub : ∀ q ∈ g'.gowners, q ∈ g.gowners
  nodes_derived : ∀ n' ∈ g'.nodes, ∃ n ∈ g.nodes, n'.id = n.id ∧ ∀ q ∈ n'.owners, q ∈ n.owners

namespace Pruned

protected theorem refl (g : GPathM) : Pruned g g where
  step_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n hn := ⟨n, hn, rfl, fun _ hq => hq⟩

protected theorem trans {g₁ g₂ g₃ : GPathM} (h₁₂ : Pruned g₁ g₂) (h₂₃ : Pruned g₂ g₃) :
    Pruned g₁ g₃ where
  step_eq := h₂₃.step_eq.trans h₁₂.step_eq
  gowners_sub q hq := h₁₂.gowners_sub q (h₂₃.gowners_sub q hq)
  nodes_derived n₃ hn₃ := by
    obtain ⟨n₂, hn₂, hid₂, hown₂⟩ := h₂₃.nodes_derived n₃ hn₃
    obtain ⟨n₁, hn₁, hid₁, hown₁⟩ := h₁₂.nodes_derived n₂ hn₂
    exact ⟨n₁, hn₁, hid₂.trans hid₁, fun q hq => hown₁ q (hown₂ q hq)⟩

end Pruned

namespace GPathM

-- ============================================================
-- Primitive operations
-- ============================================================

/-- Pointwise behavior of the `updateAtGo` transformer: it either leaves the
node alone or applies `f`, so id preservation and owner narrowing lift. -/
private theorem updateAtGo_point (id : PathNodeId) (f : PNodeM → PNodeM)
    (hid : ∀ n, (f n).id = n.id)
    (hown : ∀ n, ∀ q ∈ (f n).owners, q ∈ n.owners) (n : PNodeM) :
    (match n.id == id with | true => f n | false => n).id = n.id ∧
    ∀ q ∈ (match n.id == id with | true => f n | false => n).owners, q ∈ n.owners := by
  cases n.id == id
  · exact ⟨rfl, fun _ hq => hq⟩
  · exact ⟨hid n, hown n⟩

theorem pruned_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hid : ∀ n, (f n).id = n.id)
    (hown : ∀ n, ∀ q ∈ (f n).owners, q ∈ n.owners) :
    Pruned g (updateAt g id f) where
  step_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n' hn' := by
    simp only [updateAt, updateAtGo] at hn'
    rcases List.mem_map.mp hn' with ⟨n, hn, hEq⟩
    subst hEq
    obtain ⟨h1, h2⟩ := updateAtGo_point id f hid hown n
    exact ⟨n, hn, h1, h2⟩

theorem pruned_removeNode (g : GPathM) (id : PathNodeId) :
    Pruned g (removeNode g id) where
  step_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n' hn' := by
    dsimp only [removeNode] at hn'
    rcases List.mem_map.mp hn' with ⟨n, hn, hEq⟩
    subst hEq
    exact ⟨n, (List.mem_filter.mp hn).1, rfl, fun _ hq => hq⟩

theorem pruned_filterRequire (g : GPathM) (req : NodeId) :
    Pruned g (filterRequire g req) where
  step_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n hn := ⟨n, hn, rfl, fun _ hq => hq⟩

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
          (fun _ q hq => (List.mem_filter.mp hq).1)
      split
      · exact h₁
      · exact Pruned.trans h₁ (pruned_removeNode _ id)

theorem pruned_cleanInvalid (g : GPathM) : Pruned g (cleanInvalid g) :=
  pruned_cleanInvalidGo _ g

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
          (fun _ q hq => (List.mem_filter.mp hq).1)
      split
      · exact h₁
      · exact Pruned.trans h₁ (pruned_removeNode _ id)
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

theorem pruned_reviewPass (g : GPathM) : Pruned g (reviewPass g) := by
  simp only [reviewPass]
  exact Pruned.trans (pruned_cleanInvalid g)
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

end GPathM

end AbsSat.GraphPath.Model
