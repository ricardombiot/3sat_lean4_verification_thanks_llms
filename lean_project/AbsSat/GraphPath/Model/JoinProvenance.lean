-- lean_project/AbsSat/GraphPath/Model/JoinProvenance.lean
import AbsSat.GraphPath.Model.JoinDescent
import AbsSat.GraphPath.Model.Hereditary

/-!
# Where the nodes of a choice of a join come from

`JoinSplit` (`HereditaryRun`) asks that a global owner surviving in a constrained `join` be a
global owner of one constrained side. This file proves the **node half** of it, which needs no
fixpoint argument:

* `node_left_of_not_gowner`, `node_right_of_not_gowner` — in any narrowing of `join g₁ g₂`, a node
  that owns a choice `q` absent from one side's global owners is a node of the **other** side.
* `slice_one_side` — hence the slice of a choice exclusive to one side has **all** its nodes on
  that side.

So a choice of a join cannot mix *nodes* of the two sides, exactly as `no_chain_across_sides`
says for partial chains. What is left of `JoinSplit` is therefore only about **owner entries**
at the nodes both sides share, where `mergeNode` unions the tables, and about choices that both
sides already had. That residue is the greatest-fixpoint exactness measured in v119/v124/v128,
and it is what v129 records as the single remaining obstacle.
-/

namespace AbsSat.GraphPath.Model.JoinProvenance

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Hereditary
open AbsSat.GraphPath.Model.AggressiveReview (pruned_filterAllAgg)

/-- **Owners in range are global owners**: the `ownGow` fact that every reviewed state has
(`Pinned.Ctx.ownGow`, `Candidates.owner_mem_gowners`). -/
def OwnGow (g : GPathM) : Prop :=
  ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners,
    0 ≤ q.id.step → q.id.step < g.current_step → q ∈ g.gowners

/-- The record a narrowing of a join derives from. -/
private theorem source_node {g₁ g₂ B : GPathM} (hpr : Pruned (join g₁ g₂) B)
    (hnd : NodupIds (join g₁ g₂)) {x : PathNodeId} {n : PNodeM} (hx : B.node? x = some n) :
    ∃ n₀, (join g₁ g₂).node? x = some n₀ ∧ ∀ q ∈ n.owners, q ∈ n₀.owners := by
  have hnB : n ∈ B.nodes := List.mem_of_find?_eq_some hx
  have hid : n.id = x := node?_id_eq B x n hx
  obtain ⟨n₀, hn₀, hids, hown, _⟩ := hpr.nodes_derived n hnB
  refine ⟨n₀, ?_, hown⟩
  have h := node?_of_mem hnd n₀ hn₀
  rw [← hids, hid] at h
  exact h

/-- **A node owning a choice the right side does not have is a node of the left side.** -/
theorem node_left_of_not_gowner (g₁ g₂ B : GPathM) (hpr : Pruned (join g₁ g₂) B)
    (hnd : NodupIds (join g₁ g₂)) (ho₂ : OwnGow g₂)
    (hstep : (join g₁ g₂).current_step = g₂.current_step)
    {q x : PathNodeId} {n : PNodeM} (hx : B.node? x = some n) (hq : q ∈ n.owners)
    (h0 : 0 ≤ q.id.step) (h1 : q.id.step < B.current_step)
    (hq2 : q ∉ g₂.gowners) : (g₁.node? x).isSome = true := by
  obtain ⟨n₀, hn₀, hown⟩ := source_node hpr hnd hx
  cases hcase : g₁.node? x with
  | some m => simp
  | none =>
    exfalso
    have h2 : g₂.node? x = some n₀ := by
      rw [← join_node?_only_right g₁ g₂ x hcase]; exact hn₀
    refine hq2 (ho₂ x n₀ h2 q (hown q hq) h0 ?_)
    rw [← hstep, ← hpr.step_eq]
    exact h1

/-- **A node owning a choice the left side does not have is a node of the right side.** -/
theorem node_right_of_not_gowner (g₁ g₂ B : GPathM) (hpr : Pruned (join g₁ g₂) B)
    (hnd : NodupIds (join g₁ g₂)) (ho₁ : OwnGow g₁)
    (hstep : (join g₁ g₂).current_step = g₁.current_step)
    {q x : PathNodeId} {n : PNodeM} (hx : B.node? x = some n) (hq : q ∈ n.owners)
    (h0 : 0 ≤ q.id.step) (h1 : q.id.step < B.current_step)
    (hq1 : q ∉ g₁.gowners) : (g₂.node? x).isSome = true := by
  obtain ⟨n₀, hn₀, hown⟩ := source_node hpr hnd hx
  cases hcase : g₂.node? x with
  | some m => simp
  | none =>
    exfalso
    have h1s : (g₁.node? x).isSome = true := by
      rcases join_node?_source g₁ g₂ x n₀ hn₀ with h | h
      · exact h
      · rw [hcase] at h; exact absurd h (by simp)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h1s
    have hJm : (join g₁ g₂).node? x = some m :=
      JoinDescent.join_node?_only_left g₁ g₂ x m hm hcase
    have hmn : m = n₀ := by
      rw [hJm] at hn₀
      exact Option.some_inj.mp hn₀
    refine hq1 (ho₁ x m hm q ?_ h0 ?_)
    · rw [hmn]; exact hown q hq
    · rw [← hstep, ← hpr.step_eq]; exact h1

-- ============================================================
-- The slice of an exclusive choice
-- ============================================================

/-- The nodes of a narrowing that own `q`. -/
def SliceOf (B : GPathM) (q : PathNodeId) (x : PathNodeId) : Prop :=
  ∃ n, B.node? x = some n ∧ q ∈ n.owners

/-- **The slice of an exclusive choice sits on one side.** If a choice surviving in a
constrained join was not already a choice of both sides, then every node of the join that owns
it is a node of the side that had it. -/
theorem slice_one_side (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (C : Cons)
    (hnd : NodupIds (join g₁ g₂)) (ho₁ : OwnGow g₁) (ho₂ : OwnGow g₂)
    {q : PathNodeId} (h0 : 0 ≤ q.id.step)
    (h1 : q.id.step < (Fw (join g₁ g₂) C).current_step)
    (hex : q ∉ g₁.gowners ∨ q ∉ g₂.gowners) :
    (∀ x, SliceOf (Fw (join g₁ g₂) C) q x → (g₁.node? x).isSome = true) ∨
      (∀ x, SliceOf (Fw (join g₁ g₂) C) q x → (g₂.node? x).isSome = true) := by
  have hpr : Pruned (join g₁ g₂) (Fw (join g₁ g₂) C) :=
    Pruned.trans (ReaderAggRun.keeps_filterWeakAll (join g₁ g₂) C).1 (pruned_filterAllAgg _ [])
  rcases hex with hq1 | hq2
  · refine Or.inr (fun x hx => ?_)
    obtain ⟨n, hn, hqn⟩ := hx
    exact node_right_of_not_gowner g₁ g₂ _ hpr hnd ho₁ (grown_join_left g₁ g₂).step_eq
      hn hqn h0 h1 hq1
  · refine Or.inl (fun x hx => ?_)
    obtain ⟨n, hn, hqn⟩ := hx
    exact node_left_of_not_gowner g₁ g₂ _ hpr hnd ho₂ (grown_join_right g₁ g₂ hok).step_eq
      hn hqn h0 h1 hq2

/-- info: 'AbsSat.GraphPath.Model.JoinProvenance.slice_one_side' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms slice_one_side

end AbsSat.GraphPath.Model.JoinProvenance
