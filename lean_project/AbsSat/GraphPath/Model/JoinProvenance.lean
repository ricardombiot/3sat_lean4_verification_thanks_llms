-- lean_project/AbsSat/GraphPath/Model/JoinProvenance.lean
import AbsSat.GraphPath.Model.JoinDescent
import AbsSat.GraphPath.Model.Hereditary
import AbsSat.GraphPath.Model.LocalContradiction

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
open AbsSat.GraphPath.Model.AggressiveReview (pruned_filterAllAgg sharesEveryStep)
open AbsSat.GraphPath.Model.AggFixpoint (AggOk)

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


-- ============================================================
-- The side is read off the top step
-- ============================================================

/-- A node one side does not have is not one of its choices either. -/
theorem not_gowner_of_node_none {g : GPathM} (hgn : GownersNodes.GN g) {z : PathNodeId}
    (hz : g.node? z = none) : z ∉ g.gowners := by
  intro hzg
  have hsome := (GownersNodes.hasNode_iff g z).mp (hgn z hzg)
  rw [hz] at hsome
  exact absurd hsome (by simp)

/-- **The slice of a node one side does not have lies entirely on the other side.** Applied to a
top-step node — each of which belongs to exactly one side, since a send adds one node and a join
keeps both — this is the criterion: the side of a choice is read off the top step.

Every choice surviving in a constrained join owns some top node (its record is valid, so it has an
owner at every step) and, by the symmetry of the sweep, belongs to that node's slice. Measured on
Tseitin K4 even: of 27,670 surviving choices, not one failed to own a top node exclusive to a
side, and the 3,033 that own top nodes of both sides are exactly those that survive in both
constrained sides. -/
theorem slice_of_exclusive_top (g₁ g₂ B : GPathM) (hpr : Pruned (join g₁ g₂) B)
    (hnd : NodupIds (join g₁ g₂)) (ho₂ : OwnGow g₂) (hgn₂ : GownersNodes.GN g₂)
    (hstep : (join g₁ g₂).current_step = g₂.current_step)
    {z x : PathNodeId} {nx : PNodeM} (hx : B.node? x = some nx) (hzx : z ∈ nx.owners)
    (hz0 : 0 ≤ z.id.step) (hz1 : z.id.step < B.current_step)
    (hznone : g₂.node? z = none) : (g₁.node? x).isSome = true :=
  node_left_of_not_gowner g₁ g₂ B hpr hnd ho₂ hstep hx hzx hz0 hz1
    (not_gowner_of_node_none hgn₂ hznone)

/-- **The criterion applied to the slice of a choice.** If every owner of a choice `q` at the top step is a node
the right side does not have, then every node of the constrained join that owns `q` is a node of
the left side.

The symmetric sweep is what makes this work: it leaves each member of the slice sharing an owner
with `q` at *every* step, the top one included, and that shared owner is one of `q`'s top owners,
which only the left side has. This covers the choices whose top owners all belong to one side
(24,637 of 27,670 in Tseitin K4 even); for the rest, `slice_of_exclusive_top` still gives a side,
on the slice of one top node instead of the slice of the choice. -/
theorem slice_side_of_tops (g₁ g₂ B : GPathM) (hpr : Pruned (join g₁ g₂) B)
    (hnd : NodupIds (join g₁ g₂)) (ho₂ : OwnGow g₂) (hgn₂ : GownersNodes.GN g₂)
    (hstep : (join g₁ g₂).current_step = g₂.current_step)
    (hagg : AggOk B) (hpos : 0 < B.current_step)
    {q x : PathNodeId} {nq nx : PNodeM}
    (hq : B.node? q = some nq) (hx : B.node? x = some nx)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < B.current_step)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < B.current_step)
    (hqx : q ∈ nx.owners) (hvx : isValidNode B nx = true) (hvq : isValidNode B nq = true)
    (htop : ∀ r ∈ nq.owners, r.id.step = B.current_step - 1 → g₂.node? r = none) :
    (g₁.node? x).isSome = true := by
  obtain ⟨_, hsh⟩ := hagg x nx q nq hx hq hx0 hx1 hq0 hq1 hqx hvx hvq
  have hk0 : (0:Int) ≤ B.current_step - 1 := by omega
  have hall : (intRange 0 (B.current_step - 1)).all
      (fun k => !hasStepEntry nq.owners k || (ownersAt nx.owners k).any
        (fun r => nq.owners.contains r)) = true := by
    simpa only [sharesEveryStep] using hsh
  have hcl := List.all_eq_true.mp hall _ (mem_intRange hk0 (Int.le_refl _))
  have hent : hasStepEntry nq.owners (B.current_step - 1) = true :=
    LocalContradiction.ownersOk_of_isValidNode B nq hvq _ hk0 (by omega)
  simp only [hent, Bool.not_true, Bool.false_or] at hcl
  obtain ⟨r, hr, hrq⟩ := List.any_eq_true.mp hcl
  have hrx : r ∈ nx.owners := (List.mem_filter.mp hr).1
  have hrs : r.id.step = B.current_step - 1 := eq_of_beq (List.mem_filter.mp hr).2
  have hrnone : g₂.node? r = none := htop r (List.mem_of_elem_eq_true hrq) hrs
  exact slice_of_exclusive_top g₁ g₂ B hpr hnd ho₂ hgn₂ hstep hx hrx (by omega) (by omega) hrnone

/-- info: 'AbsSat.GraphPath.Model.JoinProvenance.slice_one_side' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms slice_one_side

/-- info: 'AbsSat.GraphPath.Model.JoinProvenance.slice_side_of_tops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms slice_side_of_tops

/-- info: 'AbsSat.GraphPath.Model.JoinProvenance.slice_of_exclusive_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms slice_of_exclusive_top

end AbsSat.GraphPath.Model.JoinProvenance
