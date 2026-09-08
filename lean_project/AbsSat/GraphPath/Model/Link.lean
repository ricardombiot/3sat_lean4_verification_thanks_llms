-- lean_project/AbsSat/GraphPath/Model/Link.lean
import AbsSat.GraphPath.Model.ZeroOneAll

/-!
The link between the machine's `owners` tables and the CSP — and the point at
which v12's strategy **does not close**.

## Where the CSP lives

At the *map* level. Requirements are about `NodeId`, and `denot` produces a
list of `NodeId`. `owners` are `PathNodeId`s, several of which can share a map
id with different parents, so the 0/1/all shape has to be read after
projecting (`ownersMapIdsAt`).

## What is proved: the "1" case

`owners_pinned_at_required_step` — at a step one of its requirements names, a
node's owners project to *exactly* that requirement. Nothing else survives
there. That is lemma L1 (`ReqFiltered`) read at the map level, which is where
the constraint network lives, and `owners_nonempty_at_step` makes it a genuine
singleton rather than possibly empty.

So the "1" of 0/1/all does hold of the machine's own tables. That is real
progress: it says the filter enforces exactly what the map demands.

## What is refuted: the "all" case

The remaining half would be that at a step *no* requirement names, the owners
project to **all** the map nodes still available. **That is false**, and
`lake exe l6search` exhibits it: over 1,680 states it reports 164 (node, step)
pairs in *valid* graphs whose projection is a proper subset of two or more map
nodes — neither a singleton nor all. A concrete witness: projection
`{(2,0), (2,1)}` against a step-2 domain of `{(2,0), (2,1), (2,2)}`.

The mechanism is not a bug. The coherence pass intersects a node's owners with
the **union** over its neighbours (`unionOwnersOf`), and a union of two
singletons is a two-element set. The tables aggregate over neighbours, so they
are an arc-consistency approximation along the parent/son links, not the
constraint network's own rows.

## What this means for v12's strategy

The raw constraints the map generates *are* 0/1/all — that is
`GraphMap.MapReqs`, and it stands. `ZeroOneAll.helly` shows such supports have
the Helly property, and that stands too. What does not hold is the step that
would connect them: **the machine's tables are not those supports.**

So the gap is not the inclusion `owners ⊆ support` as `ArcConsistency.lean`
framed it. It is that 0/1/all constraints are majority-closed, giving strict
width 2 — which needs *path* consistency — while the machine maintains
something weaker, arc consistency along the parent/son links plus the global
owners. Whether that weaker propagation is nonetheless enough **for this
particular map** is the open question, and it is not answered by CCJ off the
shelf.

The empirical evidence still says yes: no reader error over thousands of
`diffTest` instances, no counterexample over 1,680 `l6search` states. But the
clean route sketched in v12 does not close, and this module is where it stops.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

/-- The **map nodes** a node's owners still allow at step `j`. The CSP lives at
the map level — requirements are about `NodeId`, and `denot` produces a list of
`NodeId` — while `owners` are `PathNodeId`s, several of which can share a map
id with different parents. So the 0/1/all shape has to be read after this
projection. -/
def ownersMapIdsAt (n : PNodeM) (j : Int) : List NodeId :=
  (ownersAt n.owners j).map (·.id)

theorem mem_ownersMapIdsAt {n : PNodeM} {j : Int} {m : NodeId}
    (h : m ∈ ownersMapIdsAt n j) : ∃ q ∈ n.owners, q.id.step = j ∧ q.id = m := by
  obtain ⟨q, hq, hEq⟩ := List.mem_map.mp h
  simp only [ownersAt, List.mem_filter] at hq
  exact ⟨q, hq.1, eq_of_beq hq.2, hEq⟩

/-- **The "1" of 0/1/all, for the machine's own tables.** At a step one of its
requirements names, a node's owners project to exactly that requirement — no
other map node survives there.

This is lemma L1 (`ReqFiltered`) read at the map level, which is where the
constraint network lives. -/
theorem owners_pinned_at_required_step (reqOf : NodeId → List NodeId) (g : GPathM)
    (hreach : Reachable reqOf g) (pid : PathNodeId) (n : PNodeM)
    (hn : g.node? pid = some n) (req : NodeId) (hreq : req ∈ reqOf n.id.id) :
    ∀ m ∈ ownersMapIdsAt n req.step, m = req := by
  intro m hm
  obtain ⟨q, hq, hqstep, rfl⟩ := mem_ownersMapIdsAt hm
  exact L1 reqOf hreach n (List.mem_of_find?_eq_some hn) req hreq q hq hqstep

/-- And it is non-empty, by arc consistency. So the projection is *exactly*
`{req}`: the support really is the singleton the map asked for. -/
theorem owners_nonempty_at_step (n : PNodeM) (j : Int)
    (h : hasStepEntry n.owners j = true) : ownersMapIdsAt n j ≠ [] := by
  simp only [hasStepEntry, List.any_eq_true] at h
  obtain ⟨q, hq, hqs⟩ := h
  intro hnil
  have : q.id ∈ ownersMapIdsAt n j := by
    refine List.mem_map_of_mem ?_
    simp only [ownersAt, List.mem_filter]
    exact ⟨hq, hqs⟩
  rw [hnil] at this
  exact absurd this List.not_mem_nil

/-- The shape v12's strategy needed and the falsifier refutes: at every step, a
node's owners project either to one map node or to all those still available.
Stated for the record — `lake exe l6search` reports 164 violations of it over
1,680 valid states. -/
def OwnersAllOrOne (g : GPathM) : Prop :=
  ∀ pid n, g.node? pid = some n → ∀ j, 0 ≤ j → j < g.current_step →
    (∃ m, ∀ m' ∈ ownersMapIdsAt n j, m' = m) ∨
    (∀ d ∈ g.line j, d.id.id ∈ ownersMapIdsAt n j)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.owners_pinned_at_required_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owners_pinned_at_required_step

/-- info: 'AbsSat.GraphPath.Model.owners_nonempty_at_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owners_nonempty_at_step

end AbsSat.GraphPath.Model
