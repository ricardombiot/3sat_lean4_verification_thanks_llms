-- lean_project/AbsSat/GraphPath/Model/ArcConsistency.lean
import AbsSat.GraphPath.Model.JoinSound
import AbsSat.GraphPath.Model.OwnersInvariants

/-!
Step (2) of `verificacion_inseguridad_autor_v12.md`'s strategy: **`review`'s
fixpoint is arc consistent.**

`MapReqs.lean` established step (1): the map generates only 0/1/all
constraints. Step (3) would be Cooper–Cohen–Jeavons — a non-empty
arc-consistent 0/1/all network has a solution — which is exactly "no zombies".
This module does step (2), and says precisely what step (3) still needs.

## Arc consistency is not a new notion here — it is `is_valid_node`

Read the machine as a CSP: variables are steps, the domain of step `k` is the
nodes at step `k`, and a node's `owners` at step `j` is its *support table* for
step `j`. Then arc consistency is three clauses, and the algorithm already
enforces all three:

* **support** — every surviving node has at least one owner at every step below
  `current_step`. That is, verbatim, `is_valid_node`'s owners clause
  (`owners_ok_of_isValidNode` isolates it from the parents/sons clauses). So
  `review`'s fixpoint gives it: `review_arcSupported`, on top of F2.c's
  `review_node_valid`.
* **pinned** — at a step some requirement names, the support is narrowed to
  that requirement. That is the "1" of 0/1/all, and it is lemma **L1**
  (`ReqFiltered`), proved back in phase F5.
* **coherent** — support is consistent with the parents' and the sons'
  support. Those are F2.c's `review_owners_coherent_parents` / `_sons`.

`review_arcConsistent` assembles the four. Nothing in it is new mathematics;
what is new is the reading — that three results proved for unrelated reasons
are the three clauses of one standard notion.

## What step (3) still needs, precisely

CCJ is a theorem about a CSP's own support sets. What is arc-consistent here
are the `owners` tables. To apply CCJ they must *be* the support sets, and
that is two inclusions of very different difficulty:

* `owners ⊇ support` — the tables never drop a genuine support. This is the
  preservation work of `CleanInvalid.lean` / `Coherence.lean`, already done.
* `owners ⊆ support` — the tables hold nothing spurious, i.e. the propagation
  is strong enough to have reached the true AC fixpoint. **Not proved**, and
  it is the same "prune enough" direction that the no-zombies half has needed
  all along.

So step (2) is done and step (3) is blocked on exactly one inclusion — the
same one that has been the open half since v11.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

/-- `is_valid_node`'s owners clause, isolated from the parents/sons clauses:
it holds in every branch. -/
theorem owners_ok_of_isValidNode (g : GPathM) (n : PNodeM) (h : isValidNode g n = true) :
    (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry n.owners k) = true := by
  simp only [isValidNode] at h
  split at h
  · split at h
    · exact h
    · exact (Bool.and_eq_true _ _).mp h |>.1
  · split at h
    · exact (Bool.and_eq_true _ _).mp h |>.1
    · exact (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1 |>.1

-- ============================================================
-- Arc consistency, in the algorithm's own terms
-- ============================================================

/-- **Arc consistency.** The CSP is: variables = steps, the domain of step `k`
= the nodes at step `k`, and a node's `owners` at step `j` is its support
table for step `j`. Arc consistency then has three clauses, and each is
something the algorithm already enforces. -/
structure ArcConsistent (reqOf : NodeId → List NodeId) (g : GPathM) : Prop where
  /-- Every surviving node has support at every step below `current_step`.
  This is exactly `is_valid_node`'s owners clause. -/
  supported : ∀ pid n, g.node? pid = some n →
    ∀ k, 0 ≤ k → k < g.current_step → hasStepEntry n.owners k = true
  /-- At a step some requirement names, the support is narrowed to that
  requirement — the "1" of 0/1/all. This is lemma L1. -/
  pinned : ReqFiltered reqOf g
  /-- Support is consistent with the parents' support (top-down pass). -/
  coherent_parents : ∀ k ∈ intRange 1 (g.current_step - 1),
    ∀ id ∈ ((g.line k).map (·.id)), ∀ d, g.node? id = some d →
      intersectOwners d.owners (unionOwnersOf g d.parents) = d.owners
  /-- Support is consistent with the sons' support (bottom-up pass). -/
  coherent_sons : ∀ k ∈ intRange 0 (g.current_step - 2),
    ∀ id ∈ ((g.line k).map (·.id)), ∀ d, g.node? id = some d →
      intersectOwners d.owners (unionOwnersOf g d.sons) = d.owners

/-- **The support clause: `review`'s fixpoint establishes it.** -/
theorem review_arcSupported (g : GPathM) (h : isValid (review g) = true)
    (pid : PathNodeId) (n : PNodeM) (hn : (review g).node? pid = some n)
    (k : Int) (hlo : 0 ≤ k) (hhi : k < (review g).current_step) :
    hasStepEntry n.owners k = true := by
  have hall := owners_ok_of_isValidNode _ n (review_node_valid g h pid n hn)
  simp only [List.all_eq_true] at hall
  exact hall k (mem_intRange hlo (by omega))

/-- **`review`'s fixpoint is arc consistent.** All four clauses come from work
already done: the support clause from F2.c's per-node form, the pinned clause
from lemma L1, the two coherence clauses from F2.c's per-node form as well. -/
theorem review_arcConsistent (reqOf : NodeId → List NodeId) (g : GPathM)
    (h : isValid (review g) = true) (hreach : Reachable reqOf (review g)) :
    ArcConsistent reqOf (review g) where
  supported := review_arcSupported g h
  pinned := L1 reqOf hreach
  coherent_parents := fun k hk id hid d hd =>
    review_owners_coherent_parents g h k hk id hid d hd
  coherent_sons := fun k hk id hid d hd =>
    review_owners_coherent_sons g h k hk id hid d hd

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.review_arcConsistent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_arcConsistent

/-- info: 'AbsSat.GraphPath.Model.review_arcSupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_arcSupported

end AbsSat.GraphPath.Model
