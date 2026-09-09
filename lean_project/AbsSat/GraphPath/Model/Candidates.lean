-- lean_project/AbsSat/GraphPath/Model/Candidates.lean
import AbsSat.GraphPath.Model.GownersNodes
import AbsSat.GraphPath.Model.ArcConsistency

/-!
**What `FilteredChain` can now assume: the candidate sets are never empty.**

`FilteredChain` asks for a `ChainSound` chain of `filterAll g reqs`. A chain is
a *selection* — one node per step — so before asking whether a coherent
selection exists, it is worth knowing whether there is anything to select at
all. v25's `GownersAreNodes` makes that answerable, and the answer is yes, at
two levels:

* **globally** — every step holds a node (`GownersNodes.node_at_every_step`);
* **relative to any node** — every surviving node *owns* a node at every step
  (`candidate_at_step` below).

The second is the one that matters, because a chain's members must be owners
of one another. It says: pick any node you like, and at every other step its
own support is non-empty *and consists of real nodes*. Before v25 the second
half of that was missing — `degenerate` is exactly a graph where the support
is non-empty and consists of nothing at all.

**What that leaves.** The domains of the constraint problem are non-empty and
concrete. What is open is that a **coherent selection** across them exists:
parent-linked between consecutive steps, and pairwise co-owned. That is
`FilteredChain`, and this module does not close it — it removes the part of it
that was about emptiness rather than about choice.
-/

namespace AbsSat.GraphPath.Model.Candidates

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.GownersNodes (GN GN_filterAll GN_reachable hasNode_iff)

variable (reqOf : NodeId → List NodeId)

-- ============================================================
-- An owner of a surviving node is itself a node
-- ============================================================

/-- At a valid `review` fixpoint, a node's owners are global owners
(`owners_mem_gowners`), and global owners are nodes (v25). So **every owner of
a surviving node is a surviving node.** -/
theorem owner_mem_gowners (h : GPathM) (hv : isValid (review h) = true)
    (pid : PathNodeId) (n : PNodeM) (hn : (review h).node? pid = some n)
    (q : PathNodeId) (hq : q ∈ n.owners)
    (hlo : 0 ≤ q.id.step) (hhi : q.id.step < (review h).current_step) :
    q ∈ (review h).gowners :=
  owners_mem_gowners (review h) n (review_owners_within_gowners h hv pid n hn) q hq
    (hasStepEntry_of_isValid (review h) hv q.id.step hlo hhi)

theorem owner_is_node (h : GPathM) (hv : isValid (review h) = true)
    (hgn : GN (review h))
    (pid : PathNodeId) (n : PNodeM) (hn : (review h).node? pid = some n)
    (q : PathNodeId) (hq : q ∈ n.owners)
    (hlo : 0 ≤ q.id.step) (hhi : q.id.step < (review h).current_step) :
    ((review h).node? q).isSome = true :=
  (hasNode_iff (review h) q).mp (hgn q (owner_mem_gowners h hv pid n hn q hq hlo hhi))

-- ============================================================
-- Every node owns a node at every step
-- ============================================================

/-- **The candidate set at step `k`, seen from `pid`, is non-empty and made of
real nodes.** The support clause of `isValidNode` gives an owner at `k`; v25
turns it into a node.

This is the domain-non-emptiness of the constraint problem, and it is what
`degenerate` failed: there the support was non-empty and named nothing. -/
theorem candidate_at_step (h : GPathM) (hv : isValid (review h) = true)
    (hgn : GN (review h))
    (pid : PathNodeId) (n : PNodeM) (hn : (review h).node? pid = some n)
    (k : Int) (hlo : 0 ≤ k) (hhi : k < (review h).current_step) :
    ∃ q ∈ ownersAt n.owners k, ((review h).node? q).isSome = true ∧ q.id.step = k := by
  have hvalid := review_node_valid h hv pid n hn
  have hall := owners_ok_of_isValidNode (review h) n hvalid
  have hentry : hasStepEntry n.owners k = true :=
    List.all_eq_true.mp hall k (mem_intRange hlo (by omega))
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hentry
  have hstep : q.id.step = k := eq_of_beq hqs
  refine ⟨q, List.mem_filter.mpr ⟨hq, hqs⟩, ?_, hstep⟩
  exact owner_is_node h hv hgn pid n hn q hq (by rw [hstep]; exact hlo)
    (by rw [hstep]; exact hhi)

-- ============================================================
-- Both, for the graphs the obligation is about
-- ============================================================

/-- Same, phrased on `filterAll g reqs` — where `FilteredChain` lives. -/
theorem candidate_at_step_filterAll (g : GPathM) (reqs : List NodeId)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true)
    (pid : PathNodeId) (n : PNodeM) (hn : (filterAll g reqs).node? pid = some n)
    (k : Int) (hlo : 0 ≤ k) (hhi : k < (filterAll g reqs).current_step) :
    ∃ q ∈ ownersAt n.owners k,
      ((filterAll g reqs).node? q).isSome = true ∧ q.id.step = k :=
  candidate_at_step _ hv (GN_filterAll g reqs (GN_reachable reqOf g hreach)) pid n hn k hlo hhi

/-- **The domains are non-empty and concrete.** Every step holds a node, and
every node's support at every step holds a node. What `FilteredChain` still
owes is a *coherent selection* among them — parent-linked and pairwise
co-owned — not the existence of candidates. -/
theorem domains_nonempty (g : GPathM) (reqs : List NodeId)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true) :
    (∀ k, 0 ≤ k → k < (filterAll g reqs).current_step →
      ∃ n ∈ (filterAll g reqs).nodes, n.id.id.step = k) ∧
    (∀ pid n, (filterAll g reqs).node? pid = some n →
      ∀ k, 0 ≤ k → k < (filterAll g reqs).current_step →
        ∃ q ∈ ownersAt n.owners k,
          ((filterAll g reqs).node? q).isSome = true ∧ q.id.step = k) :=
  ⟨fun k hlo hhi => GownersNodes.node_at_every_step reqOf g reqs hreach hv k hlo hhi,
   fun pid n hn k hlo hhi =>
     candidate_at_step_filterAll reqOf g reqs hreach hv pid n hn k hlo hhi⟩

/-- **`ChainG`'s third clause comes free for any chain drawn from a node's own
support.** A chain whose members are all owners of one surviving node
automatically lives inside `gowners` — so of `ChainSound`'s four extra
conditions beyond `IsChain ∧ PairwiseOwned`, this one is already paid. -/
theorem chainG_gowners_free (h : GPathM) (hv : isValid (review h) = true)
    (pid : PathNodeId) (n : PNodeM) (hn : (review h).node? pid = some n)
    (sel : Int → PathNodeId)
    (hsel : ∀ k, 0 ≤ k → k < (review h).current_step → sel k ∈ ownersAt n.owners k) :
    ∀ k, 0 ≤ k → k < (review h).current_step → sel k ∈ (review h).gowners := by
  intro k hlo hhi
  have hmem := hsel k hlo hhi
  have hq := List.mem_filter.mp hmem
  have hstep : (sel k).id.step = k := eq_of_beq hq.2
  exact owner_mem_gowners h hv pid n hn (sel k) hq.1 (by rw [hstep]; exact hlo)
    (by rw [hstep]; exact hhi)

/-- info: 'AbsSat.GraphPath.Model.Candidates.candidate_at_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms candidate_at_step

/-- info: 'AbsSat.GraphPath.Model.Candidates.domains_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms domains_nonempty

end AbsSat.GraphPath.Model.Candidates
