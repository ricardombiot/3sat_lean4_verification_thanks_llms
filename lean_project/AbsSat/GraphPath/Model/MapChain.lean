-- lean_project/AbsSat/GraphPath/Model/MapChain.lean
import AbsSat.GraphPath.Model.SelfOwn

/-!
**`PairwiseOwned` through the map's own structure — and the assembly of
everything proved so far.**

The map enters the argument through **requirements**, not through `owners`. A
requirement pins one node at one step (`GraphMap.MapReqs.Functional`: at most
one per step, the 0/1/all class), and lemma L1 (`ReqFiltered`) says the
machine's filter enforces exactly that. So the natural map-level condition on a
chain is not "its members own each other" but "its members satisfy each other's
requirements".

This module relates the two.

## What is proved: co-ownership *implies* requirement satisfaction

`reqSatisfying_of_pairwiseOwned` — a pairwise-owned chain satisfies every
requirement of every node it selects. The proof is L1 read along the chain:
pairwise ownership puts `sel req.step` inside the owners of `sel k` at
`req.step`, and L1 says that whole set projects to `req`.

This is the direction where the map's structure genuinely gives something, and
it is the direction `ChainSound_filterAll` consumes.

## What is open: the converse

`ReqSatImpliesOwned` — a requirement-satisfying chain is co-owned. **Not
proved.** v13 is the reason to be careful: the machine's `owners` tables are
narrower than the raw constraints (they intersect against the *union* over
neighbours), so satisfying the requirements does not automatically place a node
inside another's table.

## The assembly

`ChainSound_of_parts` puts together everything the last several turns proved —
`IsChain` (v27), `son_link` and `root_shape` (v29), `self_owned` (v30) — and
shows `ChainSound` follows from **exactly two** open statements:

1. a requirement-satisfying path exists **in the valid state the machine
   holds**, and
2. `ReqSatImpliesOwned`.

Everything else is discharged.

**A correction the author had to make.** An earlier version of this docstring
glossed (1) as "which, on a 3SAT map, is the formula being satisfiable". That
conflates two different things. The map with its requirements *draws* the 3SAT
expression in terms the machine understands, and **the drawing guarantees
nothing**: nothing about the map says a requirement-satisfying path has to
exist. It is the **machine** that, having processed the map and come out with a
valid set, would guarantee satisfiability — and that implication, from
validity to a readable solution, is precisely what (1) is and what is open.

And the other side is not an omission but the design: the machine may simply
fail to build the set step by step, in which case the graph goes invalid,
every obligation stated on valid graphs is vacuous, and that failure **is** the
UNSAT verdict. `Certifies.lean` places it correctly; this docstring did not.
-/

namespace AbsSat.GraphPath.Model.MapChain

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

variable (reqOf : NodeId → List NodeId)

-- ============================================================
-- Co-ownership implies requirement satisfaction
-- ============================================================

/-- A selection satisfies the requirements of the nodes it picks. This is the
map-level condition — it mentions `reqOf`, not `owners`. -/
def ReqSatisfying (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ k, 0 ≤ k → k < g.current_step → ∀ req ∈ reqOf (sel k).id,
    0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req

/-- **L1, read along a chain.** Pairwise ownership puts `sel req.step` inside
the owners of `sel k` at that step, and `ReqFiltered` says that whole set
projects to `req`. So a co-owned chain satisfies every requirement of every
node it selects. -/
theorem reqSatisfying_of_pairwiseOwned (g : GPathM) (hrf : ReqFiltered reqOf g)
    (hback : ∀ n ∈ g.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step)
    (sel : Int → PathNodeId) (hchain : IsChain g sel) (howned : PairwiseOwned g sel) :
    ReqSatisfying reqOf g sel := by
  intro k hlo hhi req hreq hrlo hrhi
  obtain ⟨hsome, hstep⟩ := hchain.1 k hlo hhi
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hnid : n.id = sel k := node?_id_eq g _ n hn
  have hmemn : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hreq' : req ∈ reqOf n.id.id := by rw [hnid]; exact hreq
  have hne : req.step ≠ k := by
    have := hback n hmemn req hreq'
    rw [hnid, hstep] at this
    omega
  have hmem := howned req.step k hrlo hlo hrhi hhi hne
  simp only [ownersAt, List.mem_filter, ownersOf, hn] at hmem
  exact hrf n hmemn req hreq' (sel req.step) hmem.1 (eq_of_beq hmem.2)

/-- **The converse — the open direction.** A chain that satisfies every
requirement is co-owned. This is where the map's 0/1/all structure would have
to enter, and v13 is the reason it does not follow for free: the `owners`
tables are narrower than the raw constraints. -/
def ReqSatImpliesOwned (g : GPathM) : Prop :=
  ∀ sel, IsChain g sel → ReqSatisfying reqOf g sel → PairwiseOwned g sel

-- ============================================================
-- The assembly
-- ============================================================

/-- **Everything proved, in one place.** `ChainSound` follows from the five
conditions the last several turns closed, plus exactly two open statements:
that a requirement-satisfying path exists **in the valid state the machine
holds** (not a property of the map — see the module docstring), and
`ReqSatImpliesOwned`.

The `gowners` hypothesis is `Ownership.NodesAreGowners` read along the chain —
measured at zero violations over 259,187 nodes, not proved. -/
theorem ChainSound_of_parts (g : GPathM)
    (hsmp : Sons.SMP g) (hrz : Sons.RootAtZero g) (hnr : Parents.NotRoot g)
    (hso : Ownership.SelfOwned g) (hri : ReqSatImpliesOwned reqOf g)
    (hpos : 0 < g.current_step)
    (sel : Int → PathNodeId) (hchain : IsChain g sel)
    (hrs : ReqSatisfying reqOf g sel)
    (hgow : ∀ k, 0 ≤ k → k < g.current_step → sel k ∈ g.gowners) :
    ChainSound g sel := by
  have howned : PairwiseOwned g sel := hri sel hchain hrs
  refine ⟨⟨hchain, howned, hgow⟩, ?_, ?_, ?_⟩
  · exact Ownership.self_owned_of_SelfOwned g hso sel (fun k hlo hhi => (hchain.1 k hlo hhi).1)
  · exact Sons.son_link_of_SMP g hsmp sel hchain
  · exact Sons.root_shape_of g hrz hnr sel hchain hpos

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.MapChain.reqSatisfying_of_pairwiseOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqSatisfying_of_pairwiseOwned

/-- info: 'AbsSat.GraphPath.Model.MapChain.ChainSound_of_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_of_parts

end AbsSat.GraphPath.Model.MapChain
