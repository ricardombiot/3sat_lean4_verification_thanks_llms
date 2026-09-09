-- lean_project/AbsSat/GraphPath/Model/Ownership.lean
import AbsSat.GraphPath.Model.PathExists

/-!
**The ownership relation itself, and why `PairwiseOwned` is a different kind of
statement from everything proved so far.**

v27 closed `IsChain`: a path exists. What it does not give is that the path is
**co-owned**, and that is the last piece of `ChainSound` with mathematical
content in it. This module measures the relation the property is about, records
what holds and what does not, and proves exactly what the cheap shortcut would
have bought.

## What `lake exe extend --owners` reports

Over every valid state the machine holds:

Over a campaign of 80 random instances — 7,800 valid states, 259,187 nodes:

| property | violations |
|---|---|
| **`nodes ⊆ gowners`** — every node's id is a global owner | **0** |
| **self-ownership** — every node owns itself | **0** |
| **symmetry** — `q` owns `n` ⟹ `n` owns `q` | **1,364**, in 19 of 80 instances |
| **support clique** — the owners of one node own each other | **63,917,242**, in 80 of 80 |

The first two are candidate invariants worth proving, and they are stated
below. The last two are refuted.

**A correction, recorded because it was mine.** An earlier version of this
docstring reported symmetry as holding with zero violations. That came from
four hand-picked instances; the campaign refutes it. Four instances is not a
measurement, and there was a campaign harness sitting right there. The
mechanism is visible in hindsight: `reviewNode` intersects a node's owners
against the union over its *neighbours*, which is not a symmetric operation, so
`q` can be pruned from `n`'s owners while `n` stays in `q`'s.

## Why the refutation matters

`SupportClique_gives_PairwiseOwned` below proves that if a node's support were
a clique, any chain drawn from that support would be co-owned **for free** —
and v27 already builds paths. So the two together would have closed
`ChainSound`. They do not, because the clique fails, and it fails by a wide
margin: two nodes can both be compatible with `t` and incompatible with each
other. That *is* the Helly problem, stated in the machine's own vocabulary.

## The shape of what is left

Every obligation this project has discharged was **local**: a property of one
node, or of one operation, preserved step by step. `PairwiseOwned` is not. It
is a property of a *global selection*, and the clique measurement says it does
not reduce to a local one by way of a single node's support. That is why no
amount of further invariants will produce it.
-/

namespace AbsSat.GraphPath.Model.Ownership

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- Three properties that hold, stated for the record
-- ============================================================

/-- Ownership is symmetric. ⚠ **Refuted** — `lake exe extend --randomowners`
reports 1,364 violations across 19 of 80 instances. Kept as the record of a
plausible-looking invariant that is false, and of why: the coherence pass
intersects against the union over a node's neighbours, which is not
symmetric. -/
def OwnersSymmetric (h : GPathM) : Prop :=
  ∀ pid n, h.node? pid = some n → ∀ q ∈ n.owners, ∀ m, h.node? q = some m → pid ∈ m.owners

/-- Every node's id is a global owner — the converse of
`GownersNodes.GownersAreNodes`. `filterRequire` breaks it and `review` restores
it. **No violation over 259,187 nodes.** -/
def NodesAreGowners (h : GPathM) : Prop := ∀ n ∈ h.nodes, n.id ∈ h.gowners

/-- Every node owns itself. This is exactly `ChainSound`'s `self_owned` field,
read off the graph instead of off a chain. **No violation over 259,187
nodes** — and by `self_owned_of_SelfOwned` below, proving it discharges one of
the three conditions `ChainSound` still lacks. -/
def SelfOwned (h : GPathM) : Prop :=
  ∀ pid n, h.node? pid = some n → pid ∈ n.owners

theorem self_owned_of_SelfOwned (h : GPathM) (hso : SelfOwned h)
    (sel : Int → PathNodeId)
    (hsome : ∀ k, 0 ≤ k → k < h.current_step → (h.node? (sel k)).isSome = true) :
    ∀ k, 0 ≤ k → k < h.current_step → sel k ∈ ownersOf h (sel k) := by
  intro k hlo hhi
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hsome k hlo hhi)
  simp only [ownersOf, hn]
  exact hso (sel k) n hn

-- ============================================================
-- The shortcut, and what it would have bought
-- ============================================================

/-- The owners of one node, at distinct steps, own each other. **Refuted** —
`lake exe extend --randomowners` reports 63,917,242 violations across all 80
instances of the campaign. Stated because the next theorem shows exactly what it would
have closed. -/
def SupportClique (h : GPathM) (t : PNodeM) : Prop :=
  ∀ q₁ ∈ t.owners, ∀ q₂ ∈ t.owners, q₁.id.step ≠ q₂.id.step →
    ∀ m, h.node? q₂ = some m → q₁ ∈ m.owners

/-- **What the clique would have bought.** A chain drawn from a node's support
would be co-owned for free — and v27 already builds paths, so the two together
would have closed `ChainSound`. The clique is false, so this is the measure of
what the refutation costs, not a route. -/
theorem SupportClique_gives_PairwiseOwned (h : GPathM) (t : PNodeM)
    (hclique : SupportClique h t) (sel : Int → PathNodeId)
    (hsel : ∀ k, 0 ≤ k → k < h.current_step → sel k ∈ ownersAt t.owners k)
    (hstep : ∀ k, 0 ≤ k → k < h.current_step → (sel k).id.step = k)
    (hsome : ∀ k, 0 ≤ k → k < h.current_step → (h.node? (sel k)).isSome = true) :
    PairwiseOwned h sel := by
  intro i j hi0 hj0 hi hj hne
  have hmi := List.mem_filter.mp (hsel i hi0 hi)
  have hmj := List.mem_filter.mp (hsel j hj0 hj)
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (hsome j hj0 hj)
  have hstepne : (sel i).id.step ≠ (sel j).id.step := by
    rw [hstep i hi0 hi, hstep j hj0 hj]; exact hne
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · simp only [ownersOf, hm]
    exact hclique (sel i) hmi.1 (sel j) hmj.1 hstepne m hm
  · exact beq_iff_eq.mpr (hstep i hi0 hi)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.Ownership.SupportClique_gives_PairwiseOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SupportClique_gives_PairwiseOwned

/-- info: 'AbsSat.GraphPath.Model.Ownership.self_owned_of_SelfOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms self_owned_of_SelfOwned

end AbsSat.GraphPath.Model.Ownership
