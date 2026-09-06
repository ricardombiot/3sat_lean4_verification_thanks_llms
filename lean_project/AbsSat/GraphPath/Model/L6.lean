-- lean_project/AbsSat/GraphPath/Model/L6.lean
import AbsSat.GraphPath.Model.Filter
import AbsSat.GraphPath.Model.Reachable

/-!
Bridge lemma **L6** — the total-support invariant, "no zombies"
(`formal_bridge_owners_runpure.md` §5). This is the make-or-break of the whole
bridge, and it is **not proved**. This module states it, proves the seed case,
and records exactly where the difficulty sits.

The statement has two halves:

* `Supported g` — every node the machine can still look up lies on some
  complete co-owned chain;
* `Inhabited g` — a valid graph denotes something.

**Why it is hard.** Pairwise ownership is a 2-consistency. That 2-consistency
implies a *global* chain is a Helly-type property, and it is false for
arbitrary constraint systems: arc consistency does not imply satisfiability.
The bridge document therefore predicts the proof must come from the specific
3SAT map structure (scope-1 requirements in the literal block, ≤3 required
steps per clause case).

**Where the induction breaks.** `Reachable` has three constructors. The `seed`
case is proved below. The `join` case is monotone — `join` only adds nodes,
parents and owners, and `g₁`'s nodes keep their position, so `node?` still
finds them; a chain of either side stays a chain of the join. It needs the
growth counterpart of `Pruned`, which does not exist yet.

The `up` case is the whole difficulty, and it does not reduce: a node
surviving `upFiltering` was kept because its owners still have an entry at
every step (`isValidNode`) and because the parents/sons coherence passes did
not knock it out — that is 1-consistency plus a 2-consistency, and the chain
needs a single consistent selection across *all* steps. In one line:

    L6's `up` case  ≡  L2's ⊇ direction  ≡  "filtering never kills a chain
    through a surviving node".

**Empirical status (2026-09-06).** `L6Search.lean` (driven by `lake exe
l6search`) builds states with `initSeed` / `upFiltering` / `join` over
synthetic maps whose requirements are arbitrary subject only to `Reachable`'s
own hypotheses — backward-pointing and step-distinct — with *no 3SAT
structure whatsoever*, and enumerates every candidate chain. Over 310 maps,
including states with 81 candidate selections, it found **no** valid state
without a complete co-owned chain.

That is evidence, not proof, and it cuts against the bridge document's
expectation: if L6 needed the 3SAT structure, a search over arbitrary
requirements should have broken it. Either the machine's own construction
(owners start as "everyone owns everyone" and are only ever pruned coherently)
forces the Helly property by itself, or the falsifier is not yet adversarial
enough. Both are worth knowing before investing in a proof.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

/-- **L6, "no zombies"**: every node the machine can still look up lies on
some complete co-owned chain. -/
def Supported (g : GPathM) : Prop :=
  ∀ pid n, g.node? pid = some n →
    ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ sel pid.id.step = pid

/-- The other half of L6: a valid graph denotes something. -/
def Inhabited (g : GPathM) : Prop := ∃ p, denot g p

private theorem initSeed_nodes (d : NodeId) (title : String) :
    (GPathM.initSeed d title).nodes =
      [PNodeM.mk { id := d, parent_id := none } title [] [] [{ id := d, parent_id := none }]] := by
  unfold GPathM.initSeed GPathM.up GPathM.addNode
  simp [GPathM.isValid, GPathM.empty, GPathM.intRange, GPathM.hasStepEntry]

private theorem initSeed_current (d : NodeId) (title : String) :
    (GPathM.initSeed d title).current_step = 1 := by
  unfold GPathM.initSeed GPathM.up GPathM.addNode
  simp [GPathM.isValid, GPathM.empty, GPathM.intRange, GPathM.hasStepEntry]

/-- **L6, seed case.** -/
theorem Supported_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    Supported (GPathM.initSeed d title) := by
  intro pid n hn
  have hmem : n ∈ (GPathM.initSeed d title).nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq _ pid n hn
  rw [initSeed_nodes] at hmem
  simp only [List.mem_singleton] at hmem
  subst hmem
  have hpid : ({ id := d, parent_id := none } : PathNodeId) = pid := hid
  subst hpid
  refine ⟨fun _ => { id := d, parent_id := none }, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro k hlo hhi
    rw [initSeed_current] at hhi
    refine ⟨?_, ?_⟩
    · rw [hn]; rfl
    · show d.step = k
      omega
  · intro k hlo hhi
    rw [initSeed_current] at hhi
    omega
  · intro i j hi hj hi' hj' hne
    rw [initSeed_current] at hi' hj'
    omega
  · rfl

end AbsSat.GraphPath.Model
