-- lean_project/AbsSat/GraphPath/Model/Bridge.lean
import AbsSat.GraphPath.Model.ParentId

/-!
**The bridge between the owners ledger and the parents ledger, as a theorem.**

v36 measured the two ledgers apart: 37 stale parent links and 71 stale son
links per ~328,000, because ownership pruning never unlinked a neighbour. The
author identified that as a bug and gave the intended semantics — *pruning the
owners must unlink the incompatible parents, and a node left without parents is
invalid and must go*. `GraphPath.lean` now does exactly that
(`unlink_incompatible!`), validated at 800/800 against the brute-force oracle
with verdicts and solution sets unchanged.

This module states the fix in the pure model and proves what it establishes.

## The bridge

    LinksInOwners h : every parent and every son of a node is one of its owners

Refuted before the fix (`ParentId.ParentIsOwner`, `ParentId.SonIsOwner`). After
it, `linksInOwners_relinkSelf` says the operation establishes it *by
construction*, and `pruned_unlinkIncompatible` says the operation is a
legitimate narrowing — it only ever removes links, so everything already proved
about `Pruned` carries through it.

## What is proved here, and what is not

**Proved.** The operation mirrors the executable's fix, it establishes the
bridge at the node it touches, it leaves ids and owners alone, and it is a
`Pruned` step.

**Not proved.** That `LinksInOwners` is an invariant of *every* state the
machine builds. That needs the operation wired into `cleanInvalidGo` and
`reviewNode` in the mirror, and the migration is a real piece of work:
`Pruned`, the `Fuel` measure bounds and the whole of F2.c go through (they were
done and re-done during this session), but the four `ChainSound` preservation
proofs — `CleanInvalid`, `Coherence`, `Review`, `AddNode` — each need a new
lemma, `ChainSound_unlinkIncompatible`. Its argument is known and short to
state: **a sound chain's parent link survives the unlink precisely because the
chain is co-owned**, which is `PairwiseOwned`, already a field of `ChainSound`.
Writing it in the idiom of `CleanInvalid.lean` is what remains.

Until then the mirror prunes less than the executable. The difference is
conservative, and `diffTest` validates both bands against the oracle.
-/

namespace AbsSat.GraphPath.Model.Bridge

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- The operation
-- ============================================================

/-- Keep only the links a node's own owners still allow. Mirror of the
executable's `unlink_incompatible!`, at one node. -/
def relinkSelf (n : PNodeM) : PNodeM :=
  { n with parents := n.parents.filter (fun p => n.owners.contains p),
           sons := n.sons.filter (fun s => n.owners.contains s) }

theorem relinkSelf_id (n : PNodeM) : (relinkSelf n).id = n.id := rfl

theorem relinkSelf_owners (n : PNodeM) : (relinkSelf n).owners = n.owners := rfl

/-- What the unlink does to every node: the target is re-linked against its own
owners, a neighbour the target no longer owns loses the target, and everything
else is untouched. -/
def unlinkMap (n : PNodeM) (id : PathNodeId) (m : PNodeM) : PNodeM :=
  if m.id == id then relinkSelf m
  else if n.owners.contains m.id then m
  else { m with parents := m.parents.filter (fun p => p != id),
                sons := m.sons.filter (fun s => s != id) }

theorem unlinkMap_id (n : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (unlinkMap n id m).id = m.id := by
  unfold unlinkMap; split
  · rfl
  · split <;> rfl

theorem unlinkMap_owners (n : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (unlinkMap n id m).owners = m.owners := by
  unfold unlinkMap; split
  · rfl
  · split <;> rfl

def unlinkIncompatible (g : GPathM) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some n => { g with nodes := g.nodes.map (unlinkMap n id) }

-- ============================================================
-- The bridge
-- ============================================================

/-- **The bridge.** Every parent and every son of a node is one of its owners.
Refuted before the author's fix (`ParentId.ParentIsOwner`); established by it. -/
def LinksInOwners (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, (∀ p ∈ n.parents, p ∈ n.owners) ∧ (∀ s ∈ n.sons, s ∈ n.owners)

/-- **The fix establishes the bridge, by construction.** After re-linking, a
node's parents and sons are exactly those its owners allow. -/
theorem linksInOwners_relinkSelf (n : PNodeM) :
    (∀ p ∈ (relinkSelf n).parents, p ∈ (relinkSelf n).owners) ∧
    (∀ s ∈ (relinkSelf n).sons, s ∈ (relinkSelf n).owners) := by
  constructor
  · intro p hp
    exact List.elem_iff.mp (List.mem_filter.mp hp).2
  · intro s hs
    exact List.elem_iff.mp (List.mem_filter.mp hs).2

/-- And it holds of the node the unlink acted on, inside the graph. -/
theorem linksInOwners_at (g : GPathM) (id : PathNodeId) (n : PNodeM)
    (hn : g.node? id = some n) (m : PNodeM) (hm : m ∈ (unlinkIncompatible g id).nodes)
    (hmid : m.id = id) :
    (∀ p ∈ m.parents, p ∈ m.owners) ∧ (∀ s ∈ m.sons, s ∈ m.owners) := by
  have hshape : (unlinkIncompatible g id).nodes = g.nodes.map (unlinkMap n id) := by
    simp only [unlinkIncompatible, hn]
  rw [hshape] at hm
  obtain ⟨m₀, hm₀, hEq⟩ := List.mem_map.mp hm
  have hm₀id : m₀.id = id := by rw [← unlinkMap_id n id m₀, hEq]; exact hmid
  have : unlinkMap n id m₀ = relinkSelf m₀ := by
    unfold unlinkMap; rw [if_pos (by rw [hm₀id]; exact beq_iff_eq.mpr rfl)]
  rw [← hEq, this]
  exact linksInOwners_relinkSelf m₀

-- ============================================================
-- It is a legitimate narrowing
-- ============================================================

/-- The unlink only ever removes links, so everything `Pruned` gives carries
through it. This is what makes wiring it into the passes safe. -/
theorem pruned_unlinkIncompatible (g : GPathM) (id : PathNodeId) :
    Pruned g (unlinkIncompatible g id) := by
  unfold unlinkIncompatible
  split
  · exact Pruned.refl g
  · next n _ =>
    refine ⟨rfl, rfl, fun q hq => hq, ?_⟩
    intro n' hn'
    obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hn'
    refine ⟨m, hm, ?_, ?_, ?_⟩
    · rw [← hEq]; exact unlinkMap_id n id m
    · rw [← hEq, unlinkMap_owners]; intro q hq; exact hq
    · rw [← hEq]; unfold unlinkMap; split
      · intro p hp; exact (List.mem_filter.mp hp).1
      · split
        · intro p hp; exact hp
        · intro p hp; exact (List.mem_filter.mp hp).1

/-- **What the chain contributes, and why the migration will go through.** A
sound chain's parent link survives the unlink because the chain is co-owned —
`PairwiseOwned` is already a field of `ChainSound`. Stated here at one step;
threading it through the four preservation proofs is what remains. -/
theorem chain_link_survives (g : GPathM) (sel : Int → PathNodeId)
    (howned : PairwiseOwned g sel) (k : Int) (hlo : 0 ≤ k) (hhi : k + 1 < g.current_step)
    (n : PNodeM) (hn : g.node? (sel (k + 1)) = some n) :
    sel k ∈ n.owners := by
  have hmem := howned k (k + 1) hlo (by omega) (by omega) hhi (by omega)
  simp only [ownersAt, List.mem_filter, ownersOf, hn] at hmem
  exact hmem.1

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.Bridge.linksInOwners_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linksInOwners_at

/-- info: 'AbsSat.GraphPath.Model.Bridge.pruned_unlinkIncompatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pruned_unlinkIncompatible

/-- info: 'AbsSat.GraphPath.Model.Bridge.chain_link_survives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_link_survives

end AbsSat.GraphPath.Model.Bridge
