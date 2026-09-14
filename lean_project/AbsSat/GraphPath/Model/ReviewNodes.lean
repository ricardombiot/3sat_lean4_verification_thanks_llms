-- lean_project/AbsSat/GraphPath/Model/ReviewNodes.lean
import AbsSat.GraphPath.Model.RemovalClosure
import AbsSat.GraphPath.Model.Fabric

/-!
# Which nodes the review keeps

`P = reqs.foldl filterRequire g` is a reachable state with its pins placed. `RemovalClosure`
proves that the review removes every node of the closure `Unsupported P`. This module proves the
other inclusion, given one hypothesis:

* `FabricOutside P` — the nodes of `P` outside the closure carry a `Fabric` (`Fabric.lean`): a
  symmetric sub-table of their owners with an entry at every step, every entry backed by a parent
  and by a son inside the table.

`Fabric.FOk_review` — proved for the machine's review — keeps every member of a fabric alive. So:

* `fabric_survives` — a member of a fabric of `P` is a node after `filterAll`.
* `removed_unsupported` — **inclusion 1**: under `FabricOutside`, a node the review removes is
  unsupported.
* `survives_iff` — under `FabricOutside`, a node of `P` survives the filter **iff** it is not
  unsupported: the review keeps exactly `P ∖ R`.

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210): the greatest fabric inside `P ∖ R`
keeps all of `P ∖ R` in 6,111 of 6,111 valid filtered states, and every state the driver keeps
carries a fabric over all its nodes (3,774 of 3,774). `FabricOutside` itself is not proved here.
-/

namespace AbsSat.GraphPath.Model.ReviewNodes

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure

/-- The nodes outside the removal closure carry a fabric. -/
def FabricOutside (P : GPathM) : Prop :=
  ∃ S T, Fabric.Fabric P S T ∧ ∀ x, (P.node? x).isSome = true → Unsupported P x ∨ S x

theorem smp_pins (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) : Sons.SMP (reqs.foldl filterRequire g) := by
  unfold Sons.SMP
  rw [foldl_filterRequire_nodes]
  exact Sons.SMP_reachable reqOf g hr

theorem notRoot_pins (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) : Parents.NotRoot (reqs.foldl filterRequire g) := by
  unfold Parents.NotRoot
  rw [foldl_filterRequire_nodes]
  exact (Parents.Shape_reachable reqOf g hr).notroot

/-- **A member of a fabric of the pinned state survives the filter.** -/
theorem fabric_survives (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) {S : PathNodeId → Prop} {T : PathNodeId → PathNodeId → Prop}
    (hfab : Fabric.Fabric (reqs.foldl filterRequire g) S T) {x : PathNodeId} (hx : S x) :
    ((filterAll g reqs).node? x).isSome = true := by
  have hok : Fabric.FOk (reqs.foldl filterRequire g) S T :=
    ⟨hfab, smp_pins reqOf g hr reqs, notRoot_pins reqOf g hr reqs⟩
  exact (Fabric.FOk_review _ S T hok).fab.node x hx

/-- **Inclusion 1.** Under `FabricOutside`, every node the review removes is unsupported. -/
theorem removed_unsupported (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hfab : FabricOutside (reqs.foldl filterRequire g)) {x : PathNodeId}
    (hx : ((reqs.foldl filterRequire g).node? x).isSome = true)
    (hgone : (filterAll g reqs).node? x = none) : Unsupported (reqs.foldl filterRequire g) x := by
  obtain ⟨S, T, hf, hcov⟩ := hfab
  rcases hcov x hx with hu | hs
  · exact hu
  · have hsurv := fabric_survives reqOf g hr reqs hf hs
    rw [hgone] at hsurv
    exact absurd hsurv (by simp)

/-- **The review keeps exactly `P ∖ R`**, under `FabricOutside`. -/
theorem survives_iff (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true)
    (hfab : FabricOutside (reqs.foldl filterRequire g)) (x : PathNodeId)
    (hx : ((reqs.foldl filterRequire g).node? x).isSome = true) :
    ((filterAll g reqs).node? x).isSome = true ↔ ¬ Unsupported (reqs.foldl filterRequire g) x := by
  constructor
  · intro hs hu
    have hnone := unsupported_removed reqOf g hr reqs hv hu
    rw [hnone] at hs
    exact absurd hs (by simp)
  · intro hnu
    obtain ⟨S, T, hf, hcov⟩ := hfab
    exact fabric_survives reqOf g hr reqs hf ((hcov x hx).resolve_left hnu)

/-- info: 'AbsSat.GraphPath.Model.ReviewNodes.removed_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms removed_unsupported

/-- info: 'AbsSat.GraphPath.Model.ReviewNodes.survives_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms survives_iff

end AbsSat.GraphPath.Model.ReviewNodes
