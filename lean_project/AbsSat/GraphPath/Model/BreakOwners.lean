-- lean_project/AbsSat/GraphPath/Model/BreakOwners.lean
import AbsSat.GraphPath.Model.IdClosureLevels
import AbsSat.GraphPath.Model.IdDiesProof
import AbsSat.GraphPath.Model.LitOwners
import AbsSat.GraphPath.Model.ParentOwners
import AbsSat.GraphPath.Model.IdSeparator

/-!
# Owner agreement with break: propagation to id closure

When a node loses all chains due to a break at step `k = r.step`, the owners of the node at that
step already carry the seed of contradiction: each is either directly contradicted by the pin,
or depends on an owner that is.

This establishes the connection between the operational notion of "break" and the stratified
id closure, raising nodes in steps to level 1 of `IdClosureAt`.
-/

namespace AbsSat.GraphPath.Model.BreakOwners

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.IdClosureLevels
open AbsSat.GraphPath.Model.IdDiesProof
open AbsSat.GraphPath.Model.LitOwners
open AbsSat.GraphPath.Model.ParentOwners
open AbsSat.GraphPath.Model.IdSeparator

variable (φ : Cnf)

/-! ## Core lemma: fixing contradictions via owners -/

theorem owners_level_one_all {g : GPathM}
    {n : PNodeM} (k : Int) (_h0 : 0 ≤ k) (_hk : k < g.current_step)
    {reqs : List NodeId}
    (hcontra : ∀ q ∈ ownersAt n.owners k, q ∈ g.gowners →
      IdContradicts φ reqs q) :
    ∀ q ∈ ownersAt n.owners k, q ∈ g.gowners →
      IdClosureAt φ reqs g 0 q := by
  intro q hq hqg
  exact IdClosureAt.base q (hcontra q hq hqg)

theorem owners_agreement_one {g : GPathM}
    {x : PathNodeId} {n : PNodeM} (hnx : g.node? x = some n) (k : Int)
    (_h0 : 0 ≤ k) (_hk : k < g.current_step)
    {reqs : List NodeId}
    (hcontra : ∀ q ∈ ownersAt n.owners k, q ∈ g.gowners →
      IdContradicts φ reqs q) :
    IdClosureAt φ reqs g 1 x :=
  @IdClosureAt.succ_step φ reqs g 0 x n hnx k ‹0 ≤ k› ‹k < g.current_step›
    (fun q hq hqg => owners_level_one_all φ k ‹0 ≤ k› ‹k < g.current_step› hcontra q hq hqg)

/-! ## Main theorem: owners agree with break -/

/-- When a node's owners at step k are all directly contradicted by pins,
the node itself is raised to level 1 of the id closure. -/
theorem owners_agree_with_break {g : GPathM}
    {x : PathNodeId} {n : PNodeM} (hn : g.node? x = some n) (k : Int)
    (h0 : 0 ≤ k) (hk : k < g.current_step)
    {reqs : List NodeId}
    (hcontra : ∀ q ∈ ownersAt n.owners k, q ∈ g.gowners →
      IdContradicts φ reqs q) :
    IdClosureAt φ reqs g 1 x :=
  owners_agreement_one φ hn k h0 hk hcontra

end AbsSat.GraphPath.Model.BreakOwners
