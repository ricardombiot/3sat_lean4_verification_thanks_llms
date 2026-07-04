-- lean_project/AbsSat/GraphPath/Model/Denot.lean
import AbsSat.GraphPath.Model.GPathM

/-!
Phase F4 of `docs/plans/espejo_gpathm_lema_L1.md`: the denotation of a
GPath as the set of co-owned chains. Only definitions — proofs belong to
L2–L7 of the bridge and are out of scope here.

A chain is a selection of one `PathNodeId` per step that forms a
parent–son path through the graph and is *pairwise-owned*: every selected
node owns every other selected node.
-/

namespace AbsSat.GraphPath.Model

open AbsSat.Utils.Alias
open GPathM

def ownersOf (g : GPathM) (pid : PathNodeId) : List PathNodeId :=
  match g.node? pid with
  | some n => n.owners
  | none => []

def IsChain (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  (∀ k, 0 ≤ k → k < g.current_step →
    (g.node? (sel k)).isSome ∧ (sel k).id.step = k) ∧
  (∀ k, 0 ≤ k → k + 1 < g.current_step →
    sel k ∈ ((g.node? (sel (k + 1))).map PNodeM.parents).getD [])

def PairwiseOwned (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ i j, 0 ≤ i → 0 ≤ j → i < g.current_step → j < g.current_step → i ≠ j →
    sel i ∈ ownersAt (ownersOf g (sel j)) i

def pathOf (sel : Int → PathNodeId) (g : GPathM) : List NodeId :=
  ((intRange 0 (g.current_step - 1)).reverse.map fun k => (sel k).id)

def denot (g : GPathM) (p : List NodeId) : Prop :=
  ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ p = pathOf sel g

end AbsSat.GraphPath.Model
