-- lean_project/AbsSat/GraphPath/Model/PureDriverPins.lean
import AbsSat.GraphPath.Model.PureDriverImproves
import AbsSat.GraphPath.Model.IdSeparator

/-!
# The driver with the pin prune

`PureDriverImproves` restricts the global owners at the earlier clause steps
that share a variable with the destination `d`. This driver goes one step
further before the review: everything whose id contradicts one of `d`'s pins
(`IdSeparator.IdContradicts`, read as a `Bool` — the id's own map node, its
parent's, and both steps of every variable) is removed at three levels:

1. the global owners;
2. the nodes, together with the links that point at them;
3. the entries of every remaining node's owners table.

`FixAgreeInv.FixAgree` says a node and its owners never fix a variable
differently, so an owners table has no pairwise conflict of its own: the only
pairwise conflicts a send introduces are with `d`'s pins, and this prune removes
all of them before the review runs.

    upFilteringPin φ g d = up (filterAll (pinPrune φ d (filterWeakAll g ws)) reqs) d

Measurement only for now: no theorems, and `SatMachinePureImproves` is unchanged.
`lake exe improves-diff` compares the three drivers.
-/

namespace AbsSat.GraphPath.Model.PureDriverPins

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (mapSons)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.IdSeparator (fixes varVal)
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit pureRun)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeakAll pureRunW)

/-- The `(variable, value)` pairs `d` pins. -/
def pinValues (φ : Cnf) (d : NodeId) : List (Int × Int) :=
  (reqOfCnf φ d).filterMap (varVal φ)

/-- `IdContradicts`, as a `Bool`, against precomputed pin values. -/
def contradictsB (φ : Cnf) (pvs : List (Int × Int)) (w : PathNodeId) : Bool :=
  (fixes φ w).any (fun vv => pvs.any (fun pv => pv.1 == vv.1 && pv.2 != vv.2))

/-- Remove every global owner, node, link and owners entry whose id contradicts a pin of `d`. -/
def pinPrune (φ : Cnf) (d : NodeId) (g : GPathM) : GPathM :=
  let bad := contradictsB φ (pinValues φ d)
  let nodes := (g.nodes.filter (fun n => !bad n.id)).map (fun n =>
    { n with
      owners := n.owners.filter (fun q => !bad q),
      parents := n.parents.filter (fun p => !bad p),
      sons := n.sons.filter (fun s => !bad s) })
  { g with nodes := nodes, gowners := g.gowners.filter (fun q => !bad q) }

/-- Weak filter, pin prune, hard requirements and review, then UP. -/
def upFilteringPin (φ : Cnf) (g : GPathM) (d : NodeId) (title : String) : GPathM :=
  up (filterAll (pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d))) (reqOfCnf φ d)) d title

def sendToP (φ : Cnf) (g : GPathM) (next : PureLine) (d : NodeId) : PureLine :=
  if isValid (upFilteringPin φ g d "") then insertPure next d (upFilteringPin φ g d "") else next

def sendAllP (φ : Cnf) (kv : NodeId × GPathM) (next : PureLine) : PureLine :=
  (mapSons φ kv.1.step kv.1.index).foldl (sendToP φ kv.2) next

def pureAdvanceP (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv => sendAllP φ kv next) []

def pureStepsP (φ : Cnf) : Nat → PureLine → PureLine
  | 0, line => line
  | n + 1, line => pureStepsP φ n (pureAdvanceP φ line)

def pureRunP (φ : Cnf) : PureLine := pureStepsP φ (stepCount φ - 1).toNat (pureInit φ)

-- ============================================================
-- Verdicts against the other drivers and the oracle
-- ============================================================

private def pos (v : Nat) : Lit := ⟨v, true⟩
private def neg (v : Nat) : Lit := ⟨v, false⟩

private def sat3 : Cnf :=
  { nVars := 4,
    clauses := [⟨pos 0, pos 1, pos 2⟩, ⟨neg 0, pos 1, pos 3⟩, ⟨pos 0, neg 1, neg 2⟩,
                ⟨neg 1, neg 2, neg 3⟩] }

private def unsat3 : Cnf :=
  { nVars := 3,
    clauses := [⟨pos 0, pos 1, pos 2⟩, ⟨pos 0, pos 1, neg 2⟩, ⟨pos 0, neg 1, pos 2⟩,
                ⟨pos 0, neg 1, neg 2⟩, ⟨neg 0, pos 1, pos 2⟩, ⟨neg 0, pos 1, neg 2⟩,
                ⟨neg 0, neg 1, pos 2⟩, ⟨neg 0, neg 1, neg 2⟩] }

private def verdicts (φ : Cnf) : Bool × Bool × Bool × Bool :=
  (!(pureRunP φ).isEmpty, !(pureRunW φ).isEmpty, !(pureRun φ).isEmpty, !(bruteForceSat φ).isEmpty)

#guard verdicts sat3 == (true, true, true, true)
#guard verdicts unsat3 == (false, false, false, false)

end AbsSat.GraphPath.Model.PureDriverPins
