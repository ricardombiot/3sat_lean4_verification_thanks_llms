-- lean/improves_bin/AbsSatBin/GraphPath/Model/DriverBin.lean
import AbsSatBin.GraphPath.Model.UpBin
import AbsSatBin.GraphMap.CnfMapBin

/-!
# The pure machine over the bin map

`lean_project`'s `PureDriver` with three changes, each the Julia one (`sat_machine.jl`):

* requirements come from `CnfMapBin.reqOf`;
* destinations come from `CnfMapBin.sonsOf` (`map_node.sons`), so a positive variable node is
  sent only to the negation node it agrees with;
* the UP is `upFilteringW … (isProhibited φ)` (`map_prohibited(machine.gmap)`).

Definitions only; the invariants of `PureDriver` come later, once the UP lemmas they consume
are re-proved for `addNodeW`.
-/

namespace AbsSatBin.GraphPath.Model.DriverBin

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM

abbrev PureLine := List (NodeId × GPathM)

/-- States arriving at the same map node are merged (`CollectionTimeline.impact!`). -/
def insertPure (line : PureLine) (key : NodeId) (g : GPathM) : PureLine :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, existing) =>
    line.map (fun kv => if kv.1 == key then (key, doJoin existing g) else kv)
  | none => line ++ [(key, g)]

/-- The bin `send_to_destine!`: filter by the destination's requirements, UP skipping the
prohibited windows, keep the state only if it is still valid. -/
def sendTo (φ : Cnf) (g : GPathM) (next : PureLine) (d : NodeId) : PureLine :=
  let g' := upFilteringW g (reqOf φ d) d "" (isProhibited φ)
  if isValid g' then insertPure next d g' else next

/-- Send one state to every son of its origin (`send_to_destine_by_origin!`). -/
def sendAll (φ : Cnf) (kv : NodeId × GPathM) (next : PureLine) : PureLine :=
  (sonsOf φ kv.1).foldl (sendTo φ kv.2) next

def pureAdvance (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv => sendAll φ kv next) []

def pureInit (φ : Cnf) : PureLine :=
  (mapNodes φ 0).foldl
    (fun line id => insertPure line id (upW GPathM.empty id "" (isProhibited φ))) []

def pureSteps (φ : Cnf) : Nat → PureLine → PureLine
  | 0, line => line
  | n + 1, line => pureSteps φ n (pureAdvance φ line)

/-- The whole run. An empty result is the UNSAT answer. -/
def pureRun (φ : Cnf) : PureLine := pureSteps φ (stepCount φ - 1).toNat (pureInit φ)

-- ============================================================
-- Checks the tests and the harness read
-- ============================================================

/-- No node below the top is left without a son: what Julia's `GRAVE ERROR READER` detects
(error 4 of `bin-map_informe_errores.md`). -/
def noDeadNodes (g : GPathM) : Bool :=
  g.nodes.all (fun n => n.id.id.step == g.current_step - 1 || !n.sons.isEmpty)

/-- The brute-force verdict, for small formulas. -/
def bruteSat (φ : Cnf) : Bool :=
  (List.range (2 ^ φ.nVars)).any (fun m => satB (fun v => m.testBit v) φ)

-- ============================================================
-- Tests: the index-sensitive cases
-- ============================================================

section Examples

private def pos (v : Nat) : Lit := { v := v, pos := true }
private def neg (v : Nat) : Lit := { v := v, pos := false }

/-- `x₀ ∨ x₁ ∨ x₁` over two variables: steps `0` F, `1..4` variables, `5` F,
`6,7,8` = `L1,L2,L3`, `9` F. -/
private def φOr : Cnf := { nVars := 2, clauses := [{ l1 := pos 0, l2 := pos 1, l3 := pos 1 }] }

/-- `(x ∨ x ∨ x) ∧ (¬x ∨ ¬x ∨ ¬x)`: UNSAT, and every branch dies on an empty row. -/
private def φUnsat : Cnf :=
  { nVars := 1, clauses := [{ l1 := pos 0, l2 := pos 0, l3 := pos 0 },
                            { l1 := neg 0, l2 := neg 0, l3 := neg 0 }] }

private def nid (s i : Int) : NodeId := { step := s, index := i }

def run_tests : IO Unit := do
  -- The map steps of φOr are where the table says they are.
  assert! stepCount φOr == 10
  assert! clauseStep φOr 0 0 == 6 && clauseStep φOr 0 2 == 8
  -- The window is recognised on the *shifted* identifier, most recent first: the L2 node
  -- whose own parent is L1=0, shifted onto L3=0.
  let last00 : PathNodeId := { id := nid 7 0, parent_id := some (nid 6 0), gparent_id := some (nid 5 0) }
  let last10 : PathNodeId := { id := nid 7 0, parent_id := some (nid 6 1), gparent_id := some (nid 5 0) }
  assert! isProhibited φOr (shiftPid last00 (nid 8 0))
  assert! !isProhibited φOr (shiftPid last00 (nid 8 1))
  assert! !isProhibited φOr (shiftPid last10 (nid 8 0))
  -- One step too early (the L2 step) is never prohibited, even with zeros everywhere.
  let at6 : PathNodeId := { id := nid 6 0, parent_id := some (nid 5 0), gparent_id := some (nid 4 1) }
  assert! !isProhibited φOr (shiftPid at6 (nid 7 0))

  -- φOr is SAT; the run ends at the top fusion with one state.
  let r := pureRun φOr
  assert! r.length == 1
  match r with
  | [(top, g)] =>
    assert! top == nid 9 0
    assert! isValid g
    -- Error 4: the L2=0 node reached from L1=0 lost its only son (the window) and was pruned.
    assert! !(g.nodes.any (fun n => n.id.id == nid 7 0 && n.id.parent_id == some (nid 6 0)))
    assert! noDeadNodes g
    -- Three solutions: (x₀,x₁) ∈ {01, 10, 11}. Both values of x₀ survive at step 1.
    assert! (g.line 1).length == 2
  | _ => assert! false

  -- Error 3: UNSAT, every branch dies on an empty row, nothing reaches the top.
  assert! (pureRun φUnsat).isEmpty
  assert! !bruteSat φUnsat

  IO.println "All DriverBin tests passed!"

#eval run_tests

end Examples

end AbsSatBin.GraphPath.Model.DriverBin
