-- lean_project/AbsSat/SatMachine/PureSatMachineImproves.lean
import AbsSat.GraphPath.Model.PureDriverImproves
import AbsSat.SatMachine.PureSatMachine

/-! # `SatMachinePureImproves` — the pure machine with the map's improvements

The same timeline wrapper as `SatMachinePure`, over `PureDriverImproves` instead
of `PureDriver`. Today the one improvement is the weak requirements of
`CnfMapImproves`: before the hard requirements and the review, every clause node
restricts the global owners at the earlier clause steps it shares variables with.

`SatMachinePure` stays the reference. This machine is where improvements are
tried; `lake exe improves-diff` runs both and compares verdicts, final lines and
review load.
-/

namespace AbsSat.SatMachine.PureSatMachineImproves

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphMap.CnfMap

structure SatMachinePureImproves where
  cnf : Cnf
  timeline : List PureLine
  current_step : Nat
  deriving Repr

def init_pure (cnf : Cnf) : SatMachinePureImproves where
  cnf := cnf
  timeline := [pureInit cnf]
  current_step := 0

def step_pure (m : SatMachinePureImproves) : SatMachinePureImproves :=
  let final_step := (stepCount m.cnf).toNat
  if m.current_step >= final_step - 1 then
    m
  else
    let current_line :=
      if m.current_step < m.timeline.length then m.timeline[m.current_step]! else []
    { cnf := m.cnf
      timeline := m.timeline ++ [pureAdvanceW m.cnf current_line]
      current_step := m.current_step + 1 }

def run_pure_fuel (cnf : Cnf) : Nat → SatMachinePureImproves → SatMachinePureImproves
  | 0, m => m
  | fuel + 1, m =>
    if m.current_step >= (stepCount cnf).toNat - 1 then m
    else run_pure_fuel cnf fuel (step_pure m)

def run_pure (cnf : Cnf) : SatMachinePureImproves :=
  run_pure_fuel cnf (stepCount cnf).toNat (init_pure cnf)

def final_line (m : SatMachinePureImproves) : PureLine :=
  m.timeline.getLastD []

def solution_count (m : SatMachinePureImproves) : Nat := (final_line m).length

def is_satisfiable (m : SatMachinePureImproves) : Bool := !(final_line m).isEmpty

end AbsSat.SatMachine.PureSatMachineImproves
