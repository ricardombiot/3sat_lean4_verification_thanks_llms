-- Pure executable SAT machine
-- Combines GPathM (pure graph paths) with PureDriver (pure loop)
-- Provides deterministic, debuggable step-by-step execution

import AbsSat.GraphPath.Model.GPathM
import AbsSat.GraphPath.Model.PureDriver
import AbsSat.Cnf.Formula
import AbsSat.GraphMap.CnfMap
import AbsSat.Utils.Alias

namespace AbsSat.SatMachine.PureSatMachine

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphMap.CnfMap

/-- Pure executable SAT machine state.
    Stores immutable CNF and timeline (list of GPathM states per step).
    All operations are pure functions with deterministic results. -/
structure SatMachinePure where
  /-- The CNF formula (immutable, arithmetic encoding) -/
  cnf : Cnf
  /-- Timeline: List of "rows" (PureLine = states keyed by map node)
      Index corresponds to step number -/
  timeline : List PureLine
  /-- Current execution step (0-indexed) -/
  current_step : Nat
  deriving Repr

/-- Initialize pure machine: create seed states at step 0 -/
def init_pure (cnf : Cnf) : SatMachinePure where
  cnf := cnf
  timeline := [pureInit cnf]
  current_step := 0

/-- Execute one step: advance all states from step k to step k+1 -/
def step_pure (m : SatMachinePure) : SatMachinePure :=
  let final_step := (stepCount m.cnf).toNat
  if m.current_step >= final_step - 1 then
    m  -- Already at final step, no-op
  else
    let current_line :=
      if m.current_step < m.timeline.length then
        m.timeline[m.current_step]!
      else
        []
    let next_line := pureAdvance m.cnf current_line
    {
      cnf := m.cnf
      timeline := m.timeline ++ [next_line]
      current_step := m.current_step + 1
    }

/-- Run until completion with fuel-based recursion -/
def run_pure_fuel (cnf : Cnf) : Nat → SatMachinePure → SatMachinePure
  | 0, m => m
  | fuel + 1, m =>
    let final_step := (stepCount cnf).toNat
    if m.current_step >= final_step - 1 then
      m
    else
      run_pure_fuel cnf fuel (step_pure m)

/-- Complete pure execution: initialize and run to completion -/
def run_pure (cnf : Cnf) : SatMachinePure :=
  let final_step := (stepCount cnf).toNat
  run_pure_fuel cnf final_step (init_pure cnf)

/-- Get solution count: number of valid states at final step -/
def solution_count (m : SatMachinePure) : Nat :=
  if m.timeline.isEmpty then
    0
  else
    let final_line := m.timeline[m.timeline.length - 1]!
    final_line.length

/-- Check if machine reached satisfiable state
    A formula is UNSAT if the final timeline is empty (no valid solutions reached final step)
    A formula is SAT if there are any states at the final step -/
def is_satisfiable (m : SatMachinePure) : Bool :=
  if m.timeline.isEmpty then
    false
  else
    let final_line := m.timeline[m.timeline.length - 1]!
    !final_line.isEmpty

end AbsSat.SatMachine.PureSatMachine
