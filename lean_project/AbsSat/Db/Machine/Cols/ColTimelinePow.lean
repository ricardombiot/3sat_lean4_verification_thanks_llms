-- lean_project/AbsSat/Db/Machine/Cols/ColTimelinePow.lean
import Std.Data.HashMap
import AbsSat.Utils.Alias
import AbsSat.Db.Machine.Cols.ColTimelinePowStep
import AbsSat.GraphPow.GraphPow

namespace AbsSat.Db.Machine.Cols.ColTimelinePow

open AbsSat.Utils.Alias
open AbsSat.Db.Machine.Cols.ColTimelinePowStep

structure ColTimelinePow where
  table : Std.HashMap Step ColTimelinePowStep

instance : Repr ColTimelinePow where
  reprPrec t _ := "ColTimelinePow(" ++ repr t.table.toList ++ ")"

def new : ColTimelinePow := {
  table := {}
}

def get_step (timeline : ColTimelinePow) (step : Step) : Option ColTimelinePowStep :=
  timeline.table.get? step

def get_counter_graphs_step (timeline : ColTimelinePow) (step : Step) : Int :=
  match get_step timeline step with
  | some timeline_step => timeline_step.counter_graphs
  | none => 0

def remove_line! (timeline : ColTimelinePow) (step : Step) : ColTimelinePow :=
  { timeline with table := timeline.table.erase step }

def get_gpath! (timeline : ColTimelinePow) (step : Step) (map_node_id : NodeId) : Option GPow :=
  match get_step timeline step with
  | some timeline_step => ColTimelinePowStep.get_gpath! timeline_step map_node_id
  | none => none

def get_if_dontexiste_create_it! (timeline : ColTimelinePow) (step : Step) : (ColTimelinePow × ColTimelinePowStep) :=
  match get_step timeline step with
  | some s => (timeline, s)
  | none =>
    let new_step := ColTimelinePowStep.new
    let new_timeline := { timeline with table := timeline.table.insert step new_step }
    (new_timeline, new_step)

def impact! (timeline : ColTimelinePow) (step : Step) (gpath : GPow) : IO ColTimelinePow := do
  let (timeline_with_step, timeline_step) := get_if_dontexiste_create_it! timeline step
  let updated_step ← ColTimelinePowStep.impact! timeline_step gpath
  pure { timeline_with_step with table := timeline_with_step.table.insert step updated_step }

def init_gpath_seed! (timeline : ColTimelinePow) (node_id : NodeId) (title : String) : IO ColTimelinePow := do
  let gpath ← GPow.new
  -- do_up! is IO Unit.
  GPow.do_up! gpath node_id title
  let step0 : Step := 0
  impact! timeline step0 gpath

def for_each_gpath (timeline : ColTimelinePow) (step : Step) (fn_each : GPow -> IO Unit) : IO Unit := do
  match get_step timeline step with
  | some timeline_step => ColTimelinePowStep.for_each_gpath timeline_step fn_each
  | none => pure ()

section Theorems

  theorem new_is_empty : (new).table.isEmpty := by
    simp [new]

  theorem get_counter_graphs_step_of_new (step : Step) :
    get_counter_graphs_step new step = 0 := by
    simp [get_counter_graphs_step, get_step, new]

end Theorems

section Examples

  def run_tests : IO Unit := do
    let timeline := new
    assert! (get_counter_graphs_step timeline 0) == 0
    IO.println "All ColTimelinePow tests passed!"

  #eval run_tests

end Examples

end AbsSat.Db.Machine.Cols.ColTimelinePow
