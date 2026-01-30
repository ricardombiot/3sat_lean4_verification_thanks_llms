-- lean_project/AbsSat/Db/Machine/Cols/ColTimeline.lean
import Std.Data.HashMap
import AbsSat.Utils.Alias
import AbsSat.GraphPath.GraphPath
import AbsSat.Db.Machine.Cols.ColTimelineStep

namespace AbsSat.Db.Machine.Cols.ColTimeline

open AbsSat.Utils.Alias
open AbsSat.GraphPath
open AbsSat.Db.Machine.Cols.ColTimelineStep

structure ColTimeline where
  table : Std.HashMap Step ColTimelineStep

instance : Repr ColTimeline where
  reprPrec t _ := "ColTimeline(" ++ repr t.table.toList ++ ")"

def new : ColTimeline := {
  table := {}
}

def get_step (timeline : ColTimeline) (step : Step) : Option ColTimelineStep :=
  timeline.table.get? step

def get_counter_graphs_step (timeline : ColTimeline) (step : Step) : Int :=
  match get_step timeline step with
  | some timeline_step => timeline_step.counter_graphs
  | none => 0

def remove_line! (timeline : ColTimeline) (step : Step) : ColTimeline :=
  { timeline with table := timeline.table.erase step }

def get_gpath! (timeline : ColTimeline) (step : Step) (map_node_id : NodeId) : Option GPath :=
  match get_step timeline step with
  | some timeline_step => ColTimelineStep.get_gpath! timeline_step map_node_id
  | none => none

def get_if_dontexiste_create_it! (timeline : ColTimeline) (step : Step) : (ColTimeline × ColTimelineStep) :=
  match get_step timeline step with
  | some s => (timeline, s)
  | none =>
    let new_step := ColTimelineStep.new
    let new_timeline := { timeline with table := timeline.table.insert step new_step }
    (new_timeline, new_step)

-- Now IO because ColTimelineStep.impact! is IO
def impact! (timeline : ColTimeline) (step : Step) (gpath : GPath) : IO ColTimeline := do
  let (timeline_with_step, timeline_step) := get_if_dontexiste_create_it! timeline step
  let updated_step ← ColTimelineStep.impact! timeline_step gpath
  pure { timeline_with_step with table := timeline_with_step.table.insert step updated_step }

-- IO because GPath.new and impact! are IO
def init_gpath_seed! (timeline : ColTimeline) (node_id : NodeId) (title : String) : IO ColTimeline := do
  let gpath ← GPath.new
  -- do_up! is IO Unit.
  do_up! gpath node_id title
  let step0 : Step := 0
  impact! timeline step0 gpath

def for_each_gpath (timeline : ColTimeline) (step : Step) (fn_each : GPath -> IO Unit) : IO Unit := do
  match get_step timeline step with
  | some timeline_step => ColTimelineStep.for_each_gpath timeline_step fn_each
  | none => pure ()

section Theorems

  theorem new_is_empty : (new).table.isEmpty := by
    simp [new]

  theorem get_counter_graphs_step_of_new (step : Step) :
    get_counter_graphs_step new step = 0 := by
    simp [get_counter_graphs_step, get_step, new]
    -- get? empty is none -> 0

end Theorems

section Examples

  def run_tests : IO Unit := do
    let timeline := new
    assert! (get_counter_graphs_step timeline 0) == 0

    let step1_data : ColTimelineStep := { table := {}, counter_graphs := 5 }
    let timeline := { timeline with table := timeline.table.insert 1 step1_data }
    assert! (get_counter_graphs_step timeline 1) == 5
    assert! (get_counter_graphs_step timeline 0) == 0

    IO.println "All ColTimeline tests passed!"

  #eval run_tests

end Examples

end AbsSat.Db.Machine.Cols.ColTimeline
