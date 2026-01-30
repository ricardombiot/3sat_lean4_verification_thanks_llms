import Std.Data.HashMap
import AbsSat.Utils.Alias
import AbsSat.GraphPow.GraphPow

namespace AbsSat.Db.Machine.Cols.ColTimelinePowStep

open AbsSat.Utils.Alias
open AbsSat.GraphPow

structure ColTimelinePowStep where
  table : Std.HashMap NodeId GPow
  counter_graphs : Int

instance : Repr ColTimelinePowStep where
  reprPrec s _ := "ColTimelinePowStep(graphs=" ++ repr s.counter_graphs ++ ")"

def new : ColTimelinePowStep := {
  table := {},
  counter_graphs := 0
}

def get_gpath! (step : ColTimelinePowStep) (map_node_id : NodeId) : Option GPow :=
  step.table.get? map_node_id

def impact! (step : ColTimelinePowStep) (gpath : GPow) : IO ColTimelinePowStep := do
  let is_valid ← gpath.is_valid.get
  if is_valid then
    let map_parent_id? ← gpath.map_parent_id.get
    let map_node_id := match map_parent_id? with
      | some i => i
      | none => NodeId.mk 0 0

    match step.table.get? map_node_id with
    | none =>
      pure { step with
        table := step.table.insert map_node_id gpath,
        counter_graphs := step.counter_graphs + 1
      }
    | some _current_gpath =>
      -- GraphPow.do_join! placeholder logic
      pure step
  else
    pure step

def for_each_gpath (step : ColTimelinePowStep) (fn_each : GPow -> IO Unit) : IO Unit := do
  for (_, gpath) in step.table do
    fn_each gpath

end AbsSat.Db.Machine.Cols.ColTimelinePowStep
