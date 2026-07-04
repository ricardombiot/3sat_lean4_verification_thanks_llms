-- lean_project/AbsSat/Db/Machine/Cols/ColTimelineStep.lean
import Std.Data.HashMap
import AbsSat.Utils.Alias
import AbsSat.GraphPath.GraphPath

namespace AbsSat.Db.Machine.Cols.ColTimelineStep

open AbsSat.Utils.Alias
open AbsSat.GraphPath

structure ColTimelineStep where
  table : Std.HashMap NodeId GPath
  counter_graphs : Int

-- Repr deriving issue with GPath refs? GPath does not derive Repr.
-- ColTimelineStep contains GPath. So we cannot derive Repr unless we ignore table.
instance : Repr ColTimelineStep where
  reprPrec s _ := "ColTimelineStep(graphs=" ++ repr s.counter_graphs ++ ")"

def new : ColTimelineStep := {
  table := {},
  counter_graphs := 0
}

def get_gpath! (step : ColTimelineStep) (map_node_id : NodeId) : Option GPath :=
  step.table.get? map_node_id

def impact! (step : ColTimelineStep) (gpath : GPath) : IO ColTimelineStep := do
  let valid ← gpath.is_valid.get
  if valid then
    let parent_id? ← gpath.map_parent_id.get

    let map_node_id := match parent_id? with
      | some i => i -- i is NodeId
      | none => { step := 0, index := 0 } -- Fallback/Error case, assuming strict typing

    match step.table.get? map_node_id with
    | none =>
      pure { step with
        table := step.table.insert map_node_id gpath,
        counter_graphs := step.counter_graphs + 1
      }
    | some current_gpath =>
      -- Two different histories converged on the same destination node
      -- (a common son of distinct earlier choices): merge the incoming
      -- gpath into the one already parked here instead of dropping it,
      -- or a whole branch of otherwise-valid candidates silently vanishes.
      AbsSat.GraphPath.do_join! current_gpath gpath
      pure { step with table := step.table.insert map_node_id current_gpath }
  else
    pure step

def for_each_gpath (step : ColTimelineStep) (fn_each : GPath -> IO Unit) : IO Unit := do
  for (_, gpath) in step.table.toList do
    fn_each gpath

end AbsSat.Db.Machine.Cols.ColTimelineStep
