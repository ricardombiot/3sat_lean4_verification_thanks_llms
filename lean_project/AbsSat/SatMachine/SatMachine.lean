import AbsSat.GraphMap.GraphMap
import AbsSat.GraphPath.GraphPath
import AbsSat.Db.Machine.Cols.ColTimeline
import AbsSat.Utils.Alias

namespace AbsSat.SatMachine

open AbsSat.GraphMap.GraphMap
open AbsSat.GraphPath
open AbsSat.Db.Machine.Cols.ColTimeline
open AbsSat.Utils.Alias

structure MSat where
  gmap : GMap
  timeline : IO.Ref ColTimeline
  current_step : IO.Ref Step

def new (gmap : GMap) : IO MSat := do
  let timeline ← IO.mkRef AbsSat.Db.Machine.Cols.ColTimeline.new
  let current_step ← IO.mkRef 0
  pure { gmap := gmap, timeline := timeline, current_step := current_step }

def init! (machine : MSat) : IO Unit := do
  for_each_node_step machine.gmap 0 (fun map_node => do
    let id := map_node.id
    let title := map_node.title
    let timeline ← machine.timeline.get
    let new_timeline ← init_gpath_seed! timeline id title
    machine.timeline.set new_timeline
  )

def is_finished (machine : MSat) : IO Bool := do
  let current ← machine.current_step.get
  pure (machine.gmap.step - 1 == current)

def have_gpaths_step (machine : MSat) : IO Bool := do
  let current ← machine.current_step.get
  let timeline ← machine.timeline.get
  let count := get_counter_graphs_step timeline current
  pure (count > 0)

def have_solution (machine : MSat) : IO Bool := do
  let finished ← is_finished machine
  let have_paths ← have_gpaths_step machine
  pure (finished && have_paths)

def send_to_destine! (machine : MSat) (inmutable_gpath : GPath) (id_destine : NodeId) : IO Unit := do
  let map_node_destine? := get_node machine.gmap id_destine
  match map_node_destine? with
  | some map_node_destine =>
      let title := map_node_destine.title
      let requires := map_node_destine.requires

      -- Clone gpath
      let gpath ← GPath.clone inmutable_gpath
      do_up_filtering! gpath requires id_destine title

      let is_valid ← gpath.is_valid.get
      if is_valid then
          let current ← machine.current_step.get
          let next_step := current + 1

          let timeline ← machine.timeline.get
          let new_timeline ← impact! timeline next_step gpath
          machine.timeline.set new_timeline
      else
          pure ()
  | none => pure ()

def send_to_destine_by_origin! (machine : MSat) (inmutable_gpath : GPath) : IO Unit := do
  let map_parent_id? ← inmutable_gpath.map_parent_id.get
  match map_parent_id? with
  | some map_parent_id =>
      let map_node? := get_node machine.gmap map_parent_id
      match map_node? with
      | some map_node =>
         for id_destine in map_node.sons do
             send_to_destine! machine inmutable_gpath id_destine
      | none => pure ()
  | none => pure ()

def make_step! (machine : MSat) : IO Unit := do
  let current ← machine.current_step.get
  let timeline ← machine.timeline.get

  -- Iterate current step gpaths
  for_each_gpath timeline current (fun gpath => do
      send_to_destine_by_origin! machine gpath
  )

  -- Remove line
  let timeline_current ← machine.timeline.get
  let timeline_cleaned := remove_line! timeline_current current
  machine.timeline.set timeline_cleaned

  machine.current_step.modify (· + 1)

partial def execute_step! (machine : MSat) : IO Unit := do
  let finished ← is_finished machine
  let have_paths ← have_gpaths_step machine

  if !finished && have_paths then
     make_step! machine
     execute_step! machine
  else
     pure ()

def run! (machine : MSat) : IO Unit := do
  init! machine
  execute_step! machine

end AbsSat.SatMachine
