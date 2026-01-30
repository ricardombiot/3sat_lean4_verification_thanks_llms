import AbsSat.GraphPath.GraphPath
import AbsSat.Utils.Alias
import AbsSat.Db.Path.Docs.PathDocNode

namespace AbsSat.GraphPath.GraphPathVisual

open AbsSat.GraphPath.GPath
open AbsSat.Utils.Alias

structure PathDiagram where
  graph : GPath
  dot_txt : String

def build (graph : GPath) : PathDiagram :=
  let dot_txt := "digraph G { compound=true; a -> b; }"
  { graph := graph, dot_txt := dot_txt }

def to_png (_diagram : PathDiagram) (_name : String) (_path : String := "./test_visual") : IO Unit :=
  pure ()

end AbsSat.GraphPath.GraphPathVisual
