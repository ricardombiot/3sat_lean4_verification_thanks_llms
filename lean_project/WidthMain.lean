-- lean_project/WidthMain.lean
import AbsSat.GraphPath.Model.WidthProbe

/-- `lake exe width <file.cnf> ...` — reports map size and machine width. -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.println "usage: lake exe width <file.cnf> ..."
    return 1
  for path in args do
    AbsSat.GraphPath.Model.WidthProbe.report path
  return 0
