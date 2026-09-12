import AbsSat.SatMachine.PureSatMachineIO

open AbsSat.SatMachine.PureSatMachineIO

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.println "Usage: pure-sat-machine [--verbose] <cnf-file>"
    IO.println ""
    IO.println "Options:"
    IO.println "  --verbose    Print step-by-step debugging output"
    IO.println ""
    IO.println "Solves a 3-SAT formula in DIMACS CNF format using pure executable machine."
  else
    match args with
    | ["--verbose", path] => solve path true
    | [path] => solve path false
    | _ => IO.println "Error: Invalid arguments"
