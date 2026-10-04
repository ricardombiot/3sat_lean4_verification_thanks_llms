import AbsSatBin.GraphPath.Model.DriverBin
import AbsSatBin.GraphPath.Model.ReaderExec
import AbsSatBin.Cnf.Dimacs

/-! `lake exe driverbin-check f1.cnf …` — runs the pure bin machine on each formula and compares
its verdict with brute force; also checks that the final state has no dead node (the condition
Julia's reader reports as `GRAVE ERROR`). Prints one TSV line per file and exits with 1 on any
disagreement. -/

open AbsSatBin.Cnf AbsSatBin.GraphPath.Model AbsSatBin.GraphPath.Model.DriverBin AbsSatBin.GraphPath.Model.PureDriver

def checkOne (path : String) : IO Bool := do
  let lines := (← IO.FS.lines path).toList
  let name := (System.FilePath.mk path).fileName.getD path
  match Dimacs.parse lines with
  | .error e => IO.println s!"{name}\tSKIP\t{e}"; return true
  | .ok φ =>
    if φ.clauses.isEmpty then IO.println s!"{name}\tSKIP\tno clauses"; return true
    let t0 ← IO.monoMsNow
    let r := pureRun φ
    let sat := !r.isEmpty
    let dead := r.any (fun kv => !noDeadNodes kv.2)
    let t1 ← IO.monoMsNow
    let reader := ReaderExec.readerVerdictW φ
    let t2 ← IO.monoMsNow
    let truth := bruteSat φ
    let ok := sat == truth && reader == truth && !dead
    IO.println s!"{name}\t{if ok then "OK" else "FAIL"}\tmachine={if sat then "SAT" else "UNSAT"}\tbrute={if truth then "SAT" else "UNSAT"}\treader={if reader then "SAT" else "UNSAT"}\tdead={dead}\tms={t1 - t0}\treader_ms={t2 - t1}"
    return ok

def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  for f in args do
    if !(← checkOne f) then bad := bad + 1
  IO.println s!"fallos={bad} de {args.length}"
  return (if bad == 0 then 0 else 1)
