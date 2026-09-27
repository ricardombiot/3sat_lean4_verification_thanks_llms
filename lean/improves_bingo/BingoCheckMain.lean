import AbsSatBingo.Model.Driver
import AbsSatBin.Cnf.Dimacs

/-! `lake exe bingo-check f1.cnf …` — la máquina bingo contra la fuerza bruta: veredicto de la máquina, veredicto
del lector y ningún nodo muerto en la línea final. Una fila TSV por fichero; sale con 1 si algo no cuadra. -/

open AbsSatBin.Cnf AbsSatBingo.Model

def checkOne (path : String) : IO Bool := do
  let name := (System.FilePath.mk path).fileName.getD path
  match Dimacs.parse (← IO.FS.lines path).toList with
  | .error e => IO.println s!"{name}\tSKIP\t{e}"; return true
  | .ok φ =>
    if φ.clauses.isEmpty then IO.println s!"{name}\tSKIP\tno clauses"; return true
    let t0 ← IO.monoMsNow
    let r := Driver.run φ
    let sat := !r.isEmpty
    let dead := r.any (fun kv => !Driver.noDeadNodes kv.2)
    let t1 ← IO.monoMsNow
    let reader := Driver.readerVerdict φ
    let t2 ← IO.monoMsNow
    let truth := Driver.bruteSat φ
    let ok := sat == truth && reader == truth && !dead
    IO.println s!"{name}\t{if ok then "OK" else "FAIL"}\tmachine={if sat then "SAT" else "UNSAT"}\tbrute={if truth then "SAT" else "UNSAT"}\treader={if reader then "SAT" else "UNSAT"}\tdead={dead}\tms={t1 - t0}\treader_ms={t2 - t1}"
    return ok

def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  for f in args do
    if !(← checkOne f) then bad := bad + 1
  IO.println s!"fallos={bad} de {args.length}"
  return (if bad == 0 then 0 else 1)
