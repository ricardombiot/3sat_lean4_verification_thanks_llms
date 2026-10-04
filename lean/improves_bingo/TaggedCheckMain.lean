import AbsSatBingo.Tagged.Defs
import AbsSatBin.Cnf.Dimacs

/-! `lake exe tagged-check f1.cnf …` — la máquina con etiquetas (fase T1 de `docs/plans/lean_row_tags.md`) contra la
fuerza bruta y contra la máquina sin etiquetas: veredicto de la máquina y del lector, y mismo estado final (vivos y
aristas de cada entrada de la línea final; en Julia la regla no quita ninguna arista en el corpus, informe v205).
Una fila TSV por fichero; sale con 1 si algo no cuadra. -/

open AbsSatBin.Cnf AbsSatBingo.Model

def checkOne (path : String) : IO Bool := do
  let name := (System.FilePath.mk path).fileName.getD path
  match Dimacs.parse (← IO.FS.lines path).toList with
  | .error e => IO.println s!"{name}\tSKIP\t{e}"; return true
  | .ok φ =>
    if φ.clauses.isEmpty then IO.println s!"{name}\tSKIP\tno clauses"; return true
    let t0 ← IO.monoMsNow
    let rT := DriverT.runT φ
    let satT := !rT.isEmpty
    let t1 ← IO.monoMsNow
    let readerT := DriverT.readerVerdictT φ
    let t2 ← IO.monoMsNow
    let r := Driver.run φ
    let same := rT.length == r.length && (rT.zip r).all (fun (a, b) =>
      a.1 == b.1 && a.2.g.alive.length == b.2.alive.length && a.2.g.edges.length == b.2.edges.length &&
      a.2.g.alive.all (b.2.alive.contains ·) && a.2.g.edges.all (fun e => b.2.hasEdge e.1 e.2))
    let tags := rT.foldl (fun s kv => s + kv.2.tags.length) 0
    let truth := Driver.bruteSat φ
    let ok := satT == truth && readerT == truth && same
    IO.println s!"{name}\t{if ok then "OK" else "FAIL"}\tmachineT={if satT then "SAT" else "UNSAT"}\tbrute={if truth then "SAT" else "UNSAT"}\treaderT={if readerT then "SAT" else "UNSAT"}\tsame_state={same}\ttags={tags}\tms={t1 - t0}\treader_ms={t2 - t1}"
    return ok

def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  for f in args do
    if !(← checkOne f) then bad := bad + 1
  IO.println s!"fallos={bad} de {args.length}"
  return (if bad == 0 then 0 else 1)
