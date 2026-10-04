import AbsSatBingo.Exe.Dump
import AbsSatBin.Cnf.Dimacs

/-! `lake exe bingo-dump SALIDA f.cnf [off|on]` — con modo, escribe `SALIDA/<f>.txt` en el formato de
`test_3sat/dump_forbid.jl` (FORBID, sin soluciones, con los tríos por arista) para el diferencial del modo
(`docs/plans/lean_forbid_on.md`, F2). Sin modo, corre la máquina bingo sobre la fórmula y escribe `SALIDA/<f>.txt` en el
formato de `dump_final.jl`; imprime la fila de `summary.tsv` (instance, truth, sat, sols_ok, nsols, rounds, time). -/

open AbsSatBin.Cnf AbsSatBingo.Model AbsSatBingo.Exe.Dump

def main (args : List String) : IO UInt32 := do
  match args with
  | [out, path] =>
    let name := (System.FilePath.mk path).fileName.getD path
    match Dimacs.parse (← IO.FS.lines path).toList with
    | .error _ => IO.println s!"{name}\t?\tERROR\t\t\t\t"; return 0
    | .ok φ =>
      let t0 ← IO.monoMsNow
      let line := Driver.run φ
      let sat := !line.isEmpty
      let txt := dumpRun name (Driver.bruteSat φ) sat line
      let t1 ← IO.monoMsNow
      IO.FS.createDirAll out
      IO.FS.writeFile (System.FilePath.mk out / s!"{name}.txt") txt
      IO.println s!"{name}\t{Driver.bruteSat φ}\t{sat}\t-\t-\t-\t{(t1 - t0).toFloat / 1000.0}"
      return 0
  | [out, path, mode] =>
    let name := (System.FilePath.mk path).fileName.getD path
    let m := if mode == "on" then Mode.on else Mode.off
    match Dimacs.parse (← IO.FS.lines path).toList with
    | .error _ => IO.println s!"{name}\tERROR"; return 0
    | .ok φ =>
      let t0 ← IO.monoMsNow
      let line := Driver.runM m φ
      let txt := dumpForbidRun name (!line.isEmpty) line
      let t1 ← IO.monoMsNow
      IO.FS.createDirAll out
      IO.FS.writeFile (System.FilePath.mk out / s!"{name}.txt") txt
      IO.println s!"{name}\t{mode}\t{!line.isEmpty}\t{(t1 - t0).toFloat / 1000.0}"
      return 0
  | _ => IO.eprintln "uso: bingo-dump SALIDA f.cnf [off|on]"; return 2
