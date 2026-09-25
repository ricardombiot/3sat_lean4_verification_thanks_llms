-- lean/improves_bin/AbsSatBin/GraphMap/MapBinDump.lean
import AbsSatBin.GraphMap.CnfMapBin
import AbsSatBin.Cnf.Dimacs

/-!
# `lake exe mapbin-dump` — the arithmetic bin map, dumped for the differential

`CnfMapBin` claims to reproduce what `GraphMapBin.load_import_bin!` builds in
Julia. Every theorem downstream is a correct proof about the *wrong map* if that
claim is off by one anywhere, so this module writes the same canonical dump as
`julia/improves_bin/test_3sat/dump_map_bin.jl`, one fact per line:

    S <stepCount>
    N <node> R <requirements, sorted> O <sons, sorted>
    W <prohibited window>

and `scripts/diff_map_bin.sh` sorts both and compares them. Lines are unordered;
only the multiset matters. `IO` only, no theorems.
-/

namespace AbsSatBin.GraphMap.MapBinDump

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

def keysSorted (ids : List NodeId) : String :=
  ",".intercalate ((ids.map as_key).toArray.qsort (fun a b => decide (a < b))).toList

def dumpLines (φ : Cnf) : List String := Id.run do
  if φ.clauses.isEmpty then
    return ["SKIP no clauses (Julia builds no fusion nodes)"]
  let mut out : List String := [s!"S {stepCount φ}"]
  for k in List.range (stepCount φ).toNat do
    for d in mapNodes φ (k : Int) do
      out := out ++ [s!"N {as_key d} R {keysSorted (reqOf φ d)} O {keysSorted (sonsOf φ d)}"]
  for w in prohibitedList φ do
    out := out ++ [s!"W {as_key_from_PathNodeId w}"]
  return out

def dumpFile (outDir : System.FilePath) (path : System.FilePath) : IO Unit := do
  let lines := (← IO.FS.lines path).toList
  let name := (path.fileStem.getD "out") ++ ".txt"
  let body := match Dimacs.parse lines with
    | .error e => [s!"SKIP {e}"]
    | .ok φ => dumpLines φ
  IO.FS.writeFile (outDir / name) ("\n".intercalate body ++ "\n")

def main (args : List String) : IO UInt32 := do
  match args with
  | outDir :: files@(_ :: _) =>
    IO.FS.createDirAll outDir
    for f in files do dumpFile outDir f
    return 0
  | _ =>
    IO.eprintln "usage: mapbin-dump OUTDIR f1.cnf [f2.cnf ...]"
    return 1

end AbsSatBin.GraphMap.MapBinDump
