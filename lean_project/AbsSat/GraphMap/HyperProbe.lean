-- lean_project/AbsSat/GraphMap/HyperProbe.lean
import AbsSat.GraphMap.Hypergraph
import AbsSat.GraphMap.ImportCnf
import AbsSat.SatMachine.DiffTest

/-!
`lake exe hyper` — runs the GYO reduction of `Hypergraph.lean` on the maps
`ImportCnf` actually builds, and reports whether they are α-acyclic and, if
not, how big the cyclic core is.

    lake exe hyper <file.cnf> ...
    lake exe hyper --random <cases> <seed> [minVars] [varSpan]

Exit code 0 always: this is a measurement, not a test. What it answers is
whether route E — "use Beeri–Fagin–Maier–Yannakakis instead of CCJ" — can
apply at all.
-/

namespace AbsSat.GraphMap.HyperProbe

open AbsSat.GraphMap.GraphMap AbsSat.GraphMap.ImportCnf
open AbsSat.GraphMap.Hypergraph

def line (path : String) (r : Report) : String :=
  String.intercalate "\n"
    [ path,
      s!"  steps={r.steps}",
      s!"  by-step  edges={r.edgesStep} core={r.coreStep} edges over {r.coreVertsS} steps  α-acyclic={r.acyclicS}",
      s!"  by-node  edges={r.edgesNode} core={r.coreNode} edges over {r.coreVertsN} steps  α-acyclic={r.acyclicN}" ]

def report (path : String) : IO Report := do
  let gmap ← load_import! path
  let r := analyse gmap
  IO.println (line path r)
  pure r

open AbsSat.SatMachine.DiffTest (Rng gen_cnf)

def runRandom (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- hypergraph acyclicity: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut acyclicS := 0
  let mut acyclicN := 0
  let mut maxCoreS := 0
  let mut maxCoreN := 0
  let mut sumCoreS := 0
  for idx in [0:cases] do
    let (rng1, nv) := rng.below nvSpan
    let nVars := nvMin + nv
    let (rng2, nClauses) :=
      if idx % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    IO.FS.writeFile "hyper_tmp.cnf" cnf
    let gmap ← load_import! "hyper_tmp.cnf"
    let r := analyse gmap
    if r.acyclicS then acyclicS := acyclicS + 1
    if r.acyclicN then acyclicN := acyclicN + 1
    maxCoreS := Nat.max maxCoreS r.coreStep
    maxCoreN := Nat.max maxCoreN r.coreNode
    sumCoreS := sumCoreS + r.coreStep
  IO.println s!"--- by-step  α-acyclic in {acyclicS}/{cases} maps  (largest core {maxCoreS} edges) ---"
  IO.println s!"--- by-node  α-acyclic in {acyclicN}/{cases} maps  (largest core {maxCoreN} edges) ---"
  IO.println s!"--- mean by-step core: {sumCoreS / cases} edges ---"
  if acyclicS == cases then
    IO.println "Every map is α-acyclic: BFMY applies, route E is open. ⚠ verify the construction."
  else
    IO.println "Not α-acyclic: BFMY does not apply. Route E is closed."
  pure 0

end AbsSat.GraphMap.HyperProbe
