-- lean_project/L6SearchMain.lean
import AbsSat.GraphPath.Model.L6Search

/--
Falsifier for bridge lemma L6 ("no zombies"): builds machine states over
synthetic maps whose requirements obey only `Reachable`'s own hypotheses, and
reports any valid state with no complete co-owned chain.

Usage: `lake exe l6search [steps] [width] [trials]` — defaults 4 3 150.
Exit code 1 if a counterexample is found.
-/
def main (args : List String) : IO UInt32 := do
  let steps := (args[0]?.bind (·.toNat?)).getD 4
  let width := (args[1]?.bind (·.toNat?)).getD 3
  let trials := (args[2]?.bind (·.toNat?)).getD 150
  IO.println s!"--- L6 falsifier: steps={steps} width={width} maps={trials} ---"
  let (states, richest, rich, sels, bad) := L6Search.diag2 steps width trials
  IO.println s!"states={states}  richest selection space={richest}  \
states with >=8 selections={rich}  selections enumerated={sels}"
  if bad == 0 then
    IO.println "No counterexample: every valid state had a complete co-owned chain. ✅"
    pure 0
  else
    IO.println s!"COUNTEREXAMPLE to L6: {bad} valid state(s) with no chain. ❌"
    pure 1
