import Lean
import AbsSat

/-! # Which lemmas does a theorem really rest on?

`#deps T pat` walks the dependency closure of `T` — its type and its proof term, recursively, through
every constant of the project (private ones included) — and lists the constants whose name contains
`pat`. It answers questions like *if `cleanInvalid` changes, which of its lemmas does the ladder
actually consume?*, which a text search cannot: most mentions are comments, or live in branches the
theorem never uses.

Not a `lean_exe`: run it with

    lake env lean Probes/DepsClosure.lean
-/

open Lean Elab Command

partial def depsClosure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    out := out.push n
    match env.find? n with
    | some ci =>
      let refs := ci.type.getUsedConstants ++
        (match ci with
         | .thmInfo t => t.value.getUsedConstants
         | .defnInfo d => d.value.getUsedConstants
         | _ => #[])
      for r in refs do
        if !seen.contains r && (r.toString.splitOn "AbsSat").length > 1 then todo := todo.push r
    | none => pure ()
  return out

/-- Auxiliary constants Lean generates (`_proof_i`, `match_i`, `eq_def`, …) are left out. -/
def isAux (n : Name) : Bool :=
  let s := n.toString
  ["_proof_", "match_", "._f", "eq_def", "_simp_", "_sunfold", "_unfold"].any
    (fun p => (s.splitOn p).length > 1)

elab "#deps " id:ident pat:str : command => do
  let env ← getEnv
  let all := depsClosure env id.getId
  let hits := ((all.filter (fun n => !isAux n && (n.toString.splitOn pat.getString).length > 1)).map
    (·.toString)).qsort (· < ·)
  logInfo m!"{id.getId}: {all.size} constants; matching \"{pat.getString}\": {hits.size}\n{String.intercalate "\n" hits.toList}"

-- 2026-09-23: what the ladder consumes of `cleanInvalid` (plan step 6, brick 5)
#deps AbsSat.GraphPath.Model.TopGoodLadder.readerVerdictW_iff_of_readerSegGood "cleanInvalid"
#deps AbsSat.GraphPath.Model.TopGoodLadder.readerVerdictW_iff_of_readerSegGood "cleanStep"
#deps AbsSat.GraphPath.Model.TopGoodLadder.readerVerdictW_iff_of_readerSegGood "reviewPass"
