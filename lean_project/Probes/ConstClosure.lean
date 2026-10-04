import AbsSat.GraphPath.Model.OneStep
open Lean Meta

partial def closure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := NameSet.empty
  let mut st : Array Name := #[root]
  while !st.isEmpty do
    let n := st.back!
    st := st.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      for c in ci.type.getUsedConstants do st := st.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do st := st.push c
  return seen

#eval show MetaM Unit from do
  let env ← getEnv
  for root in [``AbsSat.GraphPath.Model.OneStep.readerVerdictW_iff_of_keptOwn,
               ``AbsSat.GraphPath.Model.TopGoodLadder.readerVerdictW_iff_of_readerSegGood] do
    let s := closure env root
    let mut mods : Std.HashMap Name Nat := {}
    for n in s.toList do
      if let some idx := env.getModuleIdxFor? n then
        let m := env.header.moduleNames[idx.toNat]!
        if m.getRoot == `AbsSat then mods := mods.insert m (mods.getD m 0 + 1)
    IO.println s!"{root}: {s.size} constantes, {mods.size} modulos AbsSat"
    for (m, k) in mods.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
      IO.println s!"  {k}\t{m}"
