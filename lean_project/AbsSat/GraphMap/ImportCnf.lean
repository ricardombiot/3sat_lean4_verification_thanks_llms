import AbsSat.GraphMap.GraphMap
import AbsSat.Utils.Alias
import Std.Data.HashMap

namespace AbsSat.GraphMap.ImportCnf

open AbsSat.GraphMap.GraphMap
open AbsSat.Utils.Alias

def cnf_p! (gmap : GMap) (line : String) : IO GMap := do
  -- Check for "cnf" as a safeguard, or assume structure
  -- Julia: contains(line, "cnf")
  -- Lean: List.isInfix [ 'c', 'n', 'f' ] line.toList
  -- Simpler: check splitted parts.
  let configurations := line.splitOn " " |> List.filter (fun s : String => s.length > 0)
  match configurations with
  | _ :: "cnf" :: nStr :: _ =>
      if let some nVars := nStr.toNat? then
        let mut gmap := gmap
        for varName in [1:nVars+1] do
          gmap ← add_var! gmap s!"{varName}"
        return gmap
      else
        IO.println s!"Error parsing NVARS from: {line}"
        return gmap
  | _ =>
      -- Maybe the line is "p cnf ..."
      match configurations with
      | "p" :: "cnf" :: nStr :: _ =>
          if let some nVars := nStr.toNat? then
            let mut gmap := gmap
            for varName in [1:nVars+1] do
               gmap ← add_var! gmap s!"{varName}"
            return gmap
          else
            IO.println s!"Error parsing NVARS from: {line}"
            return gmap
      | _ =>
         IO.println s!"Invalid p cnf line: {line}"
         return gmap

def cnf_or! (gmap : GMap) (line : String) : IO GMap := do
  let line := line.replace "-" "!"
  let literals := line.splitOn " " |> List.filter (fun s : String => s.length > 0)

  -- cnf lines often end with 0, so let's filter "0" if it stands alone or handle it
  -- Julia code: splits space, ensures length 4 (3 literals + 0?).
  -- "1 -3 0" -> ["1", "-3", "0"]?
  -- Julia original: `length(literals) != 4`. So 3 lits + termination `0`.

  if literals.length < 3 then
     return gmap -- Should throw or ignore?

  match literals with
  | l1 :: l2 :: l3 :: _ =>
     add_gate! gmap l1 l2 l3
  | _ => return gmap

def import! (gmap : GMap) (path_file : String) : IO GMap := do
  if !(← System.FilePath.pathExists path_file) then
     throw $ IO.userError s!"File not found: {path_file}"

  let lines ← IO.FS.lines path_file
  let mut gmap := gmap
  let mut stage := "waiting_conf"

  for line in lines do
    let line := line.trim
    if line.isEmpty then continue
    let firstCheck := line.front
    if firstCheck != 'c' then
      if stage == "waiting_conf" && firstCheck == 'p' then
         gmap ← cnf_p! gmap line
         stage := "reading_ors"
      else if stage == "reading_ors" then
         if firstCheck == '%' || firstCheck == '0' then break
         gmap ← cnf_or! gmap line
  return gmap

def load_import! (path_file : String) : IO GMap := do
  let gmap ← AbsSat.GraphMap.GraphMap.new
  let gmap ← import! gmap path_file
  let gmap := close_vars! gmap
  let gmap := close_gates! gmap
  return gmap

end AbsSat.GraphMap.ImportCnf
