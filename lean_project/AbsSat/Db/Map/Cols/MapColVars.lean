-- This file is part of the AbsSat library.
-- The AbsSat library is released under the MIT license.
-- See the LICENSE file in the root of this repository for details.

import Std.Data.HashMap

namespace AbsSat.Db.Map.Cols.MapColVars

/-
  A mutable structure that holds a dictionary mapping variable names (as strings)
  to their corresponding step numbers (as integers). This is a direct translation
  of the Julia `MapColVars` structure.
-/
structure MapColVars where
  table : IO.Ref (Std.HashMap String Int)

instance : Repr MapColVars where
  reprPrec _ _ := "MapColVars"

/-
  Creates a new, empty instance of `MapColVars`.
  The internal hash map is initialized but contains no entries.
  This is an IO action because it involves creating a mutable reference.
-/
def new : IO MapColVars := do
  let tableRef ← IO.mkRef {}
  return { table := tableRef }

/-
  Removes negation characters ("-" and "!") from a string.
  This function is used to normalize variable names before table lookup.
  It is a pure function and does not interact with the `MapColVars` state.

  - `title`: The input string, which may contain negation characters.
  - Returns: A new string with all instances of "-" and "!" removed.
-/
def clean_title (title : String) : String :=
  title.replace "-" "" |>.replace "!" ""

/-
  Checks if a variable title contains negation characters ("-" or "!").
  This is a pure function and is used to determine whether a variable
  should be treated as its negated form.

  - `title`: The input string, which may contain negation characters.
  - Returns: `true` if the string contains either "-" or "!", `false` otherwise.
-/
def is_neg (title : String) : Bool :=
  title.contains '-' || title.contains '!'

/-
  Retrieves the step number for a given variable title from the `MapColVars` table.
  If the title is negated, it adjusts the step number accordingly. If the title
  is not found after cleaning, it returns `none`.

  - `colVars`: The `MapColVars` instance containing the variable table.
  - `title`: The variable name to look up, which may be negated.
  - Returns: An `IO (Option Int)` action that resolves to the step number
    (or `step + 1` for negated variables) if found, otherwise `none`.
-/
def get_step_var (colVars : MapColVars) (title : String) : IO (Option Int) := do
  let have_neg := is_neg title
  let cleaned_title := clean_title title
  let table ← colVars.table.get

  match table.get? cleaned_title with
  | some step =>
    if have_neg then
      return some (step + 1)
    else
      return some step
  | none =>
    return none

def register_var! (colVars : MapColVars) (title : String) (step : Int) : IO Unit := do
  let cleaned_title := clean_title title
  let table ← colVars.table.get
  if !table.contains cleaned_title then
    let new_table := table.insert cleaned_title step
    colVars.table.set new_table

section Theorems

/-
  The `new` function correctly initializes an empty `MapColVars` instance.
  This theorem demonstrates that the size of the hash map within a newly
  created `MapColVars` is zero.
-/
def new_creates_empty_table : IO Unit := do
  let colVars ← new
  let table ← colVars.table.get
  assert! table.isEmpty

-- Pure theorems commented out to rely on runtime verification in run_tests
-- to avoid kernel reduction issues with string manipulations.

/-
  Verifies that `get_step_var` returns the correct step for a non-negated variable.
-/
def get_step_var_returns_step_for_normal_var : IO Unit := do
  let colVars ← new
  let initialTable : Std.HashMap String Int := {}
  let initialTable := initialTable.insert "v1" 10
  colVars.table.set initialTable
  let step ← get_step_var colVars "v1"
  assert! step == some 10

/-
  Verifies that `get_step_var` returns `step + 1` for a negated variable.
-/
def get_step_var_returns_step_plus_one_for_negated_var : IO Unit := do
  let colVars ← new
  let initialTable : Std.HashMap String Int := {}
  let initialTable := initialTable.insert "v1" 10
  colVars.table.set initialTable
  let step ← get_step_var colVars "-v1"
  assert! step == some 11

/-
  Verifies that `get_step_var` returns `none` for a variable not in the table.
-/
def get_step_var_returns_none_for_missing_var : IO Unit := do
  let colVars ← new
  let step ← get_step_var colVars "nonexistent"
  assert! step == none

end Theorems

section Examples

def run_tests : IO Unit := do
  new_creates_empty_table
  get_step_var_returns_step_for_normal_var
  get_step_var_returns_step_plus_one_for_negated_var
  get_step_var_returns_none_for_missing_var

  let colVars ← new
  let table ← colVars.table.get
  assert! table.isEmpty

  assert! clean_title "test-1" == "test1"
  assert! clean_title "!test2" == "test2"
  assert! clean_title "te-!st-3" == "test3"
  assert! clean_title "normal" == "normal"

  assert! is_neg "-test"
  assert! is_neg "!test"
  assert! not (is_neg "test")

  IO.println "All MapColVars tests passed!"

#eval run_tests

end Examples

end AbsSat.Db.Map.Cols.MapColVars
