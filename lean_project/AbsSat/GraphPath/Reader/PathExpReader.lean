-- lean_project/AbsSat/GraphPath/Reader/PathExpReader.lean
import AbsSat.GraphPath.GraphPath
import AbsSat.GraphPath.Reader.PathReader

namespace AbsSat.GraphPath.Reader

structure GPathExpReader where
  list_readers : Array GPathReader
  list_solutions : Array (Array Bool)
  is_finished : Bool
-- deriving Repr

def GPathExpReader.new (gpath : GPath) : GPathExpReader :=
  let reader_seed := GPathReader.new gpath
  let list_readers := #[reader_seed]
  let list_solutions := #[]
  let is_finished := false
  ⟨list_readers, list_solutions, is_finished⟩

section Theorems

theorem new_is_finished_is_false (gpath : GPath) : (GPathExpReader.new gpath).is_finished = false := by
  simp [GPathExpReader.new]

theorem new_list_solutions_is_empty (gpath : GPath) : (GPathExpReader.new gpath).list_solutions.isEmpty := by
  simp [GPathExpReader.new]

theorem new_list_readers_has_one_element (gpath : GPath) : (GPathExpReader.new gpath).list_readers.size = 1 := by
  simp [GPathExpReader.new]

end Theorems

section Examples

def run_tests : IO Unit := do
  let gpath ← GPath.new
  let exp_reader := GPathExpReader.new gpath
  IO.println s!"New GPathExpReader created: is_finished={exp_reader.is_finished}"
  IO.println s!"GPathExpReader list_solutions: {exp_reader.list_solutions}"
  IO.println s!"GPathExpReader list_readers size: {exp_reader.list_readers.size}"

-- #eval run_tests

end Examples

end AbsSat.GraphPath.Reader
