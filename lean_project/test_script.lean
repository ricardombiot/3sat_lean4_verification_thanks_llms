import AbsSat.Cnf.Formula

namespace AbsSat.Cnf

def enumAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let rest := enumAssignments n
    (rest.map (fun a => false :: a)) ++ (rest.map (fun a => true :: a))

def toAssign (l : List Bool) : Assign :=
  fun i => match l[i]? with
    | some b => b
    | none => false

def bruteForceSat (φ : Cnf) : List (List Bool) :=
  (enumAssignments φ.nVars).filter (fun l => satB (toAssign l) φ)

theorem length_mem_enumAssignments {n : Nat} {l : List Bool} (h : l ∈ enumAssignments n) :
    l.length = n := by
  induction n generalizing l with
  | zero =>
    simp only [enumAssignments, List.mem_singleton] at h
    rw [h, List.length_nil]
  | succ n ih =>
    simp only [enumAssignments, List.mem_append, List.mem_map] at h
    rcases h with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
    · simp only [List.length_cons]
      rw [ih ha]

theorem bruteForceSat_sound (φ : Cnf) (l : List Bool) (h : l ∈ bruteForceSat φ) :
    Sat (toAssign l) φ := by
  simp only [bruteForceSat, List.mem_filter] at h
  exact (satB_iff (toAssign l) φ).mp h.2
