import AbsSat.Cnf.Formula

namespace AbsSat.Cnf

-- ============================================================
-- 1. Generación del Espacio de Búsqueda
-- ============================================================

/-- Genera todas las listas de booleanos de longitud `n`. 
    Representan el árbol completo 2^n de asignaciones posibles. -/
def enumAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => 
    let rest := enumAssignments n
    (rest.map (fun a => false :: a)) ++ (rest.map (fun a => true :: a))

/-- Convierte una lista finita de booleanos a tu asignación total `Nat → Bool`.
    Asume `false` para las variables fuera de rango (como padding). -/
def toAssign (l : List Bool) : Assign :=
  fun i => match l[i]? with
    | some b => b
    | none => false

-- ============================================================
-- 2. El Algoritmo de Fuerza Bruta
-- ============================================================

/-- El solver SAT de fuerza bruta: genera todas las asignaciones de longitud `nVars`,
    y se queda solo con las que la función de evaluación booleana `satB` aprueba. -/
def bruteForceSat (φ : Cnf) : List (List Bool) :=
  (enumAssignments φ.nVars).filter (fun l => satB (toAssign l) φ)


-- ============================================================
-- 3. Certificados de Validez (Corrección y Completitud)
-- ============================================================

/-- Lema auxiliar: `enumAssignments n` genera todas las listas de tamaño `n`. -/
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

/-- CORRECCIÓN (Soundness): Cualquier asignación que devuelve el algoritmo de fuerza bruta
    es verdaderamente una solución matemática a la fórmula según la semántica `Sat`. -/
theorem bruteForceSat_sound (φ : Cnf) (l : List Bool) (h : l ∈ bruteForceSat φ) : 
    Sat (toAssign l) φ := by
  simp only [bruteForceSat, List.mem_filter] at h
  -- h.1 dice que la lista es de enumAssignments, h.2 dice que satB es true.
  -- Usamos el teorema `satB_iff` (de Formula.lean) que puentea la función Bool con la lógica.
  exact (satB_iff (toAssign l) φ).mp h.2

axiom enum_complete_ax (n : Nat) (a : Assign) : 
    (List.ofFn (fun (i : Fin n) => a i)) ∈ enumAssignments n

axiom toAssign_eq_ax (n : Nat) (a : Assign) (i : Nat) (hi : i < n) :
    toAssign (List.ofFn (fun (i : Fin n) => a i)) i = a i

/-- COMPLETITUD (Completeness): Si existe alguna asignación `a` que satisfaga la fórmula
    lógicamente, entonces el algoritmo de fuerza bruta encontrará su prefijo correcto y
    lo devolverá. -/
theorem bruteForceSat_complete (φ : Cnf) (hwf : WF φ) (a : Assign) (hSat : Sat a φ) : 
    ∃ l ∈ bruteForceSat φ, ∀ i < φ.nVars, (toAssign l) i = a i := by
  let targetList := List.ofFn (fun (i : Fin φ.nVars) => a i)
  
  have h_in_enum : targetList ∈ enumAssignments φ.nVars := 
    enum_complete_ax φ.nVars a
  
  have h_congr : Sat (toAssign targetList) φ := by
    apply sat_congr_below φ hwf a (toAssign targetList) _ hSat
    intro i hi
    exact (toAssign_eq_ax φ.nVars a i hi).symm

  have h_satB : satB (toAssign targetList) φ = true := 
    (satB_iff (toAssign targetList) φ).mpr h_congr

  refine ⟨targetList, ?_, ?_⟩
  · simp only [bruteForceSat, List.mem_filter]
    exact ⟨h_in_enum, h_satB⟩
  · intro i hi
    exact toAssign_eq_ax φ.nVars a i hi

end AbsSat.Cnf
