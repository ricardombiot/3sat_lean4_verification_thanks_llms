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

/-- Lema auxiliar (el recíproco de `length_mem_enumAssignments`): toda lista de booleanos está
    entre las que `enumAssignments` genera para su longitud. -/
theorem mem_enumAssignments_length : ∀ l : List Bool, l ∈ enumAssignments l.length
  | [] => by simp [enumAssignments]
  | b :: t => by
    have ih := mem_enumAssignments_length t
    cases b <;> simp [enumAssignments, ih]

/-- La lista de los `n` primeros valores de una asignación está en el espacio de búsqueda. -/
theorem enum_complete (n : Nat) (a : Assign) : (List.range n).map a ∈ enumAssignments n := by
  have h := mem_enumAssignments_length ((List.range n).map a)
  simpa using h

/-- Leída como asignación, esa lista coincide con `a` por debajo de `n`. -/
theorem toAssign_map_range (n : Nat) (a : Assign) (i : Nat) (hi : i < n) :
    toAssign ((List.range n).map a) i = a i := by
  simp [toAssign, List.getElem?_range hi]

/-- COMPLETITUD (Completeness): Si existe alguna asignación `a` que satisfaga la fórmula
    lógicamente, entonces el algoritmo de fuerza bruta encontrará su prefijo correcto y
    lo devolverá. -/
theorem bruteForceSat_complete (φ : Cnf) (hwf : WF φ) (a : Assign) (hSat : Sat a φ) :
    ∃ l ∈ bruteForceSat φ, ∀ i < φ.nVars, (toAssign l) i = a i := by
  let targetList := (List.range φ.nVars).map a

  have h_in_enum : targetList ∈ enumAssignments φ.nVars :=
    enum_complete φ.nVars a

  have h_congr : Sat (toAssign targetList) φ := by
    apply sat_congr_below φ hwf a (toAssign targetList) _ hSat
    intro i hi
    exact (toAssign_map_range φ.nVars a i hi).symm

  have h_satB : satB (toAssign targetList) φ = true :=
    (satB_iff (toAssign targetList) φ).mpr h_congr

  refine ⟨targetList, ?_, ?_⟩
  · simp only [bruteForceSat, List.mem_filter]
    exact ⟨h_in_enum, h_satB⟩
  · intro i hi
    exact toAssign_map_range φ.nVars a i hi

/-- **El oráculo decide la satisfacibilidad**: su lista no está vacía exactamente cuando la
    fórmula es satisfacible. -/
theorem bruteForceSat_ne_nil_iff (φ : Cnf) (hwf : WF φ) :
    bruteForceSat φ ≠ [] ↔ Satisfiable φ := by
  constructor
  · intro h
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨toAssign l, bruteForceSat_sound φ l hl⟩
  · intro ⟨a, ha⟩ hnil
    obtain ⟨l, hl, _⟩ := bruteForceSat_complete φ hwf a ha
    rw [hnil] at hl
    cases hl

/-- info: 'AbsSat.Cnf.bruteForceSat_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bruteForceSat_sound

/-- info: 'AbsSat.Cnf.bruteForceSat_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bruteForceSat_complete

/-- info: 'AbsSat.Cnf.bruteForceSat_ne_nil_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bruteForceSat_ne_nil_iff

end AbsSat.Cnf
