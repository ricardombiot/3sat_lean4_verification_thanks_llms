-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain6BR.lean
import AbsSatBingo.Model.ForbidOnChain6BC

/-!
# El lector en orden de bisección para la clase de seis bloques

`sepPinFree_of_bisect` pide la ventana de todos los bloques de en medio, pero un orden de bisección solo usa las de
los lados de tres bloques. **`BisectOrderW n ord Win`** dice además qué ventanas usa cada separador (`Win`), y
**`sepPinFree_of_bisectW`** solo pide esas.

Con `[3, 1, 2, 4, 5]`, solo el primero (`s3`, lados de tres y tres) usa ventanas: la de `B1` (lee `s1`, `s2`) y la de
`B4` (lee `s4`, `s5`), las dos que da la clase (`bisectOrderW_6`).

Resultado: **`sepPinFree_of_chain6BC`** (T2) y **`reader_bisect_of_chain6BC`**: el lector que lee primero
`s3, s1, s2, s4, s5` no se atasca en ninguna fórmula de la clase, sin hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

namespace GPathB

/-- **Un orden de bisección, diciendo qué ventanas usa**: la del bloque `q + 1` si el lado derecho tiene tres bloques
o más, la del `q - 2` si los tiene el izquierdo. -/
def BisectOrderW (n : Nat) (ord : List Nat) (Win : Nat → Prop) : Prop :=
  ∀ (k q : Nat), ord[k]? = some q → 1 ≤ q ∧ q < n ∧ ∃ a b : Nat, a < q ∧ q < b ∧ b ≤ n ∧
    (a = 0 ∨ ∃ i : Nat, i < k ∧ ord[i]? = some a) ∧ (b = n ∨ ∃ i : Nat, i < k ∧ ord[i]? = some b) ∧
    (q - a ≤ 3 ∨ (1 ≤ a ∧ q - a ≤ 4)) ∧ (b - q ≤ 3 ∨ (b < n ∧ b - q ≤ 4)) ∧
    (q + 3 ≤ b → Win (q + 1)) ∧ (a + 3 ≤ q → Win (q - 2))

theorem bisectOrder_of_W {n : Nat} {ord : List Nat} {Win : Nat → Prop} (h : BisectOrderW n ord Win) :
    BisectOrder n ord := fun k q hq => by
  obtain ⟨q1, qn, a, b, ha, hb, hbn, hA, hB, hLL, hLR, _, _⟩ := h k q hq
  exact ⟨q1, qn, a, b, ha, hb, hbn, hA, hB, hLL, hLR⟩

section T2W

variable {n : Nat} {zone : Nat → Nat}

/-- **T2 en orden de bisección**, con solo las ventanas que usa el orden. -/
theorem sepPinFree_of_bisectW (D : ChainN φ n zone) {sv : Nat → Nat}
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k) {Win : Nat → Prop}
    (hw : ∀ p, Win p → ∃ lam, 0 ≤ lam ∧ lam < stepCount φ ∧ ReadsAt φ lam (sv p) ∧ ReadsAt φ lam (sv (p + 1)))
    {ord : List Nat} (hord : BisectOrderW n ord Win) : SepPinFree φ (ord.map sv) (stepCount φ) := by
  intro k R0 r s hpre hs hrs hr1 hrT
  rw [List.getElem?_map] at hs
  cases hq : ord[R0.length]? with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs
    have hsq : sv q = s := Option.some.inj hs
    obtain ⟨q1, qn, a, b, ha, hb, hbn, hA, hB, hLL, hLR, hWR, hWL⟩ := hord _ _ hq
    have hl := locPair_read (φ := φ) (stepCount φ) k R0 r
    have hv : stepVar φ r.step = some (sv q) := by rw [hsq]; exact hrs
    have fixOf : ∀ c, (c = 0 ∨ ∃ i, i < R0.length ∧ ord[i]? = some c) → 1 ≤ c → c < n →
        ∀ y y', Pinned φ (SolE φ (stepCount φ) k) R0 y → Pinned φ (SolE φ (stepCount φ) k) R0 y' →
          ∀ z, zone z = n + c → y z = y' z := by
      intro c hc h1 h2 y y' qy qy' z hz
      rcases hc with h | ⟨i, hi, ho⟩
      · omega
      rw [D.sep1 c h1 h2 z (sv c) hz (hsv c h1 h2)]
      exact fixed_of_prefix hpre hi ho y y' qy qy'
    have hmid : midFusion φ < stepCount φ := by unfold stepCount midFusion; omega
    refine phantomFree_bisect hl D hsv hv (fun h => hw (q + 1) (hWR h))
      (fun h => by
        obtain ⟨lam, l0, lN, r1, r2⟩ := hw (q - 2) (hWL h)
        exact ⟨lam, l0, lN, by rw [show q - 1 = q - 2 + 1 by omega]; exact r2, r1⟩) hmid (hsv q q1 qn) q1 ha hb hbn
      (fun h1 => fixOf a hA h1 (by omega)) (fun h2 => fixOf b ?_ (by omega) h2) hLL hLR (by omega) hrT
    rcases hB with h | h
    · omega
    · exact Or.inr h

end T2W

/-- **El orden para seis bloques usa solo las ventanas de `B1` y `B4`.** -/
theorem bisectOrderW_6 : BisectOrderW 6 [3, 1, 2, 4, 5] (fun p => p = 1 ∨ p = 4) := by
  intro k q h
  rcases k with _ | _ | _ | _ | _ | k
  · have : q = 3 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 0, 6, by omega, by omega, by omega, Or.inl rfl, Or.inl rfl, Or.inl (by omega),
      Or.inl (by omega), fun _ => Or.inr rfl, fun _ => Or.inl rfl⟩
  · have : q = 1 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 0, 3, by omega, by omega, by omega, Or.inl rfl, Or.inr ⟨0, by omega, rfl⟩,
      Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · have : q = 2 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 1, 3, by omega, by omega, by omega, Or.inr ⟨1, by omega, rfl⟩,
      Or.inr ⟨0, by omega, rfl⟩, Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega),
      fun h => absurd h (by omega)⟩
  · have : q = 4 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 3, 6, by omega, by omega, by omega, Or.inr ⟨0, by omega, rfl⟩, Or.inl rfl,
      Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · have : q = 5 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 4, 6, by omega, by omega, by omega, Or.inr ⟨3, by omega, rfl⟩, Or.inl rfl,
      Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · simp at h

variable {zone sv : Nat → Nat}

/-- **T2 para toda fórmula de la clase**, en el orden `s3, s1, s2, s4, s5`. -/
theorem sepPinFree_of_chain6BC (C : Chain6BC φ zone sv) :
    SepPinFree φ ([3, 1, 2, 4, 5].map sv) (stepCount φ) := by
  have h1 := C.cl (j := 1) (by omega)
  have h4 := C.cl (j := 4) (by omega)
  obtain ⟨a1, a2⟩ := C.w1 _ h1
  obtain ⟨b4, b5⟩ := C.w4 _ h4
  have kb : ∀ j, j < 6 → 0 ≤ clauseStep φ j 2 ∧ clauseStep φ j 2 < stepCount φ := fun j hj => by
    simp only [clauseStep, stepCount, C.len]; omega
  refine sepPinFree_of_bisectW C.D C.hsv (fun p hp => ?_) bisectOrderW_6
  rcases hp with rfl | rfl
  · exact ⟨clauseStep φ 1 2, (kb 1 (by omega)).1, (kb 1 (by omega)).2, readsAt_clause h1 a1,
      readsAt_clause h1 a2⟩
  · exact ⟨clauseStep φ 4 2, (kb 4 (by omega)).1, (kb 4 (by omega)).2,
      by rw [← b4]; exact readsAt_clause h4 (Or.inr (Or.inr rfl)), readsAt_clause h4 b5⟩

/-- Toda cláusula de la clase está en un bloque. -/
theorem blocks_of_chain6BC (C : Chain6BC φ zone sv) : ∀ c ∈ φ.clauses, ∃ j, j < 6 ∧ ClIn (BlkN 6 zone j) c := by
  intro c hc
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  have hjl : j < 6 := by
    rw [← C.len]
    by_cases h : j < φ.clauses.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  refine ⟨ord6 j, ?_, C.blk j c hj⟩
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ord6]

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {zone sv : Nat → Nat}

/-- **El lector en orden de bisección no se atasca en ninguna cadena de seis bloques de la clase**: toda lectura que
empieza por `s3, s1, s2, s4, s5` deja un estado válido con la rama de una solución que coincide con todas las
elecciones. Sin hipótesis. -/
theorem reader_bisect_of_chain6BC (hb : Bounded φ) (C : Chain6BC φ zone sv) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g')
    (hsf : SepFirst φ ([3, 1, 2, 4, 5].map sv) R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_sep_on hb (fun T hT => phantomAtW_of_phantomAt (phantomAt_of_chain6BC hb C T hT))
    (sepCover_of_chainN C.D (blocks_of_chain6BC C)
      (mem_sep_iff C.D C.hsv (bisectOrder_of_W bisectOrderW_6) (fun q h1 h2 => by
        rcases (by omega : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with rfl | rfl | rfl | rfl | rfl <;> simp)))
    (sepPinFree_of_chain6BC C) hkv hr hsf

/-- **En `chain6_bisect_lit`.** -/
theorem reader_bisect_chain6B {kv : NodeId × GPathB} (hkv : kv ∈ runM .on chain6B) {R : List NodeId}
    {g' : GPathB} (hr : Reading kv.2 R g') (hsf : SepFirst chain6B ([3, 1, 2, 4, 5].map
      (fun k => [6, 7, 8, 9, 10].getD (k - 1) 0)) R) :
    g'.isValid = true ∧ ∃ a, Sat a chain6B ∧ (∀ r ∈ R, selOfAssign chain6B a r.step = r) ∧
      CT g' (pidOfAssign chain6B a) :=
  reader_bisect_of_chain6BC bounded_chain6B chain6BC_chain6B hkv hr hsf

end MachineOn

end AbsSatBingo.Model
