-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainReads.lean
import AbsSatBingo.Model.ForbidOnLink

/-!
# Un lado de cualquier longitud: contar lecturas, no variables

Los lemas de lado de `ForbidOnChainSide` piden cardinales a cada región que cubre una cara (a lo sumo dos variables).
Pero una cara solo tiene que coincidir con `a0` en lo que **leen** las ventanas del triángulo: `Agr` mira solo eso
(`agr_reads`). Así las elecciones de cara (`SideCap.p0`, `SideCap.pP`) se aplican a «región ∩ leídas», y un tramo largo
que el triángulo no lee no cuesta nada.

El lado derecho de `v` (separador `m`), bloques `m … b-1`, con el primer separador leído `t_r` (`r` sin leer antes):

* **`side_two`**: el testigo de un separador sin leer `t_c` (`1 ≤ c < r`; por ejemplo el de su paso de variable, que
  siempre existe). Dos regiones, `m … m+c-1` (de `P`) y `m+c … m+r-1` (con `t_r`), unidas en `t_c`.
* **`side_three`**: la ventana de la cláusula del bloque `m + a` (lee `t_a` y `t_{a+1}`). Tres regiones: `m … m+a-1`,
  el bloque `m + a`, y `m+a+1 … m+r-1`, unidas en `t_a` y `t_{a+1}`.

Cada región pide que el triángulo lea a lo sumo dos de sus variables (una sola en la de `v` si sus caras no son todas de
`P`). La longitud del lado no aparece.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop}

/-- Coincidir en lo leído de `M` es coincidir en `M`. -/
theorem agr_reads {i j l : Int} {M : Nat → Prop} {d a0 : Assign}
    (h : Agr φ i j l (fun z => M z ∧ InW φ i j l z) d a0) : Agr φ i j l M d a0 :=
  fun z hm hw => h z ⟨hm, hw⟩ hw

section Reads

variable {n : Nat} {zone : Nat → Nat} {m b : Nat} {i j l : Int} {a0 : Assign}

/-- La cara de la región de `v`: una de `P` que coincide con `a0` en lo leído de `M`. -/
theorem pickP_reads {Q : Assign → Prop} {lam : Int} (C : SideCap φ P0 P Q i j l lam a0) {M : Nat → Prop}
    (h : Le1 (fun z => M z ∧ InW φ i j l z) ∨ (No3 (fun z => M z ∧ InW φ i j l z) ∧ ∀ c, Q c → P c)) :
    ∃ d, P d ∧ Q d ∧ Agr φ i j l M d a0 := by
  rcases h with h | ⟨h, hQ⟩
  · obtain ⟨d, qP, qQ, ag⟩ := C.pP h
    exact ⟨d, qP, qQ, agr_reads ag⟩
  · obtain ⟨d, qQ, ag⟩ := C.p0 h
    exact ⟨d, hQ d qQ, qQ, agr_reads ag⟩

/-- **Dos regiones**, unidas en `t_c` por las caras del testigo. -/
theorem side_two (hm : 1 ≤ m) {r c : Nat} (hc1 : 1 ≤ c) (hcr : c < r) (hrb : m + r ≤ b)
    (hfix : FixedEnd n zone P0 b) (h0 : P0 a0) {Q : Assign → Prop} {lam : Int} (C : SideCap φ P0 P Q i j l lam a0)
    (hlc : ∀ z, zone z = n + (m + c) → ReadsAt φ lam z)
    (hun : ∀ k z, 1 ≤ k → k < r → zone z = n + (m + k) → ¬ InW φ i j l z)
    (hrd : m + r < b → ∀ z, zone z = n + (m + r) → InW φ i j l z)
    (hA : Le1 (fun z => (m ≤ zone z ∧ zone z < m + c) ∧ InW φ i j l z) ∨
      (No3 (fun z => (m ≤ zone z ∧ zone z < m + c) ∧ InW φ i j l z) ∧ ∀ q, Q q → P q))
    (hB : No3 (fun z => ((m + c ≤ zone z ∧ zone z < m + r) ∨ (m + r < b ∧ zone z = n + (m + r))) ∧
      InW φ i j l z)) :
    ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  obtain ⟨dA, pA, qA, agA⟩ := pickP_reads (M := fun z => m ≤ zone z ∧ zone z < m + c) C hA
  obtain ⟨dB, qB, agB'⟩ := C.p0 hB
  have agB := agr_reads agB'
  have q0A := C.q0 _ qA; have q0B := C.q0 _ qB
  refine ⟨fun p => if p < m + c then dA else if p < m + r then dB else a0,
    ⟨fun p _ _ => ?_, by simp only [if_pos (show m < m + c by omega)]; exact pA, fun p a1 a2 z hz => ?_,
      fun p a1 a2 z hBk hv hw => ?_⟩⟩
  · by_cases e : p < m + c
    · rw [if_pos e]; exact q0A
    by_cases e' : p < m + r
    · rw [if_neg e, if_pos e']; exact q0B
    · rw [if_neg e, if_neg e']; exact h0
  · -- las uniones
    by_cases e1 : p < m + c
    · rw [if_pos (by omega), if_pos e1]
    by_cases e2 : p = m + c
    · subst e2
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      exact C.win _ _ qA qB z (hlc z hz)
    by_cases e3 : p < m + r
    · rw [if_neg (by omega), if_pos (by omega), if_neg e1, if_pos e3]
    by_cases e4 : p = m + r
    · subst e4
      rw [if_neg (by omega), if_pos (by omega), if_neg e1, if_neg e3]
      exact agB z (Or.inr ⟨by omega, hz⟩) (hrd (by omega) z hz)
    · rw [if_neg (by omega), if_neg (by omega), if_neg e1, if_neg e3]
  · -- coincidir con `a0`
    by_cases e1 : p < m + c
    · rw [if_pos e1]
      rcases hBk with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact agA z ⟨by omega, by omega⟩ hw
      · exact absurd hw (hun (p - m) z (by omega) (by omega) (by rw [h]; omega))
      · exact absurd hw (hun (p + 1 - m) z (by omega) (by omega) (by rw [h]; omega))
    by_cases e2 : p < m + r
    · rw [if_neg e1, if_pos e2]
      rcases hBk with h | ⟨_, h⟩ | ⟨h1, h⟩
      · exact agB z (Or.inl ⟨by omega, by omega⟩) hw
      · exact absurd hw (hun (p - m) z (by omega) (by omega) (by rw [h]; omega))
      · by_cases e3 : p + 1 < m + r
        · exact absurd hw (hun (p + 1 - m) z (by omega) (by omega) (by rw [h]; omega))
        · by_cases e4 : m + r < b
          · exact agB z (Or.inr ⟨e4, by omega⟩) hw
          · exact hfix (by omega) dB a0 q0B h0 z (by omega)
    · rw [if_neg e1, if_neg e2]

/-- **Tres regiones**, unidas en `t_a` y `t_{a+1}` por la ventana del bloque `m + a`. -/
theorem side_three (hm : 1 ≤ m) {r a : Nat} (ha1 : 1 ≤ a) (har : a < r) (hrb : m + r ≤ b)
    (hfix : FixedEnd n zone P0 b) (h0 : P0 a0) {Q : Assign → Prop} {lam : Int} (C : SideCap φ P0 P Q i j l lam a0)
    (hla : ∀ z, zone z = n + (m + a) → ReadsAt φ lam z)
    (hla1 : ∀ z, zone z = n + (m + a + 1) → ReadsAt φ lam z)
    (hun : ∀ k z, 1 ≤ k → k < r → zone z = n + (m + k) → ¬ InW φ i j l z)
    (hrd : m + r < b → ∀ z, zone z = n + (m + r) → InW φ i j l z)
    (hA : Le1 (fun z => (m ≤ zone z ∧ zone z < m + a) ∧ InW φ i j l z) ∨
      (No3 (fun z => (m ≤ zone z ∧ zone z < m + a) ∧ InW φ i j l z) ∧ ∀ q, Q q → P q))
    (hM : No3 (fun z => (zone z = m + a ∨ (a + 1 = r ∧ m + r < b ∧ zone z = n + (m + r))) ∧ InW φ i j l z))
    (hB : No3 (fun z => ((m + a + 1 ≤ zone z ∧ zone z < m + r) ∨ (a + 1 < r ∧ m + r < b ∧ zone z = n + (m + r))) ∧
      InW φ i j l z)) :
    ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  obtain ⟨dA, pA, qA, agA⟩ := pickP_reads (M := fun z => m ≤ zone z ∧ zone z < m + a) C hA
  obtain ⟨dM, qM, agM'⟩ := C.p0 hM
  obtain ⟨dB, qB, agB'⟩ := C.p0 hB
  have agM := agr_reads agM'; have agB := agr_reads agB'
  have q0A := C.q0 _ qA; have q0M := C.q0 _ qM; have q0B := C.q0 _ qB
  refine ⟨fun p => if p < m + a then dA else if p = m + a then dM else if p < m + r then dB else a0,
    ⟨fun p _ _ => ?_, by simp only [if_pos (show m < m + a by omega)]; exact pA, fun p a1 a2 z hz => ?_,
      fun p a1 a2 z hBk hv hw => ?_⟩⟩
  · by_cases e : p < m + a
    · rw [if_pos e]; exact q0A
    by_cases e' : p = m + a
    · rw [if_neg e, if_pos e']; exact q0M
    by_cases e'' : p < m + r
    · rw [if_neg e, if_neg e', if_pos e'']; exact q0B
    · rw [if_neg e, if_neg e', if_neg e'']; exact h0
  · -- las uniones
    by_cases e1 : p < m + a
    · rw [if_pos (by omega), if_pos e1]
    by_cases e2 : p = m + a
    · subst e2
      rw [if_pos (by omega), if_neg (by omega), if_pos rfl]
      exact C.win _ _ qA qM z (hla z hz)
    by_cases e3 : p = m + a + 1
    · subst e3
      rw [if_neg (by omega), if_pos (by omega), if_neg e1, if_neg e2]
      by_cases e5 : a + 1 < r
      · rw [if_pos (by omega)]
        exact C.win _ _ qM qB z (hla1 z hz)
      · rw [if_neg (by omega)]
        exact agM z (Or.inr ⟨by omega, by omega, by omega⟩) (hrd (by omega) z (by omega))
    by_cases e4 : p < m + r
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg e1, if_neg e2, if_pos e4]
    by_cases e6 : p = m + r
    · subst e6
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg e1, if_neg e2, if_neg e4]
      exact agB z (Or.inr ⟨by omega, by omega, hz⟩) (hrd (by omega) z hz)
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg e1, if_neg e2, if_neg e4]
  · -- coincidir con `a0`
    by_cases e1 : p < m + a
    · rw [if_pos e1]
      rcases hBk with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact agA z ⟨by omega, by omega⟩ hw
      · exact absurd hw (hun (p - m) z (by omega) (by omega) (by rw [h]; omega))
      · exact absurd hw (hun (p + 1 - m) z (by omega) (by omega) (by rw [h]; omega))
    by_cases e2 : p = m + a
    · rw [if_neg e1, if_pos e2]
      rcases hBk with h | ⟨_, h⟩ | ⟨h1, h⟩
      · exact agM z (Or.inl (by omega)) hw
      · exact absurd hw (hun (p - m) z (by omega) (by omega) (by rw [h]; omega))
      · by_cases e5 : a + 1 < r
        · exact absurd hw (hun (a + 1) z (by omega) e5 (by rw [h]; omega))
        · by_cases e6 : m + r < b
          · exact agM z (Or.inr ⟨by omega, e6, by omega⟩) hw
          · exact hfix (by omega) dM a0 q0M h0 z (by omega)
    by_cases e3 : p < m + r
    · rw [if_neg e1, if_neg e2, if_pos e3]
      rcases hBk with h | ⟨_, h⟩ | ⟨h1, h⟩
      · exact agB z (Or.inl ⟨by omega, by omega⟩) hw
      · exact absurd hw (hun (p - m) z (by omega) (by omega) (by rw [h]; omega))
      · by_cases e4 : p + 1 < m + r
        · exact absurd hw (hun (p + 1 - m) z (by omega) (by omega) (by rw [h]; omega))
        · by_cases e6 : m + r < b
          · exact agB z (Or.inr ⟨by omega, e6, by omega⟩) hw
          · exact hfix (by omega) dB a0 q0B h0 z (by omega)
    · rw [if_neg e1, if_neg e2, if_neg e3]

end Reads

end GPathB

end AbsSatBingo.Model
