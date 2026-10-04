-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain7B.lean
import AbsSatBingo.Model.ForbidOnChain6BR

/-!
# Un lado libre de cuatro bloques, con caras completas

En la unión de siete bloques en bisección, la variable de dentro `z3` deja un solo lado, de cuatro bloques y libre
(`B3, B4, B5, B6`). Con las tres caras de `P` (el otro lado ya está fijado), cierra:

* **`side_right4free`**: el triángulo no lee `t_1, t_2, t_3`. Las caras de la ventana del bloque `m + 2` (lee `t_2` y
  `t_3`) dan una fuente para los bloques `m` y `m + 1` juntos (dos variables, de `P`), otra para `m + 2` y otra para el
  bloque final.
* **`phantomFree_inner4`**: `v` de dentro del bloque `m`, el separador `m` fijado, el lado `m … b-1` de hasta tres
  bloques, de cuatro con el extremo fijo, o de cuatro libre; descenso por el primer separador leído.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int}

section Four

variable {n : Nat} {zone : Nat → Nat} {m : Nat} {i j l : Int} {a0 : Assign}

/-- **El lado libre de cuatro bloques sin leer ninguno de sus separadores**, con caras de `P`. -/
theorem side_right4free (D : ChainN φ n zone) (hm : 1 ≤ m) (hbn : m + 4 = n) (h0 : P0 a0) {Q : Assign → Prop}
    {lam : Int} (C : SideCap φ P0 P Q i j l lam a0) (hQ : ∀ c, Q c → P c)
    (hl2 : ∀ z, zone z = n + (m + 2) → ReadsAt φ lam z) (hl3 : ∀ z, zone z = n + (m + 3) → ReadsAt φ lam z)
    (hun : ∀ k z, 1 ≤ k → k < 4 → zone z = n + (m + k) → ¬ InW φ i j l z) :
    ∃ src, SideOut φ n zone P0 P i j l a0 m (m + 4) src := by
  obtain ⟨d0, q0, ag0⟩ := C.p0 (no3_or (D.cardM m hm (by omega)) (D.cardM (m + 1) (by omega) (by omega)))
  obtain ⟨d2, q2, ag2⟩ := C.p0 (no3_of_le1 (D.cardM (m + 2) (by omega) (by omega)))
  obtain ⟨d3, q3, ag3⟩ := C.p0 (no3_last D (p := m + 3) (by omega) (by omega))
  refine ⟨fun p => if p = m ∨ p = m + 1 then d0 else if p = m + 2 then d2 else if p = m + 3 then d3 else a0,
    ⟨fun p _ _ => ?_, by simp only; exact hQ _ q0, fun p a c z hz => ?_,
      fun p a c z hB hv hw => ?_⟩⟩
  · by_cases e : p = m ∨ p = m + 1
    · rw [if_pos e]; exact C.q0 _ q0
    by_cases e2 : p = m + 2
    · rw [if_neg e, if_pos e2]; exact C.q0 _ q2
    by_cases e3 : p = m + 3
    · rw [if_neg e, if_neg e2, if_pos e3]; exact C.q0 _ q3
    · rw [if_neg e, if_neg e2, if_neg e3]; exact h0
  · rcases (by omega : p = m + 1 ∨ p = m + 2 ∨ p = m + 3) with rfl | rfl | rfl
    · rw [if_pos (Or.inl (by omega)), if_pos (Or.inr rfl)]
    · rw [if_pos (Or.inr (by omega)), if_neg (by omega), if_pos rfl]
      exact C.win _ _ q0 q2 z (hl2 z hz)
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
      exact C.win _ _ q2 q3 z (hl3 z hz)
  · rcases (by omega : p = m ∨ p = m + 1 ∨ p = m + 2 ∨ p = m + 3) with rfl | rfl | rfl | rfl
    · rw [if_pos (Or.inl rfl)]
      rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact ag0 z (Or.inl h) hw
      · exact absurd h hv
      · exact absurd hw (hun 1 z (by omega) (by omega) (by omega))
    · rw [if_pos (Or.inr rfl)]
      rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact ag0 z (Or.inr h) hw
      · exact absurd hw (hun 1 z (by omega) (by omega) (by omega))
      · exact absurd hw (hun 2 z (by omega) (by omega) (by omega))
    · rw [if_neg (by omega), if_pos rfl]
      rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact ag2 z h hw
      · exact absurd hw (hun 2 z (by omega) (by omega) (by omega))
      · exact absurd hw (hun 3 z (by omega) (by omega) (by omega))
    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      rcases hB with h | ⟨_, h⟩ | ⟨h1, _⟩
      · exact ag3 z h hw
      · exact absurd hw (hun 3 z (by omega) (by omega) (by omega))
      · omega

end Four

section Inner4

/-- Una ventana antes de `Nn` que lee `s` y `s'`. -/
def WinAt (φ : Cnf) (Nn : Int) (s s' : Nat) : Prop :=
  ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt φ lam s ∧ ReadsAt φ lam s'

variable {n : Nat} {zone sv : Nat → Nat} {m b : Nat}

/-- **`v` dentro del bloque `m`, con el separador `m` fijado**, el lado `m … b-1` de hasta cuatro bloques. -/
theorem phantomFree_inner4 (hl : LocPair φ P0 P σ) (D : ChainN φ n zone)
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k) (hm1 : 1 ≤ m) (hmb : m < b) (hbn : b ≤ n)
    (hL : b - m ≤ 4) (hfix : FixedEnd n zone P0 b) (hfree4 : b - m = 4 → b = n)
    (hw3 : m + 3 ≤ b → WinAt φ Nn (sv (m + 1)) (sv (m + 2)))
    (hw4 : m + 4 ≤ b → WinAt φ Nn (sv (m + 2)) (sv (m + 3)))
    (hmid : midFusion φ < Nn) {v : Nat} (hv : stepVar φ σ = some v) (hzv : zone v = m)
    (hfa : ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + m → c z = c' z) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) :
    PhantomFree φ P0 P Nn σ := by
  have eqsv : ∀ {k z}, 1 ≤ k → k < n → zone z = n + k → z = sv k := fun {k z} a c h =>
    D.sep1 k a c z (sv k) h (hsv k a c)
  refine phantomFree_of_descent hσ0 hσN (fun x u w => frS φ sv m b x.id.step u.id.step w.id.step)
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, h0, hx0, hu0, hw0⟩ := t.b3 hS
  have hpos := frS_pos (φ := φ) (sv := sv) (i := x.id.step) (j := u.id.step) (l := w.id.step) hmb
  have hle := frS_le (φ := φ) (sv := sv) (m := m) (b := b) (i := x.id.step) (j := u.id.step) (l := w.id.step)
  have hun : ∀ k z, 1 ≤ k → k < frS φ sv m b x.id.step u.id.step w.id.step → zone z = n + (m + k) →
      ¬ InW φ x.id.step u.id.step w.id.step z := fun k z a c hz => by
    rw [eqsv (by omega) (by omega) hz]; exact frS_un hL a c
  have hrd : m + frS φ sv m b x.id.step u.id.step w.id.step < b →
      ∀ z, zone z = n + (m + frS φ sv m b x.id.step u.id.step w.id.step) → InW φ x.id.step u.id.step w.id.step z :=
    fun h z hz => by rw [eqsv (by omega) (by omega) hz]; exact frS_rd (by omega)
  have glue := fun {sR : Nat → Assign} (O : SideOut φ n zone P0 P x.id.step u.id.step w.id.step a0 m b sR) =>
    glue_one_tri hl D hv hzv hmb hbn hfa hfix h0 hx0 hu0 hw0 O
  -- caras completas de un testigo cuyos subtriángulos leen `s` (un separador de más cerca)
  have cap : ∀ {lam : Int} {k : Nat}, 0 ≤ lam → lam < Nn → ReadsAt φ lam (sv (m + k)) → 1 ≤ k →
      k < frS φ sv m b x.id.step u.id.step w.id.step →
      ∃ Q, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 ∧ ∀ c, Q c → P c := by
    intro lam k l0 lN lr hk1 hkf
    exact capFull hl hS t hx0 hu0 hw0 l0 lN lr (frS_un hL hk1 hkf) (fun x' u' w' t' h' => ih x' u' w' t' (by
      have := frS_of (φ := φ) hL hk1 (i := x'.id.step) (j := u'.id.step) (l := w'.id.step) h'
      omega))
  generalize hf : frS φ sv m b x.id.step u.id.step w.id.step = f at hpos hle hun hrd cap
  rcases (by omega : f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4) with rfl | rfl | rfl | rfl
  · -- el testigo de `σ`
    rcases faces_sigma hS hanch hσ0 hσN t h0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
    · exact h
    have n3 : No3 (fun z => zone z = m ∨ (m + 1 < b ∧ zone z = n + (m + 1))) := by
      by_cases h : m + 1 < b
      · intro y1 y2 y3 b1 b2 b3
        exact no3_mid_sep D hm1 (by omega) y1 y2 y3 (b1.imp id (·.2)) (b2.imp id (·.2)) (b3.imp id (·.2))
      · intro y1 y2 y3 b1 b2 b3
        exact no3_last D hm1 (by omega) y1 y2 y3 (b1.resolve_right (fun h' => h h'.1))
          (b2.resolve_right (fun h' => h h'.1)) (b3.resolve_right (fun h' => h h'.1))
    obtain ⟨d, qd, ag⟩ := F.pick n3
    exact glue (side_right1 (by omega) hfix h0 qd (hl.sub _ qd) ag (fun h z hz => hrd h z hz))
  · -- el testigo del paso de `t_1`
    have hsv1 : sv (m + 1) < φ.nVars := D.sepv _ (by rw [hsv _ (by omega) (by omega)]; omega)
      (by rw [hsv _ (by omega) (by omega)]; omega)
    have r1 : ReadsAt φ (varStep (sv (m + 1))) (sv (m + 1)) := reads_self (stepVar_var hsv1)
    obtain ⟨Q, C, _⟩ := cap (k := 1) (by simp only [varStep]; omega)
      (by simp only [varStep, midFusion] at hmid ⊢; omega) r1 (Nat.le_refl _) (by omega)
    obtain ⟨sR, O⟩ := side_right2 D hm1 (by omega) hbn hfix h0 C
      (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r1)
      (fun z hz => hun 1 z (Nat.le_refl _) (by omega) hz) hrd
    exact glue O
  · -- la ventana del bloque `m + 1`
    obtain ⟨lam, l0, lN, r1, r2⟩ := hw3 (by omega)
    obtain ⟨Q, C, _⟩ := cap (k := 1) l0 lN r1 (Nat.le_refl _) (by omega)
    obtain ⟨sR, O⟩ := side_right3 D hm1 (r := 3) (Or.inl rfl) (by omega) hbn hfix h0 C
      (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r1)
      (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r2) hun hrd
    exact glue O
  · by_cases hfx : b < n
    · -- cuatro con el extremo fijo
      obtain ⟨lam, l0, lN, r1, r2⟩ := hw3 (by omega)
      obtain ⟨Q, C, _⟩ := cap (k := 1) l0 lN r1 (Nat.le_refl _) (by omega)
      obtain ⟨sR, O⟩ := side_right3 D hm1 (r := 4) (Or.inr ⟨rfl, by omega, hfx⟩) (by omega) hbn hfix h0 C
        (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r1)
        (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r2) hun hrd
      exact glue O
    · -- cuatro libre: la ventana del bloque `m + 2`, con caras de `P`
      have hb4 : b = m + 4 := by omega
      obtain ⟨lam, l0, lN, r2, r3⟩ := hw4 (by omega)
      obtain ⟨Q, C, hQ⟩ := cap (k := 2) l0 lN r2 (by omega) (by omega)
      obtain ⟨sR, O⟩ := side_right4free D hm1 (by omega) h0 C hQ
        (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r2)
        (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r3) (fun k z a c hz => hun k z a c hz)
      subst hb4
      exact glue O

end Inner4

end GPathB

end AbsSatBingo.Model
