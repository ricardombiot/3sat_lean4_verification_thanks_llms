-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainAny.lean
import AbsSatBingo.Model.ForbidOnChainReads

/-!
# Un lado de cualquier longitud: el descenso

`v` es de dentro del bloque `m`, con el separador `m` fijado (todas las ramas de `P0` lo leen igual), y el lado son los
bloques `m … b-1`, **de cualquier longitud**. El descenso es por el primer separador leído, ahora sin tope (`frN`,
por recursión con combustible).

* `r = 1`: las caras del testigo de `σ`.
* `r ≥ 2`: el testigo del **paso de variable** de un separador sin leer `t_c` (siempre existe, antes de la línea);
  sus subtriangulaciones leen `t_c` y bajan a `≤ c`. Las caras de las dos regiones salen de `pick3`, y se unen en `t_c`
  (`side_twoD`).

**La hipótesis es estática** (`SideSplit`): lo que lee un triángulo depende solo de los pasos de sus nodos, así que el
corte `c` es una propiedad de la fórmula (su numeración y el orden de sus cláusulas). Una región solo es mala
(`Bad3`) si tiene tres variables distintas, cada una leída en una de las tres ventanas: es como falla `pick3`.

Resultado: **`phantomFree_inner_any`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int}

/-! ## El primer separador leído, sin tope -/

open Classical in
/-- Buscar desde `k`, con `f` pasos de combustible, el primer separador `sv (m + k)` leído. -/
noncomputable def frAux (φ : Cnf) (sv : Nat → Nat) (m : Nat) (i j l : Int) : Nat → Nat → Nat
  | k, 0 => k
  | k, f + 1 => if InW φ i j l (sv (m + k)) then k else frAux φ sv m i j l (k + 1) f

theorem frAux_spec (sv : Nat → Nat) (m : Nat) (i j l : Int) :
    ∀ f k, k ≤ frAux φ sv m i j l k f ∧ frAux φ sv m i j l k f ≤ k + f ∧
      (∀ k', k ≤ k' → k' < frAux φ sv m i j l k f → ¬ InW φ i j l (sv (m + k'))) ∧
      (frAux φ sv m i j l k f < k + f → InW φ i j l (sv (m + frAux φ sv m i j l k f))) := by
  intro f
  induction f with
  | zero => intro k; simp only [frAux]; exact ⟨Nat.le_refl _, by omega, fun _ a b => absurd b (by omega), fun h => by omega⟩
  | succ f ih =>
    intro k
    by_cases h : InW φ i j l (sv (m + k))
    · have e : frAux φ sv m i j l k (f + 1) = k := by simp only [frAux, if_pos h]
      rw [e]
      exact ⟨Nat.le_refl _, by omega, fun _ a b => absurd b (by omega), fun _ => h⟩
    · have e : frAux φ sv m i j l k (f + 1) = frAux φ sv m i j l (k + 1) f := by simp only [frAux, if_neg h]
      rw [e]
      obtain ⟨a1, a2, a3, a4⟩ := ih (k + 1)
      refine ⟨by omega, by omega, fun k' b1 b2 => ?_, fun hh => a4 (by omega)⟩
      by_cases e' : k' = k
      · rw [e']; exact h
      · exact a3 k' (by omega) b2

/-- **El primer separador leído** del lado `m … b-1` (la longitud `b - m` si no se lee ninguno). -/
noncomputable def frN (φ : Cnf) (sv : Nat → Nat) (m b : Nat) (i j l : Int) : Nat := frAux φ sv m i j l 1 (b - m - 1)

section FrN

variable {sv : Nat → Nat} {m b : Nat} {i j l : Int}

theorem frN_pos : 1 ≤ frN φ sv m b i j l := (frAux_spec sv m i j l _ 1).1

theorem frN_le (hmb : m < b) : frN φ sv m b i j l ≤ b - m := by
  have := (frAux_spec (φ := φ) sv m i j l (b - m - 1) 1).2.1
  unfold frN; omega

theorem frN_un {k : Nat} (hk : 1 ≤ k) (hkf : k < frN φ sv m b i j l) : ¬ InW φ i j l (sv (m + k)) :=
  (frAux_spec sv m i j l _ 1).2.2.1 k hk hkf

theorem frN_rd (hmb : m < b) (h : frN φ sv m b i j l < b - m) : InW φ i j l (sv (m + frN φ sv m b i j l)) :=
  (frAux_spec sv m i j l _ 1).2.2.2 (by unfold frN at h; omega)

theorem frN_of {k : Nat} (hk : 1 ≤ k) (hw : InW φ i j l (sv (m + k))) : frN φ sv m b i j l ≤ k :=
  Nat.le_of_not_lt (fun hc => frN_un hk hc hw)

end FrN

/-! ## Las regiones -/

/-- **Una región mala**: tres variables distintas de `M`, leídas una en cada ventana (la tercera, la segunda y la
primera). Es como falla `pick3`. -/
def Bad3 (φ : Cnf) (i j l : Int) (M : Nat → Prop) : Prop :=
  ∃ z1 z2 z3, M z1 ∧ M z2 ∧ M z3 ∧ z1 ≠ z2 ∧ z1 ≠ z3 ∧ z2 ≠ z3 ∧ ReadsAt φ l z1 ∧ ReadsAt φ j z2 ∧ ReadsAt φ i z3

/-- **El corte del lado**: con el primer separador leído en `r ≥ 2`, un separador sin leer `t_c` deja las dos regiones
buenas. Es estático: solo depende de los pasos `i, j, l`. -/
def SideSplit (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) (m b : Nat) (N : Int) : Prop :=
  ∀ i j l : Int, 0 ≤ i → i < N → 0 ≤ j → j < N → 0 ≤ l → l < N → 2 ≤ frN φ sv m b i j l → ∃ c, 1 ≤ c ∧ c < frN φ sv m b i j l ∧
    ¬ Bad3 φ i j l (fun z => m ≤ zone z ∧ zone z < m + c) ∧
    ¬ Bad3 φ i j l (fun z => (m + c ≤ zone z ∧ zone z < m + frN φ sv m b i j l) ∨
      (m + frN φ sv m b i j l < b ∧ zone z = n + (m + frN φ sv m b i j l)))

section Two

variable {n : Nat} {zone : Nat → Nat} {m b : Nat} {i j l : Int} {a0 : Assign}

/-- **Dos regiones**, con sus caras ya elegidas. -/
theorem side_twoD {r c : Nat} (hc1 : 1 ≤ c) (hcr : c < r) (hrb : m + r ≤ b)
    (hfix : FixedEnd n zone P0 b) (h0 : P0 a0) {Q : Assign → Prop} {lam : Int} (C : SideCap φ P0 P Q i j l lam a0)
    (hlc : ∀ z, zone z = n + (m + c) → ReadsAt φ lam z)
    (hun : ∀ k z, 1 ≤ k → k < r → zone z = n + (m + k) → ¬ InW φ i j l z)
    (hrd : m + r < b → ∀ z, zone z = n + (m + r) → InW φ i j l z)
    (hdA : ∃ d, P d ∧ Q d ∧ Agr φ i j l (fun z => m ≤ zone z ∧ zone z < m + c) d a0)
    (hdB : ∃ d, Q d ∧ Agr φ i j l (fun z => (m + c ≤ zone z ∧ zone z < m + r) ∨ (m + r < b ∧ zone z = n + (m + r)))
      d a0) :
    ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  obtain ⟨dA, pA, qA, agA⟩ := hdA
  obtain ⟨dB, qB, agB⟩ := hdB
  have q0A := C.q0 _ qA; have q0B := C.q0 _ qB
  refine ⟨fun p => if p < m + c then dA else if p < m + r then dB else a0,
    ⟨fun p _ _ => ?_, by simp only [if_pos (show m < m + c by omega)]; exact pA, fun p a1 a2 z hz => ?_,
      fun p a1 a2 z hBk hv hw => ?_⟩⟩
  · by_cases e : p < m + c
    · rw [if_pos e]; exact q0A
    by_cases e' : p < m + r
    · rw [if_neg e, if_pos e']; exact q0B
    · rw [if_neg e, if_neg e']; exact h0
  · by_cases e1 : p < m + c
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
  · by_cases e1 : p < m + c
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

end Two

/-! ## El descenso -/

section Any

variable {n : Nat} {zone sv : Nat → Nat} {m b : Nat}

/-- **`v` dentro del bloque `m`, con el separador `m` fijado, y un lado de cualquier longitud** que se puede cortar
(`SideSplit`). -/
theorem phantomFree_inner_any (hl : LocPair φ P0 P σ) (D : ChainN φ n zone)
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k) (hm1 : 1 ≤ m) (hmb : m < b) (hbn : b ≤ n)
    (hfix : FixedEnd n zone P0 b) (hmid : midFusion φ < Nn) (hsplit : SideSplit φ n zone sv m b Nn)
    {v : Nat} (hv : stepVar φ σ = some v) (hzv : zone v = m)
    (hfa : ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + m → c z = c' z) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) :
    PhantomFree φ P0 P Nn σ := by
  have eqsv : ∀ {k z}, 1 ≤ k → k < n → zone z = n + k → z = sv k := fun {k z} a c h =>
    D.sep1 k a c z (sv k) h (hsv k a c)
  refine phantomFree_of_descent hσ0 hσN (fun x u w => frN φ sv m b x.id.step u.id.step w.id.step)
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, h0, hx0, hu0, hw0⟩ := t.b3 hS
  have hpos := frN_pos (φ := φ) (sv := sv) (m := m) (b := b) (i := x.id.step) (j := u.id.step) (l := w.id.step)
  have hle := frN_le (φ := φ) (sv := sv) (i := x.id.step) (j := u.id.step) (l := w.id.step) hmb
  have hun : ∀ k z, 1 ≤ k → k < frN φ sv m b x.id.step u.id.step w.id.step → zone z = n + (m + k) →
      ¬ InW φ x.id.step u.id.step w.id.step z := fun k z a c hz => by
    rw [eqsv (by omega) (by omega) hz]; exact frN_un a c
  have hrd : m + frN φ sv m b x.id.step u.id.step w.id.step < b →
      ∀ z, zone z = n + (m + frN φ sv m b x.id.step u.id.step w.id.step) → InW φ x.id.step u.id.step w.id.step z :=
    fun h z hz => by rw [eqsv (by omega) (by omega) hz]; exact frN_rd hmb (by omega)
  have glue := fun {sR : Nat → Assign} (O : SideOut φ n zone P0 P x.id.step u.id.step w.id.step a0 m b sR) =>
    glue_one_tri hl D hv hzv hmb hbn hfa hfix h0 hx0 hu0 hw0 O
  by_cases hr : 2 ≤ frN φ sv m b x.id.step u.id.step w.id.step
  · -- el testigo del paso de variable de `t_c`
    obtain ⟨c, hc1, hcr, gA, gB⟩ := hsplit _ _ _ (hS.steps _ _ t.xu).1 (hS.steps _ _ t.xu).2
      (hS.steps _ _ (hS.symm _ _ t.xu)).1 (hS.steps _ _ (hS.symm _ _ t.xu)).2 (hS.steps _ _ (hS.symm _ _ t.xw)).1
      (hS.steps _ _ (hS.symm _ _ t.xw)).2 hr
    have hsvc : sv (m + c) < φ.nVars := D.sepv _ (by rw [hsv _ (by omega) (by omega)]; omega)
      (by rw [hsv _ (by omega) (by omega)]; omega)
    have rc : ReadsAt φ (varStep (sv (m + c))) (sv (m + c)) := reads_self (stepVar_var hsvc)
    obtain ⟨c1, c2, c3, F⟩ := faces_Pw hS t hx0 hu0 hw0 (by simp only [varStep]; omega)
      (by simp only [varStep, midFusion] at hmid ⊢; omega) rc (frN_un hc1 hcr)
      (fun x' u' w' t' h' => ih x' u' w' t' (by
        have := frN_of (φ := φ) (sv := sv) (m := m) (b := b) (i := x'.id.step) (j := u'.id.step) (l := w'.id.step)
          hc1 h'
        omega))
    have C := sideCap_of_facesP hl F
    obtain ⟨sR, O⟩ := side_twoD hc1 hcr (by omega) hfix h0 C
      (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact rc) hun hrd
      (by
        rcases F.pick3 (fun z => m ≤ zone z ∧ zone z < m + c) with ⟨d, qd, ag⟩ | h
        · exact ⟨d, qd.1, qd, ag⟩
        · exact absurd h gA)
      (by
        rcases F.pick3 _ with h | h
        · exact h
        · exact absurd h gB)
    exact glue O
  · -- `r = 1`: el testigo de `σ`
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
    exact glue (side_right1 (by omega) hfix h0 qd (hl.sub _ qd) ag (fun h z hz => by
      have e : frN φ sv m b x.id.step u.id.step w.id.step = 1 := by omega
      rw [e] at hrd; exact hrd (by omega) z hz))

end Any

end GPathB

end AbsSatBingo.Model
