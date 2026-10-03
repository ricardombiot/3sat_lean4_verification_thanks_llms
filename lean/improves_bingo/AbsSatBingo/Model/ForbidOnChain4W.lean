-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4W.lean
import AbsSatBingo.Model.ForbidOnChain4R

/-!
# El testigo de una ventana: el lector en cuatro bloques con cualquier orden

En el tercer paso de una cláusula la ventana lee sus tres variables. El testigo de la regla en ese paso da tres caras
que pasan por un mismo nodo de esa ventana: **las tres leen igual todas las variables de la cláusula**. Si la cláusula
es la del bloque `{s1} ∪ M ∪ {s2}`, sus caras leen igual `s1` y `s2` a la vez, y los dos cortes quedan libres. Es lo
que faltaba en `ForbidOnChain4` para `v` dentro de un bloque (`probe_hard4_read.jl`: los triángulos de ese caso
aparecen en el lector y todos se salvan).

* `faces_Pw`: las caras del testigo de cualquier paso, con las ramas leyendo igual lo que lee la ventana del paso.
* `glue4_PI`, `glue4_triI`: la rama de cuatro fuentes con `v` en `C` o en `N`.
* `v ∈ C` (`phantomFree_chain4_C`): rangos «lee `s3`» (testigo de `σ`), «lee `s2`» (testigo de `s3`), «lee `s1`»
  (testigo de `s2`), «nada» (**testigo de la ventana** de `{s1, m, s2}`).
* `v ∈ N` (`phantomFree_chain4_N`): «lee `s2` y `s3`» (`σ`), «solo `s2`» (testigo de `s3`, caras por el nodo que lee
  `s2`), «solo `s3`» y «nada» (testigo de la ventana).
* **`Chain4R φ`**: cada variable tiene datos para cualquier lectura (`Struct4`) o está en `C` o `N` de una cadena de
  cuatro cuyo bloque `{s1} ∪ M ∪ {s2}` tiene una ventana que lee `s1` y `s2` (`Chain4W`); `v` en `A` o `M` es el
  mismo caso leyendo la cadena al revés. **`hRead_of_chain4R`**: la hipótesis del lector.
* **`reader_on_chain4LR`**: con `Chain4L` (las líneas) y `Chain4R` (la lectura), el lector no se atasca **con
  cualquier orden de lectura**, sin hipótesis sobre la máquina. `reader_fourChainL_any`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

-- ============================================================
-- La rama de cuatro fuentes con `v` dentro de un bloque
-- ============================================================

section GlueI

variable {s1 s2 s3 : Nat} {A M N C : Nat → Prop} {d4 d3 d2 d1 a0 : Assign} {P0 P : Assign → Prop} {σ : Int}

/-- **De `P`** con `v` en `C` (fuente `d4` de `P`) o en `N` (fuente `d3` de `P`). -/
theorem glue4_PI (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat} (hv : stepVar φ σ = some v)
    (h0 : P0 a0) (h1 : P0 d1) (h2 : P0 d2) (h3 : P0 d3) (h4 : P0 d4) (e1 : d1 s1 = d2 s1) (e2 : d2 s2 = d3 s2)
    (e3 : d3 s3 = d4 s3) (hpos : (C v ∧ P d4) ∨ (N v ∧ P d3)) :
    P (glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0) := by
  refine p_of_sources hl (glue4_P0 hl D h0 h1 h2 h3 h4 e1 e2 e3) (fun h => by rw [hv] at h; cases h)
    (fun z hz => ?_)
  rw [hv] at hz; cases hz
  have tv : ∀ {Q : Nat → Prop} {cl : Clause}, ClVar cl v → ClIn Q cl → Q v := by
    intro Q cl hcv hin
    obtain ⟨a, b, c⟩ := hin
    rcases hcv with e | e | e
    · rw [e]; exact a
    · rw [e]; exact b
    · rw [e]; exact c
  rcases hpos with ⟨hc, q4⟩ | ⟨hn, q3⟩
  · refine ⟨⟨d4, q4, g4C hc⟩, fun cl hcl hcv => ?_⟩
    rcases D.cl cl hcl with hi | hi | hi | hi | hi
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl hc)))) (tv hcv hi)
    · rcases tv hcv hi with h | h
      · exact absurd hc (fun hc => D.dAC v h hc)
      · rw [h] at hc; exact absurd hc D.cS1
    · rcases tv hcv hi with h | h | h
      · rw [h] at hc; exact absurd hc D.cS1
      · exact absurd hc (fun hc => D.dMC v h hc)
      · rw [h] at hc; exact absurd hc D.cS2
    · rcases tv hcv hi with h | h | h
      · rw [h] at hc; exact absurd hc D.cS2
      · exact absurd hc (fun hc => D.dNC v h hc)
      · rw [h] at hc; exact absurd hc D.cS3
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d4, q4, g4B4 D e3 i1, g4B4 D e3 i2, g4B4 D e3 i3⟩
  · refine ⟨⟨d3, q3, g4N D (Or.inl hn)⟩, fun cl hcl hcv => ?_⟩
    rcases D.cl cl hcl with hi | hi | hi | hi | hi
    · exact absurd (Or.inr (Or.inr (Or.inl hn))) (tv hcv hi)
    · rcases tv hcv hi with h | h
      · exact absurd hn (fun hn => D.dAN v h hn)
      · rw [h] at hn; exact absurd hn D.nS1
    · rcases tv hcv hi with h | h | h
      · rw [h] at hn; exact absurd hn D.nS1
      · exact absurd hn (fun hn => D.dMN v h hn)
      · rw [h] at hn; exact absurd hn D.nS2
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d3, q3, g4B3 D e2 i1, g4B3 D e2 i2, g4B3 D e2 i3⟩
    · rcases tv hcv hi with h | h
      · exact absurd hn (fun hn => D.dNC v hn h)
      · rw [h] at hn; exact absurd hn D.nS3

end GlueI

namespace GPathB

variable {P0 P : Assign → Prop} {Nn σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

section Tools

variable {s1 s2 s3 : Nat} {A M N C : Nat → Prop}

/-- **Cerrar un triángulo con cuatro fuentes**, `v` en `C` o en `N`. -/
theorem glue4_triI (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat}
    (hv : stepVar φ σ = some v) {x u w : PathNodeId} {a0 d1 d2 d3 d4 : Assign} (h0 : P0 a0)
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) (p1 : P0 d1) (p2 : P0 d2) (p3 : P0 d3) (p4 : P0 d4)
    (e1 : d1 s1 = d2 s1) (e2 : d2 s2 = d3 s2) (e3 : d3 s3 = d4 s3) (hpos : (C v ∧ P d4) ∨ (N v ∧ P d3))
    (a4 : Agr φ x.id.step u.id.step w.id.step C d4 a0)
    (a3 : Agr φ x.id.step u.id.step w.id.step (fun z => N z ∨ z = s3) d3 a0)
    (a2 : Agr φ x.id.step u.id.step w.id.step (fun z => M z ∨ z = s2) d2 a0)
    (a1 : Agr φ x.id.step u.id.step w.id.step (fun z => A z ∨ z = s1) d1 a0) : TriOf φ P x u w :=
  ⟨glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0, glue4_PI hl D hv h0 p1 p2 p3 p4 e1 e2 e3 hpos,
    (glue4_pid (Or.inl rfl) a4 a3 a2 a1).trans hx0, (glue4_pid (Or.inr (Or.inl rfl)) a4 a3 a2 a1).trans hu0,
    (glue4_pid (Or.inr (Or.inr rfl)) a4 a3 a2 a1).trans hw0⟩

/-- Fuera de `v`, `C` tiene a lo sumo una variable. -/
theorem le1_Cv (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat} (hc : C v) : Le1 (fun z => C z ∧ z ≠ v) := by
  intro z1 z2 h1 h2
  by_cases e : z1 = z2
  · exact e
  · exact absurd (D.cardC z1 z2 v h1.1 h2.1 hc e h1.2 h2.2) (fun h => h)

end Tools

/-- **Las caras del testigo del paso `lam`**, para un triángulo que no lee una variable `s` que lee la ventana de
`lam`: las ramas de las tres son de `P` y pasan por el mismo nodo de `lam`. -/
theorem faces_Pw (hS : PhStruct φ P0 Nn R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w) {a0 : Assign}
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < Nn) {s : Nat}
    (hs : ReadsAt φ lam s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s → TriOf φ P x' u' w') :
    ∃ c1 c2 c3, Faces φ (fun c => P c ∧ pidOfAssign φ c lam = pidOfAssign φ c1 lam) a0 c1 c2 c3
      x.id.step u.id.step w.id.step := by
  obtain ⟨n, hns, hn⟩ := t.wit hS h0 hN
  rcases hn with hn | ⟨t1, t2, t3⟩
  · exfalso
    apply hno
    rcases hn with e | e | e
    · exact inW_of_reads (Or.inl rfl) (by rw [← e, hns]; exact hs)
    · exact inW_of_reads (Or.inr (Or.inl rfl)) (by rw [← e, hns]; exact hs)
    · exact inW_of_reads (Or.inr (Or.inr rfl)) (by rw [← e, hns]; exact hs)
  have fr : ∀ {y z : PathNodeId}, InW φ y.id.step z.id.step n.id.step s :=
    inW_of_reads (Or.inr (Or.inr rfl)) (by rw [hns]; exact hs)
  obtain ⟨c1, q1, c1x, c1u, c1n⟩ := hP x u n t1 fr
  obtain ⟨c2, q2, c2x, c2w, c2n⟩ := hP x w n t2 fr
  obtain ⟨c3, q3, c3u, c3w, c3n⟩ := hP u w n t3 fr
  rw [hns] at c1n c2n c3n
  exact ⟨c1, c2, c3, ⟨⟨q1, rfl⟩, ⟨q2, c2n.trans c1n.symm⟩, ⟨q3, c3n.trans c1n.symm⟩, c1x.trans hx0.symm,
    c2x.trans hx0.symm, c1u.trans hu0.symm, c3u.trans hu0.symm, c2w.trans hw0.symm, c3w.trans hw0.symm⟩⟩

/-- Dos fuentes del mismo testigo leen igual lo que lee su ventana. -/
theorem agree_at {c1 d d' : Assign} {lam : Int} (h : pidOfAssign φ d lam = pidOfAssign φ c1 lam)
    (h' : pidOfAssign φ d' lam = pidOfAssign φ c1 lam) {s : Nat} (hs : ReadsAt φ lam s) : d s = d' s :=
  var_of_reads (h.trans h'.symm) hs

section Left

variable {s1 s2 s3 : Nat} {A M N C : Nat → Prop}

/-- **El lado izquierdo con el testigo de la ventana**: fuentes para `A ∪ {s1}` y `M ∪ {s2}`, de `a0` o de las caras. -/
theorem left_window (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) {a0 c1 c2 c3 : Assign}
    {i j l lam : Int} (h0 : P0 a0)
    (F : Faces φ (fun c => P c ∧ pidOfAssign φ c lam = pidOfAssign φ c1 lam) a0 c1 c2 c3 i j l)
    (hw1 : ReadsAt φ lam s1) (hno2 : ¬ InW φ i j l s2) :
    ∃ d1 d2, P0 d1 ∧ P0 d2 ∧ d1 s1 = d2 s1 ∧ pidOfAssign φ d2 lam = pidOfAssign φ c1 lam ∧
      Agr φ i j l (fun z => A z ∨ z = s1) d1 a0 ∧ Agr φ i j l (fun z => M z ∨ z = s2) d2 a0 := by
  by_cases h1 : InW φ i j l s1
  · obtain ⟨d2, ⟨q2, p2⟩, ag2⟩ := F.pick (no3_or D.cardM (le1_eq s1))
    exact ⟨a0, d2, h0, hl.sub _ q2, (ag2 s1 (Or.inr rfl) h1).symm, p2, agr_refl',
      agr_or (agr_mono ag2 (fun z h => Or.inl h)) (fun iw => absurd iw hno2)⟩
  · obtain ⟨d1, ⟨q1, p1⟩, ag1⟩ := F.pick D.cardA
    obtain ⟨d2, ⟨q2, p2⟩, ag2⟩ := F.pick (no3_of_le1 D.cardM)
    exact ⟨d1, d2, hl.sub _ q1, hl.sub _ q2, agree_at p1 p2 hw1, p2, agr_or ag1 (fun iw => absurd iw h1),
      agr_or ag2 (fun iw => absurd iw hno2)⟩

end Left

-- ============================================================
-- `v ∈ C`
-- ============================================================

open Classical in
/-- El primer índice que se cumple de tres (`3` si ninguno). -/
noncomputable def rkF (p q r : Prop) : Nat := if p then 0 else if q then 1 else if r then 2 else 3

theorem rkF_p {p q r : Prop} (h : p) : rkF p q r = 0 := by simp [rkF, h]
theorem rkF_q {p q r : Prop} (h : q) : rkF p q r ≤ 1 := by
  unfold rkF; split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
theorem rkF_1 {p q r : Prop} (hp : ¬ p) (hq : q) : rkF p q r = 1 := by simp [rkF, hp, hq]
theorem rkF_2 {p q r : Prop} (hp : ¬ p) (hq : ¬ q) (hr : r) : rkF p q r = 2 := by simp [rkF, hp, hq, hr]
theorem rkF_3 {p q r : Prop} (hp : ¬ p) (hq : ¬ q) (hr : ¬ r) : rkF p q r = 3 := by simp [rkF, hp, hq, hr]

/-- Un triángulo que cumple la segunda tiene rango menor que uno que no cumple ni la primera ni la segunda. -/
theorem rkF_q_lt {p q r p' q' r' : Prop} (h : q') (hp : ¬ p) (hq : ¬ q) : rkF p' q' r' < rkF p q r := by
  have h1 := rkF_q (p := p') (r := r') h
  have h2 : 2 ≤ rkF p q r := by
    unfold rkF; rw [if_neg hp, if_neg hq]; split <;> omega
  omega

section CaseC

variable {s1 s2 s3 : Nat} {A M N C : Nat → Prop}

theorem agrC (hl : LocPair φ P0 P σ) {v : Nat} (hv : stepVar φ σ = some v) {Q : Assign → Prop}
    {a0 c1 c2 c3 d : Assign} {i j l : Int} (F : Faces φ Q a0 c1 c2 c3 i j l) (q1 : P c1) (q2 : P c2) (qd : P d)
    (ag : Agr φ i j l (fun z => C z ∧ z ≠ v) d a0) : Agr φ i j l C d a0 := by
  intro z hz iw
  by_cases e : z = v
  · subst e; exact vfix4 hl hv F q1 q2 qd iw
  · exact ag z ⟨hz, e⟩ iw

/-- **Cuatro bloques, `v ∈ C`**, con el testigo de la ventana del bloque `{s1} ∪ M ∪ {s2}`. -/
theorem phantomFree_chain4_C (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat}
    (hv : stepVar φ σ = some v) (hC : C v) {k : Int} (hk0 : 0 ≤ k) (hkN : k < Nn) (hk1 : ReadsAt φ k s1)
    (hk2 : ReadsAt φ k s2) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) (hN : midFusion φ < Nn) : PhantomFree φ P0 P Nn σ := by
  have rng : ∀ {s : Nat}, s < φ.nVars → 0 ≤ varStep s ∧ varStep s < Nn := by
    intro s hs
    have h1 : 0 ≤ varStep s := by simp only [varStep]; omega
    have h2 : varStep s < midFusion φ := by simp only [varStep, midFusion]; omega
    exact ⟨h1, by omega⟩
  have hCv := le1_Cv D hC
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => rkF (InW φ x.id.step u.id.step w.id.step s3) (InW φ x.id.step u.id.step w.id.step s2)
      (InW φ x.id.step u.id.step w.id.step s1))
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  by_cases h3 : InW φ x.id.step u.id.step w.id.step s3
  · -- base: el testigo de `σ`
    rcases faces_sigma hS hanch hσ0 hσN t hP0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
    · exact h
    obtain ⟨d4, q4, ag4⟩ := F.pick (no3_or hCv (le1_eq s3))
    exact glue4_triI hl D hv hP0 hx0 hu0 hw0 hP0 hP0 hP0 (hl.sub _ q4) rfl rfl (ag4 s3 (Or.inr rfl) h3).symm
      (Or.inl ⟨hC, q4⟩) (agrC hl hv F F.q1 F.q2 q4 (agr_mono ag4 (fun z h => Or.inl h))) agr_refl' agr_refl'
      agr_refl'
  by_cases h2 : InW φ x.id.step u.id.step w.id.step s2
  · -- el testigo del paso de `s3`
    obtain ⟨l0, lN⟩ := rng D.s3v
    obtain ⟨c1, c2, c3, F⟩ := faces_P hS t hx0 hu0 hw0 l0 lN (stepVar_var D.s3v) h3
      (fun x' u' w' t' h' => ih x' u' w' t' (by rw [rkF_p h', rkF_1 h3 h2]; omega))
    obtain ⟨d4, ⟨q4, s4e⟩, ag4⟩ := F.pick (no3_of_le1 hCv)
    obtain ⟨d3, ⟨q3, s3e⟩, ag3⟩ := F.pick (no3_or D.cardN (le1_eq s2))
    exact glue4_triI hl D hv hP0 hx0 hu0 hw0 hP0 hP0 (hl.sub _ q3) (hl.sub _ q4) rfl (ag3 s2 (Or.inr rfl) h2).symm
      (s3e.trans s4e.symm) (Or.inl ⟨hC, q4⟩) (agrC hl hv F F.q1.1 F.q2.1 q4 ag4)
      (agr_or (agr_mono ag3 (fun z h => Or.inl h)) (fun iw => absurd iw h3)) agr_refl' agr_refl'
  by_cases h1 : InW φ x.id.step u.id.step w.id.step s1
  · -- el testigo del paso de `s2`
    obtain ⟨l0, lN⟩ := rng D.s2v
    obtain ⟨c1, c2, c3, F⟩ := faces_P hS t hx0 hu0 hw0 l0 lN (stepVar_var D.s2v) h2
      (fun x' u' w' t' h' => ih x' u' w' t' (rkF_q_lt h' h3 h2))
    obtain ⟨d2, ⟨q2, s2e⟩, ag2⟩ := F.pick (no3_or D.cardM (le1_eq s1))
    obtain ⟨d3, ⟨q3, s3e⟩, ag3⟩ := F.pick (no3_or D.cardN hCv)
    exact glue4_triI hl D hv hP0 hx0 hu0 hw0 hP0 (hl.sub _ q2) (hl.sub _ q3) (hl.sub _ q3)
      (ag2 s1 (Or.inr rfl) h1).symm (s2e.trans s3e.symm) rfl (Or.inl ⟨hC, q3⟩)
      (agrC hl hv F F.q1.1 F.q2.1 q3 (agr_mono ag3 (fun z h => Or.inr h)))
      (agr_or (agr_mono ag3 (fun z h => Or.inl h)) (fun iw => absurd iw h3))
      (agr_or (agr_mono ag2 (fun z h => Or.inl h)) (fun iw => absurd iw h2)) agr_refl'
  · -- nada: el testigo de la ventana de `{s1} ∪ M ∪ {s2}`
    obtain ⟨c1, c2, c3, F⟩ := faces_Pw hS t hx0 hu0 hw0 hk0 hkN hk2 h2
      (fun x' u' w' t' h' => ih x' u' w' t' (rkF_q_lt h' h3 h2))
    obtain ⟨d1, d2, p1, p2, e1, pd2, ag1, ag2⟩ := left_window hl D hP0 F hk1 h2
    obtain ⟨d3, ⟨q3, pd3⟩, ag3⟩ := F.pick (no3_or D.cardN hCv)
    exact glue4_triI hl D hv hP0 hx0 hu0 hw0 p1 p2 (hl.sub _ q3) (hl.sub _ q3) e1 (agree_at pd2 pd3 hk2) rfl
      (Or.inl ⟨hC, q3⟩) (agrC hl hv F F.q1.1 F.q2.1 q3 (agr_mono ag3 (fun z h => Or.inr h)))
      (agr_or (agr_mono ag3 (fun z h => Or.inl h)) (fun iw => absurd iw h3)) ag2 ag1

end CaseC

-- ============================================================
-- `v ∈ N`
-- ============================================================

section CaseN

variable {s1 s2 s3 : Nat} {A M N C : Nat → Prop}

theorem agrN (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat} (hv : stepVar φ σ = some v)
    (hn : N v) {Q : Assign → Prop} {a0 c1 c2 c3 d : Assign} {i j l : Int} (F : Faces φ Q a0 c1 c2 c3 i j l)
    (q1 : P c1) (q2 : P c2) (qd : P d) (h3 : InW φ i j l s3 → d s3 = a0 s3) :
    Agr φ i j l (fun z => N z ∨ z = s3) d a0 := by
  intro z hz iw
  rcases hz with hz | hz
  · rw [D.cardN z v hz hn] at iw ⊢; exact vfix4 hl hv F q1 q2 qd iw
  · subst hz; exact h3 iw

/-- Solo se lee `s2`, y lo lee el primer nodo: el testigo del paso de `s3`, con las dos caras por el primer nodo. -/
theorem cN_one (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat} (hv : stepVar φ σ = some v)
    (hn : N v) (hS : PhStruct φ P0 Nn R Tf) (hN : midFusion φ < Nn) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (hx : ReadsAt φ x.id.step s2) (hno : ¬ InW φ x.id.step u.id.step w.id.step s3)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s2 →
      InW φ x'.id.step u'.id.step w'.id.step s3 → TriOf φ P x' u' w') : TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨c1, c2, c3, F, q1, q2⟩ := faces_Px hl hS t hx0 hu0 hw0 (lam := varStep s3) (by simp only [varStep]; omega)
    (by have := D.s3v; simp only [varStep, midFusion] at hN ⊢; omega) (stepVar_var D.s3v) hno hx hP
  obtain ⟨d4, ⟨q4, s4e⟩, ag4⟩ := F.pick D.cardC
  exact glue4_triI hl D hv hP0 hx0 hu0 hw0 hP0 hP0 (hl.sub _ q1) q4 rfl (var_of_reads F.e1 hx).symm s4e.symm
    (Or.inr ⟨hn, q1⟩) ag4 (agrN hl D hv hn F q1 q2 q1 (fun iw => absurd iw hno)) agr_refl' agr_refl'

/-- **Cuatro bloques, `v ∈ N`**, con el testigo de la ventana del bloque `{s1} ∪ M ∪ {s2}`. -/
theorem phantomFree_chain4_N (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat}
    (hv : stepVar φ σ = some v) (hn : N v) {k : Int} (hk0 : 0 ≤ k) (hkN : k < Nn) (hk1 : ReadsAt φ k s1)
    (hk2 : ReadsAt φ k s2) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) (hN : midFusion φ < Nn) : PhantomFree φ P0 P Nn σ := by
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => rk4 (InW φ x.id.step u.id.step w.id.step s2) (InW φ x.id.step u.id.step w.id.step s3))
    (fun R Tf hS hanch x u w t ih => ?_)
  by_cases h2 : InW φ x.id.step u.id.step w.id.step s2
  · by_cases h3 : InW φ x.id.step u.id.step w.id.step s3
    · -- base: el testigo de `σ`
      obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
      rcases faces_sigma hS hanch hσ0 hσN t hP0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
      · exact h
      obtain ⟨d3, q3, ag3⟩ := F.pick (no3_or (le1_eq s2) (le1_eq s3))
      exact glue4_triI hl D hv hP0 hx0 hu0 hw0 hP0 hP0 (hl.sub _ q3) hP0 rfl (ag3 s2 (Or.inl rfl) h2).symm
        (ag3 s3 (Or.inr rfl) h3) (Or.inr ⟨hn, q3⟩) agr_refl' (agrN hl D hv hn F F.q1 F.q2 q3
          (fun iw => ag3 s3 (Or.inr rfl) iw)) agr_refl' agr_refl'
    · -- solo `s2`: el nodo que lo lee al primer sitio
      refine of_reads_first hS (H := fun x u w => ¬ InW φ x.id.step u.id.step w.id.step s3)
        (fun _ _ _ h => not_inW_swap12 h) (fun _ _ _ h => not_inW_swap23 h)
        (fun x' u' w' t' h' hx' => cN_one hl D hv hn hS hN t' hx' h' (fun a b c t'' p q => ih a b c t'' (by
          rw [rk4_pq p q, rk4_1 h2 h3]; omega))) x u w t h3 h2
  · obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
    -- el testigo de la ventana; sus caras leen `s2`
    obtain ⟨c1, c2, c3, F⟩ := faces_Pw hS t hx0 hu0 hw0 hk0 hkN hk2 h2
      (fun x' u' w' t' h' => ih x' u' w' t' (by
        have := rk4_p (q := InW φ x'.id.step u'.id.step w'.id.step s3) h'
        by_cases h3 : InW φ x.id.step u.id.step w.id.step s3
        · rw [rk4_2 h2 h3]; omega
        · rw [rk4_3 h2 h3]; omega))
    obtain ⟨d1, d2, p1, p2, e1, pd2, ag1, ag2⟩ := left_window hl D hP0 F hk1 h2
    by_cases h3 : InW φ x.id.step u.id.step w.id.step s3
    · -- solo `s3`: `N ∪ {s3}` de una cara que coincide con `a0` en `s3`; `C` de `a0`
      obtain ⟨d3, ⟨q3, pd3⟩, ag3⟩ := F.pick (no3_of_le1 (le1_eq s3))
      exact glue4_triI hl D hv hP0 hx0 hu0 hw0 p1 p2 (hl.sub _ q3) hP0 e1 (agree_at pd2 pd3 hk2)
        (ag3 s3 rfl h3) (Or.inr ⟨hn, q3⟩) agr_refl' (agrN hl D hv hn F F.q1.1 F.q2.1 q3 (fun iw => ag3 s3 rfl iw))
        ag2 ag1
    · -- nada: `N ∪ {s3}` y `C` de una misma cara
      obtain ⟨d3, ⟨q3, pd3⟩, ag3⟩ := F.pick D.cardC
      exact glue4_triI hl D hv hP0 hx0 hu0 hw0 p1 p2 (hl.sub _ q3) (hl.sub _ q3) e1 (agree_at pd2 pd3 hk2) rfl
        (Or.inr ⟨hn, q3⟩) ag3 (agrN hl D hv hn F F.q1.1 F.q2.1 q3 (fun iw => absurd iw h3)) ag2 ag1

end CaseN

end GPathB

-- ============================================================
-- La clase y el lector
-- ============================================================

/-- **`Chain4W`**: una cadena de cuatro bloques cuyo bloque `{s1} ∪ M ∪ {s2}` tiene una ventana que lee `s1` y `s2`
(la de su cláusula). -/
def Chain4W (φ : Cnf) (s1 s2 s3 : Nat) (A M N C : Nat → Prop) : Prop :=
  Chain4Data φ s1 s2 s3 A M N C ∧ ∃ k, 0 ≤ k ∧ k < fusionTop φ ∧ ReadsAt φ k s1 ∧ ReadsAt φ k s2

/-- **`Chain4R φ`**: cada variable tiene datos para cualquier lectura, o está en `C` o en `N` de una cadena `Chain4W`
(en `A` o `M`, leyendo la cadena al revés). -/
def Chain4R (φ : Cnf) : Prop :=
  ∀ v, Struct4 φ v ∨ ∃ s1 s2 s3 A M N C, Chain4W φ s1 s2 s3 A M N C ∧ (C v ∨ N v)

namespace GPathB

open Driver Machine MachineOn

variable {P0 P : Assign → Prop} {Nn σ : Int}

theorem phantomFree_of_chain4R (hcl : Chain4R φ) (hl : LocPair φ P0 P σ) (hσ0 : 0 ≤ σ) (hσN : σ < Nn)
    (hN : midFusion φ < Nn) (hF : fusionTop φ ≤ Nn) : PhantomFree φ P0 P Nn σ := by
  cases hv : stepVar φ σ with
  | none => exact phantomFree_none hl hv hσ0 hσN
  | some v =>
    rcases hcl v with h | ⟨s1, s2, s3, A, M, N, C, ⟨D, k, hk0, hkF, hk1, hk2⟩, hc | hn⟩
    · exact phantomFree_of_struct4 hl hv h hσ0 hσN hN
    · exact phantomFree_chain4_C hl D hv hc hk0 (by omega) hk1 hk2 hσ0 hσN hN
    · exact phantomFree_chain4_N hl D hv hn hk0 (by omega) hk1 hk2 hσ0 hσN hN

/-- **La hipótesis de la lectura vale en toda fórmula `Chain4R`.** -/
theorem hRead_of_chain4R (hcl : Chain4R φ) (k : NodeId) : HRead φ (stepCount φ) (SolE φ (stepCount φ) k) := by
  intro R r _ hr1 hrT
  exact phantomFree_of_chain4R hcl (locPair_read _ k R r) (by omega) hrT (by unfold stepCount midFusion; omega)
    (by unfold stepCount fusionTop; omega)

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector no se atasca, con cualquier orden de lectura**, en toda fórmula `Chain4L` (las líneas) y `Chain4R`
(la lectura), sin hipótesis sobre la máquina. -/
theorem reader_on_chain4LR (hbd : Bounded φ) (hL : Chain4L φ) (hR : Chain4R φ) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on hbd (phantomAt_of_chain4L hbd hL) (fun k => hRead_of_chain4R hR k) hkv hr

end MachineOn

-- ============================================================
-- Un caso concreto
-- ============================================================

/-- La ventana de la cláusula `(¬x5 ∨ x4 ∨ x6)` lee `x5` y `x6`. -/
theorem win_fourChainL_56 :
    ReadsAt fourChainL (clauseStep fourChainL 1 2) 5 ∧ ReadsAt fourChainL (clauseStep fourChainL 1 2) 6 := by
  have hj : fourChainL.clauses[1]? = some ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩ := rfl
  refine ⟨⟨clauseStep fourChainL 1 0, Or.inr (Or.inr ⟨by simp [clauseStep, fourChainL], by simp [clauseStep, fourChainL]⟩),
    stepVar_clause hj 0 (by omega)⟩, ⟨clauseStep fourChainL 1 2, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩⟩

/-- La ventana de la cláusula `(¬x6 ∨ x1 ∨ x7)` lee `x7` y `x6`. -/
theorem win_fourChainL_76 :
    ReadsAt fourChainL (clauseStep fourChainL 2 2) 7 ∧ ReadsAt fourChainL (clauseStep fourChainL 2 2) 6 := by
  have hj : fourChainL.clauses[2]? = some ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩ := rfl
  refine ⟨⟨clauseStep fourChainL 2 2, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩,
    ⟨clauseStep fourChainL 2 0, Or.inr (Or.inr ⟨by simp [clauseStep, fourChainL], by simp [clauseStep, fourChainL]⟩),
      stepVar_clause hj 0 (by omega)⟩⟩

theorem chain4R_fourChainL : Chain4R fourChainL := by
  intro v
  by_cases hs : v = 5 ∨ v = 6 ∨ v = 7
  · exact Or.inl (struct4_fourChainL_sep hs)
  by_cases h9 : 9 ≤ v
  · exact Or.inl (struct4_fourChainL_out h9)
  by_cases hr : v = 1 ∨ v = 3 ∨ v = 8
  · -- en la orientación `5, 6, 7`: `N = {1}`, `C = {3, 8}`
    refine Or.inr ⟨_, _, _, _, _, _, _, ⟨chain4Data_fourChainL, clauseStep fourChainL 1 2,
      by simp [clauseStep, fourChainL], by simp [clauseStep, fusionTop, fourChainL], win_fourChainL_56⟩, ?_⟩
    rcases hr with h | h | h
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · -- al revés, `7, 6, 5`: `N = {4}`, `C = {0, 2}`
    refine Or.inr ⟨_, _, _, _, _, _, _, ⟨chain4Data_fourChainL_rev, clauseStep fourChainL 2 2,
      by simp [clauseStep, fourChainL], by simp [clauseStep, fusionTop, fourChainL], win_fourChainL_76⟩, ?_⟩
    by_cases h4 : v = 4
    · exact Or.inr h4
    · exact Or.inl (by omega)

namespace MachineOn

open GPathB Driver Machine

/-- **El lector no se atasca en `fourChainL` con cualquier orden de lectura.** Cuatro bloques, numeración cruzada,
sin ninguna hipótesis. -/
theorem reader_fourChainL_any {kv : NodeId × GPathB} (hkv : kv ∈ runM .on fourChainL) {R : List NodeId}
    {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a fourChainL ∧ (∀ r ∈ R, selOfAssign fourChainL a r.step = r) ∧
      CT g' (pidOfAssign fourChainL a) :=
  reader_on_chain4LR bounded_fourChainL chain4L_fourChainL chain4R_fourChainL hkv hr

end MachineOn

end AbsSatBingo.Model
