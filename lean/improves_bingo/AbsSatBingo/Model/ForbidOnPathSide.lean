-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnPathSide.lean
import AbsSatBingo.Model.ForbidOnPathN

/-!
# Un lado de un camino de unidades: cortes de una o dos variables

Se fija `v`, el único del corte `m - 1` (`lo v = m - 1`, `hi v = m`). El **lado derecho** son las unidades `m, m+1, …`.
`probe_split_wide.jl` dice cómo cerrarlo en las cadenas anchas: un corte intermedio `c` (leído entero por la ventana del
testigo: las caras coinciden en él) y una **cola** `e` (el primer corte que lee entero el triángulo, o uno fijo):

* **`SideOutP`**: una fuente por unidad (de `P0`; la de la unidad `m`, de `P`), unidas en los cortes, y que coinciden con
  `a0` en lo leído de cada unidad salvo `v`. Es simétrica: no distingue la primera unidad de una variable de la última,
  así que el lado izquierdo es el derecho del camino al revés (`loR`, `hiR`).
* **`sideP_one`**: sin corte intermedio; una cara de `P` hasta la cola.
* **`sideP_two`**: dos regiones, `m … c` (de `P`) y `c+1 … e`, unidas en el corte `c` por el testigo. **El corte puede
  tener dos variables**: con la numeración en orden, la ventana del paso de `z₂` lee `z₁` y `z₂`.
* **`glueP_sides_tri`**: los dos lados, unidos en `v` porque las fuentes de sus dos unidades son de `P`, cierran el
  triángulo por `glueP_tri`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {σ : Int}

/-- **La salida de un lado**: las unidades `m, m+1, …`. -/
structure SideOutP (φ : Cnf) (lo hi : Nat → Nat) (P0 P : Assign → Prop) (i j l : Int) (a0 : Assign) (v m : Nat)
    (src : Nat → Assign) : Prop where
  p0   : ∀ p, m ≤ p → P0 (src p)
  pm   : P (src m)
  join : ∀ k, m ≤ k → ∀ z, lo z ≤ k → k + 1 ≤ hi z → src k z = src (k + 1) z
  agr  : ∀ p, m ≤ p → ∀ z, InU lo hi p z → z ≠ v → InW φ i j l z → src p z = a0 z

section Right

variable {lo hi : Nat → Nat} {i j l : Int} {a0 : Assign} {v m : Nat}

/-- Lo que hay junto a `v` a su izquierda es `v`. -/
def OnlyV (lo hi : Nat → Nat) (v m : Nat) : Prop := ∀ z, lo z < m → m ≤ hi z → z = v

/-- La cola `e`: el triángulo lee entero su corte, o las ramas de `P0` lo leen igual. -/
def TailAt (φ : Cnf) (lo hi : Nat → Nat) (P0 : Assign → Prop) (i j l : Int) (e : Nat) : Prop :=
  ∀ z, lo z ≤ e → e + 1 ≤ hi z → InW φ i j l z ∨ ∀ c c', P0 c → P0 c' → c z = c' z

/-- **Sin corte intermedio**: una cara de `P` hasta la cola `e`. -/
theorem sideP_one {e : Nat} (hme : m ≤ e) (hhiv : hi v = m) (hv1 : OnlyV lo hi v m) (h0 : P0 a0) (htl : TailAt φ lo hi P0 i j l e)
    (hd : ∃ d, P d ∧ P0 d ∧ Agr φ i j l (fun z => (m ≤ lo z ∧ lo z ≤ e) ∨ (lo z ≤ e ∧ e + 1 ≤ hi z ∧ z ≠ v)) d a0) :
    ∃ src, SideOutP φ lo hi P0 P i j l a0 v m src := by
  obtain ⟨d, pd, qd, ag⟩ := hd
  refine ⟨fun p => if p ≤ e then d else a0, fun p _ => ?_, by simp only [if_pos hme]; exact pd,
    fun k hk z h1 h2 => ?_, fun p hp z hz hzv hw => ?_⟩
  · by_cases h : p ≤ e
    · rw [if_pos h]; exact qd
    · rw [if_neg h]; exact h0
  · by_cases e1 : k < e
    · rw [if_pos (by omega), if_pos (by omega)]
    by_cases e2 : k = e
    · subst e2
      rw [if_pos (Nat.le_refl _), if_neg (by omega)]
      have hzv : z ≠ v := fun hz => by
        subst hz
        omega
      rcases htl z h1 h2 with hw | hf
      · exact ag z (Or.inr ⟨h1, h2, hzv⟩) hw
      · exact hf d a0 qd h0
    · rw [if_neg (by omega), if_neg (by omega)]
  · unfold InU at hz
    by_cases h : p ≤ e
    · rw [if_pos h]
      have hlo : m ≤ lo z := Classical.byContradiction (fun hn => hzv (hv1 z (by omega) (by omega)))
      exact ag z (Or.inl ⟨hlo, by omega⟩) hw
    · rw [if_neg h]

/-- **Dos regiones**, unidas en el corte `c` por las caras del testigo. -/
theorem sideP_two {c e : Nat} (hmc : m ≤ c) (hce : c < e) (hhiv : hi v = m) (hv1 : OnlyV lo hi v m) (h0 : P0 a0)
    (htl : TailAt φ lo hi P0 i j l e) {Q : Assign → Prop} {lam : Int} (C : SideCap φ P0 P Q i j l lam a0)
    (hlc : ∀ z, lo z ≤ c → c + 1 ≤ hi z → ReadsAt φ lam z)
    (hdA : ∃ d, P d ∧ Q d ∧ Agr φ i j l (fun z => m ≤ lo z ∧ lo z ≤ c) d a0)
    (hdB : ∃ d, Q d ∧ Agr φ i j l (fun z => (c + 1 ≤ lo z ∧ lo z ≤ e) ∨ (lo z ≤ e ∧ e + 1 ≤ hi z ∧ z ≠ v)) d a0) :
    ∃ src, SideOutP φ lo hi P0 P i j l a0 v m src := by
  obtain ⟨dA, pA, qA, agA⟩ := hdA
  obtain ⟨dB, qB, agB⟩ := hdB
  have q0A := C.q0 _ qA; have q0B := C.q0 _ qB
  have nv : ∀ {z}, m ≤ hi z → z ≠ v → m ≤ lo z := fun {z} h hzv =>
    Classical.byContradiction (fun hn => hzv (hv1 z (by omega) h))
  refine ⟨fun p => if p ≤ c then dA else if p ≤ e then dB else a0, fun p _ => ?_,
    by simp only [if_pos hmc]; exact pA, fun k hk z h1 h2 => ?_, fun p hp z hz hzv hw => ?_⟩
  · by_cases e1 : p ≤ c
    · rw [if_pos e1]; exact q0A
    by_cases e2 : p ≤ e
    · rw [if_neg e1, if_pos e2]; exact q0B
    · rw [if_neg e1, if_neg e2]; exact h0
  · by_cases e1 : k < c
    · rw [if_pos (by omega), if_pos (by omega)]
    by_cases e2 : k = c
    · subst e2
      rw [if_pos (Nat.le_refl _), if_neg (by omega), if_pos (by omega)]
      exact C.win _ _ qA qB z (hlc z h1 h2)
    by_cases e3 : k < e
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    by_cases e4 : k = e
    · subst e4
      rw [if_neg (by omega), if_pos (Nat.le_refl _), if_neg (by omega), if_neg (by omega)]
      have hzv : z ≠ v := fun hz => by
        subst hz
        omega
      rcases htl z h1 h2 with hw | hf
      · exact agB z (Or.inr ⟨h1, h2, hzv⟩) hw
      · exact hf dB a0 q0B h0
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · unfold InU at hz
    have hlo := nv (by omega) hzv
    by_cases e1 : p ≤ c
    · rw [if_pos e1]; exact agA z ⟨hlo, by omega⟩ hw
    by_cases e2 : p ≤ e
    · rw [if_neg e1, if_pos e2]
      by_cases hl : c + 1 ≤ lo z
      · exact agB z (Or.inl ⟨hl, by omega⟩) hw
      · -- vive en el corte `c`: la de `A` la lleva
        rw [← C.win _ _ qA qB z (hlc z (by omega) (by omega))]
        exact agA z ⟨hlo, by omega⟩ hw
    · rw [if_neg e1, if_neg e2]

end Right

/-! ## El camino al revés, y pegar los dos lados -/

/-- El camino al revés. -/
def loR (n : Nat) (lo hi : Nat → Nat) (z : Nat) : Nat := if lo z < n then n - 1 - hi z else lo z
def hiR (n : Nat) (lo hi : Nat → Nat) (z : Nat) : Nat := if lo z < n then n - 1 - lo z else hi z

section Glue

variable {n : Nat} {lo hi : Nat → Nat}

theorem inU_rev (D : PathN φ n lo hi) {p z : Nat} (hz : lo z < n) (hp : p < n) :
    InU (loR n lo hi) (hiR n lo hi) (n - 1 - p) z ↔ InU lo hi p z := by
  have := D.ord z hz
  unfold InU loR hiR
  rw [if_pos hz, if_pos hz]
  omega

/-- **Pegar los dos lados en `v`.** -/
theorem glueP_sides_tri (hl : LocPair φ P0 P σ) (D : PathN φ n lo hi) {v : Nat} (hv : stepVar φ σ = some v)
    {m : Nat} (hm1 : 1 ≤ m) (hmn : m < n) (hlov : lo v = m - 1) (hhiv : hi v = m) (hv1 : OnlyV lo hi v m)
    {x u w : PathNodeId} {a0 : Assign} (h0 : P0 a0) (hx0 : pidOfAssign φ a0 x.id.step = x)
    (hu0 : pidOfAssign φ a0 u.id.step = u) (hw0 : pidOfAssign φ a0 w.id.step = w) {sL sR : Nat → Assign}
    (OL : SideOutP φ (loR n lo hi) (hiR n lo hi) P0 P x.id.step u.id.step w.id.step a0 v (n - m) sL)
    (OR : SideOutP φ lo hi P0 P x.id.step u.id.step w.id.step a0 v m sR)
    (hpv : InW φ x.id.step u.id.step w.id.step v → ∃ c, P c ∧ c v = a0 v) : TriOf φ P x u w := by
  have sv : ∀ {c c'}, P c → P c' → c v = c' v := fun q q' => hl.sameVar hv q q'
  let src : Nat → Assign := fun p => if p < m then sL (n - 1 - p) else sR p
  have sLp : ∀ p, p < m → src p = sL (n - 1 - p) := fun p h => by simp only [src]; rw [if_pos h]
  have sRp : ∀ p, m ≤ p → src p = sR p := fun p h => by simp only [src]; rw [if_neg (by omega)]
  have pL : P (sL (n - m)) := OL.pm
  have pR : P (sR m) := OR.pm
  have pL' : P (src (m - 1)) := by rw [sLp _ (by omega), show n - 1 - (m - 1) = n - m by omega]; exact pL
  have hs : ∀ j, j < n → P0 (src j) := by
    intro j hj
    by_cases h : j < m
    · rw [sLp j h]; exact OL.p0 _ (by omega)
    · rw [sRp j (by omega)]; exact OR.p0 _ (by omega)
  have hJ : JoinP lo hi src := by
    intro k z h1 h2
    by_cases c1 : k + 1 < m
    · rw [sLp _ (by omega), sLp _ c1]
      have hz : lo z < n := by omega
      have := OL.join (n - 1 - (k + 1)) (by omega) z (by unfold loR; rw [if_pos hz]; omega)
        (by unfold hiR; rw [if_pos hz]; omega)
      rw [show n - 1 - (k + 1) + 1 = n - 1 - k by omega] at this
      exact this.symm
    by_cases c2 : k + 1 = m
    · have e := hv1 z (by omega) (by omega)
      subst e
      rw [sLp _ (by omega), sRp _ (by omega), show n - 1 - k = n - m by omega, show k + 1 = m by omega]
      exact sv pL pR
    · rw [sRp _ (by omega), sRp _ (by omega)]
      exact OR.join k (by omega) z h1 h2
  have hvU : ∀ j, j < n → InU lo hi j v → P (src j) := by
    intro j _ h
    unfold InU at h
    rcases (by omega : j = m - 1 ∨ j = m) with rfl | rfl
    · exact pL'
    · rw [sRp _ (Nat.le_refl _)]; exact pR
  refine glueP_tri hl D hv ⟨m, hmn, by unfold InU; omega⟩ h0 hx0 hu0 hw0 hs hJ hvU (fun b hb z hz hw => ?_)
  have hzn : lo z < n := by omega
  have hU : InU lo hi b z := by have := D.ord z hzn; unfold InU; omega
  by_cases hzv : z = v
  · -- `v`: de una rama de `P`
    subst hzv
    obtain ⟨c, pc, ec⟩ := hpv hw
    have hb' : b = m - 1 := by omega
    subst hb'
    rw [sv pL' pc]; exact ec
  by_cases h : b < m
  · rw [sLp _ h]
    exact OL.agr _ (by omega) z ((inU_rev D hzn hb).mpr hU) hzv hw
  · rw [sRp _ (by omega)]
    exact OR.agr b (by omega) z hU hzv hw

end Glue

end GPathB

end AbsSatBingo.Model
