-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain6BI.lean
import AbsSatBingo.Model.ForbidOnChain6B

/-!
# `chain6_bisect_lit`: seis bloques en orden de bisección, sin hipótesis

`scripts/cnf/chain6_bisect_lit.cnf` (variables desde 0): la cadena de `chain6_cross` con las cláusulas en orden de
bisección de bloques, `B0, B1, B2 | B5, B4 | B3`, y los literales de `B4` y de la unión `B3` ordenados:

`(x0 ∨ x2 ∨ x6) ∧ (¬x6 ∨ x4 ∨ x7) ∧ (¬x7 ∨ x5 ∨ x8) ∧ (¬x10 ∨ x11 ∨ x12) ∧ (x10 ∨ x3 ∨ ¬x9) ∧ (x9 ∨ ¬x8 ∨ x1)`.

Separadores `s1 … s5 = x6, x7, x8, x9, x10`; bloques `{x0, x2}, {x4}, {x5}, {x1}, {x3}, {x11, x12}`.

Cada línea de la cláusula `j` ve el prefijo de `j + 1` cláusulas (`phantomAt_of_prefix`), y en él la variable fijada
`v` es un separador de una cadena corta (lados de hasta tres bloques, extremos libres: `case_sep`), escrita como
`zoneV` y comprobada con `decide`. Una variable de dentro de un bloque final se vuelve separador con un bloque vacío
delante. En la unión (la última cláusula), lo que fija `k` corta la cadena:

* `p = 0`, `v = s4`: `k` (el último literal de `B4`) ya fija `s4` (`phantomFree_fixedLoc`);
* `p = 1`, `v = s3`: `k` fija `s4`; lados de tres bloques (libre) y uno (fijo);
* `p = 2`, `v = x1` (dentro de `B3`): `k` fija `s3`; un solo lado de tres bloques (`phantomFree_inner`).

Resultado: **`phantomAt_chain6B`**, **`machineExact_chain6B`**, **`spineVerdictOn_iff_chain6B`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- Las seis cláusulas. -/
def c6b0 : Clause := ⟨⟨0, true⟩, ⟨2, true⟩, ⟨6, true⟩⟩
def c6b1 : Clause := ⟨⟨6, false⟩, ⟨4, true⟩, ⟨7, true⟩⟩
def c6b2 : Clause := ⟨⟨7, false⟩, ⟨5, true⟩, ⟨8, true⟩⟩
def c6b3 : Clause := ⟨⟨10, false⟩, ⟨11, true⟩, ⟨12, true⟩⟩
def c6b4 : Clause := ⟨⟨10, true⟩, ⟨3, true⟩, ⟨9, false⟩⟩
def c6b5 : Clause := ⟨⟨9, true⟩, ⟨8, false⟩, ⟨1, true⟩⟩

/-- **`chain6_bisect_lit`.** -/
def chain6B : Cnf := ⟨13, [c6b0, c6b1, c6b2, c6b3, c6b4, c6b5]⟩

/-- Sus prefijos. -/
def chain6B1 : Cnf := ⟨13, [c6b0]⟩
def chain6B2 : Cnf := ⟨13, [c6b0, c6b1]⟩
def chain6B3 : Cnf := ⟨13, [c6b0, c6b1, c6b2]⟩
def chain6B4 : Cnf := ⟨13, [c6b0, c6b1, c6b2, c6b3]⟩
def chain6B5 : Cnf := ⟨13, [c6b0, c6b1, c6b2, c6b3, c6b4]⟩

theorem bounded_chain6B : Bounded chain6B := by
  intro c hc
  simp only [chain6B, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Clause.Bounded, chain6B, c6b0, c6b1, c6b2, c6b3, c6b4, c6b5]

namespace GPathB

open Driver Machine MachineOn

variable {ψ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int}

/-- **Un separador con los dos lados cortos y los extremos libres**, en una cadena concreta. -/
theorem case_sep (hl : LocPair ψ P0 P σ) {n : Nat} {vals sps : List Nat} (C : ChainN ψ n (zoneV n vals))
    (hsv : ∀ k, k < n → 1 ≤ k → zoneV n vals (sps.getD (k - 1) 0) = n + k) {v m : Nat}
    (hv : stepVar ψ σ = some v) (hzv : zoneV n vals v = n + m) (hm1 : 1 ≤ m) (hmn : m < n)
    (hL : m ≤ 3 ∧ n - m ≤ 2) (hmid : midFusion ψ < Nn)
    (hwL : 3 ≤ m → ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt ψ lam (sps.getD (m - 1 - 1) 0) ∧
      ReadsAt ψ lam (sps.getD (m - 2 - 1) 0))
    (hσ0 : 0 ≤ σ) (hσN : σ < Nn) : PhantomFree ψ P0 P Nn σ :=
  phantomFree_bisect hl C (sv := fun k => sps.getD (k - 1) 0) (fun k h1 h2 => hsv k h2 h1) hv
    (fun h => absurd h (by omega)) (fun h => hwL (by omega)) hmid hzv hm1 (a := 0) (b := n) (by omega) hmn
    (Nat.le_refl _) (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) (Or.inl (by omega))
    (Or.inl (by omega)) hσ0 hσN

theorem clVar_l1 (c : Clause) : ClVar c c.l1.v := Or.inl rfl
theorem clVar_l2 (c : Clause) : ClVar c c.l2.v := Or.inr (Or.inl rfl)
theorem clVar_l3 (c : Clause) : ClVar c c.l3.v := Or.inr (Or.inr rfl)

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-! ## Las cadenas de cada línea -/

theorem ch1_0 : ChainN chain6B1 3 (zoneV 3 [4, 6, 1, 6, 6, 6, 5, 6, 6, 6, 6, 6, 6]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch1_1 : ChainN chain6B1 3 (zoneV 3 [1, 6, 4, 6, 6, 6, 5, 6, 6, 6, 6, 6, 6]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch1_2 : ChainN chain6B1 2 (zoneV 2 [0, 4, 0, 4, 4, 4, 3, 4, 4, 4, 4, 4, 4]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch2_0 : ChainN chain6B2 2 (zoneV 2 [0, 4, 0, 4, 1, 4, 3, 1, 4, 4, 4, 4, 4]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch2_1 : ChainN chain6B2 3 (zoneV 3 [0, 6, 0, 6, 5, 6, 4, 1, 6, 6, 6, 6, 6]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch2_2 : ChainN chain6B2 3 (zoneV 3 [0, 6, 0, 6, 1, 6, 4, 5, 6, 6, 6, 6, 6]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch3_0 : ChainN chain6B3 3 (zoneV 3 [0, 6, 0, 6, 1, 2, 4, 5, 2, 6, 6, 6, 6]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch3_1 : ChainN chain6B3 4 (zoneV 4 [0, 8, 0, 8, 1, 7, 5, 6, 2, 8, 8, 8, 8]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch3_2 : ChainN chain6B3 4 (zoneV 4 [0, 8, 0, 8, 1, 2, 5, 6, 7, 8, 8, 8, 8]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch4_0 : ChainN chain6B4 2 (zoneV 2 [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 1]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch4_1 : ChainN chain6B4 2 (zoneV 2 [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 3, 1]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch4_2 : ChainN chain6B4 2 (zoneV 2 [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 1, 3]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch5_0 : ChainN chain6B5 2 (zoneV 2 [4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 3, 1, 1]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch5_1 : ChainN chain6B5 3 (zoneV 3 [6, 6, 6, 4, 6, 6, 6, 6, 6, 1, 5, 2, 2]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem ch5_2 : ChainN chain6B5 3 (zoneV 3 [6, 6, 6, 1, 6, 6, 6, 6, 6, 4, 5, 2, 2]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
/-- La cadena entera. -/
theorem ch6 : ChainN chain6B 6 (zoneV 6 [0, 3, 0, 4, 1, 2, 7, 8, 9, 10, 11, 5, 5]) :=
  chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Las líneas de cada cláusula -/

/-- Los casos de una línea: tras fijar la posición `p`, `v` es la variable de ese literal. -/
theorem lit_v {c : Clause} {p : Nat} {v : Nat} (h : (litAt c p).v = v) : (litAt c p).v = v := h

/-- **Primera cláusula.** -/
theorem phantomAt_chain6B1 {T : Int} (hT0 : clauseStep chain6B1 0 0 ≤ T) (hT2 : T ≤ clauseStep chain6B1 0 2)
    (hT : 1 ≤ T) : PhantomAt chain6B1 T := by
  refine phantomAt_of_lineLocalF (bounded_prefix bounded_chain6B 1 : Bounded chain6B1) (j0 := 0) (c0 := c6b0) rfl hT0 hT2 hT
    (fun {_ _ _ N v} p hp hTp hpv hl hv _ _ hσ0 hσN hTN => ?_)
  have hmid : midFusion chain6B1 < N := by rw [hTp] at hTN; simp only [clauseStep, midFusion, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega
  rcases p with _ | _ | _ | p
  · obtain rfl : v = 0 := hpv.symm
    exact case_sep hl ch1_0 (sps := [0, 6]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 2 := hpv.symm
    exact case_sep hl ch1_1 (sps := [2, 6]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 6 := hpv.symm
    exact case_sep hl ch1_2 (sps := [6]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · omega

/-- **Segunda cláusula.** -/
theorem phantomAt_chain6B2 {T : Int} (hT0 : clauseStep chain6B2 1 0 ≤ T) (hT2 : T ≤ clauseStep chain6B2 1 2)
    (hT : 1 ≤ T) : PhantomAt chain6B2 T := by
  refine phantomAt_of_lineLocalF (bounded_prefix bounded_chain6B 2 : Bounded chain6B2) (j0 := 1) (c0 := c6b1) rfl hT0 hT2 hT
    (fun {_ _ _ N v} p hp hTp hpv hl hv _ _ hσ0 hσN hTN => ?_)
  have hmid : midFusion chain6B2 < N := by rw [hTp] at hTN; simp only [clauseStep, midFusion, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega
  rcases p with _ | _ | _ | p
  · obtain rfl : v = 6 := hpv.symm
    exact case_sep hl ch2_0 (sps := [6]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 4 := hpv.symm
    exact case_sep hl ch2_1 (sps := [6, 4]) (by decide) hv (m := 2) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 7 := hpv.symm
    exact case_sep hl ch2_2 (sps := [6, 7]) (by decide) hv (m := 2) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · omega

/-- **Tercera cláusula**: con lados de tres bloques, la ventana de `B1` (lee `s1`, `s2`). -/
theorem phantomAt_chain6B3 {T : Int} (hT0 : clauseStep chain6B3 2 0 ≤ T) (hT2 : T ≤ clauseStep chain6B3 2 2)
    (hT : 1 ≤ T) : PhantomAt chain6B3 T := by
  refine phantomAt_of_lineLocalF (bounded_prefix bounded_chain6B 3 : Bounded chain6B3) (j0 := 2) (c0 := c6b2) rfl hT0 hT2 hT
    (fun {_ _ _ N v} p hp hTp hpv hl hv _ _ hσ0 hσN hTN => ?_)
  have hmid : midFusion chain6B3 < N := by rw [hTp] at hTN; simp only [clauseStep, midFusion, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega
  have hj1 : chain6B3.clauses[1]? = some c6b1 := rfl
  have w1 : ∃ lam, 0 ≤ lam ∧ lam < N ∧ ReadsAt chain6B3 lam 7 ∧ ReadsAt chain6B3 lam 6 :=
    ⟨clauseStep chain6B3 1 2, by simp only [clauseStep]; omega,
      by rw [hTp] at hTN; simp only [clauseStep, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega,
      readsAt_clause hj1 (clVar_l3 c6b1), readsAt_clause hj1 (clVar_l1 c6b1)⟩
  rcases p with _ | _ | _ | p
  · obtain rfl : v = 7 := hpv.symm
    exact case_sep hl ch3_0 (sps := [6, 7]) (by decide) hv (m := 2) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 5 := hpv.symm
    exact case_sep hl ch3_1 (sps := [6, 7, 5]) (by decide) hv (m := 3) (by decide) (by omega) (by omega)
      (by omega) hmid (fun _ => w1) hσ0 hσN
  · obtain rfl : v = 8 := hpv.symm
    exact case_sep hl ch3_2 (sps := [6, 7, 8]) (by decide) hv (m := 3) (by decide) (by omega) (by omega)
      (by omega) hmid (fun _ => w1) hσ0 hσN
  · omega

/-- **Cuarta cláusula** (`B5`, aún suelta). -/
theorem phantomAt_chain6B4 {T : Int} (hT0 : clauseStep chain6B4 3 0 ≤ T) (hT2 : T ≤ clauseStep chain6B4 3 2)
    (hT : 1 ≤ T) : PhantomAt chain6B4 T := by
  refine phantomAt_of_lineLocalF (bounded_prefix bounded_chain6B 4 : Bounded chain6B4) (j0 := 3) (c0 := c6b3) rfl hT0 hT2 hT
    (fun {_ _ _ N v} p hp hTp hpv hl hv _ _ hσ0 hσN hTN => ?_)
  have hmid : midFusion chain6B4 < N := by rw [hTp] at hTN; simp only [clauseStep, midFusion, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega
  rcases p with _ | _ | _ | p
  · obtain rfl : v = 10 := hpv.symm
    exact case_sep hl ch4_0 (sps := [10]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 11 := hpv.symm
    exact case_sep hl ch4_1 (sps := [11]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 12 := hpv.symm
    exact case_sep hl ch4_2 (sps := [12]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · omega

/-- **Quinta cláusula** (`B4`, unida a `B5`). -/
theorem phantomAt_chain6B5 {T : Int} (hT0 : clauseStep chain6B5 4 0 ≤ T) (hT2 : T ≤ clauseStep chain6B5 4 2)
    (hT : 1 ≤ T) : PhantomAt chain6B5 T := by
  refine phantomAt_of_lineLocalF (bounded_prefix bounded_chain6B 5 : Bounded chain6B5) (j0 := 4) (c0 := c6b4) rfl hT0 hT2 hT
    (fun {_ _ _ N v} p hp hTp hpv hl hv _ _ hσ0 hσN hTN => ?_)
  have hmid : midFusion chain6B5 < N := by rw [hTp] at hTN; simp only [clauseStep, midFusion, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega
  rcases p with _ | _ | _ | p
  · obtain rfl : v = 10 := hpv.symm
    exact case_sep hl ch5_0 (sps := [10]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 3 := hpv.symm
    exact case_sep hl ch5_1 (sps := [3, 10]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · obtain rfl : v = 9 := hpv.symm
    exact case_sep hl ch5_2 (sps := [9, 10]) (by decide) hv (m := 1) (by decide) (by omega) (by omega)
      (by omega) hmid (fun h => absurd h (by omega)) hσ0 hσN
  · omega

/-- **La unión** (`B3`, la última): lo que fija `k` corta la cadena. -/
theorem phantomAt_chain6B6 {T : Int} (hT0 : clauseStep chain6B 5 0 ≤ T) (hT2 : T ≤ clauseStep chain6B 5 2)
    (hT : 1 ≤ T) : PhantomAt chain6B T := by
  refine phantomAt_of_lineLocalF bounded_chain6B (j0 := 5) (c0 := c6b5) rfl hT0 hT2 hT
    (fun {P0 _ σ N v} p hp hTp hpv hl hv hL3 hfix hσ0 hσN hTN => ?_)
  have hmid : midFusion chain6B < N := by rw [hTp] at hTN; simp only [clauseStep, midFusion, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega
  have hj1 : chain6B.clauses[1]? = some c6b1 := rfl
  have hj4 : chain6B.clauses[4]? = some c6b4 := rfl
  have hj5 : chain6B.clauses[5]? = some c6b5 := rfl
  have hsv : ∀ k, 1 ≤ k → k < 6 → zoneV 6 [0, 3, 0, 4, 1, 2, 7, 8, 9, 10, 11, 5, 5]
      ([6, 7, 8, 9, 10].getD (k - 1) 0) = 6 + k := by
    have h : ∀ k, k < 6 → 1 ≤ k → zoneV 6 [0, 3, 0, 4, 1, 2, 7, 8, 9, 10, 11, 5, 5]
        ([6, 7, 8, 9, 10].getD (k - 1) 0) = 6 + k := by decide
    exact fun k h1 h2 => h k h2 h1
  rcases p with _ | _ | _ | p
  · -- `v = s4`, ya fijada por `k` (el último literal de `B4`)
    obtain rfl : v = 9 := hpv.symm
    have hk : stepVar chain6B (T - 1) = some 9 := by
      rw [hTp, show clauseStep chain6B 5 0 - 1 = clauseStep chain6B 4 2 by simp only [clauseStep]; omega]
      exact stepVar_clause hj4 2 (by omega)
    have h3 : isL3 chain6B σ = false := by
      cases e : isL3 chain6B σ with
      | false => rfl
      | true =>
        have := hL3 e
        rw [this, hTp] at e
        exact absurd e (by decide)
    exact phantomFree_fixedLoc hl hv h3 (fun a b ha hb => hfix a b ha hb 9 hk) hσ0 hσN
  · -- `v = s3`; `k` fija `s4`
    obtain rfl : v = 8 := hpv.symm
    have hk : stepVar chain6B (T - 1) = some 9 := by
      rw [hTp, show clauseStep chain6B 5 1 - 1 = clauseStep chain6B 5 0 by simp only [clauseStep]; omega]
      exact stepVar_clause hj5 0 (by omega)
    refine phantomFree_bisect hl ch6 (sv := fun k => [6, 7, 8, 9, 10].getD (k - 1) 0) hsv hv
      (fun h => absurd h (by omega))
      (fun _ => ⟨clauseStep chain6B 1 2, by simp only [clauseStep]; omega,
        by rw [hTp] at hTN; simp only [clauseStep, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega,
        readsAt_clause hj1 (clVar_l3 c6b1), readsAt_clause hj1 (clVar_l1 c6b1)⟩)
      hmid (m := 3) (a := 0) (b := 4) (by decide) (by omega) (by omega) (by omega) (by omega)
      (fun h => absurd h (by omega)) (fun _ c c' qc qc' z hz => ?_) (Or.inl (by omega)) (Or.inl (by omega))
      hσ0 hσN
    rw [zoneV_eq (k := 10) (y := 9) (by omega) (by decide) hz]
    exact hfix c c' qc qc' 9 hk
  · -- `v = x1`, dentro de `B3`; `k` fija `s3`
    obtain rfl : v = 1 := hpv.symm
    have hk : stepVar chain6B (T - 1) = some 8 := by
      rw [hTp, show clauseStep chain6B 5 2 - 1 = clauseStep chain6B 5 1 by simp only [clauseStep]; omega]
      exact stepVar_clause hj5 1 (by omega)
    have S : SideData chain6B 6 (zoneV 6 [0, 3, 0, 4, 1, 2, 7, 8, 9, 10, 11, 5, 5])
        (fun k => [6, 7, 8, 9, 10].getD (k - 1) 0) P0 N 3 6 :=
      ⟨ch6, hsv, fun _ => ⟨clauseStep chain6B 4 2, by simp only [clauseStep]; omega,
        by rw [hTp] at hTN; simp only [clauseStep, prefixCnf, chain6B, chain6B1, chain6B2, chain6B3, chain6B4, chain6B5] at hTN ⊢; omega,
        readsAt_clause hj4 (clVar_l3 c6b4), readsAt_clause hj4 (clVar_l1 c6b4)⟩, hmid, by omega, by omega,
        by omega, fun h => absurd h (by omega), by omega⟩
    refine phantomFree_inner hl S (Or.inl (by omega)) hv (by decide) (fun c c' qc qc' z hz => ?_) hσ0 hσN
    rw [zoneV_eq (k := 9) (y := 8) (by omega) (by decide) hz]
    exact hfix c c' qc qc' 8 hk
  · omega


/-! ## Todas las líneas -/

/-- **`chain6_bisect_lit` cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_chain6B (T : Int) (hT : 1 ≤ T) : PhantomAt chain6B T := by
  have hb := bounded_chain6B
  have cs : ∀ j p : Nat, clauseStep chain6B j p = 28 + 3 * (j : Int) + (p : Int) := fun _ _ => by
    simp only [clauseStep, chain6B]; omega
  have hm : midFusion chain6B = 27 := by decide
  have hft : fusionTop chain6B = 46 := by decide
  by_cases hlow : T + 1 ≤ midFusion chain6B + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  rw [hm] at hlow
  have ft : ∀ j : Nat, j ≤ 6 → fusionTop (prefixCnf chain6B j) = 28 + 3 * (j : Int) := by
    intro j hj
    simp only [fusionTop, prefixCnf, chain6B, List.length_take, List.length_cons, List.length_nil]
    omega
  have cs' : ∀ m j p : Nat, clauseStep (prefixCnf chain6B m) j p = clauseStep chain6B j p := fun _ _ _ => rfl
  by_cases p0 : T ≤ clauseStep chain6B 0 2
  · rw [cs] at p0
    exact phantomAt_of_prefix hb (j := 1) (by rw [ft 1 (by omega)]; omega)
      (phantomAt_chain6B1 (by rw [show chain6B1 = prefixCnf chain6B 1 from rfl, cs', cs]; omega)
        (by rw [show chain6B1 = prefixCnf chain6B 1 from rfl, cs', cs]; omega) hT)
  by_cases p1 : T ≤ clauseStep chain6B 1 2
  · rw [cs] at p0 p1
    exact phantomAt_of_prefix hb (j := 2) (by rw [ft 2 (by omega)]; omega)
      (phantomAt_chain6B2 (by rw [show chain6B2 = prefixCnf chain6B 2 from rfl, cs', cs]; omega)
        (by rw [show chain6B2 = prefixCnf chain6B 2 from rfl, cs', cs]; omega) hT)
  by_cases p2 : T ≤ clauseStep chain6B 2 2
  · rw [cs] at p1 p2
    exact phantomAt_of_prefix hb (j := 3) (by rw [ft 3 (by omega)]; omega)
      (phantomAt_chain6B3 (by rw [show chain6B3 = prefixCnf chain6B 3 from rfl, cs', cs]; omega)
        (by rw [show chain6B3 = prefixCnf chain6B 3 from rfl, cs', cs]; omega) hT)
  by_cases p3 : T ≤ clauseStep chain6B 3 2
  · rw [cs] at p2 p3
    exact phantomAt_of_prefix hb (j := 4) (by rw [ft 4 (by omega)]; omega)
      (phantomAt_chain6B4 (by rw [show chain6B4 = prefixCnf chain6B 4 from rfl, cs', cs]; omega)
        (by rw [show chain6B4 = prefixCnf chain6B 4 from rfl, cs', cs]; omega) hT)
  by_cases p4 : T ≤ clauseStep chain6B 4 2
  · rw [cs] at p3 p4
    exact phantomAt_of_prefix hb (j := 5) (by rw [ft 5 (by omega)]; omega)
      (phantomAt_chain6B5 (by rw [show chain6B5 = prefixCnf chain6B 5 from rfl, cs', cs]; omega)
        (by rw [show chain6B5 = prefixCnf chain6B 5 from rfl, cs', cs]; omega) hT)
  by_cases p5 : T ≤ clauseStep chain6B 5 2
  · rw [cs] at p4
    exact phantomAt_chain6B6 (by rw [cs]; omega) p5 hT
  -- después de la última cláusula
  rw [cs] at p5
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step chain6B k d hd
    have hks := mapNodes_step chain6B (T - 1) k hk
    omega
  have hft' : fusionTop chain6B ≤ d.step := by rw [hds, hft]; omega
  refine ⟨fun r hr => by rw [reqOf_above chain6B d hft'] at hr; exact absurd hr List.not_mem_nil, ?_⟩
  have hsv : stepVar chain6B T = none := by
    have h1 : ¬ T ≤ 0 := by omega
    have h2 : ¬ T < midFusion chain6B := by rw [hm]; omega
    have h3 : ¬ T = midFusion chain6B := by rw [hm]; omega
    have h4 : fusionTop chain6B ≤ T := by rw [hft]; omega
    simp only [stepVar, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  exact phantomFree_none (locPair_up hb T k d) hsv (by omega) (show T < T + 1 by omega)

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **La máquina `:on` es exacta en `chain6_bisect_lit`**, sin hipótesis. -/
theorem machineExact_chain6B : MachineExact chain6B :=
  (machineExact_iff bounded_chain6B).2 phantomAt_chain6B

/-- **La espina `:on` decide `chain6_bisect_lit`.** -/
theorem spineVerdictOn_iff_chain6B : SpineVerdictOn chain6B ↔ Satisfiable chain6B :=
  spineVerdictOn_iff_of_phantomFree bounded_chain6B phantomAt_chain6B

end MachineOn

end AbsSatBingo.Model
