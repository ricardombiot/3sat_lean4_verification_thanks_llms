-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5C.lean
import AbsSatBingo.Model.ForbidOnChain5L

/-!
# La clase de cinco bloques

**`Chain5C φ s1 s2 s3 s4 zone`**: `φ` tiene cinco cláusulas en cadena, la `j`-ésima dentro del bloque `j`
(`Blk5`), las tres de en medio con sus dos separadores (sus ventanas los leen), y la última con `s4`. Con cualquier
numeración de las variables y cualquier orden de los literales dentro de cada cláusula.

* Las líneas de la cláusula `j < 4` solo ven el prefijo de `j + 1` cláusulas (`phantomAt_of_prefix`), y en esa línea
  solo se fijan variables de la cláusula `j`, el último bloque del prefijo. `phantomAt_of_lineLocal` lo recoge, y cada
  prefijo usa un lema ya demostrado: separador (`SepData`) con una y dos cláusulas, cadena de tres (`ChainData`) con
  tres, y con cuatro el separador `s3` (`phantomFree_chain4_s3`) o el bloque final (`phantomFree_chain4_C`).
* Las líneas de la última cláusula: `s4` (`phantomFree_chain5_s4`), las de dentro aún libres (`FreeBelow`) y el UP del
  tercer literal (`phantomFree_up_lastC`, con `s4` en el primer o segundo literal).
* El lector por separadores: T2 con `phantomFree_chain5_s4` y `_s3` en las dos orientaciones (`chain5Data_rev`).

Resultado: **`phantomAt_of_chain5C`**, **`machineExact_of_chain5C`**, **`spineVerdictOn_iff_of_chain5C`**,
**`reader_sep_of_chain5C`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- El bloque cerrado `j` de una cadena de cinco. -/
def Blk5 (s1 s2 s3 s4 : Nat) (zone : Nat → Nat) : Nat → Nat → Prop
  | 0, z => zone z = 0 ∨ z = s1
  | 1, z => z = s1 ∨ zone z = 1 ∨ z = s2
  | 2, z => z = s2 ∨ zone z = 2 ∨ z = s3
  | 3, z => z = s3 ∨ zone z = 3 ∨ z = s4
  | _, z => z = s4 ∨ zone z = 4

/-- **La clase de cinco bloques.** -/
structure Chain5C (φ : Cnf) (s1 s2 s3 s4 : Nat) (zone : Nat → Nat) : Prop where
  D   : Chain5Data φ s1 s2 s3 s4 zone
  len : φ.clauses.length = 5
  blk : ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → ClIn (Blk5 s1 s2 s3 s4 zone j) c
  w1  : ∀ c, φ.clauses[1]? = some c → ClVar c s1 ∧ ClVar c s2
  w2  : ∀ c, φ.clauses[2]? = some c → ClVar c s2 ∧ ClVar c s3
  w3  : ∀ c, φ.clauses[3]? = some c → ClVar c s3 ∧ ClVar c s4
  w4  : ∀ c, φ.clauses[4]? = some c → ClVar c s4

-- ============================================================
-- Herramientas
-- ============================================================

/-- La ventana del tercer paso de una cláusula lee sus tres variables. -/
theorem readsAt_clause {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c) {z : Nat} (hz : ClVar c z) :
    ReadsAt φ (clauseStep φ j 2) z := by
  rcases hz with rfl | rfl | rfl
  · exact ⟨clauseStep φ j 0, Or.inr (Or.inr ⟨by simp only [clauseStep]; omega, by simp only [clauseStep]; omega⟩),
      stepVar_clause hj 0 (by omega)⟩
  · exact ⟨clauseStep φ j 1, Or.inr (Or.inl ⟨by simp only [clauseStep]; omega, by simp only [clauseStep]; omega⟩),
      stepVar_clause hj 1 (by omega)⟩
  · exact ⟨clauseStep φ j 2, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩

theorem prefix_getElem? {m j : Nat} (h : j < m) : (prefixCnf φ m).clauses[j]? = φ.clauses[j]? := by
  simp only [prefixCnf]
  exact List.getElem?_take_of_lt h

theorem mem_prefix_clause {m : Nat} {c : Clause} (hc : c ∈ (prefixCnf φ m).clauses) :
    ∃ j, j < m ∧ φ.clauses[j]? = some c := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
  by_cases him : i < m
  · exact ⟨i, him, by rw [← prefix_getElem? him]; exact hi⟩
  · simp only [prefixCnf] at hi
    rw [List.getElem?_take, if_neg him] at hi
    cases hi

theorem bounded_prefix (hb : Bounded φ) (m : Nat) : Bounded (prefixCnf φ m) :=
  fun c hc => hb c (List.mem_of_mem_take hc)

theorem clauseStep_prefix (m j p : Nat) : clauseStep (prefixCnf φ m) j p = clauseStep φ j p := rfl

theorem clauseStep_inj {j j' p p' : Nat} (hp : p < 3) (hp' : p' < 3)
    (h : clauseStep φ j p = clauseStep φ j' p') : j = j' := by
  simp only [clauseStep] at h; omega

namespace GPathB

open Driver Machine MachineOn

/-- **Una línea dentro de una cláusula**: si fijar cualquier variable de la cláusula `j0` no deja familias fantasma
(para cualquier par local), la condición fuerte de las líneas de esa cláusula vale. -/
theorem phantomAt_of_lineLocal (hb : Bounded φ) {j0 : Nat} {c0 : Clause} (hj0 : φ.clauses[j0]? = some c0) {T : Int}
    (hT0 : clauseStep φ j0 0 ≤ T) (hT2 : T ≤ clauseStep φ j0 2) (hT : 1 ≤ T)
    (H : ∀ {P0 P : Assign → Prop} {σ N : Int} {v : Nat}, LocPair φ P0 P σ → stepVar φ σ = some v → ClVar c0 v →
      0 ≤ σ → σ < N → T ≤ N → PhantomFree φ P0 P N σ) : PhantomAt φ T := by
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step φ k d hd
    have hks := mapNodes_step φ (T - 1) k hk
    omega
  have hmid : midFusion φ < T := by
    have : midFusion φ < clauseStep φ j0 0 := by simp only [clauseStep, midFusion]; omega
    omega
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨r1, r2⟩ := reqOf_range hb r hr
    rw [hds] at r2
    cases hv : stepVar φ r.step with
    | none => exact phantomFree_none (locPair_filter T k r) hv (by omega) r2
    | some v =>
      obtain ⟨j, c, p, hj, hp, e, hpv⟩ := req_lit hb hr hv (by rw [hds]; exact hmid)
      have hjj : j = j0 := by rw [hds] at e; simp only [clauseStep] at e hT0 hT2; omega
      subst hjj
      rw [hj0] at hj; cases hj
      exact H (locPair_filter T k r) hv (hpv ▸ litAt_clVar c0 p) (by omega) r2 (Int.le_refl _)
  · cases hv : stepVar φ T with
    | none => exact phantomFree_none (locPair_up hb T k d) hv (by omega) (show T < T + 1 by omega)
    | some v =>
      obtain ⟨j, c, p, hj, hp, e, hpv⟩ := step_lit hv hmid
      have hjj : j = j0 := by simp only [clauseStep] at e hT0 hT2; omega
      subst hjj
      rw [hj0] at hj; cases hj
      exact H (locPair_up hb T k d) hv (hpv ▸ litAt_clVar c0 p) (by omega) (by omega) (by omega)

end GPathB

-- ============================================================
-- Los datos de cada prefijo
-- ============================================================

section Prefixes

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

/-- Las cláusulas del prefijo de `m` cláusulas están en sus bloques. -/
theorem Chain5C.blkP (C : Chain5C φ s1 s2 s3 s4 zone) {m : Nat} {c : Clause} (hc : c ∈ (prefixCnf φ m).clauses) :
    ∃ j, j < m ∧ ClIn (Blk5 s1 s2 s3 s4 zone j) c := by
  obtain ⟨j, hj, hjc⟩ := mem_prefix_clause hc
  exact ⟨j, hj, C.blk j c hjc⟩

/-- Un bloque sin una de sus variables no tiene tres distintas. -/
theorem no3_B0_minus (C : Chain5C φ s1 s2 s3 s4 zone) {v : Nat} (hv : zone v = 0 ∨ v = s1) :
    No3 (fun z => (zone z = 0 ∨ z = s1) ∧ z ≠ v) := by
  intro z1 z2 z3 ⟨h1, n1⟩ ⟨h2, n2⟩ ⟨h3, n3⟩ d12 d13 d23
  have c0 := C.D.card0
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · exact c0 z1 z2 z3 h1 h2 h3 d12 d13 d23
  · rcases hv with hv | hv
    · exact c0 z1 z2 v h1 h2 hv d12 n1 n2
    · exact n3 (h3.trans hv.symm)
  · rcases hv with hv | hv
    · exact c0 z1 z3 v h1 h3 hv d13 n1 n3
    · exact n2 (h2.trans hv.symm)
  · exact d23 (h2.trans h3.symm)
  · rcases hv with hv | hv
    · exact c0 z2 z3 v h2 h3 hv d23 n2 n3
    · exact n1 (h1.trans hv.symm)
  · exact d13 (h1.trans h3.symm)
  · exact d12 (h1.trans h2.symm)
  · exact d12 (h1.trans h2.symm)

/-- **Una cláusula**: separador en la propia variable. -/
theorem sepData_pre1 (C : Chain5C φ s1 s2 s3 s4 zone) {v : Nat} (hv : zone v = 0 ∨ v = s1) :
    SepData (prefixCnf φ 1) v v (fun _ => False) (fun z => (zone z = 0 ∨ z = s1) ∧ z ≠ v) := by
  refine ⟨fun h => absurd rfl h, fun h => h.2 rfl, fun _ h _ => h, Or.inl rfl, fun _ _ _ h _ _ _ _ _ => h,
    no3_B0_minus C hv, fun h => absurd rfl h, fun c hc => ?_⟩
  obtain ⟨j, hj, hin⟩ := C.blkP hc
  obtain rfl : j = 0 := by omega
  refine Or.inr (Or.inr (clIn_mono (B' := fun z => ((zone z = 0 ∨ z = s1) ∧ z ≠ v) ∨ z = v) hin (fun z hz => ?_)))
  by_cases e : z = v
  · exact Or.inr e
  · exact Or.inl ⟨hz, e⟩

/-- **Dos cláusulas**: separador `s1`. -/
theorem sepData_pre2 (C : Chain5C φ s1 s2 s3 s4 zone) {v : Nat} (hv : v = s1 ∨ zone v = 1 ∨ v = s2) :
    SepData (prefixCnf φ 2) v s1 (fun z => zone z = 0) (fun z => zone z = 1 ∨ z = s2) := by
  have D := C.D
  refine ⟨fun _ => D.s1v, ?_, fun z a b => ?_, ?_, D.card0, no3_or D.card1 (le1_eq s2), fun hne z1 z2 a b d => ?_,
    fun c hc => ?_⟩
  · rintro (h | h)
    · rw [D.z1] at h; omega
    · exact D.n12 h
  · rcases b with b | rfl
    · omega
    · rw [D.z2] at a; omega
  · rcases hv with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · have hvR : zone v = 1 ∨ v = s2 := by
      rcases hv with h | h | h
      · exact absurd h hne
      · exact Or.inl h
      · exact Or.inr h
    rcases a with a | a <;> rcases b with b | b
    · exact absurd (D.card1 z1 z2 a b) d
    · rcases hvR with h | h
      · exact Or.inl (D.card1 z1 v a h)
      · exact Or.inr (b.trans h.symm)
    · rcases hvR with h | h
      · exact Or.inr (D.card1 z2 v b h)
      · exact Or.inl (a.trans h.symm)
    · exact absurd (a.trans b.symm) d
  · obtain ⟨j, hj, hin⟩ := C.blkP hc
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact Or.inr (Or.inl hin)
    · refine Or.inr (Or.inr (clIn_mono (B' := fun z => (zone z = 1 ∨ z = s2) ∨ z = s1) hin (fun z hz => ?_)))
      rcases hz with h | h | h
      · exact Or.inr h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)

/-- **Tres cláusulas**: cadena de tres, con el último bloque `Z2 ∪ {s3}`. -/
theorem chainData_pre3 (C : Chain5C φ s1 s2 s3 s4 zone) {v : Nat} (hv : v = s2 ∨ zone v = 2 ∨ v = s3) :
    ChainData (prefixCnf φ 3) v s1 s2 (fun z => zone z = 0) (fun z => zone z = 1) (fun z => zone z = 2 ∨ z = s3) := by
  have D := C.D
  have z1 := D.z1; have z2 := D.z2; have z3 := D.z3
  refine ⟨D.s1v, D.s2v, D.n12, by omega, by omega, by omega, by omega, ?_, ?_, fun z a b => by omega,
    fun z a b => ?_, fun z a b => ?_, D.card0, no3_or D.card2 (le1_eq s3), D.card1, ?_, fun c hc => ?_⟩
  · rintro (h | h)
    · omega
    · exact D.n13 h
  · rintro (h | h)
    · omega
    · exact D.n23 h
  · rcases b with b | rfl <;> omega
  · rcases b with b | rfl <;> omega
  · rcases hv with h | h | h
    · exact Or.inr (Or.inl h)
    · refine Or.inl ⟨Or.inl h, fun y1 y2 b1 b2 e1 e2 => ?_⟩
      rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2
      · exact absurd (D.card2 y1 v b1 h) e1
      · exact absurd (D.card2 y1 v b1 h) e1
      · exact absurd (D.card2 y2 v b2 h) e2
      · exact b1.trans b2.symm
    · refine Or.inl ⟨Or.inr h, fun y1 y2 b1 b2 e1 e2 => ?_⟩
      rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2
      · exact D.card2 y1 y2 b1 b2
      · exact absurd (b2.trans h.symm) e2
      · exact absurd (b1.trans h.symm) e1
      · exact absurd (b1.trans h.symm) e1
  · obtain ⟨j, hj, hin⟩ := C.blkP hc
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact Or.inr (Or.inl hin)
    · refine Or.inr (Or.inr (Or.inl (clIn_mono (B' := fun z => zone z = 1 ∨ z = s1 ∨ z = s2) hin
        (fun z hz => ?_))))
      rcases hz with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · refine Or.inr (Or.inr (Or.inr (clIn_mono (B' := fun z => (zone z = 2 ∨ z = s3) ∨ z = s2) hin
        (fun z hz => ?_))))
      rcases hz with h | h | h
      · exact Or.inr h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)

/-- **Cuatro cláusulas**: cadena de cuatro, con el último bloque `{s3} ∪ Z3 ∪ {s4}`. -/
theorem chain4Data_pre4 (C : Chain5C φ s1 s2 s3 s4 zone) :
    Chain4Data (prefixCnf φ 4) s1 s2 s3 (fun z => zone z = 0) (fun z => zone z = 1) (fun z => zone z = 2)
      (fun z => zone z = 3 ∨ z = s4) := by
  have D := C.D
  have z1 := D.z1; have z2 := D.z2; have z3 := D.z3; have z4 := D.z4
  refine ⟨D.s1v, D.s2v, D.s3v, D.n12, D.n13, D.n23, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ?_, ?_, ?_, fun z a b => by omega, fun z a b => by omega, fun z a b => ?_,
    fun z a b => by omega, fun z a b => ?_, fun z a b => ?_, D.card0, no3_or D.card3 (le1_eq s4), D.card1, D.card2,
    fun c hc => ?_⟩
  · rintro (h | h)
    · omega
    · exact D.n14 h
  · rintro (h | h)
    · omega
    · exact D.n24 h
  · rintro (h | h)
    · omega
    · exact D.n34 h
  · rcases b with b | rfl <;> omega
  · rcases b with b | rfl <;> omega
  · rcases b with b | rfl <;> omega
  · obtain ⟨j, hj, hin⟩ := C.blkP hc
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl hin)
    · exact Or.inr (Or.inr (Or.inl hin))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hin)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (clIn_mono (B' := fun z => (zone z = 3 ∨ z = s4) ∨ z = s3) hin
        (fun z hz => ?_)))))
      rcases hz with h | h | h
      · exact Or.inr h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)

end Prefixes

-- ============================================================
-- Las líneas de la clase
-- ============================================================

theorem clIn_var {B : Nat → Prop} {c : Clause} (h : ClIn B c) {z : Nat} (hz : ClVar c z) : B z := by
  obtain ⟨a, b, d⟩ := h
  rcases hz with rfl | rfl | rfl
  · exact a
  · exact b
  · exact d

namespace GPathB

open Driver Machine MachineOn

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

/-- **El UP del tercer literal de la última cláusula con `s4` en el segundo**: `k` ya fija `s4`. -/
theorem phantomFree_up_lastC2 (hb : Bounded φ) (D : Chain5Data φ s1 s2 s3 s4 zone) {T : Int} {k d : NodeId} {j : Nat}
    {c : Clause} (hjlt : j < φ.clauses.length) (hj : φ.clauses[j]? = some c) (hT : T = clauseStep φ j 2)
    (h2 : c.l2.v = s4) (hz3 : zone c.l3.v = 4) {k1 k2 : Int} (hk1 : 0 ≤ k1 ∧ k1 < T + 1 ∧ ReadsAt φ k1 s1 ∧ ReadsAt φ k1 s2)
    (hk2 : 0 ≤ k2 ∧ k2 < T + 1 ∧ ReadsAt φ k2 s2 ∧ ReadsAt φ k2 s3) :
    PhantomFree φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
      (fun a => SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) (T + 1) T := by
  have hl := locPair_up hb T k d
  have hv : stepVar φ T = some c.l3.v := by rw [hT]; exact stepVar_clause hj 2 (by omega)
  have hN : midFusion φ < T + 1 := by rw [hT]; simp only [clauseStep, midFusion]; omega
  have hT0 : 0 ≤ T := by rw [hT]; simp only [clauseStep]; omega
  have hT1 : T - 1 = clauseStep φ j 1 := by rw [hT]; simp only [clauseStep]; omega
  have sel1 : ∀ a, selOfAssign φ a (T - 1) = ⟨T - 1, bit (litVal a c.l2)⟩ := by
    intro a; rw [hT1]; exact selOfAssign_clause φ a j 1 c (by omega) hjlt hj
  have hS4 : ∀ a b, (SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) →
      (SolE φ (T + 1) d b ∧ selOfAssign φ b (T - 1) = k) → a s4 = b s4 := by
    intro a b ha hb'
    rw [← h2]
    exact litVal_inj (bit_inj (congrArg NodeId.index ((sel1 a).symm.trans (ha.2.trans (hb'.2.symm.trans (sel1 b))))))
  exact phantomFree_chain5_end hl D hv (Or.inr hz3) hS4 hk1 hk2 hT0 (by omega) hN

/-- Una variable de `Z4` solo está en la última cláusula. -/
theorem only4_of_chain5C (C : Chain5C φ s1 s2 s3 s4 zone) {v : Nat} (hz : zone v = 4) {j : Nat} {c : Clause}
    (hj : φ.clauses[j]? = some c) (hcv : ClVar c v) : j = 4 := by
  have hjlt : j < 5 := by
    rw [← C.len]
    by_cases h : j < φ.clauses.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have hB := clIn_var (C.blk j c hj) hcv
  have z1 := C.D.z1; have z2 := C.D.z2; have z3 := C.D.z3; have z4 := C.D.z4
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
  · rcases hB with h | rfl <;> omega
  · rcases hB with rfl | h | rfl <;> omega
  · rcases hB with rfl | h | rfl <;> omega
  · rcases hB with rfl | h | rfl <;> omega
  · rfl

/-- **Toda fórmula de la clase cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_of_chain5C (hb : Bounded φ) (C : Chain5C φ s1 s2 s3 s4 zone) (T : Int) (hT : 1 ≤ T) :
    PhantomAt φ T := by
  have D := C.D
  have hcl : ∀ j (hj : j < 5), φ.clauses[j]? = some (φ.clauses[j]'(by rw [C.len]; exact hj)) :=
    fun j hj => List.getElem?_eq_getElem _
  have hlen : ∀ j, j < 5 → j < φ.clauses.length := fun j hj => by rw [C.len]; exact hj
  -- las ventanas `W1` y `W2`, en `φ` y en sus prefijos
  have w1 := C.w1 _ (hcl 1 (by omega))
  have w2 := C.w2 _ (hcl 2 (by omega))
  have r11 := readsAt_clause (hcl 1 (by omega)) w1.1
  have r12 := readsAt_clause (hcl 1 (by omega)) w1.2
  have r22 := readsAt_clause (hcl 2 (by omega)) w2.1
  have r23 := readsAt_clause (hcl 2 (by omega)) w2.2
  have cs : ∀ j p, clauseStep φ j p = 2 * (φ.nVars : Int) + 2 + 3 * (j : Int) + (p : Int) := fun _ _ => rfl
  have hm : midFusion φ = 2 * (φ.nVars : Int) + 1 := rfl
  have hft : fusionTop φ = 2 * (φ.nVars : Int) + 17 := by simp only [fusionTop, C.len]; omega
  by_cases hlow : T + 1 ≤ midFusion φ + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  rw [hm] at hlow
  -- las cuatro primeras cláusulas, por su prefijo
  have pre : ∀ m, 1 ≤ m → m ≤ 4 → T ≤ clauseStep φ (m - 1) 2 → T + 1 ≤ fusionTop (prefixCnf φ m) := by
    intro m h1 h4 hTm
    simp only [fusionTop, prefixCnf, List.length_take, C.len]
    rw [cs] at hTm; omega
  by_cases p0 : T ≤ clauseStep φ 0 2
  · refine phantomAt_of_prefix hb (j := 1) (pre 1 (by omega) (by omega) p0) ?_
    refine phantomAt_of_lineLocal (bounded_prefix hb 1) (j0 := 0) ((prefix_getElem? (by omega)).trans (hcl 0 (by omega)))
      (by rw [clauseStep_prefix, cs]; omega) (by rw [clauseStep_prefix]; exact p0) hT
      (fun hl hv hcv hσ0 hσN hTN => ?_)
    exact phantomFree_sepData hl (sepData_pre1 C (clIn_var (C.blk 0 _ (hcl 0 (by omega))) hcv)) hv hσ0 hσN
      (by show midFusion φ < _; omega)
  by_cases p1 : T ≤ clauseStep φ 1 2
  · refine phantomAt_of_prefix hb (j := 2) (pre 2 (by omega) (by omega) p1) ?_
    refine phantomAt_of_lineLocal (bounded_prefix hb 2) (j0 := 1) ((prefix_getElem? (by omega)).trans (hcl 1 (by omega)))
      (by rw [clauseStep_prefix, cs]; rw [cs] at p0; omega) (by rw [clauseStep_prefix]; exact p1) hT
      (fun hl hv hcv hσ0 hσN hTN => ?_)
    exact phantomFree_sepData hl (sepData_pre2 C (clIn_var (C.blk 1 _ (hcl 1 (by omega))) hcv)) hv hσ0 hσN
      (by show midFusion φ < _; omega)
  by_cases p2 : T ≤ clauseStep φ 2 2
  · refine phantomAt_of_prefix hb (j := 3) (pre 3 (by omega) (by omega) p2) ?_
    refine phantomAt_of_lineLocal (bounded_prefix hb 3) (j0 := 2) ((prefix_getElem? (by omega)).trans (hcl 2 (by omega)))
      (by rw [clauseStep_prefix, cs]; rw [cs] at p1; omega) (by rw [clauseStep_prefix]; exact p2) hT
      (fun hl hv hcv hσ0 hσN hTN => ?_)
    exact phantomFree_chainData hl (chainData_pre3 C (clIn_var (C.blk 2 _ (hcl 2 (by omega))) hcv)) hv hσ0 hσN
      (by show midFusion φ < _; omega)
  by_cases p3 : T ≤ clauseStep φ 3 2
  · refine phantomAt_of_prefix hb (j := 4) (pre 4 (by omega) (by omega) p3) ?_
    refine phantomAt_of_lineLocal (bounded_prefix hb 4) (j0 := 3) ((prefix_getElem? (by omega)).trans (hcl 3 (by omega)))
      (by rw [clauseStep_prefix, cs]; rw [cs] at p2; omega) (by rw [clauseStep_prefix]; exact p3) hT
      (fun {_ _ _ _ v} hl hv hcv hσ0 hσN hTN => ?_)
    have hB := clIn_var (C.blk 3 _ (hcl 3 (by omega))) hcv
    by_cases e3 : v = s3
    · subst e3
      exact phantomFree_chain4_s3 hl (chain4Data_pre4 C) hv hσ0 hσN (by show midFusion φ < _; omega)
    · have hC : zone v = 3 ∨ v = s4 := by
        rcases hB with h | h | h
        · exact absurd h e3
        · exact Or.inl h
        · exact Or.inr h
      have hψ1 : (prefixCnf φ 4).clauses[1]? = some (φ.clauses[1]'(hlen 1 (by omega))) :=
        (prefix_getElem? (by omega)).trans (hcl 1 (by omega))
      exact phantomFree_chain4_C hl (chain4Data_pre4 C) hv hC (k := clauseStep φ 1 2)
        (by rw [cs]; omega) (by rw [cs] at p2 ⊢; omega) (readsAt_clause hψ1 w1.1) (readsAt_clause hψ1 w1.2) hσ0 hσN
        (by show midFusion φ < _; omega)
  -- la última cláusula, sobre la fórmula entera
  have hc4 := hcl 4 (by omega)
  have w4 := C.w4 _ hc4
  have hB4 : ∀ {v : Nat}, ClVar (φ.clauses[4]'(hlen 4 (by omega))) v → v = s4 ∨ zone v = 4 :=
    fun hcv => clIn_var (C.blk 4 _ hc4) hcv
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step φ k d hd
    have hks := mapNodes_step φ (T - 1) k hk
    omega
  by_cases hTop : clauseStep φ 4 2 < T
  · -- después de la última cláusula
    have hft' : fusionTop φ ≤ d.step := by rw [hds, hft]; rw [cs] at hTop; omega
    refine ⟨fun r hr => by rw [reqOf_above φ d hft'] at hr; exact absurd hr List.not_mem_nil, ?_⟩
    have hsv : stepVar φ T = none := by
      have h1 : ¬ T ≤ 0 := by omega
      have h2 : ¬ T < midFusion φ := by rw [hm]; rw [cs] at hTop; omega
      have h3 : ¬ T = midFusion φ := by rw [hm]; rw [cs] at hTop; omega
      have h4 : fusionTop φ ≤ T := by rw [hft]; rw [cs] at hTop; omega
      simp only [stepVar, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    exact phantomFree_none (locPair_up hb T k d) hsv (by omega) (show T < T + 1 by omega)
  have k1 : ∀ {N : Int}, T ≤ N → 0 ≤ clauseStep φ 1 2 ∧ clauseStep φ 1 2 < N ∧ ReadsAt φ (clauseStep φ 1 2) s1 ∧
      ReadsAt φ (clauseStep φ 1 2) s2 := fun h => ⟨by rw [cs]; omega, by rw [cs] at p3 ⊢; omega, r11, r12⟩
  have k2 : ∀ {N : Int}, T ≤ N → 0 ≤ clauseStep φ 2 2 ∧ clauseStep φ 2 2 < N ∧ ReadsAt φ (clauseStep φ 2 2) s2 ∧
      ReadsAt φ (clauseStep φ 2 2) s3 := fun h => ⟨by rw [cs]; omega, by rw [cs] at p3 ⊢; omega, r22, r23⟩
  -- una variable de `Z4` está libre hasta el tercer paso de la última cláusula
  have free4 : ∀ {v : Nat} {B : Int}, zone v = 4 → B ≤ clauseStep φ 4 2 → FreeBelow φ v B := by
    intro v B hz hB j c hj hcv
    have := only4_of_chain5C C hz hj hcv
    subst this
    exact hB
  have hmT : midFusion φ < T := by rw [hm]; rw [cs] at p3; omega
  refine ⟨fun r hr => ?_, ?_⟩
  · -- el filtro
    obtain ⟨r1, r2⟩ := reqOf_range hb r hr
    rw [hds] at r2
    cases hv : stepVar φ r.step with
    | none => exact phantomFree_none (locPair_filter T k r) hv (by omega) r2
    | some v =>
      obtain ⟨j, c, p, hj, hp, e, hpv⟩ := req_lit hb hr hv (by rw [hds]; exact hmT)
      have hj4 : j = 4 := by rw [hds] at e; rw [cs] at e p3 hTop; omega
      subst hj4
      rw [hc4] at hj; cases hj
      rcases hB4 (hpv ▸ litAt_clVar _ p) with h | h
      · subst h
        exact phantomFree_chain5_s4 (locPair_filter T k r) D hv (k1 (Int.le_refl _)) (k2 (Int.le_refl _)) (by omega)
          r2 hmT
      · exact phantomFree_free_filter hv (free4 h (by omega)) (by omega) r2
  · -- el UP
    cases hv : stepVar φ T with
    | none => exact phantomFree_none (locPair_up hb T k d) hv (by omega) (show T < T + 1 by omega)
    | some v =>
      obtain ⟨j, c, p, hj, hp, e, hpv⟩ := step_lit hv hmT
      have hj4 : j = 4 := by rw [cs] at e p3 hTop; omega
      subst hj4
      rw [hc4] at hj; cases hj
      rcases hB4 (hpv ▸ litAt_clVar _ p) with h | h
      · subst h
        exact phantomFree_chain5_s4 (locPair_up hb T k d) D hv (k1 (by omega)) (k2 (by omega)) (by omega) (by omega)
          (by omega)
      · by_cases hp2 : p = 2
        · subst hp2
          -- el tercer literal: `s4` es el primero o el segundo
          have hl3 : (φ.clauses[4]'(hlen 4 (by omega))).l3.v = v := hpv
          have hs4 : (φ.clauses[4]'(hlen 4 (by omega))).l1.v = s4 ∨ (φ.clauses[4]'(hlen 4 (by omega))).l2.v = s4 := by
            rcases w4 with e' | e' | e'
            · exact Or.inl e'.symm
            · exact Or.inr e'.symm
            · rw [show v = s4 from hl3.symm.trans e'.symm, D.z4] at h; omega
          rcases hs4 with h1 | h2
          · exact phantomFree_up_lastC hb D (hlen 4 (by omega)) hc4 e hds h1 (hl3 ▸ h) (k1 (by omega)) (k2 (by omega))
          · exact phantomFree_up_lastC2 hb D (hlen 4 (by omega)) hc4 e h2 (hl3 ▸ h) (k1 (by omega)) (k2 (by omega))
        · exact phantomFree_free_up hb hv (free4 h (by rw [e, cs, cs]; omega)) (by omega)

end GPathB

-- ============================================================
-- La cadena al revés, y el lector por separadores
-- ============================================================

/-- Las zonas leyendo la cadena al revés. -/
def zoneRev (zone : Nat → Nat) (z : Nat) : Nat := if zone z ≤ 4 then 4 - zone z else zone z

section Rev

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

theorem zoneRev_of {z k : Nat} (h : zone z = k) (hk : k ≤ 4) : zoneRev zone z = 4 - k := by
  unfold zoneRev; rw [if_pos (by omega), h]

theorem zone_of_zoneRev {z k : Nat} (h : zoneRev zone z = k) (hk : k ≤ 4) : zone z = 4 - k := by
  unfold zoneRev at h; split at h <;> omega

theorem zoneRev_ge {z : Nat} (h : 5 ≤ zone z) : zoneRev zone z = zone z := by
  unfold zoneRev; rw [if_neg (by omega)]

/-- **La cadena al revés**: separadores `s4, s3, s2, s1`, zonas `4 - zone`. -/
theorem chain5Data_rev (D : Chain5Data φ s1 s2 s3 s4 zone) : Chain5Data φ s4 s3 s2 s1 (zoneRev zone) := by
  have z1 := D.z1; have z2 := D.z2; have z3 := D.z3; have z4 := D.z4
  have back : ∀ {z k : Nat}, k ≤ 4 → zoneRev zone z = k → zone z = 4 - k := fun hk h => zone_of_zoneRev h hk
  refine ⟨D.s4v, D.s3v, D.s2v, D.s1v, by rw [zoneRev_ge (by omega), z4], by rw [zoneRev_ge (by omega), z3],
    by rw [zoneRev_ge (by omega), z2], by rw [zoneRev_ge (by omega), z1], fun h => D.n34 h.symm, fun h => D.n24 h.symm,
    fun h => D.n14 h.symm, fun h => D.n23 h.symm, fun h => D.n13 h.symm, fun h => D.n12 h.symm, ?_, ?_, ?_, ?_, ?_,
    fun c hc => ?_⟩
  · intro z1' z2' z3' a b c d e f
    exact D.card4 z1' z2' z3' (back (by omega) a) (back (by omega) b) (back (by omega) c) d e f
  · intro z1' z2' z3' a b c d e f
    exact D.card0 z1' z2' z3' (back (by omega) a) (back (by omega) b) (back (by omega) c) d e f
  · intro y1 y2 a b; exact D.card3 y1 y2 (back (by omega) a) (back (by omega) b)
  · intro y1 y2 a b; exact D.card2 y1 y2 (back (by omega) a) (back (by omega) b)
  · intro y1 y2 a b; exact D.card1 y1 y2 (back (by omega) a) (back (by omega) b)
  · rcases D.cl c hc with hi | hi | hi | hi | hi | hi
    · refine Or.inl (clIn_mono hi (fun z ⟨h5, n1, n2, n3, n4⟩ => ⟨by rw [zoneRev_ge h5]; exact h5, n4, n3, n2, n1⟩))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (clIn_mono hi (fun z hz => ?_))))))
      rcases hz with h | h
      · exact Or.inr (zoneRev_of h (by omega))
      · exact Or.inl h
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (clIn_mono hi (fun z hz => ?_))))))
      rcases hz with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (zoneRev_of h (by omega)))
      · exact Or.inl h
    · refine Or.inr (Or.inr (Or.inr (Or.inl (clIn_mono hi (fun z hz => ?_)))))
      rcases hz with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (zoneRev_of h (by omega)))
      · exact Or.inl h
    · refine Or.inr (Or.inr (Or.inl (clIn_mono hi (fun z hz => ?_))))
      rcases hz with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (zoneRev_of h (by omega)))
      · exact Or.inl h
    · refine Or.inr (Or.inl (clIn_mono hi (fun z hz => ?_)))
      rcases hz with h | h
      · exact Or.inr h
      · exact Or.inl (zoneRev_of h (by omega))

end Rev

namespace GPathB

open Driver Machine MachineOn

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

/-- **T2 en la clase**: fijar un separador, con lo que sea fijado antes. -/
theorem sepPinFree_of_chain5C (C : Chain5C φ s1 s2 s3 s4 zone) : SepPinFree φ [s1, s2, s3, s4] (stepCount φ) := by
  intro k R0 r s _ hs hrs hr1 hrT
  have D := C.D
  have hcl : ∀ j (hj : j < 5), φ.clauses[j]? = some (φ.clauses[j]'(by rw [C.len]; exact hj)) :=
    fun j hj => List.getElem?_eq_getElem _
  have w1 := C.w1 _ (hcl 1 (by omega))
  have w2 := C.w2 _ (hcl 2 (by omega))
  have w3 := C.w3 _ (hcl 3 (by omega))
  have kb : ∀ j, j < 5 → 0 ≤ clauseStep φ j 2 ∧ clauseStep φ j 2 < stepCount φ := fun j hj => by
    simp only [clauseStep, stepCount, C.len]; omega
  have W1 := readsAt_clause (hcl 1 (by omega)) w1.1
  have W1' := readsAt_clause (hcl 1 (by omega)) w1.2
  have W2 := readsAt_clause (hcl 2 (by omega)) w2.1
  have W2' := readsAt_clause (hcl 2 (by omega)) w2.2
  have W3 := readsAt_clause (hcl 3 (by omega)) w3.1
  have W3' := readsAt_clause (hcl 3 (by omega)) w3.2
  have hl := locPair_read (φ := φ) (stepCount φ) k R0 r
  have hN : midFusion φ < stepCount φ := by unfold stepCount midFusion; omega
  have hs' : s = s1 ∨ s = s2 ∨ s = s3 ∨ s = s4 := by
    have := List.mem_of_getElem? hs
    simpa using this
  rcases hs' with rfl | rfl | rfl | rfl
  · exact phantomFree_chain5_s4 hl (chain5Data_rev D) hrs ⟨(kb 3 (by omega)).1, (kb 3 (by omega)).2, W3', W3⟩
      ⟨(kb 2 (by omega)).1, (kb 2 (by omega)).2, W2', W2⟩ (by omega) hrT hN
  · exact phantomFree_chain5_s3 hl (chain5Data_rev D) hrs ⟨(kb 3 (by omega)).1, (kb 3 (by omega)).2, W3', W3⟩
      ⟨(kb 2 (by omega)).1, (kb 2 (by omega)).2, W2', W2⟩ ⟨(kb 1 (by omega)).1, (kb 1 (by omega)).2, W1', W1⟩
      (by omega) hrT
  · exact phantomFree_chain5_s3 hl D hrs ⟨(kb 1 (by omega)).1, (kb 1 (by omega)).2, W1, W1'⟩
      ⟨(kb 2 (by omega)).1, (kb 2 (by omega)).2, W2, W2'⟩ ⟨(kb 3 (by omega)).1, (kb 3 (by omega)).2, W3, W3'⟩
      (by omega) hrT
  · exact phantomFree_chain5_s4 hl D hrs ⟨(kb 1 (by omega)).1, (kb 1 (by omega)).2, W1, W1'⟩
      ⟨(kb 2 (by omega)).1, (kb 2 (by omega)).2, W2, W2'⟩ (by omega) hrT hN

/-- Las partes para la cobertura por separadores: la zona, o una propia fuera de la cadena. -/
def partOf (zone : Nat → Nat) (z : Nat) : Nat := if zone z ≤ 4 then zone z else z + 10

theorem sepCover_of_chain5C (C : Chain5C φ s1 s2 s3 s4 zone) : SepCover φ [s1, s2, s3, s4] (partOf zone) := by
  have D := C.D
  have z1 := D.z1; have z2 := D.z2; have z3 := D.z3; have z4 := D.z4
  -- en el bloque `j`, lo que no es separador es de la zona `j`
  have inBlk : ∀ {j z : Nat}, j < 5 → Blk5 s1 s2 s3 s4 zone j z → z ∉ [s1, s2, s3, s4] → zone z = j := by
    intro j z hj hB hS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
    · rcases hB with h | h
      · exact h
      · exact absurd (Or.inl h) hS
    · rcases hB with h | h | h
      · exact absurd (Or.inl h) hS
      · exact h
      · exact absurd (Or.inr (Or.inl h)) hS
    · rcases hB with h | h | h
      · exact absurd (Or.inr (Or.inl h)) hS
      · exact h
      · exact absurd (Or.inr (Or.inr (Or.inl h))) hS
    · rcases hB with h | h | h
      · exact absurd (Or.inr (Or.inr (Or.inl h))) hS
      · exact h
      · exact absurd (Or.inr (Or.inr (Or.inr h))) hS
    · rcases hB with h | h
      · exact absurd (Or.inr (Or.inr (Or.inr h))) hS
      · exact h
  refine ⟨fun c hc z z' hz hz' hzS hz'S => ?_, fun p y1 y2 y3 n1 n2 n3 h1 h2 h3 d12 d13 d23 => ?_⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    have hjl : j < 5 := by
      rw [← C.len]
      by_cases h : j < φ.clauses.length
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
    have e1 := inBlk hjl (clIn_var (C.blk j c hj) hz) hzS
    have e2 := inBlk hjl (clIn_var (C.blk j c hj) hz') hz'S
    unfold partOf; rw [e1, e2, if_pos (by omega), if_pos (by omega)]
  · unfold partOf at h1 h2 h3
    split at h1 <;> split at h2 <;> split at h3
    · rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4) with rfl | rfl | rfl | rfl | rfl
      · exact D.card0 y1 y2 y3 h1 h2 h3 d12 d13 d23
      · exact d12 (D.card1 y1 y2 h1 h2)
      · exact d12 (D.card2 y1 y2 h1 h2)
      · exact d12 (D.card3 y1 y2 h1 h2)
      · exact D.card4 y1 y2 y3 h1 h2 h3 d12 d13 d23
    all_goals omega

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

/-- **La máquina `:on` es exacta en toda cadena de cinco bloques de la clase**, con cualquier numeración. -/
theorem machineExact_of_chain5C (hb : Bounded φ) (C : Chain5C φ s1 s2 s3 s4 zone) : MachineExact φ :=
  (machineExact_iff hb).2 (phantomAt_of_chain5C hb C)

/-- **La espina `:on` decide toda cadena de cinco bloques de la clase.** -/
theorem spineVerdictOn_iff_of_chain5C (hb : Bounded φ) (C : Chain5C φ s1 s2 s3 s4 zone) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hb (phantomAt_of_chain5C hb C)

/-- **El lector por separadores no se atasca en ninguna cadena de cinco bloques de la clase**: toda lectura que
empieza por `s1, s2, s3, s4` deja un estado válido con la rama de una solución que coincide con todas las elecciones.
Sin hipótesis sobre la máquina. -/
theorem reader_sep_of_chain5C (hb : Bounded φ) (C : Chain5C φ s1 s2 s3 s4 zone) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g')
    (hsf : SepFirst φ [s1, s2, s3, s4] R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_sep_on hb (fun T hT => phantomAtW_of_phantomAt (phantomAt_of_chain5C hb C T hT)) (sepCover_of_chain5C C)
    (sepPinFree_of_chain5C C) hkv hr hsf

end MachineOn

-- ============================================================
-- `chain5_cross` está en la clase
-- ============================================================

theorem chain5C_chain5Cross : Chain5C chain5Cross 5 6 7 8 zone5 := by
  refine ⟨chain5Data_chain5Cross, rfl, fun j c hj => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩
  · rcases clauses_chain5Cross hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [ClIn, Blk5, zone5]
  · have : c = ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩ := by simp [chain5Cross] at hc; exact hc.symm
    subst this; simp [ClVar]
  · have : c = ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩ := by simp [chain5Cross] at hc; exact hc.symm
    subst this; simp [ClVar]
  · have : c = ⟨⟨7, false⟩, ⟨3, true⟩, ⟨8, true⟩⟩ := by simp [chain5Cross] at hc; exact hc.symm
    subst this; simp [ClVar]
  · have : c = ⟨⟨8, false⟩, ⟨9, true⟩, ⟨10, true⟩⟩ := by simp [chain5Cross] at hc; exact hc.symm
    subst this; simp [ClVar]

namespace MachineOn

open GPathB Driver Machine

/-- La clase da de nuevo `chain5_cross`. -/
theorem machineExact_chain5Cross_of_class : MachineExact chain5Cross :=
  machineExact_of_chain5C bounded_chain5Cross chain5C_chain5Cross

end MachineOn

end AbsSatBingo.Model
