-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain7BC.lean
import AbsSatBingo.Model.ForbidOnChain7B

/-!
# La clase de siete bloques en orden de bisección

**`Chain7BC φ zone sv`**: `φ` es una cadena de siete bloques (`ChainN φ 7 zone`, separadores `sv 1 … sv 6`), con las
cláusulas en orden de bisección, `B0, B1, B2 | B6, B5, B4 | B3` (`ord7`), y:

* `B1` lee `s1` y `s2`; `B5` lee `s5` y `s6` (las ventanas de los lados de tres);
* `B4` termina en `s4` y lee `s5`;
* la unión `B3` es `(s4, s3, z3)`, con `z3` de dentro del bloque `3`.

Cualquier numeración, signo y orden de literales en las demás cláusulas.

* Las líneas de `B0, B1, B2` y las de `B6, B5, B4` (en la cadena al revés) ven prefijos con hasta tres bloques leídos:
  `line_comp`.
* La unión: `k` fija `s4` (`phantomFree_fixedLoc`), `s4` (`v = s3`: `phantomFree_bisect` con lados de tres y uno
  fijo) o `s3` (`v = z3`: un lado libre de cuatro, `phantomFree_inner4`).

Resultado: **`phantomAt_of_chain7BC`**, **`machineExact_of_chain7BC`**, **`spineVerdictOn_iff_of_chain7BC`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- El bloque de cada cláusula: `B0, B1, B2, B6, B5, B4, B3`. -/
def ord7 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 5
  | 5 => 4
  | _ => 3

/-- **La clase de siete bloques en orden de bisección.** -/
structure Chain7BC (φ : Cnf) (zone sv : Nat → Nat) : Prop where
  D   : ChainN φ 7 zone
  hsv : ∀ k, 1 ≤ k → k < 7 → zone (sv k) = 7 + k
  len : φ.clauses.length = 7
  blk : ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → ClIn (BlkN 7 zone (ord7 j)) c
  w1  : ∀ c, φ.clauses[1]? = some c → ClVar c (sv 1) ∧ ClVar c (sv 2)
  w5  : ∀ c, φ.clauses[4]? = some c → ClVar c (sv 5) ∧ ClVar c (sv 6)
  w4  : ∀ c, φ.clauses[5]? = some c → c.l3.v = sv 4 ∧ ClVar c (sv 5)
  w3  : ∀ c, φ.clauses[6]? = some c → c.l1.v = sv 4 ∧ c.l2.v = sv 3 ∧ zone c.l3.v = 3

theorem Chain7BC.cl {zone sv : Nat → Nat} (C : Chain7BC φ zone sv) {j : Nat} (hj : j < 7) :
    φ.clauses[j]? = some (φ.clauses[j]'(by rw [C.len]; exact hj)) := List.getElem?_eq_getElem _

namespace GPathB

open Driver Machine MachineOn

variable {zone sv : Nat → Nat}

/-- **Las líneas de las seis primeras cláusulas**, en su prefijo. -/
theorem phantomAt_pre7 (hb : Bounded φ) (C : Chain7BC φ zone sv) {j : Nat} (hj : j ≤ 5) {T : Int}
    (hT0 : clauseStep φ j 0 ≤ T) (hT2 : T ≤ clauseStep φ j 2) (hT : 1 ≤ T) :
    PhantomAt (prefixCnf φ (j + 1)) T := by
  have hcj := C.cl (j := j) (by omega)
  have hψj : (prefixCnf φ (j + 1)).clauses[j]? = some (φ.clauses[j]'(by rw [C.len]; omega)) :=
    (prefix_getElem? (by omega)).trans hcj
  refine phantomAt_of_lineLocalF (bounded_prefix hb (j + 1)) hψj (by rw [clauseStep_prefix]; exact hT0)
    (by rw [clauseStep_prefix]; exact hT2) hT (fun {_ _ _ N v} p _ hTp hpv hl hv _ _ hσ0 hσN hTN => ?_)
  have hmid : midFusion (prefixCnf φ (j + 1)) < N := by
    rw [hTp] at hTN; simp only [clauseStep, midFusion, prefixCnf] at hTN ⊢; omega
  have hvlt : v < (prefixCnf φ (j + 1)).nVars := by rw [← hpv]; exact litAt_lt hb (List.mem_of_getElem? hcj) p
  have hBv : BlkN 7 zone (ord7 j) v := by rw [← hpv]; exact clIn_var (C.blk j _ hcj) (litAt_clVar _ p)
  have pre : ∀ c ∈ (prefixCnf φ (j + 1)).clauses, ∃ i, i ≤ j ∧ ClIn (BlkN 7 zone (ord7 i)) c := fun c hc => by
    obtain ⟨i, hi, e⟩ := mem_prefix_clause hc
    exact ⟨i, by omega, C.blk i c e⟩
  by_cases hleft : j ≤ 2
  · have ordL : ∀ i, i ≤ 2 → ord7 i = i := fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
    refine line_comp hl C.D C.hsv (Nat.le_refl _) (k := j + 1) (by omega) (by omega) (by omega) (fun c hc => ?_)
      hv hvlt ?_ hmid (fun hk => ?_) hσ0 hσN
    · obtain ⟨i, hi, hin⟩ := pre c hc
      rw [ordL i (by omega)] at hin
      exact Or.inl ⟨i, by omega, hin⟩
    · rw [show j + 1 - 1 = j by omega, ← ordL j hleft]; exact hBv
    · have h1 := C.cl (j := 1) (by omega)
      have hψ1 : (prefixCnf φ (j + 1)).clauses[1]? = some (φ.clauses[1]'(by rw [C.len]; omega)) :=
        (prefix_getElem? (by omega)).trans h1
      obtain ⟨a1, a2⟩ := C.w1 _ h1
      refine ⟨clauseStep (prefixCnf φ (j + 1)) 1 2, by simp only [clauseStep]; omega,
        by rw [hTp] at hTN; simp only [clauseStep, prefixCnf] at hTN ⊢; omega,
        readsAt_clause hψ1 a2, readsAt_clause hψ1 a1⟩
  · have Dr := chainN_rev C.D
    have hsvr : ∀ k, 1 ≤ k → k < 7 → zoneRevN 7 zone (sv (7 - k)) = 7 + k := fun k h1 h2 =>
      (zoneRevN_sep h1 h2).mpr (C.hsv (7 - k) (by omega) (by omega))
    refine line_comp hl Dr (sv := fun k => sv (7 - k)) hsvr (Nat.le_refl _) (k := j - 2) (by omega) (by omega)
      (by omega) (fun c hc => ?_) hv hvlt ?_ hmid (fun hk => ?_) hσ0 hσN
    · obtain ⟨i, hi, hin⟩ := pre c hc
      by_cases hi2 : i ≤ 2
      · have e : ord7 i = i := by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
        rw [e] at hin
        exact Or.inr (Or.inr ⟨7 - 1 - i, by omega, by omega, clIn_mono hin (fun z hz => blkN_rev (by omega) hz)⟩)
      · rcases (by omega : i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl
        · exact Or.inl ⟨7 - 1 - 6, by omega, clIn_mono hin (fun z hz => blkN_rev (by omega) hz)⟩
        · exact Or.inl ⟨7 - 1 - 5, by omega, clIn_mono hin (fun z hz => blkN_rev (by omega) hz)⟩
        · exact Or.inl ⟨7 - 1 - 4, by omega, clIn_mono hin (fun z hz => blkN_rev (by omega) hz)⟩
    · rcases (by omega : j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl
      · exact blkN_rev (j := 6) (by omega) hBv
      · exact blkN_rev (j := 5) (by omega) hBv
      · exact blkN_rev (j := 4) (by omega) hBv
    · -- la ventana de `B5` (lee `s5` y `s6`)
      have h4 := C.cl (j := 4) (by omega)
      have hψ4 : (prefixCnf φ (j + 1)).clauses[4]? = some (φ.clauses[4]'(by rw [C.len]; omega)) :=
        (prefix_getElem? (by omega)).trans h4
      obtain ⟨a5, a6⟩ := C.w5 _ h4
      refine ⟨clauseStep (prefixCnf φ (j + 1)) 4 2, by simp only [clauseStep]; omega,
        by rw [hTp] at hTN; simp only [clauseStep, prefixCnf] at hTN ⊢; omega, ?_, ?_⟩
      · show ReadsAt _ _ (sv (7 - 2)); exact readsAt_clause hψ4 a5
      · show ReadsAt _ _ (sv (7 - 1)); exact readsAt_clause hψ4 a6

/-- **Las líneas de la unión**, la última cláusula. -/
theorem phantomAt_last7 (hb : Bounded φ) (C : Chain7BC φ zone sv) {T : Int} (hT0 : clauseStep φ 6 0 ≤ T)
    (hT2 : T ≤ clauseStep φ 6 2) (hT : 1 ≤ T) : PhantomAt φ T := by
  have h1 := C.cl (j := 1) (by omega)
  have h4 := C.cl (j := 4) (by omega)
  have h5 := C.cl (j := 5) (by omega)
  have h6 := C.cl (j := 6) (by omega)
  obtain ⟨a1, a2⟩ := C.w1 _ h1
  obtain ⟨a5, a6⟩ := C.w5 _ h4
  obtain ⟨b4, b5⟩ := C.w4 _ h5
  obtain ⟨e1, e2, e3⟩ := C.w3 _ h6
  have sepEq : ∀ {i z}, 1 ≤ i → i < 7 → zone z = 7 + i → z = sv i := fun {i z} a b h =>
    C.D.sep1 i a b z (sv i) h (C.hsv i a b)
  refine phantomAt_of_lineLocalF hb h6 hT0 hT2 hT
    (fun {P0 _ σ N v} p hp hTp hpv hl hv hL3 hfix hσ0 hσN hTN => ?_)
  have hmid : midFusion φ < N := by rw [hTp] at hTN; simp only [clauseStep, midFusion] at hTN ⊢; omega
  have lt : ∀ j : Nat, j ≤ 5 → clauseStep φ j 2 < N := fun j hj => by
    rw [hTp] at hTN; simp only [clauseStep] at hTN ⊢; omega
  have w1 : ∃ lam, 0 ≤ lam ∧ lam < N ∧ ReadsAt φ lam (sv (3 - 1)) ∧ ReadsAt φ lam (sv (3 - 2)) :=
    ⟨clauseStep φ 1 2, by simp only [clauseStep]; omega, lt 1 (by omega), readsAt_clause h1 a2,
      readsAt_clause h1 a1⟩
  rcases p with _ | _ | _ | p
  · -- `v = s4`, que ya fija `k` (el último literal de `B4`)
    have hv4 : v = sv 4 := hpv.symm.trans e1
    have hk : stepVar φ (T - 1) = some (sv 4) := by
      rw [hTp, show clauseStep φ 6 0 - 1 = clauseStep φ 5 2 by simp only [clauseStep]; omega, ← b4]
      exact stepVar_clause h5 2 (by omega)
    have h3 : isL3 φ σ = false := by
      cases e : isL3 φ σ with
      | false => rfl
      | true =>
        have := hL3 e
        rw [this, hTp] at e
        simp only [isL3, Bool.and_eq_true, decide_eq_true_eq] at e
        obtain ⟨_, hmod⟩ := e
        simp only [clauseStep, midFusion] at hmod
        omega
    rw [hv4] at hv
    exact phantomFree_fixedLoc hl hv h3 (fun a b ha hb' => hfix a b ha hb' (sv 4) hk) hσ0 hσN
  · -- `v = s3`; `k` fija `s4`
    have hv3 : v = sv 3 := hpv.symm.trans e2
    have hk : stepVar φ (T - 1) = some (sv 4) := by
      rw [hTp, show clauseStep φ 6 1 - 1 = clauseStep φ 6 0 by simp only [clauseStep]; omega, ← e1]
      exact stepVar_clause h6 0 (by omega)
    rw [hv3] at hv
    exact phantomFree_bisect hl C.D C.hsv hv (fun h => absurd h (by omega)) (fun _ => w1) hmid
      (C.hsv 3 (by omega) (by omega)) (m := 3) (a := 0) (b := 4) (by omega) (by omega) (by omega) (by omega)
      (fun h => absurd h (by omega))
      (fun _ c c' qc qc' z hz => by rw [sepEq (by omega) (by omega) hz]; exact hfix c c' qc qc' _ hk)
      (Or.inl (by omega)) (Or.inl (by omega)) hσ0 hσN
  · -- `v = z3`, dentro de `B3`; `k` fija `s3`: un lado libre de cuatro
    have hz3 : zone v = 3 := by rw [← hpv]; exact e3
    have hk : stepVar φ (T - 1) = some (sv 3) := by
      rw [hTp, show clauseStep φ 6 2 - 1 = clauseStep φ 6 1 by simp only [clauseStep]; omega, ← e2]
      exact stepVar_clause h6 1 (by omega)
    refine phantomFree_inner4 hl C.D C.hsv (m := 3) (b := 7) (by omega) (by omega) (by omega) (by omega)
      (fun h => absurd h (by omega)) (fun _ => rfl)
      (fun _ => ⟨clauseStep φ 5 2, by simp only [clauseStep]; omega, lt 5 (by omega),
        by rw [show 3 + 1 = 4 from rfl, ← b4]; exact readsAt_clause h5 (Or.inr (Or.inr rfl)),
        readsAt_clause h5 b5⟩)
      (fun _ => ⟨clauseStep φ 4 2, by simp only [clauseStep]; omega, lt 4 (by omega), readsAt_clause h4 a5,
        readsAt_clause h4 a6⟩)
      hmid hv hz3
      (fun c c' qc qc' z hz => by rw [sepEq (by omega) (by omega) hz]; exact hfix c c' qc qc' _ hk) hσ0 hσN
  · omega

/-- **Toda fórmula de la clase cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_of_chain7BC (hb : Bounded φ) (C : Chain7BC φ zone sv) (T : Int) (hT : 1 ≤ T) :
    PhantomAt φ T := by
  have cs : ∀ j p : Nat, clauseStep φ j p = 2 * (φ.nVars : Int) + 2 + 3 * (j : Int) + (p : Int) := fun _ _ => rfl
  have hm : midFusion φ = 2 * (φ.nVars : Int) + 1 := rfl
  have hft : fusionTop φ = 2 * (φ.nVars : Int) + 23 := by simp only [fusionTop, C.len]; omega
  by_cases hlow : T + 1 ≤ midFusion φ + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  rw [hm] at hlow
  have ft : ∀ j : Nat, j ≤ 7 → fusionTop (prefixCnf φ j) = 2 * (φ.nVars : Int) + 3 * (j : Int) + 2 := by
    intro j hj
    simp only [fusionTop, prefixCnf, List.length_take, C.len]
    omega
  have pre : ∀ j : Nat, j ≤ 5 → clauseStep φ j 0 ≤ T → T ≤ clauseStep φ j 2 → PhantomAt φ T := by
    intro j hj h0 h2
    refine phantomAt_of_prefix hb (j := j + 1) (by rw [ft (j + 1) (by omega)]; rw [cs] at h2; omega)
      (phantomAt_pre7 hb C hj h0 h2 hT)
  by_cases p0 : T ≤ clauseStep φ 0 2
  · exact pre 0 (by omega) (by rw [cs]; omega) p0
  by_cases p1 : T ≤ clauseStep φ 1 2
  · exact pre 1 (by omega) (by rw [cs] at p0 ⊢; omega) p1
  by_cases p2 : T ≤ clauseStep φ 2 2
  · exact pre 2 (by omega) (by rw [cs] at p1 ⊢; omega) p2
  by_cases p3 : T ≤ clauseStep φ 3 2
  · exact pre 3 (by omega) (by rw [cs] at p2 ⊢; omega) p3
  by_cases p4 : T ≤ clauseStep φ 4 2
  · exact pre 4 (by omega) (by rw [cs] at p3 ⊢; omega) p4
  by_cases p5 : T ≤ clauseStep φ 5 2
  · exact pre 5 (by omega) (by rw [cs] at p4 ⊢; omega) p5
  by_cases p6 : T ≤ clauseStep φ 6 2
  · exact phantomAt_last7 hb C (by rw [cs] at p5 ⊢; omega) p6 hT
  rw [cs] at p6
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step φ k d hd
    have hks := mapNodes_step φ (T - 1) k hk
    omega
  have hft' : fusionTop φ ≤ d.step := by rw [hds, hft]; omega
  refine ⟨fun r hr => by rw [reqOf_above φ d hft'] at hr; exact absurd hr List.not_mem_nil, ?_⟩
  have hsv : stepVar φ T = none := by
    have h1 : ¬ T ≤ 0 := by omega
    have h2 : ¬ T < midFusion φ := by rw [hm]; omega
    have h3 : ¬ T = midFusion φ := by rw [hm]; omega
    have h4 : fusionTop φ ≤ T := by rw [hft]; omega
    simp only [stepVar, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  exact phantomFree_none (locPair_up hb T k d) hsv (by omega) (show T < T + 1 by omega)

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {zone sv : Nat → Nat}

/-- **La máquina `:on` es exacta en toda cadena de siete bloques de la clase.** -/
theorem machineExact_of_chain7BC (hb : Bounded φ) (C : Chain7BC φ zone sv) : MachineExact φ :=
  (machineExact_iff hb).2 (phantomAt_of_chain7BC hb C)

/-- **La espina `:on` decide toda cadena de siete bloques de la clase.** -/
theorem spineVerdictOn_iff_of_chain7BC (hb : Bounded φ) (C : Chain7BC φ zone sv) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hb (phantomAt_of_chain7BC hb C)

end MachineOn

end AbsSatBingo.Model

/-! ## `chain7_bisect_lit` está en la clase -/

namespace AbsSatBingo.Model

open AbsSatBin.Cnf

/-- **`chain7_bisect_lit`** (`scripts/cnf/chain7_bisect_lit.cnf`, variables desde 0). -/
def chain7B : Cnf :=
  ⟨15, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨7, true⟩⟩, ⟨⟨7, false⟩, ⟨4, true⟩, ⟨8, true⟩⟩, ⟨⟨8, false⟩, ⟨6, true⟩, ⟨9, true⟩⟩,
    ⟨⟨12, false⟩, ⟨13, true⟩, ⟨14, true⟩⟩, ⟨⟨11, false⟩, ⟨3, true⟩, ⟨12, true⟩⟩,
    ⟨⟨11, true⟩, ⟨5, true⟩, ⟨10, false⟩⟩, ⟨⟨10, true⟩, ⟨9, false⟩, ⟨1, true⟩⟩]⟩

theorem bounded_chain7B : Bounded chain7B := by
  intro c hc
  simp only [chain7B, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Clause.Bounded, chain7B]

namespace GPathB

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 10000

theorem chain7BC_chain7B :
    Chain7BC chain7B (zoneV 7 [0, 3, 0, 5, 1, 4, 2, 8, 9, 10, 11, 12, 13, 6, 6])
      (fun k => [7, 8, 9, 10, 11, 12].getD (k - 1) 0) := by
  refine ⟨chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    fun k h1 h2 => ?_, rfl, fun j c hj => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · have h : ∀ k, k < 7 → 1 ≤ k → zoneV 7 [0, 3, 0, 5, 1, 4, 2, 8, 9, 10, 11, 12, 13, 6, 6]
        ([7, 8, 9, 10, 11, 12].getD (k - 1) 0) = 7 + k := by decide
    exact h k h2 h1
  · have hjl : j < 7 := by
      by_cases h : j < 7
      · exact h
      · rw [List.getElem?_eq_none (by simp [chain7B]; omega)] at hj; cases hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (cases hj; decide)
  · cases hc; decide
  · cases hc; decide
  · cases hc; decide
  · cases hc; decide

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **La máquina `:on` es exacta en `chain7_bisect_lit`**, sin hipótesis. -/
theorem machineExact_chain7B : MachineExact chain7B :=
  machineExact_of_chain7BC bounded_chain7B chain7BC_chain7B

end MachineOn

end AbsSatBingo.Model
