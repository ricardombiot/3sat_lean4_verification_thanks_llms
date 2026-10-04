-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain6BC.lean
import AbsSatBingo.Model.ForbidOnChainOps
import AbsSatBingo.Model.ForbidOnChain6BI

/-!
# La clase de seis bloques en orden de bisección

**`Chain6BC φ zone sv`**: `φ` es una cadena de seis bloques (`ChainN φ 6 zone`, separadores `sv 1 … sv 5`), con las
cláusulas en orden de bisección de bloques, `B0, B1, B2 | B5, B4 | B3` (`ord6`), y:

* `B1` lee `s1` y `s2` (su ventana);
* `B4` termina en `s4` y lee `s5`;
* la unión `B3` es `(s4, s3, z3)`, con `z3` de dentro del bloque `3`.

Cualquier numeración de las variables, cualquier signo, y cualquier orden de literales en `B0, B1, B2, B5`.

* Las líneas de `B0, B1, B2` ven el prefijo, una cadena de hasta tres bloques leídos: `line_comp` sobre la cadena.
* Las de `B5, B4`, lo mismo sobre la cadena al revés (`chainN_rev`).
* Las de la unión, sobre la fórmula entera: `k` fija `s4`, `s4` o `s3` (`phantomFree_fixedLoc`, `phantomFree_bisect`
  con el extremo `s4` fijo, `phantomFree_inner`).

Resultado: **`phantomAt_of_chain6BC`**, **`machineExact_of_chain6BC`**, **`spineVerdictOn_iff_of_chain6BC`**, y
`chain6BC_chain6B` (la instancia está en la clase).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- El bloque de cada cláusula: `B0, B1, B2, B5, B4, B3`. -/
def ord6 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 4
  | _ => 3

/-- **La clase de seis bloques en orden de bisección.** -/
structure Chain6BC (φ : Cnf) (zone sv : Nat → Nat) : Prop where
  D   : ChainN φ 6 zone
  hsv : ∀ k, 1 ≤ k → k < 6 → zone (sv k) = 6 + k
  len : φ.clauses.length = 6
  blk : ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → ClIn (BlkN 6 zone (ord6 j)) c
  w1  : ∀ c, φ.clauses[1]? = some c → ClVar c (sv 1) ∧ ClVar c (sv 2)
  w4  : ∀ c, φ.clauses[4]? = some c → c.l3.v = sv 4 ∧ ClVar c (sv 5)
  w5  : ∀ c, φ.clauses[5]? = some c → c.l1.v = sv 4 ∧ c.l2.v = sv 3 ∧ zone c.l3.v = 3

theorem Chain6BC.cl {zone sv : Nat → Nat} (C : Chain6BC φ zone sv) {j : Nat} (hj : j < 6) :
    φ.clauses[j]? = some (φ.clauses[j]'(by rw [C.len]; exact hj)) := List.getElem?_eq_getElem _

instance decClVar (c : Clause) (z : Nat) : Decidable (ClVar c z) :=
  inferInstanceAs (Decidable (z = c.l1.v ∨ z = c.l2.v ∨ z = c.l3.v))

namespace GPathB

open Driver Machine MachineOn

variable {zone sv : Nat → Nat}

/-- **Las líneas de las cinco primeras cláusulas**, en su prefijo. -/
theorem phantomAt_pre6 (hb : Bounded φ) (C : Chain6BC φ zone sv) {j : Nat} (hj : j ≤ 4) {T : Int}
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
  have hBv : BlkN 6 zone (ord6 j) v := by rw [← hpv]; exact clIn_var (C.blk j _ hcj) (litAt_clVar _ p)
  have pre : ∀ c ∈ (prefixCnf φ (j + 1)).clauses, ∃ i, i ≤ j ∧ ClIn (BlkN 6 zone (ord6 i)) c := fun c hc => by
    obtain ⟨i, hi, e⟩ := mem_prefix_clause hc
    exact ⟨i, by omega, C.blk i c e⟩
  by_cases hleft : j ≤ 2
  · -- la mitad izquierda, en el sentido de la cadena
    have ordL : ∀ i, i ≤ 2 → ord6 i = i := fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
    refine line_comp hl C.D C.hsv (Nat.le_refl _) (k := j + 1) (by omega) (by omega) (by omega) (fun c hc => ?_)
      hv hvlt ?_ hmid (fun hk => ?_) hσ0 hσN
    · obtain ⟨i, hi, hin⟩ := pre c hc
      rw [ordL i (by omega)] at hin
      exact Or.inl ⟨i, by omega, hin⟩
    · rw [show j + 1 - 1 = j by omega, ← ordL j hleft]; exact hBv
    · -- la ventana de `B1`
      have h1 := C.cl (j := 1) (by omega)
      have hψ1 : (prefixCnf φ (j + 1)).clauses[1]? = some (φ.clauses[1]'(by rw [C.len]; omega)) :=
        (prefix_getElem? (by omega)).trans h1
      obtain ⟨a1, a2⟩ := C.w1 _ h1
      refine ⟨clauseStep (prefixCnf φ (j + 1)) 1 2, by simp only [clauseStep]; omega,
        by rw [hTp] at hTN; simp only [clauseStep, prefixCnf] at hTN ⊢; omega,
        readsAt_clause hψ1 a2, readsAt_clause hψ1 a1⟩
  · -- la mitad derecha, en la cadena al revés
    have Dr := chainN_rev C.D
    have hsvr : ∀ k, 1 ≤ k → k < 6 → zoneRevN 6 zone (sv (6 - k)) = 6 + k := fun k h1 h2 =>
      (zoneRevN_sep h1 h2).mpr (C.hsv (6 - k) (by omega) (by omega))
    refine line_comp hl Dr (sv := fun k => sv (6 - k)) hsvr (Nat.le_refl _) (k := j - 2) (by omega) (by omega)
      (by omega) (fun c hc => ?_) hv hvlt ?_ hmid (fun h => absurd h (by omega)) hσ0 hσN
    · obtain ⟨i, hi, hin⟩ := pre c hc
      by_cases hi2 : i ≤ 2
      · have e : ord6 i = i := by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
        rw [e] at hin
        exact Or.inr (Or.inr ⟨6 - 1 - i, by omega, by omega, clIn_mono hin (fun z hz => blkN_rev (by omega) hz)⟩)
      · rcases (by omega : i = 3 ∨ i = 4) with rfl | rfl
        · exact Or.inl ⟨6 - 1 - 5, by omega, clIn_mono hin (fun z hz => blkN_rev (by omega) hz)⟩
        · exact Or.inl ⟨6 - 1 - 4, by omega, clIn_mono hin (fun z hz => blkN_rev (by omega) hz)⟩
    · rcases (by omega : j = 3 ∨ j = 4) with rfl | rfl
      · exact blkN_rev (j := 5) (by omega) hBv
      · exact blkN_rev (j := 4) (by omega) hBv

/-- **Las líneas de la unión**, la última cláusula. -/
theorem phantomAt_last6 (hb : Bounded φ) (C : Chain6BC φ zone sv) {T : Int} (hT0 : clauseStep φ 5 0 ≤ T)
    (hT2 : T ≤ clauseStep φ 5 2) (hT : 1 ≤ T) : PhantomAt φ T := by
  have h1 := C.cl (j := 1) (by omega)
  have h4 := C.cl (j := 4) (by omega)
  have h5 := C.cl (j := 5) (by omega)
  obtain ⟨a1, a2⟩ := C.w1 _ h1
  obtain ⟨b4, b5⟩ := C.w4 _ h4
  obtain ⟨e1, e2, e3⟩ := C.w5 _ h5
  have sepEq : ∀ {i z}, 1 ≤ i → i < 6 → zone z = 6 + i → z = sv i := fun {i z} a b h =>
    C.D.sep1 i a b z (sv i) h (C.hsv i a b)
  refine phantomAt_of_lineLocalF hb h5 hT0 hT2 hT
    (fun {P0 _ σ N v} p hp hTp hpv hl hv hL3 hfix hσ0 hσN hTN => ?_)
  have hmid : midFusion φ < N := by rw [hTp] at hTN; simp only [clauseStep, midFusion] at hTN ⊢; omega
  have w1 : ∃ lam, 0 ≤ lam ∧ lam < N ∧ ReadsAt φ lam (sv (3 - 1)) ∧ ReadsAt φ lam (sv (3 - 2)) :=
    ⟨clauseStep φ 1 2, by simp only [clauseStep]; omega, by rw [hTp] at hTN; simp only [clauseStep] at hTN ⊢; omega,
      readsAt_clause h1 a2, readsAt_clause h1 a1⟩
  rcases p with _ | _ | _ | p
  · -- `v = s4`, que ya fija `k` (el último literal de `B4`)
    have hv4 : v = sv 4 := hpv.symm.trans e1
    have hk : stepVar φ (T - 1) = some (sv 4) := by
      rw [hTp, show clauseStep φ 5 0 - 1 = clauseStep φ 4 2 by simp only [clauseStep]; omega, ← b4]
      exact stepVar_clause h4 2 (by omega)
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
      rw [hTp, show clauseStep φ 5 1 - 1 = clauseStep φ 5 0 by simp only [clauseStep]; omega, ← e1]
      exact stepVar_clause h5 0 (by omega)
    rw [hv3] at hv
    exact phantomFree_bisect hl C.D C.hsv hv (fun h => absurd h (by omega)) (fun _ => w1) hmid
      (C.hsv 3 (by omega) (by omega)) (m := 3) (a := 0) (b := 4) (by omega) (by omega) (by omega) (by omega)
      (fun h => absurd h (by omega))
      (fun _ c c' qc qc' z hz => by rw [sepEq (by omega) (by omega) hz]; exact hfix c c' qc qc' _ hk)
      (Or.inl (by omega)) (Or.inl (by omega)) hσ0 hσN
  · -- `v = z3`, dentro de `B3`; `k` fija `s3`
    have hz3 : zone v = 3 := by rw [← hpv]; exact e3
    have hk : stepVar φ (T - 1) = some (sv 3) := by
      rw [hTp, show clauseStep φ 5 2 - 1 = clauseStep φ 5 1 by simp only [clauseStep]; omega, ← e2]
      exact stepVar_clause h5 1 (by omega)
    have S : SideData φ 6 zone sv P0 N 3 6 :=
      ⟨C.D, C.hsv, fun _ => ⟨clauseStep φ 4 2, by simp only [clauseStep]; omega,
        by rw [hTp] at hTN; simp only [clauseStep] at hTN ⊢; omega,
        by rw [show 3 + 1 = 4 from rfl, ← b4]; exact readsAt_clause h4 (Or.inr (Or.inr rfl)),
        readsAt_clause h4 b5⟩, hmid, by omega, by omega, by omega, fun h => absurd h (by omega),
        by omega⟩
    exact phantomFree_inner hl S (Or.inl (by omega)) hv hz3
      (fun c c' qc qc' z hz => by rw [sepEq (by omega) (by omega) hz]; exact hfix c c' qc qc' _ hk) hσ0 hσN
  · omega

/-- **Toda fórmula de la clase cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_of_chain6BC (hb : Bounded φ) (C : Chain6BC φ zone sv) (T : Int) (hT : 1 ≤ T) :
    PhantomAt φ T := by
  have cs : ∀ j p : Nat, clauseStep φ j p = 2 * (φ.nVars : Int) + 2 + 3 * (j : Int) + (p : Int) := fun _ _ => rfl
  have hm : midFusion φ = 2 * (φ.nVars : Int) + 1 := rfl
  have hft : fusionTop φ = 2 * (φ.nVars : Int) + 20 := by simp only [fusionTop, C.len]; omega
  by_cases hlow : T + 1 ≤ midFusion φ + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  rw [hm] at hlow
  have ft : ∀ j : Nat, j ≤ 6 → fusionTop (prefixCnf φ j) = 2 * (φ.nVars : Int) + 3 * (j : Int) + 2 := by
    intro j hj
    simp only [fusionTop, prefixCnf, List.length_take, C.len]
    omega
  -- las cinco primeras cláusulas, por su prefijo
  have pre : ∀ j : Nat, j ≤ 4 → clauseStep φ j 0 ≤ T → T ≤ clauseStep φ j 2 → PhantomAt φ T := by
    intro j hj h0 h2
    refine phantomAt_of_prefix hb (j := j + 1) (by rw [ft (j + 1) (by omega)]; rw [cs] at h2; omega)
      (phantomAt_pre6 hb C hj h0 h2 hT)
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
  · exact phantomAt_last6 hb C (by rw [cs] at p4 ⊢; omega) p5 hT
  -- después de la última cláusula
  rw [cs] at p5
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

/-- **La máquina `:on` es exacta en toda cadena de seis bloques de la clase.** -/
theorem machineExact_of_chain6BC (hb : Bounded φ) (C : Chain6BC φ zone sv) : MachineExact φ :=
  (machineExact_iff hb).2 (phantomAt_of_chain6BC hb C)

/-- **La espina `:on` decide toda cadena de seis bloques de la clase.** -/
theorem spineVerdictOn_iff_of_chain6BC (hb : Bounded φ) (C : Chain6BC φ zone sv) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hb (phantomAt_of_chain6BC hb C)

end MachineOn

/-! ## `chain6_bisect_lit` está en la clase -/

namespace GPathB

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 10000

theorem chain6BC_chain6B :
    Chain6BC chain6B (zoneV 6 [0, 3, 0, 4, 1, 2, 7, 8, 9, 10, 11, 5, 5]) (fun k => [6, 7, 8, 9, 10].getD (k - 1) 0) := by
  refine ⟨ch6, fun k h1 h2 => ?_, rfl, fun j c hj => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · have h : ∀ k, k < 6 → 1 ≤ k → zoneV 6 [0, 3, 0, 4, 1, 2, 7, 8, 9, 10, 11, 5, 5]
        ([6, 7, 8, 9, 10].getD (k - 1) 0) = 6 + k := by decide
    exact h k h2 h1
  · have hjl : j < 6 := by
      by_cases h : j < 6
      · exact h
      · rw [List.getElem?_eq_none (by simp [chain6B]; omega)] at hj; cases hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (cases hj; decide)
  · cases hc; decide
  · cases hc; decide
  · cases hc; decide

end GPathB

namespace MachineOn

open GPathB Driver Machine

theorem machineExact_chain6B_of_class : MachineExact chain6B :=
  machineExact_of_chain6BC bounded_chain6B GPathB.chain6BC_chain6B

end MachineOn

end AbsSatBingo.Model
