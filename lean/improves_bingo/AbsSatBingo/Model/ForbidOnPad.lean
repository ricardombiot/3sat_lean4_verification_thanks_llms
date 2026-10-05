-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnPad.lean
import AbsSatBingo.Model.ForbidOnForestPeg

/-!
# El acolchado (plan del v229, paso 5)

`padCnf φ`: la variable real `v` pasa a `2v + 1`; las pares son de relleno; las cláusulas son
`T, C₀', T, C₁', …, T` con `T = (x₀ ∨ ¬x₀ ∨ x₀)` (tautológica, sobre la variable de relleno `0`) y `Cⱼ'` la cláusula
`j` renombrada. Es el gemelo de `scripts/pad_formula.py` (que reparte las tautologías entre varias de relleno; aquí
basta una).

* **`satisfiable_pad`**: `Satisfiable (padCnf φ) ↔ Satisfiable φ`; `bounded_pad`.
* **`freeOK_pad`**: las pares (de relleno) solo están en la tautología, de una sola variable.
* **`localBlocks_pad`**: lo que lee la ventana de cada paso, fuera de las pares, cae en una variable o en una cláusula.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- La tautología sobre la variable de relleno `0`. -/
def tautC : Clause := ⟨⟨0, true⟩, ⟨0, false⟩, ⟨0, true⟩⟩

def padLit (l : Lit) : Lit := ⟨2 * l.v + 1, l.pos⟩

def padClause (c : Clause) : Clause := ⟨padLit c.l1, padLit c.l2, padLit c.l3⟩

/-- La cláusula `i` de la acolchada: tautología en las pares, la `i / 2` renombrada en las impares. -/
def padAt (φ : Cnf) (i : Nat) : Clause := if i % 2 = 0 then tautC else padClause (φ.clauses.getD (i / 2) tautC)

/-- **La fórmula acolchada.** -/
def padCnf (φ : Cnf) : Cnf :=
  { nVars := 2 * φ.nVars + 1, clauses := (List.range (2 * φ.clauses.length + 1)).map (padAt φ) }

variable {φ : Cnf}

theorem pad_getElem? (i : Nat) :
    (padCnf φ).clauses[i]? = if i < 2 * φ.clauses.length + 1 then some (padAt φ i) else none := by
  simp only [padCnf, List.getElem?_map]
  split
  · rename_i h; rw [List.getElem?_range h]; rfl
  · rename_i h; rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem pad_len : (padCnf φ).clauses.length = 2 * φ.clauses.length + 1 := by simp [padCnf]

theorem mem_pad {c : Clause} (h : c ∈ (padCnf φ).clauses) : c = tautC ∨ ∃ c0 ∈ φ.clauses, c = padClause c0 := by
  simp only [padCnf, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  unfold padAt
  split
  · exact Or.inl rfl
  · refine Or.inr ⟨_, ?_, rfl⟩
    have : i / 2 < φ.clauses.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    exact List.getElem_mem this

theorem satClause_taut (a : Assign) : SatClause a tautC := by
  unfold SatClause litVal tautC
  cases a 0 <;> simp

theorem satClause_pad (a : Assign) (c : Clause) :
    SatClause a (padClause c) ↔ SatClause (fun v => a (2 * v + 1)) c := by
  simp only [SatClause, litVal, padClause, padLit]; exact Iff.rfl

theorem sat_pad_iff (a : Assign) : Sat a (padCnf φ) ↔ Sat (fun v => a (2 * v + 1)) φ := by
  constructor
  · intro h c hc
    obtain ⟨i, hi', hi⟩ := List.mem_iff_getElem.mp hc
    have hm : padClause c ∈ (padCnf φ).clauses := by
      simp only [padCnf, List.mem_map, List.mem_range]
      refine ⟨2 * i + 1, by omega, ?_⟩
      simp only [padAt, show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some, hi]
      rfl
    exact (satClause_pad a c).mp (h _ hm)
  · intro h c hc
    rcases mem_pad hc with rfl | ⟨c0, hc0, rfl⟩
    · exact satClause_taut a
    · exact (satClause_pad a c0).mpr (h c0 hc0)

/-- **El acolchado conserva la satisfacibilidad.** -/
theorem satisfiable_pad : Satisfiable (padCnf φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨_, (sat_pad_iff a).mp ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a (z / 2), (sat_pad_iff _).mpr ?_⟩
    have e : (fun v => (fun z => a (z / 2)) (2 * v + 1)) = a := by
      funext v; simp only [show (2 * v + 1) / 2 = v by omega]
    rw [e]; exact ha

theorem bounded_pad (hb : Bounded φ) : Bounded (padCnf φ) := by
  intro c hc
  rcases mem_pad hc with rfl | ⟨c0, hc0, rfl⟩
  · simp only [Clause.Bounded, tautC, padCnf]; omega
  · have := hb c0 hc0
    simp only [Clause.Bounded, padClause, padLit, padCnf] at this ⊢
    omega

/-- Las variables de relleno: las pares. -/
def PadFree (z : Nat) : Prop := z % 2 = 0

/-- **Las de relleno solo están en la tautología**, de una sola variable. -/
theorem freeOK_pad : FreeOK (padCnf φ) PadFree := by
  intro c hc z hz hf z' hz'
  rcases mem_pad hc with rfl | ⟨c0, _, rfl⟩
  · simp only [ClVar, tautC] at hz hz'
    omega
  · exfalso
    simp only [ClVar, padClause, padLit, PadFree] at hz hf
    omega

/-- Una cláusula de la acolchada que contiene una impar es de índice impar. -/
theorem pad_odd_index {i : Nat} {c : Clause} (h : (padCnf φ).clauses[i]? = some c) {z : Nat} (hz : ClVar c z)
    (hn : ¬ PadFree z) : i % 2 = 1 := by
  rw [pad_getElem?] at h
  split at h
  · cases h
    unfold padAt at hz
    split at hz
    · simp only [ClVar, tautC, PadFree] at hz hn; omega
    · omega
  · cases h

/-- Lo que lee un paso: una variable de la parte de variables, o un literal de la cláusula del paso. -/
theorem stepVar_kind {ψ : Cnf} {k : Int} {z : Nat} (h : stepVar ψ k = some z) :
    (0 < k ∧ k < midFusion ψ ∧ z = varOfStep k) ∨
    (midFusion ψ < k ∧ k < fusionTop ψ ∧ ∃ c, ψ.clauses[((k - midFusion ψ - 1) / 3).toNat]? = some c ∧ ClVar c z) := by
  unfold stepVar at h
  by_cases h0 : k ≤ 0
  · rw [if_pos h0] at h; cases h
  rw [if_neg h0] at h
  by_cases h1 : k < midFusion ψ
  · rw [if_pos h1] at h; cases h; exact Or.inl ⟨by omega, h1, rfl⟩
  rw [if_neg h1] at h
  by_cases h2 : k = midFusion ψ
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : fusionTop ψ ≤ k
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  cases hc : clauseOf ψ k with
  | none => rw [hc] at h; cases h
  | some cp =>
    obtain ⟨c, p⟩ := cp
    rw [hc] at h
    cases h
    refine Or.inr ⟨by omega, by omega, c, ?_, ?_⟩
    · simp only [clauseOf] at hc
      split at hc
      · cases hc
      · rename_i c' hc'
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rw [hc', hc.1]
    · unfold litAt ClVar
      split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

/-- **Lecturas locales de la acolchada.** -/
theorem localBlocks_pad : LocalBlocks (padCnf φ) PadFree := by
  intro k
  by_cases hk : k ≤ midFusion (padCnf φ) + 2
  · -- la parte de variables (y los dos primeros pasos de la tautología inicial)
    let v0 := varOfStep k
    refine ⟨.var (if v0 % 2 = 1 then v0 else v0 - 1), fun z hz hf => Or.inl ?_⟩
    obtain ⟨k', hw, hs⟩ := hz
    rcases stepVar_kind hs with ⟨a0, a1, rfl⟩ | ⟨a0, _, c, hc, hcz⟩
    · simp only [PadFree] at hf
      have hk' : k' ≤ k ∧ k - 2 ≤ k' := by
        rcases hw with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      simp only [v0, varOfStep] at hf ⊢
      split <;> (congr 1; omega)
    · -- la cláusula del paso es la 0, la tautología
      exfalso
      have hk' : k' ≤ k := by rcases hw with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      have hi : ((k' - midFusion (padCnf φ) - 1) / 3).toNat = 0 := by omega
      rw [hi, pad_getElem?, if_pos (by omega)] at hc
      cases hc
      simp only [padAt, Nat.zero_mod, if_true, ClVar, tautC] at hcz
      exact hf (by simp only [PadFree]; omega)
  · -- la parte de cláusulas: la impar de las dos cláusulas que toca la ventana
    let J := ((k - midFusion (padCnf φ) - 1) / 3).toNat
    let J0 := if J % 2 = 1 then J else J - 1
    by_cases hJ : (padCnf φ).clauses[J0]?.isSome
    · obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hJ
      refine ⟨.cls J0, fun z hz hf => Or.inr ⟨J0, c0, rfl, hc0, ?_⟩⟩
      obtain ⟨k', hw, hs⟩ := hz
      have hk' : k' ≤ k ∧ k - 2 ≤ k' := by rcases hw with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      rcases stepVar_kind hs with ⟨_, a1, _⟩ | ⟨a0, _, c, hc, hcz⟩
      · omega
      · have hodd := pad_odd_index hc hcz hf
        have e : ((k' - midFusion (padCnf φ) - 1) / 3).toNat = J0 := by
          simp only [J0, J]
          split <;> omega
        rw [e, hc0] at hc
        cases hc
        exact hcz
    · -- ninguna cláusula impar ahí: la ventana no lee impares
      refine ⟨.var 0, fun z hz hf => ?_⟩
      exfalso
      obtain ⟨k', hw, hs⟩ := hz
      have hk' : k' ≤ k ∧ k - 2 ≤ k' := by rcases hw with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      rcases stepVar_kind hs with ⟨_, a1, _⟩ | ⟨a0, _, c, hc, hcz⟩
      · omega
      · have hodd := pad_odd_index hc hcz hf
        have e : ((k' - midFusion (padCnf φ) - 1) / 3).toNat = J0 := by
          simp only [J0, J]
          split <;> omega
        rw [e] at hc
        rw [hc] at hJ
        exact hJ rfl

-- ============================================================
-- El bosque de la acolchada
-- ============================================================

/-- Un vértice de `φ` en la acolchada. -/
def padVx : Vx → Vx
  | .var v => .var (2 * v + 1)
  | .cls j => .cls (2 * j + 1)

namespace IncForest

variable (F : IncForest φ) (r : Vx)

/-- El padre en la acolchada: el de `φ` en las impares; el relleno cuelga de la raíz y la tautología de `x₀`. -/
def padPar : Vx → Option Vx
  | .var z => if z % 2 = 1 then (F.par (.var (z / 2))).map padVx else some (padVx r)
  | .cls J => if J % 2 = 1 then (F.par (.cls (J / 2))).map padVx else some (.var 0)

def padDep : Vx → Nat
  | .var z => if z % 2 = 1 then F.dep (.var (z / 2)) else F.dep r + 1
  | .cls J => if J % 2 = 1 then F.dep (.cls (J / 2)) else F.dep r + 2

theorem padPar_img (v : Vx) : F.padPar r (padVx v) = (F.par v).map padVx := by
  cases v with
  | var z => simp only [padVx, padPar, show (2 * z + 1) % 2 = 1 by omega, if_true, show (2 * z + 1) / 2 = z by omega]
  | cls j => simp only [padVx, padPar, show (2 * j + 1) % 2 = 1 by omega, if_true, show (2 * j + 1) / 2 = j by omega]

theorem padDep_img (v : Vx) : F.padDep r (padVx v) = F.dep v := by
  cases v with
  | var z => simp only [padVx, padDep, show (2 * z + 1) % 2 = 1 by omega, if_true, show (2 * z + 1) / 2 = z by omega]
  | cls j => simp only [padVx, padDep, show (2 * j + 1) % 2 = 1 by omega, if_true, show (2 * j + 1) / 2 = j by omega]

/-- **El bosque de incidencia de la acolchada.** -/
def pad : IncForest (padCnf φ) where
  par := F.padPar r
  dep := F.padDep r
  dep_lt := by
    intro v p h
    cases v with
    | var z =>
      simp only [padPar] at h
      split at h
      · rename_i hz
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [padDep_img]
        simp only [padDep, if_pos hz]
        exact F.dep_lt _ _ hq
      · rename_i hz
        cases h
        rw [padDep_img]
        simp only [padDep, if_neg hz]
        omega
    | cls J =>
      simp only [padPar] at h
      split at h
      · rename_i hJ
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [padDep_img]
        simp only [padDep, if_pos hJ]
        exact F.dep_lt _ _ hq
      · rename_i hJ
        cases h
        simp only [padDep, if_neg hJ, Nat.zero_mod, show ¬ (0 % 2 = 1) by omega, if_false]
        omega
  edge := by
    intro J c z hJ hz
    rw [pad_getElem?] at hJ
    split at hJ
    · cases hJ
      unfold padAt at hz
      split at hz
      · rename_i he
        right
        simp only [ClVar, tautC] at hz
        have hz0 : z = 0 := by omega
        subst hz0
        simp only [padPar, show ¬ (J % 2 = 1) by omega, if_false]
      · rename_i ho hlt
        have hj : J / 2 < φ.clauses.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hz
        have hc0 : φ.clauses[J / 2]? = some φ.clauses[J / 2] := List.getElem?_eq_getElem hj
        -- `z` es la imagen de una variable de la cláusula `J / 2`
        obtain ⟨v, hv, rfl⟩ : ∃ v, ClVar φ.clauses[J / 2] v ∧ z = 2 * v + 1 := by
          simp only [ClVar, padClause, padLit] at hz
          rcases hz with e | e | e
          · exact ⟨_, Or.inl rfl, e⟩
          · exact ⟨_, Or.inr (Or.inl rfl), e⟩
          · exact ⟨_, Or.inr (Or.inr rfl), e⟩
        have eJ : Vx.cls J = padVx (.cls (J / 2)) := by simp only [padVx]; congr 1; omega
        have ev : Vx.var (2 * v + 1) = padVx (.var v) := rfl
        rcases F.edge (J / 2) _ v hc0 hv with h | h
        · left
          show F.padPar r (.var (2 * v + 1)) = some (.cls J)
          rw [ev, padPar_img, h, eJ]; rfl
        · right
          show F.padPar r (.cls J) = some (.var (2 * v + 1))
          rw [eJ, padPar_img, h]; rfl
    · cases hJ

theorem pad_parN (n : Nat) (v : Vx) : (F.pad r).parN n (padVx v) = (F.parN n v).map padVx := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [parN]
    show (match F.padPar r (padVx v) with | none => none | some p => (F.pad r).parN n p) = _
    rw [padPar_img]
    cases F.par v with
    | none => rfl
    | some p => exact ih p

/-- **La raíz común pasa a la acolchada.** -/
theorem pad_root (hroot : ∀ v, F.Anc r v) : ∀ v, (F.pad r).Anc (padVx r) v := by
  have img : ∀ v, (F.pad r).Anc (padVx r) (padVx v) := by
    intro v
    obtain ⟨n, hn⟩ := hroot v
    exact ⟨n, by rw [pad_parN, hn]; rfl⟩
  intro v
  cases v with
  | var z =>
    by_cases hz : z % 2 = 1
    · have e : Vx.var z = padVx (.var (z / 2)) := by simp only [padVx]; congr 1; omega
      rw [e]; exact img _
    · exact (F.pad r).anc_par (show F.padPar r (.var z) = some (padVx r) by
        simp only [padPar, if_neg hz]) ((F.pad r).anc_refl _)
  | cls J =>
    by_cases hJ : J % 2 = 1
    · have e : Vx.cls J = padVx (.cls (J / 2)) := by simp only [padVx]; congr 1; omega
      rw [e]; exact img _
    · have h0 : (F.pad r).Anc (padVx r) (.var 0) := (F.pad r).anc_par
        (show F.padPar r (.var 0) = some (padVx r) by simp only [padPar]; rfl) ((F.pad r).anc_refl _)
      exact (F.pad r).anc_par (show F.padPar r (.cls J) = some (.var 0) by simp only [padPar, if_neg hJ]) h0

end IncForest

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por nodos de ventana sobre la acolchada de un árbol de cláusulas**: si `φ` tiene un bosque de
incidencia de raíz común, sobre `padCnf φ` (que es satisfacible si y solo si `φ` lo es) el lector no se atasca, dadas
las líneas de la acolchada. -/
theorem reader_winNode_pad (hbd : Bounded φ) (F : IncForest φ) {r : Vx} (hroot : ∀ v, F.Anc r v)
    (HA : ∀ T : Int, 1 ≤ T → PhantomAtW (padCnf φ) T) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on (padCnf φ))
    {W : List (List NodeId)} {g' : GPathB} (hr : WinReading (padCnf φ) kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a (padCnf φ) ∧ (∀ q ∈ W.flatten, selOfAssign (padCnf φ) a q.step = q) ∧
      CT g' (pidOfAssign (padCnf φ) a) :=
  reader_winNode_of_forest (bounded_pad hbd) HA (F.pad r) (F.pad_root r hroot) freeOK_pad localBlocks_pad hkv hr

end MachineOn

end AbsSatBingo.Model
