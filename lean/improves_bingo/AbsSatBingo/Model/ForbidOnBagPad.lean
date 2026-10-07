-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnBagPad.lean
import AbsSatBingo.Model.ForbidOnBagTree

/-!
# El acolchado por bolsas: una descomposición de anchura 2 se vuelve legible

Una fórmula con una descomposición en árbol de bolsas de a lo sumo tres variables (`TDec`, anchura ≤ 2; admite
ciclos) no tiene por qué cumplir `BagDec`: una bolsa que no es una cláusula no la lee ninguna ventana. El acolchado
por bolsas `tdCnf φ bags` lo arregla con tautologías:

* variables como en `padCnf`: la real `v` pasa a `2v + 1`, las pares son de relleno;
* cláusulas en bloques de tres: para cada bolsa `(a, b, c)`, `T, (a ∨ ¬a ∨ b), (c ∨ ¬c ∨ c)`; para cada cláusula,
  `T, C', T`; y una `T` final, con `T = (x₀ ∨ ¬x₀ ∨ x₀)`.

La ventana del primer paso de `(c ∨ ¬c ∨ c)` lee `¬a`, `b` y `c`: la bolsa entera (`tdCut`). Toda otra ventana lee,
fuera del relleno, variables de un solo bloque, y todo bloque cabe en una bolsa (`td_var_bag`).

* **`satisfiable_td`**, `bounded_td`, `freeOK_td`.
* **`TDec.bagDec`**: la descomposición de `φ` da un `BagDec` de la acolchada.
* **`reader_winNode_td`**: el lector por nodos de ventana no se atasca en la acolchada, dadas sus líneas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- La variable `z` está en la bolsa `(a, b, c)`. -/
def BIn (z : Nat) (t : Nat × Nat × Nat) : Prop := z = t.1 ∨ z = t.2.1 ∨ z = t.2.2

/-- Las bolsas como vértices: la bolsa `i` es `Vx.var i`; los demás vértices no tienen variables. -/
def TBag (bags : List (Nat × Nat × Nat)) : Vx → Nat → Prop
  | .var i, z => ∃ t, bags[i]? = some t ∧ BIn z t
  | .cls _, _ => False

/-- **Descomposición en árbol de anchura ≤ 2** de `φ`: bolsas de tres variables (con repeticiones) en un árbol con
raíz, cada cláusula en una bolsa, cada variable en un subárbol que sube hasta su cima. -/
structure TDec (φ : Cnf) where
  bags  : List (Nat × Nat × Nat)
  T     : IncForest emptyCnf
  root  : Vx
  hroot : ∀ v, T.Anc root v
  top   : Nat → Vx
  conn  : ∀ z t, TBag bags t z → t = top z ∨ ∃ p, T.par t = some p ∧ TBag bags p z
  cover : ∀ c ∈ φ.clauses, ∃ t, ∀ z, ClVar c z → TBag bags t z
  allv  : ∀ v, v < φ.nVars → ∃ t, TBag bags t v
  bnd   : ∀ t ∈ bags, t.1 < φ.nVars ∧ t.2.1 < φ.nVars ∧ t.2.2 < φ.nVars

/-- Las dos tautologías que leen la bolsa `(a, b, c)`. -/
def rd1 (t : Nat × Nat × Nat) : Clause := ⟨⟨2 * t.1 + 1, true⟩, ⟨2 * t.1 + 1, false⟩, ⟨2 * t.2.1 + 1, true⟩⟩
def rd2 (t : Nat × Nat × Nat) : Clause := ⟨⟨2 * t.2.2 + 1, true⟩, ⟨2 * t.2.2 + 1, false⟩, ⟨2 * t.2.2 + 1, true⟩⟩

/-- La cláusula `i` del acolchado por bolsas. -/
def tdAt (φ : Cnf) (bags : List (Nat × Nat × Nat)) (i : Nat) : Clause :=
  if i % 3 = 0 then tautC
  else if i / 3 < bags.length then
    (if i % 3 = 1 then rd1 (bags.getD (i / 3) (0, 0, 0)) else rd2 (bags.getD (i / 3) (0, 0, 0)))
  else if i % 3 = 1 then padClause (φ.clauses.getD (i / 3 - bags.length) tautC) else tautC

/-- **El acolchado por bolsas.** -/
def tdCnf (φ : Cnf) (bags : List (Nat × Nat × Nat)) : Cnf :=
  { nVars := 2 * φ.nVars + 1,
    clauses := (List.range (3 * (bags.length + φ.clauses.length) + 1)).map (tdAt φ bags) }

variable {φ : Cnf} {bags : List (Nat × Nat × Nat)}

theorem td_getElem? (i : Nat) :
    (tdCnf φ bags).clauses[i]? =
      if i < 3 * (bags.length + φ.clauses.length) + 1 then some (tdAt φ bags i) else none := by
  simp only [tdCnf, List.getElem?_map]
  split
  · rename_i h; rw [List.getElem?_range h]; rfl
  · rename_i h; rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem td_len : (tdCnf φ bags).clauses.length = 3 * (bags.length + φ.clauses.length) + 1 := by simp [tdCnf]

theorem mem_td {c : Clause} (h : c ∈ (tdCnf φ bags).clauses) :
    ∃ i, i < 3 * (bags.length + φ.clauses.length) + 1 ∧ c = tdAt φ bags i := by
  simp only [tdCnf, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, rfl⟩

theorem getD_bags {b : Nat} (hb : b < bags.length) : bags.getD b (0, 0, 0) ∈ bags := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
  exact List.getElem_mem hb

theorem getD_clauses {j : Nat} (hj : j < φ.clauses.length) : φ.clauses.getD j tautC ∈ φ.clauses := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

/-- Las cláusulas del acolchado: tautologías o cláusulas de `φ` renombradas. -/
theorem tdAt_kind (i : Nat) (hi : i < 3 * (bags.length + φ.clauses.length) + 1) :
    tdAt φ bags i = tautC ∨ (∃ t ∈ bags, tdAt φ bags i = rd1 t ∨ tdAt φ bags i = rd2 t) ∨
      ∃ c0 ∈ φ.clauses, tdAt φ bags i = padClause c0 := by
  unfold tdAt
  split
  · exact Or.inl rfl
  · split
    · rename_i _ hb
      split
      · exact Or.inr (Or.inl ⟨_, getD_bags hb, Or.inl rfl⟩)
      · exact Or.inr (Or.inl ⟨_, getD_bags hb, Or.inr rfl⟩)
    · split
      · exact Or.inr (Or.inr ⟨_, getD_clauses (by omega), rfl⟩)
      · exact Or.inl rfl

theorem satClause_rd1 (a : Assign) (t : Nat × Nat × Nat) : SatClause a (rd1 t) := by
  unfold SatClause litVal rd1
  cases a (2 * t.1 + 1) <;> simp

theorem satClause_rd2 (a : Assign) (t : Nat × Nat × Nat) : SatClause a (rd2 t) := by
  unfold SatClause litVal rd2
  cases a (2 * t.2.2 + 1) <;> simp

theorem sat_td_iff (a : Assign) : Sat a (tdCnf φ bags) ↔ Sat (fun v => a (2 * v + 1)) φ := by
  constructor
  · intro h c hc
    obtain ⟨j, hj', hj⟩ := List.mem_iff_getElem.mp hc
    have hm : padClause c ∈ (tdCnf φ bags).clauses := by
      simp only [tdCnf, List.mem_map, List.mem_range]
      refine ⟨3 * (bags.length + j) + 1, by omega, ?_⟩
      have e1 : (3 * (bags.length + j) + 1) % 3 = 1 := by omega
      have e2 : (3 * (bags.length + j) + 1) / 3 = bags.length + j := by omega
      simp only [tdAt, e1, e2, show ¬ (1 = 0) by omega, if_false, if_true,
        show ¬ (bags.length + j < bags.length) by omega, show bags.length + j - bags.length = j by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, hj]
    exact (satClause_pad a c).mp (h _ hm)
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := mem_td hc
    rcases tdAt_kind i hi with e | ⟨t, _, e | e⟩ | ⟨c0, hc0, e⟩ <;> rw [e]
    · exact satClause_taut a
    · exact satClause_rd1 a t
    · exact satClause_rd2 a t
    · exact (satClause_pad a c0).mpr (h c0 hc0)

/-- **El acolchado por bolsas conserva la satisfacibilidad.** -/
theorem satisfiable_td : Satisfiable (tdCnf φ bags) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨_, (sat_td_iff a).mp ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a (z / 2), (sat_td_iff _).mpr ?_⟩
    have e : (fun v => (fun z => a (z / 2)) (2 * v + 1)) = a := by
      funext v; simp only [show (2 * v + 1) / 2 = v by omega]
    rw [e]; exact ha

theorem bounded_td (hb : Bounded φ) (hbn : ∀ t ∈ bags, t.1 < φ.nVars ∧ t.2.1 < φ.nVars ∧ t.2.2 < φ.nVars) :
    Bounded (tdCnf φ bags) := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := mem_td hc
  rcases tdAt_kind i hi with e | ⟨t, ht, e | e⟩ | ⟨c0, hc0, e⟩ <;> rw [e]
  · simp only [Clause.Bounded, tautC, tdCnf]; omega
  · have := hbn t ht; simp only [Clause.Bounded, rd1, tdCnf]; omega
  · have := hbn t ht; simp only [Clause.Bounded, rd2, tdCnf]; omega
  · have := hb c0 hc0
    simp only [Clause.Bounded, padClause, padLit, tdCnf] at this ⊢
    omega

/-- **Las de relleno solo están en la tautología.** -/
theorem freeOK_td : FreeOK (tdCnf φ bags) PadFree := by
  intro c hc z hz hf z' hz'
  obtain ⟨i, hi, rfl⟩ := mem_td hc
  rcases tdAt_kind i hi with e | ⟨t, _, e | e⟩ | ⟨c0, _, e⟩ <;> rw [e] at hz hz'
  · simp only [ClVar, tautC] at hz hz'; omega
  · simp only [ClVar, rd1, PadFree] at hz hf; omega
  · simp only [ClVar, rd2, PadFree] at hz hf; omega
  · simp only [ClVar, padClause, padLit, PadFree] at hz hf; omega

-- ============================================================
-- La descomposición de la acolchada
-- ============================================================

namespace TDec

variable (D : TDec φ)

/-- El vértice del bloque `b`: la bolsa `b`, o la bolsa que cubre la cláusula `b - #bolsas`. -/
noncomputable def blk (b : Nat) : Vx :=
  if b < D.bags.length then .var b
  else if h : b - D.bags.length < φ.clauses.length then Classical.choose (D.cover _ (getD_clauses h))
  else D.root

/-- Las bolsas de la acolchada: las mismas, con las variables renombradas. -/
def bagT (t : Vx) (z : Nat) : Prop := ∃ v, z = 2 * v + 1 ∧ TBag D.bags t v

theorem tbag_getD {b : Nat} (hb : b < D.bags.length) {v : Nat} (h : BIn v (D.bags.getD b (0, 0, 0))) :
    TBag D.bags (.var b) v :=
  ⟨_, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]; rfl, h⟩

/-- **Lo que no es relleno en un bloque cabe en su bolsa.** -/
theorem td_var_bag {i : Nat} (hi : i < 3 * (D.bags.length + φ.clauses.length) + 1) {z : Nat}
    (hz : ClVar (tdAt φ D.bags i) z) (hf : ¬ PadFree z) : i % 3 ≠ 0 ∧ D.bagT (D.blk (i / 3)) z := by
  unfold tdAt at hz
  split at hz
  · simp only [ClVar, tautC, PadFree] at hz hf; omega
  · rename_i h0
    refine ⟨h0, ?_⟩
    split at hz
    · rename_i hb
      simp only [blk, if_pos hb]
      split at hz
      · simp only [ClVar, rd1] at hz
        rcases hz with e | e | e
        · exact ⟨_, e, D.tbag_getD hb (Or.inl rfl)⟩
        · exact ⟨_, e, D.tbag_getD hb (Or.inl rfl)⟩
        · exact ⟨_, e, D.tbag_getD hb (Or.inr (Or.inl rfl))⟩
      · simp only [ClVar, rd2] at hz
        rcases hz with e | e | e <;> exact ⟨_, e, D.tbag_getD hb (Or.inr (Or.inr rfl))⟩
    · rename_i hb
      split at hz
      · have hj : i / 3 - D.bags.length < φ.clauses.length := by omega
        simp only [blk, if_neg hb, dif_pos hj]
        have spec := Classical.choose_spec (D.cover _ (getD_clauses hj))
        simp only [ClVar, padClause, padLit] at hz
        rcases hz with e | e | e
        · exact ⟨_, e, spec _ (Or.inl rfl)⟩
        · exact ⟨_, e, spec _ (Or.inr (Or.inl rfl))⟩
        · exact ⟨_, e, spec _ (Or.inr (Or.inr rfl))⟩
      · simp only [ClVar, tautC, PadFree] at hz hf; omega

/-- El paso que lee la bolsa `b`: el primero de `(c ∨ ¬c ∨ c)`. -/
def tdCut (t : Vx) : Int :=
  match t with
  | .var b => if b < D.bags.length then clauseStep (tdCnf φ D.bags) (3 * b + 2) 0 else 0
  | .cls _ => 0

theorem tdCut_lo (t : Vx) : 0 ≤ D.tdCut t := by
  cases t with
  | var b => simp only [tdCut]; split <;> (try simp only [clauseStep]) <;> omega
  | cls j => exact Int.le_refl 0

theorem tdCut_hi (t : Vx) : D.tdCut t < stepCount (tdCnf φ D.bags) := by
  have hl := td_len (φ := φ) (bags := D.bags)
  cases t with
  | var b =>
    simp only [tdCut]; split
    · simp only [clauseStep, stepCount, hl]; omega
    · simp only [stepCount, hl]; omega
  | cls j => simp only [tdCut, stepCount, hl]; omega

/-- **La ventana de `tdCut` lee la bolsa entera.** -/
theorem td_read (t : Vx) (z : Nat) (h : D.bagT t z) : WR (tdCnf φ D.bags) (D.tdCut t) z ∨ PadFree z := by
  obtain ⟨v, rfl, hv⟩ := h
  cases t with
  | cls j => exact absurd hv id
  | var b =>
    obtain ⟨tr, htr, hin⟩ := hv
    have hb : b < D.bags.length := by
      by_cases hb : b < D.bags.length
      · exact hb
      · rw [List.getElem?_eq_none (by omega)] at htr; cases htr
    have hg : D.bags.getD b (0, 0, 0) = tr := by rw [List.getD_eq_getElem?_getD, htr]; rfl
    have L := td_len (φ := φ) (bags := D.bags)
    have c1 : (tdCnf φ D.bags).clauses[3 * b + 1]? = some (rd1 tr) := by
      rw [td_getElem?, if_pos (by omega)]
      simp only [tdAt, show (3 * b + 1) % 3 = 1 by omega, show (3 * b + 1) / 3 = b by omega, if_pos hb, hg]
      rfl
    have c2 : (tdCnf φ D.bags).clauses[3 * b + 2]? = some (rd2 tr) := by
      rw [td_getElem?, if_pos (by omega)]
      simp only [tdAt, show (3 * b + 2) % 3 = 2 by omega, show (3 * b + 2) / 3 = b by omega, if_pos hb, hg]
      rfl
    left
    simp only [tdCut, if_pos hb]
    have k1 : clauseStep (tdCnf φ D.bags) (3 * b + 2) 0 - 1 = clauseStep (tdCnf φ D.bags) (3 * b + 1) 2 := by
      simp only [clauseStep]; omega
    have k2 : clauseStep (tdCnf φ D.bags) (3 * b + 2) 0 - 2 = clauseStep (tdCnf φ D.bags) (3 * b + 1) 1 := by
      simp only [clauseStep]; omega
    have p0 : (0 : Int) < clauseStep (tdCnf φ D.bags) (3 * b + 2) 0 := by simp only [clauseStep]; omega
    have p1 : (1 : Int) < clauseStep (tdCnf φ D.bags) (3 * b + 2) 0 := by simp only [clauseStep]; omega
    rcases hin with rfl | rfl | rfl
    · exact ⟨_, Or.inr (Or.inr ⟨p1, rfl⟩), by rw [k2]; exact stepVar_clause c1 1 (by omega)⟩
    · exact ⟨_, Or.inr (Or.inl ⟨p0, rfl⟩), by rw [k1]; exact stepVar_clause c1 2 (by omega)⟩
    · exact ⟨_, Or.inl rfl, stepVar_clause c2 0 (by omega)⟩

/-- **Lecturas locales de la acolchada por bolsas**: lo que lee cada ventana, fuera del relleno, cabe en una bolsa. -/
theorem td_loc (k : Int) : ∃ t, ∀ z, WR (tdCnf φ D.bags) k z → ¬ PadFree z → D.bagT t z := by
  classical
  by_cases hk : k ≤ midFusion (tdCnf φ D.bags) + 2
  · -- la parte de variables (y los dos primeros pasos de la tautología inicial)
    let v0 := varOfStep k
    let zz := if v0 % 2 = 1 then v0 else v0 - 1
    refine ⟨if h : zz / 2 < φ.nVars then Classical.choose (D.allv _ h) else D.root, fun z hz hf => ?_⟩
    obtain ⟨k', hw, hs⟩ := hz
    rcases stepVar_kind hs with ⟨a0, a1, rfl⟩ | ⟨a0, _, c, hc, hcz⟩
    · simp only [PadFree] at hf
      have hk' : k' ≤ k ∧ k - 2 ≤ k' := by
        rcases hw with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      have e : varOfStep k' = zz := by
        simp only [zz, v0, varOfStep] at hf ⊢
        split <;> omega
      have hm : midFusion (tdCnf φ D.bags) = 4 * (φ.nVars : Int) + 3 := by simp only [midFusion, tdCnf]; omega
      have hv : varOfStep k' < 2 * φ.nVars + 1 := by simp only [varOfStep]; omega
      have hlt : zz / 2 < φ.nVars := by omega
      rw [dif_pos hlt]
      exact ⟨zz / 2, by omega, Classical.choose_spec (D.allv _ hlt)⟩
    · -- la cláusula del paso es la 0, la tautología
      exfalso
      have hk' : k' ≤ k := by rcases hw with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      have hi : ((k' - midFusion (tdCnf φ D.bags) - 1) / 3).toNat = 0 := by omega
      rw [hi, td_getElem?, if_pos (by omega)] at hc
      cases hc
      simp only [tdAt, Nat.zero_mod, if_true, ClVar, tautC] at hcz
      exact hf (by simp only [PadFree]; omega)
  · -- la parte de cláusulas: el bloque de las cláusulas que toca la ventana
    let J := ((k - midFusion (tdCnf φ D.bags) - 1) / 3).toNat
    refine ⟨D.blk ((if J % 3 = 0 then J - 1 else J) / 3), fun z hz hf => ?_⟩
    obtain ⟨k', hw, hs⟩ := hz
    have hk' : k' ≤ k ∧ k - 2 ≤ k' := by rcases hw with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    rcases stepVar_kind hs with ⟨_, a1, _⟩ | ⟨a0, _, c, hc, hcz⟩
    · omega
    · rw [td_getElem?] at hc
      split at hc
      · rename_i hlt
        cases hc
        obtain ⟨h3, hb⟩ := D.td_var_bag hlt hcz hf
        have e : ((k' - midFusion (tdCnf φ D.bags) - 1) / 3).toNat / 3 = (if J % 3 = 0 then J - 1 else J) / 3 := by
          simp only [J] at h3 ⊢
          split <;> omega
        rw [← e]
        exact hb
      · cases hc

/-- **La descomposición en árbol de la acolchada por bolsas.** -/
noncomputable def bagDec : BagDec (tdCnf φ D.bags) PadFree where
  T      := D.T
  root   := D.root
  hroot  := D.hroot
  bag    := D.bagT
  top    := fun z => D.top (z / 2)
  conn   := by
    intro z t ⟨v, hz, hv⟩
    have e : z / 2 = v := by omega
    rcases D.conn v t hv with h | ⟨p, hp, hpv⟩
    · exact Or.inl (by rw [e]; exact h)
    · exact Or.inr ⟨p, hp, v, hz, hpv⟩
  cover  := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := mem_td hc
    exact ⟨D.blk (i / 3), fun z hz hf => (D.td_var_bag hi hz hf).2⟩
  cut    := D.tdCut
  cut_lo := D.tdCut_lo
  cut_hi := D.tdCut_hi
  read   := D.td_read
  loc    := D.td_loc

end TDec

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por nodos de ventana sobre la acolchada por bolsas** de una fórmula de anchura de árbol ≤ 2 (que es
satisfacible si y solo si `φ` lo es): no se atasca, dadas las líneas de la acolchada. -/
theorem reader_winNode_td (hbd : Bounded φ) (D : TDec φ)
    (HA : ∀ T : Int, 1 ≤ T → PhantomAtW (tdCnf φ D.bags) T) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on (tdCnf φ D.bags)) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading (tdCnf φ D.bags) kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a (tdCnf φ D.bags) ∧
      (∀ q ∈ W.flatten, selOfAssign (tdCnf φ D.bags) a q.step = q) ∧ CT g' (pidOfAssign (tdCnf φ D.bags) a) :=
  reader_winNode_of_bags (bounded_td hbd D.bnd) HA D.bagDec freeOK_td hkv hr

end MachineOn

-- ============================================================
-- Un ejemplo con un ciclo: el triángulo con orejas
-- ============================================================

/-- **El triángulo con orejas**: `(x₀ ∨ ¬x₃ ∨ ¬x₁)`, `(x₁ ∨ ¬x₄ ∨ ¬x₂)`, `(x₂ ∨ ¬x₅ ∨ ¬x₀)`. Su grafo de incidencia
tiene el ciclo `x₀ – C₀ – x₁ – C₁ – x₂ – C₂ – x₀`: no es Berge-acíclica. Anchura de árbol 2: la bolsa central
`{x₀, x₁, x₂}` y una bolsa por cláusula colgando de ella. -/
def triCnf : Cnf :=
  ⟨6, [⟨⟨0, true⟩, ⟨3, false⟩, ⟨1, false⟩⟩, ⟨⟨1, true⟩, ⟨4, false⟩, ⟨2, false⟩⟩,
       ⟨⟨2, true⟩, ⟨5, false⟩, ⟨0, false⟩⟩]⟩

def triBags : List (Nat × Nat × Nat) := [(0, 1, 2), (0, 3, 1), (1, 4, 2), (2, 5, 0)]

/-- El árbol de bolsas: la central (`var 0`) es la raíz y todo lo demás cuelga de ella. -/
def triTree : IncForest emptyCnf where
  par := fun v => if v = .var 0 then none else some (.var 0)
  dep := fun v => if v = .var 0 then 0 else 1
  dep_lt := by
    intro v p h
    by_cases e : v = .var 0
    · simp only [e, if_true] at h; cases h
    · simp only [e, if_false, Option.some.injEq] at h
      subst h
      simp only [e, if_true, if_false]; omega
  edge := by
    intro j c z h _
    simp only [emptyCnf, List.getElem?_nil] at h
    cases h

theorem triTree_par {i : Nat} (h : i ≠ 0) : triTree.par (.var i) = some (.var 0) := by
  simp only [triTree]
  rw [if_neg (by intro e; cases e; exact h rfl)]

/-- **La descomposición del triángulo.** -/
def triDec : TDec triCnf where
  bags  := triBags
  T     := triTree
  root  := .var 0
  hroot := by
    intro v
    by_cases e : v = .var 0
    · subst e; exact triTree.anc_refl _
    · exact ⟨1, by simp only [IncForest.parN, triTree, if_neg e]⟩
  top   := fun z => if z = 3 then .var 1 else if z = 4 then .var 2 else if z = 5 then .var 3 else .var 0
  conn  := by
    intro z t h
    cases t with
    | cls j => exact absurd h id
    | var i =>
      obtain ⟨tr, htr, hin⟩ := h
      have up : ∀ {i : Nat}, i ≠ 0 → z = 0 ∨ z = 1 ∨ z = 2 →
          ∃ p, triTree.par (.var i) = some p ∧ TBag triBags p z := by
        intro i hi hz
        exact ⟨.var 0, triTree_par hi, (0, 1, 2), rfl, by simp only [BIn]; omega⟩
      rcases i with _ | _ | _ | _ | i
      · simp only [triBags] at htr; cases htr
        left; simp only [BIn] at hin
        rcases hin with rfl | rfl | rfl <;> rfl
      · simp only [triBags] at htr; cases htr
        simp only [BIn] at hin
        rcases hin with rfl | rfl | rfl
        · exact Or.inr (up (by omega) (Or.inl rfl))
        · exact Or.inl rfl
        · exact Or.inr (up (by omega) (Or.inr (Or.inl rfl)))
      · simp only [triBags] at htr; cases htr
        simp only [BIn] at hin
        rcases hin with rfl | rfl | rfl
        · exact Or.inr (up (by omega) (Or.inr (Or.inl rfl)))
        · exact Or.inl rfl
        · exact Or.inr (up (by omega) (Or.inr (Or.inr rfl)))
      · simp only [triBags] at htr; cases htr
        simp only [BIn] at hin
        rcases hin with rfl | rfl | rfl
        · exact Or.inr (up (by omega) (Or.inr (Or.inr rfl)))
        · exact Or.inl rfl
        · exact Or.inr (up (by omega) (Or.inl rfl))
      · simp only [triBags, List.getElem?_cons_succ, List.getElem?_nil] at htr; cases htr
  cover := by
    intro c hc
    simp only [triCnf, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨.var 1, fun z hz => ⟨_, rfl, by simp only [ClVar, BIn] at hz ⊢; omega⟩⟩
    · exact ⟨.var 2, fun z hz => ⟨_, rfl, by simp only [ClVar, BIn] at hz ⊢; omega⟩⟩
    · exact ⟨.var 3, fun z hz => ⟨_, rfl, by simp only [ClVar, BIn] at hz ⊢; omega⟩⟩
  allv  := by
    intro v hv
    simp only [triCnf] at hv
    by_cases h3 : v = 3
    · exact ⟨.var 1, _, rfl, by simp only [BIn]; omega⟩
    by_cases h4 : v = 4
    · exact ⟨.var 2, _, rfl, by simp only [BIn]; omega⟩
    by_cases h5 : v = 5
    · exact ⟨.var 3, _, rfl, by simp only [BIn]; omega⟩
    exact ⟨.var 0, _, rfl, by simp only [BIn]; omega⟩
  bnd   := by
    intro t ht
    simp only [triBags, List.mem_cons, List.not_mem_nil, or_false] at ht
    simp only [triCnf]
    rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem bounded_tri : Bounded triCnf := by
  intro c hc
  simp only [triCnf, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp only [Clause.Bounded, triCnf] <;> omega

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por ventanas sobre el triángulo acolchado** (una fórmula con un ciclo) no se atasca, dadas sus
líneas. -/
theorem reader_winNode_tri (HA : ∀ T : Int, 1 ≤ T → PhantomAtW (tdCnf triCnf triBags) T) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on (tdCnf triCnf triBags)) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading (tdCnf triCnf triBags) kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a (tdCnf triCnf triBags) ∧
      (∀ q ∈ W.flatten, selOfAssign (tdCnf triCnf triBags) a q.step = q) ∧
      CT g' (pidOfAssign (tdCnf triCnf triBags) a) :=
  reader_winNode_td bounded_tri triDec HA hkv hr

end MachineOn

end AbsSatBingo.Model
