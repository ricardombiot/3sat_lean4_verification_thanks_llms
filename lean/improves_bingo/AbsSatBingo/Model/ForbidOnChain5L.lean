-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean
import AbsSatBingo.Model.ForbidOnChain5

/-!
# Las líneas de `chain5_cross`, y la máquina exacta y el lector por separadores sin hipótesis

Las líneas de las cuatro primeras cláusulas solo ven su prefijo (`phantomAt_of_prefix`), que es una cadena más corta:

* `c5p4` (cuatro cláusulas, once variables): `chain4_cross` con dos variables más que no aparecen; `Chain4L2`
  (`chain4L2_c5p4`), copiada de `ForbidOnChain4X`.
* `c5p3` (tres cláusulas): `Chain3` (`chain3_c5p3`).
* `c5p2`, `c5p1`: `Sep2`.

La última cláusula `(¬x8 ∨ x9 ∨ x10)`, sobre la fórmula entera: `x8` es `s4` (`phantomFree_chain5_s4`); `x9` está en
una sola cláusula y no es su tercer literal (`OnceNotLast`); `x10`, en el filtro, aún libre (`FreeBelow`), y en el UP de
su paso, `phantomFree_up_lastC`.

Resultado: **`phantomAt_chain5Cross`**, **`machineExact_chain5Cross`**, **`spineVerdictOn_iff_chain5Cross`** y
**`reader_sep_chain5Cross_full`**: el lector por separadores no se atasca en `chain5_cross`, sin ninguna hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

-- ============================================================
-- Cuatro cláusulas
-- ============================================================

/-- Las cuatro primeras cláusulas de `chain5_cross`, con sus once variables. -/
def c5p4 : Cnf :=
  ⟨11, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩, ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩, ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩,
    ⟨⟨7, false⟩, ⟨3, true⟩, ⟨8, true⟩⟩]⟩

theorem bounded_c5p4 : Bounded c5p4 := by
  intro c hc
  simp only [c5p4, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Clause.Bounded, c5p4]

theorem chain4Data_c5p4 : Chain4Data c5p4 5 6 7 (fun z => z = 0 ∨ z = 2) (fun z => z = 4)
    (fun z => z = 1) (fun z => z = 3 ∨ z = 8) := by
  refine ⟨by decide, by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, fun z a b => by omega,
    fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
    fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
    fun z1 z2 a b => by omega, fun c hc => ?_⟩
  simp only [c5p4, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (by simp [ClIn]))
  · exact Or.inr (Or.inr (Or.inl (by simp [ClIn])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [ClIn]))))

theorem chain4Data_c5p4_rev : Chain4Data c5p4 7 6 5 (fun z => z = 3 ∨ z = 8) (fun z => z = 1)
    (fun z => z = 4) (fun z => z = 0 ∨ z = 2) := by
  refine ⟨by decide, by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, fun z a b => by omega,
    fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
    fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
    fun z1 z2 a b => by omega, fun c hc => ?_⟩
  simp only [c5p4, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inl (by simp [ClIn])))
  · exact Or.inr (Or.inl (by simp [ClIn]))

theorem clauses_c5p4 {j : Nat} {c : Clause} (hj : c5p4.clauses[j]? = some c) :
    (j = 0 ∧ c = ⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩) ∨ (j = 1 ∧ c = ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩) ∨
      (j = 2 ∧ c = ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩) ∨ (j = 3 ∧ c = ⟨⟨7, false⟩, ⟨3, true⟩, ⟨8, true⟩⟩) := by
  match j, hj with
  | 0, hj => simp [c5p4] at hj; exact Or.inl ⟨rfl, hj.symm⟩
  | 1, hj => simp [c5p4] at hj; exact Or.inr (Or.inl ⟨rfl, hj.symm⟩)
  | 2, hj => simp [c5p4] at hj; exact Or.inr (Or.inr (Or.inl ⟨rfl, hj.symm⟩))
  | 3, hj => simp [c5p4] at hj; exact Or.inr (Or.inr (Or.inr ⟨rfl, hj.symm⟩))
  | _ + 4, hj => simp [c5p4] at hj

theorem onceNotLast_c5p4 {v : Nat} (h5 : v ≠ 5) (h6 : v ≠ 6) (h7 : v ≠ 7) (h8 : v ≠ 8) :
    OnceNotLast c5p4 v := by
  intro j c hj hcv
  rcases clauses_c5p4 hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [ClVar] at hcv
    refine ⟨by simp; omega, fun j' c' hj' hcv' => ?_⟩
    rcases clauses_c5p4 hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [ClVar] at hcv'; omega

theorem struct4_c5p4_sep {v : Nat} (h : v = 5 ∨ v = 6 ∨ v = 7) : Struct4 c5p4 v := by
  rcases h with rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, chain4Data_c5p4_rev⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, chain4Data_c5p4⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, chain4Data_c5p4⟩))

theorem struct4_c5p4_out {v : Nat} (h : 9 ≤ v) : Struct4 c5p4 v := by
  refine Or.inl ⟨v, fun _ => False, fun _ => False, ⟨fun h => absurd rfl h, fun h => h, fun _ h _ => h, Or.inl rfl,
    fun _ _ _ h _ _ _ _ _ => h, fun _ _ _ h _ _ _ _ _ => h, fun h => absurd rfl h, fun c hc => ?_⟩⟩
  simp only [c5p4, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩

theorem win_c5p4_56 :
    ReadsAt c5p4 (clauseStep c5p4 1 2) 5 ∧ ReadsAt c5p4 (clauseStep c5p4 1 2) 6 := by
  have hj : c5p4.clauses[1]? = some ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩ := rfl
  refine ⟨⟨clauseStep c5p4 1 0, Or.inr (Or.inr ⟨by simp [clauseStep, c5p4],
    by simp [clauseStep, c5p4]⟩), stepVar_clause hj 0 (by omega)⟩,
    ⟨clauseStep c5p4 1 2, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩⟩

theorem win_c5p4_76 :
    ReadsAt c5p4 (clauseStep c5p4 2 2) 7 ∧ ReadsAt c5p4 (clauseStep c5p4 2 2) 6 := by
  have hj : c5p4.clauses[2]? = some ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩ := rfl
  refine ⟨⟨clauseStep c5p4 2 2, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩,
    ⟨clauseStep c5p4 2 0, Or.inr (Or.inr ⟨by simp [clauseStep, c5p4],
      by simp [clauseStep, c5p4]⟩), stepVar_clause hj 0 (by omega)⟩⟩

/-- Las líneas: `x8` (el tercer literal de la última cláusula) por la ventana de `(¬x5 ∨ x4 ∨ x6)`, que va antes. -/
theorem chain4L2_c5p4 : Chain4L2 c5p4 := by
  intro v
  by_cases hs : v = 5 ∨ v = 6 ∨ v = 7
  · exact Or.inl (struct4_c5p4_sep hs)
  by_cases h9 : 9 ≤ v
  · exact Or.inl (struct4_c5p4_out h9)
  by_cases h8 : v = 8
  · subst h8
    refine Or.inr (Or.inr ⟨_, _, _, _, _, _, _, chain4Data_c5p4, Or.inl (Or.inr rfl),
      clauseStep c5p4 1 2, by simp [clauseStep, c5p4], win_c5p4_56.1, win_c5p4_56.2,
      fun j c p hj hp hpv => ?_⟩)
    rcases clauses_c5p4 hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · match p, hp with
      | 0, _ => simp [litAt] at hpv
      | 1, _ => simp [litAt] at hpv
      | 2, _ => first | (simp [litAt] at hpv; done) | simp [clauseStep, c5p4]
  · exact Or.inr (Or.inl (onceNotLast_c5p4 (by omega) (by omega) (by omega) h8))



-- ============================================================
-- Tres, dos y una cláusula
-- ============================================================

/-- Las tres primeras cláusulas: `(x0 ∨ x2 ∨ x5) ∧ (¬x5 ∨ x4 ∨ x6) ∧ (¬x6 ∨ x1 ∨ x7)`. -/
def c5p3 : Cnf :=
  ⟨11, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩, ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩, ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩]⟩

/-- Las dos primeras. -/
def c5p2 : Cnf := ⟨11, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩, ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩]⟩

/-- La primera. -/
def c5p1 : Cnf := ⟨11, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩]⟩

theorem bounded_c5p3 : Bounded c5p3 := by
  intro c hc
  simp only [c5p3, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp [Clause.Bounded, c5p3]

theorem bounded_c5p2 : Bounded c5p2 := by
  intro c hc
  simp only [c5p2, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [Clause.Bounded, c5p2]

theorem bounded_c5p1 : Bounded c5p1 := by
  intro c hc
  simp only [c5p1, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl; simp [Clause.Bounded, c5p1]

theorem chain3_c5p3 : Chain3 c5p3 := by
  intro v
  by_cases hr : v = 1 ∨ v = 7 ∨ v = 6 ∨ v = 4
  · refine Or.inr ⟨5, 6, fun z => z = 0 ∨ z = 2, fun z => z = 4, fun z => z = 1 ∨ z = 7,
      ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
        fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
        ?_, fun c hc => ?_⟩⟩
    · by_cases h17 : v = 1 ∨ v = 7
      · exact Or.inl ⟨h17, fun z1 z2 a b c d => by omega⟩
      · by_cases h6 : v = 6
        · exact Or.inr (Or.inl h6)
        · exact Or.inr (Or.inr (by omega))
    · simp only [c5p3, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inr (Or.inl (by simp))
      · exact Or.inr (Or.inr (Or.inl (by simp)))
      · exact Or.inr (Or.inr (Or.inr (by simp)))
  · by_cases hl : v = 0 ∨ v = 2 ∨ v = 5
    · refine Or.inr ⟨6, 5, fun z => z = 1 ∨ z = 7, fun z => z = 4, fun z => z = 0 ∨ z = 2,
        ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
          fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
          ?_, fun c hc => ?_⟩⟩
      · by_cases h02 : v = 0 ∨ v = 2
        · exact Or.inl ⟨h02, fun z1 z2 a b c d => by omega⟩
        · exact Or.inr (Or.inl (by omega))
      · simp only [c5p3, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (by simp)))
        · exact Or.inr (Or.inr (Or.inl (by simp)))
        · exact Or.inr (Or.inl (by simp))
    · refine Or.inl ⟨v, fun _ => False, fun _ => False, ⟨fun h => absurd rfl h, fun h => h, fun _ h _ => h,
        Or.inl rfl, fun _ _ _ h _ _ _ _ _ => h, fun _ _ _ h _ _ _ _ _ => h, fun h => absurd rfl h, fun c hc => ?_⟩⟩
      simp only [c5p3, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩

theorem sep2_c5p2 : Sep2 c5p2 := by
  intro v
  by_cases h2 : v = 5 ∨ (v = 4 ∨ v = 6)
  · refine ⟨5, fun z => z = 0 ∨ z = 2, fun z => z = 4 ∨ z = 6, ⟨fun _ => by decide, by omega,
      fun z a b => by omega, h2, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega,
      fun hne z1 z2 a b d => by omega, fun c hc => ?_⟩⟩
    simp only [c5p2, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (by simp))
  · by_cases h02 : v = 0 ∨ v = 2
    · refine ⟨5, fun z => z = 4 ∨ z = 6, fun z => z = 0 ∨ z = 2, ⟨fun _ => by decide, by omega,
        fun z a b => by omega, Or.inr h02, fun z1 z2 z3 a b c d e f => by omega,
        fun z1 z2 z3 a b c d e f => by omega, fun hne z1 z2 a b d => by omega, fun c hc => ?_⟩⟩
      simp only [c5p2, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Or.inr (Or.inr (by simp))
      · exact Or.inr (Or.inl (by simp))
    · refine ⟨v, fun _ => False, fun _ => False, ⟨fun h => absurd rfl h, fun h => h, fun _ h _ => h, Or.inl rfl,
        fun _ _ _ h _ _ _ _ _ => h, fun _ _ _ h _ _ _ _ _ => h, fun h => absurd rfl h, fun c hc => ?_⟩⟩
      simp only [c5p2, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩

theorem sep2_c5p1 : Sep2 c5p1 := by
  intro v
  by_cases h : v = 0 ∨ v = 2 ∨ v = 5
  · refine ⟨v, fun _ => False, fun z => (z = 0 ∨ z = 2 ∨ z = 5) ∧ z ≠ v, ⟨fun h => absurd rfl h,
      fun h => h.2 rfl, fun _ h _ => h, Or.inl rfl, fun _ _ _ h _ _ _ _ _ => h,
      fun z1 z2 z3 a b c d e f => by omega, fun h => absurd rfl h, fun c hc => ?_⟩⟩
    simp only [c5p1, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact Or.inr (Or.inr ⟨by simp; omega, by simp; omega, by simp; omega⟩)
  · refine ⟨v, fun _ => False, fun _ => False, ⟨fun h => absurd rfl h, fun h => h, fun _ h _ => h, Or.inl rfl,
      fun _ _ _ h _ _ _ _ _ => h, fun _ _ _ h _ _ _ _ _ => h, fun h => absurd rfl h, fun c hc => ?_⟩⟩
    simp only [c5p1, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩

theorem c5p4_eq : prefixCnf chain5Cross 4 = c5p4 := rfl
theorem c5p3_eq : prefixCnf chain5Cross 3 = c5p3 := rfl
theorem c5p2_eq : prefixCnf chain5Cross 2 = c5p2 := rfl
theorem c5p1_eq : prefixCnf chain5Cross 1 = c5p1 := rfl

end AbsSatBingo.Model

-- ============================================================
-- Las líneas de `chain5_cross`
-- ============================================================

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

theorem clauses_chain5Cross {j : Nat} {c : Clause} (hj : chain5Cross.clauses[j]? = some c) :
    (j = 0 ∧ c = ⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩) ∨ (j = 1 ∧ c = ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩) ∨
      (j = 2 ∧ c = ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩) ∨ (j = 3 ∧ c = ⟨⟨7, false⟩, ⟨3, true⟩, ⟨8, true⟩⟩) ∨
      (j = 4 ∧ c = ⟨⟨8, false⟩, ⟨9, true⟩, ⟨10, true⟩⟩) := by
  match j, hj with
  | 0, hj => simp [chain5Cross] at hj; exact Or.inl ⟨rfl, hj.symm⟩
  | 1, hj => simp [chain5Cross] at hj; exact Or.inr (Or.inl ⟨rfl, hj.symm⟩)
  | 2, hj => simp [chain5Cross] at hj; exact Or.inr (Or.inr (Or.inl ⟨rfl, hj.symm⟩))
  | 3, hj => simp [chain5Cross] at hj; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hj.symm⟩)))
  | 4, hj => simp [chain5Cross] at hj; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hj.symm⟩)))
  | _ + 5, hj => simp [chain5Cross] at hj

theorem onceNotLast_chain5Cross_9 : OnceNotLast chain5Cross 9 := by
  intro j c hj hcv
  rcases clauses_chain5Cross hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [ClVar] at hcv
    refine ⟨by first | (simp; done) | (simp; omega), fun j' c' hj' hcv' => ?_⟩
    rcases clauses_chain5Cross hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [ClVar] at hcv'; omega

theorem freeBelow_chain5Cross_10 {T : Int} (hT : T ≤ 38) : FreeBelow chain5Cross 10 T := by
  intro j c hj hcv
  rcases clauses_chain5Cross hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [ClVar] at hcv <;> first | omega | (simp [clauseStep, chain5Cross]; omega)

namespace GPathB

open Driver Machine MachineOn

/-- **Toda línea de `chain5_cross` cumple la condición fuerte**, sin hipótesis. -/
theorem phantomAt_chain5Cross (T : Int) (hT : 1 ≤ T) : PhantomAt chain5Cross T := by
  have hb := bounded_chain5Cross
  by_cases hlow : T + 1 ≤ midFusion chain5Cross + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  have hm : midFusion chain5Cross = 23 := rfl
  rw [hm] at hlow
  -- las cuatro primeras cláusulas: el prefijo
  by_cases p1 : T ≤ 26
  · exact phantomAt_of_prefix hb (j := 1) (by rw [c5p1_eq]; simp [fusionTop, c5p1]; omega)
      (by rw [c5p1_eq]; exact phantomAt_of_sep2 bounded_c5p1 sep2_c5p1 T hT)
  by_cases p2 : T ≤ 29
  · exact phantomAt_of_prefix hb (j := 2) (by rw [c5p2_eq]; simp [fusionTop, c5p2]; omega)
      (by rw [c5p2_eq]; exact phantomAt_of_sep2 bounded_c5p2 sep2_c5p2 T hT)
  by_cases p3 : T ≤ 32
  · exact phantomAt_of_prefix hb (j := 3) (by rw [c5p3_eq]; simp [fusionTop, c5p3]; omega)
      (by rw [c5p3_eq]; exact phantomAt_of_chain3 bounded_c5p3 chain3_c5p3 T hT)
  by_cases p4 : T ≤ 35
  · exact phantomAt_of_prefix hb (j := 4) (by rw [c5p4_eq]; simp [fusionTop, c5p4]; omega)
      (by rw [c5p4_eq]; exact phantomAt_of_chain4L2 bounded_c5p4 chain4L2_c5p4 T hT)
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step chain5Cross k d hd
    have hks := mapNodes_step chain5Cross (T - 1) k hk
    omega
  -- después de la última cláusula: nada que hacer
  by_cases hTop : 39 ≤ T
  · have hft : fusionTop chain5Cross ≤ d.step := by rw [hds]; simp [fusionTop, chain5Cross]; omega
    refine ⟨fun r hr => by rw [reqOf_above chain5Cross d hft] at hr; exact absurd hr List.not_mem_nil, ?_⟩
    have hsv : stepVar chain5Cross T = none := by
      have h1 : ¬ T ≤ 0 := by omega
      have h2 : ¬ T < midFusion chain5Cross := by rw [hm]; omega
      have h3 : ¬ T = midFusion chain5Cross := by rw [hm]; omega
      have h4 : fusionTop chain5Cross ≤ T := by simp [fusionTop, chain5Cross]; omega
      simp only [stepVar, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    exact phantomFree_none (locPair_up hb T k d) hsv (by omega) (show T < T + 1 by omega)
  -- la última cláusula `(¬x8 ∨ x9 ∨ x10)`, en los pasos 36, 37, 38
  have c1 : chain5Cross.clauses[1]? = some ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩ := rfl
  have c2 : chain5Cross.clauses[2]? = some ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩ := rfl
  have c4 : chain5Cross.clauses[4]? = some ⟨⟨8, false⟩, ⟨9, true⟩, ⟨10, true⟩⟩ := rfl
  have w1 := win_chain5Cross c1
  have w2 := win_chain5Cross c2
  have k1 : (0 : Int) ≤ clauseStep chain5Cross 1 2 ∧ clauseStep chain5Cross 1 2 < T := by
    simp [clauseStep, chain5Cross]; omega
  have k2 : (0 : Int) ≤ clauseStep chain5Cross 2 2 ∧ clauseStep chain5Cross 2 2 < T := by
    simp [clauseStep, chain5Cross]; omega
  have hc4 : ∀ p, p < 3 → clauseStep chain5Cross 4 p = 36 + p := fun p _ => by simp [clauseStep, chain5Cross]
  refine ⟨fun r hr => ?_, ?_⟩
  · -- el filtro
    obtain ⟨r1, r2⟩ := reqOf_range hb r hr
    rw [hds] at r2
    cases hv : stepVar chain5Cross r.step with
    | none => exact phantomFree_none (locPair_filter T k r) hv (by omega) r2
    | some v =>
      obtain ⟨j, c, p, hj, hp, e, hpv⟩ := req_lit hb hr hv (by rw [hds, hm]; omega)
      have hj4 : j = 4 := by
        rcases clauses_chain5Cross hj with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
          simp [clauseStep, chain5Cross] at e <;> omega
      subst hj4
      rw [c4] at hj; cases hj
      match p, hp with
      | 0, _ =>
        simp [litAt] at hpv; subst hpv
        exact phantomFree_chain5_s4 (locPair_filter T k r) chain5Data_chain5Cross hv ⟨k1.1, k1.2, w1.1, w1.2⟩
          ⟨k2.1, k2.2, w2.1, w2.2⟩ (by omega) r2 (by rw [hm]; omega)
      | 1, _ =>
        simp [litAt] at hpv; subst hpv
        have hf := freeBelow_filter hb hr hv onceNotLast_chain5Cross_9 (by rw [hds, hm]; omega)
        rw [hds] at hf
        exact phantomFree_free_filter hv hf (by omega) r2
      | 2, _ =>
        simp [litAt] at hpv; subst hpv
        exact phantomFree_free_filter hv (freeBelow_chain5Cross_10 (by rw [← hds, e, hc4 2 (by omega)]; omega))
          (by omega) r2
  · -- el UP
    have hT36 : T = 36 ∨ T = 37 ∨ T = 38 := by omega
    rcases hT36 with rfl | rfl | rfl
    · have hv : stepVar chain5Cross 36 = some 8 := by
        rw [show (36 : Int) = clauseStep chain5Cross 4 0 from (hc4 0 (by omega)).symm]
        exact stepVar_clause c4 0 (by omega)
      exact phantomFree_chain5_s4 (locPair_up hb 36 k d) chain5Data_chain5Cross hv
        ⟨k1.1, by omega, w1.1, w1.2⟩ ⟨k2.1, by omega, w2.1, w2.2⟩ (by omega) (by omega) (by rw [hm]; omega)
    · have hv : stepVar chain5Cross 37 = some 9 := by
        rw [show (37 : Int) = clauseStep chain5Cross 4 1 from (hc4 1 (by omega)).symm]
        exact stepVar_clause c4 1 (by omega)
      exact phantomFree_free_up hb hv (freeBelow_up hv onceNotLast_chain5Cross_9 (by rw [hm]; omega)) (by omega)
    · exact phantomFree_up_lastC hb chain5Data_chain5Cross (j := 4) (by decide) c4 (hc4 2 (by omega)).symm hds rfl
        (by decide) ⟨k1.1, by omega, w1.1, w1.2⟩ ⟨k2.1, by omega, w2.1, w2.2⟩

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **La máquina `:on` es exacta en `chain5_cross`**, la fórmula medida (cinco bloques, numeración cruzada), sin
ninguna hipótesis. -/
theorem machineExact_chain5Cross : MachineExact chain5Cross :=
  (machineExact_iff bounded_chain5Cross).2 phantomAt_chain5Cross

/-- **La espina `:on` decide `chain5_cross`.** -/
theorem spineVerdictOn_iff_chain5Cross : SpineVerdictOn chain5Cross ↔ Satisfiable chain5Cross :=
  spineVerdictOn_iff_of_phantomFree bounded_chain5Cross phantomAt_chain5Cross

/-- **El lector por separadores no se atasca en `chain5_cross`**, sin ninguna hipótesis: toda lectura que empieza por
`x5, x6, x7, x8` deja un estado válido con la rama de una solución que coincide con todas las elecciones. -/
theorem reader_sep_chain5Cross_full {kv : NodeId × GPathB} (hkv : kv ∈ runM .on chain5Cross) {R : List NodeId}
    {g' : GPathB} (hr : Reading kv.2 R g') (hsf : SepFirst chain5Cross [5, 6, 7, 8] R) :
    g'.isValid = true ∧ ∃ a, Sat a chain5Cross ∧ (∀ r ∈ R, selOfAssign chain5Cross a r.step = r) ∧
      CT g' (pidOfAssign chain5Cross a) :=
  reader_sep_chain5Cross (fun T hT => phantomAtW_of_phantomAt (phantomAt_chain5Cross T hT)) hkv hr hsf

end MachineOn

end AbsSatBingo.Model
