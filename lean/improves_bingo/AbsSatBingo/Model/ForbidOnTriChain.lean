-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnTriChain.lean
import AbsSatBingo.Model.ForbidOnPathLine

/-!
# Cadenas de tríos consecutivos

**`TriChain φ x`**: la cláusula `j` es `(x j, x j + 1, x j + 2)` (con signos cualesquiera), `x 0 = 0` y los saltos
`x (j+1) - x j` valen 1 o 2, **sin dos saltos de 1 seguidos** (anchura ≤ 2). Un salto de 2 deja un corte de una
variable; uno de 1, un corte de dos. Son las cadenas de `gen_chain_wide.jl` y `gen_chain_triples.jl` en orden.

* **El camino de unidades del prefijo**: las cláusulas `0 … k` son las unidades; `loC`, `hiC` cuentan (con `filter`)
  las cláusulas que quedan a la izquierda de una variable. **`inU_iff`**: `z` vive en la unidad `p` si y solo si
  `x p ≤ z ≤ x p + 2`; **`cut_iff`**: el corte `c` es `x (c+1) … x c + 2`.
* **Las lecturas** (`sv_cases`): un paso lee una variable por su paso de variable o por un literal de una cláusula
  del prefijo.
* **Lecturas locales** (**`reads_pair`**): una ventana que lee una variable de dentro `z` lee también `z - 1` o `z + 1`.
* **El par** (**`pair_cut`**): todo par `{w, w + 1}` de dentro contiene un corte entero.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- **Una cadena de tríos consecutivos, de anchura ≤ 2.** -/
structure TriChain (φ : Cnf) (x : Nat → Nat) : Prop where
  pos  : 1 ≤ φ.clauses.length
  x0   : x 0 = 0
  cl   : ∀ j c, φ.clauses[j]? = some c → c.l1.v = x j ∧ c.l2.v = x j + 1 ∧ c.l3.v = x j + 2
  jmp  : ∀ j, x j + 1 ≤ x (j + 1) ∧ x (j + 1) ≤ x j + 2
  no11 : ∀ j, x j + 3 ≤ x (j + 2)
  nv   : φ.nVars = x (φ.clauses.length - 1) + 3

namespace TriChain

variable {φ : Cnf} {x : Nat → Nat}

theorem x_le (T : TriChain φ x) {i : Nat} : ∀ d, x i + d ≤ x (i + d)
  | 0 => Nat.le_refl _
  | d + 1 => by have := x_le T (i := i) d; have := (T.jmp (i + d)).1; show x i + (d + 1) ≤ x (i + d + 1); omega

theorem x_mono (T : TriChain φ x) {i j : Nat} (h : i ≤ j) : x i + (j - i) ≤ x j := by
  have := x_le T (i := i) (j - i); rwa [show i + (j - i) = j by omega] at this

theorem x_lt (T : TriChain φ x) {i j : Nat} (h : i < j) : x i < x j := by have := x_mono T (Nat.le_of_lt h); omega

/-- Un índice por debajo de otro, si su `x` está por debajo. -/
theorem lt_of_x (T : TriChain φ x) {i j : Nat} (h : x i < x j) : i < j :=
  Classical.byContradiction (fun hn => by have := x_mono T (Nat.le_of_not_lt hn); omega)

end TriChain

/-! ## Contar las cláusulas a la izquierda -/

/-- Contar con `filter` un predicado que baja: es el umbral. -/
theorem filt_thr (Q : Nat → Bool) (hd : ∀ i j, i ≤ j → Q j = true → Q i = true) :
    ∀ m j, j < m → (Q j = true ↔ j < ((List.range m).filter Q).length) := by
  intro m
  induction m with
  | zero => intro j h; omega
  | succ m ih =>
    intro j hj
    have hle : ((List.range m).filter Q).length ≤ m := by
      have := List.length_filter_le Q (List.range m); simpa using this
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hq : Q m = true
    · have all : ∀ i, i < m → Q i = true := fun i hi => hd i m (Nat.le_of_lt hi) hq
      have heq : ((List.range m).filter Q).length = m := by
        have : ∀ i, i < m → i < ((List.range m).filter Q).length := fun i hi => (ih i hi).mp (all i hi)
        by_cases hm : m = 0
        · subst hm; simp
        · have := this (m - 1) (by omega); omega
      simp only [List.filter_cons, hq, if_true, List.filter_nil, List.length_singleton, heq]
      constructor
      · intro _; omega
      · intro _
        by_cases e : j = m
        · subst e; exact hq
        · exact all j (by omega)
    · simp only [List.filter_cons, Bool.not_eq_true] at hq ⊢
      simp only [hq, Bool.false_eq_true, if_false, List.filter_nil, List.length_nil, Nat.add_zero]
      by_cases e : j = m
      · subst e; constructor
        · intro h; rw [h] at hq; cases hq
        · intro h; omega
      · exact ih j (by omega)

/-- Las cláusulas `0 … m-1` que quedan enteras a la izquierda de `z`. -/
def loC (m : Nat) (x : Nat → Nat) (z : Nat) : Nat := ((List.range m).filter (fun j => decide (x j + 2 < z))).length

/-- Las que empiezan antes de `z`, menos uno: la última que la contiene. -/
def hiC (m : Nat) (x : Nat → Nat) (z : Nat) : Nat := ((List.range m).filter (fun j => decide (x j ≤ z))).length - 1

section Units

variable {φ : Cnf} {x : Nat → Nat}

theorem lo_iff (T : TriChain φ x) (m : Nat) {z j : Nat} (hj : j < m) : x j + 2 < z ↔ j < loC m x z := by
  have := filt_thr (fun j => decide (x j + 2 < z)) (fun i j hij h => by
    simp only [decide_eq_true_eq] at h ⊢; have := T.x_mono hij; omega) m j hj
  simp only [decide_eq_true_eq] at this
  exact this

theorem hi_iff (T : TriChain φ x) (m : Nat) {z j : Nat} (hj : j < m) : x j ≤ z ↔ j < hiC m x z + 1 := by
  have := filt_thr (fun j => decide (x j ≤ z)) (fun i j hij h => by
    simp only [decide_eq_true_eq] at h ⊢; have := T.x_mono hij; omega) m j hj
  simp only [decide_eq_true_eq] at this
  unfold hiC
  have hpos : x 0 ≤ z → 0 < ((List.range m).filter (fun j => decide (x j ≤ z))).length := fun h0 => by
    have := (filt_thr (fun j => decide (x j ≤ z)) (fun i j hij h => by
      simp only [decide_eq_true_eq] at h ⊢; have := T.x_mono hij; omega) m 0 (by omega)).mp (by simpa using h0)
    exact this
  have hz : x 0 ≤ z := by rw [T.x0]; omega
  have hp := hpos hz
  constructor
  · intro h; have := this.mp h; omega
  · intro h; exact this.mpr (by omega)

theorem lo_le (m : Nat) (z : Nat) : loC m x z ≤ m := by
  unfold loC; have := List.length_filter_le (fun j => decide (x j + 2 < z)) (List.range m); simpa using this

theorem hi_lt {m : Nat} (hm : 1 ≤ m) (z : Nat) : hiC m x z < m := by
  unfold hiC; have := List.length_filter_le (fun j => decide (x j ≤ z)) (List.range m); simp at this; omega

/-- **Vivir en la unidad `p`** es estar en la cláusula `p`. -/
theorem inU_iff (T : TriChain φ x) {m p z : Nat} (hp : p < m) :
    InU (loC m x) (hiC m x) p z ↔ x p ≤ z ∧ z ≤ x p + 2 := by
  unfold InU
  have a := lo_iff T m (z := z) hp
  have b := hi_iff T m (z := z) hp
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨b.mpr (by omega), Classical.byContradiction (fun h => by have := a.mp (by omega); omega)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Classical.byContradiction (fun h => by have := a.mpr (by omega); omega), by have := b.mp h1; omega⟩

/-- **El corte `c`** son las variables de `x (c+1)` a `x c + 2`. -/
theorem cut_iff (T : TriChain φ x) {m c z : Nat} (hc : c + 1 < m) :
    (loC m x z ≤ c ∧ c + 1 ≤ hiC m x z) ↔ x (c + 1) ≤ z ∧ z ≤ x c + 2 := by
  have a := lo_iff T m (z := z) (j := c) (by omega)
  have b := hi_iff T m (z := z) hc
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨b.mpr (by omega), Classical.byContradiction (fun h => by have := a.mp (by omega); omega)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Classical.byContradiction (fun h => by have := a.mpr (by omega); omega), by have := b.mp h1; omega⟩

end Units

/-! ## Las lecturas del prefijo -/

section Reads

variable {φ : Cnf} {x : Nat → Nat} {k : Nat}

theorem pre_len (hk : k < φ.clauses.length) : (prefixCnf φ (k + 1)).clauses.length = k + 1 := by
  simp only [prefixCnf, List.length_take]; omega

theorem pre_get (T : TriChain φ x) (hk : k < φ.clauses.length) {j : Nat} {c : Clause}
    (h : (prefixCnf φ (k + 1)).clauses[j]? = some c) :
    j ≤ k ∧ c.l1.v = x j ∧ c.l2.v = x j + 1 ∧ c.l3.v = x j + 2 := by
  have hj : j < k + 1 := by
    by_cases hj : j < k + 1
    · exact hj
    · rw [List.getElem?_eq_none (by rw [pre_len hk]; omega)] at h; cases h
  rw [prefix_getElem? hj] at h
  exact ⟨by omega, T.cl j c h⟩

/-- La cláusula `j` del prefijo existe. -/
theorem pre_some (hk : k < φ.clauses.length) {j : Nat} (hj : j ≤ k) :
    ∃ c, (prefixCnf φ (k + 1)).clauses[j]? = some c := by
  rw [prefix_getElem? (by omega), List.getElem?_eq_getElem (by omega)]
  exact ⟨_, rfl⟩

theorem litAt_v (c : Clause) {p : Nat} (hp : p < 3) {a : Nat} (h1 : c.l1.v = a) (h2 : c.l2.v = a + 1)
    (h3 : c.l3.v = a + 2) : (litAt c p).v = a + p := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- **Lo que lee un paso del prefijo**: su variable, o un literal de una cláusula `j ≤ k`. -/
theorem sv_cases (T : TriChain φ x) (hk : k < φ.clauses.length) {s : Int} {z : Nat}
    (h : stepVar (prefixCnf φ (k + 1)) s = some z) :
    (z < φ.nVars ∧ (s = varStep z ∨ s = negStep z)) ∨
      ∃ j p, j ≤ k ∧ p < 3 ∧ s = clauseStep (prefixCnf φ (k + 1)) j p ∧ z = x j + p := by
  rcases step_cases (prefixCnf φ (k + 1)) s with h0 | ⟨v, hv, e⟩ | ⟨v, hv, e⟩ | e | ⟨j, p, c, hp, _, hj, e⟩ | e
  · simp only [stepVar, if_pos h0] at h; cases h
  · rw [e, stepVar_var hv] at h
    cases h
    exact Or.inl ⟨hv, Or.inl e⟩
  · rw [e, GPathB.stepVar_neg hv] at h
    cases h
    exact Or.inl ⟨hv, Or.inr e⟩
  · exfalso
    have h0 : ¬ s ≤ 0 := by rw [e]; simp only [midFusion]; omega
    have h1 : ¬ s < midFusion (prefixCnf φ (k + 1)) := by rw [e]; omega
    simp only [stepVar, if_neg h0, if_neg h1, if_pos e] at h; cases h
  · rw [e, stepVar_clause hj p hp] at h
    cases h
    obtain ⟨hjk, e1, e2, e3⟩ := pre_get T hk hj
    exact Or.inr ⟨j, p, hjk, hp, e, litAt_v c hp e1 e2 e3⟩
  · exfalso
    have h0 : ¬ s ≤ 0 := by simp only [fusionTop] at e; omega
    have h1 : ¬ s < midFusion (prefixCnf φ (k + 1)) := by simp only [fusionTop, midFusion] at e ⊢; omega
    have h2 : ¬ s = midFusion (prefixCnf φ (k + 1)) := by simp only [fusionTop, midFusion] at e ⊢; omega
    simp only [stepVar, if_neg h0, if_neg h1, if_neg h2, if_pos e] at h; cases h

theorem sv_cl (T : TriChain φ x) (hk : k < φ.clauses.length) {j p : Nat} (hj : j ≤ k) (hp : p < 3) :
    stepVar (prefixCnf φ (k + 1)) (clauseStep (prefixCnf φ (k + 1)) j p) = some (x j + p) := by
  obtain ⟨c, hc⟩ := pre_some hk hj
  obtain ⟨_, e1, e2, e3⟩ := pre_get T hk hc
  rw [stepVar_clause hc p hp, litAt_v c hp e1 e2 e3]

/-- Leer con el paso `s'` de la ventana de `s`. -/
theorem reads_at {ψ : Cnf} {s s' : Int} {z : Nat} (h1 : s' ≤ s) (h2 : s - 2 ≤ s') (h3 : 1 ≤ s')
    (h : stepVar ψ s' = some z) : ReadsAt ψ s z := by
  refine ⟨s', ?_, h⟩
  rcases (by omega : s' = s ∨ s' = s - 1 ∨ s' = s - 2) with e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl ⟨by omega, e⟩)
  · exact Or.inr (Or.inr ⟨by omega, e⟩)

/-- **Lecturas locales**: una ventana que lee `z` de dentro lee `z - 1` o `z + 1`. -/
theorem reads_pair (T : TriChain φ x) (hk : k < φ.clauses.length) {s : Int} {z : Nat}
    (h : ReadsAt (prefixCnf φ (k + 1)) s z) (h1 : 1 ≤ z) (h2 : z + 1 ≤ x k + 2) :
    ReadsAt (prefixCnf φ (k + 1)) s (z - 1) ∨ ReadsAt (prefixCnf φ (k + 1)) s (z + 1) := by
  have hN : x k + 3 ≤ φ.nVars := by
    rw [T.nv]; have := T.x_mono (i := k) (j := φ.clauses.length - 1) (by omega); omega
  have hzN : z + 1 < (prefixCnf φ (k + 1)).nVars := by show z + 1 < φ.nVars; omega
  have hzN' : z - 1 < (prefixCnf φ (k + 1)).nVars := by show z - 1 < φ.nVars; omega
  have vz1 := stepVar_var (φ := prefixCnf φ (k + 1)) hzN
  have nz1 := GPathB.stepVar_neg (φ := prefixCnf φ (k + 1)) hzN
  have nzm := GPathB.stepVar_neg (φ := prefixCnf φ (k + 1)) hzN'
  obtain ⟨s', hw, hs'⟩ := h
  have hsw : s' ≤ s ∧ s - 2 ≤ s' := by
    rcases hw with e | ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  rcases sv_cases T hk hs' with ⟨_, e | e⟩ | ⟨j, p, hj, hp, e, ez⟩
  · -- `s' = 2z + 1`: la ventana es `2z+1, 2z+2` (lee `z - 1`) o `2z+3` (lee `z + 1`)
    simp only [varStep] at e
    by_cases hs : s ≤ 2 * (z : Int) + 2
    · refine Or.inl (reads_at (s' := negStep (z - 1)) (by simp only [negStep]; omega) (by simp only [negStep]; omega)
        (by simp only [negStep]; omega) nzm)
    · refine Or.inr (reads_at (s' := varStep (z + 1)) (by simp only [varStep]; omega) (by simp only [varStep]; omega)
        (by simp only [varStep]; omega) vz1)
  · simp only [negStep] at e
    by_cases hs : s ≤ 2 * (z : Int) + 2
    · refine Or.inl (reads_at (s' := negStep (z - 1)) (by simp only [negStep]; omega) (by simp only [negStep]; omega)
        (by simp only [negStep]; omega) nzm)
    by_cases hs3 : s = 2 * (z : Int) + 3
    · refine Or.inr (reads_at (s' := varStep (z + 1)) (by simp only [varStep]; omega) (by simp only [varStep]; omega)
        (by simp only [varStep]; omega) vz1)
    · refine Or.inr (reads_at (s' := negStep (z + 1)) (by simp only [negStep]; omega) (by simp only [negStep]; omega)
        (by simp only [negStep]; omega) nz1)
  · -- un literal de la cláusula `j`
    have cs : ∀ a b : Nat, clauseStep (prefixCnf φ (k + 1)) a b = 2 * (φ.nVars : Int) + 2 + 3 * (a : Int) + (b : Int) :=
      fun _ _ => rfl
    rw [cs] at e
    have rd : ∀ {a b : Nat}, a ≤ k → b < 3 → 2 * (φ.nVars : Int) + 2 + 3 * (a : Int) + (b : Int) ≤ s →
        s - 2 ≤ 2 * (φ.nVars : Int) + 2 + 3 * (a : Int) + (b : Int) → ReadsAt (prefixCnf φ (k + 1)) s (x a + b) :=
      fun {a} {b} ha hb l1 l2 => reads_at (s' := clauseStep (prefixCnf φ (k + 1)) a b) (by rw [cs]; omega)
        (by rw [cs]; omega) (by rw [cs]; omega) (sv_cl T hk ha hb)
    have jm := T.jmp j
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl
    · -- `z = x j`
      by_cases hs : s = 2 * (φ.nVars : Int) + 2 + 3 * (j : Int)
      · -- la ventana lee `x (j-1) + 1` y `x (j-1) + 2`
        have hj0 : 1 ≤ j := Classical.byContradiction (fun hn => by
          have : j = 0 := by omega
          subst this; rw [T.x0] at ez; omega)
        have jm' := T.jmp (j - 1)
        rw [show j - 1 + 1 = j by omega] at jm'
        by_cases hjump : x j = x (j - 1) + 1
        · refine Or.inr ?_
          have := rd (a := j - 1) (b := 2) (by omega) (by omega) (by omega) (by omega)
          rwa [show x (j - 1) + 2 = z + 1 by omega] at this
        · refine Or.inl ?_
          have := rd (a := j - 1) (b := 1) (by omega) (by omega) (by omega) (by omega)
          rwa [show x (j - 1) + 1 = z - 1 by omega] at this
      · refine Or.inr ?_
        have := rd (a := j) (b := 1) hj (by omega) (by omega) (by omega)
        rwa [show x j + 1 = z + 1 by omega] at this
    · -- `z = x j + 1`
      by_cases hs : s = 2 * (φ.nVars : Int) + 2 + 3 * (j : Int) + 1
      · refine Or.inl ?_
        have := rd (a := j) (b := 0) hj (by omega) (by omega) (by omega)
        rwa [show x j + 0 = z - 1 by omega] at this
      · refine Or.inr ?_
        have := rd (a := j) (b := 2) hj (by omega) (by omega) (by omega)
        rwa [show x j + 2 = z + 1 by omega] at this
    · -- `z = x j + 2`
      by_cases hs : s ≤ 2 * (φ.nVars : Int) + 2 + 3 * (j : Int) + 3
      · refine Or.inl ?_
        have := rd (a := j) (b := 1) hj (by omega) (by omega) (by omega)
        rwa [show x j + 1 = z - 1 by omega] at this
      · -- la ventana lee `x (j+1)` y `x (j+1) + 1`
        have hjk : j + 1 ≤ k := Classical.byContradiction (fun hn => by
          have : j = k := by omega
          subst this; omega)
        by_cases hjump : x (j + 1) = x j + 1
        · refine Or.inl ?_
          have := rd (a := j + 1) (b := 0) hjk (by omega) (by push_cast; omega) (by push_cast; omega)
          rwa [show x (j + 1) + 0 = z - 1 by omega] at this
        · refine Or.inr ?_
          have := rd (a := j + 1) (b := 1) hjk (by omega) (by push_cast; omega) (by push_cast; omega)
          rwa [show x (j + 1) + 1 = z + 1 by omega] at this

/-- **El par**: dentro de la cadena, todo par `{w, w + 1}` contiene un corte entero `c` (`x (c+1) … x c + 2`). -/
theorem pair_cut (T : TriChain φ x) {w : Nat} (h1 : 1 ≤ w) (h2 : w + 1 ≤ x k) :
    ∃ c, c + 1 ≤ k ∧ w ≤ x (c + 1) ∧ x c + 2 ≤ w + 1 := by
  have hl := hi_iff T (k + 1) (z := w) (j := hiC (k + 1) x w) (by have := hi_lt (m := k + 1) (x := x) (by omega) w; omega)
  have hxh : x (hiC (k + 1) x w) ≤ w := hl.mpr (by omega)
  have hhk : hiC (k + 1) x w < k := by
    have hk' := hi_iff T (k + 1) (z := w) (j := k) (by omega)
    have := hi_lt (m := k + 1) (x := x) (by omega) w
    by_cases e : hiC (k + 1) x w = k
    · rw [e] at hxh; omega
    · omega
  have hnext : w < x (hiC (k + 1) x w + 1) := by
    have := hi_iff T (k + 1) (z := w) (j := hiC (k + 1) x w + 1) (by omega)
    exact Classical.byContradiction (fun hn => by have := this.mp (by omega); omega)
  generalize hiC (k + 1) x w = h at hxh hhk hl hnext
  have jh := T.jmp h
  by_cases ec : w + 1 = x (h + 1) ∧ x h + 2 = w + 1
  · exact ⟨h, by omega, by omega, by omega⟩
  · -- entonces `x h = w`, y el corte es `h - 1`
    have hxw : x h = w := by omega
    have hh : 1 ≤ h := Classical.byContradiction (fun hn => by
      have : h = 0 := by omega
      subst this; rw [T.x0] at hxw; omega)
    have jm := T.jmp (h - 1)
    rw [show h - 1 + 1 = h by omega] at jm
    exact ⟨h - 1, by omega, by rw [show h - 1 + 1 = h by omega]; omega, by omega⟩

end Reads

end AbsSatBingo.Model
