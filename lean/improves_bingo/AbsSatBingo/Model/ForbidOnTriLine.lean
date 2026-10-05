-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnTriLine.lean
import AbsSatBingo.Model.ForbidOnTriChain

/-!
# Las líneas de una cadena de tríos: `LineOK` sin hipótesis

La línea de la cláusula `k` y una variable `v` suya, en el prefijo de `k + 1` cláusulas (`pathN_pre`).

* **El testigo** (`jwI`, `lamI`): el último literal de la cláusula anterior, `jw = k - 1`; si el corte `k - 1` es solo
  `{v}`, el de dos atrás, `jw = k - 2`. Lee la cláusula `jw` entera, y en los cortes `jw - 1 … k - 1` todo es `v` o lo
  lee (`glue_jw`).
* **La cola** `f`: uno más que el último corte leído entero a la izquierda de `v` (`max_below`). Solo se usa
  **`hmax`**: ningún corte de `f` a `lo v - 1` está leído entero.
* **Las piezas**: las unidades `jw … k` son piezas de una unidad (`stP_self`); las de antes de `jw`, la región de la
  izquierda.
  * **La región de la izquierda solo lee `x f` y `x f + 1`** (`left_reads`): si leyera `z ≥ x f + 2`, su ventana leería
    un par con `z` (`reads_pair`), el par contiene un corte entero (`pair_cut`), y ese corte estaría entre `f` y
    `lo v - 1`.
  * **Una pieza de una unidad `q` no lee tres variables**: si `v` está en la cláusula `q` solo le quedan dos; si no,
    leería entero su corte `q`, también entre `f` y `lo v - 1`.

Resultado: **`lineOK_tri`** para todo trío.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {x : Nat → Nat} {k : Nat}

/-- El último por debajo de `A` que cumple `Q`. -/
theorem max_below (Q : Nat → Prop) : ∀ A, (∃ c, c < A ∧ Q c) → ∃ c, c < A ∧ Q c ∧ ∀ c', c < c' → c' < A → ¬ Q c' := by
  intro A
  induction A with
  | zero => rintro ⟨c, h, _⟩; omega
  | succ A ih =>
    intro hex
    by_cases hA : Q A
    · exact ⟨A, by omega, hA, fun c' h1 h2 => absurd h2 (by omega)⟩
    · obtain ⟨c0, h0, q0⟩ := hex
      have hc0 : c0 < A := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h0) with h | h
        · exact h
        · subst h; exact absurd q0 hA
      obtain ⟨c, hc, qc, hm⟩ := ih ⟨c0, hc0, q0⟩
      refine ⟨c, by omega, qc, fun c' h1 h2 => ?_⟩
      by_cases e : c' = A
      · subst e; exact hA
      · exact hm c' h1 (by omega)

/-- `stP` no pasa de su unidad. -/
theorem stP_le_self {f : Nat} {G : Nat → Prop} : ∀ p, f ≤ p → stP f G p ≤ p
  | 0, _ => by simp only [stP]; omega
  | p + 1, h => by
    classical
    by_cases h1 : p + 1 ≤ f
    · rw [stP_le h1]; omega
    by_cases hg : G p
    · rw [stP_glue (by omega) hg]; omega
    · rw [stP_no (by omega) hg]; have := stP_le_self (f := f) (G := G) p (by omega); omega

/-- **El camino de unidades del prefijo.** -/
theorem pathN_pre (T : TriChain φ x) (hk : k < φ.clauses.length) :
    PathN (prefixCnf φ (k + 1)) (k + 1) (loC (k + 1) x) (hiC (k + 1) x) := by
  refine ⟨by omega, fun z hz => ?_, fun c hc => ?_⟩
  · have a := lo_iff T (k + 1) (z := z) (j := loC (k + 1) x z) hz
    have hxz : x (loC (k + 1) x z) ≤ z := by
      by_cases h0 : loC (k + 1) x z = 0
      · rw [h0, T.x0]; omega
      · have b := lo_iff T (k + 1) (z := z) (j := loC (k + 1) x z - 1) (by omega)
        have := (T.jmp (loC (k + 1) x z - 1)).2
        rw [show loC (k + 1) x z - 1 + 1 = loC (k + 1) x z by omega] at this
        have := b.mpr (by omega); omega
    have := (hi_iff T (k + 1) (z := z) hz).mp hxz
    exact ⟨by omega, hi_lt (by omega) z⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    obtain ⟨hjk, e1, e2, e3⟩ := pre_get T hk hj
    have u : ∀ {z}, x j ≤ z → z ≤ x j + 2 → InU (loC (k + 1) x) (hiC (k + 1) x) j z := fun h1 h2 =>
      (inU_iff T (by omega)).mpr ⟨h1, h2⟩
    exact Or.inr ⟨j, by omega, u (by omega) (by omega), u (by omega) (by omega), u (by omega) (by omega)⟩

/-- El corte `k - 1` es solo `v`. -/
def SglV (x : Nat → Nat) (k v : Nat) : Prop := 2 ≤ k ∧ v = x k ∧ x k = x (k - 1) + 2

open Classical in
/-- La cláusula del testigo. -/
noncomputable def jwI (x : Nat → Nat) (k v : Nat) : Nat := if SglV x k v then k - 2 else k - 1

open Classical in
/-- **El testigo de la línea**: el último literal de la cláusula `jw` (si `k = 0`, el paso 0, que no lee nada). -/
noncomputable def lamI (φ : Cnf) (x : Nat → Nat) (k v : Nat) : Int :=
  if k = 0 then 0 else clauseStep (prefixCnf φ (k + 1)) (jwI x k v) 2

theorem jwI_le {k v : Nat} : jwI x k v + 1 ≤ k ∨ k = 0 := by
  classical
  unfold jwI SglV; split <;> omega

/-- El testigo lee la cláusula `jw`. -/
theorem lam_reads (T : TriChain φ x) (hk : k < φ.clauses.length) {v : Nat} (hk1 : 1 ≤ k) {z : Nat}
    (h1 : x (jwI x k v) ≤ z) (h2 : z ≤ x (jwI x k v) + 2) : ReadsAt (prefixCnf φ (k + 1)) (lamI φ x k v) z := by
  have hj : jwI x k v ≤ k := by have := jwI_le (x := x) (k := k) (v := v); omega
  have e : lamI φ x k v = clauseStep (prefixCnf φ (k + 1)) (jwI x k v) 2 := by unfold lamI; rw [if_neg (by omega)]
  have := sv_cl T hk hj (p := z - x (jwI x k v)) (by omega)
  rw [show x (jwI x k v) + (z - x (jwI x k v)) = z by omega] at this
  rw [e]
  exact reads_at (s' := clauseStep (prefixCnf φ (k + 1)) (jwI x k v) (z - x (jwI x k v)))
    (by simp only [clauseStep]; omega) (by simp only [clauseStep]; omega) (by simp only [clauseStep]; omega) this

/-- **En los cortes `jw - 1 … k - 1`, todo es `v` o lo lee el testigo.** -/
theorem glue_jw (T : TriChain φ x) (hk : k < φ.clauses.length) {v : Nat}
    {c : Nat} (hc1 : jwI x k v ≤ c + 1) (hc2 : c + 1 ≤ k) :
    GlueAt (loC (k + 1) x) (hiC (k + 1) x) (XW (prefixCnf φ (k + 1)) (lamI φ x k v) v) v c := by
  classical
  intro z h1 h2
  obtain ⟨a, b⟩ := (cut_iff T (m := k + 1) (by omega)).mp ⟨h1, h2⟩
  by_cases hzv : z = v
  · exact Or.inl hzv
  have hin : x (jwI x k v) ≤ z ∧ z ≤ x (jwI x k v) + 2 := by
    by_cases hs : SglV x k v
    · have e : jwI x k v = k - 2 := by unfold jwI; rw [if_pos hs]
      rw [e] at hc1 ⊢
      unfold SglV at hs
      by_cases ec : c + 1 = k
      · exfalso
        rw [show c = k - 1 by omega] at b
        rw [show c + 1 = k by omega] at a
        omega
      · have := T.x_mono (i := k - 2) (j := c + 1) (by omega)
        rcases (by omega : c = k - 3 ∨ c = k - 2) with e | e
        · have := T.x_mono (i := k - 3) (j := k - 2) (by omega); rw [e] at b; omega
        · rw [e] at b; omega
    · have e : jwI x k v = k - 1 := by unfold jwI; rw [if_neg hs]
      rw [e] at hc1 ⊢
      have := T.x_mono (i := k - 1) (j := c + 1) (by omega)
      rcases (by omega : c = k - 2 ∨ c = k - 1) with e | e
      · have := T.x_mono (i := c) (j := k - 1) (by omega); omega
      · rw [e] at b; omega
  exact Or.inr ⟨lam_reads T hk (by omega) hin.1 hin.2, hzv⟩

/-- **`LineOK` en toda línea de una cadena de tríos**, para todo trío. -/
theorem lineOK_tri (T : TriChain φ x) (hk : k < φ.clauses.length) {v : Nat} (hv1 : x k ≤ v) (hv2 : v ≤ x k + 2)
    (i j l : Int) :
    LineOK (prefixCnf φ (k + 1)) (k + 1) (loC (k + 1) x) (hiC (k + 1) x) v (lamI φ x k v) i j l := by
  classical
  let G := GlueAt (loC (k + 1) x) (hiC (k + 1) x) (XW (prefixCnf φ (k + 1)) (lamI φ x k v) v) v
  let CR := fun c => CutRead (prefixCnf φ (k + 1)) (loC (k + 1) x) (hiC (k + 1) x) i j l c
  let A := loC (k + 1) x v
  have hA : ∀ c, c < k + 1 → (c < A ↔ x c + 2 < v) := fun c hc => (lo_iff T (k + 1) (z := v) hc).symm
  -- la cola
  obtain ⟨f, hf, hfA, hmax⟩ : ∃ f, (f = 0 ∨ CR (f - 1)) ∧ f ≤ A ∧ ∀ c, f ≤ c → c < A → ¬ CR c := by
    by_cases hex : ∃ c, c < A ∧ CR c
    · obtain ⟨c, hc, qc, hm⟩ := max_below CR A hex
      exact ⟨c + 1, Or.inr (by rw [show c + 1 - 1 = c by omega]; exact qc), by omega,
        fun c' h1 h2 => hm c' (by omega) h2⟩
    · exact ⟨0, Or.inl rfl, Nat.zero_le _, fun c _ hc qc => hex ⟨c, hc, qc⟩⟩
  refine ⟨f, hf, hfA, fun q hb => ?_⟩
  obtain ⟨z1, z2, z3, m1, m2, m3, d12, d13, d23, r1, r2, r3⟩ := hb
  have w1 : InW (prefixCnf φ (k + 1)) i j l z1 := inW_of_reads (Or.inr (Or.inr rfl)) r1
  have w2 : InW (prefixCnf φ (k + 1)) i j l z2 := inW_of_reads (Or.inr (Or.inl rfl)) r2
  have w3 : InW (prefixCnf φ (k + 1)) i j l z3 := inW_of_reads (Or.inl rfl) r3
  obtain ⟨_, p1, f1, k1, s1, u1⟩ := m1
  obtain ⟨_, p2, f2, k2, s2, u2⟩ := m2
  obtain ⟨_, p3, f3, k3, s3, u3⟩ := m3
  have v1 := (inU_iff T k1).mp u1
  have v2 := (inU_iff T k2).mp u2
  have v3 := (inU_iff T k3).mp u3
  have hjw := jwI_le (x := x) (k := k) (v := v)
  -- las unidades desde `jw` son piezas de una unidad
  have self : ∀ p, f ≤ p → p < k + 1 → jwI x k v ≤ p → stP f G p = p := by
    intro p h1 h2 h3
    by_cases e : p = f
    · subst e; exact stP_le (Nat.le_refl _)
    · have g := glue_jw T hk (v := v) (c := p - 1) (by omega) (by omega)
      have := stP_glue (G := G) (f := f) (p := p - 1) (by omega) g
      rwa [show p - 1 + 1 = p by omega] at this
  have below : ∀ p, f ≤ p → p < jwI x k v → stP f G p < jwI x k v := fun p h1 h2 => by
    have := stP_le_self (f := f) (G := G) p h1; omega
  -- una lectura de la región de la izquierda está en `x f`, `x f + 1`
  have left : ∀ {z p : Nat} {s : Int}, (s = i ∨ s = j ∨ s = l) → ReadsAt (prefixCnf φ (k + 1)) s z → f ≤ p →
      p < jwI x k v → x p ≤ z → z ≤ x p + 2 → z ≤ x f + 1 := by
    intro z p s hs hr hfp hpj hz1 hz2
    refine Classical.byContradiction (fun hz => ?_)
    have hk2 : 2 ≤ k := by have h := hpj; unfold jwI at h; split at h <;> omega
    -- `z + 1 ≤ x k`
    have hjk : x (jwI x k v - 1) + 3 ≤ x k := by
      unfold jwI
      split
      · rename_i hs
        have : 3 ≤ k := by have h := hpj; unfold jwI at h; rw [if_pos hs] at h; omega
        have := T.no11 (k - 3); have := T.x_mono (i := k - 1) (j := k) (by omega)
        rw [show k - 3 + 2 = k - 1 by omega] at *; rw [show k - 2 - 1 = k - 3 by omega]; omega
      · have := T.no11 (k - 2); rw [show k - 2 + 2 = k by omega] at this; rw [show k - 1 - 1 = k - 2 by omega]
        exact this
    have hpm := T.x_mono (i := p) (j := jwI x k v - 1) (by omega)
    have hxf := T.x_mono (i := f) (j := p) hfp
    rcases reads_pair T hk hr (by omega) (by omega) with hr' | hr'
    · -- el par `z - 1, z`
      obtain ⟨c, hck, hc1, hc2⟩ := pair_cut T (k := k) (w := z - 1) (by omega) (by omega)
      have cr : CR c := fun y h1 h2 => by
        obtain ⟨a, b⟩ := (cut_iff T (m := k + 1) (by omega)).mp ⟨h1, h2⟩
        rcases (by omega : y = z - 1 ∨ y = z) with e | e
        · rw [e]; exact inW_of_reads hs hr'
        · rw [e]; exact inW_of_reads hs hr
      have hfc : f ≤ c := by have := T.lt_of_x (i := f) (j := c + 1) (by omega); omega
      refine hmax c hfc ((hA c (by omega)).mpr ?_) cr
      by_cases hs' : SglV x k v
      · have e : jwI x k v = k - 2 := by unfold jwI; rw [if_pos hs']
        rw [e] at hpm
        unfold SglV at hs'
        have := T.no11 (k - 3); rw [show k - 3 + 2 = k - 1 by omega, show k - 2 - 1 = k - 3 by omega] at *
        have := (T.jmp (k - 1)).1; rw [show k - 1 + 1 = k by omega] at this
        omega
      · have e : jwI x k v = k - 1 := by unfold jwI; rw [if_neg hs']
        rw [e] at hpm
        have := T.no11 (k - 2); rw [show k - 2 + 2 = k by omega, show k - 1 - 1 = k - 2 by omega] at *
        omega
    · -- el par `z, z + 1`
      obtain ⟨c, hck, hc1, hc2⟩ := pair_cut T (k := k) (w := z) (by omega) (by omega)
      have cr : CR c := fun y h1 h2 => by
        obtain ⟨a, b⟩ := (cut_iff T (m := k + 1) (by omega)).mp ⟨h1, h2⟩
        rcases (by omega : y = z ∨ y = z + 1) with e | e
        · rw [e]; exact inW_of_reads hs hr
        · rw [e]; exact inW_of_reads hs hr'
      have hfc : f ≤ c := by have := T.lt_of_x (i := f) (j := c + 1) (by omega); omega
      refine hmax c hfc ((hA c (by omega)).mpr ?_) cr
      by_cases hs' : SglV x k v
      · have e : jwI x k v = k - 2 := by unfold jwI; rw [if_pos hs']
        rw [e] at hpm
        unfold SglV at hs'
        have := T.no11 (k - 3); rw [show k - 3 + 2 = k - 1 by omega, show k - 2 - 1 = k - 3 by omega] at *
        have := (T.jmp (k - 1)).1; rw [show k - 1 + 1 = k by omega] at this
        omega
      · have e : jwI x k v = k - 1 := by unfold jwI; rw [if_neg hs']
        rw [e] at hpm
        have n2 := T.no11 (k - 2); rw [show k - 2 + 2 = k by omega, show k - 1 - 1 = k - 2 by omega] at *
        -- si `x c + 2 = v`, el corte `k - 1` sería solo `v`
        refine Classical.byContradiction (fun hv => hs' ?_)
        have hc : c = k - 1 := Classical.byContradiction (fun hne => by
          have := T.x_mono (i := c) (j := k - 2) (by omega); omega)
        subst hc
        have := (T.jmp (k - 1)).2; rw [show k - 1 + 1 = k by omega] at this
        refine ⟨hk2, by omega, by omega⟩
  by_cases hq : q < jwI x k v
  · -- la región de la izquierda
    have lt : ∀ {p}, f ≤ p → p < k + 1 → stP f G p = q → p < jwI x k v := fun {p} h1 h2 h3 =>
      Classical.byContradiction (fun hn => by rw [self p h1 h2 (by omega)] at h3; omega)
    have a1 := left (Or.inr (Or.inr rfl)) r1 f1 (lt f1 k1 s1) v1.1 v1.2
    have a2 := left (Or.inr (Or.inl rfl)) r2 f2 (lt f2 k2 s2) v2.1 v2.2
    have a3 := left (Or.inl rfl) r3 f3 (lt f3 k3 s3) v3.1 v3.2
    have := T.x_mono (i := f) (j := p1) f1
    have := T.x_mono (i := f) (j := p2) f2
    have := T.x_mono (i := f) (j := p3) f3
    omega
  · -- una pieza de una unidad
    have eq : ∀ {p}, f ≤ p → p < k + 1 → stP f G p = q → p = q := fun {p} h1 h2 h3 => by
      by_cases hp : p < jwI x k v
      · have := below p h1 hp; omega
      · rw [self p h1 h2 (by omega)] at h3; exact h3
    have e1 := eq f1 k1 s1
    have e2 := eq f2 k2 s2
    have e3 := eq f3 k3 s3
    rw [e1] at v1 f1 k1; rw [e2] at v2; rw [e3] at v3
    -- las tres variables de la cláusula `q`, sin `v`
    have hvq : x q + 2 < v := by
      rcases (by omega : v < x q ∨ x q + 2 < v ∨ (x q ≤ v ∧ v ≤ x q + 2)) with h | h | h
      · have := T.x_mono (i := q) (j := k) (by omega); omega
      · exact h
      · omega
    have hqk : q < k := Classical.byContradiction (fun hn => by
      have : q = k := by omega
      subst this; omega)
    have cr : CR q := fun y h1 h2 => by
      obtain ⟨a, b⟩ := (cut_iff T (m := k + 1) (by omega)).mp ⟨h1, h2⟩
      have := (T.jmp q).1
      rcases (by omega : y = z1 ∨ y = z2 ∨ y = z3) with e | e | e
      · rw [e]; exact w1
      · rw [e]; exact w2
      · rw [e]; exact w3
    exact hmax q f1 ((hA q k1).mpr hvq) cr

/-- Una cadena de tríos tiene sus variables en rango. -/
theorem bounded_tri (T : TriChain φ x) : Bounded φ := by
  intro c hc
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  have hjl : j < φ.clauses.length := by
    by_cases h : j < φ.clauses.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  obtain ⟨e1, e2, e3⟩ := T.cl j c hj
  have := T.x_mono (i := j) (j := φ.clauses.length - 1) (by omega)
  have hn := T.nv
  unfold Clause.Bounded
  rw [e1, e2, e3, hn]
  omega

open Driver Machine MachineOn in
/-- **Las líneas de la cláusula `k`**, en su prefijo. -/
theorem phantomAt_triLine (T : TriChain φ x) (hk : k < φ.clauses.length) {Tt : Int}
    (hT0 : clauseStep φ k 0 ≤ Tt) (hT2 : Tt ≤ clauseStep φ k 2) (hT : 1 ≤ Tt) :
    PhantomAt (prefixCnf φ (k + 1)) Tt := by
  have hb := bounded_tri T
  have hcj : φ.clauses[k]? = some (φ.clauses[k]'hk) := List.getElem?_eq_getElem _
  have hψj : (prefixCnf φ (k + 1)).clauses[k]? = some (φ.clauses[k]'hk) := (prefix_getElem? (by omega)).trans hcj
  refine phantomAt_of_lineLocal (bounded_prefix hb (k + 1)) hψj (by rw [clauseStep_prefix]; exact hT0)
    (by rw [clauseStep_prefix]; exact hT2) hT (fun {P0 P σ N v} hl hv hcv hσ0 hσN hTN => ?_)
  obtain ⟨e1, e2, e3⟩ := T.cl k _ hcj
  have hv12 : x k ≤ v ∧ v ≤ x k + 2 := by
    rcases hcv with e | e | e <;> rw [e] <;> omega
  have hlam0 : 0 ≤ lamI φ x k v := by
    unfold lamI; split
    · omega
    · simp only [clauseStep]; omega
  have hlamN : lamI φ x k v < N := by
    have hjw := jwI_le (x := x) (k := k) (v := v)
    unfold lamI; split
    · omega
    · simp only [clauseStep, prefixCnf] at hT0 ⊢; omega
  exact phantomFree_lineP hl (pathN_pre T hk) hv ⟨k, by omega, (inU_iff T (by omega)).mpr hv12⟩ hlam0 hlamN hσ0 hσN
    (fun i j l => lineOK_tri T hk hv12.1 hv12.2 i j l)

open Driver Machine MachineOn in
/-- **Toda cadena de tríos de anchura ≤ 2 cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_of_triChain (T : TriChain φ x) (Tt : Int) (hT : 1 ≤ Tt) : PhantomAt φ Tt := by
  have hb := bounded_tri T
  have cs : ∀ j p : Nat, clauseStep φ j p = 2 * (φ.nVars : Int) + 2 + 3 * (j : Int) + (p : Int) := fun _ _ => rfl
  have hm : midFusion φ = 2 * (φ.nVars : Int) + 1 := rfl
  have hft : fusionTop φ = 2 * (φ.nVars : Int) + 3 * (φ.clauses.length : Int) + 2 := by simp only [fusionTop]
  have hpos := T.pos
  by_cases hlow : Tt + 1 ≤ midFusion φ + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  rw [hm] at hlow
  by_cases hin : Tt ≤ clauseStep φ (φ.clauses.length - 1) 2
  · rw [cs] at hin
    have hj : ((Tt - (2 * (φ.nVars : Int) + 2)) / 3).toNat < φ.clauses.length := by omega
    have h0 : clauseStep φ ((Tt - (2 * (φ.nVars : Int) + 2)) / 3).toNat 0 ≤ Tt := by rw [cs]; omega
    have h2 : Tt ≤ clauseStep φ ((Tt - (2 * (φ.nVars : Int) + 2)) / 3).toNat 2 := by rw [cs]; omega
    refine phantomAt_of_prefix hb (j := ((Tt - (2 * (φ.nVars : Int) + 2)) / 3).toNat + 1) ?_
      (phantomAt_triLine T hj h0 h2 hT)
    rw [cs] at h2
    simp only [fusionTop, prefixCnf, List.length_take]
    omega
  · rw [cs] at hin
    intro k d hk hd
    have hds : d.step = Tt := by
      have := sonsOfMap_step φ k d hd
      have hks := mapNodes_step φ (Tt - 1) k hk
      omega
    have hft' : fusionTop φ ≤ d.step := by rw [hds, hft]; omega
    refine ⟨fun r hr => by rw [reqOf_above φ d hft'] at hr; exact absurd hr List.not_mem_nil, ?_⟩
    have hsv : stepVar φ Tt = none := by
      have h1 : ¬ Tt ≤ 0 := by omega
      have h2 : ¬ Tt < midFusion φ := by rw [hm]; omega
      have h3 : ¬ Tt = midFusion φ := by rw [hm]; omega
      have h4 : fusionTop φ ≤ Tt := by rw [hft]; omega
      simp only [stepVar, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    exact phantomFree_none (locPair_up hb Tt k d) hsv (by omega) (show Tt < Tt + 1 by omega)

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf} {x : Nat → Nat}

/-- **La máquina `:on` es exacta en toda cadena de tríos de anchura ≤ 2**, de cualquier longitud. -/
theorem machineExact_of_triChain (T : TriChain φ x) : MachineExact φ :=
  (machineExact_iff (bounded_tri T)).2 (phantomAt_of_triChain T)

/-- **La espina `:on` decide toda cadena de tríos de anchura ≤ 2.** -/
theorem spineVerdictOn_iff_of_triChain (T : TriChain φ x) : SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree (bounded_tri T) (phantomAt_of_triChain T)

end MachineOn

end AbsSatBingo.Model

/-! ## La instancia: `chain5w2_order` -/

namespace AbsSatBingo.Model

open AbsSatBin.Cnf

/-- **`chain5w2_order`** (`scripts/cnf/wide/chain5w2_order.cnf`, variables desde 0): cinco bloques, los tres de en medio
con dos variables de dentro; las cláusulas son los tríos que empiezan en `0, 2, 3, 5, 6, 8, 9, 11`. -/
def chain5W : Cnf :=
  ⟨14, [⟨⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩⟩, ⟨⟨2, false⟩, ⟨3, true⟩, ⟨4, true⟩⟩, ⟨⟨3, true⟩, ⟨4, true⟩, ⟨5, false⟩⟩,
    ⟨⟨5, false⟩, ⟨6, false⟩, ⟨7, false⟩⟩, ⟨⟨6, true⟩, ⟨7, true⟩, ⟨8, true⟩⟩, ⟨⟨8, true⟩, ⟨9, true⟩, ⟨10, true⟩⟩,
    ⟨⟨9, false⟩, ⟨10, false⟩, ⟨11, false⟩⟩, ⟨⟨11, false⟩, ⟨12, true⟩, ⟨13, true⟩⟩]⟩

/-- Dónde empieza cada trío (y, más allá, de dos en dos). -/
def x5W (j : Nat) : Nat := if j < 8 then [0, 2, 3, 5, 6, 8, 9, 11].getD j 0 else 2 * j - 3

theorem triChain_chain5W : TriChain chain5W x5W := by
  have small : ∀ j, j < 8 → x5W j = [0, 2, 3, 5, 6, 8, 9, 11].getD j 0 := fun j h => by unfold x5W; rw [if_pos h]
  have big : ∀ j, 8 ≤ j → x5W j = 2 * j - 3 := fun j h => by unfold x5W; rw [if_neg (by omega)]
  refine ⟨by decide, rfl, fun j c hj => ?_, fun j => ?_, fun j => ?_, by decide⟩
  · have hjl : j < 8 := by
      by_cases h : j < 8
      · exact h
      · rw [List.getElem?_eq_none (by simp [chain5W]; omega)] at hj; cases hj
    have all : ∀ j, j < 8 → ∀ c, chain5W.clauses[j]? = some c →
        c.l1.v = x5W j ∧ c.l2.v = x5W j + 1 ∧ c.l3.v = x5W j + 2 := by
      intro j hj c hc
      rw [small j hj]
      revert c
      revert j
      decide
    exact all j hjl c hj
  · by_cases h : j < 7
    · rw [small j (by omega), small (j + 1) (by omega)]
      revert j; decide
    · by_cases h7 : j = 7
      · subst h7; rw [small 7 (by omega), big 8 (by omega)]; decide
      · rw [big j (by omega), big (j + 1) (by omega)]; omega
  · by_cases h : j < 6
    · rw [small j (by omega), small (j + 2) (by omega)]
      revert j; decide
    · by_cases h6 : j < 8
      · rcases (by omega : j = 6 ∨ j = 7) with rfl | rfl
        · rw [small 6 (by omega), big 8 (by omega)]; decide
        · rw [small 7 (by omega), big 9 (by omega)]; decide
      · rw [big j (by omega), big (j + 2) (by omega)]; omega

namespace MachineOn

/-- **`chain5w2_order` se decide con la máquina tal cual**, sin preproceso ni hipótesis. -/
theorem spineVerdictOn_chain5W : SpineVerdictOn chain5W ↔ Satisfiable chain5W :=
  spineVerdictOn_iff_of_triChain triChain_chain5W

end MachineOn

end AbsSatBingo.Model
