-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainLocal.lean
import AbsSatBingo.Model.ForbidOnChainAny

/-!
# Lecturas locales: el corte de un lado, para cualquier longitud

**`LocalReads`**: una ventana que lee la variable de dentro de un bloque de en medio lee también uno de sus dos
separadores. Con eso **el corte de cualquier lado es `c = 1`** (`sideSplit_of_local`):

1. Los bloques estrictamente de dentro del tramo (`m+1 … m+r-2`) no se leen: si se leyera uno, se leería uno de sus
   separadores, que son `t_k` con `1 ≤ k < r`, sin leer.
2. La región izquierda es el bloque `m`: una sola variable de dentro, así que no tiene tres.
3. La de la derecha solo tiene leídas las del bloque `m + r - 1` y `t_r`: dos variables; o, si es el último bloque de la
   cadena, sus dos de dentro y no hay `t_r`.

**Dos condiciones de la fórmula dan las lecturas locales** (`localReads_of`), sea cual sea el orden de las cláusulas:

* **`NumLocal`**: la variable de dentro `z` de un bloque de en medio está numerada entre sus dos separadores
  (`z - 1` y `z + 1` son sus separadores). Una ventana de paso de variable que lee `z` lee `z - 1` o `z + 1`.
* **`LitLocal`**: en toda cláusula con `z`, `z` es el literal de en medio, entre los dos separadores. Una ventana de
  cláusula que lee el literal de en medio lee el primero o el último.

Resultado: **`phantomFree_inner_local`**, un lado de cualquier longitud sin más hipótesis que esas dos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int}

theorem stepVar_neg {s : Nat} (hs : s < φ.nVars) : stepVar φ (negStep s) = some s := by
  have h0 : ¬ negStep s ≤ 0 := by simp only [negStep]; omega
  have h1 : negStep s < midFusion φ := by simp only [negStep, midFusion]; omega
  simp only [stepVar, if_neg h0, if_pos h1, varOfStep_negStep]

/-- **Lecturas locales**: leer la variable de dentro de un bloque de en medio es leer uno de sus separadores. -/
def LocalReads (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) : Prop :=
  ∀ (k : Int) (z p : Nat), 1 ≤ p → p + 1 < n → zone z = p → ReadsAt φ k z →
    ReadsAt φ k (sv p) ∨ ReadsAt φ k (sv (p + 1))

/-- La numeración: la variable de dentro de un bloque de en medio, entre sus dos separadores. -/
def NumLocal (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) : Prop :=
  ∀ z p, 1 ≤ p → p + 1 < n → zone z = p → 1 ≤ z ∧ z + 1 < φ.nVars ∧
    (z - 1 = sv p ∨ z - 1 = sv (p + 1)) ∧ (z + 1 = sv p ∨ z + 1 = sv (p + 1))

/-- Los literales: en toda cláusula con la variable de dentro de un bloque de en medio, es el de en medio, entre sus
separadores. -/
def LitLocal (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) : Prop :=
  ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → ∀ z p, 1 ≤ p → p + 1 < n → zone z = p → ClVar c z →
    c.l2.v = z ∧ (c.l1.v = sv p ∨ c.l1.v = sv (p + 1)) ∧ (c.l3.v = sv p ∨ c.l3.v = sv (p + 1))

section Local

variable {n : Nat} {zone sv : Nat → Nat}

/-- **Las dos condiciones dan las lecturas locales.** -/
theorem localReads_of (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    (hN : NumLocal φ n zone sv) (hC : LitLocal φ n zone sv) : LocalReads φ n zone sv := by
  intro k z p hp1 hp2 hz ⟨k', hw, hk'⟩
  -- leer una de las dos (`e` dice que es un separador del bloque)
  have pick : ∀ {y : Nat}, (y = sv p ∨ y = sv (p + 1)) → ReadsAt φ k y → ReadsAt φ k (sv p) ∨ ReadsAt φ k (sv (p + 1)) :=
    fun {y} e h => by rcases e with rfl | rfl; exact Or.inl h; exact Or.inr h
  rcases step_cases φ k' with h0 | ⟨v, hv, e⟩ | ⟨v, hv, e⟩ | e | ⟨j, q, c, hq, hjlt, hj, e⟩ | e
  · exfalso; simp only [stepVar, if_pos h0] at hk'; cases hk'
  · -- el paso positivo de `v`: es `z`
    rw [e, stepVar_var hv] at hk'
    have hvz : v = z := Option.some.inj hk'
    subst hvz
    obtain ⟨z1, z2, em, ep⟩ := hN v p hp1 hp2 hz
    rcases hw with h | ⟨_, h⟩ | ⟨_, h⟩
    · -- `k = 2v + 1`: lee `v - 1` en `k - 1`
      refine pick em ⟨k - 1, Or.inr (Or.inl ⟨by simp only [varStep] at e; omega, rfl⟩), ?_⟩
      rw [show k - 1 = negStep (v - 1) by simp only [varStep, negStep] at e ⊢; omega]
      exact stepVar_neg (by omega)
    · -- `k = 2v + 2`: lee `v - 1` en `k - 2`
      refine pick em ⟨k - 2, Or.inr (Or.inr ⟨by simp only [varStep] at e; omega, rfl⟩), ?_⟩
      rw [show k - 2 = negStep (v - 1) by simp only [varStep, negStep] at e ⊢; omega]
      exact stepVar_neg (by omega)
    · -- `k = 2v + 3`: lee `v + 1` en `k`
      refine pick ep ⟨k, Or.inl rfl, ?_⟩
      rw [show k = varStep (v + 1) by simp only [varStep] at e ⊢; omega]
      exact stepVar_var z2
  · -- el paso negativo de `v`
    rw [e, stepVar_neg hv] at hk'
    have hvz : v = z := Option.some.inj hk'
    subst hvz
    obtain ⟨z1, z2, em, ep⟩ := hN v p hp1 hp2 hz
    rcases hw with h | ⟨_, h⟩ | ⟨_, h⟩
    · -- `k = 2v + 2`: lee `v - 1` en `k - 2`
      refine pick em ⟨k - 2, Or.inr (Or.inr ⟨by simp only [negStep] at e; omega, rfl⟩), ?_⟩
      rw [show k - 2 = negStep (v - 1) by simp only [negStep] at e ⊢; omega]
      exact stepVar_neg (by omega)
    · -- `k = 2v + 3`: lee `v + 1` en `k`
      refine pick ep ⟨k, Or.inl rfl, ?_⟩
      rw [show k = varStep (v + 1) by simp only [varStep, negStep] at e ⊢; omega]
      exact stepVar_var z2
    · -- `k = 2v + 4`: lee `v + 1` en `k - 1`
      refine pick ep ⟨k - 1, Or.inr (Or.inl ⟨by simp only [negStep] at e; omega, rfl⟩), ?_⟩
      rw [show k - 1 = varStep (v + 1) by simp only [varStep, negStep] at e ⊢; omega]
      exact stepVar_var z2
  · exfalso
    have h0 : ¬ k' ≤ 0 := by rw [e]; simp only [midFusion]; omega
    have h1 : ¬ k' < midFusion φ := by rw [e]; omega
    simp only [stepVar, if_neg h0, if_neg h1, if_pos e] at hk'; cases hk'
  · -- un paso de cláusula: su literal es `z`, el de en medio
    rw [e, stepVar_clause hj q hq] at hk'
    cases hk'
    have hcv : ClVar c (litAt c q).v := litAt_clVar c q
    obtain ⟨e2, e1, e3⟩ := hC j c hj _ p hp1 hp2 hz hcv
    -- el literal es el de en medio
    have hq1 : q = 1 := by
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
      · exfalso
        have : zone c.l1.v = p := hz
        rcases e1 with h | h <;> rw [h, hsv _ (by omega) (by omega)] at this <;> omega
      · rfl
      · exfalso
        have : zone c.l3.v = p := hz
        rcases e3 with h | h <;> rw [h, hsv _ (by omega) (by omega)] at this <;> omega
    subst hq1
    rcases hw with h | ⟨_, h⟩ | ⟨_, h⟩
    · -- `k` es el paso del literal de en medio: lee el primero en `k - 1`
      refine pick e1 ⟨k - 1, Or.inr (Or.inl ⟨by
        rw [e] at h; simp only [clauseStep] at h; omega, rfl⟩), ?_⟩
      rw [show k - 1 = clauseStep φ j 0 by rw [e] at h; simp only [clauseStep] at h ⊢; omega]
      exact stepVar_clause hj 0 (by omega)
    · -- `k` es el del último: lo lee
      refine pick e3 ⟨k, Or.inl rfl, ?_⟩
      rw [show k = clauseStep φ j 2 by rw [e] at h; simp only [clauseStep] at h ⊢; omega]
      exact stepVar_clause hj 2 (by omega)
    · -- `k` es el siguiente al último: lee el último en `k - 1`
      refine pick e3 ⟨k - 1, Or.inr (Or.inl ⟨by
        rw [e] at h; simp only [clauseStep] at h ⊢; omega, rfl⟩), ?_⟩
      rw [show k - 1 = clauseStep φ j 2 by rw [e] at h; simp only [clauseStep] at h ⊢; omega]
      exact stepVar_clause hj 2 (by omega)
  · exfalso
    have h0 : ¬ k' ≤ 0 := by have := e; simp only [fusionTop] at this; omega
    have h1 : ¬ k' < midFusion φ := by simp only [fusionTop, midFusion] at e ⊢; omega
    have h2 : ¬ k' = midFusion φ := by simp only [fusionTop, midFusion] at e ⊢; omega
    simp only [stepVar, if_neg h0, if_neg h1, if_neg h2, if_pos e] at hk'; cases hk'

/-- **El corte de cualquier lado, con lecturas locales: `c = 1`.** -/
theorem sideSplit_of_local (D : ChainN φ n zone) (hL : LocalReads φ n zone sv) {m b : Nat} (hm1 : 1 ≤ m) (hmb : m < b) (hbn : b ≤ n) (N : Int) :
    SideSplit φ n zone sv m b N := by
  intro i j l _ _ _ _ _ _ hr
  have hle := frN_le (φ := φ) (sv := sv) (i := i) (j := j) (l := l) hmb
  generalize hrd : frN φ sv m b i j l = r at hr hle
  have hun : ∀ k, 1 ≤ k → k < r → ¬ InW φ i j l (sv (m + k)) := fun k a c => by
    rw [← hrd] at c; exact frN_un a c
  -- leer es leer en una de las tres ventanas
  have of_inW : ∀ {z}, InW φ i j l z → ∃ k, (k = i ∨ k = j ∨ k = l) ∧ ReadsAt φ k z := by
    rintro z ⟨k, k', hk, hw, hz⟩; exact ⟨k, hk, k', hw, hz⟩
  -- los bloques de dentro del tramo no se leen
  have inner : ∀ {z}, m + 1 ≤ zone z → zone z + 2 ≤ m + r → ¬ InW φ i j l z := by
    intro z h1 h2 hw
    obtain ⟨k, hk, hrk⟩ := of_inW hw
    rcases hL k z (zone z) (by omega) (by omega) rfl hrk with h | h
    · refine hun (zone z - m) (by omega) (by omega) ?_
      rw [show m + (zone z - m) = zone z by omega]; exact inW_of_reads hk h
    · refine hun (zone z + 1 - m) (by omega) (by omega) ?_
      rw [show m + (zone z + 1 - m) = zone z + 1 by omega]; exact inW_of_reads hk h
  have inw : ∀ {k : Int} {z}, (k = i ∨ k = j ∨ k = l) → ReadsAt φ k z → InW φ i j l z :=
    fun hk h => inW_of_reads hk h
  refine ⟨1, Nat.le_refl _, by omega, ?_, ?_⟩
  · -- la región de `v`: el bloque `m`, una variable
    rintro ⟨z1, z2, z3, a1, a2, _, d12, _, _, _, _, _⟩
    exact d12 (D.cardM m hm1 (by omega) z1 z2 (by omega) (by omega))
  · rintro ⟨z1, z2, z3, a1, a2, a3, d12, d13, d23, r1, r2, r3⟩
    -- cada una es de dentro del bloque `m + r - 1` o es `t_r`
    have cl : ∀ {z} {k : Int}, (k = i ∨ k = j ∨ k = l) → ReadsAt φ k z →
        ((m + 1 ≤ zone z ∧ zone z < m + r) ∨ (m + r < b ∧ zone z = n + (m + r))) →
        zone z = m + r - 1 ∨ (m + r < b ∧ zone z = n + (m + r)) := by
      intro z k hk h hm
      rcases hm with ⟨b1, b2⟩ | h'
      · by_cases e : zone z + 2 ≤ m + r
        · exact absurd (inw hk h) (inner b1 e)
        · exact Or.inl (by omega)
      · exact Or.inr h'
    have c1 := cl (Or.inr (Or.inr rfl)) r1 (a1.imp (fun h => ⟨by omega, h.2⟩) id)
    have c2 := cl (Or.inr (Or.inl rfl)) r2 (a2.imp (fun h => ⟨by omega, h.2⟩) id)
    have c3 := cl (Or.inl rfl) r3 (a3.imp (fun h => ⟨by omega, h.2⟩) id)
    by_cases hlast : m + r - 1 + 1 < n
    · -- de en medio: una de dentro y un separador
      have e1 : ∀ {y y'}, zone y = m + r - 1 → zone y' = m + r - 1 → y = y' := fun h h' =>
        D.cardM (m + r - 1) (by omega) hlast _ _ h h'
      have e2 : ∀ {y y'}, zone y = n + (m + r) → zone y' = n + (m + r) → y = y' := fun h h' =>
        D.sep1 (m + r) (by omega) (by omega) _ _ h h'
      rcases c1 with h1 | ⟨_, h1⟩ <;> rcases c2 with h2 | ⟨_, h2⟩ <;> rcases c3 with h3 | ⟨_, h3⟩
      · exact d12 (e1 h1 h2)
      · exact d12 (e1 h1 h2)
      · exact d13 (e1 h1 h3)
      · exact d23 (e2 h2 h3)
      · exact d23 (e1 h2 h3)
      · exact d13 (e2 h1 h3)
      · exact d12 (e2 h1 h2)
      · exact d12 (e2 h1 h2)
    · -- el último bloque de la cadena: no hay `t_r`
      have nt : ∀ {y}, (zone y = m + r - 1 ∨ (m + r < b ∧ zone y = n + (m + r))) → zone y = n - 1 := by
        intro y h; rcases h with h | ⟨h, _⟩ <;> omega
      exact D.cardL z1 z2 z3 (nt c1) (nt c2) (nt c3) d12 d13 d23

/-- **Un lado de cualquier longitud con lecturas locales**: `v` de dentro del bloque `m`, el separador `m` fijado. -/
theorem phantomFree_inner_local (hl : LocPair φ P0 P σ) (D : ChainN φ n zone)
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k) (hL : LocalReads φ n zone sv) {m b : Nat} (hm1 : 1 ≤ m)
    (hmb : m < b) (hbn : b ≤ n) (hfix : FixedEnd n zone P0 b) (hmid : midFusion φ < Nn)
    {v : Nat} (hv : stepVar φ σ = some v) (hzv : zone v = m)
    (hfa : ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + m → c z = c' z) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) :
    PhantomFree φ P0 P Nn σ :=
  phantomFree_inner_any hl D hsv hm1 hmb hbn hfix hmid (sideSplit_of_local D hL hm1 hmb hbn Nn) hv hzv hfa
    hσ0 hσN

end Local

end GPathB

end AbsSatBingo.Model
