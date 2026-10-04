-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainOps.lean
import AbsSatBingo.Model.ForbidOnChain6B

/-!
# Operaciones sobre cadenas: truncar e intercambiar

Las líneas de un prefijo solo ven los bloques de las cláusulas ya leídas. Dos operaciones dan, a partir de la cadena
entera, la cadena corta en la que la variable fijada es un separador:

* **`truncZ`** (`chainN_truncS`): los bloques `0 … k-1` y el separador `k`, con un bloque vacío detrás; lo demás,
  fuera. Vale para una fórmula cuyas cláusulas están en esos bloques, fuera, o en bloques más allá de `k`.
* **`swapZ`** (`chainN_swap`): con el último bloque vacío, la variable `v` de dentro del penúltimo pasa a ser el último
  separador, y el que lo era entra en el penúltimo bloque.

**`line_comp`**: la variable fijada está en el bloque `k - 1` (el último leído) de una cadena de hasta tres bloques
leídos; se trunca, se intercambia si hace falta, y cierra `phantomFree_bisect` con extremos libres.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ ψ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int}

/-! ## Truncar -/

/-- Los bloques `0 … k-1` y los separadores `1 … k` de una cadena de `n`; lo demás, fuera (`2 (k + 1)`). -/
def truncZ (n k : Nat) (zone : Nat → Nat) (z : Nat) : Nat :=
  if zone z < k then zone z
  else if n + 1 ≤ zone z ∧ zone z ≤ n + k then zone z - n + (k + 1)
  else 2 * (k + 1)

theorem truncZ_cases (n k : Nat) (zone : Nat → Nat) (z : Nat) :
    (zone z < k ∧ truncZ n k zone z = zone z) ∨
    (¬ zone z < k ∧ n + 1 ≤ zone z ∧ zone z ≤ n + k ∧ truncZ n k zone z = zone z - n + (k + 1)) ∨
    (¬ zone z < k ∧ ¬ (n + 1 ≤ zone z ∧ zone z ≤ n + k) ∧ truncZ n k zone z = 2 * (k + 1)) := by
  unfold truncZ
  by_cases h1 : zone z < k
  · exact Or.inl ⟨h1, if_pos h1⟩
  rw [if_neg h1]
  by_cases h2 : n + 1 ≤ zone z ∧ zone z ≤ n + k
  · exact Or.inr (Or.inl ⟨h1, h2.1, h2.2, if_pos h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, if_neg h2⟩)

section Trunc

variable {n k : Nat} {zone : Nat → Nat}

theorem truncZ_lt {j z : Nat} (hj : j < k) : truncZ n k zone z = j ↔ zone z = j := by
  rcases truncZ_cases n k zone z with ⟨a, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, e⟩ <;> rw [e] <;> omega

theorem truncZ_sep (hkn : k < n) {i z : Nat} (h1 : 1 ≤ i) (hik : i ≤ k) :
    truncZ n k zone z = (k + 1) + i ↔ zone z = n + i := by
  rcases truncZ_cases n k zone z with ⟨a, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, e⟩ <;> rw [e] <;> omega

theorem truncZ_ne_k {z : Nat} : truncZ n k zone z ≠ k := by
  rcases truncZ_cases n k zone z with ⟨a, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, e⟩ <;> rw [e] <;> omega

/-- **La cadena truncada.** -/
theorem chainN_truncS (D : ChainN φ n zone) (hnv : φ.nVars ≤ ψ.nVars) (hk1 : 1 ≤ k) (hkn : k < n)
    (hcl : ∀ c ∈ ψ.clauses, (∃ j, j < k ∧ ClIn (BlkN n zone j) c) ∨ ClIn (OutN n zone) c ∨
      ∃ j, k + 1 ≤ j ∧ j < n ∧ ClIn (BlkN n zone j) c) :
    ChainN ψ (k + 1) (truncZ n k zone) := by
  -- las tres clases de variables, por su zona nueva
  have out : ∀ {z}, (zone z = n ∨ 2 * n ≤ zone z ∨ (k ≤ zone z ∧ zone z < n) ∨ n + k < zone z) →
      OutN (k + 1) (truncZ n k zone) z := by
    intro z h
    unfold OutN
    rcases truncZ_cases n k zone z with ⟨a, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, e⟩ <;> rw [e] <;> omega
  refine ⟨by omega, fun z a b => ?_, fun i h1 h2 z z' hz hz' => ?_, fun y1 y2 y3 a b c => ?_,
    fun y1 y2 y3 a b c => ?_, fun j h1 h2 z z' hz hz' => ?_, fun c hc => ?_⟩
  · rcases truncZ_cases n k zone z with ⟨a', e⟩ | ⟨a', b', c', e⟩ | ⟨a', b', e⟩
    · omega
    · exact Nat.lt_of_lt_of_le (D.sepv z b' (by omega)) hnv
    · omega
  · exact D.sep1 i h1 (by omega) z z' ((truncZ_sep hkn h1 (by omega)).mp hz) ((truncZ_sep hkn h1 (by omega)).mp hz')
  · exact D.card0 y1 y2 y3 ((truncZ_lt (by omega)).mp a) ((truncZ_lt (by omega)).mp b)
      ((truncZ_lt (by omega)).mp c)
  · exact absurd a (by rw [show k + 1 - 1 = k by omega]; exact truncZ_ne_k)
  · exact D.cardM j h1 (by omega) z z' ((truncZ_lt (by omega)).mp hz) ((truncZ_lt (by omega)).mp hz')
  · rcases hcl c hc with ⟨j, hj, i1, i2, i3⟩ | ⟨o1, o2, o3⟩ | ⟨j, hj1, hj2, i1, i2, i3⟩
    · have tb : ∀ {z}, BlkN n zone j z → BlkN (k + 1) (truncZ n k zone) j z := by
        intro z h
        rcases h with h | ⟨h1, h⟩ | ⟨h1, h⟩
        · exact Or.inl ((truncZ_lt hj).mpr h)
        · exact Or.inr (Or.inl ⟨h1, (truncZ_sep hkn h1 (by omega)).mpr h⟩)
        · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
          rw [show k + 1 + j + 1 = (k + 1) + (j + 1) by omega]
          exact (truncZ_sep hkn (by omega) (by omega)).mpr (by omega)
      exact Or.inr ⟨j, by omega, tb i1, tb i2, tb i3⟩
    · have to : ∀ {z}, OutN n zone z → OutN (k + 1) (truncZ n k zone) z := by
        intro z h; unfold OutN at h; exact out (by omega)
      exact Or.inl ⟨to o1, to o2, to o3⟩
    · have to : ∀ {z}, BlkN n zone j z → OutN (k + 1) (truncZ n k zone) z := by
        intro z h
        rcases h with h | ⟨_, h⟩ | ⟨_, h⟩ <;> exact out (by omega)
      exact Or.inl ⟨to i1, to i2, to i3⟩

end Trunc

/-! ## Intercambiar -/

/-- `v` pasa a ser el último separador (`n + (n - 1)`); el que lo era, al penúltimo bloque. -/
def swapZ (n : Nat) (zone : Nat → Nat) (v z : Nat) : Nat :=
  if z = v then 2 * n - 1 else if zone z = 2 * n - 1 then n - 2 else zone z

theorem swapZ_cases (n : Nat) (zone : Nat → Nat) (v z : Nat) :
    (z = v ∧ swapZ n zone v z = 2 * n - 1) ∨ (z ≠ v ∧ zone z = 2 * n - 1 ∧ swapZ n zone v z = n - 2) ∨
    (z ≠ v ∧ zone z ≠ 2 * n - 1 ∧ swapZ n zone v z = zone z) := by
  unfold swapZ
  by_cases h1 : z = v
  · exact Or.inl ⟨h1, if_pos h1⟩
  rw [if_neg h1]
  by_cases h2 : zone z = 2 * n - 1
  · exact Or.inr (Or.inl ⟨h1, h2, if_pos h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, if_neg h2⟩)

section Swap

variable {n : Nat} {zone : Nat → Nat} {v : Nat}

/-- **La cadena con `v` de separador.** -/
theorem chainN_swap (D : ChainN ψ n zone) (hv : zone v = n - 2) (hvlt : v < ψ.nVars)
    (hempty : ∀ z, zone z ≠ n - 1) : ChainN ψ n (swapZ n zone v) := by
  have two := D.two
  -- el último separador es una sola variable
  have s1 : ∀ {z z'}, zone z = 2 * n - 1 → zone z' = 2 * n - 1 → z = z' := fun {z z'} h h' =>
    D.sep1 (n - 1) (by omega) (by omega) z z' (by omega) (by omega)
  refine ⟨two, fun z a b => ?_, fun i h1 h2 z z' hz hz' => ?_, fun y1 y2 y3 a b c d12 d13 d23 => ?_,
    fun y1 y2 y3 a b c => ?_, fun j h1 h2 z z' hz hz' => ?_, fun c hc => ?_⟩
  · rcases swapZ_cases n zone v z with ⟨rfl, _⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩
    · exact hvlt
    · omega
    · rw [e] at a b; exact D.sepv z a b
  · by_cases hi : i = n - 1
    · subst hi
      have tv : ∀ {y}, swapZ n zone v y = n + (n - 1) → y = v := by
        intro y h
        rcases swapZ_cases n zone v y with ⟨e, _⟩ | ⟨_, _, e⟩ | ⟨_, a, e⟩
        · exact e
        · omega
        · omega
      exact (tv hz).trans (tv hz').symm
    · have tz : ∀ {y}, swapZ n zone v y = n + i → zone y = n + i := by
        intro y h
        rcases swapZ_cases n zone v y with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> omega
      exact D.sep1 i h1 h2 z z' (tz hz) (tz hz')
  · -- el bloque `0`
    have cl0 : ∀ {y}, swapZ n zone v y = 0 → (zone y = 0 ∧ y ≠ v) ∨ (n = 2 ∧ zone y = 2 * n - 1) := by
      intro y h
      rcases swapZ_cases n zone v y with ⟨_, e⟩ | ⟨a, b, e⟩ | ⟨a, _, e⟩
      · omega
      · exact Or.inr ⟨by omega, b⟩
      · exact Or.inl ⟨by omega, a⟩
    rcases cl0 a with ⟨a1, a2⟩ | ⟨_, a1⟩ <;> rcases cl0 b with ⟨b1, b2⟩ | ⟨_, b1⟩ <;>
      rcases cl0 c with ⟨c1, c2⟩ | ⟨_, c1⟩
    · exact D.card0 y1 y2 y3 a1 b1 c1 d12 d13 d23
    · exact D.card0 y1 y2 v a1 b1 (by omega) d12 a2 b2
    · exact D.card0 y1 y3 v a1 c1 (by omega) d13 a2 c2
    · exact d23 (s1 b1 c1)
    · exact D.card0 y2 y3 v b1 c1 (by omega) d23 b2 c2
    · exact d13 (s1 a1 c1)
    · exact d12 (s1 a1 b1)
    · exact d12 (s1 a1 b1)
  · -- el último bloque, vacío
    exfalso
    rcases swapZ_cases n zone v y1 with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, h, e⟩
    · omega
    · omega
    · exact hempty y1 (by omega)
  · by_cases hj : j = n - 2
    · subst hj
      have tz : ∀ {y}, swapZ n zone v y = n - 2 → zone y = 2 * n - 1 := by
        intro y h
        rcases swapZ_cases n zone v y with ⟨_, e⟩ | ⟨_, b, _⟩ | ⟨a, _, e⟩
        · omega
        · exact b
        · exact absurd (D.cardM (n - 2) h1 h2 y v (by omega) hv) a
      exact s1 (tz hz) (tz hz')
    · have tz : ∀ {y}, swapZ n zone v y = j → zone y = j := by
        intro y h
        rcases swapZ_cases n zone v y with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> omega
      exact D.cardM j h1 h2 z z' (tz hz) (tz hz')
  · have keep : ∀ {y}, y ≠ v → zone y ≠ 2 * n - 1 → swapZ n zone v y = zone y := fun {y} a b => by
      rcases swapZ_cases n zone v y with ⟨e, _⟩ | ⟨_, e, _⟩ | ⟨_, _, e⟩
      · exact absurd e a
      · exact absurd e b
      · exact e
    have nv : ∀ {y}, zone y ≠ n - 2 → y ≠ v := fun {y} h e => h (e ▸ hv)
    rcases D.cl c hc with ⟨o1, o2, o3⟩ | ⟨j, hj, i1, i2, i3⟩
    · have to : ∀ {y}, OutN n zone y → OutN n (swapZ n zone v) y := by
        intro y h
        unfold OutN at h ⊢
        rw [keep (nv (by omega)) (by omega)]; exact h
      exact Or.inl ⟨to o1, to o2, to o3⟩
    · by_cases hj1 : j = n - 1
      · -- un bloque vacío: sus cláusulas solo tienen el último separador, que pasa al penúltimo bloque
        subst hj1
        have tb : ∀ {y}, BlkN n zone (n - 1) y → BlkN n (swapZ n zone v) (n - 2) y := by
          intro y h
          rcases h with h | ⟨_, h⟩ | ⟨_, h⟩
          · exact absurd h (hempty y)
          · have e : zone y = 2 * n - 1 := by omega
            rcases swapZ_cases n zone v y with ⟨rfl, _⟩ | ⟨_, _, e'⟩ | ⟨_, b, _⟩
            · omega
            · exact Or.inl e'
            · exact absurd e b
          · omega
        exact Or.inr ⟨n - 2, by omega, tb i1, tb i2, tb i3⟩
      by_cases hj2 : j = n - 2
      · subst hj2
        have tb : ∀ {y}, BlkN n zone (n - 2) y → BlkN n (swapZ n zone v) (n - 2) y := by
          intro y h
          rcases swapZ_cases n zone v y with ⟨_, e⟩ | ⟨_, b, e⟩ | ⟨a, b, e⟩
          · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
          · exact Or.inl e
          · unfold BlkN; rw [e]; exact h
        exact Or.inr ⟨n - 2, by omega, tb i1, tb i2, tb i3⟩
      · have tb : ∀ {y}, BlkN n zone j y → BlkN n (swapZ n zone v) j y := by
          intro y h
          have a : zone y ≠ n - 2 := by rcases h with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
          have b : zone y ≠ 2 * n - 1 := by rcases h with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
          unfold BlkN; rw [keep (nv a) b]; exact h
        exact Or.inr ⟨j, hj, tb i1, tb i2, tb i3⟩

end Swap


/-! ## Una línea del último bloque leído -/

/-- **Un separador con los dos lados cortos y los extremos libres.** -/
theorem case_sepG (hl : LocPair ψ P0 P σ) {n : Nat} {zone sv : Nat → Nat} (C : ChainN ψ n zone)
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k) {v m : Nat}
    (hv : stepVar ψ σ = some v) (hzv : zone v = n + m) (hm1 : 1 ≤ m) (hmn : m < n)
    (hL : m ≤ 3 ∧ n - m ≤ 2) (hmid : midFusion ψ < Nn)
    (hwL : 3 ≤ m → ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt ψ lam (sv (m - 1)) ∧ ReadsAt ψ lam (sv (m - 2)))
    (hσ0 : 0 ≤ σ) (hσN : σ < Nn) : PhantomFree ψ P0 P Nn σ :=
  phantomFree_bisect hl C hsv hv (fun h => absurd h (by omega)) (fun h => hwL (by omega)) hmid hzv hm1 (a := 0)
    (b := n) (by omega) hmn (Nat.le_refl _) (fun h => absurd h (by omega)) (fun h => absurd h (by omega))
    (Or.inl (by omega)) (Or.inl (by omega)) hσ0 hσN

/-- **La variable fijada está en el bloque `k - 1`, el último leído** (`k ≤ 3`): se trunca la cadena en el separador
`k`, se intercambia si `v` es de dentro, y `v` es un separador con lados de hasta tres bloques y uno. -/
theorem line_comp (hl : LocPair ψ P0 P σ) {n : Nat} {zone sv : Nat → Nat} (D : ChainN φ n zone)
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k) (hnv : φ.nVars ≤ ψ.nVars) {k : Nat} (hk1 : 1 ≤ k)
    (hk3 : k ≤ 3) (hkn : k < n)
    (hcl : ∀ c ∈ ψ.clauses, (∃ j, j < k ∧ ClIn (BlkN n zone j) c) ∨ ClIn (OutN n zone) c ∨
      ∃ j, k + 1 ≤ j ∧ j < n ∧ ClIn (BlkN n zone j) c)
    {v : Nat} (hv : stepVar ψ σ = some v) (hvlt : v < ψ.nVars) (hB : BlkN n zone (k - 1) v)
    (hmid : midFusion ψ < Nn)
    (hwin : k = 3 → ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt ψ lam (sv 2) ∧ ReadsAt ψ lam (sv 1))
    (hσ0 : 0 ≤ σ) (hσN : σ < Nn) : PhantomFree ψ P0 P Nn σ := by
  have D' := chainN_truncS D hnv hk1 hkn hcl
  have hsv' : ∀ i, 1 ≤ i → i < k + 1 → truncZ n k zone (sv i) = (k + 1) + i := fun i h1 h2 =>
    (truncZ_sep hkn h1 (by omega)).mpr (hsv i h1 (by omega))
  rcases hB with h | ⟨h1, h⟩ | ⟨h1, h⟩
  · -- `v` de dentro: pasa a ser el separador `k`
    have hvz : truncZ n k zone v = k + 1 - 2 := (truncZ_lt (by omega)).mpr (by omega)
    have D'' := chainN_swap D' hvz hvlt (fun z => by rw [show k + 1 - 1 = k by omega]; exact truncZ_ne_k)
    let sv'' : Nat → Nat := fun i => if i = k then v else sv i
    have hsv'' : ∀ i, 1 ≤ i → i < k + 1 → swapZ (k + 1) (truncZ n k zone) v (sv'' i) = (k + 1) + i := by
      intro i h1 h2
      by_cases hi : i = k
      · subst hi
        simp only [sv'', if_pos rfl]
        unfold swapZ; rw [if_pos rfl]; omega
      · simp only [sv'', if_neg hi]
        have e := hsv' i h1 h2
        rcases swapZ_cases (k + 1) (truncZ n k zone) v (sv i) with ⟨a, _⟩ | ⟨_, b, _⟩ | ⟨_, _, e'⟩
        · rw [a, hvz] at e; omega
        · omega
        · rw [e', e]
    refine case_sepG hl D'' hsv'' hv (m := k) (by unfold swapZ; rw [if_pos rfl]; omega) hk1 (by omega)
      ⟨hk3, by omega⟩ hmid (fun h3 => ?_) hσ0 hσN
    obtain rfl : k = 3 := by omega
    obtain ⟨lam, l0, lN, r2, r1⟩ := hwin rfl
    refine ⟨lam, l0, lN, ?_, ?_⟩
    · show ReadsAt ψ lam (if 3 - 1 = 3 then v else sv (3 - 1))
      rw [if_neg (by omega)]; exact r2
    · show ReadsAt ψ lam (if 3 - 2 = 3 then v else sv (3 - 2))
      rw [if_neg (by omega)]; exact r1
  · -- el separador `k - 1`
    exact case_sepG hl D' hsv' hv (m := k - 1) ((truncZ_sep hkn h1 (by omega)).mpr h) h1 (by omega)
      ⟨by omega, by omega⟩ hmid (fun h3 => absurd h3 (by omega)) hσ0 hσN
  · -- el separador `k`
    exact case_sepG hl D' hsv' hv (m := k) ((truncZ_sep hkn (by omega) (Nat.le_refl _)).mpr (by omega)) hk1
      (by omega) ⟨hk3, by omega⟩ hmid (fun h3 => by
        obtain ⟨lam, l0, lN, r2, r1⟩ := hwin (by omega)
        exact ⟨lam, l0, lN, by rw [show k - 1 = 2 by omega]; exact r2, by rw [show k - 2 = 1 by omega]; exact r1⟩)
      hσ0 hσN

end GPathB

end AbsSatBingo.Model
