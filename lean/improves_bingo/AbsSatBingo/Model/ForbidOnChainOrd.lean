-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainOrd.lean
import AbsSatBingo.Model.ForbidOnChainBisectN

/-!
# Cadenas en orden, de cualquier longitud: la máquina exacta y el lector sin hipótesis

**`ChainOrdN φ n zone sv`**: una cadena de `n` bloques (`n` cualquiera) con las cláusulas en el orden de la cadena (la `j`
en el bloque `j`), la variable de dentro de cada bloque de en medio numerada entre sus dos separadores (`NumLocal`) y
como literal de en medio de sus cláusulas (`LitLocal`).

Las líneas de la cláusula `j` ven el prefijo de `j + 1` cláusulas. En él la variable fijada `v` es un separador de una
cadena corta, y cierra `phantomFree_bisectN` (dos lados abiertos de cualquier longitud):

* `j + 1 < n`: se trunca en el separador `j + 1` (`chainN_truncS`); `v = s_j` o `v = s_{j+1}` son separadores; si `v`
  es de dentro, se intercambia con `s_{j+1}` (`chainN_swap`).
* `j + 1 = n`: `v = s_{n-1}`, o `v` de dentro del último bloque, que se **aísla** como un separador nuevo con un bloque
  vacío detrás (`chainN_isolate`).

**El truco**: intercambiar y aislar rompen las lecturas locales solo en los dos bloques pegados a `v`, que son las
regiones de `v` de cada lado y no las mira `readsB`: basta `LocalReadsAway` (`away_swap`, `away_isolate`).

Resultado: **`phantomAt_of_chainOrd`**, **`machineExact_of_chainOrd`**, **`spineVerdictOn_iff_of_chainOrd`**,
**`reader_sep_of_chainOrd`** (el lector, en cualquier orden de los separadores, sin hipótesis).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ ψ : Cnf}

/-- **Una cadena en orden, de cualquier longitud.** -/
structure ChainOrdN (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) : Prop where
  D   : ChainN φ n zone
  hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k
  len : φ.clauses.length = n
  blk : ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → ClIn (BlkN n zone j) c
  num : GPathB.NumLocal φ n zone sv
  lit : GPathB.LitLocal φ n zone sv

namespace GPathB

variable {P0 P : Assign → Prop} {Nn σ : Int}

/-! ## Al prefijo -/

theorem chainN_prefix {n : Nat} {zone : Nat → Nat} (D : ChainN φ n zone) (j : Nat) :
    ChainN (prefixCnf φ j) n zone :=
  ⟨D.two, D.sepv, D.sep1, D.card0, D.cardL, D.cardM, fun c hc => D.cl c (List.mem_of_mem_take hc)⟩

theorem litLocal_prefix {n : Nat} {zone sv : Nat → Nat} (h : LitLocal φ n zone sv) (j : Nat) :
    LitLocal (prefixCnf φ j) n zone sv := by
  intro j' c hc z p h1 h2 hz hcv
  obtain ⟨i, _, e⟩ := mem_prefix_clause (List.mem_of_getElem? hc)
  exact h i c e z p h1 h2 hz hcv

/-! ## Truncar, intercambiar y aislar, con lecturas locales -/

section Ops

variable {n : Nat} {zone sv : Nat → Nat}

theorem localReads_trunc {k : Nat} (hL : LocalReads ψ n zone sv) (hkn : k < n) :
    LocalReads ψ (k + 1) (truncZ n k zone) sv := fun kk z p h1 h2 hz hr =>
  hL kk z p h1 (by omega) ((truncZ_lt (by omega)).mp hz) hr

/-- Tras intercambiar `v` con el último separador, las lecturas locales lejos de `v`. -/
theorem away_swap {n' : Nat} {zone' : Nat → Nat} {v : Nat} (hL : LocalReads ψ n' zone' sv) :
    LocalReadsAway ψ n' (swapZ n' zone' v) (fun i => if i = n' - 1 then v else sv i) (n' - 1) := by
  intro kk z p hp h1 h2 hz hr
  have e : zone' z = p := by
    rcases swapZ_cases n' zone' v z with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> omega
  rcases hL kk z p h1 h2 e hr with h | h
  · exact Or.inl (by simp only [if_neg (show p ≠ n' - 1 by omega)]; exact h)
  · exact Or.inr (by simp only [if_neg (show p + 1 ≠ n' - 1 by omega)]; exact h)

/-- Aislar `v`, de dentro del último bloque: un separador nuevo `n` y un bloque vacío detrás. -/
def isoZ (n : Nat) (zone : Nat → Nat) (v z : Nat) : Nat :=
  if z = v then 2 * n + 1 else if zone z < n then zone z
  else if n + 1 ≤ zone z ∧ zone z < 2 * n then zone z + 1 else 2 * (n + 1)

theorem isoZ_cases (n : Nat) (zone : Nat → Nat) (v z : Nat) :
    (z = v ∧ isoZ n zone v z = 2 * n + 1) ∨ (z ≠ v ∧ zone z < n ∧ isoZ n zone v z = zone z) ∨
    (z ≠ v ∧ n + 1 ≤ zone z ∧ zone z < 2 * n ∧ isoZ n zone v z = zone z + 1) ∨
    (z ≠ v ∧ n ≤ zone z ∧ ¬ (n + 1 ≤ zone z ∧ zone z < 2 * n) ∧ isoZ n zone v z = 2 * (n + 1)) := by
  unfold isoZ
  by_cases h1 : z = v
  · exact Or.inl ⟨h1, if_pos h1⟩
  rw [if_neg h1]
  by_cases h2 : zone z < n
  · exact Or.inr (Or.inl ⟨h1, h2, if_pos h2⟩)
  rw [if_neg h2]
  by_cases h3 : n + 1 ≤ zone z ∧ zone z < 2 * n
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h3.1, h3.2, if_pos h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, by omega, h3, if_neg h3⟩))

/-- **La cadena con `v` aislado.** -/
theorem chainN_isolate (D : ChainN ψ n zone) {v : Nat} (hv : zone v = n - 1) (hvlt : v < ψ.nVars) :
    ChainN ψ (n + 1) (isoZ n zone v) := by
  have two := D.two
  refine ⟨by omega, fun z a b => ?_, fun i h1 h2 z z' hz hz' => ?_, fun y1 y2 y3 a b c => ?_,
    fun y1 y2 y3 a b c => ?_, fun j h1 h2 z z' hz hz' => ?_, fun c hc => ?_⟩
  · rcases isoZ_cases n zone v z with ⟨rfl, _⟩ | ⟨_, _, e⟩ | ⟨_, b1, b2, e⟩ | ⟨_, _, _, e⟩
    · exact hvlt
    · omega
    · exact D.sepv z b1 b2
    · omega
  · by_cases hi : i = n
    · subst hi
      have tv : ∀ {y}, isoZ i zone v y = (i + 1) + i → y = v := by
        intro y h
        rcases isoZ_cases i zone v y with ⟨e, _⟩ | ⟨_, _, e⟩ | ⟨_, _, b2, e⟩ | ⟨_, _, _, e⟩
        · exact e
        all_goals omega
      exact (tv hz).trans (tv hz').symm
    · have tz : ∀ {y}, isoZ n zone v y = (n + 1) + i → zone y = n + i := by
        intro y h
        rcases isoZ_cases n zone v y with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> omega
      exact D.sep1 i h1 (by omega) z z' (tz hz) (tz hz')
  · have tz : ∀ {y}, isoZ n zone v y = 0 → zone y = 0 := by
      intro y h
      rcases isoZ_cases n zone v y with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> omega
    exact D.card0 y1 y2 y3 (tz a) (tz b) (tz c)
  · -- el bloque nuevo, vacío
    exfalso
    rcases isoZ_cases n zone v y1 with ⟨_, e⟩ | ⟨_, h, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> omega
  · by_cases hj : j = n - 1
    · -- el último bloque, sin `v`: a lo sumo una variable
      subst hj
      have tz : ∀ {y}, isoZ n zone v y = n - 1 → zone y = n - 1 ∧ y ≠ v := by
        intro y h
        rcases isoZ_cases n zone v y with ⟨_, e⟩ | ⟨a, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩
        · omega
        · exact ⟨by omega, a⟩
        · omega
        · omega
      obtain ⟨a1, a2⟩ := tz hz
      obtain ⟨b1, b2⟩ := tz hz'
      exact Classical.byContradiction (fun hne => D.cardL z z' v a1 b1 hv hne a2 b2)
    · have tz : ∀ {y}, isoZ n zone v y = j → zone y = j := by
        intro y h
        rcases isoZ_cases n zone v y with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> omega
      exact D.cardM j h1 (by omega) z z' (tz hz) (tz hz')
  · rcases D.cl c hc with ⟨o1, o2, o3⟩ | ⟨j, hj, i1, i2, i3⟩
    · have to : ∀ {y}, OutN n zone y → OutN (n + 1) (isoZ n zone v) y := by
        intro y h
        unfold OutN at h ⊢
        rcases isoZ_cases n zone v y with ⟨e1, _⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩
        · rw [e1, hv] at h; omega
        all_goals omega
      exact Or.inl ⟨to o1, to o2, to o3⟩
    · have tb : ∀ {y}, BlkN n zone j y → BlkN (n + 1) (isoZ n zone v) j y := by
        intro y h
        unfold BlkN at h ⊢
        rcases isoZ_cases n zone v y with ⟨e1, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩
        · rw [e]; rw [e1, hv] at h; omega
        all_goals rw [e]; omega
      exact Or.inr ⟨j, by omega, tb i1, tb i2, tb i3⟩

theorem away_isolate (hL : LocalReads ψ n zone sv) {v : Nat} :
    LocalReadsAway ψ (n + 1) (isoZ n zone v) (fun i => if i = n then v else sv i) n := by
  intro kk z p hp h1 h2 hz hr
  have e : zone z = p := by
    rcases isoZ_cases n zone v z with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> omega
  rcases hL kk z p h1 (by omega) e hr with h | h
  · exact Or.inl (by simp only [if_neg (show p ≠ n by omega)]; exact h)
  · exact Or.inr (by simp only [if_neg (show p + 1 ≠ n by omega)]; exact h)

end Ops

/-! ## Las líneas -/

section Lines

variable {n : Nat} {zone sv : Nat → Nat}

open Driver Machine MachineOn

/-- **Las líneas de la cláusula `j`**, en su prefijo. -/
theorem phantomAt_ordLine (hb : Bounded φ) (C : ChainOrdN φ n zone sv) {j : Nat} (hj : j < n) {T : Int}
    (hT0 : clauseStep φ j 0 ≤ T) (hT2 : T ≤ clauseStep φ j 2) (hT : 1 ≤ T) :
    PhantomAt (prefixCnf φ (j + 1)) T := by
  have hjl : j < φ.clauses.length := by rw [C.len]; exact hj
  have hcj : φ.clauses[j]? = some (φ.clauses[j]'hjl) := List.getElem?_eq_getElem _
  have hψj : (prefixCnf φ (j + 1)).clauses[j]? = some (φ.clauses[j]'hjl) := (prefix_getElem? (by omega)).trans hcj
  refine phantomAt_of_lineLocal (bounded_prefix hb (j + 1)) hψj (by rw [clauseStep_prefix]; exact hT0)
    (by rw [clauseStep_prefix]; exact hT2) hT (fun {P0 P σ N v} hl hv hcv hσ0 hσN hTN => ?_)
  have hmid : midFusion (prefixCnf φ (j + 1)) < N := by
    have := hT0; simp only [clauseStep, midFusion, prefixCnf] at this ⊢; omega
  have hBv : BlkN n zone j v := clIn_var (C.blk j _ hcj) hcv
  have hvlt : v < (prefixCnf φ (j + 1)).nVars := by
    have := hb _ (List.mem_of_getElem? hcj)
    rcases hcv with e | e | e
    · rw [e]; exact this.1
    · rw [e]; exact this.2.1
    · rw [e]; exact this.2.2
  have LR : LocalReads (prefixCnf φ (j + 1)) n zone sv := localReads_of C.hsv C.num (litLocal_prefix C.lit _)
  by_cases hlast : j + 1 < n
  · -- truncar en el separador `j + 1`
    have D' := chainN_truncS (ψ := prefixCnf φ (j + 1)) C.D (Nat.le_refl _) (k := j + 1) (by omega) hlast (fun c hc => by
      obtain ⟨i, hi, e⟩ := mem_prefix_clause hc
      exact Or.inl ⟨i, hi, C.blk i c e⟩)
    have hsv' : ∀ i, 1 ≤ i → i < j + 1 + 1 → truncZ n (j + 1) zone (sv i) = (j + 1 + 1) + i := fun i h1 h2 =>
      (truncZ_sep hlast h1 (by omega)).mpr (C.hsv i h1 (by omega))
    have LR' := localReads_trunc LR hlast
    rcases hBv with h | ⟨h1, h⟩ | ⟨h1, h⟩
    · -- de dentro: se intercambia con `s_{j+1}`
      have hvz : truncZ n (j + 1) zone v = j + 1 + 1 - 2 := (truncZ_lt (by omega)).mpr (by omega)
      have D'' := chainN_swap D' hvz hvlt (fun z => by rw [show j + 1 + 1 - 1 = j + 1 by omega]; exact truncZ_ne_k)
      have hsv'' : ∀ i, 1 ≤ i → i < j + 1 + 1 → swapZ (j + 1 + 1) (truncZ n (j + 1) zone) v
          ((fun i => if i = j + 1 + 1 - 1 then v else sv i) i) = (j + 1 + 1) + i := by
        intro i h1 h2
        by_cases hi : i = j + 1
        · subst hi
          simp only [if_pos (show j + 1 = j + 1 + 1 - 1 by omega)]
          unfold swapZ; rw [if_pos rfl]; omega
        · simp only [if_neg (show i ≠ j + 1 + 1 - 1 by omega)]
          have e := hsv' i h1 h2
          rcases swapZ_cases (j + 1 + 1) (truncZ n (j + 1) zone) v (sv i) with ⟨a, _⟩ | ⟨_, b, _⟩ | ⟨_, _, e'⟩
          · rw [a, hvz] at e; omega
          · omega
          · rw [e', e]
      exact phantomFree_bisectN hl D'' hsv'' hv (away_swap LR') hmid
        (by unfold swapZ; rw [if_pos rfl]; omega) (m := j + 1 + 1 - 1) (a := 0) (b := j + 1 + 1) (by omega)
        (by omega) (by omega) (Nat.le_refl _) (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) hσ0 hσN
    · -- el separador `j`
      exact phantomFree_bisectN hl D' hsv' hv (away_of_local LR' j) hmid ((truncZ_sep hlast h1 (by omega)).mpr h)
        (m := j) (a := 0) (b := j + 1 + 1) h1 (by omega) (by omega) (Nat.le_refl _) (fun h => absurd h (by omega))
        (fun h => absurd h (by omega)) hσ0 hσN
    · -- el separador `j + 1`
      exact phantomFree_bisectN hl D' hsv' hv (away_of_local LR' (j + 1)) hmid
        ((truncZ_sep hlast (by omega) (Nat.le_refl _)).mpr (by omega)) (m := j + 1) (a := 0) (b := j + 1 + 1)
        (by omega) (by omega) (by omega) (Nat.le_refl _) (fun h => absurd h (by omega))
        (fun h => absurd h (by omega)) hσ0 hσN
  · -- la última cláusula
    have hjn : j = n - 1 := by omega
    have D' := chainN_prefix C.D (j + 1)
    rcases hBv with h | ⟨h1, h⟩ | ⟨h1, h⟩
    · -- de dentro del último bloque: se aísla
      have D'' := chainN_isolate D' (show zone v = n - 1 by omega) hvlt
      have hsv'' : ∀ i, 1 ≤ i → i < n + 1 → isoZ n zone v ((fun i => if i = n then v else sv i) i) = (n + 1) + i := by
        intro i h1 h2
        by_cases hi : i = n
        · show isoZ n zone v (if i = n then v else sv i) = n + 1 + i
          rw [if_pos hi, show isoZ n zone v v = 2 * n + 1 by unfold isoZ; rw [if_pos rfl]]; omega
        · simp only [if_neg hi]
          have e := C.hsv i h1 (by omega)
          rcases isoZ_cases n zone v (sv i) with ⟨a, _⟩ | ⟨_, b, _⟩ | ⟨_, _, _, e'⟩ | ⟨_, _, b, _⟩
          · rw [a] at e; omega
          · omega
          · rw [e', e]; omega
          · exact absurd ⟨by omega, by omega⟩ b
      exact phantomFree_bisectN hl D'' hsv'' hv (away_isolate LR) hmid (by unfold isoZ; rw [if_pos rfl]; omega)
        (m := n) (a := 0) (b := n + 1) (by have := D'.two; omega) (by omega) (by omega) (Nat.le_refl _)
        (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) hσ0 hσN
    · -- el separador `n - 1`
      exact phantomFree_bisectN hl D' C.hsv hv (away_of_local LR j) hmid h (m := j) (a := 0) (b := n) h1
        (by omega) (by omega) (Nat.le_refl _) (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) hσ0 hσN
    · omega

/-- **Toda cadena en orden cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_of_chainOrd (hb : Bounded φ) (C : ChainOrdN φ n zone sv) (T : Int) (hT : 1 ≤ T) :
    PhantomAt φ T := by
  have cs : ∀ j p : Nat, clauseStep φ j p = 2 * (φ.nVars : Int) + 2 + 3 * (j : Int) + (p : Int) := fun _ _ => rfl
  have hm : midFusion φ = 2 * (φ.nVars : Int) + 1 := rfl
  have hft : fusionTop φ = 2 * (φ.nVars : Int) + 3 * (n : Int) + 2 := by simp only [fusionTop, C.len]
  have two := C.D.two
  by_cases hlow : T + 1 ≤ midFusion φ + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  rw [hm] at hlow
  by_cases hin : T ≤ clauseStep φ (n - 1) 2
  · -- la cláusula de la línea, y su prefijo
    rw [cs] at hin
    have hj : ((T - (2 * (φ.nVars : Int) + 2)) / 3).toNat < n := by omega
    have h0 : clauseStep φ ((T - (2 * (φ.nVars : Int) + 2)) / 3).toNat 0 ≤ T := by rw [cs]; omega
    have h2 : T ≤ clauseStep φ ((T - (2 * (φ.nVars : Int) + 2)) / 3).toNat 2 := by rw [cs]; omega
    refine phantomAt_of_prefix hb (j := ((T - (2 * (φ.nVars : Int) + 2)) / 3).toNat + 1) ?_
      (phantomAt_ordLine hb C hj h0 h2 hT)
    rw [cs] at h2
    simp only [fusionTop, prefixCnf, List.length_take, C.len]
    omega
  · -- después de la última cláusula
    rw [cs] at hin
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

end Lines

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {n : Nat} {zone sv : Nat → Nat}

/-- **La máquina `:on` es exacta en toda cadena en orden, de cualquier longitud.** -/
theorem machineExact_of_chainOrd (hb : Bounded φ) (C : ChainOrdN φ n zone sv) : MachineExact φ :=
  (machineExact_iff hb).2 (phantomAt_of_chainOrd hb C)

/-- **La espina `:on` decide toda cadena en orden.** -/
theorem spineVerdictOn_iff_of_chainOrd (hb : Bounded φ) (C : ChainOrdN φ n zone sv) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hb (phantomAt_of_chainOrd hb C)

/-- **El lector por separadores no se atasca en ninguna cadena en orden, de cualquier longitud y en cualquier orden de
los separadores.** Sin hipótesis. -/
theorem reader_sep_of_chainOrd (hb : Bounded φ) (C : ChainOrdN φ n zone sv) {ord : List Nat}
    (hord : ∀ q ∈ ord, 1 ≤ q ∧ q < n) (hall : ∀ q, 1 ≤ q → q < n → q ∈ ord) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g')
    (hsf : SepFirst φ (ord.map sv) R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_sep_local hb C.D C.hsv (localReads_of C.hsv C.num C.lit) (fun c hc => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      have hjl : j < n := by
        rw [← C.len]
        by_cases h : j < φ.clauses.length
        · exact h
        · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
      exact ⟨j, hjl, C.blk j c hj⟩)
    hord hall (fun T hT => phantomAtW_of_phantomAt (phantomAt_of_chainOrd hb C T hT)) hkv hr hsf

end MachineOn

end AbsSatBingo.Model
