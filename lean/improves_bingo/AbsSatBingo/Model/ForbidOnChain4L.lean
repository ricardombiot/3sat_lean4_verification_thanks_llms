-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4L.lean
import AbsSatBingo.Model.ForbidOnChain4

/-!
# Las líneas solo exigen el prefijo: cuatro bloques en las líneas de la máquina

Las familias de una línea (`SolE φ T k`) solo exigen las ventanas por debajo de `T`. `probe_hard4.jl` mide en
`chain4_cross` que los triángulos del caso abierto de `ForbidOnChain4` (`v` dentro de un bloque) solo aparecen, para la
variable del paso fijado, en líneas donde la cláusula de `v` aún no se exige. Aquí se demuestra lo que eso da:

* **`FreeBelow φ v B`**: toda cláusula que contiene `v` tiene su ventana en el paso `B` o después.
* `validUpTo_patch_free`: cambiar solo `v` no pisa ninguna ventana prohibida por debajo de `B`.
* **`phantomFree_free_filter`**, **`phantomFree_free_up`**: con la variable del paso fijado libre en el prefijo,
  sin familias fantasma, por el parche de una sola variable (`helly4_of_patch` con `B = {v}`).
* **`OnceNotLast φ v`**: `v` está a lo sumo en una cláusula y no es su tercer literal. Entonces en las líneas en que se
  fija `v` su cláusula aún no se exige (`freeBelow_filter`, `freeBelow_up`).
* **`Chain4L φ`**: cada variable tiene separador (`SepData`), datos de cadena de tres (`ChainData`), es separador de
  una cadena de cuatro (`Chain4At`), o `OnceNotLast`. **`phantomAt_of_chain4L`**: la condición fuerte en todas las
  líneas, sin hipótesis sobre la máquina y con cualquier numeración; **`spineVerdictOn_iff_of_chain4L`**,
  **`machineExact_of_chain4L`**.
* `fourChainL` (`chain4_cross` con la última cláusula reordenada para que su tercer literal sea el separador):
  `machineExact_fourChainL`.

**El lector no está cubierto.** La lectura (`HRead`) trabaja sobre el estado final, que exige todas las cláusulas, y
`OnceNotLast` no le sirve: ahí sigue abierto el caso de `v` dentro de un bloque. `reader_on_chain4L` lo deja como
hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

-- ============================================================
-- Una variable libre en el prefijo
-- ============================================================

/-- **`FreeBelow φ v B`**: toda cláusula que contiene `v` tiene su ventana en el paso `B` o después. -/
def FreeBelow (φ : Cnf) (v : Nat) (B : Int) : Prop :=
  ∀ j c, φ.clauses[j]? = some c → ClVar c v → B ≤ clauseStep φ j 2

/-- **Cambiar solo `v` no pisa ventanas prohibidas** por debajo de `B`, si `v` está libre ahí. -/
theorem validUpTo_patch_free {v : Nat} {B : Int} (hf : FreeBelow φ v B) {a' a0 : Assign} (h0 : ValidUpTo φ a0 B) :
    ValidUpTo φ (patch (fun z => z = v) a' a0) B := by
  intro k hk
  cases hp : isProhibited φ (pidOfAssign φ (patch (fun z => z = v) a' a0) k) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨j, c, hj, e, m1, m2, m3⟩ := prohibited_clause hp
    have out : ∀ {z : Nat}, ClVar c z → patch (fun z => z = v) a' a0 z = a0 z := by
      intro z hz
      refine patch_out (fun hzv => ?_)
      subst hzv
      have := hf j c hj hz
      omega
    have pr := prohibited_of_false (a := a0) hj ((litVal_congr (out (Or.inl rfl)).symm).trans m1)
      ((litVal_congr (out (Or.inr (Or.inl rfl))).symm).trans m2) ((litVal_congr (out (Or.inr (Or.inr rfl))).symm).trans m3)
    rw [← e, h0 k hk] at pr
    cases pr

/-- En un paso que no lee `v`, el parche elige lo que elige `a0`; en uno que lee `v`, lo que elige `a'`. -/
theorem sel_patch_v_in {v : Nat} {k : Int} (hk : stepVar φ k = some v) (a' a0 : Assign) :
    selOfAssign φ (patch (fun z => z = v) a' a0) k = selOfAssign φ a' k :=
  sel_eq_of_var (fun z hz => by rw [hk] at hz; cases hz; exact patch_in rfl)

/-- Un paso que lee `v`, con `v` libre por encima de él, no es el tercero de una cláusula: nunca está prohibido. -/
theorem not_prohibited_free {v : Nat} {T : Int} (hv : stepVar φ T = some v) (hf : FreeBelow φ v (T + 1))
    (a : Assign) : isProhibited φ (pidOfAssign φ a T) = false := by
  cases hp : isProhibited φ (pidOfAssign φ a T) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨j, c, hj, e, _⟩ := prohibited_clause hp
    have h3 : stepVar φ T = some c.l3.v := by rw [e]; exact stepVar_clause hj 2 (by omega)
    rw [hv] at h3
    have := hf j c hj (Or.inr (Or.inr (Option.some.inj h3)))
    omega

namespace GPathB

/-- **El filtro, con la variable fijada libre en el prefijo**: sin familias fantasma. -/
theorem phantomFree_free_filter {T : Int} {k r : NodeId} {v : Nat} (hv : stepVar φ r.step = some v)
    (hf : FreeBelow φ v T) (hσ0 : 0 ≤ r.step) (hσN : r.step < T) :
    PhantomFree φ (SolE φ T k) (fun a => SolE φ T k a ∧ selOfAssign φ a r.step = r) T r.step := by
  refine phantomFree_of_helly4 hσ0 hσN (helly4_of_patch (fun z => z = v)
    (fun z1 z2 _ h1 h2 _ d _ _ => absurd (h1.trans h2.symm) d) (fun a0 a' h0 h' => ?_))
  exact ⟨⟨validUpTo_patch_free hf h0.1, sel_patch_both _ h'.1.2 h0.2⟩, (sel_patch_v_in hv a' a0).trans h'.2⟩

/-- **El UP, con la variable del paso nuevo libre en el prefijo** (también en la ventana del paso nuevo): sin familias
fantasma, en la condición fuerte. -/
theorem phantomFree_free_up (hb : Bounded φ) {T : Int} {k d : NodeId} {v : Nat} (hv : stepVar φ T = some v)
    (hf : FreeBelow φ v (T + 1)) (hT : 0 ≤ T) :
    PhantomFree φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
      (fun a => SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) (T + 1) T := by
  refine phantomFree_of_helly4 hT (by omega) (helly4_of_patch (fun z => z = v)
    (fun z1 z2 _ h1 h2 _ d _ _ => absurd (h1.trans h2.symm) d) (fun a0 a' h0 h' => ?_))
  have _ := hb
  refine ⟨⟨fun q hq => ?_, ?_⟩, sel_patch_both _ h'.2 h0.1.2⟩
  · by_cases e : q = T
    · rw [e]; exact not_prohibited_free hv hf _
    · exact validUpTo_patch_free (fun j c hj hc => by have := hf j c hj hc; omega) h0.1.1 q (by omega)
  · show selOfAssign φ _ (T + 1 - 1) = d
    rw [Int.add_sub_cancel, sel_patch_v_in hv a' a0]
    have := h'.1.2
    rwa [Int.add_sub_cancel] at this

end GPathB

-- ============================================================
-- Una variable en una sola cláusula, no en su tercer literal
-- ============================================================

/-- **`OnceNotLast φ v`**: `v` está a lo sumo en una cláusula, y no es su tercer literal. -/
def OnceNotLast (φ : Cnf) (v : Nat) : Prop :=
  ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → ClVar c v →
    c.l3.v ≠ v ∧ ∀ (j' : Nat) (c' : Clause), φ.clauses[j']? = some c' → ClVar c' v → j' = j

theorem litAt_clVar (c : Clause) (p : Nat) : ClVar c (litAt c p).v := by
  match p with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | _ + 2 => exact Or.inr (Or.inr rfl)

/-- Si el paso `T` de la cláusula `j` lee `v` y `v` cumple `OnceNotLast`, la cláusula de `v` tiene su ventana
después de `T`. -/
theorem freeBelow_of_clauseStep {v j p : Nat} {c : Clause} (h : OnceNotLast φ v) (hj : φ.clauses[j]? = some c)
    (hp : p < 3) (hpv : (litAt c p).v = v) : FreeBelow φ v (clauseStep φ j p + 1) := by
  have hcv : ClVar c v := hpv ▸ litAt_clVar c p
  obtain ⟨h3, huniq⟩ := h j c hj hcv
  have hp2 : p ≠ 2 := by
    intro e; subst e; exact h3 hpv
  intro j' c' hj' hc'
  have := huniq j' c' hj' hc'
  subst this
  simp only [clauseStep]; omega

theorem stepVar_binStep {l : Lit} (hl : l.v < φ.nVars) : stepVar φ l.binStep = some l.v := by
  have h0 : ¬ l.binStep ≤ 0 := by simp only [Lit.binStep]; split <;> omega
  have h1 : l.binStep < midFusion φ := by simp only [Lit.binStep, midFusion]; split <;> omega
  simp only [stepVar, if_neg h0, if_pos h1]
  congr 1
  simp only [varOfStep, Lit.binStep]; split <;> omega

/-- **El filtro**: el requisito de un nodo del paso `T` lee la variable del literal de `T`; con `OnceNotLast`, esa
variable está libre por debajo de `T`. -/
theorem freeBelow_filter (hb : Bounded φ) {d r : NodeId} {v : Nat} (hr : r ∈ reqOf φ d)
    (hv : stepVar φ r.step = some v) (h : OnceNotLast φ v) (hlo : midFusion φ < d.step) : FreeBelow φ v d.step := by
  rcases step_cases φ d.step with h0 | ⟨_, _, e⟩ | ⟨_, _, e⟩ | e | ⟨j, p, c, hp, hjlt, hj, e⟩ | e
  · simp only [midFusion] at hlo; omega
  · simp only [varStep, midFusion] at e hlo; omega
  · simp only [negStep, midFusion] at e hlo; omega
  · omega
  · rw [reqOf_clause φ d j p c hp hjlt hj e, List.mem_singleton] at hr
    subst hr
    have hlv : (litAt c p).v < φ.nVars := by
      obtain ⟨b1, b2, b3⟩ := hb c (List.mem_of_getElem? hj)
      match p, hp with
      | 0, _ => exact b1
      | 1, _ => exact b2
      | 2, _ => exact b3
    rw [stepVar_binStep hlv] at hv
    have := freeBelow_of_clauseStep h hj hp (Option.some.inj hv)
    intro j' c' hj' hc'
    have := this j' c' hj' hc'
    omega
  · rw [reqOf_above φ d e] at hr; exact absurd hr List.not_mem_nil

/-- **El UP**: con `OnceNotLast`, la variable del paso nuevo está libre hasta el paso nuevo incluido. -/
theorem freeBelow_up {T : Int} {v : Nat} (hv : stepVar φ T = some v) (h : OnceNotLast φ v) (hlo : midFusion φ < T) :
    FreeBelow φ v (T + 1) := by
  rcases step_cases φ T with h0 | ⟨_, _, e⟩ | ⟨_, _, e⟩ | e | ⟨j, p, c, hp, _, hj, e⟩ | e
  · simp only [midFusion] at hlo; omega
  · simp only [varStep, midFusion] at e hlo; omega
  · simp only [negStep, midFusion] at e hlo; omega
  · omega
  · rw [e, stepVar_clause hj p hp] at hv
    rw [e]; exact freeBelow_of_clauseStep h hj hp (Option.some.inj hv)
  · exfalso
    have h1 : ¬ T ≤ 0 := by simp only [fusionTop] at e; omega
    have h2 : ¬ T < midFusion φ := by omega
    have h3 : ¬ T = midFusion φ := by omega
    simp only [stepVar, if_neg h1, if_neg h2, if_neg h3, if_pos e] at hv
    cases hv

-- ============================================================
-- La clase y las líneas
-- ============================================================

/-- `v` es separador de una cadena de cuatro bloques: `s3` (o `s1`, leyendo al revés) o `s2`. -/
def Chain4At (φ : Cnf) (v : Nat) : Prop :=
  (∃ s1 s2 A M N C, Chain4Data φ s1 s2 v A M N C) ∨ (∃ s1 s3 A M N C, Chain4Data φ s1 v s3 A M N C)

/-- **`Chain4L φ`**: cada variable tiene separador, datos de cadena de tres, es separador de una cadena de cuatro, o
está en una sola cláusula sin ser su tercer literal. -/
def Chain4L (φ : Cnf) : Prop :=
  ∀ v, (∃ s L Rr, SepData φ v s L Rr) ∨ (∃ s1 s2 A M C, ChainData φ v s1 s2 A M C) ∨ Chain4At φ v ∨
    OnceNotLast φ v

namespace GPathB

variable {P0 P : Assign → Prop} {N σ : Int}

/-- Sin familias fantasma para un par local, cuando la variable fijada no es `OnceNotLast`. -/
theorem phantomFree_of_struct4 {v : Nat} (hl : LocPair φ P0 P σ) (hv : stepVar φ σ = some v)
    (h : (∃ s L Rr, SepData φ v s L Rr) ∨ (∃ s1 s2 A M C, ChainData φ v s1 s2 A M C) ∨ Chain4At φ v)
    (hσ0 : 0 ≤ σ) (hσN : σ < N) (hN : midFusion φ < N) : PhantomFree φ P0 P N σ := by
  rcases h with ⟨s, L, Rr, D⟩ | ⟨s1, s2, A, M, C, D⟩ | ⟨s1, s2, A, M, Nn, C, D⟩ | ⟨s1, s3, A, M, Nn, C, D⟩
  · exact phantomFree_sepData hl D hv hσ0 hσN hN
  · exact phantomFree_chainData hl D hv hσ0 hσN hN
  · exact phantomFree_chain4_s3 hl D hv hσ0 hσN hN
  · exact phantomFree_chain4_s2 hl D hv hσ0 hσN hN

open Driver Machine MachineOn

/-- **Toda fórmula `Chain4L` cumple la condición fuerte en todas sus líneas**, con cualquier numeración. -/
theorem phantomAt_of_chain4L (hb : Bounded φ) (hcl : Chain4L φ) (T : Int) (hT : 1 ≤ T) : PhantomAt φ T := by
  by_cases hlow : T + 1 ≤ midFusion φ + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  · intro k d hk hd
    have hds : d.step = T := by
      have := sonsOfMap_step φ k d hd
      have hks := mapNodes_step φ (T - 1) k hk
      omega
    refine ⟨fun r hr => ?_, ?_⟩
    · -- el filtro
      obtain ⟨r1, r2⟩ := reqOf_range hb r hr
      rw [hds] at r2
      cases hv : stepVar φ r.step with
      | none => exact phantomFree_none (locPair_filter T k r) hv (by omega) r2
      | some v =>
        rcases hcl v with h | h | h | h
        · exact phantomFree_of_struct4 (locPair_filter T k r) hv (Or.inl h) (by omega) r2 (by omega)
        · exact phantomFree_of_struct4 (locPair_filter T k r) hv (Or.inr (Or.inl h)) (by omega) r2 (by omega)
        · exact phantomFree_of_struct4 (locPair_filter T k r) hv (Or.inr (Or.inr h)) (by omega) r2 (by omega)
        · have hf := freeBelow_filter hb hr hv h (by omega)
          rw [hds] at hf
          exact phantomFree_free_filter hv hf (by omega) r2
    · -- el UP
      cases hv : stepVar φ T with
      | none => exact phantomFree_none (locPair_up hb T k d) hv (by omega) (show T < T + 1 by omega)
      | some v =>
        rcases hcl v with h | h | h | h
        · exact phantomFree_of_struct4 (locPair_up hb T k d) hv (Or.inl h) (by omega) (by omega) (by omega)
        · exact phantomFree_of_struct4 (locPair_up hb T k d) hv (Or.inr (Or.inl h)) (by omega) (by omega) (by omega)
        · exact phantomFree_of_struct4 (locPair_up hb T k d) hv (Or.inr (Or.inr h)) (by omega) (by omega) (by omega)
        · exact phantomFree_free_up hb hv (freeBelow_up hv h (by omega)) (by omega)

end GPathB

-- ============================================================
-- Un caso concreto
-- ============================================================

/-- `chain4_cross` (variables desde 0) con la última cláusula reordenada para que su tercer literal sea el separador:
`(x0 ∨ x2 ∨ x5) ∧ (¬x5 ∨ x4 ∨ x6) ∧ (¬x6 ∨ x1 ∨ x7) ∧ (x3 ∨ x8 ∨ ¬x7)`. Numeración cruzada: los bloques son
`{0, 2, 5}`, `{5, 4, 6}`, `{6, 1, 7}`, `{7, 3, 8}`. -/
def fourChainL : Cnf :=
  ⟨9, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩, ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩, ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩,
    ⟨⟨3, true⟩, ⟨8, true⟩, ⟨7, false⟩⟩]⟩

theorem bounded_fourChainL : Bounded fourChainL := by
  intro c hc
  simp only [fourChainL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Clause.Bounded, fourChainL]

/-- La cadena en su orientación: `s1 = 5`, `s2 = 6`, `s3 = 7`. -/
theorem chain4Data_fourChainL : Chain4Data fourChainL 5 6 7 (fun z => z = 0 ∨ z = 2) (fun z => z = 4)
    (fun z => z = 1) (fun z => z = 3 ∨ z = 8) := by
  refine ⟨by decide, by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, fun z a b => by omega,
    fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
    fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
    fun z1 z2 a b => by omega, fun c hc => ?_⟩
  simp only [fourChainL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (by simp [ClIn]))
  · exact Or.inr (Or.inr (Or.inl (by simp [ClIn])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [ClIn]))))

/-- La misma cadena leída al revés: `s1 = 7`, `s2 = 6`, `s3 = 5`. -/
theorem chain4Data_fourChainL_rev : Chain4Data fourChainL 7 6 5 (fun z => z = 3 ∨ z = 8) (fun z => z = 1)
    (fun z => z = 4) (fun z => z = 0 ∨ z = 2) := by
  refine ⟨by decide, by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, fun z a b => by omega,
    fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
    fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
    fun z1 z2 a b => by omega, fun c hc => ?_⟩
  simp only [fourChainL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inl (by simp [ClIn])))
  · exact Or.inr (Or.inl (by simp [ClIn]))

theorem clauses_fourChainL {j : Nat} {c : Clause} (hj : fourChainL.clauses[j]? = some c) :
    (j = 0 ∧ c = ⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩) ∨ (j = 1 ∧ c = ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩) ∨
      (j = 2 ∧ c = ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩) ∨ (j = 3 ∧ c = ⟨⟨3, true⟩, ⟨8, true⟩, ⟨7, false⟩⟩) := by
  match j, hj with
  | 0, hj => simp [fourChainL] at hj; exact Or.inl ⟨rfl, hj.symm⟩
  | 1, hj => simp [fourChainL] at hj; exact Or.inr (Or.inl ⟨rfl, hj.symm⟩)
  | 2, hj => simp [fourChainL] at hj; exact Or.inr (Or.inr (Or.inl ⟨rfl, hj.symm⟩))
  | 3, hj => simp [fourChainL] at hj; exact Or.inr (Or.inr (Or.inr ⟨rfl, hj.symm⟩))
  | _ + 4, hj => simp [fourChainL] at hj

/-- Las variables que no son separadores están en una sola cláusula y no son su tercer literal. -/
theorem onceNotLast_fourChainL {v : Nat} (h5 : v ≠ 5) (h6 : v ≠ 6) (h7 : v ≠ 7) : OnceNotLast fourChainL v := by
  intro j c hj hcv
  rcases clauses_fourChainL hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [ClVar] at hcv
    refine ⟨by simp; omega, fun j' c' hj' hcv' => ?_⟩
    rcases clauses_fourChainL hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [ClVar] at hcv'; omega

theorem chain4L_fourChainL : Chain4L fourChainL := by
  intro v
  by_cases h7 : v = 7
  · subst h7; exact Or.inr (Or.inr (Or.inl (Or.inl ⟨_, _, _, _, _, _, chain4Data_fourChainL⟩)))
  by_cases h6 : v = 6
  · subst h6; exact Or.inr (Or.inr (Or.inl (Or.inr ⟨_, _, _, _, _, _, chain4Data_fourChainL⟩)))
  by_cases h5 : v = 5
  · subst h5; exact Or.inr (Or.inr (Or.inl (Or.inl ⟨_, _, _, _, _, _, chain4Data_fourChainL_rev⟩)))
  exact Or.inr (Or.inr (Or.inr (onceNotLast_fourChainL h5 h6 h7)))

namespace MachineOn

open GPathB Driver Machine

/-- **La espina `:on` decide toda fórmula `Chain4L`**, sin hipótesis sobre la máquina. -/
theorem spineVerdictOn_iff_of_chain4L (hbd : Bounded φ) (hcl : Chain4L φ) : SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hbd (phantomAt_of_chain4L hbd hcl)

/-- **La máquina `:on` es exacta en toda fórmula `Chain4L`.** -/
theorem machineExact_of_chain4L (hbd : Bounded φ) (hcl : Chain4L φ) : MachineExact φ :=
  (machineExact_iff hbd).2 (phantomAt_of_chain4L hbd hcl)

/-- **El lector**, con la hipótesis de la lectura todavía como hipótesis. -/
theorem reader_on_chain4L (hbd : Bounded φ) (hcl : Chain4L φ)
    (HR : ∀ k, HRead φ (stepCount φ) (SolE φ (stepCount φ) k)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on hbd (phantomAt_of_chain4L hbd hcl) HR hkv hr

/-- **Cuatro bloques con numeración cruzada, sin ninguna hipótesis**: la máquina `:on` es exacta en `fourChainL`. -/
theorem machineExact_fourChainL : MachineExact fourChainL :=
  machineExact_of_chain4L bounded_fourChainL chain4L_fourChainL

end MachineOn

end AbsSatBingo.Model
