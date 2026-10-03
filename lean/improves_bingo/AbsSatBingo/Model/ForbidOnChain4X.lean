-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4X.lean
import AbsSatBingo.Model.ForbidOnChain4W

/-!
# `chain4_cross`: la fórmula medida, sin reordenar

`ForbidOnChain4L` deja las líneas con `v` dentro de un bloque a `OnceNotLast` (la cláusula de `v` aún no se exige).
Con el testigo de la ventana (`ForbidOnChain4W`) basta otra cosa: que la ventana del bloque `{s1} ∪ M ∪ {s2}` esté
por debajo de todo paso que lee `v` (`InnerWL`), y entonces vale `phantomFree_chain4_C` / `_N` en esa línea. Cubre el
tercer literal de la última cláusula de `chain4_cross` (la variable 9 del `.cnf`), que `OnceNotLast` no cubría.

* `req_lit`, `step_lit`: el paso de la línea es de una cláusula cuyo literal lee `v`.
* **`Chain4L2 φ`**, **`phantomAt_of_chain4L2`**, `machineExact_of_chain4L2`, `reader_on_chain4L2R`.
* **`chain4Cross`** (= `scripts/cnf/chain4_cross.cnf`): **`machineExact_chain4Cross`** y **`reader_chain4Cross_any`**
  (el lector no se atasca con cualquier orden), sin ninguna hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- `v` está en `C` o en `N` de una cadena con la ventana de `{s1} ∪ M ∪ {s2}` por debajo de todo paso que lee `v`. -/
def InnerWL (φ : Cnf) (v : Nat) : Prop :=
  ∃ s1 s2 s3 A M N C, Chain4Data φ s1 s2 s3 A M N C ∧ (C v ∨ N v) ∧
    ∃ k, 0 ≤ k ∧ ReadsAt φ k s1 ∧ ReadsAt φ k s2 ∧
      ∀ (j : Nat) (c : Clause) (p : Nat), φ.clauses[j]? = some c → p < 3 → (litAt c p).v = v → k < clauseStep φ j p

/-- **`Chain4L2 φ`**: como `Chain4L`, y además las variables `InnerWL`. -/
def Chain4L2 (φ : Cnf) : Prop := ∀ v, Struct4 φ v ∨ OnceNotLast φ v ∨ InnerWL φ v

theorem chain4L2_of_chain4L (h : Chain4L φ) : Chain4L2 φ := by
  intro v
  rcases h v with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl h)

/-- El requisito de un nodo de la zona de cláusulas lee el literal de su paso. -/
theorem req_lit (hb : Bounded φ) {d r : NodeId} {v : Nat} (hr : r ∈ reqOf φ d) (hv : stepVar φ r.step = some v)
    (hlo : midFusion φ < d.step) :
    ∃ j c p, φ.clauses[j]? = some c ∧ p < 3 ∧ d.step = clauseStep φ j p ∧ (litAt c p).v = v := by
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
    exact ⟨j, c, p, hj, hp, e, Option.some.inj hv⟩
  · rw [reqOf_above φ d e] at hr; exact absurd hr List.not_mem_nil

/-- El paso nuevo de una línea de la zona de cláusulas lee el literal de su cláusula. -/
theorem step_lit {T : Int} {v : Nat} (hv : stepVar φ T = some v) (hlo : midFusion φ < T) :
    ∃ j c p, φ.clauses[j]? = some c ∧ p < 3 ∧ T = clauseStep φ j p ∧ (litAt c p).v = v := by
  rcases step_cases φ T with h0 | ⟨_, _, e⟩ | ⟨_, _, e⟩ | e | ⟨j, p, c, hp, _, hj, e⟩ | e
  · simp only [midFusion] at hlo; omega
  · simp only [varStep, midFusion] at e hlo; omega
  · simp only [negStep, midFusion] at e hlo; omega
  · omega
  · rw [e, stepVar_clause hj p hp] at hv
    exact ⟨j, c, p, hj, hp, e, Option.some.inj hv⟩
  · exfalso
    have h1 : ¬ T ≤ 0 := by simp only [fusionTop] at e; omega
    have h2 : ¬ T < midFusion φ := by omega
    have h3 : ¬ T = midFusion φ := by omega
    simp only [stepVar, if_neg h1, if_neg h2, if_neg h3, if_pos e] at hv
    cases hv

namespace GPathB

variable {P0 P : Assign → Prop} {Nn σ : Int}

/-- Sin familias fantasma con `v` `InnerWL`, si la ventana está por debajo del tope. -/
theorem phantomFree_innerWL {v : Nat} (hl : LocPair φ P0 P σ) (hv : stepVar φ σ = some v)
    {s1 s2 s3 : Nat} {A M N C : Nat → Prop} (D : Chain4Data φ s1 s2 s3 A M N C) (hcn : C v ∨ N v) {k : Int}
    (hk0 : 0 ≤ k) (hk1 : ReadsAt φ k s1) (hk2 : ReadsAt φ k s2) (hkN : k < Nn) (hσ0 : 0 ≤ σ) (hσN : σ < Nn)
    (hN : midFusion φ < Nn) : PhantomFree φ P0 P Nn σ := by
  rcases hcn with hc | hn
  · exact phantomFree_chain4_C hl D hv hc hk0 hkN hk1 hk2 hσ0 hσN hN
  · exact phantomFree_chain4_N hl D hv hn hk0 hkN hk1 hk2 hσ0 hσN hN

open Driver Machine MachineOn

/-- **Toda fórmula `Chain4L2` cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_of_chain4L2 (hb : Bounded φ) (hcl : Chain4L2 φ) (T : Int) (hT : 1 ≤ T) : PhantomAt φ T := by
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
    · obtain ⟨r1, r2⟩ := reqOf_range hb r hr
      rw [hds] at r2
      cases hv : stepVar φ r.step with
      | none => exact phantomFree_none (locPair_filter T k r) hv (by omega) r2
      | some v =>
        rcases hcl v with h | h | ⟨s1, s2, s3, A, M, N, C, D, hcn, kk, hk0, hk1, hk2, hkl⟩
        · exact phantomFree_of_struct4 (locPair_filter T k r) hv h (by omega) r2 (by omega)
        · have hf := freeBelow_filter hb hr hv h (by omega)
          rw [hds] at hf
          exact phantomFree_free_filter hv hf (by omega) r2
        · obtain ⟨j, c, p, hj, hp, e, hpv⟩ := req_lit hb hr hv (by omega)
          have := hkl j c p hj hp hpv
          exact phantomFree_innerWL (locPair_filter T k r) hv D hcn hk0 hk1 hk2 (by omega) (by omega) r2
            (by omega)
    · cases hv : stepVar φ T with
      | none => exact phantomFree_none (locPair_up hb T k d) hv (by omega) (show T < T + 1 by omega)
      | some v =>
        rcases hcl v with h | h | ⟨s1, s2, s3, A, M, N, C, D, hcn, kk, hk0, hk1, hk2, hkl⟩
        · exact phantomFree_of_struct4 (locPair_up hb T k d) hv h (by omega) (by omega) (by omega)
        · exact phantomFree_free_up hb hv (freeBelow_up hv h (by omega)) (by omega)
        · obtain ⟨j, c, p, hj, hp, e, hpv⟩ := step_lit hv (by omega)
          have := hkl j c p hj hp hpv
          exact phantomFree_innerWL (locPair_up hb T k d) hv D hcn hk0 hk1 hk2 (by omega) (by omega) (by omega)
            (by omega)

end GPathB

namespace MachineOn

open GPathB Driver Machine

theorem spineVerdictOn_iff_of_chain4L2 (hbd : Bounded φ) (hcl : Chain4L2 φ) : SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hbd (phantomAt_of_chain4L2 hbd hcl)

theorem machineExact_of_chain4L2 (hbd : Bounded φ) (hcl : Chain4L2 φ) : MachineExact φ :=
  (machineExact_iff hbd).2 (phantomAt_of_chain4L2 hbd hcl)

/-- **El lector no se atasca, con cualquier orden de lectura**, en toda fórmula `Chain4L2` y `Chain4R`. -/
theorem reader_on_chain4L2R (hbd : Bounded φ) (hL : Chain4L2 φ) (hR : Chain4R φ) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on hbd (phantomAt_of_chain4L2 hbd hL) (fun k => hRead_of_chain4R hR k) hkv hr

end MachineOn

-- ============================================================
-- `chain4_cross`
-- ============================================================

/-- **`chain4_cross`** (`scripts/cnf/chain4_cross.cnf`, variables desde 0):
`(x0 ∨ x2 ∨ x5) ∧ (¬x5 ∨ x4 ∨ x6) ∧ (¬x6 ∨ x1 ∨ x7) ∧ (¬x7 ∨ x3 ∨ x8)`. -/
def chain4Cross : Cnf :=
  ⟨9, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩, ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩, ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩,
    ⟨⟨7, false⟩, ⟨3, true⟩, ⟨8, true⟩⟩]⟩

theorem bounded_chain4Cross : Bounded chain4Cross := by
  intro c hc
  simp only [chain4Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Clause.Bounded, chain4Cross]

theorem chain4Data_chain4Cross : Chain4Data chain4Cross 5 6 7 (fun z => z = 0 ∨ z = 2) (fun z => z = 4)
    (fun z => z = 1) (fun z => z = 3 ∨ z = 8) := by
  refine ⟨by decide, by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, fun z a b => by omega,
    fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
    fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
    fun z1 z2 a b => by omega, fun c hc => ?_⟩
  simp only [chain4Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (by simp [ClIn]))
  · exact Or.inr (Or.inr (Or.inl (by simp [ClIn])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [ClIn]))))

theorem chain4Data_chain4Cross_rev : Chain4Data chain4Cross 7 6 5 (fun z => z = 3 ∨ z = 8) (fun z => z = 1)
    (fun z => z = 4) (fun z => z = 0 ∨ z = 2) := by
  refine ⟨by decide, by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, fun z a b => by omega,
    fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
    fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
    fun z1 z2 a b => by omega, fun c hc => ?_⟩
  simp only [chain4Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn]))))
  · exact Or.inr (Or.inr (Or.inl (by simp [ClIn])))
  · exact Or.inr (Or.inl (by simp [ClIn]))

theorem clauses_chain4Cross {j : Nat} {c : Clause} (hj : chain4Cross.clauses[j]? = some c) :
    (j = 0 ∧ c = ⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩) ∨ (j = 1 ∧ c = ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩) ∨
      (j = 2 ∧ c = ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩) ∨ (j = 3 ∧ c = ⟨⟨7, false⟩, ⟨3, true⟩, ⟨8, true⟩⟩) := by
  match j, hj with
  | 0, hj => simp [chain4Cross] at hj; exact Or.inl ⟨rfl, hj.symm⟩
  | 1, hj => simp [chain4Cross] at hj; exact Or.inr (Or.inl ⟨rfl, hj.symm⟩)
  | 2, hj => simp [chain4Cross] at hj; exact Or.inr (Or.inr (Or.inl ⟨rfl, hj.symm⟩))
  | 3, hj => simp [chain4Cross] at hj; exact Or.inr (Or.inr (Or.inr ⟨rfl, hj.symm⟩))
  | _ + 4, hj => simp [chain4Cross] at hj

theorem onceNotLast_chain4Cross {v : Nat} (h5 : v ≠ 5) (h6 : v ≠ 6) (h7 : v ≠ 7) (h8 : v ≠ 8) :
    OnceNotLast chain4Cross v := by
  intro j c hj hcv
  rcases clauses_chain4Cross hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [ClVar] at hcv
    refine ⟨by simp; omega, fun j' c' hj' hcv' => ?_⟩
    rcases clauses_chain4Cross hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [ClVar] at hcv'; omega

theorem struct4_chain4Cross_sep {v : Nat} (h : v = 5 ∨ v = 6 ∨ v = 7) : Struct4 chain4Cross v := by
  rcases h with rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, chain4Data_chain4Cross_rev⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, chain4Data_chain4Cross⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, chain4Data_chain4Cross⟩))

theorem struct4_chain4Cross_out {v : Nat} (h : 9 ≤ v) : Struct4 chain4Cross v := by
  refine Or.inl ⟨v, fun _ => False, fun _ => False, ⟨fun h => absurd rfl h, fun h => h, fun _ h _ => h, Or.inl rfl,
    fun _ _ _ h _ _ _ _ _ => h, fun _ _ _ h _ _ _ _ _ => h, fun h => absurd rfl h, fun c hc => ?_⟩⟩
  simp only [chain4Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩

theorem win_chain4Cross_56 :
    ReadsAt chain4Cross (clauseStep chain4Cross 1 2) 5 ∧ ReadsAt chain4Cross (clauseStep chain4Cross 1 2) 6 := by
  have hj : chain4Cross.clauses[1]? = some ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩ := rfl
  refine ⟨⟨clauseStep chain4Cross 1 0, Or.inr (Or.inr ⟨by simp [clauseStep, chain4Cross],
    by simp [clauseStep, chain4Cross]⟩), stepVar_clause hj 0 (by omega)⟩,
    ⟨clauseStep chain4Cross 1 2, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩⟩

theorem win_chain4Cross_76 :
    ReadsAt chain4Cross (clauseStep chain4Cross 2 2) 7 ∧ ReadsAt chain4Cross (clauseStep chain4Cross 2 2) 6 := by
  have hj : chain4Cross.clauses[2]? = some ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩ := rfl
  refine ⟨⟨clauseStep chain4Cross 2 2, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩,
    ⟨clauseStep chain4Cross 2 0, Or.inr (Or.inr ⟨by simp [clauseStep, chain4Cross],
      by simp [clauseStep, chain4Cross]⟩), stepVar_clause hj 0 (by omega)⟩⟩

/-- Las líneas: `x8` (el tercer literal de la última cláusula) por la ventana de `(¬x5 ∨ x4 ∨ x6)`, que va antes. -/
theorem chain4L2_chain4Cross : Chain4L2 chain4Cross := by
  intro v
  by_cases hs : v = 5 ∨ v = 6 ∨ v = 7
  · exact Or.inl (struct4_chain4Cross_sep hs)
  by_cases h9 : 9 ≤ v
  · exact Or.inl (struct4_chain4Cross_out h9)
  by_cases h8 : v = 8
  · subst h8
    refine Or.inr (Or.inr ⟨_, _, _, _, _, _, _, chain4Data_chain4Cross, Or.inl (Or.inr rfl),
      clauseStep chain4Cross 1 2, by simp [clauseStep, chain4Cross], win_chain4Cross_56.1, win_chain4Cross_56.2,
      fun j c p hj hp hpv => ?_⟩)
    rcases clauses_chain4Cross hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · match p, hp with
      | 0, _ => simp [litAt] at hpv
      | 1, _ => simp [litAt] at hpv
      | 2, _ => first | (simp [litAt] at hpv; done) | simp [clauseStep, chain4Cross]
  · exact Or.inr (Or.inl (onceNotLast_chain4Cross (by omega) (by omega) (by omega) h8))

/-- La lectura: como `fourChainL`. -/
theorem chain4R_chain4Cross : Chain4R chain4Cross := by
  intro v
  by_cases hs : v = 5 ∨ v = 6 ∨ v = 7
  · exact Or.inl (struct4_chain4Cross_sep hs)
  by_cases h9 : 9 ≤ v
  · exact Or.inl (struct4_chain4Cross_out h9)
  by_cases hr : v = 1 ∨ v = 3 ∨ v = 8
  · refine Or.inr ⟨_, _, _, _, _, _, _, ⟨chain4Data_chain4Cross, clauseStep chain4Cross 1 2,
      by simp [clauseStep, chain4Cross], by simp [clauseStep, fusionTop, chain4Cross], win_chain4Cross_56⟩, ?_⟩
    rcases hr with h | h | h
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · refine Or.inr ⟨_, _, _, _, _, _, _, ⟨chain4Data_chain4Cross_rev, clauseStep chain4Cross 2 2,
      by simp [clauseStep, chain4Cross], by simp [clauseStep, fusionTop, chain4Cross], win_chain4Cross_76⟩, ?_⟩
    by_cases h4 : v = 4
    · exact Or.inr h4
    · exact Or.inl (by omega)

namespace MachineOn

open GPathB Driver Machine

/-- **La máquina `:on` es exacta en `chain4_cross`**, la fórmula medida, sin ninguna hipótesis. -/
theorem machineExact_chain4Cross : MachineExact chain4Cross :=
  machineExact_of_chain4L2 bounded_chain4Cross chain4L2_chain4Cross

/-- **El lector no se atasca en `chain4_cross` con cualquier orden de lectura**, sin ninguna hipótesis. -/
theorem reader_chain4Cross_any {kv : NodeId × GPathB} (hkv : kv ∈ runM .on chain4Cross) {R : List NodeId}
    {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a chain4Cross ∧ (∀ r ∈ R, selOfAssign chain4Cross a r.step = r) ∧
      CT g' (pidOfAssign chain4Cross a) :=
  reader_on_chain4L2R bounded_chain4Cross chain4L2_chain4Cross chain4R_chain4Cross hkv hr

end MachineOn

end AbsSatBingo.Model
