-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnDescent.lean
import AbsSatBingo.Model.ForbidOnChain

/-!
# El descenso: un rango por triángulo y un solo argumento

`ForbidOnSep` y `ForbidOnChain` suben por niveles escritos a mano: los triángulos con un nodo en tal paso, luego los
que tienen uno en tal otro, luego todos. Aquí los niveles se sustituyen por **un rango** `ρ` sobre los triángulos y un
solo argumento de descenso:

* **`tri_descent`** (sin máquina, sin fórmula). Si cada triángulo de la estructura es de una rama de `P` en cuanto lo
  son todos los de rango menor, todos lo son. Es el contraejemplo mínimo: si hubiera un triángulo fantasma, el de
  rango mínimo tendría por debajo solo triángulos buenos, y el paso lo haría bueno. Se demuestra por inducción sobre
  una cota del rango.
* **`phantomFree_of_descent`**: con eso y las parejas (`pairs_of_struct`), sin familias fantasma.

El rango cuenta qué pasos de variables compartidas toca el triángulo. Un triángulo que no toca el paso `lam` tiene en
`lam` un testigo cuyas tres caras sí lo tocan (`Tri.wit`): por eso el rango baja al pasar a las caras, y el paso solo
tiene que pegar ramas de las caras.

Validación: los dos resultados de bloques compartidos se rehacen con este argumento, cada uno con su rango y
reutilizando los pegados de `ForbidOnSep` y `ForbidOnChain`:

* `phantomFree_sep_desc` (dos bloques; rango `hitRank [lam]`);
* `phantomFree_chainData_desc` (tres bloques; rango `hitRank [lam2, lam1]` con `v` en el último bloque o `v = s2`, y
  `midRank` con `v` en el de en medio);
* `phantomFree_of_chain3_desc`, `phantomAt_of_chain3_desc`, `hRead_of_chain3_desc`, `machineExact_of_chain3_desc`.

**`hitRank S`**: el índice del primer paso de la lista `S` que toca el triángulo (la longitud de `S` si no toca
ninguno). Un triángulo que no toca los `k + 1` primeros tiene en el paso `S[k]` un testigo cuyas caras tienen rango
`≤ k` (`hitRank_face`). Las dos validaciones hacen esa cuenta a mano; `hitRank_face` es la versión para una lista
de cualquier longitud (cadenas más largas).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

namespace GPathB

variable {P0 P : Assign → Prop} {N σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

-- ============================================================
-- El descenso
-- ============================================================

/-- **El descenso** (contraejemplo mínimo). Si cada triángulo es de una rama de `P` en cuanto lo son todos los de
rango menor, todos lo son. -/
theorem tri_descent (ρ : PathNodeId → PathNodeId → PathNodeId → Nat)
    (step : ∀ x u w, Tri R Tf x u w →
      (∀ x' u' w', Tri R Tf x' u' w' → ρ x' u' w' < ρ x u w → TriOf φ P x' u' w') → TriOf φ P x u w) :
    ∀ x u w, Tri R Tf x u w → TriOf φ P x u w := by
  have bound : ∀ n : Nat, ∀ x u w, Tri R Tf x u w → ρ x u w < n → TriOf φ P x u w := by
    intro n
    induction n with
    | zero => intro _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro x u w t h
      exact step x u w t (fun x' u' w' t' h' => ih x' u' w' t' (by omega))
  exact fun x u w t => bound _ x u w t (Nat.lt_succ_self _)

/-- **Sin familias fantasma por descenso**: basta el paso del descenso en cada estructura cerrada. -/
theorem phantomFree_of_descent (hσ0 : 0 ≤ σ) (hσN : σ < N) (ρ : PathNodeId → PathNodeId → PathNodeId → Nat)
    (step : ∀ (R : PathNodeId → PathNodeId → Prop) (Tf : Trios), PhStruct φ P0 N R Tf →
      (∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) →
      ∀ x u w, Tri R Tf x u w →
        (∀ x' u' w', Tri R Tf x' u' w' → ρ x' u' w' < ρ x u w → TriOf φ P x' u' w') → TriOf φ P x u w) :
    PhantomFree φ P0 P N σ := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have hS : PhStruct φ P0 N R Tf := ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩
  refine ⟨pairs_of_struct hσ0 hσN hS hanch, fun x u w a b c d e f g => ?_⟩
  exact tri_descent ρ (step R Tf hS hanch) x u w ⟨a, b, c, d, e, f, g⟩

-- ============================================================
-- El rango por pasos tocados
-- ============================================================

/-- El triángulo toca el paso `lam`: uno de sus nodos está en él. -/
def Hits (lam : Int) (x u w : PathNodeId) : Prop := x.id.step = lam ∨ u.id.step = lam ∨ w.id.step = lam

instance (lam : Int) (x u w : PathNodeId) : Decidable (Hits lam x u w) := by
  unfold Hits; infer_instance

/-- **`hitRank S`**: el índice del primer paso de `S` que toca el triángulo (la longitud de `S` si ninguno). -/
def hitRank : List Int → PathNodeId → PathNodeId → PathNodeId → Nat
  | [], _, _, _ => 0
  | lam :: S, x, u, w => if Hits lam x u w then 0 else hitRank S x u w + 1

theorem hitRank_zero {lam : Int} {S : List Int} {x u w : PathNodeId} (h : Hits lam x u w) :
    hitRank (lam :: S) x u w = 0 := by
  simp only [hitRank, if_pos h]

theorem hitRank_succ {lam : Int} {S : List Int} {x u w : PathNodeId} (h : ¬ Hits lam x u w) :
    hitRank (lam :: S) x u w = hitRank S x u w + 1 := by
  simp only [hitRank, if_neg h]

/-- **La cara baja el rango**: si `t` no toca los `k + 1` primeros pasos de `S`, un triángulo que toca `S[k]` tiene
rango `≤ k < rango de t`. -/
theorem hitRank_face {S : List Int} {k : Nat} (hk : k < S.length) {x u w x' u' w' : PathNodeId}
    (hle : k < hitRank S x u w) (hh : Hits (S[k]'hk) x' u' w') : hitRank S x' u' w' < hitRank S x u w := by
  suffices h : ∀ (S : List Int) (k : Nat) (hk : k < S.length), Hits (S[k]'hk) x' u' w' → hitRank S x' u' w' ≤ k by
    have := h S k hk hh; omega
  intro S
  induction S with
  | nil => intro k hk; simp at hk
  | cons lam S ih =>
    intro k hk hh'
    by_cases h0 : Hits lam x' u' w'
    · rw [hitRank_zero h0]; exact Nat.zero_le _
    · rw [hitRank_succ h0]
      cases k with
      | zero => exact absurd hh' h0
      | succ k =>
        have := ih k (by simp at hk; omega) hh'
        omega

end GPathB

-- ============================================================
-- Validación 1: dos bloques que comparten una variable
-- ============================================================

namespace GPathB

variable {P0 P : Assign → Prop} {N σ : Int}

/-- **`phantomFree_sep` por descenso**, con rango `hitRank [lam]`: los triángulos que tocan el paso de `s` son la base
(el ancla si `lam = σ`, o `tri_lam_any`); los demás, por el pegado de `tri_glue`, cuyas caras tocan `lam`. -/
theorem phantomFree_sep_desc {lam : Int} {s : Nat} {L Rr : Nat → Prop} (hσ0 : 0 ≤ σ) (hσN : σ < N) (hl0 : 0 ≤ lam)
    (hlN : lam < N) (hsl : stepVar φ lam = some s)
    (hL : ∀ z1 z2 z3, L z1 → L z2 → L z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False)
    (hR : ∀ z1 z2 z3, Rr z1 → Rr z2 → Rr z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False)
    (hG : ∀ a0 c c', P0 a0 → P c → P c' → c s = c' s → P (glue s L Rr c c' a0))
    (h0 : lam = σ ∨ ((∀ z1 z2, Rr z1 → Rr z2 → z1 ≠ z2 → stepVar φ σ = some z1 ∨ stepVar φ σ = some z2) ∧
      ∀ a0 a', P0 a0 → P a' → a' s = a0 s → P (patch Rr a' a0))) : PhantomFree φ P0 P N σ := by
  refine phantomFree_of_descent hσ0 hσN (hitRank [lam]) (fun R Tf hS hanch x u w t ih => ?_)
  have base : ∀ x u w, Tri R Tf x u w → Hits lam x u w → TriOf φ P x u w := by
    intro x u w t hh
    rcases h0 with h0 | ⟨hcard, hG0⟩
    · rw [h0] at hh; exact tri_anchor hS hanch x u w t.xu t.xw t.uw t.nxu t.nxw t.nuw t.nf hh
    · exact tri_lam_any hσ0 hσN hsl hcard hG0 hS hanch x u w t.xu t.xw t.uw t.nxu t.nxw t.nuw t.nf hh
  by_cases hh : Hits lam x u w
  · exact base x u w t hh
  · -- rango 1: las caras tocan `lam` y tienen rango 0
    exact tri_glue hl0 hlN hsl hL hR hG hS (fun x' u' w' a b c d e f g hh' => ih x' u' w' ⟨a, b, c, d, e, f, g⟩
      (by rw [hitRank_zero hh', hitRank_succ hh]; omega)) x u w t.xu t.xw t.uw t.nxu t.nxw t.nuw t.nf

-- ============================================================
-- Validación 2: tres bloques en cadena
-- ============================================================

/-- El rango con `v` en el bloque de en medio: `0` si el triángulo tiene el primer nodo en el paso de `s2` y el
tercero en el de `s1`; `1` si toca el paso de `s2`; `2` si no. -/
def midRank (lam1 lam2 : Int) (x u w : PathNodeId) : Nat :=
  if x.id.step = lam2 ∧ w.id.step = lam1 then 0 else if Hits lam2 x u w then 1 else 2

/-- **`phantomFree_chainData` por descenso.** Con `v` en el último bloque (o `v = s2`), rango `hitRank [lam2, lam1]`
(`lam2 = σ` si `v = s2`): base `tri_lam_any` (o el ancla); rango 1, el pegado de `chain_mid`; rango 2, el de
`chain_far`. Con `v` en el de en medio, rango `midRank`: base `chain_both`; rango 1, `chain_near`; rango 2,
`chain_allmid`. -/
theorem phantomFree_chainData_desc {v s1 s2 : Nat} {A M C : Nat → Prop} (hl : LocPair φ P0 P σ)
    (D : ChainData φ v s1 s2 A M C) (hv : stepVar φ σ = some v) (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (hN : midFusion φ < N) : PhantomFree φ P0 P N σ := by
  have rng : ∀ {s : Nat}, s < φ.nVars → 0 ≤ varStep s ∧ varStep s < N := by
    intro s hs
    have h1 : 0 ≤ varStep s := by simp only [varStep]; omega
    have h2 : varStep s < midFusion φ := by simp only [varStep, midFusion]; omega
    exact ⟨h1, by omega⟩
  obtain ⟨h10, h1N⟩ := rng D.s1v
  obtain ⟨h20, h2N⟩ := rng D.s2v
  have hs1 := stepVar_var D.s1v
  have hs2 := stepVar_var D.s2v
  -- la parte común de los dos primeros casos: `lam2` es el paso de `s2` (o `σ`), con su base
  have last : ∀ {lam2 : Int}, 0 ≤ lam2 → lam2 < N → stepVar φ lam2 = some s2 →
      (C v ∧ ∀ z1 z2, C z1 → C z2 → z1 ≠ v → z2 ≠ v → z1 = z2) ∨ v = s2 →
      (∀ (R : PathNodeId → PathNodeId → Prop) (Tf : Trios), PhStruct φ P0 N R Tf →
        (∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) →
        ∀ x u w, Tri R Tf x u w → Hits lam2 x u w → TriOf φ P x u w) → PhantomFree φ P0 P N σ := by
    intro lam2 h20' h2N' hs2' hc base
    refine phantomFree_of_descent hσ0 hσN (hitRank [lam2, varStep s1]) (fun R Tf hS hanch x u w t ih => ?_)
    by_cases h2 : Hits lam2 x u w
    · exact base R Tf hS hanch x u w t h2
    have r2 := hitRank_succ (S := [varStep s1]) h2
    by_cases h1 : Hits (varStep s1) x u w
    · -- rango 1: el testigo en `lam2` da caras de rango 0
      have r1 : hitRank [varStep s1] x u w = 0 := hitRank_zero h1
      exact any_of_first hS (chain_mid hl D hv hS h20' h2N' hs1 hs2' (fun x' u' w' t' hh' =>
          ih x' u' w' t' (by rw [hitRank_zero hh', r2, r1]; omega))) x u w t h1
    · -- rango 2: el testigo en el paso de `s1` da caras de rango ≤ 1
      have r1 := hitRank_succ (S := []) h1
      exact chain_far hl D hv hS hc h10 h1N hs1 (fun x' u' w' t' hh' => ih x' u' w' t' (by
          by_cases g2 : Hits lam2 x' u' w'
          · rw [hitRank_zero g2, r2, r1]; omega
          · rw [hitRank_succ g2, hitRank_zero hh', r2, r1]; omega)) x u w t
  rcases D.pos with ⟨hCv, huniq⟩ | hvs | hMv
  · -- `v` en el último bloque: la base es el parche del último bloque con el testigo de `σ`
    refine last h20 h2N hs2 (Or.inl ⟨hCv, huniq⟩) (fun R Tf hS hanch x u w t hh => ?_)
    refine tri_lam_any (Rr := C) hσ0 hσN hs2 (fun z1 z2 b1 b2 d => ?_) (fun a0 a' h0 h' hss => ?_) hS hanch x u w
      t.xu t.xw t.uw t.nxu t.nxw t.nuw t.nf hh
    · by_cases e1 : z1 = v
      · exact Or.inl (by rw [e1]; exact hv)
      · by_cases e2 : z2 = v
        · exact Or.inr (by rw [e2]; exact hv)
        · exact absurd (huniq z1 z2 b1 b2 e1 e2) d
    · have := glue3_P hl D hv h0 h0 h0 (hl.sub _ h') rfl hss.symm (fun _ => h')
        (fun e => absurd hCv (by rw [e]; exact D.nC2)) (fun hm => absurd hCv (fun hc => D.dMC v hm hc))
      rwa [glue3_self] at this
  · -- `v = s2`: el paso fijado hace de paso de `s2`, y la base es el ancla
    have hs2' : stepVar φ σ = some s2 := by rw [← hvs]; exact hv
    exact last hσ0 hσN hs2' (Or.inr hvs) (fun R Tf hS hanch x u w t hh =>
      tri_anchor hS hanch x u w t.xu t.xw t.uw t.nxu t.nxw t.nuw t.nf hh)
  · -- `v` en el bloque de en medio
    refine phantomFree_of_descent hσ0 hσN (midRank (varStep s1) (varStep s2)) (fun R Tf hS hanch x u w t ih => ?_)
    by_cases h0 : x.id.step = varStep s2 ∧ w.id.step = varStep s1
    · exact chain_both hl D hv hS hMv hσ0 hσN hanch hs1 hs2 x u w t h0.1 h0.2
    have r0 : ∀ {x' u' w' : PathNodeId}, x'.id.step = varStep s2 → w'.id.step = varStep s1 →
        midRank (varStep s1) (varStep s2) x' u' w' = 0 := by
      intro x' u' w' a b; simp only [midRank, if_pos (And.intro a b)]
    by_cases h2 : Hits (varStep s2) x u w
    · -- rango 1: `chain_near`, cuyas dos caras útiles tienen rango 0
      have r : midRank (varStep s1) (varStep s2) x u w = 1 := by simp only [midRank, if_neg h0, if_pos h2]
      exact any_of_first hS (chain_near hl D hv hS hMv h10 h1N hs1 hs2 (fun x' u' w' t' a b =>
        ih x' u' w' t' (by rw [r0 a b, r]; omega))) x u w t h2
    · -- rango 2: `chain_allmid`, con las caras en el paso de `s2`
      have r : midRank (varStep s1) (varStep s2) x u w = 2 := by simp only [midRank, if_neg h0, if_neg h2]
      exact chain_allmid hl D hv hS hMv h20 h2N hs2 (fun x' u' w' t' hh' => ih x' u' w' t' (by
        rw [r]; simp only [midRank]; split
        · omega
        · rw [if_pos (show Hits (varStep s2) x' u' w' from hh')]; omega)) x u w t

theorem phantomFree_of_chain3_desc (hcl : Chain3 φ) (hl : LocPair φ P0 P σ) (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (hN : midFusion φ < N) : PhantomFree φ P0 P N σ := by
  cases hv : stepVar φ σ with
  | none => exact phantomFree_none hl hv hσ0 hσN
  | some v =>
    rcases hcl v with ⟨s, L, Rr, D⟩ | ⟨s1, s2, A, M, C, D⟩
    · -- dos bloques, por descenso
      by_cases hvs : v = s
      · subst hvs
        exact phantomFree_sep_desc hσ0 hσN hσ0 hσN hv D.cardL D.cardR (sep_glue_P hl D hv) (Or.inl rfl)
      · have hs := D.sv hvs
        have hl0 : 0 ≤ varStep s := by simp only [varStep]; omega
        have hlN : varStep s < N := by
          have : varStep s < midFusion φ := by simp only [varStep, midFusion]; omega
          omega
        refine phantomFree_sep_desc hσ0 hσN hl0 hlN (stepVar_var hs) D.cardL D.cardR (sep_glue_P hl D hv)
          (Or.inr ⟨fun z1 z2 b1 b2 d => ?_, sep_patch_P hl D hv hvs⟩)
        rcases D.card0 hvs z1 z2 b1 b2 d with e | e
        · exact Or.inl (by rw [e]; exact hv)
        · exact Or.inr (by rw [e]; exact hv)
    · exact phantomFree_chainData_desc hl D hv hσ0 hσN hN

open Driver Machine MachineOn

/-- **`phantomAt_of_chain3` por descenso.** -/
theorem phantomAt_of_chain3_desc (hb : Bounded φ) (hcl : Chain3 φ) (T : Int) (hT : 1 ≤ T) : PhantomAt φ T := by
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
    refine ⟨fun r hr => ?_, phantomFree_of_chain3_desc hcl (locPair_up hb T k d) (by omega) (by omega) (by omega)⟩
    obtain ⟨r1, r2⟩ := reqOf_range hb r hr
    rw [hds] at r2
    exact phantomFree_of_chain3_desc hcl (locPair_filter T k r) (by omega) r2 (by omega)

/-- **`hRead_of_chain3` por descenso.** -/
theorem hRead_of_chain3_desc (hcl : Chain3 φ) {T : Int} (hN : midFusion φ < T) (k : NodeId) :
    HRead φ T (SolE φ T k) := by
  intro R r _ hr1 hrT
  exact phantomFree_of_chain3_desc hcl (locPair_read T k R r) (by omega) hrT hN

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **La máquina `:on` es exacta en toda fórmula de cadenas de tres bloques**, por descenso. -/
theorem machineExact_of_chain3_desc (hbd : Bounded φ) (hcl : Chain3 φ) : MachineExact φ :=
  (machineExact_iff hbd).2 (phantomAt_of_chain3_desc hbd hcl)

/-- **El lector no se atasca en ninguna fórmula de cadenas de tres bloques**, por descenso. -/
theorem reader_on_chain3_desc (hbd : Bounded φ) (hcl : Chain3 φ) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on hbd (phantomAt_of_chain3_desc hbd hcl)
    (fun k => hRead_of_chain3_desc hcl (by unfold stepCount midFusion; omega) k) hkv hr

/-- Tres cláusulas en cadena, por descenso. -/
theorem machineExact_threeChain_desc : MachineExact threeChain :=
  machineExact_of_chain3_desc bounded_threeChain chain3_threeChain

end MachineOn

end AbsSatBingo.Model
