-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnLocal.lean
import AbsSatBingo.Model.ForbidOnSep

/-!
# Las familias de ramas son locales: construir una rama cláusula a cláusula

En las tres situaciones de la prueba (filtro, UP y lectura) las familias `P0` y `P` se definen con condiciones sobre
un paso cada vez: una ventana prohibida (el tercer paso de una cláusula) y nodos fijados. `LocPair φ P0 P σ` lo
recoge sin mencionar la situación:

* `sub`: `P ⊆ P0`;
* `loc`: una asignación que en cada paso coincide localmente con alguna rama de `P0` es de `P0`;
* `anc`: una rama de `P0` que en el paso `σ` coincide localmente con una de `P` es de `P`;
* `same`: las ramas de `P` eligen el mismo nodo en `σ`.

«Coincidir localmente en el paso `q`» (`LAgree`) es elegir el mismo nodo y, si `q` es el tercer paso de una cláusula,
tener la misma ventana.

Con eso una rama se construye **por fuentes** (`p0_of_sources`, `p_of_sources`): basta que cada variable tome su
valor de alguna rama y que cada cláusula tenga sus tres variables tomadas de una misma rama. Es la herramienta para
pegar ramas distintas en bloques distintos cuando las variables compartidas coinciden.

`locPair_filter`, `locPair_up`, `locPair_read` son las tres situaciones. `phantomFree_sepData` rehace el resultado de
`ForbidOnSep` para una variable, sobre cualquier `LocPair`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

-- ============================================================
-- El tercer paso de una cláusula
-- ============================================================

theorem isL3_clause {q : Int} (h : isL3 φ q = true) : ∃ j c, φ.clauses[j]? = some c ∧ q = clauseStep φ j 2 := by
  simp only [isL3, Bool.and_eq_true] at h
  obtain ⟨⟨hlo, hhi⟩, hmod⟩ := h
  have hlo := of_decide_eq_true hlo
  have hhi := of_decide_eq_true hhi
  have hmod := of_decide_eq_true hmod
  obtain ⟨c, p, _, hc⟩ := clauseOf_isSome φ q hlo hhi
  obtain ⟨j, hjdef⟩ : ∃ j, j = ((q - midFusion φ - 1) / 3).toNat := ⟨_, rfl⟩
  have hcj : φ.clauses[j]? = some c := by
    simp only [clauseOf] at hc
    split at hc
    · exact absurd hc (by simp)
    · next c' hc' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rw [hjdef, hc']; rw [hc.1]
  exact ⟨j, c, hcj, by simp only [hjdef, clauseStep, midFusion] at hlo hmod ⊢; omega⟩

theorem isL3_of_prohibited {w : PathNodeId} (h : isProhibited φ w = true) : isL3 φ w.id.step = true := by
  simp only [isProhibited, Bool.and_eq_true] at h
  exact h.1.1.1

/-- Dos asignaciones que coinciden en las tres variables de una cláusula tienen la misma ventana en su tercer paso. -/
theorem pid_clause {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c) {g a : Assign}
    (e1 : g c.l1.v = a c.l1.v) (e2 : g c.l2.v = a c.l2.v) (e3 : g c.l3.v = a c.l3.v) :
    pidOfAssign φ g (clauseStep φ j 2) = pidOfAssign φ a (clauseStep φ j 2) := by
  have h2 : clauseStep φ j 2 - 1 = clauseStep φ j 1 := by simp only [clauseStep]; omega
  have h1 : clauseStep φ j 2 - 2 = clauseStep φ j 0 := by simp only [clauseStep]; omega
  refine pid_of_agree (fun k' z hw hz => ?_)
  rcases hw with e | ⟨_, e⟩ | ⟨_, e⟩
  · rw [e, stepVar_clause hj 2 (by omega)] at hz; cases hz; exact e3
  · rw [e, h2, stepVar_clause hj 1 (by omega)] at hz; cases hz; exact e2
  · rw [e, h1, stepVar_clause hj 0 (by omega)] at hz; cases hz; exact e1

-- ============================================================
-- Las familias locales
-- ============================================================

/-- `g` y `a` coinciden localmente en el paso `q`: eligen el mismo nodo y, en el tercer paso de una cláusula, tienen
la misma ventana. -/
def LAgree (φ : Cnf) (q : Int) (g a : Assign) : Prop :=
  selOfAssign φ g q = selOfAssign φ a q ∧ (isL3 φ q = true → pidOfAssign φ g q = pidOfAssign φ a q)

/-- **Un par de familias locales** (`P0` de antes, `P` de después de fijar el paso `σ`). -/
structure LocPair (φ : Cnf) (P0 P : Assign → Prop) (σ : Int) : Prop where
  sub  : ∀ a, P a → P0 a
  loc  : ∀ g, (∀ q, ∃ a, P0 a ∧ LAgree φ q g a) → P0 g
  anc  : ∀ g, P0 g → (∃ a, P a ∧ LAgree φ σ g a) → P g
  same : ∀ a a', P a → P a' → selOfAssign φ a σ = selOfAssign φ a' σ

variable {P0 P : Assign → Prop} {σ : Int}

/-- **Construir una rama de `P0` por fuentes**: cada variable toma su valor de alguna rama, y las tres variables de
cada cláusula, de una misma rama. -/
theorem p0_of_sources (hl : LocPair φ P0 P σ) {g : Assign} (hne : ∃ a, P0 a) (pt : ∀ z, ∃ a, P0 a ∧ g z = a z)
    (cl : ∀ c ∈ φ.clauses, ∃ a, P0 a ∧ g c.l1.v = a c.l1.v ∧ g c.l2.v = a c.l2.v ∧ g c.l3.v = a c.l3.v) :
    P0 g := by
  refine hl.loc g (fun q => ?_)
  by_cases h3 : isL3 φ q = true
  · obtain ⟨j, c, hj, e⟩ := isL3_clause h3
    obtain ⟨a, ha, e1, e2, e3⟩ := cl c (List.mem_of_getElem? hj)
    have hp : pidOfAssign φ g q = pidOfAssign φ a q := by rw [e]; exact pid_clause hj e1 e2 e3
    exact ⟨a, ha, congrArg PathNodeId.id hp, fun _ => hp⟩
  · cases hv : stepVar φ q with
    | none =>
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, sel_eq_of_var (fun z hz => by rw [hv] at hz; cases hz), fun h => absurd h h3⟩
    | some z =>
      obtain ⟨a, ha, e⟩ := pt z
      exact ⟨a, ha, sel_eq_of_var (fun z' hz' => by rw [hv] at hz'; cases hz'; exact e), fun h => absurd h h3⟩

/-- **Y una de `P`**: además, la variable del paso `σ` y las cláusulas que la contienen toman sus valores de ramas de
`P`. -/
theorem p_of_sources (hl : LocPair φ P0 P σ) {g : Assign} (h0 : P0 g) (hnone : stepVar φ σ = none → ∃ a, P a)
    (hv : ∀ z, stepVar φ σ = some z → (∃ a, P a ∧ g z = a z) ∧
      ∀ c ∈ φ.clauses, ClVar c z → ∃ a, P a ∧ g c.l1.v = a c.l1.v ∧ g c.l2.v = a c.l2.v ∧ g c.l3.v = a c.l3.v) :
    P g := by
  refine hl.anc g h0 ?_
  by_cases h3 : isL3 φ σ = true
  · obtain ⟨j, c, hj, e⟩ := isL3_clause h3
    have hs : stepVar φ σ = some c.l3.v := by rw [e]; exact stepVar_clause hj 2 (by omega)
    obtain ⟨a, ha, e1, e2, e3⟩ := (hv _ hs).2 c (List.mem_of_getElem? hj) (Or.inr (Or.inr rfl))
    have hp : pidOfAssign φ g σ = pidOfAssign φ a σ := by rw [e]; exact pid_clause hj e1 e2 e3
    exact ⟨a, ha, congrArg PathNodeId.id hp, fun _ => hp⟩
  · cases hs : stepVar φ σ with
    | none =>
      obtain ⟨a, ha⟩ := hnone hs
      exact ⟨a, ha, sel_eq_of_var (fun z hz => by rw [hs] at hz; cases hz), fun h => absurd h h3⟩
    | some z =>
      obtain ⟨a, ha, e⟩ := (hv z hs).1
      exact ⟨a, ha, sel_eq_of_var (fun z' hz' => by rw [hs] at hz'; cases hz'; exact e), fun h => absurd h h3⟩

/-- Las ramas de `P` leen igual la variable del paso `σ`. -/
theorem LocPair.sameVar (hl : LocPair φ P0 P σ) {v : Nat} (hv : stepVar φ σ = some v) {a a' : Assign} (ha : P a)
    (ha' : P a') : a v = a' v := var_eq_of_sel (hl.same a a' ha ha') v hv

-- ============================================================
-- Las tres situaciones
-- ============================================================

namespace GPathB

open Driver Machine MachineOn

theorem validUpTo_of_local {g : Assign} {T : Int} {Q : Assign → Prop} (hQ : ∀ a, Q a → ValidUpTo φ a T)
    (h : ∀ q, ∃ a, Q a ∧ LAgree φ q g a) : ValidUpTo φ g T := by
  intro q hq
  cases hp : isProhibited φ (pidOfAssign φ g q) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a, ha, _, hpid⟩ := h q
    have h3 : isL3 φ q = true := by have := isL3_of_prohibited hp; rwa [pid_step] at this
    rw [hpid h3, hQ a ha q hq] at hp
    cases hp

/-- El filtro. -/
theorem locPair_filter (T : Int) (k r : NodeId) :
    LocPair φ (SolE φ T k) (fun a => SolE φ T k a ∧ selOfAssign φ a r.step = r) r.step := by
  refine ⟨fun a h => h.1, fun g h => ⟨validUpTo_of_local (fun a ha => ha.1) h, ?_⟩,
    fun g h0 ⟨a, ha, hsel, _⟩ => ⟨h0, hsel.trans ha.2⟩, fun a a' h h' => h.2.trans h'.2.symm⟩
  obtain ⟨a, ha, hsel, _⟩ := h (T - 1)
  exact hsel.trans ha.2

/-- La lectura. -/
theorem locPair_read (T : Int) (k : NodeId) (R : List NodeId) (r : NodeId) :
    LocPair φ (Pinned φ (SolE φ T k) R) (fun a => Pinned φ (SolE φ T k) R a ∧ selOfAssign φ a r.step = r) r.step := by
  refine ⟨fun a h => h.1, fun g h => ⟨⟨validUpTo_of_local (fun a ha => ha.1.1) h, ?_⟩, fun x hx => ?_⟩,
    fun g h0 ⟨a, ha, hsel, _⟩ => ⟨h0, hsel.trans ha.2⟩, fun a a' h h' => h.2.trans h'.2.symm⟩
  · obtain ⟨a, ha, hsel, _⟩ := h (T - 1)
    exact hsel.trans ha.1.2
  · obtain ⟨a, ha, hsel, _⟩ := h x.step
    exact hsel.trans (ha.2 x hx)

/-- El UP. -/
theorem locPair_up (hb : Bounded φ) (T : Int) (k d : NodeId) :
    LocPair φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
      (fun a => SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) T := by
  have hdT : ∀ {a : Assign}, SolE φ (T + 1) d a → selOfAssign φ a T = d := by
    intro a ha
    have := ha.2
    rwa [Int.add_sub_cancel] at this
  refine ⟨fun a ha => ?_, fun g h => ⟨⟨validUpTo_of_local (fun a ha => ha.1.1) h, ?_⟩, fun r hr => ?_⟩,
    fun g h0 ⟨a, ha, hsel, hpid⟩ => ⟨⟨validUpTo_succ h0.1.1 ?_, ?_⟩, h0.1.2⟩,
    fun a a' h h' => (hdT h.1).trans (hdT h'.1).symm⟩
  · refine ⟨⟨validUpTo_mono ha.1.1 (by omega), ha.2⟩, fun r hr => ?_⟩
    exact reqSat_selOfAssign φ hb a T r (by rw [hdT ha.1]; exact hr)
  · obtain ⟨a, ha, hsel, _⟩ := h (T - 1)
    exact hsel.trans ha.1.2
  · obtain ⟨a, ha, hsel, _⟩ := h r.step
    exact hsel.trans (ha.2 r hr)
  · cases hp : isProhibited φ (pidOfAssign φ g T) with
    | false => rfl
    | true =>
      exfalso
      have h3 : isL3 φ T = true := by have := isL3_of_prohibited hp; rwa [pid_step] at this
      rw [hpid h3, ha.1.1 T (by omega)] at hp
      cases hp
  · show selOfAssign φ g (T + 1 - 1) = d
    rw [Int.add_sub_cancel]
    exact hsel.trans (hdT ha.1)

-- ============================================================
-- `ForbidOnSep` para una variable, sobre cualquier par local
-- ============================================================

section SepLoc

variable {N : Int} {v s : Nat} {L Rr : Nat → Prop}

theorem sep_glue_P (hl : LocPair φ P0 P σ) (D : SepData φ v s L Rr) (hv : stepVar φ σ = some v) :
    ∀ a0 c c', P0 a0 → P c → P c' → c s = c' s → P (glue s L Rr c c' a0) := by
  intro a0 c c' h0 hc hc' hss
  have out : ∀ {z : Nat}, ¬ (Rr z ∨ L z ∨ z = s) → glue s L Rr c c' a0 z = a0 z := fun h =>
    glue_out (fun hr => h (Or.inl hr)) (fun hl' => h (Or.inr hl'))
  have hP0 : P0 (glue s L Rr c c' a0) := by
    refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun cl hcl => ?_)
    · by_cases h1 : Rr z
      · exact ⟨c', hl.sub _ hc', glue_Rp D hss (Or.inl h1)⟩
      · by_cases h2 : L z ∨ z = s
        · exact ⟨c, hl.sub _ hc, glue_Lp D h2⟩
        · exact ⟨a0, h0, glue_out h1 h2⟩
    · rcases D.cl cl hcl with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
      · exact ⟨a0, h0, out o1, out o2, out o3⟩
      · exact ⟨c, hl.sub _ hc, glue_Lp D i1, glue_Lp D i2, glue_Lp D i3⟩
      · exact ⟨c', hl.sub _ hc', glue_Rp D hss i1, glue_Rp D hss i2, glue_Rp D hss i3⟩
  refine p_of_sources hl hP0 (fun h => by rw [hv] at h; cases h) (fun z hz => ?_)
  rw [hv] at hz; cases hz
  have hin : Rr v ∨ L v ∨ v = s := by
    rcases D.mem with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  refine ⟨?_, fun cl hcl hcv => ?_⟩
  · rcases D.mem with h | h
    · exact ⟨c, hc, glue_Lp D (Or.inr h)⟩
    · exact ⟨c', hc', glue_Rp D hss (Or.inl h)⟩
  · rcases D.cl cl hcl with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
    · exfalso
      rcases hcv with e | e | e
      · exact o1 (by rw [← e]; exact hin)
      · exact o2 (by rw [← e]; exact hin)
      · exact o3 (by rw [← e]; exact hin)
    · exact ⟨c, hc, glue_Lp D i1, glue_Lp D i2, glue_Lp D i3⟩
    · exact ⟨c', hc', glue_Rp D hss i1, glue_Rp D hss i2, glue_Rp D hss i3⟩

theorem sep_patch_P (hl : LocPair φ P0 P σ) (D : SepData φ v s L Rr) (hv : stepVar φ σ = some v) (hvs : v ≠ s) :
    ∀ a0 a', P0 a0 → P a' → a' s = a0 s → P (patch Rr a' a0) := by
  intro a0 a' h0 h' hss
  have hRv : Rr v := by
    rcases D.mem with h | h
    · exact absurd h hvs
    · exact h
  have inR : ∀ {z : Nat}, (Rr z ∨ z = s) → patch Rr a' a0 z = a' z := by
    intro z h
    rcases h with h | h
    · exact patch_in h
    · rw [h, patch_out D.nR]; exact hss.symm
  have notR : ∀ {z : Nat}, (L z ∨ z = s) → ¬ Rr z := by
    intro z h hr
    rcases h with h | h
    · exact D.disj z h hr
    · rw [h] at hr; exact D.nR hr
  have hP0 : P0 (patch Rr a' a0) := by
    refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun cl hcl => ?_)
    · by_cases h1 : Rr z
      · exact ⟨a', hl.sub _ h', patch_in h1⟩
      · exact ⟨a0, h0, patch_out h1⟩
    · rcases D.cl cl hcl with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
      · exact ⟨a0, h0, patch_out (fun h => o1 (Or.inl h)), patch_out (fun h => o2 (Or.inl h)),
          patch_out (fun h => o3 (Or.inl h))⟩
      · exact ⟨a0, h0, patch_out (notR i1), patch_out (notR i2), patch_out (notR i3)⟩
      · exact ⟨a', hl.sub _ h', inR i1, inR i2, inR i3⟩
  refine p_of_sources hl hP0 (fun h => by rw [hv] at h; cases h) (fun z hz => ?_)
  rw [hv] at hz; cases hz
  refine ⟨⟨a', h', patch_in hRv⟩, fun cl hcl hcv => ?_⟩
  rcases D.cl cl hcl with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
  · exfalso
    rcases hcv with e | e | e
    · exact o1 (by rw [← e]; exact Or.inl hRv)
    · exact o2 (by rw [← e]; exact Or.inl hRv)
    · exact o3 (by rw [← e]; exact Or.inl hRv)
  · exfalso
    rcases hcv with e | e | e
    · exact notR i1 (by rw [← e]; exact hRv)
    · exact notR i2 (by rw [← e]; exact hRv)
    · exact notR i3 (by rw [← e]; exact hRv)
  · exact ⟨a', h', inR i1, inR i2, inR i3⟩

/-- **Sin familias fantasma alrededor de una variable con separador**, para cualquier par local. -/
theorem phantomFree_sepData (hl : LocPair φ P0 P σ) (D : SepData φ v s L Rr) (hv : stepVar φ σ = some v)
    (hσ0 : 0 ≤ σ) (hσN : σ < N) (hN : midFusion φ < N) : PhantomFree φ P0 P N σ := by
  by_cases hvs : v = s
  · subst hvs
    exact phantomFree_sep hσ0 hσN hσ0 hσN hv D.cardL D.cardR (sep_glue_P hl D hv) (Or.inl rfl)
  · have hs := D.sv hvs
    have hl0 : 0 ≤ varStep s := by simp only [varStep]; omega
    have hlN : varStep s < N := by
      have : varStep s < midFusion φ := by simp only [varStep, midFusion]; omega
      omega
    refine phantomFree_sep hσ0 hσN hl0 hlN (stepVar_var hs) D.cardL D.cardR (sep_glue_P hl D hv)
      (Or.inr ⟨fun z1 z2 b1 b2 d => ?_, sep_patch_P hl D hv hvs⟩)
    rcases D.card0 hvs z1 z2 b1 b2 d with e | e
    · exact Or.inl (by rw [e]; exact hv)
    · exact Or.inr (by rw [e]; exact hv)

/-- Un paso fijado que no lee ninguna variable no cambia nada. -/
theorem phantomFree_none (hl : LocPair φ P0 P σ) (hv : stepVar φ σ = none) (hσ0 : 0 ≤ σ) (hσN : σ < N) :
    PhantomFree φ P0 P N σ := by
  refine phantomFree_of_helly4 hσ0 hσN (helly4_of_patch (fun _ => False)
    (fun _ _ _ h _ _ _ _ _ => absurd h (fun h => h)) (fun a0 a' h0 h' => ?_))
  rw [patch_empty]
  refine hl.anc a0 h0 ⟨a', h', sel_eq_of_var (fun z hz => by rw [hv] at hz; cases hz), fun h3 => ?_⟩
  exfalso
  obtain ⟨j, c, hj, e⟩ := isL3_clause h3
  rw [e, stepVar_clause hj 2 (by omega)] at hv
  cases hv

end SepLoc

end GPathB

end AbsSatBingo.Model
