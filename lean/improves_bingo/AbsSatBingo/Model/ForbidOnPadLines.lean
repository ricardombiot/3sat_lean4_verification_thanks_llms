-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnPadLines.lean
import AbsSatBingo.Model.ForbidOnPad

/-!
# Las líneas en los árboles de cláusulas: `PhantomAtW` sin hipótesis

Las familias de una línea (`SolE` y sus filtros) solo miran el prefijo: son **locales bajo `N`** (`LocBelow`), con
`N = T` en el filtro y `N = T + 1` en el UP. Para H2′ hace falta un `λ < N`. El separador `m` de `sep_three` da
`λ = cutStep m`; si cae bajo la línea, la prueba del lector (`twoWitnessF_of_forest`) vale tal cual. Si cae más allá:

* **Sin terceros pasos bajo `N`**: la familia es un producto (cada paso lee una variable) y el trío tiene rama común
  pegando variable a variable.
* **`m` es una cláusula aún sin comprobar**: las ramas respecto de `m` no se tocan bajo la línea (`br_clause`), y cada
  rama tiene a lo sumo una variable de `m` (`var_of_m_inj`). Por palomar, en cada región uno de los tres nodos lee
  solo lo que leen los otros dos, y la rama de su pareja sirve de fuente. El trío no era Helly-fallido.

* **`glue_regions`**: pegado por regiones sin corte (huellas de los pasos bajo `N` y fuentes por región).
* **`twoWitnessF_of_forestN`**: H2′ bajo `N` en los árboles de cláusulas con lecturas locales.
* **`phantomAtW_of_forest`**, **`phantomAtW_pad`**, **`machineExactW_pad`**, **`reader_winNode_tree`**: las líneas,
  la máquina exacta y el lector sin hipótesis sobre la acolchada de todo árbol de cláusulas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- **Local bajo `N`**: basta coincidir localmente con la familia en los pasos anteriores a `N`. -/
def LocBelow (φ : Cnf) (P : Assign → Prop) (N : Int) : Prop :=
  ∀ g, (∀ q, q < N → ∃ a, P a ∧ LAgree φ q g a) → P g

theorem LocBelow.loc {P : Assign → Prop} {N : Int} (h : LocBelow φ P N) :
    ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g :=
  fun g hg => h g (fun q _ => hg q)

theorem validUpTo_of_below {g : Assign} {T : Int} {Q : Assign → Prop} (hQ : ∀ a, Q a → ValidUpTo φ a T)
    (h : ∀ q, q < T → ∃ a, Q a ∧ LAgree φ q g a) : ValidUpTo φ g T := by
  intro q hq
  cases hp : isProhibited φ (pidOfAssign φ g q) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a, ha, _, hpid⟩ := h q hq
    have h3 : isL3 φ q = true := by have := isL3_of_prohibited hp; rwa [Machine.pid_step] at this
    rw [hpid h3, hQ a ha q hq] at hp
    cases hp

/-- La familia del filtro es local bajo `T`. -/
theorem locBelow_filter {T : Int} {k r : NodeId} (hr : r.step < T) :
    LocBelow φ (fun a => SolE φ T k a ∧ selOfAssign φ a r.step = r) T := by
  intro g h
  refine ⟨⟨validUpTo_of_below (fun a ha => ha.1.1) h, ?_⟩, ?_⟩
  · obtain ⟨a, ha, hsel, _⟩ := h (T - 1) (by omega)
    exact hsel.trans ha.1.2
  · obtain ⟨a, ha, hsel, _⟩ := h r.step hr
    exact hsel.trans ha.2

/-- La familia del UP es local bajo `T + 1`. -/
theorem locBelow_up {T : Int} {d : NodeId} : LocBelow φ (SolE φ (T + 1) d) (T + 1) := by
  intro g h
  refine ⟨validUpTo_of_below (fun a ha => ha.1) h, ?_⟩
  obtain ⟨a, ha, hsel, _⟩ := h (T + 1 - 1) (by omega)
  exact hsel.trans ha.2

-- ============================================================
-- El pegado por regiones sin corte
-- ============================================================

/-- **El pegado por regiones**: si la huella de cada paso bajo `N` cae en una región y cada región tiene una fuente
de `P` que coincide con los tres nodos en lo que leen de ella, hay una rama de `P` por los tres. -/
theorem glue_regions {P : Assign → Prop} {N : Int} (hloc : LocBelow φ P N) (reg : Nat → Nat)
    (hfp : ∀ q, q < N → ∃ Q, ∀ g a, (∀ z, reg z = Q → g z = a z) → LAgree φ q g a)
    {x u w : PathNodeId} {cx cu cw : Assign}
    (tx : pidOfAssign φ cx x.id.step = x) (tu : pidOfAssign φ cu u.id.step = u)
    (tw : pidOfAssign φ cw w.id.step = w)
    (src : ∀ Q, ∃ a, P a ∧ (∀ z, reg z = Q → WR φ x.id.step z → a z = cx z) ∧
      (∀ z, reg z = Q → WR φ u.id.step z → a z = cu z) ∧ (∀ z, reg z = Q → WR φ w.id.step z → a z = cw z)) :
    ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
      pidOfAssign φ a w.id.step = w := by
  let s : Nat → Assign := fun Q => Classical.choose (src Q)
  have hs := fun Q => Classical.choose_spec (src Q)
  let g : Assign := fun z => s (reg z) z
  have hg : ∀ Q z, reg z = Q → g z = s Q z := by
    intro Q z h
    show s (reg z) z = s Q z
    rw [h]
  refine ⟨g, hloc g (fun q hq => ?_), ?_, ?_, ?_⟩
  · obtain ⟨Q, hQ⟩ := hfp q hq
    exact ⟨s Q, (hs Q).1, hQ g (s Q) (fun z hz => hg Q z hz)⟩
  · exact (pid_of_agree (fun k' z hw hz => (hg _ z rfl).trans ((hs (reg z)).2.1 z rfl ⟨k', hw, hz⟩))).trans tx
  · exact (pid_of_agree (fun k' z hw hz => (hg _ z rfl).trans ((hs (reg z)).2.2.1 z rfl ⟨k', hw, hz⟩))).trans tu
  · exact (pid_of_agree (fun k' z hw hz => (hg _ z rfl).trans ((hs (reg z)).2.2.2 z rfl ⟨k', hw, hz⟩))).trans tw

/-- **La fuente por cobertura**: si en la región `Q` lo que lee un nodo lo leen los otros dos, la rama de su pareja
sirve de fuente. -/
theorem src_cover {P : Assign → Prop} {reg : Nat → Nat} {x u w : PathNodeId} {a1 a2 a3 : Assign}
    (h1 : P a1) (h2 : P a2) (h3 : P a3)
    (x1 : pidOfAssign φ a1 x.id.step = x) (u1 : pidOfAssign φ a1 u.id.step = u)
    (x2 : pidOfAssign φ a2 x.id.step = x) (w2 : pidOfAssign φ a2 w.id.step = w)
    (u3 : pidOfAssign φ a3 u.id.step = u) (w3 : pidOfAssign φ a3 w.id.step = w) (Q : Nat)
    (hc : (∀ z, reg z = Q → WR φ w.id.step z → WR φ x.id.step z ∨ WR φ u.id.step z) ∨
      (∀ z, reg z = Q → WR φ u.id.step z → WR φ x.id.step z ∨ WR φ w.id.step z) ∨
      (∀ z, reg z = Q → WR φ x.id.step z → WR φ u.id.step z ∨ WR φ w.id.step z)) :
    ∃ a, P a ∧ (∀ z, reg z = Q → WR φ x.id.step z → a z = a1 z) ∧
      (∀ z, reg z = Q → WR φ u.id.step z → a z = a1 z) ∧ (∀ z, reg z = Q → WR φ w.id.step z → a z = a2 z) := by
  have e12 : ∀ z, WR φ x.id.step z → a1 z = a2 z := fun z hz => agree_of_win (x1.trans x2.symm) hz
  have e13 : ∀ z, WR φ u.id.step z → a1 z = a3 z := fun z hz => agree_of_win (u1.trans u3.symm) hz
  have e23 : ∀ z, WR φ w.id.step z → a2 z = a3 z := fun z hz => agree_of_win (w2.trans w3.symm) hz
  rcases hc with c | c | c
  · refine ⟨a1, h1, fun _ _ _ => rfl, fun _ _ _ => rfl, fun z hz hw => ?_⟩
    rcases c z hz hw with h | h
    · exact e12 z h
    · exact (e13 z h).trans (e23 z hw).symm
  · refine ⟨a2, h2, fun z _ h => (e12 z h).symm, fun z hz hu => ?_, fun _ _ _ => rfl⟩
    rcases c z hz hu with h | h
    · exact (e12 z h).symm
    · exact (e23 z h).trans (e13 z hu).symm
  · refine ⟨a3, h3, fun z hz hx => ?_, fun z _ h => (e13 z h).symm, fun z _ h => (e23 z h).symm⟩
    rcases c z hz hx with h | h
    · exact (e13 z h).symm
    · exact (e23 z h).symm.trans (e12 z hx).symm

-- ============================================================
-- Las ramas de una cláusula
-- ============================================================

namespace IncForest

variable (F : IncForest φ)

/-- **Cada rama de una cláusula `m` tiene a lo sumo una variable de `m`**: sus variables son su padre (arriba) o
hijos suyos (cada uno su propia rama). -/
theorem var_of_m_inj {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c) {z z' : Nat} (hz : ClVar c z)
    (hz' : ClVar c z') (e : F.br (.cls j) (.var z) = F.br (.cls j) (.var z')) : z = z' := by
  have side : ∀ {y : Nat}, ClVar c y →
      (F.par (.var y) = some (.cls j) ∧ F.br (.cls j) (.var y) = some (.var y)) ∨
      (F.par (.cls j) = some (.var y) ∧ F.br (.cls j) (.var y) = none) := by
    intro y hy
    have hne : Vx.var y ≠ Vx.cls j := fun h => by cases h
    rcases F.edge j c y hj hy with h | h
    · exact Or.inl ⟨h, F.inBr_unique (F.br_spec hne) (Or.inr ⟨_, rfl, h, F.anc_refl _⟩)⟩
    · refine Or.inr ⟨h, F.inBr_unique (F.br_spec hne) (Or.inl ⟨rfl, fun ha => ?_⟩)⟩
      have := F.dep_le_of_anc ha
      have := F.dep_lt _ _ h
      omega
  rcases side hz with ⟨_, b⟩ | ⟨p, b⟩ <;> rcases side hz' with ⟨_, b'⟩ | ⟨p', b'⟩
  · rw [b, b'] at e; cases e; rfl
  · rw [b, b'] at e; cases e
  · rw [b, b'] at e; cases e
  · rw [p] at p'; cases p'; rfl

end IncForest

-- ============================================================
-- H2′ bajo `N` en los árboles de cláusulas
-- ============================================================

/-- **H2′ bajo `N`** en los árboles de cláusulas con lecturas locales, para toda familia local bajo `N`. -/
theorem twoWitnessF_of_forestN (hbd : Bounded φ) (F : IncForest φ) {r : Vx} (hroot : ∀ v, F.Anc r v)
    {Fr : Nat → Prop} (hFr : FreeOK φ Fr) (hlb : LocalBlocks φ Fr) {P0 P : Assign → Prop} {N : Int}
    (hloc : LocBelow φ P N) : TwoWitnessF φ P0 P N := by
  classical
  intro x u w nxu nxw nuw _ pxu pxw puw hno
  obtain ⟨Bx, hBx⟩ := hlb x.id.step
  obtain ⟨Bu, hBu⟩ := hlb u.id.step
  obtain ⟨Bw, hBw⟩ := hlb w.id.step
  let b : Fin 3 → Vx := fun i => if i = 0 then Bx else if i = 1 then Bu else Bw
  obtain ⟨m, _, hsep⟩ := F.sep_three hroot b
  obtain ⟨a1, h1, x1, u1⟩ := pxu
  obtain ⟨a2, h2, x2, w2⟩ := pxw
  obtain ⟨a3, h3, u3, w3⟩ := puw
  by_cases hA : cutStep φ m < N
  · -- el corte cae bajo la línea: la prueba del lector
    have peg : PegF φ (ConstIn P) Fr (cutStep φ m) (F.regOf m) x u w :=
      pegF_forest hbd F hsep (fun z h hf => hBx z h hf) (fun z h hf => hBu z h hf) (fun z h hf => hBw z h hf)
    have hfix : ∀ a b, P a → P b → ∀ z, ConstIn P z → a z = b z := fun a b ha hb z hz => hz a b ha hb
    have hl := hloc.loc
    by_cases ex : cutStep φ m = x.id.step
    · exact absurd (glue_pegF (s := x) hl hfix hFr peg h1 h1 h2 x1 u1 w2 (by rw [ex]; exact x1)
        (by rw [ex]; exact x1) (by rw [ex]; exact x2) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
    by_cases eu : cutStep φ m = u.id.step
    · exact absurd (glue_pegF (s := u) hl hfix hFr peg h1 h1 h3 x1 u1 w3 (by rw [eu]; exact u1)
        (by rw [eu]; exact u1) (by rw [eu]; exact u3) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
    by_cases ew : cutStep φ m = w.id.step
    · exact absurd (glue_pegF (s := w) hl hfix hFr peg h2 h3 h2 x2 u3 w2 (by rw [ew]; exact w2)
        (by rw [ew]; exact w3) (by rw [ew]; exact w2) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
    refine ⟨cutStep φ m, (cutStep_bounds m).1, hA, ex, eu, ew, fun s _ hx hu hw => ?_⟩
    exact absurd ⟨hx, hu, hw⟩ (noCommon_of_pegF hl hfix hFr peg ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩
      ⟨a3, h3, u3, w3⟩ hno s)
  -- el corte cae más allá de la línea: el trío tiene rama común
  exfalso
  apply hno
  by_cases hB1 : ∀ q, q < N → isL3 φ q = false
  · -- sin terceros pasos bajo `N`: regiones de una variable
    refine glue_regions hloc (fun z => z) (fun q hq => ⟨(stepVar φ q).getD 0, fun g a hga =>
      ⟨sel_eq_of_var (fun v hv => hga v (by rw [hv]; rfl)), fun h => by rw [hB1 q hq] at h; cases h⟩⟩)
      x1 u1 w2 (fun Q => src_cover h1 h2 h3 x1 u1 x2 w2 u3 w3 Q ?_)
    by_cases hx : WR φ x.id.step Q
    · exact Or.inl (fun z hz _ => Or.inl (by rw [show z = Q from hz]; exact hx))
    · by_cases hu : WR φ u.id.step Q
      · exact Or.inl (fun z hz _ => Or.inr (by rw [show z = Q from hz]; exact hu))
      · exact Or.inr (Or.inr (fun z hz hxz => absurd (by rw [show z = Q from hz] at hxz; exact hxz) hx))
  -- un tercer paso bajo `N`: `m` es una cláusula aún sin comprobar
  obtain ⟨q0, hq0, h30⟩ : ∃ q, q < N ∧ isL3 φ q = true := Classical.byContradiction fun hn =>
    hB1 (fun q hq => by
      cases e : isL3 φ q
      · rfl
      · exact absurd ⟨q, hq, e⟩ hn)
  obtain ⟨j0, c0, _, e0⟩ := isL3_clause h30
  have hmv : ∀ z, Vx.var z ≠ m := by
    intro v e
    subst e
    apply hA
    simp only [cutStep]
    split
    · simp only [varStep]; simp only [clauseStep] at e0; omega
    · simp only [clauseStep] at e0; omega
  have hmc : ∀ j c, φ.clauses[j]? = some c → clauseStep φ j 2 < N → Vx.cls j ≠ m := by
    intro j c hj hlt e
    apply hA
    rw [← e]
    simp only [cutStep, if_pos (List.getElem?_eq_some_iff.mp hj).1]
    exact hlt
  let reg : Nat → Nat := fun z => if Fr z then 2 * z + 1 else 2 * codeBr (F.br m (.var z))
  -- las cláusulas distintas de `m` no cruzan regiones
  have hcl : ∀ j c, φ.clauses[j]? = some c → Vx.cls j ≠ m → ∀ z z', ClVar c z → ClVar c z' →
      reg z = reg z' := by
    intro j c hj hjm z z' hz hz'
    by_cases hf : Fr z
    · rw [hFr c (List.mem_of_getElem? hj) z hz hf z' hz']
    · by_cases hf' : Fr z'
      · rw [hFr c (List.mem_of_getElem? hj) z' hz' hf' z hz]
      · simp only [reg, if_neg hf, if_neg hf']
        rw [F.br_clause hj hz (hmv z) hjm, F.br_clause hj hz' (hmv z') hjm]
  -- las huellas de los pasos bajo `N`
  have hfp : ∀ q, q < N → ∃ Q, ∀ g a, (∀ z, reg z = Q → g z = a z) → LAgree φ q g a := by
    intro q hq
    by_cases h3 : isL3 φ q = true
    · obtain ⟨j, c, hj, e⟩ := isL3_clause h3
      have hjm := hmc j c hj (by rw [← e]; exact hq)
      refine ⟨reg c.l3.v, fun g a hga => ?_⟩
      have e1 : g c.l1.v = a c.l1.v := hga _ (hcl j c hj hjm _ _ (Or.inl rfl) (Or.inr (Or.inr rfl)))
      have e2 : g c.l2.v = a c.l2.v := hga _ (hcl j c hj hjm _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      have e3 : g c.l3.v = a c.l3.v := hga _ rfl
      have hp : pidOfAssign φ g q = pidOfAssign φ a q := by rw [e]; exact pid_clause hj e1 e2 e3
      exact ⟨congrArg PathNodeId.id hp, fun _ => hp⟩
    · exact ⟨reg ((stepVar φ q).getD 0), fun g a hga =>
        ⟨sel_eq_of_var (fun v hv => hga v (by rw [hv]; rfl)), fun h => absurd h h3⟩⟩
  -- lo que lee un nodo cae en la rama de su bloque
  have hR1 : ∀ B z, InBlk φ B z → B ≠ m → F.br m (.var z) = F.br m B := by
    intro B z hb hBm
    rcases hb with rfl | ⟨j, c, rfl, hj, hz⟩
    · rfl
    · exact F.br_clause hj hz (hmv z) hBm
  -- dos nodos con lecturas propias en una misma región: ni los dos fuera de `m`, ni los dos en `m`
  have key : ∀ (y y' : PathNodeId) (By By' : Vx) (zy zy' : Nat),
      (∀ z, WR φ y.id.step z → ¬ Fr z → InBlk φ By z) → (∀ z, WR φ y'.id.step z → ¬ Fr z → InBlk φ By' z) →
      ((By = m ∧ By' = m) ∨ (By ≠ m ∧ By' ≠ m ∧ F.br m By ≠ F.br m By')) →
      WR φ y.id.step zy → WR φ y'.id.step zy' → ¬ WR φ y.id.step zy' → reg zy = reg zy' → False := by
    intro y y' By By' zy zy' hy hy' hc ry ry' ny e
    have hne : zy ≠ zy' := fun h => ny (h ▸ ry)
    by_cases fz : Fr zy <;> by_cases fz' : Fr zy' <;> simp only [reg, fz, fz', if_true, if_false] at e
    · exact hne (by omega)
    · omega
    · omega
    have eb : F.br m (.var zy) = F.br m (.var zy') := codeBr_inj (by omega)
    rcases hc with ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
    · subst b1
      have i1 := hy zy ry fz
      have i2 := hy' zy' ry' fz'
      rcases i1 with e1 | ⟨j, c, ej, hj, hz⟩
      · exact hmv zy e1.symm
      rcases i2 with e2 | ⟨j', c', ej', hj', hz'⟩
      · exact hmv zy' (e2.symm.trans b2)
      rw [ej] at b2 eb
      rw [b2] at ej'
      cases ej'
      rw [hj] at hj'
      cases hj'
      exact hne (F.var_of_m_inj hj hz hz' eb)
    · exact b3 ((hR1 _ _ (hy zy ry fz) b1).symm.trans (eb.trans (hR1 _ _ (hy' zy' ry' fz') b2)))
  have s01 : Bx = m ∨ Bu = m ∨ F.br m Bx ≠ F.br m Bu := by simpa [b] using hsep 0 1 (by decide)
  have s02 : Bx = m ∨ Bw = m ∨ F.br m Bx ≠ F.br m Bw := by simpa [b] using hsep 0 2 (by decide)
  have s12 : Bu = m ∨ Bw = m ∨ F.br m Bu ≠ F.br m Bw := by simpa [b] using hsep 1 2 (by decide)
  have pick : ∀ {B B' : Vx}, (B = m ∨ B' = m ∨ F.br m B ≠ F.br m B') → ¬ B = m → ¬ B' = m →
      (B = m ∧ B' = m) ∨ (B ≠ m ∧ B' ≠ m ∧ F.br m B ≠ F.br m B') := by
    intro B B' hs n1 n2
    rcases hs with h | h | h
    · exact absurd h n1
    · exact absurd h n2
    · exact Or.inr ⟨n1, n2, h⟩
  refine glue_regions hloc reg hfp x1 u1 w2 (fun Q => src_cover h1 h2 h3 x1 u1 x2 w2 u3 w3 Q ?_)
  by_cases cw : ∀ z, reg z = Q → WR φ w.id.step z → WR φ x.id.step z ∨ WR φ u.id.step z
  · exact Or.inl cw
  by_cases cu : ∀ z, reg z = Q → WR φ u.id.step z → WR φ x.id.step z ∨ WR φ w.id.step z
  · exact Or.inr (Or.inl cu)
  by_cases cx : ∀ z, reg z = Q → WR φ x.id.step z → WR φ u.id.step z ∨ WR φ w.id.step z
  · exact Or.inr (Or.inr cx)
  exfalso
  have wit : ∀ {y y' y'' : PathNodeId},
      ¬ (∀ z, reg z = Q → WR φ y.id.step z → WR φ y'.id.step z ∨ WR φ y''.id.step z) →
      ∃ z, reg z = Q ∧ WR φ y.id.step z ∧ ¬ WR φ y'.id.step z ∧ ¬ WR φ y''.id.step z := by
    intro y y' y'' h
    exact Classical.byContradiction fun hn => h (fun z hz hy => Classical.byContradiction fun ho =>
      hn ⟨z, hz, hy, fun h => ho (Or.inl h), fun h => ho (Or.inr h)⟩)
  obtain ⟨zw, qw, rw', nwx, nwu⟩ := wit cw
  obtain ⟨zu, qu, ru, nux, nuw'⟩ := wit cu
  obtain ⟨zx, qx, rx, nxu', nxw'⟩ := wit cx
  by_cases ex : Bx = m <;> by_cases eu : Bu = m <;> by_cases ew : Bw = m
  · exact key x u Bx Bu zx zu hBx hBu (Or.inl ⟨ex, eu⟩) rx ru nux (qx.trans qu.symm)
  · exact key x u Bx Bu zx zu hBx hBu (Or.inl ⟨ex, eu⟩) rx ru nux (qx.trans qu.symm)
  · exact key x w Bx Bw zx zw hBx hBw (Or.inl ⟨ex, ew⟩) rx rw' nwx (qx.trans qw.symm)
  · exact key u w Bu Bw zu zw hBu hBw (pick s12 eu ew) ru rw' nwu (qu.trans qw.symm)
  · exact key u w Bu Bw zu zw hBu hBw (Or.inl ⟨eu, ew⟩) ru rw' nwu (qu.trans qw.symm)
  · exact key x w Bx Bw zx zw hBx hBw (pick s02 ex ew) rx rw' nwx (qx.trans qw.symm)
  · exact key x u Bx Bu zx zu hBx hBu (pick s01 ex eu) rx ru nux (qx.trans qu.symm)
  · exact key x u Bx Bu zx zu hBx hBu (pick s01 ex eu) rx ru nux (qx.trans qu.symm)

namespace GPathB

open Driver Machine MachineOn

/-- **Las líneas en los árboles de cláusulas** con lecturas locales: `PhantomAtW` en cada línea, sin hipótesis. -/
theorem phantomAtW_of_forest (hbd : Bounded φ) (F : IncForest φ) {r : Vx} (hroot : ∀ v, F.Anc r v)
    {Fr : Nat → Prop} (hFr : FreeOK φ Fr) (hlb : LocalBlocks φ Fr) {T : Int} (hT : 1 ≤ T) : PhantomAtW φ T := by
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step φ k d hd
    have hks := mapNodes_step φ (T - 1) k hk
    omega
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨r1, r2⟩ := reqOf_range hbd r hr
    rw [hds] at r2
    exact phantomFree_of_twoWitnessF (by omega) r2
      (twoWitnessF_of_forestN hbd F hroot hFr hlb (locBelow_filter r2))
  · exact phantomFree_of_twoWitnessF (by omega) (by omega)
      (twoWitnessF_of_forestN hbd F hroot hFr hlb locBelow_up)

/-- **Las líneas de la acolchada** de todo árbol de cláusulas. -/
theorem phantomAtW_pad (hbd : Bounded φ) (F : IncForest φ) {r : Vx} (hroot : ∀ v, F.Anc r v) :
    ∀ T : Int, 1 ≤ T → PhantomAtW (padCnf φ) T :=
  fun _ hT => phantomAtW_of_forest (bounded_pad hbd) (F.pad r) (F.pad_root r hroot) freeOK_pad localBlocks_pad hT

/-- **La máquina es exacta** sobre la acolchada de todo árbol de cláusulas. -/
theorem machineExactW_pad (hbd : Bounded φ) (F : IncForest φ) {r : Vx} (hroot : ∀ v, F.Anc r v) :
    MachineExactW (padCnf φ) :=
  (machineExactW_iff (bounded_pad hbd)).mpr (phantomAtW_pad hbd F hroot)

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por nodos de ventana no se atasca** sobre la acolchada de todo árbol de cláusulas, sin hipótesis. -/
theorem reader_winNode_tree (hbd : Bounded φ) (F : IncForest φ) {r : Vx} (hroot : ∀ v, F.Anc r v)
    {kv : NodeId × GPathB} (hkv : kv ∈ runM .on (padCnf φ)) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading (padCnf φ) kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a (padCnf φ) ∧ (∀ q ∈ W.flatten, selOfAssign (padCnf φ) a q.step = q) ∧
      CT g' (pidOfAssign (padCnf φ) a) :=
  reader_winNode_pad hbd F hroot (phantomAtW_pad hbd F hroot) hkv hr

end MachineOn

end AbsSatBingo.Model
