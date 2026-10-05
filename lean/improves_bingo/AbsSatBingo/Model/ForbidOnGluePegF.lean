-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnGluePegF.lean
import AbsSatBingo.Model.ForbidOnGluePeg

/-!
# El pegado con variables libres y el corte de las constantes (plan del v229, pasos 1 y 2)

* **Paso 1.** El corte fijado es `ConstIn P`: las variables en las que todas las ramas de `P` coinciden (`hfix` sale
  por definición, y el corte es mayor que el de las elecciones).
* **Paso 2.** Variables **libres** `Fr`: solo están en cláusulas de una sola variable (como las tautologías
  `(d ∨ ¬d ∨ d)` del acolchado). No cuentan para las regiones: una región libre puede tocar los tres nodos. El pegado
  les da el valor de cualquier nodo del trío que las lea (`freeVal`; todos coinciden por las ramas de las parejas).

* **`PegF`**, **`glue_pegF`**, `noCommon_of_pegF`, `twoWitnessF_of_pegF`.
* **`reader_winNode_of_pegF`**: el lector por nodos de ventana con `PegF`, el corte de las constantes y las libres.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- Las variables en las que todas las ramas de `P` coinciden. -/
def ConstIn (P : Assign → Prop) (z : Nat) : Prop := ∀ a b, P a → P b → a z = b z

/-- Las variables libres solo están en cláusulas de una sola variable. -/
def FreeOK (φ : Cnf) (Fr : Nat → Prop) : Prop :=
  ∀ c ∈ φ.clauses, ∀ z, ClVar c z → Fr z → ∀ z', ClVar c z' → z' = z

/-- **El pegado en `λ` con variables libres**: el corte de las regiones incluye las libres. -/
structure PegF (φ : Cnf) (KF Fr : Nat → Prop) (lam : Int) (reg : Nat → Nat) (x u w : PathNodeId) : Prop where
  cl  : ∀ c ∈ φ.clauses, ∀ z z', ClVar c z → ClVar c z' → ¬ (KF z ∨ WR φ lam z ∨ Fr z) →
          ¬ (KF z' ∨ WR φ lam z' ∨ Fr z') → reg z = reg z'
  no3 : ∀ q, ¬ (Touch φ (fun z => KF z ∨ WR φ lam z ∨ Fr z) reg q x ∧
          Touch φ (fun z => KF z ∨ WR φ lam z ∨ Fr z) reg q u ∧ Touch φ (fun z => KF z ∨ WR φ lam z ∨ Fr z) reg q w)
  two : ∀ q (y z : PathNodeId), (y = x ∧ z = u ∨ y = x ∧ z = w ∨ y = u ∧ z = w) →
          Touch φ (fun z => KF z ∨ WR φ lam z ∨ Fr z) reg q y → Touch φ (fun z => KF z ∨ WR φ lam z ∨ Fr z) reg q z →
          ∀ v, WR φ lam v → ¬ KF v → AdjReg φ (fun z => KF z ∨ WR φ lam z ∨ Fr z) reg q v →
          WR φ y.id.step v ∨ WR φ z.id.step v

/-- **El pegado con libres.** -/
theorem glue_pegF {P : Assign → Prop} (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g)
    {KF Fr : Nat → Prop} (hfix : ∀ a b, P a → P b → ∀ z, KF z → a z = b z) (hFr : FreeOK φ Fr)
    {lam : Int} {reg : Nat → Nat} {x u w s : PathNodeId} (hp : PegF φ KF Fr lam reg x u w)
    {ax au aw : Assign} (hax : P ax) (hau : P au) (haw : P aw)
    (tx : pidOfAssign φ ax x.id.step = x) (tu : pidOfAssign φ au u.id.step = u)
    (tw : pidOfAssign φ aw w.id.step = w)
    (sx : pidOfAssign φ ax lam = s) (su : pidOfAssign φ au lam = s) (sw : pidOfAssign φ aw lam = s)
    (pxu : ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u)
    (pxw : ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w)
    (puw : ∃ a, P a ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w) :
    ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
      pidOfAssign φ a w.id.step = w := by
  classical
  let Kc : Nat → Prop := fun z => KF z ∨ WR φ lam z ∨ Fr z
  let Kt : Nat → Prop := fun z => KF z ∨ WR φ lam z
  have Su : ∀ z, WR φ lam z → au z = ax z := fun z hz => agree_of_win (su.trans sx.symm) hz
  have Sw : ∀ z, WR φ lam z → aw z = ax z := fun z hz => agree_of_win (sw.trans sx.symm) hz
  -- dos nodos que leen la misma variable le dan el mismo valor (por la rama de su pareja)
  have xu : ∀ z, WR φ x.id.step z → WR φ u.id.step z → ax z = au z := by
    intro z h1 h2; obtain ⟨b, _, b1, b2⟩ := pxu
    exact (agree_of_win (tx.trans b1.symm) h1).trans (agree_of_win (b2.trans tu.symm) h2)
  have xw : ∀ z, WR φ x.id.step z → WR φ w.id.step z → ax z = aw z := by
    intro z h1 h2; obtain ⟨b, _, b1, b2⟩ := pxw
    exact (agree_of_win (tx.trans b1.symm) h1).trans (agree_of_win (b2.trans tw.symm) h2)
  have uw : ∀ z, WR φ u.id.step z → WR φ w.id.step z → au z = aw z := by
    intro z h1 h2; obtain ⟨b, _, b1, b2⟩ := puw
    exact (agree_of_win (tu.trans b1.symm) h1).trans (agree_of_win (b2.trans tw.symm) h2)
  -- el valor de una libre: el del primer nodo que la lee
  let fv : Nat → Bool := fun z =>
    if WR φ x.id.step z then ax z else if WR φ u.id.step z then au z else if WR φ w.id.step z then aw z else ax z
  have fvP : ∀ z, ∃ b, P b ∧ fv z = b z := by
    intro z
    by_cases h1 : WR φ x.id.step z
    · exact ⟨ax, hax, if_pos h1⟩
    · by_cases h2 : WR φ u.id.step z
      · exact ⟨au, hau, by simp only [fv, if_neg h1, if_pos h2]⟩
      · by_cases h3 : WR φ w.id.step z
        · exact ⟨aw, haw, by simp only [fv, if_neg h1, if_neg h2, if_pos h3]⟩
        · exact ⟨ax, hax, by simp only [fv, if_neg h1, if_neg h2, if_neg h3]⟩
  have fvx : ∀ z, WR φ x.id.step z → fv z = ax z := fun z h => if_pos h
  have fvu : ∀ z, WR φ u.id.step z → fv z = au z := by
    intro z h
    by_cases h1 : WR φ x.id.step z
    · rw [fvx z h1]; exact xu z h1 h
    · simp only [fv, if_neg h1, if_pos h]
  have fvw : ∀ z, WR φ w.id.step z → fv z = aw z := by
    intro z h
    by_cases h1 : WR φ x.id.step z
    · rw [fvx z h1]; exact xw z h1 h
    · by_cases h2 : WR φ u.id.step z
      · simp only [fv, if_neg h1, if_pos h2]; exact uw z h2 h
      · simp only [fv, if_neg h1, if_neg h2, if_pos h]
  -- una fuente por región (como en `glue_peg`)
  have hsrc : ∀ q, ∃ b, P b ∧ (Touch φ Kc reg q x → pidOfAssign φ b x.id.step = x) ∧
      (Touch φ Kc reg q u → pidOfAssign φ b u.id.step = u) ∧ (Touch φ Kc reg q w → pidOfAssign φ b w.id.step = w) ∧
      (∀ v, WR φ lam v → ¬ KF v → AdjReg φ Kc reg q v → b v = ax v) := by
    intro q
    by_cases hx : Touch φ Kc reg q x <;> by_cases hu : Touch φ Kc reg q u <;> by_cases hw : Touch φ Kc reg q w
    · exact absurd ⟨hx, hu, hw⟩ (hp.no3 q)
    · obtain ⟨b, hb, b1, b2⟩ := pxu
      refine ⟨b, hb, fun _ => b1, fun _ => b2, fun h => absurd h hw, fun v hv hk ha => ?_⟩
      rcases hp.two q x u (Or.inl ⟨rfl, rfl⟩) hx hu v hv hk ha with r | r
      · exact agree_of_win (b1.trans tx.symm) r
      · exact (agree_of_win (b2.trans tu.symm) r).trans (Su v hv)
    · obtain ⟨b, hb, b1, b2⟩ := pxw
      refine ⟨b, hb, fun _ => b1, fun h => absurd h hu, fun _ => b2, fun v hv hk ha => ?_⟩
      rcases hp.two q x w (Or.inr (Or.inl ⟨rfl, rfl⟩)) hx hw v hv hk ha with r | r
      · exact agree_of_win (b1.trans tx.symm) r
      · exact (agree_of_win (b2.trans tw.symm) r).trans (Sw v hv)
    · exact ⟨ax, hax, fun _ => tx, fun h => absurd h hu, fun h => absurd h hw, fun _ _ _ _ => rfl⟩
    · obtain ⟨b, hb, b1, b2⟩ := puw
      refine ⟨b, hb, fun h => absurd h hx, fun _ => b1, fun _ => b2, fun v hv hk ha => ?_⟩
      rcases hp.two q u w (Or.inr (Or.inr ⟨rfl, rfl⟩)) hu hw v hv hk ha with r | r
      · exact (agree_of_win (b1.trans tu.symm) r).trans (Su v hv)
      · exact (agree_of_win (b2.trans tw.symm) r).trans (Sw v hv)
    · exact ⟨au, hau, fun h => absurd h hx, fun _ => tu, fun h => absurd h hw, fun v hv _ _ => Su v hv⟩
    · exact ⟨aw, haw, fun h => absurd h hx, fun h => absurd h hu, fun _ => tw, fun v hv _ _ => Sw v hv⟩
    · exact ⟨ax, hax, fun h => absurd h hx, fun h => absurd h hu, fun h => absurd h hw, fun _ _ _ _ => rfl⟩
  let src : Nat → Assign := fun q => Classical.choose (hsrc q)
  have hsP : ∀ q, P (src q) := fun q => (Classical.choose_spec (hsrc q)).1
  have hsx : ∀ q, Touch φ Kc reg q x → pidOfAssign φ (src q) x.id.step = x :=
    fun q => (Classical.choose_spec (hsrc q)).2.1
  have hsu : ∀ q, Touch φ Kc reg q u → pidOfAssign φ (src q) u.id.step = u :=
    fun q => (Classical.choose_spec (hsrc q)).2.2.1
  have hsw : ∀ q, Touch φ Kc reg q w → pidOfAssign φ (src q) w.id.step = w :=
    fun q => (Classical.choose_spec (hsrc q)).2.2.2.1
  have hsK : ∀ q v, WR φ lam v → ¬ KF v → AdjReg φ Kc reg q v → src q v = ax v :=
    fun q => (Classical.choose_spec (hsrc q)).2.2.2.2
  let g : Assign := fun z => if Kt z then ax z else if Fr z then fv z else src (reg z) z
  have gK : ∀ {z}, Kt z → g z = ax z := fun {z} h => if_pos h
  have gF : ∀ {z}, ¬ Kt z → Fr z → g z = fv z := fun {z} h hf => by simp only [g, if_neg h, if_pos hf]
  have gR : ∀ {z}, ¬ Kc z → g z = src (reg z) z := fun {z} h => by
    have h1 : ¬ Kt z := fun h' => h (h'.elim Or.inl (fun e => Or.inr (Or.inl e)))
    have h2 : ¬ Fr z := fun h' => h (Or.inr (Or.inr h'))
    simp only [g, if_neg h1, if_neg h2]
  have cut : ∀ {q z}, Kt z → AdjReg φ Kc reg q z → src q z = ax z := by
    intro q z hz ha
    by_cases hk : KF z
    · exact hfix _ _ (hsP q) hax z hk
    · exact hsK q z (hz.resolve_left hk) hk ha
  have hl := locPair_self hloc
  have hg : P g := by
    refine p0_of_sources hl ⟨ax, hax⟩ (fun z => ?_) (fun c hc => ?_)
    · by_cases h : Kt z
      · exact ⟨ax, hax, gK h⟩
      · by_cases hf : Fr z
        · obtain ⟨b, hb, e⟩ := fvP z
          exact ⟨b, hb, (gF h hf).trans e⟩
        · exact ⟨src (reg z), hsP _, gR (fun h' => h'.elim (fun e => h (Or.inl e))
            (fun e => e.elim (fun e' => h (Or.inr e')) hf))⟩
    · by_cases hex : ∃ z0, ClVar c z0 ∧ ¬ Kc z0
      · obtain ⟨z0, hz0, hn0⟩ := hex
        have one : ∀ {z}, ClVar c z → g z = src (reg z0) z := by
          intro z hz
          by_cases h : Kt z
          · rw [gK h, cut h ⟨c, hc, hz, z0, hz0, hn0, rfl⟩]
          · by_cases hf : Fr z
            · exact absurd (Or.inr (Or.inr ((hFr c hc z hz hf z0 hz0) ▸ hf))) hn0
            · have hn : ¬ Kc z := fun h' => h'.elim (fun e => h (Or.inl e))
                (fun e => e.elim (fun e' => h (Or.inr e')) hf)
              rw [gR hn, hp.cl c hc z z0 hz hz0 hn hn0]
        exact ⟨src (reg z0), hsP _, one (Or.inl rfl), one (Or.inr (Or.inl rfl)), one (Or.inr (Or.inr rfl))⟩
      · -- todas en el corte o libres
        by_cases hfree : ∃ z1, ClVar c z1 ∧ ¬ Kt z1 ∧ Fr z1
        · obtain ⟨z1, hz1, hk1, hf1⟩ := hfree
          have alleq : ∀ {z}, ClVar c z → z = z1 := fun {z} hz => hFr c hc z1 hz1 hf1 z hz
          obtain ⟨b, hb, e⟩ := fvP z1
          have one : ∀ {z}, ClVar c z → g z = b z := by
            intro z hz; rw [alleq hz, gF hk1 hf1, e]
          exact ⟨b, hb, one (Or.inl rfl), one (Or.inr (Or.inl rfl)), one (Or.inr (Or.inr rfl))⟩
        · have all : ∀ {z}, ClVar c z → g z = ax z := by
            intro z hz
            refine gK (Classical.byContradiction fun h => ?_)
            by_cases hf : Fr z
            · exact hfree ⟨z, hz, h, hf⟩
            · exact hex ⟨z, hz, fun h' => h'.elim (fun e => h (Or.inl e))
                (fun e => e.elim (fun e' => h (Or.inr e')) hf)⟩
          exact ⟨ax, hax, all (Or.inl rfl), all (Or.inr (Or.inl rfl)), all (Or.inr (Or.inr rfl))⟩
  have thr : ∀ {y : PathNodeId} {ay : Assign}, P ay → pidOfAssign φ ay y.id.step = y →
      (∀ z, WR φ lam z → ay z = ax z) → (∀ z, WR φ y.id.step z → fv z = ay z) →
      (∀ q, Touch φ Kc reg q y → pidOfAssign φ (src q) y.id.step = y) → pidOfAssign φ g y.id.step = y := by
    intro y ay hay ty Sy Fy hT
    refine (pid_of_agree (a0 := ay) (fun k' z hw hz => ?_)).trans ty
    have hr : WR φ y.id.step z := ⟨k', hw, hz⟩
    by_cases h : Kt z
    · rw [gK h]
      rcases h with hk | hk
      · exact hfix _ _ hax hay z hk
      · exact (Sy z hk).symm
    · by_cases hf : Fr z
      · rw [gF h hf]; exact Fy z hr
      · have hn : ¬ Kc z := fun h' => h'.elim (fun e => h (Or.inl e))
          (fun e => e.elim (fun e' => h (Or.inr e')) hf)
        rw [gR hn]
        exact agree_of_win ((hT (reg z) ⟨z, hn, rfl, hr⟩).trans ty.symm) hr
  exact ⟨g, hg, thr hax tx (fun _ _ => rfl) fvx hsx, thr hau tu Su fvu hsu, thr haw tw Sw fvw hsw⟩

theorem noCommon_of_pegF {P : Assign → Prop} (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g)
    {KF Fr : Nat → Prop} (hfix : ∀ a b, P a → P b → ∀ z, KF z → a z = b z) (hFr : FreeOK φ Fr)
    {lam : Int} {reg : Nat → Nat} {x u w : PathNodeId} (hp : PegF φ KF Fr lam reg x u w)
    (pxu : ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u)
    (pxw : ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w)
    (puw : ∃ a, P a ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w)
    (hno : ¬ ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
      pidOfAssign φ a w.id.step = w) :
    ∀ s, ¬ (NodeProj φ P x lam s ∧ NodeProj φ P u lam s ∧ NodeProj φ P w lam s) := by
  rintro s ⟨⟨ax, hax, tx, sx⟩, ⟨au, hau, tu, su⟩, ⟨aw, haw, tw, sw⟩⟩
  exact hno (glue_pegF hloc hfix hFr hp hax hau haw tx tu tw sx su sw pxu pxw puw)

/-- **`PegF` con el corte de las constantes, para cada trío Helly-fallido, da H2′.** -/
theorem twoWitnessF_of_pegF {P0 P : Assign → Prop} {N : Int}
    (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g) {Fr : Nat → Prop} (hFr : FreeOK φ Fr)
    (h : ∀ x u w : PathNodeId, x ≠ u → x ≠ w → u ≠ w → Tri0 φ P0 x u w →
      ¬ (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
        pidOfAssign φ a w.id.step = w) →
      ∃ lam reg, 0 ≤ lam ∧ lam < N ∧ lam ≠ x.id.step ∧ lam ≠ u.id.step ∧ lam ≠ w.id.step ∧
        PegF φ (ConstIn P) Fr lam reg x u w) :
    TwoWitnessF φ P0 P N := by
  intro x u w nxu nxw nuw h0 pxu pxw puw hno
  obtain ⟨lam, reg, l0, l1, lx, lu, lw, hp⟩ := h x u w nxu nxw nuw h0 hno
  refine ⟨lam, l0, l1, lx, lu, lw, fun s _ hx hu hw => ?_⟩
  exact absurd ⟨hx, hu, hw⟩
    (noCommon_of_pegF hloc (fun a b ha hb z hz => hz a b ha hb) hFr hp pxu pxw puw hno s)

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por nodos de ventana no se atasca con las líneas y `PegF`** (corte de las constantes, variables
libres en cláusulas de una sola variable). -/
theorem reader_winNode_of_pegF (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    {Fr : Nat → Prop} (hFr : FreeOK φ Fr)
    (h : ∀ (k : NodeId) (W0 : List (List NodeId)) (j : Nat) (gp p x : NodeId), (∀ v ∈ W0, WinTriple φ v) →
      j < φ.clauses.length → gp.step = clauseStep φ j 0 → p.step = clauseStep φ j 1 → x.step = clauseStep φ j 2 →
      ∀ x' u' w' : PathNodeId, x' ≠ u' → x' ≠ w' → u' ≠ w' →
        Tri0 φ (Pinned φ (SolE φ (stepCount φ) k) W0.flatten) x' u' w' →
        ¬ (∃ a, (Pinned φ (SolE φ (stepCount φ) k) W0.flatten a ∧ ∀ r ∈ [gp, p, x], selOfAssign φ a r.step = r) ∧
          pidOfAssign φ a x'.id.step = x' ∧ pidOfAssign φ a u'.id.step = u' ∧ pidOfAssign φ a w'.id.step = w') →
        ∃ lam reg, 0 ≤ lam ∧ lam < stepCount φ ∧ lam ≠ x'.id.step ∧ lam ≠ u'.id.step ∧ lam ≠ w'.id.step ∧
          PegF φ (ConstIn (fun a => Pinned φ (SolE φ (stepCount φ) k) W0.flatten a ∧
            ∀ r ∈ [gp, p, x], selOfAssign φ a r.step = r)) Fr lam reg x' u' w')
    {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading φ kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_winNode_of_twoWitnessF hbd HA (fun k W0 j gp p x hW0 hj s0 s1 s2 =>
    twoWitnessF_of_pegF loc_window hFr (h k W0 j gp p x hW0 hj s0 s1 s2)) hkv hr

end MachineOn

end AbsSatBingo.Model
