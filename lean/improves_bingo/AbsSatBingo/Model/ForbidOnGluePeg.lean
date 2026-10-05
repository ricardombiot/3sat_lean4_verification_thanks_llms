-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnGluePeg.lean
import AbsSatBingo.Model.ForbidOnWinBridge

/-!
# El pegado en un paso λ: H2′ desde el grafo de la fórmula

Un trío `x, u, w` sin rama de `P` por los tres, con ramas de `P` por cada pareja, y un paso `λ`. El **corte** `Kc` son
las variables fijadas en `P` (`KF`, donde todas las ramas de `P` coinciden) y las que lee la ventana de `λ`. Las
**regiones** (`reg`) parten el resto de modo que las variables de cada cláusula fuera del corte están en una sola
región (las componentes del grafo primal sin el corte lo cumplen).

**`Peg`**: ninguna región toca lo que leen los tres nodos, y si toca lo de dos, las variables de `λ` vecinas de la
región las lee uno de esos dos.

* **`glue_peg`**: si un nodo `s` de `λ` fuera alcanzable por ramas de `P` desde los tres, pegando por regiones (una
  rama por cada nodo que la región toca, o la de la pareja) y el corte (común a las ramas que pasan por `s`) sale una
  rama de `P` por los tres (`p0_of_sources`).
* **`noCommon_of_peg`**: con `Peg` en `λ`, ningún `s` de `λ` es alcanzable desde los tres (H2 en `λ`).
* **`twoWitnessF_of_peg`**: si todo trío Helly-fallido tiene un `λ` fuera de sus pasos con `Peg`, vale H2′.
* **`reader_winNode_of_peg`**: el lector por nodos de ventana no se atasca con las líneas y `Peg` en cada ventana.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- La ventana del paso `k` lee la variable `z`. -/
def WR (φ : Cnf) (k : Int) (z : Nat) : Prop := ∃ k', InWin k k' ∧ stepVar φ k' = some z

/-- Dos ramas con la misma ventana en `k` coinciden en lo que esa ventana lee. -/
theorem agree_of_win {a b : Assign} {k : Int} (h : pidOfAssign φ a k = pidOfAssign φ b k) {z : Nat}
    (hz : WR φ k z) : a z = b z := by
  obtain ⟨k', hw, hs⟩ := hz
  exact var_of_pid_eq h hw hs

/-- La región `q` toca lo que lee el nodo `y`. -/
def Touch (φ : Cnf) (Kc : Nat → Prop) (reg : Nat → Nat) (q : Nat) (y : PathNodeId) : Prop :=
  ∃ z, ¬ Kc z ∧ reg z = q ∧ WR φ y.id.step z

/-- La variable `v` es vecina de la región `q`: comparte una cláusula con una variable de `q` fuera del corte. -/
def AdjReg (φ : Cnf) (Kc : Nat → Prop) (reg : Nat → Nat) (q : Nat) (v : Nat) : Prop :=
  ∃ c ∈ φ.clauses, ClVar c v ∧ ∃ z0, ClVar c z0 ∧ ¬ Kc z0 ∧ reg z0 = q

/-- **El pegado en `λ`** para el trío `x, u, w`, con las variables fijadas `KF` y las regiones `reg`. -/
structure Peg (φ : Cnf) (KF : Nat → Prop) (lam : Int) (reg : Nat → Nat) (x u w : PathNodeId) : Prop where
  cl  : ∀ c ∈ φ.clauses, ∀ z z', ClVar c z → ClVar c z' → ¬ (KF z ∨ WR φ lam z) → ¬ (KF z' ∨ WR φ lam z') →
          reg z = reg z'
  no3 : ∀ q, ¬ (Touch φ (fun z => KF z ∨ WR φ lam z) reg q x ∧ Touch φ (fun z => KF z ∨ WR φ lam z) reg q u ∧
          Touch φ (fun z => KF z ∨ WR φ lam z) reg q w)
  two : ∀ q (y z : PathNodeId), (y = x ∧ z = u ∨ y = x ∧ z = w ∨ y = u ∧ z = w) →
          Touch φ (fun z => KF z ∨ WR φ lam z) reg q y → Touch φ (fun z => KF z ∨ WR φ lam z) reg q z →
          ∀ v, WR φ lam v → ¬ KF v → AdjReg φ (fun z => KF z ∨ WR φ lam z) reg q v →
          WR φ y.id.step v ∨ WR φ z.id.step v

/-- Una familia cerrada por coincidencias locales es un `LocPair` consigo misma en el paso `0`. -/
theorem locPair_self {P : Assign → Prop} (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g) :
    LocPair φ P P 0 :=
  ⟨fun _ h => h, hloc, fun _ h _ => h, fun _ _ _ _ => sel_eq_of_var (fun z hz => by simp [stepVar] at hz)⟩

/-- **El pegado.** -/
theorem glue_peg {P : Assign → Prop} (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g)
    {KF : Nat → Prop} (hfix : ∀ a b, P a → P b → ∀ z, KF z → a z = b z)
    {lam : Int} {reg : Nat → Nat} {x u w s : PathNodeId} (hp : Peg φ KF lam reg x u w)
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
  let Kc : Nat → Prop := fun z => KF z ∨ WR φ lam z
  -- en lo que lee `λ`, las tres fuentes por `s` coinciden con `ax`
  have Su : ∀ z, WR φ lam z → au z = ax z := fun z hz => agree_of_win (su.trans sx.symm) hz
  have Sw : ∀ z, WR φ lam z → aw z = ax z := fun z hz => agree_of_win (sw.trans sx.symm) hz
  -- una fuente por región
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
  let g : Assign := fun z => if Kc z then ax z else src (reg z) z
  have gK : ∀ {z}, Kc z → g z = ax z := fun {z} h => if_pos h
  have gR : ∀ {z}, ¬ Kc z → g z = src (reg z) z := fun {z} h => if_neg h
  -- en el corte, cualquier fuente de una región vecina coincide con `ax`
  have cut : ∀ {q z}, Kc z → AdjReg φ Kc reg q z → src q z = ax z := by
    intro q z hz ha
    by_cases hk : KF z
    · exact hfix _ _ (hsP q) hax z hk
    · exact hsK q z (hz.resolve_left hk) hk ha
  have hl := locPair_self hloc
  have hg : P g := by
    refine p0_of_sources hl ⟨ax, hax⟩ (fun z => ?_) (fun c hc => ?_)
    · by_cases h : Kc z
      · exact ⟨ax, hax, gK h⟩
      · exact ⟨src (reg z), hsP _, gR h⟩
    · by_cases hex : ∃ z0, ClVar c z0 ∧ ¬ Kc z0
      · obtain ⟨z0, hz0, hn0⟩ := hex
        have one : ∀ {z}, ClVar c z → g z = src (reg z0) z := by
          intro z hz
          by_cases h : Kc z
          · rw [gK h, cut h ⟨c, hc, hz, z0, hz0, hn0, rfl⟩]
          · rw [gR h, hp.cl c hc z z0 hz hz0 h hn0]
        exact ⟨src (reg z0), hsP _, one (Or.inl rfl), one (Or.inr (Or.inl rfl)), one (Or.inr (Or.inr rfl))⟩
      · have all : ∀ {z}, ClVar c z → g z = ax z := fun {z} hz =>
          gK (Classical.byContradiction fun h => hex ⟨z, hz, h⟩)
        exact ⟨ax, hax, all (Or.inl rfl), all (Or.inr (Or.inl rfl)), all (Or.inr (Or.inr rfl))⟩
  -- por cada nodo del trío, `g` lee lo mismo que su fuente
  have thr : ∀ {y : PathNodeId} {ay : Assign}, P ay → pidOfAssign φ ay y.id.step = y →
      (∀ z, WR φ lam z → ay z = ax z) →
      (∀ q, Touch φ Kc reg q y → pidOfAssign φ (src q) y.id.step = y) → pidOfAssign φ g y.id.step = y := by
    intro y ay hay ty Sy hT
    refine (pid_of_agree (a0 := ay) (fun k' z hw hz => ?_)).trans ty
    have hr : WR φ y.id.step z := ⟨k', hw, hz⟩
    by_cases h : Kc z
    · rw [gK h]
      rcases h with hk | hk
      · exact hfix _ _ hax hay z hk
      · exact (Sy z hk).symm
    · rw [gR h]
      exact agree_of_win ((hT (reg z) ⟨z, h, rfl, hr⟩).trans ty.symm) hr
  exact ⟨g, hg, thr hax tx (fun _ _ => rfl) hsx, thr hau tu Su hsu, thr haw tw Sw hsw⟩

/-- **Con `Peg` en `λ`, ningún nodo de `λ` es alcanzable desde los tres** (si no hay rama de `P` por los tres). -/
theorem noCommon_of_peg {P : Assign → Prop} (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g)
    {KF : Nat → Prop} (hfix : ∀ a b, P a → P b → ∀ z, KF z → a z = b z)
    {lam : Int} {reg : Nat → Nat} {x u w : PathNodeId} (hp : Peg φ KF lam reg x u w)
    (pxu : ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u)
    (pxw : ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w)
    (puw : ∃ a, P a ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w)
    (hno : ¬ ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
      pidOfAssign φ a w.id.step = w) :
    ∀ s, ¬ (NodeProj φ P x lam s ∧ NodeProj φ P u lam s ∧ NodeProj φ P w lam s) := by
  rintro s ⟨⟨ax, hax, tx, sx⟩, ⟨au, hau, tu, su⟩, ⟨aw, haw, tw, sw⟩⟩
  exact hno (glue_peg hloc hfix hp hax hau haw tx tu tw sx su sw pxu pxw puw)

/-- **`Peg` para cada trío Helly-fallido da H2′.** -/
theorem twoWitnessF_of_peg {P0 P : Assign → Prop} {N : Int}
    (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g)
    {KF : Nat → Prop} (hfix : ∀ a b, P a → P b → ∀ z, KF z → a z = b z)
    (h : ∀ x u w : PathNodeId, x ≠ u → x ≠ w → u ≠ w → Tri0 φ P0 x u w →
      ¬ (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
        pidOfAssign φ a w.id.step = w) →
      ∃ lam reg, 0 ≤ lam ∧ lam < N ∧ lam ≠ x.id.step ∧ lam ≠ u.id.step ∧ lam ≠ w.id.step ∧
        Peg φ KF lam reg x u w) :
    TwoWitnessF φ P0 P N := by
  intro x u w nxu nxw nuw h0 pxu pxw puw hno
  obtain ⟨lam, reg, l0, l1, lx, lu, lw, hp⟩ := h x u w nxu nxw nuw h0 hno
  refine ⟨lam, l0, l1, lx, lu, lw, fun s _ hx hu hw => ?_⟩
  exact absurd ⟨hx, hu, hw⟩ (noCommon_of_peg hloc hfix hp pxu pxw puw hno s)

/-- Las variables que leen los pasos de una lista de elecciones (fijadas en la familia que las cumple). -/
def PinVars (φ : Cnf) (R : List NodeId) (z : Nat) : Prop := ∃ r ∈ R, stepVar φ r.step = some z

namespace GPathB

open Driver Machine MachineOn

/-- La familia de una ventana más es cerrada por coincidencias locales. -/
theorem loc_window {T : Int} {k : NodeId} {R w : List NodeId} :
    ∀ g, (∀ q, ∃ a, (Pinned φ (SolE φ T k) R a ∧ ∀ r ∈ w, selOfAssign φ a r.step = r) ∧ LAgree φ q g a) →
      (Pinned φ (SolE φ T k) R g ∧ ∀ r ∈ w, selOfAssign φ g r.step = r) := by
  intro g h
  have hl := locPair_read (φ := φ) T k (R ++ w) ⟨0, 0⟩
  have hg := hl.loc g (fun q => by
    obtain ⟨a, ⟨⟨ha, hR⟩, hw⟩, hag⟩ := h q
    exact ⟨a, ⟨ha, fun r hr => (List.mem_append.mp hr).elim (hR r) (hw r)⟩, hag⟩)
  exact ⟨⟨hg.1, fun r hr => hg.2 r (List.mem_append_left _ hr)⟩, fun r hr => hg.2 r (List.mem_append_right _ hr)⟩

/-- En la familia de una ventana más, todas las ramas leen igual las variables fijadas. -/
theorem fix_window {T : Int} {k : NodeId} {R w : List NodeId} :
    ∀ a b, (Pinned φ (SolE φ T k) R a ∧ ∀ r ∈ w, selOfAssign φ a r.step = r) →
      (Pinned φ (SolE φ T k) R b ∧ ∀ r ∈ w, selOfAssign φ b r.step = r) → ∀ z, PinVars φ (R ++ w) z → a z = b z := by
  intro a b ha hb z ⟨r, hr, hz⟩
  have sa : selOfAssign φ a r.step = r := (List.mem_append.mp hr).elim (ha.1.2 r) (ha.2 r)
  have sb : selOfAssign φ b r.step = r := (List.mem_append.mp hr).elim (hb.1.2 r) (hb.2 r)
  exact var_eq_of_sel (sa.trans sb.symm) z hz

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por nodos de ventana no se atasca con las líneas y `Peg`**: para cada ventana (con cualesquiera
ventanas antes) y cada trío Helly-fallido, un paso `λ` fuera de los del trío cuya ventana, con las variables fijadas,
corta la fórmula de modo que ninguna región toque los tres nodos. -/
theorem reader_winNode_of_peg (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (h : ∀ (k : NodeId) (W0 : List (List NodeId)) (j : Nat) (gp p x : NodeId), (∀ v ∈ W0, WinTriple φ v) →
      j < φ.clauses.length → gp.step = clauseStep φ j 0 → p.step = clauseStep φ j 1 → x.step = clauseStep φ j 2 →
      ∀ x' u' w' : PathNodeId, x' ≠ u' → x' ≠ w' → u' ≠ w' →
        Tri0 φ (Pinned φ (SolE φ (stepCount φ) k) W0.flatten) x' u' w' →
        ¬ (∃ a, (Pinned φ (SolE φ (stepCount φ) k) W0.flatten a ∧ ∀ r ∈ [gp, p, x], selOfAssign φ a r.step = r) ∧
          pidOfAssign φ a x'.id.step = x' ∧ pidOfAssign φ a u'.id.step = u' ∧ pidOfAssign φ a w'.id.step = w') →
        ∃ lam reg, 0 ≤ lam ∧ lam < stepCount φ ∧ lam ≠ x'.id.step ∧ lam ≠ u'.id.step ∧ lam ≠ w'.id.step ∧
          Peg φ (PinVars φ (W0.flatten ++ [gp, p, x])) lam reg x' u' w')
    {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading φ kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_winNode_of_twoWitnessF hbd HA (fun k W0 j gp p x hW0 hj s0 s1 s2 =>
    twoWitnessF_of_peg loc_window fix_window (h k W0 j gp p x hW0 hj s0 s1 s2)) hkv hr

end MachineOn

end AbsSatBingo.Model
