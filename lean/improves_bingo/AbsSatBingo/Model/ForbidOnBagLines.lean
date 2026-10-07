-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnBagLines.lean
import AbsSatBingo.Model.ForbidOnBagPad

/-!
# Las líneas con bolsas: `PhantomAtW` sin hipótesis en la acolchada por bolsas

Para las líneas hace falta H2′ con un `λ` bajo la línea `N`. El truco es el orden: **las bolsas se leen antes de que
se compruebe ninguna cláusula real** (`BagsFirst`). Entonces solo hay dos casos:

* **Alguna ventana bajo `N` puede estar prohibida**: es el tercer paso de una cláusula real, y todas las bolsas se
  leyeron antes. El corte de la bolsa separadora cae bajo `N` y vale la prueba del lector (`witness_bags`).
* **Ninguna puede estarlo**: bajo `N` solo hay tautologías, la familia solo fija nodos de una variable cada uno y es
  un producto. El trío tiene rama común pegando variable a variable (`glue_regionsS`): no era Helly-fallido.

Para el segundo caso la localidad se afina: en un paso donde nada puede estar prohibido (`SafeAt`) basta elegir el
mismo nodo (`LAgreeS`, `LocBelowS`).

* **`twoWitnessF_of_bagsN`**, **`phantomAtW_of_bags`**: con `BagsFirst`, las líneas sin hipótesis.
* **`bagsFirst_td`**: la acolchada por bolsas lee las bolsas primero.
* **`phantomAtW_td`**, **`machineExactW_td`**, **`reader_winNode_td_free`**, **`reader_winNode_tri_free`**: la máquina
  exacta y el lector sin hipótesis en la acolchada de toda fórmula de anchura de árbol ≤ 2, ciclos incluidos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- En el paso `q` ninguna rama puede estar prohibida. -/
def SafeAt (φ : Cnf) (q : Int) : Prop := ∀ g : Assign, isProhibited φ (pidOfAssign φ g q) = false

/-- Coincidir localmente, sin pedir la ventana donde nada puede estar prohibido. -/
def LAgreeS (φ : Cnf) (q : Int) (g a : Assign) : Prop :=
  selOfAssign φ g q = selOfAssign φ a q ∧ (¬ SafeAt φ q → pidOfAssign φ g q = pidOfAssign φ a q)

/-- **Local bajo `N`, afinado.** -/
def LocBelowS (φ : Cnf) (P : Assign → Prop) (N : Int) : Prop :=
  ∀ g, (∀ q, q < N → ∃ a, P a ∧ LAgreeS φ q g a) → P g

theorem isL3_of_unsafe {q : Int} (h : ¬ SafeAt φ q) : isL3 φ q = true :=
  Classical.byContradiction fun hn => h (fun g => by
    cases hp : isProhibited φ (pidOfAssign φ g q) with
    | false => rfl
    | true =>
      exact absurd (by have := isL3_of_prohibited hp; rwa [Machine.pid_step] at this) hn)

theorem LocBelowS.locBelow {P : Assign → Prop} {N : Int} (h : LocBelowS φ P N) : LocBelow φ P N :=
  fun g hg => h g (fun q hq => by
    obtain ⟨a, ha, h1, h2⟩ := hg q hq
    exact ⟨a, ha, h1, fun hs => h2 (isL3_of_unsafe hs)⟩)

theorem validUpTo_of_belowS {g : Assign} {T : Int} {Q : Assign → Prop} (hQ : ∀ a, Q a → ValidUpTo φ a T)
    (h : ∀ q, q < T → ∃ a, Q a ∧ LAgreeS φ q g a) : ValidUpTo φ g T := by
  intro q hq
  cases hp : isProhibited φ (pidOfAssign φ g q) with
  | false => rfl
  | true =>
    exfalso
    have hns : ¬ SafeAt φ q := fun hs => by rw [hs g] at hp; cases hp
    obtain ⟨a, ha, _, hpid⟩ := h q hq
    rw [hpid hns, hQ a ha q hq] at hp
    cases hp

theorem locBelowS_filter {T : Int} {k r : NodeId} (hr : r.step < T) :
    LocBelowS φ (fun a => SolE φ T k a ∧ selOfAssign φ a r.step = r) T := by
  intro g h
  refine ⟨⟨validUpTo_of_belowS (fun a ha => ha.1.1) h, ?_⟩, ?_⟩
  · obtain ⟨a, ha, hsel, _⟩ := h (T - 1) (by omega)
    exact hsel.trans ha.1.2
  · obtain ⟨a, ha, hsel, _⟩ := h r.step hr
    exact hsel.trans ha.2

theorem locBelowS_up {T : Int} {d : NodeId} : LocBelowS φ (SolE φ (T + 1) d) (T + 1) := by
  intro g h
  refine ⟨validUpTo_of_belowS (fun a ha => ha.1) h, ?_⟩
  obtain ⟨a, ha, hsel, _⟩ := h (T + 1 - 1) (by omega)
  exact hsel.trans ha.2

/-- **El pegado por regiones**, con la localidad afinada. -/
theorem glue_regionsS {P : Assign → Prop} {N : Int} (hloc : LocBelowS φ P N) (reg : Nat → Nat)
    (hfp : ∀ q, q < N → ∃ Q, ∀ g a, (∀ z, reg z = Q → g z = a z) → LAgreeS φ q g a)
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

/-- **Las bolsas primero**: toda bolsa se lee no más tarde que cualquier ventana que pueda estar prohibida. -/
def BagsFirst {Fr : Nat → Prop} (D : BagDec φ Fr) : Prop :=
  ∀ t q (g : Assign), isProhibited φ (pidOfAssign φ g q) = true → D.cut t ≤ q

namespace BagDec

variable {Fr : Nat → Prop} (D : BagDec φ Fr)

include D in
/-- **H2′ bajo `N` con bolsas leídas primero.** -/
theorem twoWitnessF_of_bagsN (hFr : FreeOK φ Fr) (hfirst : BagsFirst D) {P0 P : Assign → Prop} {N : Int}
    (hloc : LocBelowS φ P N) : TwoWitnessF φ P0 P N := by
  classical
  intro x u w nxu nxw nuw _ pxu pxw puw hno
  by_cases hs : ∀ q, q < N → SafeAt φ q
  · -- nada puede estar prohibido bajo `N`: la familia es un producto y el trío tiene rama común
    exfalso
    apply hno
    obtain ⟨a1, h1, x1, u1⟩ := pxu
    obtain ⟨a2, h2, x2, w2⟩ := pxw
    obtain ⟨a3, h3, u3, w3⟩ := puw
    refine glue_regionsS hloc (fun z => z) (fun q hq => ⟨(stepVar φ q).getD 0, fun g a hga =>
      ⟨sel_eq_of_var (fun v hv => hga v (by rw [hv]; rfl)), fun hn => absurd (hs q hq) hn⟩⟩)
      x1 u1 w2 (fun Q => src_cover h1 h2 h3 x1 u1 x2 w2 u3 w3 Q ?_)
    by_cases hx : WR φ x.id.step Q
    · exact Or.inl (fun z hz _ => Or.inl (by rw [show z = Q from hz]; exact hx))
    · by_cases hu : WR φ u.id.step Q
      · exact Or.inl (fun z hz _ => Or.inr (by rw [show z = Q from hz]; exact hu))
      · exact Or.inr (Or.inr (fun z hz hxz => absurd (by rw [show z = Q from hz] at hxz; exact hxz) hx))
  · -- alguna ventana bajo `N` puede estar prohibida: todas las bolsas se leyeron antes
    obtain ⟨q0, hq0, hns⟩ : ∃ q, q < N ∧ ¬ SafeAt φ q :=
      Classical.byContradiction fun hn => hs (fun q hq => Classical.byContradiction fun h => hn ⟨q, hq, h⟩)
    obtain ⟨g0, hg0⟩ : ∃ g, isProhibited φ (pidOfAssign φ g q0) = true :=
      Classical.byContradiction fun hn => hns (fun g => by
        cases e : isProhibited φ (pidOfAssign φ g q0) with
        | false => rfl
        | true => exact absurd ⟨g, e⟩ hn)
    obtain ⟨Bx, hBx⟩ := D.loc x.id.step
    obtain ⟨Bu, hBu⟩ := D.loc u.id.step
    obtain ⟨Bw, hBw⟩ := D.loc w.id.step
    exact D.witness_bags hFr hloc.locBelow.loc hBx hBu hBw
      (fun m _ => Int.lt_of_le_of_lt (hfirst m q0 g0 hg0) hq0) pxu pxw puw hno

end BagDec

namespace GPathB

open Driver Machine MachineOn

/-- **Las líneas con bolsas leídas primero**: `PhantomAtW` en cada línea, sin hipótesis. -/
theorem phantomAtW_of_bags (hbd : Bounded φ) {Fr : Nat → Prop} (D : BagDec φ Fr) (hFr : FreeOK φ Fr)
    (hfirst : BagsFirst D) {T : Int} (hT : 1 ≤ T) : PhantomAtW φ T := by
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step φ k d hd
    have hks := mapNodes_step φ (T - 1) k hk
    omega
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨r1, r2⟩ := reqOf_range hbd r hr
    rw [hds] at r2
    exact phantomFree_of_twoWitnessF (by omega) r2 (D.twoWitnessF_of_bagsN hFr hfirst (locBelowS_filter r2))
  · exact phantomFree_of_twoWitnessF (by omega) (by omega) (D.twoWitnessF_of_bagsN hFr hfirst locBelowS_up)

end GPathB

-- ============================================================
-- La acolchada por bolsas lee las bolsas primero
-- ============================================================

variable {bags : List (Nat × Nat × Nat)}

/-- Fuera de las cláusulas reales, todo bloque del acolchado es tautológico. -/
theorem tdAt_sat {j : Nat} (hj : j / 3 < bags.length ∨ j % 3 ≠ 1) (a : Assign) : SatClause a (tdAt φ bags j) := by
  unfold tdAt
  split
  · exact satClause_taut a
  · split
    · split
      · exact satClause_rd1 a _
      · exact satClause_rd2 a _
    · split
      · omega
      · exact satClause_taut a

theorem TDec.bagsFirst_td (D : TDec φ) : BagsFirst D.bagDec := by
  intro t q g hp
  obtain ⟨j, c, hj, e, f1, f2, f3⟩ := prohibited_clause hp
  rw [td_getElem?] at hj
  split at hj
  · cases hj
    have hpad : D.bags.length ≤ j / 3 ∧ j % 3 = 1 := by
      refine Classical.byContradiction fun hn => ?_
      have hs := tdAt_sat (φ := φ) (bags := D.bags) (j := j) (by omega) g
      unfold SatClause at hs
      rw [f1, f2, f3] at hs
      simp at hs
    show D.tdCut t ≤ q
    cases t with
    | var b =>
      simp only [TDec.tdCut]
      split
      · rw [e]; simp only [clauseStep]; omega
      · rw [e]; simp only [clauseStep]; omega
    | cls i => rw [e]; simp only [TDec.tdCut, clauseStep]; omega
  · cases hj

namespace GPathB

/-- **Las líneas de la acolchada por bolsas**, sin hipótesis. -/
theorem phantomAtW_td (hbd : Bounded φ) (D : TDec φ) : ∀ T : Int, 1 ≤ T → PhantomAtW (tdCnf φ D.bags) T :=
  fun _ hT => phantomAtW_of_bags (bounded_td hbd D.bnd) D.bagDec freeOK_td D.bagsFirst_td hT

/-- **La máquina es exacta** en la acolchada por bolsas de toda fórmula de anchura de árbol ≤ 2. -/
theorem machineExactW_td (hbd : Bounded φ) (D : TDec φ) : MachineExactW (tdCnf φ D.bags) :=
  (machineExactW_iff (bounded_td hbd D.bnd)).mpr (phantomAtW_td hbd D)

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por nodos de ventana no se atasca**, sin hipótesis, en la acolchada por bolsas de toda fórmula de
anchura de árbol ≤ 2 (que es satisfacible si y solo si la original lo es). -/
theorem reader_winNode_td_free (hbd : Bounded φ) (D : TDec φ) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on (tdCnf φ D.bags)) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading (tdCnf φ D.bags) kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a (tdCnf φ D.bags) ∧
      (∀ q ∈ W.flatten, selOfAssign (tdCnf φ D.bags) a q.step = q) ∧ CT g' (pidOfAssign (tdCnf φ D.bags) a) :=
  reader_winNode_td hbd D (phantomAtW_td hbd D) hkv hr

/-- **El triángulo con orejas** (una fórmula con un ciclo), acolchado: el lector no se atasca, sin hipótesis. -/
theorem reader_winNode_tri_free {kv : NodeId × GPathB} (hkv : kv ∈ runM .on (tdCnf triCnf triBags))
    {W : List (List NodeId)} {g' : GPathB} (hr : WinReading (tdCnf triCnf triBags) kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a (tdCnf triCnf triBags) ∧
      (∀ q ∈ W.flatten, selOfAssign (tdCnf triCnf triBags) a q.step = q) ∧
      CT g' (pidOfAssign (tdCnf triCnf triBags) a) :=
  reader_winNode_td_free bounded_tri triDec hkv hr

end MachineOn

end AbsSatBingo.Model
