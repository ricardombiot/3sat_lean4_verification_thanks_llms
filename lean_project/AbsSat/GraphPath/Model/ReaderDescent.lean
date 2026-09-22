-- lean_project/AbsSat/GraphPath/Model/ReaderDescent.lean
import AbsSat.GraphPath.Model.PinExtends
import AbsSat.GraphPath.Model.Descent

/-!
# El lector no se atasca: del descenso a la respuesta de la máquina

`NoDeadEndVerdict.sat_of_*` saca `Satisfiable φ` del **estado final**. Eso es un hecho sobre la
fórmula, no sobre lo que la máquina imprime: fuera de `ReaderExec` ningún teorema del repo concluía
`readerVerdictW φ = true`, así que la mejor hipótesis medida seguía permitiendo un `unknown`.

Este módulo cierra ese hueco. Pedido **a lo largo de la trayectoria del lector**, el descenso da
`PinExtends`, y con él todo lo que `PinExtends.lean` ya demuestra:

* **`chain_of_commonOwner`** — un estado válido del lector con `CommonOwner` tiene cadena
  (`noDeadEnd_of_commonOwner` → `topAnchor_of` → `nonempty_of_noDeadEnd`).
* **`pinExtends_of_commonOwner`** — el pin que el lector necesita es el nodo que la propia cadena
  elige en ese paso. Descarga `PinExtends` entera.
* **`answer_ne_unknown_*`** / **`answer_unsat_*`** — *la máquina nunca contesta `unknown`*, y sobre
  una fórmula insatisfacible contesta `unsat`.

Y dos maneras de tener `CommonOwner` en un estado, que son las dos puntas del inventario:

| | |
|---|---|
| **`AllParentsOwn`** (`Descent.commonOwner_of_allParentsOwn`) | *el padre no hay que elegirlo*: todo padre posee a todo owner de arriba. **No acota el in-degree.** Es la forma precisa de la intuición de que al lector siempre le queda un camino por el que bajar |
| **`PairMeet` + `TwoParents`** (`Descent.commonOwner_of_pairMeet`) | Helly con número dos: acota el in-degree a 2 y pide que los pares se encuentren |

`ReaderDescent.twoParents_of_pruned` hace que `TwoParents` solo haga falta en la semilla; las otras
dos son hipótesis sobre la trayectoria.
-/

namespace AbsSat.GraphPath.Model.ReaderDescent

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.PinExtends
open AbsSat.GraphPath.Model.Answer (Answer answer)

-- ============================================================
-- El descenso en un estado de la trayectoria
-- ============================================================

/-- **Un estado válido del lector con `CommonOwner` tiene cadena.** El ancla de arriba es gratis
(`topAnchor_of`), `CommonOwner` da la extensión de un paso (`noDeadEnd_of_commonOwner`), y un
descenso que llega al paso 0 es una cadena `ChainSound`. -/
theorem chain_of_commonOwner (S : GPathM) (h : RF S) (hv : isValid S = true)
    (hpos : 0 < S.current_step) (hco : Descent.CommonOwner S) : ∃ sel, ChainSound S sel := by
  have a := adj_rf h hv
  have hnd := Descent.noDeadEnd_of_commonOwner S a (aggOk_rf h hv) hco
  have ha := NoDeadEnd.topAnchor_of S hv hpos a.rc.gn a.rc.oos a.rc.shape a.rc.rootz
    (fun q d hd => a.ctx.nodeval q d hd)
  obtain ⟨_, sel, hsc, _⟩ := NoDeadEnd.nonempty_of_noDeadEnd S hpos ha hnd
  exact ⟨sel, hsc⟩

/-- **El pin que el lector necesita es el nodo que la cadena elige.** Pinchar el nodo de mapa que la
cadena selecciona en el paso `l` conserva la cadena (`ChainSound_filterAllAgg`), y una cadena hace
válido el estado (`isValid_of_ChainG`). Así que el descenso, a lo largo de la trayectoria, descarga
`PinExtends`. -/
theorem pinExtends_of_commonOwner (g₀ : GPathM) (h0 : RF g₀) (hpos : 0 < g₀.current_step)
    (hco : ∀ S, ReadFrom g₀ S → isValid S = true → Descent.CommonOwner S) : PinExtends g₀ := by
  intro S hS hv l hl0 hl1
  obtain ⟨hrf, hpr⟩ := rf_readFrom h0 hS
  obtain ⟨sel, hsc⟩ := chain_of_commonOwner S hrf hv (by rw [hpr.step_eq]; exact hpos) (hco S hS hv)
  obtain ⟨_, hstep⟩ := hsc.chain.1.1 l hl0 hl1
  refine ⟨(sel l).id, hstep, ?_⟩
  refine PickInduction.isValid_of_ChainG _ sel
    (ChainSound_filterAllAgg S [(sel l).id] sel hsc ?_).chain
  intro req hreq _ _
  rw [List.mem_singleton.mp hreq, hstep]

-- ============================================================
-- `TwoParents` desciende por poda
-- ============================================================

/-- **Un estrechamiento conserva «a lo sumo dos padres».** `Pruned` deriva cada nodo de uno del
estado más ancho con su lista de padres contenida. Todo estado que el lector alcanza es un `Pruned`
del de partida (`rf_readFrom`), así que `TwoParents` solo hay que comprobarlo en la semilla. -/
theorem twoParents_of_pruned {g g' : GPathM} (hpr : Pruned g g')
    (h : Descent.TwoParents g) : Descent.TwoParents g' := by
  intro n' hn' c hc c' hc' c'' hc''
  obtain ⟨n, hn, _, _, hpar⟩ := hpr.nodes_derived n' hn'
  exact h n hn c (hpar c hc) c' (hpar c' hc') c'' (hpar c'' hc'')

-- ============================================================
-- Las dos maneras de tener `CommonOwner`
-- ============================================================

/-- **La intuición, en un estado**: si el padre no hay que elegirlo, el descenso baja. Sin cota
ninguna sobre el in-degree. -/
theorem commonOwner_of_allParentsOwn_rf (S : GPathM) (h : RF S) (hv : isValid S = true)
    (hap : Descent.AllParentsOwn S) : Descent.CommonOwner S :=
  Descent.commonOwner_of_allParentsOwn S (adj_rf h hv) (aggOk_rf h hv) hap

/-- **La vía de Helly**: in-degree acotado a dos, y los pares se encuentran. -/
theorem commonOwner_of_pairMeet_rf (S : GPathM) (h : RF S) (hv : isValid S = true)
    (htp : Descent.TwoParents S) (hpm : Descent.PairMeet S) : Descent.CommonOwner S :=
  Descent.commonOwner_of_pairMeet S (adj_rf h hv) (aggOk_rf h hv) htp hpm

-- ============================================================
-- La corrida, y la respuesta de la máquina
-- ============================================================

variable (φ : Cnf)

/-- **La hipótesis de la intuición, sobre la corrida**: en todo estado que el lector alcanza desde
todo estado de la línea final, ningún padre hay que elegirlo. -/
def RunAllParentsOwn : Prop :=
  ∀ kv ∈ pureRunW φ, ∀ S, ReadFrom (filterAllAgg kv.2 []) S → isValid S = true →
    Descent.AllParentsOwn S

/-- La vía de Helly, sobre la corrida. `TwoParents` solo en la semilla. -/
def RunPairMeet : Prop :=
  ∀ kv ∈ pureRunW φ, ∀ S, ReadFrom (filterAllAgg kv.2 []) S → isValid S = true →
    Descent.PairMeet S

def RunTwoParents : Prop :=
  ∀ kv ∈ pureRunW φ, Descent.TwoParents (filterAllAgg kv.2 [])

theorem pos_final (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) :
    0 < (filterAllAgg kv.2 []).current_step := by
  obtain ⟨_, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  rw [(pruned_filterAllAgg kv.2 []).step_eq, hstep]
  exact ConservationCore.stepCount_pos φ

theorem runPinExtends_of_allParentsOwn (hwf : WF φ) (hap : RunAllParentsOwn φ) :
    RunPinExtends φ := fun kv hkv =>
  pinExtends_of_commonOwner _ (rf_final φ hwf kv hkv) (pos_final φ hwf kv hkv)
    (fun S hS hv => commonOwner_of_allParentsOwn_rf S (rf_readFrom (rf_final φ hwf kv hkv) hS).1 hv
      (hap kv hkv S hS hv))

theorem runPinExtends_of_pairMeet (hwf : WF φ) (htp : RunTwoParents φ) (hpm : RunPairMeet φ) :
    RunPinExtends φ := fun kv hkv =>
  pinExtends_of_commonOwner _ (rf_final φ hwf kv hkv) (pos_final φ hwf kv hkv)
    (fun S hS hv =>
      commonOwner_of_pairMeet_rf S (rf_readFrom (rf_final φ hwf kv hkv) hS).1 hv
        (twoParents_of_pruned (rf_readFrom (rf_final φ hwf kv hkv) hS).2 (htp kv hkv))
        (hpm kv hkv S hS hv))

/-- **El lector no se atasca**, bajo la intuición: la máquina nunca contesta `unknown`. Esto es lo
que `NoDeadEndVerdict.sat_of_*` **no** daba — demostraban la fórmula satisfacible, no que la máquina
lo diga. -/
theorem answer_ne_unknown_apo (hwf : WF φ) (hap : RunAllParentsOwn φ) : answer φ ≠ .unknown :=
  answer_ne_unknown_px φ hwf (runPinExtends_of_allParentsOwn φ hwf hap)

/-- Y sobre una fórmula insatisfacible contesta `unsat`. -/
theorem answer_unsat_apo (hwf : WF φ) (hap : RunAllParentsOwn φ) (hns : ¬ Satisfiable φ) :
    answer φ = .unsat :=
  answer_unsat_px φ hwf (runPinExtends_of_allParentsOwn φ hwf hap) hns

/-- **La máquina decide**, bajo la intuición. -/
theorem verdict_iff_allParentsOwn (hwf : WF φ) (hap : RunAllParentsOwn φ) :
    (∃ kv ∈ pureRunW φ, isValid (filterAllAgg kv.2 []) = true) ↔ Satisfiable φ :=
  verdict_iff_pinExtends φ hwf (runPinExtends_of_allParentsOwn φ hwf hap)

/-- Lo mismo por la vía de Helly. -/
theorem answer_ne_unknown_pm (hwf : WF φ) (htp : RunTwoParents φ) (hpm : RunPairMeet φ) :
    answer φ ≠ .unknown :=
  answer_ne_unknown_px φ hwf (runPinExtends_of_pairMeet φ hwf htp hpm)

theorem answer_unsat_pm (hwf : WF φ) (htp : RunTwoParents φ) (hpm : RunPairMeet φ)
    (hns : ¬ Satisfiable φ) : answer φ = .unsat :=
  answer_unsat_px φ hwf (runPinExtends_of_pairMeet φ hwf htp hpm) hns

/-- info: 'AbsSat.GraphPath.Model.ReaderDescent.twoParents_of_pruned' does not depend on any axioms -/
#guard_msgs in
#print axioms twoParents_of_pruned

/-- info: 'AbsSat.GraphPath.Model.ReaderDescent.chain_of_commonOwner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_of_commonOwner

/-- info: 'AbsSat.GraphPath.Model.ReaderDescent.pinExtends_of_commonOwner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinExtends_of_commonOwner

/-- info: 'AbsSat.GraphPath.Model.ReaderDescent.answer_ne_unknown_apo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown_apo

/-- info: 'AbsSat.GraphPath.Model.ReaderDescent.answer_unsat_apo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_unsat_apo

/-- info: 'AbsSat.GraphPath.Model.ReaderDescent.answer_ne_unknown_pm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown_pm

end AbsSat.GraphPath.Model.ReaderDescent
