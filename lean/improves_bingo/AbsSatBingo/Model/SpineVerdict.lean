-- lean/improves_bingo/AbsSatBingo/Model/SpineVerdict.lean
import AbsSatBingo.Model.SpineZombie
import AbsSatBingo.Model.ConeAnc

/-!
# El veredicto del lector por la espina

Los estados que visita el lector son revisados, luego cerrados (`cInv_visited`). En un estado cerrado la espina baja
sin retroceso hasta una camarilla (`noZombie_of_spine`), bajo `TwoParents` y `SpineTrio`. Con eso,
**`readerVerdict_iff_of_spine`**: el veredicto del lector es la satisfacibilidad bajo esas dos propiedades de sus
estados visitados, **sin ninguna hipótesis sobre los joins ni sobre las llegadas**.

**Aviso (medido después, `probe_spinehyps.jl`): `SpineTrio` es FALSA en `clause_mix`.** La espina sin revisión, con
elecciones al azar entre dos padres, se atasca en 2 de 544 cadenas (en el estado final y en uno fijado), aunque otra
elección sí llega. Este teorema es correcto pero su hipótesis no vale en general: **hay que revisar tras cada
elección** (el lector por caminos con revisión no se atasca: 0 en todas las lecturas medidas). Queda como referencia;
las piezas reutilizables son `carried_of_spine`, `forced_parent` y `two_helly`.

* **`line_linksInv`**: `LinksInv` en todas las entradas de la línea, sin hipótesis.
* **`visited_pres`**: una propiedad que conservan las primitivas de la revisión vale en todos los estados visitados.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace SecLine

open GPathB Driver Machine CliqueSplit Final

variable {φ : Cnf}

/-- **`LinksInv` en todas las entradas de la línea.** -/
theorem line_linksInv (hbd : Bounded φ) : ∀ n, ∀ kv ∈ steps φ n (init φ), LinksInv kv.2 := by
  intro n
  induction n with
  | zero =>
    intro kv hkv
    have hkv' : kv ∈ init φ := by simpa [steps] using hkv
    rw [init_eq, List.mem_singleton] at hkv'
    subst hkv'
    exact sInvC_initSeed.1.1.1.2.2.2.2.2.2.2
  | succ n ih =>
    intro kv hkv
    obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd n
    have key : ∀ {d : NodeId} {e : GPathB}, ArrTree φ n d e → LinksInv e ∧ EdgesAlive e := by
      intro d e ht
      induction ht with
      | leaf kv hkv hd hv =>
        have ho := hl kv hkv
        have hs := shrinks_filterAll kv.2 (reqOf φ d)
        have hcf : (kv.2.filterAll (reqOf φ d)).current_step = (n : Int) + 1 := hs.1.step.trans ho.step
        have hds : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
          rw [hcf, sonsOfMap_step φ kv.1 d hd, ho.key]; omega
        have hli := revPrims_filterAll revPrims_linksInv _ (reqOf φ d) (ih kv hkv)
        have hz := revPrims_filterAll revPrims_aboveZero _ (reqOf φ d) (hent kv hkv).1.2.2.2
        refine ⟨?_, edgesAlive_arr hbd hkv hv⟩
        rw [arr_eq hv]; show LinksInv (GPathB.filterAll _ [])
        exact revPrims_filterAll revPrims_linksInv _ _
          (linksInv_addNode hli (below_of_shrinks hs ho.below) hz hds)
      | node _ _ ih₁ ih₂ =>
        unfold doJoin
        split
        · exact ⟨linksInv_join ih₁.1 ih₂.1 ih₁.2 ih₂.2, edgesAlive_join ih₁.2 ih₂.2⟩
        · exact ih₁
    exact (key (steps_tree n kv hkv)).1

/-- Lo que conservan las primitivas de la revisión vale en todos los estados que visita el lector. -/
theorem visited_pres {P : GPathB → Prop} (hp : RevPrims P) {g₀ : GPathB} (h₀ : P g₀) :
    ∀ h, Visited g₀ h → P h := by
  intro h hv
  induction hv with
  | start => exact revPrims_review hp _ (hp.dirty _ _ h₀)
  | pin _ _ ih => exact revPrims_filterAll hp _ _ ih

/-- **Las hipótesis de la espina**: en los estados válidos que visita el lector, como mucho dos padres vivos por
nodo y `SpineTrio`. -/
def HypsSpine (φ : Cnf) : Prop :=
  ∀ kv ∈ run φ, ∀ h, Visited kv.2 h → h.isValid = true → TwoParents h ∧ SpineTrio h

/-- **El veredicto del lector es la satisfacibilidad bajo `TwoParents` y `SpineTrio`** en sus estados visitados. -/
theorem readerVerdict_iff_of_spine (hbd : Bounded φ) (H : HypsSpine φ) : readerVerdict φ = true ↔ Satisfiable φ := by
  apply Decode.readerVerdict_iff_of_noZombie hbd
  intro kv hkv h hvis hval
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [hrun] at hkv
  obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd (stepCount φ - 1).toNat
  have hok := hl kv hkv
  have hcs : 2 ≤ kv.2.current_step := by
    have hsc : 2 ≤ stepCount φ := by unfold stepCount; omega
    rw [hok.step]; omega
  have hci := cInv_visited hok.docs (hent kv hkv).1.1 hok.below (hent kv hkv).1.2.2.2 hcs h hvis
  obtain ⟨hdocs, _, hb, hz, hcs', hcl⟩ := hci
  have hls := visited_pres revPrims_linksStep (hent kv hkv).1.2.2.1 h hvis
  have hli := visited_pres revPrims_linksInv (line_linksInv hbd _ kv hkv) h hvis
  obtain ⟨htwo, htrio⟩ := H kv (by rw [hrun]; exact hkv) h hvis hval
  exact noZombie_of_spine (hcl hval) hdocs hb hz hls hli (by omega) htwo htrio hval

end SecLine

end AbsSatBingo.Model
