-- lean/improves_bingo/AbsSatBingo/Model/LineStep.lean
import AbsSatBingo.Model.FamKernel

/-!
# El paso de la inducción por la línea, en familia

Una línea es una familia de pares (clave, estado) `L`. `LTUf L c`: una cima del núcleo de la unión de la línea
fijado en `Q` está en el núcleo de un estado de la línea con su clave, fijado igual. `PinFreeF`: fijar por los
requisitos de la fila de una cima no la mata en la unión de la línea.

**`ltuf_step`**: `LTUf` de una línea da `LTUf` de la siguiente, con `PinFreeF` en la siguiente y dos hechos de cómo se
construye la siguiente: sus entradas están cubiertas por las llegadas (`Covers`) y cada llegada válida está dentro de
la entrada de su destino (`LineUpF`). La bajada es `famStruct_rows_down` y la subida es (A).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (shiftPid)

namespace GPathB

open Machine (Below below_of_shrinks mapId_of_mem_shiftRowIds)

/-- La familia de estados de una línea. -/
def famOf (L : NodeId × GPathB → Prop) : GPathB → Prop := fun g => ∃ kv, L kv ∧ kv.2 = g

section step
variable (rq : NodeId → List NodeId) (title : String) (forb : PathNodeId → Bool)

/-- **`LTUf`**: la partición de la unión de una línea por sus estados. -/
def LTUf (L : NodeId × GPathB → Prop) (c : Int) : Prop :=
  ∀ (Q : List NodeId) (p : PathNodeId), p.id.step = c - 1 → FamKernel (famOf L) c Q p p →
    ∃ kv, L kv ∧ kv.1 = p.id ∧ Kernel kv.2 Q p p

/-- **`PinFreeF`**: fijar por los requisitos de la fila de una cima no la mata en la unión de la línea. -/
def PinFreeF (L : NodeId × GPathB → Prop) (c : Int) : Prop :=
  ∀ (Q : List NodeId) (t : PathNodeId), t.id.step = c - 1 → FamKernel (famOf L) c Q t t →
    FamKernel (famOf L) c (rq t.id ++ Q) t t

/-- La llegada de `kv` a `d`: filtrar, la fila nueva y el review. -/
def arrival (kv : NodeId × GPathB) (d : NodeId) : GPathB := ((kv.2.filterAll (rq d)).addNode d title forb).review

/-- La familia de las llegadas válidas de la línea `L` (con hijos `Son`). -/
def Arrivals (L : NodeId × GPathB → Prop) (Son : NodeId → NodeId → Prop) : GPathB → Prop :=
  fun a => ∃ kv d, L kv ∧ Son kv.1 d ∧ (kv.2.filterAll (rq d)).isValid = true ∧ a = arrival rq title forb kv d

/-- Cada llegada válida está dentro de la entrada de su destino en la línea siguiente. -/
def LineUpF (L L' : NodeId × GPathB → Prop) (Son : NodeId → NodeId → Prop) : Prop :=
  ∀ kv d, L kv → Son kv.1 d → (kv.2.filterAll (rq d)).isValid = true → ∀ (Q : List NodeId) (t : PathNodeId),
    Kernel (arrival rq title forb kv d) Q t t → ∃ kv', L' kv' ∧ kv'.1 = d ∧ Kernel kv'.2 Q t t

/-- Los datos de un remitente. -/
structure SenderOk (T : Int) (kv : NodeId × GPathB) : Prop where
  docs : AliveDocs kv.2
  nd   : NodupIds kv.2
  below : Below kv.2
  links : LinksStep kv.2
  top  : TopExact kv.2
  step : kv.2.current_step = T
  tid  : TopDocsId kv.2 kv.1

/-- **El paso**: `LTUf` de la línea `L` (paso `T`) da `LTUf` de la siguiente `L'` (paso `T + 1`), con `PinFreeF` en
`L'`, las entradas de `L'` cubiertas por las llegadas y cada llegada dentro de la entrada de su destino. -/
theorem ltuf_step {T : Int} (hT : 1 ≤ T) {L L' : NodeId × GPathB → Prop} {Son : NodeId → NodeId → Prop}
    (hsnd : ∀ kv, L kv → SenderOk T kv) (hson : ∀ k d, Son k d → d.step = T)
    (hcov : Covers (famOf L') (Arrivals rq title forb L Son)) (hup : LineUpF rq title forb L L' Son)
    (hpf : PinFreeF rq L' (T + 1)) (hih : LTUf L T) : LTUf L' (T + 1) := by
  intro Q t hts hk
  obtain ⟨V0, R0, hst0, ha0, hr0⟩ := hk
  have hk1 := hpf Q t hts ⟨V0, R0, hst0, ha0, hr0⟩
  -- las llegadas están cubiertas por las filas nuevas de las copias
  let G : GPathB → NodeId → Prop := fun f d => ∃ kv, L kv ∧ Son kv.1 d ∧ f.isValid = true ∧ f = kv.2.filterAll (rq d)
  have hGok : ∀ f d, G f d → AliveDocs f ∧ Below f ∧ LinksStep f ∧ f.current_step = T ∧ d.step = T := by
    rintro f d ⟨kv, hL, hS, _, rfl⟩
    have hok := hsnd kv hL
    exact ⟨aliveDocs_filterAll hok.docs _, below_of_shrinks (shrinks_filterAll _ _) hok.below,
      revPrims_filterAll revPrims_linksStep _ _ hok.links, (shrinks_filterAll _ _).1.step.trans hok.step, hson _ _ hS⟩
  have hcovA : Covers (Arrivals rq title forb L Son) (RowsOf G title forb) := by
    rintro a ⟨kv, d, hL, hS, hv, rfl⟩
    have hok := hsnd kv hL
    have hfs : (kv.2.filterAll (rq d)).current_step = T := (shrinks_filterAll _ _).1.step.trans hok.step
    have hnd : NodupIds ((kv.2.filterAll (rq d)).addNode d title forb) :=
      nodupIds_addNode (revPrims_filterAll revPrims_nodupIds _ _ hok.nd)
        (below_of_shrinks (shrinks_filterAll _ _) hok.below) (by rw [hfs]; exact hson _ _ hS)
    exact covers_trans (covers_sub (shrinks_review _).1 hnd)
      (covers_of_sub (fun g hg => ⟨_, d, ⟨kv, hL, hS, hv, rfl⟩, hg⟩)) _ rfl
  obtain ⟨V, R, hst, ha, hr⟩ := famKernel_covers (covers_trans hcov hcovA) hk1
  -- t es de una fila nueva: su padre p, por la regla de nodos
  obtain ⟨a, ⟨f, d, hG, rfl⟩, hta⟩ := hst.alive (hst.dom hr).1
  obtain ⟨hfd, hfb, _, hfs, hds⟩ := hGok f d hG
  have htn : t ∈ f.newRowIds d forb := by
    rcases alive_addNode_cases (title := title) hfd hfb (hds.trans hfs.symm) hta with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  obtain ⟨q, _, hq⟩ := parent_of_row (by omega) htn
  have hroot : t.parent_id.isNone = false := by rw [hq]; rfl
  obtain ⟨p, ⟨a1, n1, ⟨f1, d1, hG1, rfl⟩, hn1, hpn1⟩, htp⟩ := (hst.node (hst.dom hr).1).1 hroot
  obtain ⟨hfd1, hfb1, _, hfs1, hds1⟩ := hGok f1 d1 hG1
  obtain ⟨htn1, rfl⟩ := node?_addNode_top (title := title) (forb := forb) hfb1 hn1 (by omega)
  have hp1 : p ∈ f1.rowParents d1 t := hpn1
  have htd1 : t.id = d1 := mapId_of_mem_shiftRowIds (List.mem_filter.mp htn1).1
  obtain ⟨n0, hn0, hn0p, hps⟩ := step_of_newParents (rowParents_sub hp1)
  -- la bajada: el padre en la unión de la línea anterior, fijado con los requisitos de la fila
  have hdown := famStruct_rows_down (title := title) (forb := forb) (c := T) hGok (by rw [show T + 1 = T + 1 from rfl]; exact hst)
  have hcovL : Covers (fun f => ∃ d, G f d) (famOf L) := by
    rintro g ⟨d', kv, hL, _, _, rfl⟩
    exact covers_trans (covers_sub (shrinks_filterAll _ _).1 (hsnd kv hL).nd)
      (covers_of_sub (fun g' hg' => ⟨kv, hL, hg'.symm⟩)) _ rfl
  have hkp : FamKernel (famOf L) T (rq t.id ++ Q) p p := by
    refine famKernel_covers hcovL ⟨_, _, hdown, fun b hb y hy hys => ha b hb hy.1 hys, ?_⟩
    exact ⟨hst.refl (hst.dom htp).2, by omega, by omega⟩
  obtain ⟨kv', hL', hkey, hk'⟩ := hih (rq t.id ++ Q) p (by omega) hkp
  obtain ⟨kv1, hL1, hS1, _, rfl⟩ := hG1
  have hok1 := hsnd kv1 hL1
  have hpid : p.id = kv1.1 := by
    rw [← hn0p]
    exact topDocsId_filterAll hok1.tid _ n0 hn0 (by rw [hn0p]; exact hps)
  have hok' := hsnd kv' hL'
  have hSon' : Son kv'.1 t.id := by rw [hkey, hpid, htd1]; exact hS1
  -- la copia del remitente con los requisitos de la fila
  have hkc : Kernel (kv'.2.filterAll (rq t.id)) Q p p := (kernel_pin_list_iff hok'.docs hok'.nd p p).mpr hk'
  have hcs' : (kv'.2.filterAll (rq t.id)).current_step = T := (shrinks_filterAll _ _).1.step.trans hok'.step
  have hpnew : p ∈ (kv'.2.filterAll (rq t.id)).newParents := by
    obtain ⟨V2, R2, hst2, _, hr2⟩ := hkc
    obtain ⟨m, hm, rfl⟩ := aliveDocs_filterAll hok'.docs _ p (hst2.alive (hst2.dom hr2).1)
    exact mem_newParents (by omega) hm (by rw [hcs']; omega)
  have hsh : shiftPid p t.id = t := by
    have := (List.mem_filter.mp hp1).2
    rw [htd1]; exact beq_iff_eq.mp this
  obtain ⟨htn', hp'⟩ := row_of_parent (by omega) hpnew hsh (forb_of_newRow htn1)
  have hP : ∀ r ∈ Q, r.step = (kv'.2.filterAll (rq t.id)).current_step → r = t.id := by
    intro r hr' hrs
    exact (ha0 r hr' (hst0.dom hr0).1 (by rw [hrs, hcs']; omega)).symm
  have hA := kernel_up_of_parent (title := title) (topExact_filterAll hok'.top hok'.docs hok'.nd _)
    (below_of_shrinks (shrinks_filterAll _ _) hok'.below) (by omega) (by rw [hcs']; omega) hp' htn' hP hkc
  have hv : (kv'.2.filterAll (rq t.id)).isValid = true := by
    obtain ⟨V2, R2, hst2, _, hr2⟩ := hkc
    exact isValid_of_sec hst2 (hst2.dom hr2).1
  exact hup kv' t.id hL' hSon' hv Q t hA

end step

end GPathB

end AbsSatBingo.Model
