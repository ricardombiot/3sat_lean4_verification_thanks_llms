-- lean_project/AbsSat/GraphPath/Model/ExactSeq.lean
import AbsSat.GraphPath.Model.TablesExact

/-!
# El envío paso a paso con las tablas exactas

Con `TablesExact` viajando por la sucesión de filtros de un paso, las parejas de cada paso ya no son
hipótesis: salen de la exactitud del estado intermedio (`frontierPairs_of_tablesExact`). Lo que queda
por paso son las **ternas que sobreviven** (`StepTriples`).

Y el envío de una vez es el de uno a uno (`SendConfluent2`, medido: 6.082 de 6.082 envíos iguales en
la semilla 1).
-/

namespace AbsSat.GraphPath.Model.ExactSeq

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.FullExt (FullChainG)
open AbsSat.GraphPath.Model.FullExt1
open AbsSat.GraphPath.Model.StepFilter
open AbsSat.GraphPath.Model.TablesExact
open AbsSat.GraphPath.Model.SendSeq (sendSteps)

/-- **Las ternas a lo largo de la sucesión.** -/
def StepsTriples : GPathM → List (Int × List NodeId) → Prop
  | _, [] => True
  | T, e :: es => 0 ≤ e.1 ∧ e.1 < T.current_step ∧ StepTriples T e ∧ StepsTriples (seqStep T e) es

/-- **La sucesión conserva `FullExt1` y `TablesExact`**, desde las ternas de cada paso. -/
theorem exact_seqSend : ∀ (es : List (Int × List NodeId)) (T : GPathM), SCtx T → FullExt1 T →
    TablesExact T → StepsTriples T es → isValid (seqSend T es) = true →
    FullExt1 (seqSend T es) ∧ TablesExact (seqSend T es)
  | [], _, _, hF, hE, _, _ => ⟨hF, hE⟩
  | e :: es, T, c, hF, hE, ⟨he0, he1, hT, hrest⟩, hv => by
    have hv1 : isValid (seqStep T e) = true :=
      Certifies.isValid_of_pruned (pruned_seqSend es (seqStep T e)) hv
    exact exact_seqSend es (seqStep T e) (sctx_seqStep T e c hv1)
      (fullExt1_stepFilter T e c.rc c.smp c.self c.pos hF he0 he1
        (frontierPairs_of_tablesExact T hE e.1) hv1)
      (tablesExact_stepFilter T e c hE he0 he1 hT hv1) hrest hv

/-- info: 'AbsSat.GraphPath.Model.ExactSeq.exact_seqSend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exact_seqSend

/-- Dos estados que crecen el uno hasta el otro tienen las mismas tablas exactas. -/
theorem tablesExact_of_grown {S F : GPathM} (hSF : Grown S F) (hFS : Grown F S)
    (h : TablesExact S) : TablesExact F := by
  rintro r hr q' hq' hne h0 h1 ⟨nr, hnr, hown⟩
  obtain ⟨nr', hnr', ho, _⟩ := hFS.node?_grown r nr hnr
  obtain ⟨s, hs, hsr, hsq⟩ := h r (hFS.gowners_grown r hr) q' (hFS.gowners_grown q' hq') hne h0
    (by rw [hFS.step_eq]; exact h1) ⟨nr', hnr', ho q' hown⟩
  exact ⟨s, fullChain_of_grown hSF s hs, hsr, hsq⟩

variable (φ : Cnf)

/-- **El envío de una vez es el de uno a uno**: cada uno crece hasta el otro. -/
def SendConfluent2 : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index,
      isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true →
      isValid (seqSend (reviewAgg kv.2) (sendSteps φ d)) = true ∧
      Grown (seqSend (reviewAgg kv.2) (sendSteps φ d))
        (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) ∧
      Grown (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d))
        (seqSend (reviewAgg kv.2) (sendSteps φ d))

/-- **Las ternas que sobreviven en cada paso del envío.** -/
def SendTriples : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), 0 ≤ k → StateOkF φ k kv → MInv φ kv.2 →
    FullExt1 kv.2 → TablesExact kv.2 →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index,
      isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true →
      StepsTriples (reviewAgg kv.2) (sendSteps φ d)

/-- **El revisado de un envío es extendible y exacto**, si el que envía lo era. -/
theorem sendExact (hC : SendConfluent2 φ) (hT : SendTriples φ) (k : Int) (kv : NodeId × GPathM)
    (hk0 : 0 ≤ k) (hkv : StateOkF φ k kv) (hm : MInv φ kv.2) (hF : FullExt1 kv.2)
    (hE : TablesExact kv.2) (hso : Ownership.SelfOwned kv.2) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    FullExt1 (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) ∧
      TablesExact (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) := by
  obtain ⟨hvS, hSF, hFS⟩ := hC k kv hkv hm d hd hval
  have hpos : 0 < kv.2.current_step := by rw [hkv.step]; omega
  have hT0v : isValid (reviewAgg kv.2) = true :=
    Certifies.isValid_of_pruned (pruned_seqSend _ _) hvS
  have hRd : ReadableAgg (reviewAgg kv.2) := ⟨kv.2, [], hm.rctx, rfl⟩
  have c0 : SCtx (reviewAgg kv.2) :=
    ⟨RCtx_of_readableAgg _ hRd,
      AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot [],
      ReaderLadder.selfOwned_of_readable _ hRd hT0v,
      by rw [(pruned_reviewAgg kv.2).step_eq]; exact hpos⟩
  have hF0 : FullExt1 (reviewAgg kv.2) :=
    fullExt1_reviewAgg kv.2 (Ladder1.reviewComplete1_of_fullExt1 kv.2 hso hm.smp hm.rctx.rootz
      hm.rctx.shape.notroot hpos hF)
  have hE0 : TablesExact (reviewAgg kv.2) :=
    tablesExact_reviewAgg kv.2 hm.rctx.nodup hso hm.smp hm.rctx.rootz hm.rctx.shape.notroot hpos hE
  obtain ⟨hFS', hES⟩ := exact_seqSend _ _ c0 hF0 hE0 (hT k kv hk0 hkv hm hF hE d hd hval) hvS
  refine ⟨fun q hq h0 h1 => ?_, tablesExact_of_grown hSF hFS hES⟩
  rw [hSF.step_eq] at h1
  obtain ⟨s, hs, hsq⟩ := hFS' q (hFS.gowners_grown q hq) h0 h1
  exact ⟨s, fullChain_of_grown hSF s hs, hsq⟩

/-- info: 'AbsSat.GraphPath.Model.ExactSeq.sendExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sendExact

end AbsSat.GraphPath.Model.ExactSeq
