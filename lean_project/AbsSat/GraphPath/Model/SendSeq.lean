-- lean_project/AbsSat/GraphPath/Model/SendSeq.lean
import AbsSat.GraphPath.Model.StepFilter

/-!
# El envío como sucesión de filtros de un paso

Un envío filtra de una vez el filtro débil (varios pasos, cada uno con su lista de ids admitidos) y
los requisitos duros (varios pasos, un id cada uno), y revisa al final. Hecho **uno a uno**, con su
review en medio, es `StepFilter.seqSend`, y ahí cada paso conserva `FullExt1` desde sus parejas.

Dos hipótesis con nombre:

* `SendConfluent`: el resultado de una vez no es menor que el de uno a uno (medido con
  `row-degree seqsend`: iguales como conjuntos);
* `SendPairs`: las parejas de cada paso filtrado, en los estados intermedios.
-/

namespace AbsSat.GraphPath.Model.SendSeq

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
open AbsSat.GraphPath.Model.FullExt1
open AbsSat.GraphPath.Model.StepFilter

variable (φ : Cnf)

/-- Los filtros de un paso de un envío: los débiles y, después, cada requisito duro. -/
def sendSteps (d : NodeId) : List (Int × List NodeId) :=
  weakReqOfCnf φ d ++ (reqOfCnf φ d).map (fun r => (r.step, [r]))

/-- **El envío de una vez no es menor que uno a uno**: lo que queda uno a uno es válido, crece hasta
el de una vez, y la tabla global de una vez está en la de uno a uno. -/
def SendConfluent : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index,
      isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true →
      isValid (seqSend (reviewAgg kv.2) (sendSteps φ d)) = true ∧
      Grown (seqSend (reviewAgg kv.2) (sendSteps φ d))
        (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) ∧
      ∀ q ∈ (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)).gowners,
        q ∈ (seqSend (reviewAgg kv.2) (sendSteps φ d)).gowners

/-- **Las parejas de cada paso filtrado**, en los estados intermedios del envío uno a uno. -/
def SendPairs : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), 0 ≤ k → StateOkF φ k kv → MInv φ kv.2 → FullExt1 kv.2 →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index,
      isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true →
      StepsPairs (reviewAgg kv.2) (sendSteps φ d)

/-- **`SendExt1`, desde el envío uno a uno.** -/
theorem sendExt1_of (hC : SendConfluent φ) (hP : SendPairs φ) : Ladder1.SendExt1 φ := by
  intro k kv hk0 hkv hm hF hso d hd hval
  obtain ⟨hvS, hG, hsub⟩ := hC k kv hkv hm d hd hval
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
  have hS := fullExt1_seqSend _ _ c0 hF0 (hP k kv hk0 hkv hm hF d hd hval) hvS
  intro q hq h0 h1
  rw [hG.step_eq] at h1
  obtain ⟨s, hs, hsq⟩ := hS q (hsub q hq) h0 h1
  exact ⟨s, fullChain_of_grown hG s hs, hsq⟩

/-- info: 'AbsSat.GraphPath.Model.SendSeq.sendExt1_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sendExt1_of

/-- **El lector sin retroceso decide 3-SAT** desde tres hipótesis: el envío de una vez no es menor
que uno a uno (`SendConfluent`), y las parejas de cada paso que se filtra tienen cadena común, en
los envíos (`SendPairs`) y en los pines del lector (`PinPairs`). -/
theorem readerVerdictW_iff_of_steps (hC : ∀ ψ : Cnf, WF ψ → SendConfluent ψ)
    (hSP : ∀ ψ : Cnf, WF ψ → SendPairs ψ) (hP : PinPairs.PinPairs) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  PinPairs.readerVerdictW_iff_of_pairs (fun ψ hψ => sendExt1_of ψ (hC ψ hψ) (hSP ψ hψ)) hP φ hwf

/-- info: 'AbsSat.GraphPath.Model.SendSeq.readerVerdictW_iff_of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_steps

end AbsSat.GraphPath.Model.SendSeq
