-- lean_project/AbsSat/GraphPath/Model/RoundExact.lean
import AbsSat.GraphPath.Model.PinDoomed

/-!
# El lector con una sola hipótesis por pin: `RoundExact`

`row-degree roundexact` (semillas 1 y 7, 86 pines del lector, review simétrico): la limpieza de un pin
deja tramos sin cadena completa —exactamente los condenados: 74 y 12—, y **a la salida de la primera
vuelta no queda ninguno** (0 de 18.000 tramos). Así que la primera vuelta restaura `SegExact`.

Y basta con eso: `SegExact` a la salida de la primera vuelta llega al punto fijo del pin, haya las
vueltas que haya y actúe o no el barrido agresivo. Toda cadena completa de la primera vuelta es cadena
completa del estado pinchado (al subir por una poda solo se gana), allí es sana, y la review agresiva
conserva las cadenas sanas (`ChainSound_reviewAgg`); un tramo del resultado ya era tramo tras la
primera vuelta, porque el resultado es una poda de ella.

La escalera queda con `hStart` y una sola hipótesis por pin, `RoundExact`: **la primera vuelta del pin
deja todo tramo en una cadena completa.** Sustituye a las tres de `PinDoomed` (`PinFirstRound`,
`LaterValid`, `AggInactive`).
-/

namespace AbsSat.GraphPath.Model.RoundExact

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak)
open AbsSat.GraphPath.Model.SegExact (SegExact seg_before)
open AbsSat.GraphPath.Model.FullExt (FullChainG chainSound_of_fullChain fullChain_of_chainSound)

/-- **La hipótesis por pin**: la primera vuelta del review deja todo tramo en una cadena completa. -/
def RoundExact (X : GPathM) : Prop := isValid (reviewPass X) = true → SegExact (reviewPass X)

/-- **El resultado de la review agresiva es una poda de la primera vuelta**, si el estado es válido. -/
theorem pruned_reviewPass_reviewAgg (X : GPathM) (hv : isValid X = true) :
    Pruned (reviewPass X) (reviewAgg X) := by
  have hrev : Pruned (reviewPass X) (review X) := by
    show Pruned (reviewPass X) (reviewFuel (measure X + 1) X)
    simp only [reviewFuel, hv, if_true]
    split
    · exact pruned_reviewFuel _ _
    · exact Pruned.refl _
  refine Pruned.trans hrev ?_
  show Pruned (review X) (reviewAggFuel (measure X + 1) X)
  simp only [reviewAggFuel]
  split
  · split
    · exact Pruned.trans (pruned_aggSweep _) (pruned_reviewAggFuel _ _)
    · exact Pruned.refl _
  · exact Pruned.refl _

/-- **Una cadena completa de un estado podado lo es del de antes**: al subir, nodos, tablas, padres y
global solo ganan. -/
theorem fullChain_before (g g' : GPathM) (hpr : Pruned g g') (hnd : NodupIds g) (s : Int → PathNodeId)
    (h : FullChainG g' s) : FullChainG g s := by
  obtain ⟨⟨hpc, hpo⟩, hg⟩ := h
  have hcs := hpr.step_eq
  rw [hcs] at hpc hpo hg
  obtain ⟨hpc0, hpo0⟩ := seg_before g g' hpr hnd s 0 (g.current_step - 1) hpc hpo
  exact ⟨⟨hpc0, hpo0⟩, fun j h0 h1 => hpr.gowners_sub _ (hg j h0 h1)⟩

/-- **`SegExact` tras la primera vuelta llega al punto fijo del review agresivo.** -/
theorem segExact_reviewAgg_of_round (X : GPathM) (hnd : NodupIds X)
    (hself : ∀ pid n, X.node? pid = some n → pid ∈ n.owners)
    (hsmp : Sons.SMP X) (hroot : Sons.RootAtZero X) (hnr : Parents.NotRoot X)
    (hpos : 0 < X.current_step) (hv : isValid X = true) (hR : SegExact (reviewPass X)) :
    SegExact (reviewAgg X) := by
  have hpr1 := pruned_reviewPass X
  have hpr2 := pruned_reviewPass_reviewAgg X hv
  have hnd1 : NodupIds (reviewPass X) := PinAliveChain.NodupIds_reviewPass X hnd
  intro sel lo hi hlo hlh hhi hpc hpo
  obtain ⟨hpc1, hpo1⟩ := seg_before _ _ hpr2 hnd1 sel lo hi hpc hpo
  obtain ⟨s, hs, hsel⟩ := hR sel lo hi hlo hlh (by rw [← hpr2.step_eq]; exact hhi) hpc1 hpo1
  have hsX := fullChain_before X _ hpr1 hnd s hs
  exact ⟨s, fullChain_of_chainSound _ s (ChainSound_reviewAgg X s
    (chainSound_of_fullChain X hself hsmp hroot hnr hpos s hsX)), hsel⟩

/-- info: 'AbsSat.GraphPath.Model.RoundExact.segExact_reviewAgg_of_round' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segExact_reviewAgg_of_round

/-- **El lector sin retroceso decide 3-SAT**, con `SegExact` en la línea final revisada (`hStart`) y,
en cada pin del lector, **una sola hipótesis**: la primera vuelta del review del estado pinchado deja
todo tramo en una cadena completa (`RoundExact`; medido: 0 fallos en 86 pines). -/
theorem readerVerdictW_iff_of_roundExact
    (hStart : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact (filterAllAgg kv.2 []))
    (hPin : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      RoundExact (filterWeak g (q.id.step, [q.id])))
    (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine SegExact.readerVerdictW_iff_of_readerSegExact ?_ φ hwf
  intro φ' hwf' kv hkv g hR hv
  obtain ⟨hm, hcs, _⟩ := ReaderAggRun.pureRunW_state φ' hwf' kv hkv
  have hpos : 0 < kv.2.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ'
  have ctx₀ : PinAliveChain.DCtx (filterAllAgg kv.2 []) :=
    { rd := ⟨kv.2, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms
      sn := AggInvariants.SN_filterAllAgg kv.2 [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot []
      pos := by rw [(pruned_filterAllAgg kv.2 []).step_eq]; exact hpos }
  revert hv
  induction hR with
  | start => exact hStart φ' hwf' kv hkv
  | pin g k q hR hv hk hq _ =>
    intro hv'
    have ctx := TopGoodLadder.dctx_of_readFromR _ ctx₀ g hR
    have rc := ReaderAgg.RCtx_of_readableAgg g ctx.rd
    have cG := Reader.Ctx_of_readable g (ReaderAgg.readable_of_readableAgg g ctx.rd) hv
    have hRE := hPin φ' hwf' kv hkv g k q hR hv hk hq
    rw [SegExactFilter.filterAllAgg_pin] at hv' ⊢
    let X := filterWeak g (q.id.step, [q.id])
    have hprX := pruned_reviewAgg X
    have hvX : isValid X = true := Certifies.isValid_of_pruned hprX hv'
    have hv1 : isValid (reviewPass X) = true :=
      Certifies.isValid_of_pruned (pruned_reviewPass_reviewAgg X hvX) hv'
    exact segExact_reviewAgg_of_round X rc.nodup (fun pid n h => cG.self pid n h) ctx.smp rc.rootz
      rc.shape.notroot ctx.pos hvX (hRE hv1)

/-- info: 'AbsSat.GraphPath.Model.RoundExact.readerVerdictW_iff_of_roundExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_roundExact

end AbsSat.GraphPath.Model.RoundExact
