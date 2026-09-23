-- lean_project/AbsSat/GraphPath/Model/TopGoodLadder.lean
import AbsSat.GraphPath.Model.Ladder2
import AbsSat.GraphPath.Model.PinExactBoundary

/-!
# La escalera con una sola hipótesis: la compatibilidad colectiva en los estados del lector

El descenso por padres está demostrado: desde `TopGood` —toda cadena desde la cima tiene, por
debajo, una entrada común a todos sus nodos y al anfitrión— sale el paso con cualquier opción
(`TopGoodUp.anyOptionStep_of_topGood`), de ahí la cadena por cada entrada
(`OwnerChainedBuild.ownerChained_of_anyOption`) y el veredicto. El `up` la crea por construcción
(`TopGoodUp.topGood_addNode`).

Queda una frase, sin disfrazar: **en todo estado válido que el lector visita vale `TopGood`**.
Medida (`row-degree topgoodops`): 0 fallos en 2.523.099 cadenas, semilla 1, en todas las clases de
estado. Y lo que sabemos de por qué: si el filtro deja una cadena sin entrada común admitida, un nodo
suyo se queda sin ninguna admitida y el review base lo elimina (`toptrace`: 62.961 de 62.961).
-/

namespace AbsSat.GraphPath.Model.TopGoodLadder

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg

/-- **Los hijos están un paso por encima**: cada hijo es un nodo que lo tiene como padre, y los
padres están un paso por debajo. -/
theorem sAbove_of (g : GPathM) (hsn : Sons.SN g) (hpms : Sons.PMS g) (hpb : Parents.PBelow g) :
    Sons.SAbove g := by
  intro n hn s hs
  obtain ⟨m, hm, hmid⟩ := hsn n hn s hs
  have := hpb m hm n.id (hpms n hn s hs m hm hmid)
  rw [hmid] at this
  omega

/-- **El contexto del descenso, en un estado válido del lector.** -/
theorem tctx_of_reader (g : GPathM) (ctx : PinAliveChain.DCtx g) (hv : isValid g = true) :
    Threaded.TCtx g :=
  have adj := AdjacentOwners.adj_of_readable g ctx.rd hv ctx.pms ctx.sn
  have rc := RCtx_of_readableAgg g ctx.rd
  { nodeval := adj.ctx.nodeval
    shape := adj.ctx.shape
    links := adj.links
    cpar := adj.cohP
    cson := adj.cohS
    sabove := sAbove_of g ctx.sn ctx.pms adj.ctx.shape.pbelow
    sn := ctx.sn
    pms := ctx.pms
    ownerNode := fun pid n hn q hq h0 h1 =>
      (GownersNodes.hasNode_iff g q).mp (rc.gn q (adj.ctx.ownGow pid n hn q hq h0 h1)) }

/-- **De `TopGood` a la cadena por cada entrada**, en un estado válido del lector. -/
theorem ownerChained_of_topGood (g : GPathM) (ctx : PinAliveChain.DCtx g) (hv : isValid g = true)
    (hT : TopGoodUp.TopGood g) : ReaderChain.OwnerChained g := by
  have adj := AdjacentOwners.adj_of_readable g ctx.rd hv ctx.pms ctx.sn
  have rc := RCtx_of_readableAgg g ctx.rd
  have tctx := tctx_of_reader g ctx hv
  have hok : AggFixpoint.AggOk g := by
    obtain ⟨g₀, reqs, _, hg⟩ := ctx.rd
    rw [hg] at hv ⊢
    exact AggFixpoint.aggOk_reviewAgg _ hv
  have hsym := PinExactBoundary.ownSymmetric_of_aggOk g hok rc.snn rc.below adj.ctx.nodeval
  exact OwnerChainedBuild.ownerChained_of_anyOption g hok adj ctx.smp ctx.pos tctx hsym rc.oos rc.gn
    (TopGoodUp.anyOptionStep_of_topGood g tctx adj hsym hT)

/-- info: 'AbsSat.GraphPath.Model.TopGoodLadder.ownerChained_of_topGood' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_topGood

/-- **La única hipótesis**: en todo estado válido que el lector visita vale `TopGood`. -/
def ReaderTopGood : Prop :=
  ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g,
    PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true → TopGoodUp.TopGood g

theorem dctx_of_readFromR (g₀ : GPathM) (ctx₀ : PinAliveChain.DCtx g₀) :
    ∀ g, PinAliveChain.ReadFromR g₀ g → PinAliveChain.DCtx g := by
  intro g hR
  induction hR with
  | start => exact ctx₀
  | pin g _ q _ _ _ _ ih => exact PinAliveChain.DCtx_filterAllAgg g ih _

/-- **El lector sin retroceso decide 3-SAT, con la compatibilidad colectiva como única hipótesis.** -/
theorem readerVerdictW_iff_of_readerTopGood (h : ReaderTopGood) (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine ⟨fun h' => ReaderExec.readerVerdictW_sound φ hwf h', fun hsat => ?_⟩
  obtain ⟨a, hsa⟩ := hsat
  obtain ⟨g, hmem, hcs, _, sel, hsel⟩ := ConservationImproves.pureRunW_full_chain φ a hwf hsa
  have hm := (ReaderAggRun.pureRunW_state φ hwf _ hmem).1
  have hsel0 : ChainSound (filterAllAgg g []) sel :=
    ChainSound_filterAllAgg g [] sel hsel (fun _ hreq => absurd hreq List.not_mem_nil)
  have hpos : 0 < g.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ
  have ctx₀ : PinAliveChain.DCtx (filterAllAgg g []) :=
    { rd := ⟨g, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg g [] hm.pms
      sn := AggInvariants.SN_filterAllAgg g [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg g hm.smp hm.rctx.shape.notroot []
      pos := by rw [(pruned_filterAllAgg g []).step_eq]; exact hpos }
  refine PinAliveChain.readerVerdictW_of_chainsR φ _ hmem
    (PickInduction.isValid_of_ChainG _ sel hsel0.chain) (fun g' hR hv' => ?_)
  have ctx := dctx_of_readFromR _ ctx₀ g' hR
  have hoc := ownerChained_of_topGood g' ctx hv' (h φ hwf _ hmem g' hR hv')
  have hent := hasStepEntry_of_isValid g' hv' 0 (Int.le_refl 0) ctx.pos
  simp only [hasStepEntry, List.any_eq_true] at hent
  obtain ⟨q, hq, hqs⟩ := hent
  have hqs' : q.id.step = 0 := eq_of_beq hqs
  obtain ⟨s, hsc, _⟩ := hoc q hq (by rw [hqs']; exact Int.le_refl 0) (by rw [hqs']; exact ctx.pos)
  exact ⟨s, hsc⟩

/-- info: 'AbsSat.GraphPath.Model.TopGoodLadder.readerVerdictW_iff_of_readerTopGood' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_readerTopGood

-- ============================================================
-- Hacia la pasada entera: lo que no toca las tablas
-- ============================================================

/-- **Un pin no toca las tablas de los nodos**, solo la global: conserva `TopGood` tal cual. -/
theorem topGood_filterRequire (g : GPathM) (req : NodeId) (h : TopGoodUp.TopGood g) :
    TopGoodUp.TopGood (filterRequire g req) := h

/-- **El filtro débil tampoco.** -/
theorem topGood_filterWeak (g : GPathM) (e : Int × List NodeId) (h : TopGoodUp.TopGood g) :
    TopGoodUp.TopGood (PureDriverImproves.filterWeak g e) := h

theorem topGood_foldl_filterRequire (reqs : List NodeId) :
    ∀ g : GPathM, TopGoodUp.TopGood g → TopGoodUp.TopGood (reqs.foldl filterRequire g) := by
  induction reqs with
  | nil => intro g h; exact h
  | cons r rs ih => intro g h; exact ih _ (topGood_filterRequire g r h)

/-- info: 'AbsSat.GraphPath.Model.TopGoodLadder.topGood_foldl_filterRequire' does not depend on any axioms -/
#guard_msgs in
#print axioms topGood_foldl_filterRequire

end AbsSat.GraphPath.Model.TopGoodLadder
