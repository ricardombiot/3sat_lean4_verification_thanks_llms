-- lean_project/AbsSat/GraphPath/Model/ReaderLadder.lean
import AbsSat.GraphPath.Model.FullExt

/-!
# La escalera del lector, con una sola hipótesis

    FilterReviewComplete  →  FullExtG (de cada estado que el lector lee)  →  OwnerChained
                          →  PinAlive  →  (readerVerdictW φ = true ↔ Satisfiable φ)

La hipótesis habla de **un estado filtrado y su review**, nada más: un tramo dentro de la tabla
global que sobrevive al review agresivo ya se extendía, antes del review, a una cadena que sobrevive
al review (`ChainSound`). La otra dirección —si se extiende, sobrevive— está demostrada
(`FullExt.seg_survives_of_extends`, sobre `ChainSound_reviewAgg`).

Medido (`row-degree filterkill`), tras cada filtro de la construcción y de los pines del lector:
ningún tramo que no se extiende sobrevive —0 de 1.896 en `dos_de_tres.cnf`, 0 de 223.027 en las
aleatorias, semilla 1— y todos los que se extienden sobreviven.
-/

namespace AbsSat.GraphPath.Model.ReaderLadder

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.SegReview
open AbsSat.GraphPath.Model.TopGoodUp (Seg)
open AbsSat.GraphPath.Model.FullExt

/-- **La completitud del review, en la forma que la escalera usa.** -/
def ReviewCompleteCS (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ g.current_step - 1 →
    Seg g sel lo hi → (∀ j, lo ≤ j → j ≤ hi → sel j ∈ g.gowners) →
    Seg (AggressiveReview.reviewAgg g) sel lo hi →
    (∀ j, lo ≤ j → j ≤ hi → sel j ∈ (AggressiveReview.reviewAgg g).gowners) →
    ∃ s, ChainSound g s ∧ ∀ j, lo ≤ j → j ≤ hi → s j = sel j

/-- **Con ella, el estado revisado cumple `FullExtG`**, sin ninguna hipótesis de forma: la cadena
sobrevive al review (`ChainSound_reviewAgg`) y una cadena que sobrevive es completa y está dentro de
la global (`fullChain_of_chainSound`). -/
theorem fullExtG_reviewAgg_cs (g : GPathM) (hnd : NodupIds g) (hc : ReviewCompleteCS g) :
    FullExtG (AggressiveReview.reviewAgg g) := by
  have hpr := AggressiveReview.pruned_reviewAgg g
  intro sel lo hi hlo0 hlohi hhi hs hsg
  have hhi' : hi ≤ g.current_step - 1 := by rw [← hpr.step_eq]; exact hhi
  obtain ⟨s, hcs, hag⟩ := hc sel lo hi hlo0 hlohi hhi' (seg_of_pruned hpr hnd sel lo hi hs)
    (fun j hj1 hj2 => hpr.gowners_sub _ (hsg j hj1 hj2)) hs hsg
  have hR := fullChain_of_chainSound _ s (AggressiveReview.ChainSound_reviewAgg g s hcs)
  exact ⟨s, hR.1, hR.2, hag⟩

/-- **La hipótesis de la escalera**: la completitud del review en todo estado filtrado del lector. -/
def FilterReviewComplete : Prop :=
  ∀ (g₀ : GPathM) (reqs : List NodeId), Reader.RCtx g₀ → ReviewCompleteCS (reqs.foldl filterRequire g₀)

theorem nodupIds_foldl_filterRequire (reqs : List NodeId) :
    ∀ g : GPathM, NodupIds g → NodupIds (reqs.foldl filterRequire g) := by
  induction reqs with
  | nil => intro g h; exact h
  | cons r rs ih => intro g h; exact ih _ h

/-- **Todo estado que el lector lee cumple `OwnerChained`.** -/
theorem ownerChained_of_filterReviewComplete (h : FilterReviewComplete) :
    ∀ g, PinAliveChain.DCtx g → isValid g = true → ReaderChain.OwnerChained g := by
  intro g ctx hv
  have adj := AdjacentOwners.adj_of_readable g ctx.rd hv ctx.pms ctx.sn
  have rc := RCtx_of_readableAgg g ctx.rd
  obtain ⟨g₀, reqs, hc0, hg⟩ := ctx.rd
  have hF : FullExtG g := by
    rw [hg]
    exact fullExtG_reviewAgg_cs _ (nodupIds_foldl_filterRequire reqs g₀ hc0.nodup) (h g₀ reqs hc0)
  exact ownerChained_of_fullExtG g adj ctx.smp ctx.pos rc.gn hF

/-- **`PinAlive`, desde la completitud del review.** -/
theorem pinAlive_of_filterReviewComplete (h : FilterReviewComplete) : PinAliveChain.PinAlive :=
  PinAliveChain.pinAlive_of_ownerChained (ownerChained_of_filterReviewComplete h)

/-- **El lector sin retroceso decide 3-SAT, con la completitud del review como única hipótesis.** -/
theorem readerVerdictW_iff_of_filterReviewComplete (h : FilterReviewComplete) (φ : Cnf)
    (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  PinAliveChain.readerVerdictW_iff_of_pinAlive (pinAlive_of_filterReviewComplete h) φ hwf

/--
info: 'AbsSat.GraphPath.Model.ReaderLadder.readerVerdictW_iff_of_filterReviewComplete' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_filterReviewComplete

end AbsSat.GraphPath.Model.ReaderLadder
