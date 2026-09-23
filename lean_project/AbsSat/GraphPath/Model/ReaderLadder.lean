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

-- ============================================================
-- Dónde la completitud sale sola
-- ============================================================

/-- **Sin filtro, la completitud sale de `FullExtG`**: un tramo dentro de la global ya se extiende
dentro de ella, y esa cadena es `ChainSound` por la forma del estado. -/
theorem reviewCompleteCS_of_fullExtG (g : GPathM)
    (hself : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (hsmp : Sons.SMP g) (hroot : Sons.RootAtZero g) (hnr : Parents.NotRoot g)
    (hpos : 0 < g.current_step) (hF : FullExtG g) : ReviewCompleteCS g := by
  intro sel lo hi hlo0 hlohi hhi hs hsg _ _
  obtain ⟨s, hsF, hsg', hag⟩ := hF sel lo hi hlo0 hlohi hhi hs hsg
  exact ⟨s, chainSound_of_fullChain g hself hsmp hroot hnr hpos s ⟨hsF, hsg'⟩, hag⟩

/-- Los pines solo tocan la tabla global. -/
theorem foldl_filterRequire_nodes (reqs : List NodeId) :
    ∀ g : GPathM, (reqs.foldl filterRequire g).nodes = g.nodes ∧
      (reqs.foldl filterRequire g).current_step = g.current_step := by
  induction reqs with
  | nil => intro g; exact ⟨rfl, rfl⟩
  | cons r rs ih => intro g; exact ih (filterRequire g r)

/-- Los pines solo encogen la tabla global. -/
theorem gowners_foldl_filterRequire_sub (reqs : List NodeId) :
    ∀ (g : GPathM) (q : PathNodeId), q ∈ (reqs.foldl filterRequire g).gowners → q ∈ g.gowners := by
  induction reqs with
  | nil => intro g q hq; exact hq
  | cons r rs ih => intro g q hq; exact (List.mem_filter.mp (ih (filterRequire g r) q hq)).1

/-- Una entrada que cumple todos los pines sigue en la tabla global. -/
theorem mem_gowners_foldl_filterRequire (reqs : List NodeId) :
    ∀ (g : GPathM) (q : PathNodeId), q ∈ g.gowners →
      (∀ r ∈ reqs, q.id.step = r.step → q.id = r) → q ∈ (reqs.foldl filterRequire g).gowners := by
  induction reqs with
  | nil => intro g q hq _; exact hq
  | cons r rs ih =>
    intro g q hq hr
    refine ih (filterRequire g r) q (List.mem_filter.mpr ⟨hq, ?_⟩)
      (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))
    if hs : q.id.step = r.step then
      have := hr r List.mem_cons_self hs
      simp [this]
    else
      simp [hs]

/-- **Tras los requisitos DUROS de un envío, la completitud sale de `FullExtG` del estado de antes**:
es el argumento de la cima. Toda cadena completa del estado pasa por la cima, que solo lleva `d`, y
una cadena poseída por pares cumple sola los requisitos de todo nodo que elige
(`MapChain.reqSatisfying_of_pairwiseOwned`); así que el filtro no le quita nada. -/
theorem reviewCompleteCS_of_hardReqs (reqOf : NodeId → List NodeId) (P : GPathM) (d : NodeId)
    (htop : TablesSoundBuild.TopSingleId P d) (hpos : 0 < P.current_step)
    (hrf : ReqFiltered reqOf P)
    (hback : ∀ n ∈ P.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step)
    (hself : ∀ pid n, P.node? pid = some n → pid ∈ n.owners)
    (hsmp : Sons.SMP P) (hroot : Sons.RootAtZero P) (hnr : Parents.NotRoot P)
    (hF : FullExtG P) : ReviewCompleteCS ((reqOf d).foldl filterRequire P) := by
  obtain ⟨hnodes, hcs⟩ := foldl_filterRequire_nodes (reqOf d) P
  have hnode : ∀ y, ((reqOf d).foldl filterRequire P).node? y = P.node? y := by
    intro y; simp only [node?, hnodes]
  -- un tramo del filtrado es tramo del de antes, y al revés
  have segEq : ∀ sel lo hi, Seg ((reqOf d).foldl filterRequire P) sel lo hi ↔ Seg P sel lo hi := by
    intro sel lo hi
    simp only [Seg, Extendable.PartialChain, hnode]
  have hgsub : ∀ q ∈ ((reqOf d).foldl filterRequire P).gowners, q ∈ P.gowners :=
    fun q hq => gowners_foldl_filterRequire_sub (reqOf d) P q hq
  intro sel lo hi hlo0 hlohi hhi hs hsg _ _
  rw [hcs] at hhi
  obtain ⟨s, hsF, hsg', hag⟩ := hF sel lo hi hlo0 hlohi hhi ((segEq sel lo hi).mp hs)
    (fun j hj1 hj2 => hgsub _ (hsg j hj1 hj2))
  -- la cadena cumple los requisitos de la cima
  have hchain := Extendable.isChain_of_partial P s hsF.1
  have howned : PairwiseOwned P s := by
    intro i j hi0 hj0 hi1 hj1 hij
    obtain ⟨hsj, _⟩ := hsF.1.1 j hj0 (by omega)
    obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp hsj
    obtain ⟨_, hstep⟩ := hsF.1.1 i hi0 (by omega)
    refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hstep⟩
    simp only [ownersOf, hnj]
    exact hsF.2 i j hi0 hj0 (by omega) (by omega) hij nj hnj
  have hrs := MapChain.reqSatisfying_of_pairwiseOwned reqOf P hrf hback s hchain howned
  have htopid : (s (P.current_step - 1)).id = d :=
    htop _ (hsg' _ (by omega) (Int.le_refl _)) (hsF.1.1 _ (by omega) (Int.le_refl _)).2
  have hkeep : ∀ j, 0 ≤ j → j ≤ P.current_step - 1 →
      s j ∈ ((reqOf d).foldl filterRequire P).gowners := by
    intro j hj0 hj1
    refine mem_gowners_foldl_filterRequire (reqOf d) P (s j) (hsg' j hj0 hj1) (fun r hr hrs' => ?_)
    have hjs := (hsF.1.1 j hj0 hj1).2
    have hr0 : 0 ≤ r.step := by rw [← hrs', hjs]; exact hj0
    have hr1 : r.step < P.current_step := by rw [← hrs', hjs]; omega
    have := hrs (P.current_step - 1) (by omega) (by omega) r (by rw [htopid]; exact hr) hr0 hr1
    rw [← hjs, hrs', this]
  -- y es una cadena completa del filtrado, dentro de su global
  have hfull : FullChainG ((reqOf d).foldl filterRequire P) s := by
    refine ⟨(segEq s 0 _).mpr ?_, fun j hj0 hj1 => hkeep j hj0 (by rw [hcs] at hj1; exact hj1)⟩
    rw [hcs]; exact hsF
  have hself' : ∀ pid n, ((reqOf d).foldl filterRequire P).node? pid = some n → pid ∈ n.owners :=
    fun pid n h => hself pid n (by rw [← hnode]; exact h)
  have hsmp' : Sons.SMP ((reqOf d).foldl filterRequire P) := by
    intro n hn; rw [hnodes] at hn ⊢; exact hsmp n hn
  have hroot' : Sons.RootAtZero ((reqOf d).foldl filterRequire P) := by
    intro n hn; rw [hnodes] at hn; exact hroot n hn
  have hnr' : Parents.NotRoot ((reqOf d).foldl filterRequire P) := by
    intro n hn; rw [hnodes] at hn; exact hnr n hn
  exact ⟨s, chainSound_of_fullChain _ hself' hsmp' hroot' hnr' (by rw [hcs]; exact hpos) s hfull,
    hag⟩

/-- info: 'AbsSat.GraphPath.Model.ReaderLadder.reviewCompleteCS_of_hardReqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reviewCompleteCS_of_hardReqs

-- ============================================================
-- La escalera restringida a los estados de la máquina
-- ============================================================

/-! La escalera de arriba pide la completitud en **todo** estado con `RCtx`. Pero el lector solo
parte de la línea final de la máquina y solo pincha entradas de la tabla global. Restringida a esos
estados, `FullExtG` viaja con el lector: la tiene el estado de partida (hipótesis de la
construcción) y cada pin la pasa al siguiente (hipótesis de la completitud, ahora **con** `FullExtG`
del estado pinchado). -/

/-- El review agresivo acaba siempre en un `review`. -/
theorem reviewAggFuel_is_review : ∀ (fuel : Nat) (g : GPathM),
    ∃ h, AggressiveReview.reviewAggFuel fuel g = review h := by
  intro fuel
  induction fuel with
  | zero => intro g; exact ⟨g, rfl⟩
  | succ n ih =>
    intro g
    simp only [AggressiveReview.reviewAggFuel]
    split
    · split
      · exact ih _
      · exact ⟨g, rfl⟩
    · exact ⟨g, rfl⟩

/-- **Un estado del lector válido se posee a sí mismo**: es un `review`, y ahí cada nodo pasa
`isValidNode`, que con `OOS` deja al propio nodo como su único owner en su paso. -/
theorem selfOwned_of_readable (g : GPathM) (rd : ReadableAgg g) (hv : isValid g = true) :
    Ownership.SelfOwned g := by
  have rc := RCtx_of_readableAgg g rd
  obtain ⟨g₀, reqs, _, hg⟩ := rd
  obtain ⟨h, hh⟩ := reviewAggFuel_is_review
    (GPathM.measure (reqs.foldl filterRequire g₀) + 1) (reqs.foldl filterRequire g₀)
  have he : g = review h := by rw [hg]; exact hh
  subst he
  exact SelfOwn.SelfOwned_of_OOS h hv rc.oos rc.snn rc.below

/-- **Lo que la construcción debe dar**: cada estado de la línea final se extiende y se posee. -/
def LineFullExt : Prop :=
  ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
    FullExtG kv.2 ∧ Ownership.SelfOwned kv.2

/-- **Lo que el pin debe dar**: la completitud del review tras pinchar una entrada viva de un estado
del lector que ya cumple `FullExtG`. -/
def PinComplete : Prop :=
  ∀ g : GPathM, PinAliveChain.DCtx g → isValid g = true → FullExtG g →
    ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
      ReviewCompleteCS (filterRequire g q.id)

/-- **`FullExtG` viaja con el lector.** -/
theorem fullExtG_of_readFromR (hP : PinComplete) (g₀ : GPathM) (ctx₀ : PinAliveChain.DCtx g₀)
    (hF₀ : FullExtG g₀) :
    ∀ g, PinAliveChain.ReadFromR g₀ g → PinAliveChain.DCtx g ∧ FullExtG g := by
  intro g hR
  induction hR with
  | start => exact ⟨ctx₀, hF₀⟩
  | pin g k q _ hv hk hq ih =>
    obtain ⟨ctx, hF⟩ := ih
    have hqg : q ∈ g.gowners := (List.mem_filter.mp hq).1
    have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
    have hmem := List.mem_of_find?_eq_some hk
    have h0 : 0 ≤ k := mem_intRange_lower hmem
    have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
    refine ⟨PinAliveChain.DCtx_filterAllAgg g ctx _, ?_⟩
    exact fullExtG_reviewAgg_cs _
      (nodupIds_foldl_filterRequire [q.id] g (RCtx_of_readableAgg g ctx.rd).nodup)
      (hP g ctx hv hF q hqg (by rw [hqs]; exact h0) (by rw [hqs]; exact h1))

/-- **Una cadena en cada estado válido que cumple `FullExtG`.** -/
theorem chain_of_fullExtG (g : GPathM) (ctx : PinAliveChain.DCtx g) (hv : isValid g = true)
    (hF : FullExtG g) : ∃ sel, ChainSound g sel := by
  have adj := AdjacentOwners.adj_of_readable g ctx.rd hv ctx.pms ctx.sn
  have hoc := ownerChained_of_fullExtG g adj ctx.smp ctx.pos (RCtx_of_readableAgg g ctx.rd).gn hF
  have hent := hasStepEntry_of_isValid g hv 0 (Int.le_refl 0) ctx.pos
  simp only [hasStepEntry, List.any_eq_true] at hent
  obtain ⟨q, hq, hqs⟩ := hent
  have hqs' : q.id.step = 0 := eq_of_beq hqs
  obtain ⟨sel, hsc, _⟩ := hoc q hq (by rw [hqs']; exact Int.le_refl 0) (by rw [hqs']; exact ctx.pos)
  exact ⟨sel, hsc⟩

/-- **El lector sin retroceso decide 3-SAT, sobre los estados de la máquina.** Dos hipótesis, cada
una de una operación: la construcción deja la línea final extendible (`LineFullExt`), y el review
tras un pin es completo cuando el estado pinchado lo era (`PinComplete`). -/
theorem readerVerdictW_iff_of_machine (hL : LineFullExt) (hP : PinComplete) (φ : Cnf)
    (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine ⟨fun h => ReaderExec.readerVerdictW_sound φ hwf h, fun hsat => ?_⟩
  obtain ⟨a, hsa⟩ := hsat
  obtain ⟨g, hmem, hcs, _, sel, hsel⟩ := ConservationImproves.pureRunW_full_chain φ a hwf hsa
  have hm := (ReaderAggRun.pureRunW_state φ hwf _ hmem).1
  have hsel0 : ChainSound (AggressiveReview.filterAllAgg g []) sel :=
    AggressiveReview.ChainSound_filterAllAgg g [] sel hsel (fun _ hreq => absurd hreq List.not_mem_nil)
  have hpos : 0 < g.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ
  have ctx₀ : PinAliveChain.DCtx (AggressiveReview.filterAllAgg g []) :=
    { rd := ⟨g, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg g [] hm.pms
      sn := AggInvariants.SN_filterAllAgg g [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg g hm.smp hm.rctx.shape.notroot []
      pos := by rw [(AggressiveReview.pruned_filterAllAgg g []).step_eq]; exact hpos }
  obtain ⟨hFg, hso⟩ := hL φ hwf _ hmem
  have hF₀ : FullExtG (AggressiveReview.filterAllAgg g []) :=
    fullExtG_reviewAgg_cs g hm.rctx.nodup
      (reviewCompleteCS_of_fullExtG g hso hm.smp hm.rctx.rootz hm.rctx.shape.notroot hpos hFg)
  exact PinAliveChain.readerVerdictW_of_chainsR φ _ hmem
    (PickInduction.isValid_of_ChainG _ sel hsel0.chain)
    (fun g' hR hv' =>
      have hc := fullExtG_of_readFromR hP _ ctx₀ hF₀ g' hR
      chain_of_fullExtG g' hc.1 hv' hc.2)

/-- info: 'AbsSat.GraphPath.Model.ReaderLadder.readerVerdictW_iff_of_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_machine

end AbsSat.GraphPath.Model.ReaderLadder
