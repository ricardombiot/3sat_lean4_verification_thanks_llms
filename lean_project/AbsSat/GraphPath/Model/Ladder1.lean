-- lean_project/AbsSat/GraphPath/Model/Ladder1.lean
import AbsSat.GraphPath.Model.LineExt
import AbsSat.GraphPath.Model.FullExt1

/-!
# La escalera sobre `FullExt1`

La misma escalera restringida a la máquina (`ReaderLadder.readerVerdictW_iff_of_machine`,
`LineExt.readerVerdictW_iff_of_ops`), pero con el invariante de un solo nodo. La unión deja de ser
hipótesis (`FullExt1.fullExt1_join`), y quedan dos, de la misma forma —**tras un filtro, el estado
revisado cumple `FullExt1`**, que es la completitud del review entrada a entrada
(`reviewComplete1_of_revised`)—:

* `SendExt1`: tras el filtro débil y los requisitos duros de un envío;
* `PinExt1`: tras un pin del lector (medido: `row-degree ext1`, 0 fallos).
-/

namespace AbsSat.GraphPath.Model.Ladder1

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF Fsac prunes_Fsac StateOkF_sent
  stateOkF_initSeed okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.FullExt (FullChainG chainSound_of_fullChain)
open AbsSat.GraphPath.Model.FullExt1

variable (φ : Cnf)

-- ============================================================
-- Las dos hipótesis
-- ============================================================

/-- **Tras los filtros de un envío, el estado revisado cumple `FullExt1`**, si el que envía lo
cumplía y el envío sale válido. Es lo que `row-degree ext1` mide. -/
def SendExt1 : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 → FullExt1 kv.2 →
    Ownership.SelfOwned kv.2 → ∀ d ∈ mapSons φ kv.1.step kv.1.index,
      isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true →
      FullExt1 (filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d))

/-- **Tras un pin del lector, el estado revisado cumple `FullExt1`**, si el pinchado lo cumplía y el
pin —en el primer paso con elección, como hace el lector— lo deja válido. -/
def PinExt1 : Prop :=
  ∀ g : GPathM, PinAliveChain.DCtx g → isValid g = true → FullExt1 g →
    ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
      ReaderExec.firstChoice g = some q.id.step →
      isValid (filterAllAgg g [q.id]) = true → FullExt1 (filterAllAgg g [q.id])

/-- **Son la completitud del review, entrada a entrada**: `FullExt1` del revisado da
`ReviewComplete1` del filtrado —la cadena del revisado es `ChainSound` y el review solo quita
(`SubsetSemantics.ChainSound_of_pruned`)—, y al revés es `fullExt1_reviewAgg`. -/
theorem reviewComplete1_of_revised (X : GPathM) (hnd : NodupIds X) (hsmp : Sons.SMP X)
    (hself : ∀ pid n, (reviewAgg X).node? pid = some n → pid ∈ n.owners)
    (hsmp' : Sons.SMP (reviewAgg X)) (hroot : Sons.RootAtZero (reviewAgg X))
    (hnr : Parents.NotRoot (reviewAgg X)) (hpos : 0 < (reviewAgg X).current_step)
    (h : FullExt1 (reviewAgg X)) : ReviewComplete1 X := by
  have hpr := pruned_reviewAgg X
  intro q hq h0 h1
  obtain ⟨s, hs, hsq⟩ := h q hq h0 (by rw [hpr.step_eq]; exact h1)
  exact ⟨s, SubsetSemantics.ChainSound_of_pruned hpr hnd hsmp s
    (chainSound_of_fullChain _ hself hsmp' hroot hnr hpos s hs), hsq⟩

-- ============================================================
-- La línea
-- ============================================================

theorem fullExt1_initSeed (d : NodeId) : FullExt1 (GPathM.initSeed d "") :=
  fullExt1_of_fullExtG _ (GownersNodes.GN_initSeed d "") (LineExt.fullExtG_initSeed d)

theorem fullExt1_sent (hS : SendExt1 φ) (k : Int) (hk0 : 0 ≤ k) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) (hm : MInv φ kv.2) (hF : FullExt1 kv.2)
    (hso : Ownership.SelfOwned kv.2) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    FullExt1 (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") := by
  have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hsok.onMap
  let W := filterWeakAll kv.2 (weakReqOfCnf φ d)
  let F := filterAllAgg W (reqOfCnf φ d)
  have hk : Keeps kv.2 F := Keeps.trans (keeps_filterWeakAll _ _) (keeps_filterAllAgg _ _)
  have hcW := RCtx_of_keeps (keeps_filterWeakAll kv.2 (weakReqOfCnf φ d)) hm.rctx
  have hRF : ReadableAgg F := ⟨W, reqOfCnf φ d, hcW, rfl⟩
  have rcF := RCtx_of_readableAgg F hRF
  have hvF : isValid F = true := by
    cases h : isValid F with
    | true => rfl
    | false =>
      exfalso
      have he : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = F := by
        simp only [upFilteringWeak, GPathM.up, F, W] at h ⊢
        rw [if_neg (by rw [h]; exact Bool.false_ne_true)]
      rw [he, h] at hval
      exact Bool.false_ne_true hval
  have heq : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = addNode F d "" := by
    simp only [upFilteringWeak, GPathM.up, F, W] at hvF ⊢
    rw [if_pos hvF]
  rw [heq]
  have hFF : FullExt1 F := hS k kv hkv hm hF hso d hd hval
  have ctxF := Reader.Ctx_of_readable F (readable_of_readableAgg F hRF) hvF
  have hstepF : F.current_step = k + 1 := by rw [hk.1.step_eq, hkv.step]
  exact fullExt1_addNode F d "" (by rw [hstepF, hdstep]) (by rw [hstepF]; omega) rcF.below rcF.gn
    ctxF.ownGow ctxF.self hFF

def LineInv1 (k : Int) (line : PureLine) : Prop :=
  LineInv φ k line ∧ ∀ kv ∈ line, FullExt1 kv.2 ∧ LineSelf.SelfMem kv.2

theorem lineInv1_insertPure (k : Int) (line : PureLine) (key : NodeId) (g : GPathM)
    (hl : LineInv1 φ k line) (hg : StateOkF φ k (key, g)) (hm : MInv φ g) (hgF : FullExt1 g)
    (hgS : LineSelf.SelfMem g) :
    LineInv1 φ k (insertPure line key g) := by
  refine ⟨LineInv_insertPure φ k line key g hl.1 hg hm, ?_⟩
  intro kv hkv
  unfold insertPure at hkv
  cases hf : line.find? (fun x => x.1 == key) with
  | none =>
    simp only [hf] at hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl.2 kv h
    · rw [List.mem_singleton.mp h]; exact ⟨hgF, hgS⟩
  | some e =>
    simp only [hf] at hkv
    obtain ⟨x, hx, hEq⟩ := List.mem_map.mp hkv
    cases hb : x.1 == key with
    | true =>
      have hx2 : kv = (key, doJoin e.2 g) := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]
      have hekey : e.1 = key :=
        eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
      have hemem : e ∈ line := List.mem_of_find?_eq_some hf
      have hesok : StateOkF φ k (key, e.2) := by
        have h := hl.1.1.2 e hemem
        rwa [← hekey]
      have hok := okJoin_of_stateOkF φ k key e.2 g hesok hg
      show FullExt1 (doJoin e.2 g) ∧ LineSelf.SelfMem (doJoin e.2 g)
      simp only [doJoin, hok, if_pos]
      exact ⟨fullExt1_join e.2 g hok (hl.2 e hemem).1 hgF,
        LineSelf.selfMem_join e.2 g (hl.2 e hemem).2 hgS⟩
    | false =>
      have hx2 : kv = x := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]
      exact hl.2 x hx

theorem lineInv1_sendToW (hwf : WF φ) (hS : SendExt1 φ) (k : Int) (hk0 : 0 ≤ k)
    (kv : NodeId × GPathM) (hkv : StateOkF φ k kv) (hm : MInv φ kv.2) (hF : FullExt1 kv.2)
    (hsm : LineSelf.SelfMem kv.2)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (next : PureLine)
    (hn : LineInv1 φ (k + 1) next) : LineInv1 φ (k + 1) (sendToW φ kv.2 next d) := by
  simp only [sendToW]
  split
  · next hval =>
    exact lineInv1_insertPure φ (k + 1) next d _ hn
      (StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval)
      (MInv_sent φ hwf k kv hkv hm d hd hval) (fullExt1_sent φ hS k hk0 kv hkv hm hF (LineSelf.selfOwned_of_selfMem _ hsm) d hd hval)
      (LineSelf.selfMem_sent φ kv hm d hval)
  · exact hn

theorem lineInv1_pureAdvanceW (hwf : WF φ) (hS : SendExt1 φ) (k : Int) (hk0 : 0 ≤ k)
    (line : PureLine) (hl : LineInv1 φ k line) : LineInv1 φ (k + 1) (pureAdvanceW φ line) := by
  simp only [pureAdvanceW]
  have hsend : ∀ kv, StateOkF φ k kv → MInv φ kv.2 → FullExt1 kv.2 → LineSelf.SelfMem kv.2 →
      ∀ acc, LineInv1 φ (k + 1) acc → LineInv1 φ (k + 1) (sendAllW φ kv acc) := by
    intro kv hkv hm hF hsm acc hacc
    simp only [sendAllW]
    have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
        ∀ acc, LineInv1 φ (k + 1) acc → LineInv1 φ (k + 1) (l.foldl (sendToW φ kv.2) acc) := by
      intro l
      induction l with
      | nil => intro _ acc h; exact h
      | cons x xs ih =>
        intro hx acc h
        simp only [List.foldl_cons]
        exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
          (lineInv1_sendToW φ hwf hS k hk0 kv hkv hm hF hsm x (hx x List.mem_cons_self) acc h)
    exact main _ (fun _ hd => hd) acc hacc
  have main : ∀ (l : PureLine),
      (∀ kv ∈ l, StateOkF φ k kv ∧ MInv φ kv.2 ∧ FullExt1 kv.2 ∧ LineSelf.SelfMem kv.2) →
      ∀ acc, LineInv1 φ (k + 1) acc →
        LineInv1 φ (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (hsend x hx0.1 hx0.2.1 hx0.2.2.1 hx0.2.2.2 acc h)
  exact main line (fun kv hkv => ⟨hl.1.1.2 kv hkv, hl.1.2 kv hkv, (hl.2 kv hkv).1, (hl.2 kv hkv).2⟩) []
    ⟨⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem lineInv1_init (hwf : WF φ) : LineInv1 φ 0 (pureInit φ) := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineInv1 φ 0 acc →
        LineInv1 φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (lineInv1_insertPure φ 0 acc x _ h (stateOkF_initSeed φ x hx0)
          (MInv_initSeed φ hwf x hx0) (fullExt1_initSeed x) (LineSelf.selfMem_initSeed x))
  exact main _ (fun _ hdm => hdm) []
    ⟨⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem lineInv1_steps (hwf : WF φ) (hS : SendExt1 φ) :
    ∀ (n : Nat) (k : Int) (line : PureLine), 0 ≤ k → LineInv1 φ k line →
      ∀ kv ∈ pureStepsW φ n line, FullExt1 kv.2 := by
  intro n
  induction n with
  | zero => intro _ _ _ hl kv hkv; exact (hl.2 kv hkv).1
  | succ m ih =>
    intro k line hk0 hl
    exact ih (k + 1) _ (by omega) (lineInv1_pureAdvanceW φ hwf hS k hk0 line hl)

/-- **La línea final cumple `FullExt1`**, con `SendExt1` como única hipótesis. -/
theorem pureRunW_fullExt1 (hwf : WF φ) (hS : SendExt1 φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) : FullExt1 kv.2 :=
  lineInv1_steps φ hwf hS _ 0 (pureInit φ) (Int.le_refl 0) (lineInv1_init φ hwf) kv hkv

-- ============================================================
-- El lector
-- ============================================================

/-- **Sin filtro, la completitud sale sola** de `FullExt1`. -/
theorem reviewComplete1_of_fullExt1 (g : GPathM)
    (hself : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (hsmp : Sons.SMP g) (hroot : Sons.RootAtZero g) (hnr : Parents.NotRoot g)
    (hpos : 0 < g.current_step) (h : FullExt1 g) : ReviewComplete1 g := by
  intro q hq h0 h1
  obtain ⟨s, hs, hsq⟩ := h q ((pruned_reviewAgg g).gowners_sub q hq) h0 h1
  exact ⟨s, chainSound_of_fullChain g hself hsmp hroot hnr hpos s hs, hsq⟩

theorem fullExt1_of_readFromR (hP : PinExt1) (g₀ : GPathM) (ctx₀ : PinAliveChain.DCtx g₀)
    (hF₀ : FullExt1 g₀) :
    ∀ g, PinAliveChain.ReadFromR g₀ g → PinAliveChain.DCtx g ∧ (isValid g = true → FullExt1 g) := by
  intro g hR
  induction hR with
  | start => exact ⟨ctx₀, fun _ => hF₀⟩
  | pin g k q _ hv hk hq ih =>
    obtain ⟨ctx, hF⟩ := ih
    have hqg : q ∈ g.gowners := (List.mem_filter.mp hq).1
    have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
    have hmem := List.mem_of_find?_eq_some hk
    have h0 : 0 ≤ k := mem_intRange_lower hmem
    have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
    exact ⟨PinAliveChain.DCtx_filterAllAgg g ctx _,
      hP g ctx hv (hF hv) q hqg (by rw [hqs]; exact h0) (by rw [hqs]; exact h1)
        (by rw [hqs]; exact hk)⟩

theorem chain_of_fullExt1 (g : GPathM) (ctx : PinAliveChain.DCtx g) (hv : isValid g = true)
    (hF : FullExt1 g) : ∃ sel, ChainSound g sel := by
  have adj := AdjacentOwners.adj_of_readable g ctx.rd hv ctx.pms ctx.sn
  have hoc := ownerChained_of_fullExt1 g adj ctx.smp ctx.pos hF
  have hent := hasStepEntry_of_isValid g hv 0 (Int.le_refl 0) ctx.pos
  simp only [hasStepEntry, List.any_eq_true] at hent
  obtain ⟨q, hq, hqs⟩ := hent
  have hqs' : q.id.step = 0 := eq_of_beq hqs
  obtain ⟨sel, hsc, _⟩ := hoc q hq (by rw [hqs']; exact Int.le_refl 0) (by rw [hqs']; exact ctx.pos)
  exact ⟨sel, hsc⟩

/-- **El lector sin retroceso decide 3-SAT**, con dos hipótesis de la misma forma: el estado
revisado cumple `FullExt1` tras los filtros de un envío (`SendExt1`) y tras un pin del lector
(`PinExt1`). La unión, el `up`, la semilla y el inicio del lector están demostrados. -/
theorem readerVerdictW_iff_of_ext1 (hS : ∀ ψ : Cnf, WF ψ → SendExt1 ψ)
    (hP : PinExt1) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine ⟨fun h => ReaderExec.readerVerdictW_sound φ hwf h, fun hsat => ?_⟩
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
  have hF₀ : FullExt1 (filterAllAgg g []) :=
    fullExt1_reviewAgg g (reviewComplete1_of_fullExt1 g (LineSelf.pureRunW_selfOwned φ hwf _ hmem)
      hm.smp hm.rctx.rootz hm.rctx.shape.notroot hpos (pureRunW_fullExt1 φ hwf (hS φ hwf) _ hmem))
  exact PinAliveChain.readerVerdictW_of_chainsR φ _ hmem
    (PickInduction.isValid_of_ChainG _ sel hsel0.chain)
    (fun g' hR hv' =>
      have hc := fullExt1_of_readFromR hP _ ctx₀ hF₀ g' hR
      chain_of_fullExt1 g' hc.1 hv' (hc.2 hv'))

/-- info: 'AbsSat.GraphPath.Model.Ladder1.readerVerdictW_iff_of_ext1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_ext1

end AbsSat.GraphPath.Model.Ladder1
