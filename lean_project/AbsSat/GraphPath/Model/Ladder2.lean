-- lean_project/AbsSat/GraphPath/Model/Ladder2.lean
import AbsSat.GraphPath.Model.ExactSeq

/-!
# La escalera sobre las tablas exactas

La línea lleva cuatro cosas: `FullExt1`, la autoposesión, los owners dentro de la global (`OwnIn`) y
`TablesExact`. La semilla, el `up` y la unión las conservan (demostrado); el envío las conserva desde
`SendConfluent2` y `SendTriples`; el pin del lector, desde `PinTriples`. Las parejas ya no son
hipótesis en ningún sitio: salen de `TablesExact`.
-/

namespace AbsSat.GraphPath.Model.Ladder2

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
open AbsSat.GraphPath.Model.FullExt1
open AbsSat.GraphPath.Model.StepFilter
open AbsSat.GraphPath.Model.TablesExact
open AbsSat.GraphPath.Model.ExactSeq
open AbsSat.GraphPath.Model.LineSelf (SelfMem)

variable (φ : Cnf)

/-- Lo que cada estado de la línea lleva. -/
structure LS (g : GPathM) : Prop where
  ext : FullExt1 g
  self : SelfMem g
  own : OwnIn g
  exact : TablesExact g

-- ============================================================
-- Semilla, `up`, unión
-- ============================================================

theorem ownIn_addNode (F : GPathM) (d : NodeId) (t : String) (h : OwnIn F) :
    OwnIn (addNode F d t) := by
  intro n hn q hq
  rw [addNode_gowners]
  rcases ParentOwners.mem_addNode_nodes hn with ⟨m, hm, rfl⟩ | ⟨pid, hpid, rfl⟩
  · rw [upMap_owners] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ (h m hm q hq)
    · exact List.mem_append_right _ (gainedOwners_subset F d m q hq)
  · rw [rowNode_owners] at hq
    rcases rowOwners_mem_gowners_or_self F d pid q hq with hq | rfl
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ hpid

theorem ownIn_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (h₁ : OwnIn g₁) (h₂ : OwnIn g₂) :
    OwnIn (join g₁ g₂) := by
  have G₁ := grown_join_left g₁ g₂
  have G₂ := grown_join_right g₁ g₂ hok
  intro n hn q hq
  rcases ParentOwners.mem_join_nodes' hn with ⟨a, ha, _, hsrc⟩ | hn₂
  · rcases hsrc q hq with hqa | ⟨b, hb, _, hqb⟩
    · exact G₁.gowners_grown q (h₁ a ha q hqa)
    · exact G₂.gowners_grown q (h₂ b hb q hqb)
  · exact G₂.gowners_grown q (h₂ n hn₂ q hq)

theorem ls_initSeed (d : NodeId) : LS (GPathM.initSeed d "") := by
  have hg := Certifies.initSeed_gowners d ""
  refine ⟨Ladder1.fullExt1_initSeed d, LineSelf.selfMem_initSeed d, ?_, ?_⟩
  · intro n hn q hq
    rw [initSeed_nodes] at hn
    rw [List.mem_singleton.mp hn] at hq
    rw [hg, List.mem_singleton.mp hq]
    exact List.mem_singleton_self _
  · rintro r hr q' hq' hne _ _ _
    rw [hg] at hr hq'
    rw [List.mem_singleton.mp hr, List.mem_singleton.mp hq'] at hne
    exact absurd rfl hne

theorem ls_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (hm₁ : MInv φ g₁) (hm₂ : MInv φ g₂)
    (h₁ : LS g₁) (h₂ : LS g₂) : LS (join g₁ g₂) :=
  ⟨fullExt1_join g₁ g₂ hok h₁.ext h₂.ext, LineSelf.selfMem_join g₁ g₂ h₁.self h₂.self,
    ownIn_join g₁ g₂ hok h₁.own h₂.own,
    tablesExact_join g₁ g₂ hok hm₁.rctx.nodup hm₂.rctx.nodup
      (LineSelf.selfOwned_of_selfMem _ h₁.self) (LineSelf.selfOwned_of_selfMem _ h₂.self)
      h₁.own h₂.own h₁.exact h₂.exact⟩

-- ============================================================
-- El envío
-- ============================================================

theorem ls_sent (hC : SendConfluent2 φ) (hT : SendTriples φ) (k : Int) (hk0 : 0 ≤ k)
    (kv : NodeId × GPathM) (hkv : StateOkF φ k kv) (hm : MInv φ kv.2) (hL : LS kv.2) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    LS (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") := by
  have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hsok.onMap
  have hso := LineSelf.selfOwned_of_selfMem _ hL.self
  obtain ⟨hFF, hEF⟩ := sendExact φ hC hT k kv hk0 hkv hm hL.ext hL.exact hso d hd hval
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
  have ctxF := Reader.Ctx_of_readable F (readable_of_readableAgg F hRF) hvF
  have hstepF : F.current_step = k + 1 := by rw [hk.1.step_eq, hkv.step]
  -- los owners de `F` están en pasos no negativos: vienen de `kv.2`, donde son nodos
  have hownF : OwnIn F := by
    intro n hn q hq
    obtain ⟨n₀, hn₀, _, hown₀, _⟩ := hk.1.nodes_derived n hn
    obtain ⟨m, hmm, hmid⟩ := hm.own n₀ hn₀ q (hown₀ q hq)
    have hq0 : 0 ≤ q.id.step := by rw [← hmid]; exact hm.rctx.snn m hmm
    have hq1 : q.id.step < F.current_step := rcF.ownb n hn q hq
    exact ctxF.ownGow n.id n (node?_of_mem rcF.nodup n hn) q hq hq0 hq1
  have hself := LineSelf.selfMem_sent φ kv hm d hval
  rw [heq] at hself ⊢
  exact ⟨fullExt1_addNode F d "" (by rw [hstepF, hdstep]) (by rw [hstepF]; omega) rcF.below rcF.gn
      ctxF.ownGow ctxF.self hFF, hself, ownIn_addNode F d "" hownF,
    tablesExact_addNode F d "" (by rw [hstepF, hdstep]) (by rw [hstepF]; omega) rcF.below
      ctxF.ownGow ctxF.self rcF.oos rcF.ownb hFF hEF⟩

-- ============================================================
-- La línea
-- ============================================================

def LineInv2 (k : Int) (line : PureLine) : Prop :=
  LineInv φ k line ∧ ∀ kv ∈ line, LS kv.2

theorem lineInv2_insertPure (k : Int) (line : PureLine) (key : NodeId) (g : GPathM)
    (hl : LineInv2 φ k line) (hg : StateOkF φ k (key, g)) (hm : MInv φ g) (hgL : LS g) :
    LineInv2 φ k (insertPure line key g) := by
  refine ⟨LineInv_insertPure φ k line key g hl.1 hg hm, ?_⟩
  intro kv hkv
  unfold insertPure at hkv
  cases hf : line.find? (fun x => x.1 == key) with
  | none =>
    simp only [hf] at hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl.2 kv h
    · rw [List.mem_singleton.mp h]; exact hgL
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
      show LS (doJoin e.2 g)
      simp only [doJoin, hok, if_pos]
      exact ls_join φ e.2 g hok (hl.1.2 e hemem) hm (hl.2 e hemem) hgL
    | false =>
      have hx2 : kv = x := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]
      exact hl.2 x hx

theorem lineInv2_pureAdvanceW (hwf : WF φ) (hC : SendConfluent2 φ) (hT : SendTriples φ) (k : Int)
    (hk0 : 0 ≤ k) (line : PureLine) (hl : LineInv2 φ k line) :
    LineInv2 φ (k + 1) (pureAdvanceW φ line) := by
  simp only [pureAdvanceW]
  have hsend : ∀ kv, StateOkF φ k kv → MInv φ kv.2 → LS kv.2 → ∀ acc,
      LineInv2 φ (k + 1) acc → LineInv2 φ (k + 1) (sendAllW φ kv acc) := by
    intro kv hkv hm hL acc hacc
    simp only [sendAllW]
    have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
        ∀ acc, LineInv2 φ (k + 1) acc → LineInv2 φ (k + 1) (l.foldl (sendToW φ kv.2) acc) := by
      intro l
      induction l with
      | nil => intro _ acc h; exact h
      | cons x xs ih =>
        intro hx acc h
        simp only [List.foldl_cons]
        refine ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _ ?_
        have hxd := hx x List.mem_cons_self
        simp only [sendToW]
        split
        · next hval =>
          exact lineInv2_insertPure φ (k + 1) acc x _ h
            (StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv x hxd hval)
            (MInv_sent φ hwf k kv hkv hm x hxd hval)
            (ls_sent φ hC hT k hk0 kv hkv hm hL x hxd hval)
        · exact h
    exact main _ (fun _ hd => hd) acc hacc
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOkF φ k kv ∧ MInv φ kv.2 ∧ LS kv.2) →
      ∀ acc, LineInv2 φ (k + 1) acc →
        LineInv2 φ (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (hsend x hx0.1 hx0.2.1 hx0.2.2 acc h)
  exact main line (fun kv hkv => ⟨hl.1.1.2 kv hkv, hl.1.2 kv hkv, hl.2 kv hkv⟩) []
    ⟨⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem lineInv2_init (hwf : WF φ) : LineInv2 φ 0 (pureInit φ) := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineInv2 φ 0 acc →
        LineInv2 φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (lineInv2_insertPure φ 0 acc x _ h (stateOkF_initSeed φ x hx0)
          (MInv_initSeed φ hwf x hx0) (ls_initSeed x))
  exact main _ (fun _ hdm => hdm) []
    ⟨⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem lineInv2_steps (hwf : WF φ) (hC : SendConfluent2 φ) (hT : SendTriples φ) :
    ∀ (n : Nat) (k : Int) (line : PureLine), 0 ≤ k → LineInv2 φ k line →
      ∀ kv ∈ pureStepsW φ n line, LS kv.2 := by
  intro n
  induction n with
  | zero => intro _ _ _ hl; exact hl.2
  | succ m ih =>
    intro k line hk0 hl
    exact ih (k + 1) _ (by omega) (lineInv2_pureAdvanceW φ hwf hC hT k hk0 line hl)

theorem pureRunW_ls (hwf : WF φ) (hC : SendConfluent2 φ) (hT : SendTriples φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) : LS kv.2 :=
  lineInv2_steps φ hwf hC hT _ 0 (pureInit φ) (Int.le_refl 0) (lineInv2_init φ hwf) kv hkv

/-- info: 'AbsSat.GraphPath.Model.Ladder2.pureRunW_ls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunW_ls

-- ============================================================
-- El lector
-- ============================================================

/-- **Las ternas que sobreviven al pin del lector.** -/
def PinTriples : Prop :=
  ∀ g : GPathM, PinAliveChain.DCtx g → isValid g = true → FullExt1 g → TablesExact g →
    ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
      ReaderExec.firstChoice g = some q.id.step → StepTriples g (q.id.step, [q.id])

/-- **El pin del lector conserva `FullExt1` y `TablesExact`**: es un filtro de un paso. -/
theorem pin_exact (hP : PinTriples) (g : GPathM) (ctx : PinAliveChain.DCtx g)
    (hv : isValid g = true) (hF : FullExt1 g) (hE : TablesExact g) (q : PathNodeId)
    (hq : q ∈ g.gowners) (h0 : 0 ≤ q.id.step) (h1 : q.id.step < g.current_step)
    (hfc : ReaderExec.firstChoice g = some q.id.step)
    (hv' : isValid (filterAllAgg g [q.id]) = true) :
    FullExt1 (filterAllAgg g [q.id]) ∧ TablesExact (filterAllAgg g [q.id]) := by
  have heq : filterAllAgg g [q.id] = reviewAgg (filterWeak g (q.id.step, [q.id])) := by
    simp only [filterAllAgg, List.foldl_cons, List.foldl_nil, filterRequire_eq_filterWeak]
  rw [heq] at hv' ⊢
  have rc := RCtx_of_readableAgg g ctx.rd
  have c : SCtx g := ⟨rc, ctx.smp, ReaderLadder.selfOwned_of_readable g ctx.rd hv, ctx.pos⟩
  exact ⟨fullExt1_stepFilter g _ rc ctx.smp c.self ctx.pos hF h0 h1
      (frontierPairs_of_tablesExact g hE _) hv',
    tablesExact_stepFilter g _ c hE h0 h1 (hP g ctx hv hF hE q hq h0 h1 hfc) hv'⟩

theorem exact_of_readFromR (hP : PinTriples) (g₀ : GPathM) (ctx₀ : PinAliveChain.DCtx g₀)
    (hF₀ : FullExt1 g₀) (hE₀ : TablesExact g₀) :
    ∀ g, PinAliveChain.ReadFromR g₀ g →
      PinAliveChain.DCtx g ∧ (isValid g = true → FullExt1 g ∧ TablesExact g) := by
  intro g hR
  induction hR with
  | start => exact ⟨ctx₀, fun _ => ⟨hF₀, hE₀⟩⟩
  | pin g k q _ hv hk hq ih =>
    obtain ⟨ctx, hFE⟩ := ih
    have hqg : q ∈ g.gowners := (List.mem_filter.mp hq).1
    have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
    have hmem := List.mem_of_find?_eq_some hk
    have h0 : 0 ≤ k := mem_intRange_lower hmem
    have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
    exact ⟨PinAliveChain.DCtx_filterAllAgg g ctx _, fun hv' =>
      pin_exact hP g ctx hv (hFE hv).1 (hFE hv).2 q hqg (by rw [hqs]; exact h0)
        (by rw [hqs]; exact h1) (by rw [hqs]; exact hk) hv'⟩

/-- **El lector sin retroceso decide 3-SAT**, desde tres hipótesis: el envío de una vez es el de
uno a uno (`SendConfluent2`), y las ternas que sobreviven a cada filtro de un paso ya tenían cadena
común, en los envíos (`SendTriples`) y en los pines del lector (`PinTriples`). Semilla, `up`, unión,
review sin filtro y parejas: demostrados. -/
theorem readerVerdictW_iff_of_triples (hC : ∀ ψ : Cnf, WF ψ → SendConfluent2 ψ)
    (hT : ∀ ψ : Cnf, WF ψ → SendTriples ψ) (hP : PinTriples) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine ⟨fun h => ReaderExec.readerVerdictW_sound φ hwf h, fun hsat => ?_⟩
  obtain ⟨a, hsa⟩ := hsat
  obtain ⟨g, hmem, hcs, _, sel, hsel⟩ := ConservationImproves.pureRunW_full_chain φ a hwf hsa
  have hm := (ReaderAggRun.pureRunW_state φ hwf _ hmem).1
  have hL := pureRunW_ls φ hwf (hC φ hwf) (hT φ hwf) _ hmem
  have hso := LineSelf.selfOwned_of_selfMem _ hL.self
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
    fullExt1_reviewAgg g (Ladder1.reviewComplete1_of_fullExt1 g hso hm.smp hm.rctx.rootz
      hm.rctx.shape.notroot hpos hL.ext)
  have hE₀ : TablesExact (filterAllAgg g []) :=
    tablesExact_reviewAgg g hm.rctx.nodup hso hm.smp hm.rctx.rootz hm.rctx.shape.notroot hpos
      hL.exact
  exact PinAliveChain.readerVerdictW_of_chainsR φ _ hmem
    (PickInduction.isValid_of_ChainG _ sel hsel0.chain)
    (fun g' hR hv' =>
      have hc := exact_of_readFromR hP _ ctx₀ hF₀ hE₀ g' hR
      Ladder1.chain_of_fullExt1 g' hc.1 hv' (hc.2 hv').1)

/-- info: 'AbsSat.GraphPath.Model.Ladder2.readerVerdictW_iff_of_triples' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_triples

end AbsSat.GraphPath.Model.Ladder2
