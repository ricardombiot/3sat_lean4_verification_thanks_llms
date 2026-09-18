-- lean_project/AbsSat/GraphPath/Model/PinUp.lean
import AbsSat.GraphPath.Model.PinSplit

/-!
# Bottom-up: the only choice is a variable's value

Pinning the steps bottom-up (probe `pinup`, v145), all the choice is at the variable steps: at a negation,
fusion or clause step the steps below have already decided everything, and at a variable step **every**
live value keeps the state valid. This module proves the first half and keeps the second as the
hypothesis:

* **`decided_off_var`** (no hypothesis) — with the steps below decided (one map node each), a negation,
  fusion or clause step is decided too: a negation node's requirement names its variable's value, a
  clause row's requirements name its three literals' values, and the node's owners carry its
  requirements (`ReqFiltered`); fusion steps have one map node.
* **`LivePinUp`** — the hypothesis: with the steps below `2v` decided and the state valid, pinning **any
  live value** of variable `v` keeps it valid.
* **`complete_up`** — under it, pinning bottom-up never gets stuck and ends with every step decided; the
  state is then a path (`PinExtends.chain_of_ids`).
* **`verdict_iff_up`**, **`answer_unsat_up`** — the Improves verdict under `LivePinUp` alone.
-/

namespace AbsSat.GraphPath.Model.PinUp

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.AggFixpoint (AggOk)
open AbsSat.GraphPath.Model.SupportSplit (mem_of_hasNode')
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.PickInduction (gowner_of_isValid)
open AbsSat.GraphPath.Model.MapReachable (NodesOnMap NodesOnMap_of_pruned)
open AbsSat.GraphPath.Model.ReaderComplete (pin_id sat_decode)
open AbsSat.GraphPath.Model.PinExtends
open AbsSat.GraphPath.Model.PinSplit (pin_keeps_of_all)

variable (φ : Cnf)

-- ============================================================
-- Decided steps
-- ============================================================

/-- Every live node of step `k` carries the same map node. -/
def Decided (S : GPathM) (k : Int) : Prop :=
  ∀ a b, Mem S a → Mem S b → a.id.step = k → b.id.step = k → a.id = b.id

theorem nodeId_eq {x y : NodeId} (hs : x.step = y.step) (hi : x.index = y.index) : x = y := by
  cases x; cases y; cases hs; cases hi; rfl

theorem mem_of_pruned {S F : GPathM} (hpr : Pruned S F) (hnd : NodupIds S) {a : PathNodeId} (ha : Mem F a) :
    Mem S a := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨n₀, hn₀, hid, _, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hn)
  have ha' := node?_id_eq F a n hn
  exact ⟨n₀, by rw [← ha', hid]; exact node?_of_mem hnd n₀ hn₀⟩

theorem decided_of_pruned {S F : GPathM} (hpr : Pruned S F) (hnd : NodupIds S) {k : Int} (h : Decided S k) :
    Decided F k :=
  fun a b ha hb => h a b (mem_of_pruned hpr hnd ha) (mem_of_pruned hpr hnd hb)

theorem reqFiltered_of_pruned {S F : GPathM} (hpr : Pruned S F) (h : ReqFiltered (reqOfCnf φ) S) :
    ReqFiltered (reqOfCnf φ) F := by
  intro d hd req hreq q hq hs
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived d hd
  rw [hid] at hreq
  exact h n hn req hreq q (hown q hq) hs

/-- A pinned step is decided. -/
theorem decided_pin (S : GPathM) (m : NodeId) (hrf : RF (filterAllAgg S [m]))
    (hv : isValid (filterAllAgg S [m]) = true) : Decided (filterAllAgg S [m]) m.step := by
  have ad := adj_rf hrf hv
  intro a b ha hb hsa hsb
  rw [pin_id S m a (mem_gowner _ ad ha) hsa, pin_id S m b (mem_gowner _ ad hb) hsb]

-- ============================================================
-- Off the variable steps, the steps below decide
-- ============================================================

theorem onMap_of_mem (S : GPathM) (hmap : NodesOnMap φ S) {a : PathNodeId} (ha : Mem S a) :
    a.id ∈ mapNodes φ a.id.step := by
  obtain ⟨n, hn⟩ := ha
  have := hmap n (List.mem_of_find?_eq_some hn)
  rw [node?_id_eq S a n hn] at this
  exact this

/-- A live node's requirement is the map node of one of its owners. -/
theorem owner_at_req (S : GPathM) (ad : AdjacentOwners.Adj S) (hok : AggOk S) (hsmp : Sons.SMP S)
    (hrf : ReqFiltered (reqOfCnf φ) S) {a : PathNodeId} (ha : Mem S a) (req : NodeId)
    (hreq : req ∈ reqOfCnf φ a.id) (h0 : 0 ≤ req.step) (h1 : req.step < S.current_step) :
    ∃ c, Mem S c ∧ c.id = req := by
  have sup := sup_self S ad hok hsmp
  obtain ⟨v, hav, hvs⟩ := sup.cov a ha req.step h0 h1
  obtain ⟨m, hm, hin, hmv⟩ := hav
  have hid := node?_id_eq S a m hm
  exact ⟨v, hmv, hrf m (List.mem_of_find?_eq_some hm) req (by rw [hid]; exact hreq) v hin hvs⟩

/-- Two live nodes whose requirements at a decided step are functions of their indices. -/
theorem req_agree (S : GPathM) (ad : AdjacentOwners.Adj S) (hok : AggOk S) (hsmp : Sons.SMP S)
    (hrf : ReqFiltered (reqOfCnf φ) S) {a b : PathNodeId} (ha : Mem S a) (hb : Mem S b)
    (ra rb : NodeId) (hra : ra ∈ reqOfCnf φ a.id) (hrb : rb ∈ reqOfCnf φ b.id) (hs : ra.step = rb.step)
    (h0 : 0 ≤ ra.step) (h1 : ra.step < S.current_step) (hdec : Decided S ra.step) : ra = rb := by
  obtain ⟨c, hc, hcid⟩ := owner_at_req φ S ad hok hsmp hrf ha ra hra h0 h1
  obtain ⟨d, hd, hdid⟩ := owner_at_req φ S ad hok hsmp hrf hb rb hrb (by omega) (by omega)
  have := hdec c d hc hd (by rw [hcid]) (by rw [hdid, hs])
  rw [← hcid, ← hdid, this]

theorem litStep_bounds (lt : Lit) (hlt : lt.v < φ.nVars) : 0 ≤ lt.step ∧ lt.step < litBlock φ := by
  unfold Lit.step litBlock
  refine ⟨?_, ?_⟩ <;> split <;> omega

/-- **Off the variable steps, the steps below decide.** -/
theorem decided_off_var (hwf : WF φ) (S : GPathM) (ad : AdjacentOwners.Adj S) (hok : AggOk S)
    (hsmp : Sons.SMP S) (hrf : ReqFiltered (reqOfCnf φ) S) (hmap : NodesOnMap φ S)
    (hcs : S.current_step = stepCount φ) (l : Int) (hl0 : 0 ≤ l) (hl1 : l < stepCount φ)
    (hnv : ¬ (l < litBlock φ ∧ l % 2 = 0)) (hpre : ∀ k, 0 ≤ k → k < l → Decided S k) : Decided S l := by
  have hnv' : l < litBlock φ → l % 2 = 1 := fun h => by
    have h2 : ¬ (l % 2 = 0) := fun h0 => hnv ⟨h, h0⟩
    clear hnv
    omega
  clear hnv
  intro a b ha hb hsa hsb
  have hma := onMap_of_mem φ S hmap ha
  have hmb := onMap_of_mem φ S hmap hb
  rw [hsa] at hma
  rw [hsb] at hmb
  by_cases hlit : l < litBlock φ
  · -- a negation step: the requirement names the variable's value
    have hodd : l % 2 = 1 := hnv' hlit
    clear hnv'
    have hv : ((l / 2).toNat) < φ.nVars := by unfold litBlock at hlit; omega
    have hneg : ∀ x : NodeId, x.step = l → reqOfCnf φ x = [{ step := varStep (l / 2).toNat, index := 1 - x.index }] :=
      fun x hx => reqOfCnf_neg φ x _ hv (by rw [hx]; unfold negStep; omega)
    have hst : (varStep (l / 2).toNat) = l - 1 := by unfold varStep; omega
    have heq := req_agree φ S ad hok hsmp hrf ha hb
      { step := varStep (l / 2).toNat, index := 1 - a.id.index }
      { step := varStep (l / 2).toNat, index := 1 - b.id.index }
      (by rw [hneg a.id hsa]; exact List.mem_singleton_self _)
      (by rw [hneg b.id hsb]; exact List.mem_singleton_self _) rfl
      (by show 0 ≤ varStep (l / 2).toNat; rw [hst]; omega)
      (by show varStep (l / 2).toNat < S.current_step; rw [hst, hcs]; omega)
      (hpre _ (by show 0 ≤ varStep (l / 2).toNat; rw [hst]; omega)
        (by show varStep (l / 2).toNat < l; rw [hst]; omega))
    have hidx : 1 - a.id.index = 1 - b.id.index := congrArg NodeId.index heq
    exact nodeId_eq (by rw [hsa, hsb]) (by omega)
  · clear hnv'
    by_cases hclause : litBlock φ < l ∧ l < fusionTop φ
    · -- a clause step: the three requirements name the row's three literal values
      let j : Nat := (l - litBlock φ - 1).toNat
      have hjlt : j < φ.clauses.length := by
        show (l - litBlock φ - 1).toNat < φ.clauses.length; unfold fusionTop at hclause; unfold litBlock at hclause ⊢; omega
      have hjs : l = clauseStep φ j := by
        show l = clauseStep φ (l - litBlock φ - 1).toNat; unfold clauseStep; unfold litBlock at hclause ⊢; omega
      have hc : φ.clauses[j]? = some φ.clauses[j] := List.getElem?_eq_getElem hjlt
      obtain ⟨⟨hv1, hv2, hv3⟩, _⟩ := hwf φ.clauses[j] (List.mem_of_getElem? hc)
      have hreq : ∀ x : NodeId, x.step = l → reqOfCnf φ x =
          [litReq φ.clauses[j].l1 (b1 x.index), litReq φ.clauses[j].l2 (b2 x.index),
            litReq φ.clauses[j].l3 (b3 x.index)] :=
        fun x hx => reqOfCnf_clause φ x j _ hjlt hc (by rw [hx]; exact hjs)
      have hlitStep : ∀ lt : Lit, lt.v < φ.nVars → 0 ≤ lt.step ∧ lt.step < litBlock φ :=
        fun lt hlt => litStep_bounds φ lt hlt
      have hbit : ∀ (lt : Lit) (f : Int → Int), lt.v < φ.nVars →
          litReq lt (f a.id.index) ∈ reqOfCnf φ a.id → litReq lt (f b.id.index) ∈ reqOfCnf φ b.id →
          f a.id.index = f b.id.index := by
        intro lt f hlt hia hib
        obtain ⟨hs0, hs1⟩ := hlitStep lt hlt
        have hlb := hclause.1
        have hsr : (litReq lt (f a.id.index)).step = lt.step := rfl
        have := req_agree φ S ad hok hsmp hrf ha hb (litReq lt (f a.id.index)) (litReq lt (f b.id.index))
          hia hib rfl (by rw [hsr]; exact hs0)
          (by rw [hsr, hcs]; unfold stepCount; unfold litBlock at hs1; omega)
          (by rw [hsr]; exact hpre _ hs0 (by omega))
        exact congrArg NodeId.index this
      have e1 := hbit φ.clauses[j].l1 b1 hv1 (by rw [hreq a.id hsa]; exact List.mem_cons_self) (by rw [hreq b.id hsb]; exact List.mem_cons_self)
      have e2 := hbit φ.clauses[j].l2 b2 hv2 (by rw [hreq a.id hsa]; exact List.mem_cons_of_mem _ List.mem_cons_self) (by rw [hreq b.id hsb]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have e3 := hbit φ.clauses[j].l3 b3 hv3 (by rw [hreq a.id hsa]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by rw [hreq b.id hsb]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      rw [mapNodes_clause φ j hjlt l hjs] at hma hmb
      have ra : 1 ≤ a.id.index ∧ a.id.index ≤ 7 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hma
        rcases hma with h | h | h | h | h | h | h <;> (rw [h]; dsimp only; exact ⟨by omega, by omega⟩)
      have rb : 1 ≤ b.id.index ∧ b.id.index ≤ 7 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmb
        rcases hmb with h | h | h | h | h | h | h <;> (rw [h]; dsimp only; exact ⟨by omega, by omega⟩)
      unfold b1 at e1
      unfold b2 at e2
      unfold b3 at e3
      exact nodeId_eq (by rw [hsa, hsb]) (by omega)
    · -- a fusion step: one map node
      have hc' : litBlock φ < l → fusionTop φ ≤ l := fun h => by
        have : ¬ (l < fusionTop φ) := fun h1 => hclause ⟨h, h1⟩
        clear hclause
        omega
      clear hclause
      have hcase : l ≤ litBlock φ ∨ fusionTop φ ≤ l := by
        by_cases hle : l ≤ litBlock φ
        · exact Or.inl hle
        · exact Or.inr (hc' (by clear hc'; omega))
      clear hc'
      have hone : mapNodes φ l = [⟨l, 0⟩] := by
        unfold mapNodes
        rw [if_neg (by omega), if_neg (by omega), if_neg hlit]
        rcases hcase with hle | hft
        · rw [if_pos hle]
        · by_cases hle : l ≤ litBlock φ
          · rw [if_pos hle]
          · rw [if_neg hle, if_pos hft]
      rw [hone] at hma hmb
      rw [List.mem_singleton.mp hma, List.mem_singleton.mp hmb]

-- ============================================================
-- The hypothesis, and pinning bottom-up
-- ============================================================

/-- **The hypothesis**: with the steps below `2v` decided and the state valid, pinning any live value of
variable `v` keeps it valid. -/
def LivePinUp (g₀ : GPathM) : Prop :=
  ∀ S, ReadFrom g₀ S → isValid S = true → ∀ v : Nat, v < φ.nVars →
    (∀ k, 0 ≤ k → k < 2 * (v : Int) → Decided S k) →
    ∀ a, Mem S a → a.id.step = 2 * (v : Int) → isValid (filterAllAgg S [a.id]) = true

/-- What the reader's starting state carries. -/
structure Base (g₀ : GPathM) : Prop where
  rf : RF g₀
  req : ReqFiltered (reqOfCnf φ) g₀
  map : NodesOnMap φ g₀
  cs : g₀.current_step = stepCount φ

theorem facts_of_readFrom {g₀ : GPathM} (hB : Base φ g₀) {S : GPathM} (hS : ReadFrom g₀ S) :
    RF S ∧ ReqFiltered (reqOfCnf φ) S ∧ NodesOnMap φ S ∧ S.current_step = stepCount φ := by
  obtain ⟨hrf, hpr⟩ := rf_readFrom hB.rf hS
  exact ⟨hrf, reqFiltered_of_pruned φ hpr hB.req, NodesOnMap_of_pruned φ hpr hB.map, hpr.step_eq.trans hB.cs⟩

/-- **One step up.** With the steps below `l` decided, step `l` admits a pin keeping the state valid:
a live value at a variable step (the hypothesis), the decided map node elsewhere (no hypothesis). -/
theorem step_up (hwf : WF φ) {g₀ : GPathM} (hB : Base φ g₀) (hL : LivePinUp φ g₀) {S : GPathM}
    (hS : ReadFrom g₀ S) (hv : isValid S = true) (l : Int) (hl0 : 0 ≤ l) (hl1 : l < stepCount φ)
    (hpre : ∀ k, 0 ≤ k → k < l → Decided S k) :
    ∃ m : NodeId, m.step = l ∧ isValid (filterAllAgg S [m]) = true := by
  obtain ⟨hrf, hreq, hmap, hcs⟩ := facts_of_readFrom φ hB hS
  have ad := adj_rf hrf hv
  obtain ⟨q, hq, hqs⟩ := gowner_of_isValid S hv l hl0 (by rw [hcs]; exact hl1)
  have hmq := mem_of_hasNode' S ad (ad.ctx.gn q hq)
  by_cases hvar : l < litBlock φ ∧ l % 2 = 0
  · have hvn : (l / 2).toNat < φ.nVars := by have := hvar.1; unfold litBlock at this; omega
    have h2 : 2 * (((l / 2).toNat : Nat) : Int) = l := by omega
    refine ⟨q.id, hqs, hL S hS hv _ hvn (fun k h0 h1 => hpre k h0 (by rw [h2] at h1; exact h1)) q hmq
      (by rw [h2]; exact hqs)⟩
  · have hdec := decided_off_var φ hwf S ad (aggOk_rf hrf hv) hrf.smp hreq hmap hcs l hl0 hl1 hvar hpre
    exact ⟨q.id, hqs, (pin_keeps_of_all S hrf hv q.id (fun p hp hps => hdec p q hp hmq (by rw [hps, hqs]) hqs)).1⟩

/-- **Pinning bottom-up never gets stuck**, under `LivePinUp`, and ends with every step decided. -/
theorem complete_up (hwf : WF φ) {g₀ : GPathM} (hB : Base φ g₀) (hL : LivePinUp φ g₀) :
    ∀ (n : Nat) (S : GPathM) (l : Int), ReadFrom g₀ S → isValid S = true → 0 ≤ l →
      l + (n : Int) = stepCount φ → (∀ k, 0 ≤ k → k < l → Decided S k) →
      ∃ F, ReadFrom g₀ F ∧ isValid F = true ∧ Pruned S F ∧ ∀ k, 0 ≤ k → k < stepCount φ → Decided F k := by
  intro n
  induction n with
  | zero =>
    intro S l hS hv _ hln hpre
    exact ⟨S, hS, hv, Pruned.refl S, fun k h0 h1 => hpre k h0 (by omega)⟩
  | succ n ih =>
    intro S l hS hv hl0 hln hpre
    obtain ⟨m, hms, hvm⟩ := step_up φ hwf hB hL hS hv l hl0 (by omega) hpre
    have hS1 : ReadFrom g₀ (filterAllAgg S [m]) := ReadFrom.pin S m hS hv
    have hrfS := (facts_of_readFrom φ hB hS).1
    have hrf1 := (facts_of_readFrom φ hB hS1).1
    have hpr := pruned_filterAllAgg S [m]
    have hnd := (RCtx_of_readableAgg S hrfS.readable).nodup
    obtain ⟨F, hF, hvF, hprF, hdec⟩ := ih (filterAllAgg S [m]) (l + 1) hS1 hvm (by omega) (by omega)
      (fun k h0 h1 => by
        by_cases hk : k < l
        · exact decided_of_pruned hpr hnd (hpre k h0 hk)
        · have : k = m.step := by omega
          rw [this]; exact decided_pin S m hrf1 hvm)
    exact ⟨F, hF, hvF, Pruned.trans hpr hprF, hdec⟩

/-- A state with every step decided, valid, from the reader: a path. -/
theorem chain_of_decided {g₀ : GPathM} (hB : Base φ g₀) {F : GPathM} (hF : ReadFrom g₀ F)
    (hv : isValid F = true) (hdec : ∀ k, 0 ≤ k → k < stepCount φ → Decided F k) : ∃ sel, ChainSound F sel := by
  obtain ⟨hrf, _, _, hcs⟩ := facts_of_readFrom φ hB hF
  have ad := adj_rf hrf hv
  have hpos : 0 < F.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ
  obtain ⟨q, hq, _⟩ := gowner_of_isValid F hv 0 (Int.le_refl _) hpos
  obtain ⟨sel, hsc, _⟩ := chain_of_ids F ad (aggOk_rf hrf hv) hrf.smp hv
    (fun a b ha hb hs => by
      obtain ⟨h0, h1⟩ := mem_bounds F ad ha
      exact hdec a.id.step h0 (by rw [← hcs]; exact h1) a b ha hb rfl hs.symm)
    (mem_of_hasNode' F ad (ad.ctx.gn q hq))
  exact ⟨sel, hsc⟩

/-- **Every valid state the reader reaches, with the steps below `l` decided, holds a path.** -/
theorem chain_up (hwf : WF φ) {g₀ : GPathM} (hB : Base φ g₀) (hL : LivePinUp φ g₀) {S : GPathM}
    (hS : ReadFrom g₀ S) (hv : isValid S = true) (l : Int) (hl0 : 0 ≤ l) (hl1 : l ≤ stepCount φ)
    (hpre : ∀ k, 0 ≤ k → k < l → Decided S k) : ∃ sel, ChainSound S sel := by
  obtain ⟨F, hF, hvF, hpr, hdec⟩ := complete_up φ hwf hB hL (stepCount φ - l).toNat S l hS hv hl0
    (by omega) hpre
  obtain ⟨sel, hsc⟩ := chain_of_decided φ hB hF hvF hdec
  have hrfS := (facts_of_readFrom φ hB hS).1
  exact ⟨sel, SubsetSemantics.ChainSound_of_pruned hpr (RCtx_of_readableAgg S hrfS.readable).nodup
    hrfS.smp sel hsc⟩

-- ============================================================
-- The verdict
-- ============================================================

def RunLivePinUp : Prop := ∀ kv ∈ pureRunW φ, LivePinUp φ (filterAllAgg kv.2 [])

theorem base_final (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) :
    Base φ (filterAllAgg kv.2 []) := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hpr := pruned_filterAllAgg kv.2 []
  exact ⟨rf_final φ hwf kv hkv, reqFiltered_of_pruned φ hpr hm.rf, NodesOnMap_of_pruned φ hpr hm.onMap,
    hpr.step_eq.trans hstep⟩

/-- **The Improves verdict under `LivePinUp` alone.** -/
theorem sat_of_up (hwf : WF φ) (hL : RunLivePinUp φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  obtain ⟨sel, hsc⟩ := chain_up φ hwf (base_final φ hwf kv hkv) (hL kv hkv) ReadFrom.start hv 0
    (Int.le_refl _) (by have := ConservationCore.stepCount_pos φ; omega) (fun k h0 h1 => absurd h1 (by omega))
  exact ⟨_, sat_decode φ hwf kv hkv sel
    (SubsetSemantics.ChainSound_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup hm.smp sel hsc)⟩

theorem verdict_iff_up (hwf : WF φ) (hL : RunLivePinUp φ) :
    (∃ kv ∈ pureRunW φ, isValid (filterAllAgg kv.2 []) = true) ↔ Satisfiable φ :=
  ⟨fun ⟨kv, hkv, hv⟩ => sat_of_up φ hwf hL kv hkv hv, fun h => CertificateSet.exists_valid_of_sat φ hwf h⟩

theorem answer_unsat_up (hwf : WF φ) (hL : RunLivePinUp φ) (hns : ¬ Satisfiable φ) :
    Answer.answer φ = .unsat := by
  unfold Answer.answer
  simp only
  have hall : ((pureRunW φ).map (fun kv => filterAllAgg kv.2 [])).all (fun g => !isValid g) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hg
    cases hv : isValid (filterAllAgg kv.2 []) with
    | false => rfl
    | true => exact absurd (sat_of_up φ hwf hL kv hkv hv) hns
  rw [if_pos hall]

-- ============================================================
-- The reader, under `LivePinUp`
-- ============================================================

/-- **The reader never gets stuck**, under `LivePinUp`, and what it reads is the value sequence of a path
of the state it started from. Its invariant: the steps below the next variable are decided. -/
theorem read_complete_up (hwf : WF φ) {g₀ : GPathM} (hB : Base φ g₀) (hL : LivePinUp φ g₀) :
    ∀ (n v : Nat) (g : GPathM), ReadFrom g₀ g → isValid g = true → v + n ≤ φ.nVars →
      (∀ k, 0 ≤ k → k < 2 * (v : Int) → Decided g k) →
      ∃ bs sel, Answer.readGreedy n v g = some bs ∧ ChainSound g sel ∧
        ∀ i : Nat, i < n → (sel (2 * ((v + i : Nat) : Int))).id.index = (if bs.getD i false then 1 else 0) := by
  intro n
  induction n with
  | zero =>
    intro v g hg hv hvn hpre
    obtain ⟨sel, hcs⟩ := chain_up φ hwf hB hL hg hv (2 * (v : Int)) (by omega)
      (by unfold stepCount; omega) hpre
    exact ⟨[], sel, rfl, hcs, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro v g hg hv hvn hpre
    obtain ⟨hrf, hreq, hmap, hcsg⟩ := facts_of_readFrom φ hB hg
    have rc := RCtx_of_readableAgg g hrf.readable
    have ad := adj_rf hrf hv
    have step : ∀ (b : Bool), isValid (filterAllAgg g [⟨2 * (v : Int), if b then 1 else 0⟩]) = true →
        ∃ bs sel, Answer.readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), if b then 1 else 0⟩]) = some bs ∧
          ChainSound g sel ∧ (sel (2 * (v : Int))).id.index = (if b then 1 else 0) ∧
          ∀ i : Nat, i < n → (sel (2 * ((v + 1 + i : Nat) : Int))).id.index = (if bs.getD i false then 1 else 0) := by
      intro b hvb
      let r : NodeId := ⟨2 * (v : Int), if b then 1 else 0⟩
      have hpr := pruned_filterAllAgg g [r]
      have hg1 : ReadFrom g₀ (filterAllAgg g [r]) := ReadFrom.pin g r hg hv
      obtain ⟨hrf1, hreq1, hmap1, hcs1⟩ := facts_of_readFrom φ hB hg1
      have ad1 := adj_rf hrf1 hvb
      -- the steps below the next variable are decided
      have hpre2 : ∀ k, 0 ≤ k → k < 2 * (v : Int) + 1 → Decided (filterAllAgg g [r]) k := by
        intro k h0 h1
        by_cases hk : k < 2 * (v : Int)
        · exact decided_of_pruned hpr rc.nodup (hpre k h0 hk)
        · have : k = r.step := by show k = 2 * (v : Int); omega
          rw [this]; exact decided_pin g r hrf1 hvb
      have hpre1 : ∀ k, 0 ≤ k → k < 2 * ((v + 1 : Nat) : Int) → Decided (filterAllAgg g [r]) k := by
        intro k h0 h1
        by_cases hk : k < 2 * (v : Int) + 1
        · exact hpre2 k h0 hk
        · have hk' : k = 2 * (v : Int) + 1 := by omega
          rw [hk']
          refine decided_off_var φ hwf _ ad1 (aggOk_rf hrf1 hvb) hrf1.smp hreq1 hmap1 hcs1 _ (by omega)
            (by unfold stepCount; omega) (fun h => ?_) hpre2
          have := h.2
          omega
      obtain ⟨bs, sel, hrd, hsc, hidx⟩ := ih (v + 1) (filterAllAgg g [r]) hg1 hvb (by omega) hpre1
      refine ⟨bs, sel, hrd, SubsetSemantics.ChainSound_of_pruned hpr rc.nodup hrf.smp sel hsc, ?_, hidx⟩
      have h0' : 0 ≤ 2 * (v : Int) := by omega
      have h1 : 2 * (v : Int) < (filterAllAgg g [r]).current_step := by rw [hcs1]; unfold stepCount; omega
      have hgow := hsc.chain.2.2 (2 * (v : Int)) h0' h1
      have hst := (hsc.chain.1.1 (2 * (v : Int)) h0' h1).2
      have := pin_id g r _ hgow hst
      rw [this]
    have finish : ∀ (b : Bool) (bs : List Bool) (sel : Int → PathNodeId),
        (sel (2 * (v : Int))).id.index = (if b then 1 else 0) →
        (∀ i : Nat, i < n → (sel (2 * ((v + 1 + i : Nat) : Int))).id.index = (if bs.getD i false then 1 else 0)) →
        ∀ i : Nat, i < n + 1 → (sel (2 * ((v + i : Nat) : Int))).id.index = (if (b :: bs).getD i false then 1 else 0) := by
      intro b bs sel hb hrest i hi
      cases i with
      | zero => simpa using hb
      | succ i =>
        have := hrest i (by omega)
        rw [show v + (i + 1) = v + 1 + i by omega]
        simpa using this
    simp only [Answer.readGreedy]
    by_cases hz : isValid (filterAllAgg g [⟨2 * (v : Int), 0⟩]) = true
    · rw [if_pos hz]
      obtain ⟨bs, sel, hrd, hsc, hb, hrest⟩ := step false hz
      have hrd' : Answer.readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), 0⟩]) = some bs := by simpa using hrd
      exact ⟨false :: bs, sel, by rw [hrd']; rfl, hsc, finish false bs sel hb hrest⟩
    · rw [if_neg hz]
      -- every live value keeps the state valid; a live value exists, and it is not value 0
      have hk0 : 0 ≤ 2 * (v : Int) := by omega
      have hk1 : 2 * (v : Int) < g.current_step := by rw [hcsg]; unfold stepCount; omega
      obtain ⟨q, hq, hqs⟩ := gowner_of_isValid g hv (2 * (v : Int)) hk0 hk1
      have hmq := mem_of_hasNode' g ad (ad.ctx.gn q hq)
      have hvq := hL g hg hv v (by omega) hpre q hmq hqs
      have hon := onMap_of_mem φ g hmap hmq
      rw [hqs] at hon
      have hlit : 2 * (v : Int) < litBlock φ := by unfold litBlock; omega
      rcases ReaderComplete.var_node φ (2 * (v : Int)) hk0 hlit q.id hon with h | h
      · rw [h] at hvq; exact absurd hvq hz
      · rw [h] at hvq
        rw [if_pos hvq]
        obtain ⟨bs, sel, hrd, hsc, hb, hrest⟩ := step true hvq
        have hrd' : Answer.readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), 1⟩]) = some bs := by simpa using hrd
        exact ⟨true :: bs, sel, by rw [hrd']; rfl, hsc, finish true bs sel hb hrest⟩

/-- **The machine always answers**, under `LivePinUp` alone. -/
theorem answer_ne_unknown_up (hwf : WF φ) (hL : RunLivePinUp φ) : Answer.answer φ ≠ .unknown := by
  unfold Answer.answer
  simp only
  split
  · intro h; cases h
  · next hall =>
    have hall' : ((pureRunW φ).map (fun kv => filterAllAgg kv.2 [])).all (fun g => !isValid g) = false := by
      cases hb : ((pureRunW φ).map (fun kv => filterAllAgg kv.2 [])).all (fun g => !isValid g) with
      | false => rfl
      | true => exact absurd hb hall
    obtain ⟨g, hg, hvg⟩ := ReaderComplete.exists_false_of_all_false _ _ hall'
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hg
    have hv : isValid (filterAllAgg kv.2 []) = true := by simpa using hvg
    obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
    have hpr := pruned_filterAllAgg kv.2 []
    obtain ⟨bs, sel, hrd, hsc, hidx⟩ := read_complete_up φ hwf (base_final φ hwf kv hkv) (hL kv hkv)
      φ.nVars 0 _ ReadFrom.start hv (by omega) (fun k h0 h1 => absurd h1 (by omega))
    have hsc' : ChainSound kv.2 sel := SubsetSemantics.ChainSound_of_pruned hpr hm.rctx.nodup hm.smp sel hsc
    have hmodel := sat_decode φ hwf kv hkv sel hsc'
    have hagree : ∀ v, v < φ.nVars → CnfChain.decode sel v = Answer.toAssign bs v := by
      intro v hv'
      have := hidx v hv'
      simp only [Nat.zero_add] at this
      simp only [CnfChain.decode, Answer.toAssign, this]
      cases bs.getD v false <;> rfl
    have hsat : satB (Answer.toAssign bs) φ = true :=
      (satB_iff _ φ).mpr (ReaderComplete.sat_congr φ hwf _ _ hagree hmodel)
    have hcert : Answer.certificate φ (filterAllAgg kv.2 []) = some (Answer.toAssign bs) := by
      unfold Answer.certificate
      rw [if_pos hv, hrd]
      simp only [Option.bind_some, hsat, if_true]
    split
    · intro h; cases h
    · next hnone =>
      have := ReaderComplete.none_of_findSome_none _ _ hnone _ hg
      rw [hcert] at this
      cases this

/-- info: 'AbsSat.GraphPath.Model.PinUp.answer_ne_unknown_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown_up

/-- info: 'AbsSat.GraphPath.Model.PinUp.decided_off_var' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decided_off_var

/-- info: 'AbsSat.GraphPath.Model.PinUp.verdict_iff_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdict_iff_up

/-- info: 'AbsSat.GraphPath.Model.PinUp.answer_unsat_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_unsat_up

end AbsSat.GraphPath.Model.PinUp
