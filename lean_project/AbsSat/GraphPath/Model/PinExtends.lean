-- lean_project/AbsSat/GraphPath/Model/PinExtends.lean
import AbsSat.GraphPath.Model.Greedy

/-!
# The reader's way: pin a step, review, go on — one local hypothesis

The greedy construction without reviews gets stuck (probe `greedy`, v144). The reader's own way reviews
after every choice: pin a map node at some step, review, go on. This module shows that this way needs
**one local hypothesis** and nothing else — no exactness, no `GhostsLine`:

* **`chain_of_ids`** (no hypothesis) — a valid reviewed state in which all the nodes of a step share the
  same map node **is a path**: at each step there is then a single node (its parent's map node is fixed
  too, through the parent link), the global owners form a clique, and a covering clique is a sound
  chain (`Greedy.chain_of_clique`).
* **`PinExtends g₀`** — the hypothesis: *in every valid state the reader reaches from `g₀`, every step
  admits a pin that keeps the state valid*.
* **`chain_of_readFrom`** — under it, every valid state the reader reaches holds a path: pin every step
  in turn, and the fully pinned valid state is a path (`chain_of_ids`).
* **`sat_of_pinExtends`**, **`verdict_iff_pinExtends`** — the Improves verdict under `PinExtends` alone.
* **`read_complete_px`**, **`answer_ne_unknown_px`**, **`answer_unsat_px`** — the reader never gets stuck,
  its certificate checks, and on an unsatisfiable formula the machine answers UNSAT: all under
  `PinExtends` alone.
-/

namespace AbsSat.GraphPath.Model.PinExtends

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup SMP_filterAllAgg)
open AbsSat.GraphPath.Model.AggFixpoint (AggOk aggOk_reviewAgg)
open AbsSat.GraphPath.Model.BranchCompat (pinOneByOne)
open AbsSat.GraphPath.Model.SupportSplit (mem_of_hasNode')
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.PickInduction (gowner_of_isValid)
open AbsSat.GraphPath.Model.Greedy (Clique chain_of_clique)
open AbsSat.GraphPath.Model.MapReachable (NodesOnMap NodesOnMap_of_pruned)
open AbsSat.GraphPath.Model.Answer (Answer readGreedy certificate answer)
open AbsSat.GraphPath.Model.ReaderComplete (pin_id var_node sat_decode sat_congr exists_false_of_all_false
  none_of_findSome_none)

-- ============================================================
-- One map node per step: the state is a path
-- ============================================================

theorem mem_gowner (R : GPathM) (ad : AdjacentOwners.Adj R) {a : PathNodeId} (ha : Mem R a) :
    a ∈ R.gowners := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨h0, h1⟩ := mem_bounds R ad ⟨m, hm⟩
  exact ad.ctx.ownGow a m hm a (ad.ctx.self a m hm) h0 h1

/-- Below the root, a node's parent map node is the map node of a node one step down. -/
theorem parent_of_mem (R : GPathM) (ad : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R)
    {a : PathNodeId} (ha : Mem R a) (hs : 0 < a.id.step) :
    ∃ v, Mem R v ∧ v.id.step = a.id.step - 1 ∧ a.parent_id = some v.id ∧
      a.gparent_id = v.parent_id := by
  have sup := sup_self R ad hok hsmp
  obtain ⟨m, hm⟩ := ha
  obtain ⟨_, h1⟩ := mem_bounds R ad ⟨m, hm⟩
  obtain ⟨v, hav, hvs⟩ := sup.cov a ⟨m, hm⟩ (a.id.step - 1) (by omega) (by omega)
  have hva := sup.sym a v hav
  have hp := sup.link a v m hav hva (by omega) hm
  have hpmp := ad.rc.pmp m (List.mem_of_find?_eq_some hm) v hp
  have hgpmp := ad.rc.gpmp.1 m (List.mem_of_find?_eq_some hm) v hp
  rw [node?_id_eq R a m hm] at hpmp hgpmp
  obtain ⟨_, _, _, hmv⟩ := hav
  exact ⟨v, hmv, hvs, hpmp.symm, hgpmp⟩

theorem root_of_mem (R : GPathM) (ad : AdjacentOwners.Adj R) {a : PathNodeId} (ha : Mem R a)
    (hz : a.id.step = 0) : a.parent_id = none := by
  obtain ⟨m, hm⟩ := ha
  have hid := node?_id_eq R a m hm
  have := ad.rc.rootz m (List.mem_of_find?_eq_some hm) (by rw [hid]; exact hz)
  rw [hid] at this
  exact this

/-- And a root records no grandparent either. -/
theorem groot_of_mem (R : GPathM) (ad : AdjacentOwners.Adj R) {a : PathNodeId} (ha : Mem R a)
    (hz : a.id.step = 0) : a.gparent_id = none := by
  obtain ⟨m, hm⟩ := ha
  have hid := node?_id_eq R a m hm
  have := ad.rc.gpmp.2 m (List.mem_of_find?_eq_some hm)
    (by rw [hid]; exact root_of_mem R ad ⟨m, hm⟩ hz)
  rw [hid] at this
  exact this

/-- Same map node at every step ⟹ same node at every step. -/
theorem eq_of_ids (R : GPathM) (ad : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R)
    (hid : ∀ a b, Mem R a → Mem R b → a.id.step = b.id.step → a.id = b.id) :
    ∀ a b, Mem R a → Mem R b → a.id.step = b.id.step → a = b := by
  intro a b ha hb hs
  have h1 := hid a b ha hb hs
  obtain ⟨h0a, _⟩ := mem_bounds R ad ha
  have h2 : a.parent_id = b.parent_id := by
    by_cases hz : a.id.step = 0
    · rw [root_of_mem R ad ha hz, root_of_mem R ad hb (by omega)]
    · obtain ⟨v, hv, hvs, hpa, _⟩ := parent_of_mem R ad hok hsmp ha (by omega)
      obtain ⟨w, hw, hws, hpb, _⟩ := parent_of_mem R ad hok hsmp hb (by omega)
      rw [hpa, hpb, hid v w hv hw (by omega)]
  -- the third component: the parents' own `parent_id`, and they agree one step lower
  have h3 : a.gparent_id = b.gparent_id := by
    by_cases hz : a.id.step = 0
    · rw [groot_of_mem R ad ha hz, groot_of_mem R ad hb (by omega)]
    · obtain ⟨v, hv, hvs, _, hga⟩ := parent_of_mem R ad hok hsmp ha (by omega)
      obtain ⟨w, hw, hws, _, hgb⟩ := parent_of_mem R ad hok hsmp hb (by omega)
      rw [hga, hgb]
      by_cases hz1 : v.id.step = 0
      · rw [root_of_mem R ad hv hz1, root_of_mem R ad hw (by omega)]
      · obtain ⟨x, hx, hxs, hpx, _⟩ := parent_of_mem R ad hok hsmp hv (by omega)
        obtain ⟨y, hy, hys, hpy, _⟩ := parent_of_mem R ad hok hsmp hw (by omega)
        rw [hpx, hpy, hid x y hx hy (by omega)]
  cases a
  cases b
  simp only [PathNodeId.mk.injEq]
  exact ⟨h1, h2, h3⟩

/-- **One map node per step: the state is a path.** A valid reviewed state whose nodes at each step
share their map node holds a sound chain through all of its nodes. No hypothesis. -/
theorem chain_of_ids (R : GPathM) (ad : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R)
    (hv : isValid R = true) (hid : ∀ a b, Mem R a → Mem R b → a.id.step = b.id.step → a.id = b.id)
    {p : PathNodeId} (hp : Mem R p) : ∃ sel, ChainSound R sel ∧ ∀ a, Mem R a → sel a.id.step = a := by
  have sup := sup_self R ad hok hsmp
  have huniq := eq_of_ids R ad hok hsmp hid
  obtain ⟨h0, h1⟩ := mem_bounds R ad hp
  have hc : Clique R R.gowners := by
    refine ⟨fun a ha b hb => ?_, fun a ha b hb hs =>
      huniq a b (mem_of_hasNode' R ad (ad.ctx.gn a ha)) (mem_of_hasNode' R ad (ad.ctx.gn b hb)) hs⟩
    have hma := mem_of_hasNode' R ad (ad.ctx.gn a ha)
    have hmb := mem_of_hasNode' R ad (ad.ctx.gn b hb)
    obtain ⟨hb0, hb1⟩ := mem_bounds R ad hmb
    obtain ⟨v, hav, hvs⟩ := sup.cov a hma b.id.step hb0 hb1
    obtain ⟨m, hm, hin, hmv⟩ := hav
    rw [huniq v b hmv hmb hvs] at hin
    exact ⟨m, hm, hin, hmb⟩
  obtain ⟨sel, hsc, hsel⟩ := chain_of_clique R ad hok hsmp (by omega) R.gowners p hc
    (fun k h0 h1 => gowner_of_isValid R hv k h0 h1)
  exact ⟨sel, hsc, fun a ha => hsel a (mem_gowner R ad ha)⟩

-- ============================================================
-- The reader's states
-- ============================================================

/-- What the reader's states carry. -/
structure RF (S : GPathM) : Prop where
  readable : ReadableAgg S
  smp : Sons.SMP S
  pms : Sons.PMS S
  sn : Sons.SN S

theorem rf_pin (S : GPathM) (h : RF S) (m : NodeId) : RF (filterAllAgg S [m]) :=
  ⟨ReadableAgg_filterAllAgg S h.readable [m],
    SMP_filterAllAgg S h.smp (RCtx_of_readableAgg S h.readable).shape.notroot [m],
    AggInvariants.PMS_filterAllAgg S [m] h.pms, AggInvariants.SN_filterAllAgg S [m] h.sn⟩

theorem rf_readFrom {g₀ : GPathM} (h0 : RF g₀) {S : GPathM} (hS : ReadFrom g₀ S) : RF S ∧ Pruned g₀ S := by
  induction hS with
  | start => exact ⟨h0, Pruned.refl _⟩
  | pin g mid _ _ ih => exact ⟨rf_pin g ih.1 mid, Pruned.trans ih.2 (pruned_filterAllAgg g [mid])⟩

theorem adj_rf {S : GPathM} (h : RF S) (hv : isValid S = true) : AdjacentOwners.Adj S :=
  AdjacentOwners.adj_of_readable S h.readable hv h.pms h.sn

theorem aggOk_rf {S : GPathM} (h : RF S) (hv : isValid S = true) : AggOk S := by
  obtain ⟨g₀, rq, _, heq⟩ := h.readable
  rw [heq] at hv ⊢
  exact aggOk_reviewAgg _ hv

-- ============================================================
-- The hypothesis, and pinning every step
-- ============================================================

/-- **The local hypothesis**: in every valid state the reader reaches from `g₀`, every step admits a pin
that keeps the state valid. -/
def PinExtends (g₀ : GPathM) : Prop :=
  ∀ S, ReadFrom g₀ S → isValid S = true → ∀ l, 0 ≤ l → l < S.current_step →
    ∃ m : NodeId, m.step = l ∧ isValid (filterAllAgg S [m]) = true

/-- Under the hypothesis, the reader pins any list of steps and stays valid. -/
theorem complete_pins {g₀ : GPathM} (hX : PinExtends g₀) : ∀ (steps : List Int) (S : GPathM),
    ReadFrom g₀ S → isValid S = true → (∀ l ∈ steps, 0 ≤ l ∧ l < S.current_step) →
    ∃ P, ReadFrom g₀ (pinOneByOne S P) ∧ isValid (pinOneByOne S P) = true ∧ ∀ l ∈ steps, ∃ r ∈ P, r.step = l
  | [], S, hS, hv, _ => ⟨[], hS, hv, fun _ h => absurd h List.not_mem_nil⟩
  | l :: rest, S, hS, hv, hr => by
    obtain ⟨m, hms, hvm⟩ := hX S hS hv l (hr l List.mem_cons_self).1 (hr l List.mem_cons_self).2
    have hcs := (pruned_filterAllAgg S [m]).step_eq
    obtain ⟨P, h1, h2, h3⟩ := complete_pins hX rest _ (ReadFrom.pin S m hS hv) hvm
      (fun l' hl' => by rw [hcs]; exact hr l' (List.mem_cons_of_mem _ hl'))
    refine ⟨m :: P, h1, h2, fun l' hl' => ?_⟩
    rcases List.mem_cons.mp hl' with rfl | hl''
    · exact ⟨m, List.mem_cons_self, hms⟩
    · obtain ⟨r, hr', hrs⟩ := h3 l' hl''
      exact ⟨r, List.mem_cons_of_mem _ hr', hrs⟩

/-- **Every valid state the reader reaches holds a path**, under `PinExtends`: pin every step, and the
fully pinned valid state is a path. -/
theorem chain_of_readFrom {g₀ : GPathM} (hX : PinExtends g₀) (h0 : RF g₀) {S : GPathM}
    (hS : ReadFrom g₀ S) (hv : isValid S = true) (hpos : 0 < S.current_step) : ∃ sel, ChainSound S sel := by
  let steps : List Int := (List.range S.current_step.toNat).map (fun (i : Nat) => (i : Int))
  have hsteps : ∀ l, 0 ≤ l → l < S.current_step → l ∈ steps := by
    intro l h0 h1
    exact List.mem_map.mpr ⟨l.toNat, List.mem_range.mpr (by omega), by omega⟩
  obtain ⟨P, hF, hvF, hcov⟩ := complete_pins hX steps S hS hv (fun l hl => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    have := List.mem_range.mp hi
    exact ⟨by omega, by omega⟩)
  have hrf := (rf_readFrom h0 hF).1
  have ad := adj_rf hrf hvF
  have hprS := SeqPin.pruned_pinOneByOne P S
  have hcsF := hprS.step_eq
  have hid : ∀ a b, Mem (pinOneByOne S P) a → Mem (pinOneByOne S P) b → a.id.step = b.id.step →
      a.id = b.id := by
    intro a b ha hb hs
    obtain ⟨h0, h1⟩ := mem_bounds _ ad ha
    obtain ⟨r, hr, hrs⟩ := hcov a.id.step (hsteps _ h0 (by rw [← hcsF]; exact h1))
    rw [OraclePath.pinned_ids P S r hr a (mem_gowner _ ad ha) hrs.symm,
      OraclePath.pinned_ids P S r hr b (mem_gowner _ ad hb) (by rw [← hs]; exact hrs.symm)]
  obtain ⟨q, hq, _⟩ := gowner_of_isValid _ hvF 0 (Int.le_refl _) (by rw [hcsF]; exact hpos)
  obtain ⟨sel, hsc, _⟩ := chain_of_ids _ ad (aggOk_rf hrf hvF) hrf.smp hvF hid
    (mem_of_hasNode' _ ad (ad.ctx.gn q hq))
  have hrfS := (rf_readFrom h0 hS).1
  exact ⟨sel, SubsetSemantics.ChainSound_of_pruned hprS (RCtx_of_readableAgg S hrfS.readable).nodup
    hrfS.smp sel hsc⟩

-- ============================================================
-- The verdict
-- ============================================================

variable (φ : Cnf)

/-- The hypothesis for the machine: from every reader's state of the last line. -/
def RunPinExtends : Prop := ∀ kv ∈ pureRunW φ, PinExtends (filterAllAgg kv.2 [])

theorem rf_final (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) :
    RF (filterAllAgg kv.2 []) := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  exact ⟨⟨kv.2, [], hm.rctx, rfl⟩, SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot [],
    AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms, AggInvariants.SN_filterAllAgg kv.2 [] hm.sn⟩

/-- **The Improves verdict under `PinExtends` alone.** -/
theorem sat_of_pinExtends (hwf : WF φ) (hX : RunPinExtends φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hpr := pruned_filterAllAgg kv.2 []
  have hpos : 0 < (filterAllAgg kv.2 []).current_step := by
    rw [hpr.step_eq, hstep]; exact ConservationCore.stepCount_pos φ
  obtain ⟨sel, hsc⟩ := chain_of_readFrom (hX kv hkv) (rf_final φ hwf kv hkv) ReadFrom.start hv hpos
  exact ⟨_, sat_decode φ hwf kv hkv sel (SubsetSemantics.ChainSound_of_pruned hpr hm.rctx.nodup hm.smp sel hsc)⟩

/-- **The machine decides, under `PinExtends` alone.** -/
theorem verdict_iff_pinExtends (hwf : WF φ) (hX : RunPinExtends φ) :
    (∃ kv ∈ pureRunW φ, isValid (filterAllAgg kv.2 []) = true) ↔ Satisfiable φ :=
  ⟨fun ⟨kv, hkv, hv⟩ => sat_of_pinExtends φ hwf hX kv hkv hv,
   fun h => CertificateSet.exists_valid_of_sat φ hwf h⟩

-- ============================================================
-- The reader, under the local hypothesis
-- ============================================================

/-- **The reader never gets stuck**, under `PinExtends`, and what it reads is the value sequence of a
path of the state it started from. -/
theorem read_complete_px {g₀ : GPathM} (hX : PinExtends g₀) (h0 : RF g₀) (hmap0 : NodesOnMap φ g₀) :
    ∀ (n v : Nat) (g : GPathM), ReadFrom g₀ g → isValid g = true →
      v + n ≤ φ.nVars → 2 * ((v + n : Nat) : Int) ≤ g.current_step → 0 < g.current_step →
      ∃ bs sel, readGreedy n v g = some bs ∧ ChainSound g sel ∧
        ∀ i : Nat, i < n → (sel (2 * ((v + i : Nat) : Int))).id.index = (if bs.getD i false then 1 else 0) := by
  intro n
  induction n with
  | zero =>
    intro v g hg hv _ _ hpos
    obtain ⟨sel, hcs⟩ := chain_of_readFrom hX h0 hg hv hpos
    exact ⟨[], sel, rfl, hcs, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro v g hg hv hvn hcs hpos
    obtain ⟨hrf, hpr0⟩ := rf_readFrom h0 hg
    have rc := RCtx_of_readableAgg g hrf.readable
    have hmap : NodesOnMap φ g := NodesOnMap_of_pruned φ hpr0 hmap0
    have step : ∀ (b : Bool), isValid (filterAllAgg g [⟨2 * (v : Int), if b then 1 else 0⟩]) = true →
        ∃ bs sel, readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), if b then 1 else 0⟩]) = some bs ∧
          ChainSound g sel ∧ (sel (2 * (v : Int))).id.index = (if b then 1 else 0) ∧
          ∀ i : Nat, i < n → (sel (2 * ((v + 1 + i : Nat) : Int))).id.index = (if bs.getD i false then 1 else 0) := by
      intro b hvb
      let r : NodeId := ⟨2 * (v : Int), if b then 1 else 0⟩
      have hpr := pruned_filterAllAgg g [r]
      obtain ⟨bs, sel, hrd, hsc, hidx⟩ := ih (v + 1) (filterAllAgg g [r]) (ReadFrom.pin g r hg hv) hvb
        (by omega) (by rw [hpr.step_eq]; omega) (by rw [hpr.step_eq]; exact hpos)
      refine ⟨bs, sel, hrd, SubsetSemantics.ChainSound_of_pruned hpr rc.nodup hrf.smp sel hsc, ?_, hidx⟩
      have h0' : 0 ≤ 2 * (v : Int) := by omega
      have h1 : 2 * (v : Int) < (filterAllAgg g [r]).current_step := by rw [hpr.step_eq]; omega
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
    simp only [readGreedy]
    by_cases hz : isValid (filterAllAgg g [⟨2 * (v : Int), 0⟩]) = true
    · rw [if_pos hz]
      obtain ⟨bs, sel, hrd, hsc, hb, hrest⟩ := step false hz
      have hrd' : readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), 0⟩]) = some bs := by simpa using hrd
      exact ⟨false :: bs, sel, by rw [hrd']; rfl, hsc, finish false bs sel hb hrest⟩
    · rw [if_neg hz]
      -- some pin keeps the state valid at this step; it is a value node, and not value 0
      have hk0 : 0 ≤ 2 * (v : Int) := by omega
      have hk1 : 2 * (v : Int) < g.current_step := by omega
      obtain ⟨m, hms, hvm⟩ := hX g hg hv (2 * (v : Int)) hk0 hk1
      have hprm := pruned_filterAllAgg g [m]
      obtain ⟨q, hq, hqs⟩ := gowner_of_isValid _ hvm (2 * (v : Int)) hk0 (by rw [hprm.step_eq]; exact hk1)
      have hqm : q.id = m := pin_id g m q hq (by rw [hqs, hms])
      obtain ⟨nd, hnd, hndid⟩ := rc.gn q (hprm.gowners_sub q hq)
      have hon := hmap nd hnd
      rw [hndid, hqs, hqm] at hon
      have hlit : 2 * (v : Int) < litBlock φ := by unfold litBlock; omega
      rcases var_node φ (2 * (v : Int)) hk0 hlit m hon with h | h
      · rw [h] at hvm; exact absurd hvm hz
      · rw [h] at hvm
        rw [if_pos hvm]
        obtain ⟨bs, sel, hrd, hsc, hb, hrest⟩ := step true hvm
        have hrd' : readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), 1⟩]) = some bs := by simpa using hrd
        exact ⟨true :: bs, sel, by rw [hrd']; rfl, hsc, finish true bs sel hb hrest⟩

-- ============================================================
-- The answer
-- ============================================================

/-- **The machine always answers**, under `PinExtends` alone. -/
theorem answer_ne_unknown_px (hwf : WF φ) (hX : RunPinExtends φ) : answer φ ≠ .unknown := by
  unfold answer
  simp only
  split
  · intro h; cases h
  · next hall =>
    have hall' : ((pureRunW φ).map (fun kv => filterAllAgg kv.2 [])).all (fun g => !isValid g) = false := by
      cases hb : ((pureRunW φ).map (fun kv => filterAllAgg kv.2 [])).all (fun g => !isValid g) with
      | false => rfl
      | true => exact absurd hb hall
    obtain ⟨g, hg, hvg⟩ := exists_false_of_all_false _ _ hall'
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hg
    have hv : isValid (filterAllAgg kv.2 []) = true := by simpa using hvg
    obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
    have hpos := ConservationCore.stepCount_pos φ
    have hpr := pruned_filterAllAgg kv.2 []
    have hcsG : (filterAllAgg kv.2 []).current_step = stepCount φ := by rw [hpr.step_eq, hstep]
    obtain ⟨bs, sel, hrd, hsc, hidx⟩ := read_complete_px φ (hX kv hkv) (rf_final φ hwf kv hkv)
      (NodesOnMap_of_pruned φ hpr hm.onMap) φ.nVars 0 _ ReadFrom.start hv
      (by omega) (by rw [hcsG]; unfold stepCount; omega) (by rw [hcsG]; exact hpos)
    have hsc' : ChainSound kv.2 sel := SubsetSemantics.ChainSound_of_pruned hpr hm.rctx.nodup hm.smp sel hsc
    have hmodel := sat_decode φ hwf kv hkv sel hsc'
    have hagree : ∀ v, v < φ.nVars → CnfChain.decode sel v = Answer.toAssign bs v := by
      intro v hv'
      have := hidx v hv'
      simp only [Nat.zero_add] at this
      simp only [CnfChain.decode, Answer.toAssign, this]
      cases bs.getD v false <;> rfl
    have hsat : satB (Answer.toAssign bs) φ = true :=
      (satB_iff _ φ).mpr (sat_congr φ hwf _ _ hagree hmodel)
    have hcert : certificate φ (filterAllAgg kv.2 []) = some (Answer.toAssign bs) := by
      unfold certificate
      rw [if_pos hv, hrd]
      simp only [Option.bind_some, hsat, if_true]
    split
    · intro h; cases h
    · next hnone =>
      have := none_of_findSome_none _ _ hnone _ hg
      rw [hcert] at this
      cases this

/-- **On an unsatisfiable formula the machine answers UNSAT**, under `PinExtends` alone. -/
theorem answer_unsat_px (hwf : WF φ) (hX : RunPinExtends φ) (hns : ¬ Satisfiable φ) :
    answer φ = .unsat := by
  unfold answer
  simp only
  have hall : ((pureRunW φ).map (fun kv => filterAllAgg kv.2 [])).all (fun g => !isValid g) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hg
    cases hv : isValid (filterAllAgg kv.2 []) with
    | false => rfl
    | true => exact absurd (sat_of_pinExtends φ hwf hX kv hkv hv) hns
  rw [if_pos hall]

/-- info: 'AbsSat.GraphPath.Model.PinExtends.chain_of_ids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_of_ids

/-- info: 'AbsSat.GraphPath.Model.PinExtends.verdict_iff_pinExtends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdict_iff_pinExtends

/-- info: 'AbsSat.GraphPath.Model.PinExtends.answer_ne_unknown_px' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown_px

/-- info: 'AbsSat.GraphPath.Model.PinExtends.answer_unsat_px' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_unsat_px

end AbsSat.GraphPath.Model.PinExtends
