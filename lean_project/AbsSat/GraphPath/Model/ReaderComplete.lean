-- lean_project/AbsSat/GraphPath/Model/ReaderComplete.lean
import AbsSat.GraphPath.Model.Answer
import AbsSat.GraphPath.Model.OraclePath

/-!
# The reader never gets stuck: the machine always answers

`Answer.lean` proves that every answer the machine gives is correct, with no hypothesis; the only
possible imperfection is answering *unknown*. This module shows, by induction over the variables the
reader pins, that it never happens:

* the invariant: **the reader's current state is valid and exact** (its tables are slices);
* a valid exact state holds a whole path (`exact_chain`); that path takes value `0` or `1` at the next
  variable, so one of the two pins keeps it (`ChainSound_filterAllAgg`) and the state stays valid — the
  reader is never stuck;
* at the end, the path the last state holds passes through every value read, so the assignment read is
  the path's decoding, which is a model: the certificate checks.

The step keeps exactness under one hypothesis, of the same kind as the declared one (`GhostsLine`) and
measured with no exception (probe `helly pinexact`: 21,709 arbitrary pins):

* **`ReaderPinExact`** — pinning one map node on a valid exact reader's state and reviewing keeps it
  exact.

Result:

* **`answer_ne_unknown`** — under `GhostsLine` and `ReaderPinExact`, the machine never answers
  *unknown*: it answers UNSAT or SAT with a checked certificate (and both are correct with no
  hypothesis, `Answer.lean`).
-/

namespace AbsSat.GraphPath.Model.ReaderComplete

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv)
open AbsSat.GraphPath.Model.Answer (Answer readGreedy certificate answer)
open AbsSat.GraphPath.Model.Exactness (TablesSound)
open AbsSat.GraphPath.Model.RoundInvariant (GhostsLine filterSlices_of_ghosts)
open AbsSat.GraphPath.Model.SliceInvariant (run_slices)
open AbsSat.GraphPath.Model.MapReachable (NodesOnMap NodesOnMap_of_pruned ChainOnMap chainOnMap_of_nodesOnMap)
open AbsSat.GraphPath.Model.PickInduction (gowner_of_isValid)

variable (φ : Cnf)

/-- **The step hypothesis**: pinning one map node on a valid exact reader's state and reviewing keeps
it exact. -/
def ReaderPinExact : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → TablesSound g →
    ∀ r : NodeId, isValid (filterAllAgg g [r]) = true → TablesSound (filterAllAgg g [r])

-- ============================================================
-- A valid exact state holds a whole path
-- ============================================================

theorem exact_chain (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true) (ht : TablesSound g)
    (hpos : 0 < g.current_step) : ∃ sel, ChainSound g sel := by
  have rc := RCtx_of_readableAgg g hR
  have ctx := Reader.Ctx_of_readable g (readable_of_readableAgg g hR) hv
  obtain ⟨q, hq, hq0⟩ := gowner_of_isValid g hv 0 (Int.le_refl _) hpos
  obtain ⟨m, hmm, hmid⟩ := rc.gn q hq
  have hqm : g.node? q = some m := by rw [← hmid]; exact node?_of_mem rc.nodup m hmm
  obtain ⟨sel, hcs, _, _⟩ := ht q m hqm (by omega) (by omega) q (by omega) (by omega) (ctx.self q m hqm)
  exact ⟨sel, hcs⟩

/-- A global owner at a pinned step carries the pin. -/
theorem pin_id (g : GPathM) (r : NodeId) (q : PathNodeId) (hq : q ∈ (filterAllAgg g [r]).gowners)
    (hs : q.id.step = r.step) : q.id = r :=
  OraclePath.pinned_ids [r] g r List.mem_cons_self q hq hs

/-- The map nodes of a variable step are its two values. -/
theorem var_node (k : Int) (hk0 : 0 ≤ k) (hk : k < litBlock φ) (d : NodeId) (h : d ∈ mapNodes φ k) :
    d = ⟨k, 0⟩ ∨ d = ⟨k, 1⟩ := by
  unfold mapNodes at h
  rw [if_neg (by omega)] at h
  split at h
  · exact absurd h List.not_mem_nil
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact h

-- ============================================================
-- The reader, by induction on the variables
-- ============================================================

/-- **The reader never gets stuck**, and what it reads is the value sequence of a path of the state it
started from. -/
theorem read_complete (hPE : ReaderPinExact) :
    ∀ (n v : Nat) (g : GPathM), ReadableAgg g → isValid g = true → TablesSound g → NodesOnMap φ g →
      Sons.SMP g → v + n ≤ φ.nVars → 2 * ((v + n : Nat) : Int) ≤ g.current_step → 0 < g.current_step →
      ∃ bs sel, readGreedy n v g = some bs ∧ ChainSound g sel ∧
        ∀ i : Nat, i < n → (sel (2 * ((v + i : Nat) : Int))).id.index = (if bs.getD i false then 1 else 0) := by
  intro n
  induction n with
  | zero =>
    intro v g hR hv ht _ _ _ _ hpos
    obtain ⟨sel, hcs⟩ := exact_chain g hR hv ht hpos
    exact ⟨[], sel, rfl, hcs, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro v g hR hv ht hmap hsmp hvn hcs hpos
    have rc := RCtx_of_readableAgg g hR
    -- one pinned value: the recursive call and what it gives back
    have step : ∀ (b : Bool), isValid (filterAllAgg g [⟨2 * (v : Int), if b then 1 else 0⟩]) = true →
        ∃ bs sel, readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), if b then 1 else 0⟩]) = some bs ∧
          ChainSound g sel ∧ (sel (2 * (v : Int))).id.index = (if b then 1 else 0) ∧
          ∀ i : Nat, i < n → (sel (2 * ((v + 1 + i : Nat) : Int))).id.index = (if bs.getD i false then 1 else 0) := by
      intro b hvb
      let r : NodeId := ⟨2 * (v : Int), if b then 1 else 0⟩
      have hpr := pruned_filterAllAgg g [r]
      obtain ⟨bs, sel, hrd, hsc, hidx⟩ := ih (v + 1) (filterAllAgg g [r])
        (ReadableAgg_filterAllAgg g hR [r]) hvb (hPE g hR hv ht r hvb)
        (NodesOnMap_of_pruned φ hpr hmap) (AnchoredSurvive.SMP_filterAllAgg g hsmp rc.shape.notroot [r])
        (by omega) (by rw [hpr.step_eq]; omega) (by rw [hpr.step_eq]; exact hpos)
      refine ⟨bs, sel, hrd, SubsetSemantics.ChainSound_of_pruned hpr rc.nodup hsmp sel hsc, ?_, hidx⟩
      -- the path's node at the pinned step is a global owner there, so it carries the pin
      have h0 : 0 ≤ 2 * (v : Int) := by omega
      have h1 : 2 * (v : Int) < (filterAllAgg g [r]).current_step := by rw [hpr.step_eq]; omega
      have hgow := hsc.chain.2.2 (2 * (v : Int)) h0 h1
      have hst := (hsc.chain.1.1 (2 * (v : Int)) h0 h1).2
      have := pin_id g r _ hgow hst
      rw [this]
    have finish : ∀ (b : Bool) (bs : List Bool) (sel : Int → PathNodeId),
        ChainSound g sel → (sel (2 * (v : Int))).id.index = (if b then 1 else 0) →
        (∀ i : Nat, i < n → (sel (2 * ((v + 1 + i : Nat) : Int))).id.index = (if bs.getD i false then 1 else 0)) →
        ∀ i : Nat, i < n + 1 → (sel (2 * ((v + i : Nat) : Int))).id.index = (if (b :: bs).getD i false then 1 else 0) := by
      intro b bs sel _ hb hrest i hi
      cases i with
      | zero => simpa using hb
      | succ i =>
        have := hrest i (by omega)
        rw [show v + (i + 1) = v + 1 + i by omega]
        simpa using this
    simp only [readGreedy]
    by_cases h0 : isValid (filterAllAgg g [⟨2 * (v : Int), 0⟩]) = true
    · rw [if_pos h0]
      obtain ⟨bs, sel, hrd, hsc, hb, hrest⟩ := step false h0
      have hrd' : readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), 0⟩]) = some bs := by simpa using hrd
      refine ⟨false :: bs, sel, by rw [hrd']; rfl, hsc, finish false bs sel hsc hb hrest⟩
    · rw [if_neg h0]
      -- the state holds a path; it cannot take value 0 here, so it takes value 1
      obtain ⟨sel0, hsc0⟩ := exact_chain g hR hv ht hpos
      have hk0 : 0 ≤ 2 * (v : Int) := by omega
      have hk1 : 2 * (v : Int) < g.current_step := by omega
      obtain ⟨hsome, hst⟩ := hsc0.chain.1.1 (2 * (v : Int)) hk0 hk1
      obtain ⟨nd, hnd⟩ := Option.isSome_iff_exists.mp hsome
      have hndm := List.mem_of_find?_eq_some hnd
      have hid := node?_id_eq g _ nd hnd
      have hon := hmap nd hndm
      rw [hid, hst] at hon
      have hlit : 2 * (v : Int) < litBlock φ := by unfold litBlock; omega
      have hvalid : ∀ r : NodeId, (sel0 (2 * (v : Int))).id = r → isValid (filterAllAgg g [r]) = true := by
        intro r hr
        have hc := ChainSound_filterAllAgg g [r] sel0 hsc0 (fun req hreq _ _ => by
          rw [List.mem_singleton.mp hreq]
          have : req.step = 2 * (v : Int) := by rw [List.mem_singleton.mp hreq, ← hr, hst]
          rw [← hr]
          rw [List.mem_singleton.mp hreq] at this
          rw [← hr] at this
          rw [this])
        exact EmptinessReduction.isValid_of_denotS _ _ ⟨sel0, hc, rfl⟩
      rcases var_node φ (2 * (v : Int)) hk0 hlit _ hon with h | h
      · exact absurd (hvalid _ h) h0
      · have h1 := hvalid _ h
        rw [if_pos h1]
        obtain ⟨bs, sel, hrd, hsc, hb, hrest⟩ := step true h1
        have hrd' : readGreedy n (v + 1) (filterAllAgg g [⟨2 * (v : Int), 1⟩]) = some bs := by simpa using hrd
        refine ⟨true :: bs, sel, by rw [hrd']; rfl, hsc, finish true bs sel hsc hb hrest⟩

-- ============================================================
-- The certificate checks
-- ============================================================

/-- A chain of a state of the last line decodes to a model. -/
theorem sat_decode (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (sel : Int → PathNodeId)
    (hsc : ChainSound kv.2 sel) : Sat (CnfChain.decode sel) φ := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  obtain ⟨hchain, howned, _⟩ := hsc.chain
  have hrs := ReaderAggRun.reqSatisfying_of_MInv φ kv.2 hm sel hchain howned
  have hcm : ChainOnMap φ kv.2 sel := chainOnMap_of_nodesOnMap φ kv.2 hm.onMap sel hchain
  refine PartialPaths.sat_of_satUpTo_final φ _ ?_
  intro j c hj hle
  have hjlt : j < φ.clauses.length := by
    rcases Nat.lt_or_ge j φ.clauses.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  exact PrefixDecode.satClause_of_reqSat_prefix φ kv.2 sel hwf hchain hrs hcm j hjlt c hj
    (by rw [hstep]; omega)

/-- Two assignments that agree on the variables of `φ` satisfy it alike. -/
theorem sat_congr (hwf : WF φ) (a b : Assign) (hab : ∀ v, v < φ.nVars → a v = b v) (h : Sat a φ) :
    Sat b φ := by
  intro c hc
  have hw := (hwf c hc).1
  have hl : ∀ l : Lit, l.v < φ.nVars → litVal a l = litVal b l := by
    intro l hlv
    simp only [litVal, hab l.v hlv]
  have := h c hc
  unfold SatClause at this ⊢
  rw [← hl c.l1 hw.1, ← hl c.l2 hw.2.1, ← hl c.l3 hw.2.2]
  exact this

-- ============================================================
-- The machine always answers
-- ============================================================

theorem exists_false_of_all_false {α : Type} (p : α → Bool) :
    ∀ l : List α, l.all p = false → ∃ x ∈ l, p x = false := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases hx : p x with
    | false => exact ⟨x, List.mem_cons_self, hx⟩
    | true =>
      simp only [List.all_cons, hx, Bool.true_and] at h
      obtain ⟨y, hy, hpy⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hpy⟩

theorem none_of_findSome_none {α β : Type} (f : α → Option β) :
    ∀ l : List α, l.findSome? f = none → ∀ x ∈ l, f x = none := by
  intro l
  induction l with
  | nil => intro _ x hx; exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    intro h x hx
    simp only [List.findSome?_cons] at h
    cases hy : f y with
    | some b => rw [hy] at h; cases h
    | none =>
      rw [hy] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hy
      · exact ih h x hx'

/-- **The machine always answers**: under `GhostsLine` and `ReaderPinExact`, it never says *unknown*. -/
theorem answer_ne_unknown (hwf : WF φ) (hG : GhostsLine φ) (hPE : ReaderPinExact) :
    answer φ ≠ .unknown := by
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
    -- the reader's state of `kv` has a checked certificate
    obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
    have hpos := ConservationCore.stepCount_pos φ
    have hl := ReaderAggRun.LineInv_steps φ hwf (stepCount φ - 1).toNat 0 (PureDriver.pureInit φ)
      (ReaderAggRun.LineInv_init φ hwf)
    have hcast : (0 : Int) + (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
    rw [hcast] at hl
    have ht : TablesSound (filterAllAgg kv.2 []) :=
      filterSlices_of_ghosts φ hG _ kv (hl.1.2 kv hkv) hm (run_slices φ hwf (filterSlices_of_ghosts φ hG) kv hkv)
        [] [] hv
    have hpr := pruned_filterAllAgg kv.2 []
    have hcsG : (filterAllAgg kv.2 []).current_step = stepCount φ := by rw [hpr.step_eq, hstep]
    have hR : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
    obtain ⟨bs, sel, hrd, hsc, hidx⟩ := read_complete φ hPE φ.nVars 0 _ hR hv ht
      (NodesOnMap_of_pruned φ hpr hm.onMap) (AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot [])
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

/-- info: 'AbsSat.GraphPath.Model.ReaderComplete.answer_ne_unknown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown

end AbsSat.GraphPath.Model.ReaderComplete
