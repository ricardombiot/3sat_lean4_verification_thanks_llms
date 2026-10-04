-- lean_project/AbsSat/GraphPath/Model/SliceInvariant.lean
import AbsSat.GraphPath.Model.Exactness
import AbsSat.GraphPath.Model.NoDeadEndVerdict
import AbsSat.GraphPath.Model.BranchLines

/-!
# The slice invariant, carried by the construction

The author's design (v139): every node's table is the set of nodes of the paths through it — its
**slice**. The up makes it true at birth (the new node takes every global owner of the pinned,
reviewed state, and joins every table); the join keeps it (a joined table is the union of the sides'
slices). This is `Exactness.TablesSound` (and `TablesComplete`, free).

This module carries the invariant along the whole run, **by construction**, with one hypothesis — the
only operation not yet proved to keep it:

* **`FilterSlices`** — pinning a line state (weak requirements and requirements) and reviewing it keeps
  every table a slice.

and gives:

* `tablesSound_sent` — a send keeps the invariant (the filter by hypothesis, the up by
  `tablesSound_addNode`);
* `lineSlices_advance`, `lineSlices_init` — every line of the driver has it (seeds by
  `tablesSound_initSeed`, joins by `tablesSound_join`);
* **`sat_of_slices`** — and the verdict follows at once: a valid reader's state has a global owner, which
  owns itself, so its slice holds a whole path, which is a model.
-/

namespace AbsSat.GraphPath.Model.SliceInvariant

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
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_sendToW LineInv_pureAdvanceW LineInv_init
  LineInv_steps)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF StateOkF_sent Fsac prunes_Fsac)
open AbsSat.GraphPath.Model.BranchLines (sent sendToW_eq insert_src advance_inv lineInv_nil)
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes tablesSound_initSeed tablesSound_addNode
  tablesSound_join)
open AbsSat.GraphPath.Model.PickInduction (gowner_of_isValid)

variable (φ : Cnf)

/-- **The one open step**: pinning and reviewing a line state keeps every table a slice. -/
def FilterSlices : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 → TablesSound kv.2 →
    ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
      isValid (filterAllAgg (filterWeakAll kv.2 ws) rq) = true →
      TablesSound (filterAllAgg (filterWeakAll kv.2 ws) rq)

/-- Every table of every state of a line is a slice. -/
def LineSlices (L : PureLine) : Prop := ∀ kv ∈ L, TablesSound kv.2

-- ============================================================
-- A send keeps the slices
-- ============================================================

theorem nonneg_of_mapNodes (k : Int) (d : NodeId) (h : d ∈ mapNodes φ k) : 0 ≤ k := by
  unfold mapNodes at h
  split at h
  · exact absurd h List.not_mem_nil
  · omega

/-- **A send keeps the slices**: the filter by hypothesis, the up because the new node takes the whole
state as its table. -/
theorem tablesSound_sent (_hwf : WF φ) (hF : FilterSlices φ) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) (hm : MInv φ kv.2) (ht : TablesSound kv.2)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hval : isValid (sent φ kv.2 d) = true) :
    TablesSound (sent φ kv.2 d) := by
  have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hsok.onMap
  have hk0 : 0 ≤ k := nonneg_of_mapNodes φ k kv.1 hkv.onMap
  let F := filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)
  have hkF : Keeps kv.2 F :=
    Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have hvF : isValid F = true := by
    by_cases h : isValid F = true
    · exact h
    · exfalso
      have he : sent φ kv.2 d = F := by
        simp only [sent, upFilteringWeak, GPathM.up, F, if_neg h]
      rw [he] at hval
      exact h hval
  have hRF : ReadableAgg F :=
    ⟨filterWeakAll kv.2 (weakReqOfCnf φ d), reqOfCnf φ d,
      RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  have rcF := RCtx_of_readableAgg F hRF
  have ctxF := Reader.Ctx_of_readable F (readable_of_readableAgg F hRF) hvF
  have hstepF : F.current_step = k + 1 := by rw [hkF.1.step_eq, hkv.step]
  have heq : sent φ kv.2 d = addNode F d "" := by
    simp only [sent, upFilteringWeak, GPathM.up, F] at hvF ⊢
    rw [if_pos hvF]
  rw [heq]
  refine tablesSound_addNode F d "" (by rw [hstepF, hdstep]) (by rw [hstepF]; omega) rcF.below ?_
    rcF.nodup hvF (fun y m hy => ctxF.self y m hy) ?_ rcF.gn (hF k kv hkv hm ht _ _ hvF)
  · have hmo := hm.mok
    unfold MachineOk at hmo ⊢
    rw [hkF.1.step_eq, hkF.1.map_parent_eq]
    exact hmo
  · intro y m hy w hw
    have hmem : m ∈ F.nodes := List.mem_of_find?_eq_some hy
    obtain ⟨n₀, hn₀, _, hown₀, _⟩ := hkF.1.nodes_derived m hmem
    obtain ⟨m', hm', hm'id⟩ := hm.own n₀ hn₀ w (hown₀ w hw)
    rw [hkF.1.step_eq, ← hm'id]
    exact hm.rctx.below m' hm'

-- ============================================================
-- Lines keep the slices
-- ============================================================

theorem lineSlices_insertPure (acc : PureLine) (key : NodeId) (g : GPathM)
    (hacc : LineSlices acc) (hg : TablesSound g) : LineSlices (insertPure acc key g) := by
  rintro ⟨d, B⟩ hB
  rcases insert_src acc key g d B hB with ⟨_, hB'⟩ | ⟨hB', _⟩
  · rcases hB' with rfl | ⟨e, he, rfl⟩
    · exact hg
    · unfold doJoin
      split
      · next hok => exact tablesSound_join e g hok (hacc (key, e) he) hg
      · exact hacc (key, e) he
  · exact hacc (d, B) hB'

theorem lineSlices_advance (hwf : WF φ) (hF : FilterSlices φ) (k : Int) (L : PureLine)
    (hl : LineInv φ k L) (hs : LineSlices L) : LineSlices (pureAdvanceW φ L) := by
  have main := advance_inv φ (fun acc => LineInv φ (k + 1) acc ∧ LineSlices acc) L ?_
    ⟨lineInv_nil φ (k + 1), fun _ h => absurd h List.not_mem_nil⟩
  · exact main.2
  intro kv hkv d hd acc ⟨ha, hsl⟩
  refine ⟨LineInv_sendToW φ hwf k kv (hl.1.2 kv hkv) (hl.2 kv hkv) d hd acc ha, ?_⟩
  rw [sendToW_eq]
  split
  · next hv =>
    exact lineSlices_insertPure acc d _ hsl
      (tablesSound_sent φ hwf hF k kv (hl.1.2 kv hkv) (hl.2 kv hkv) (hs kv hkv) d hd hv)
  · exact hsl

theorem lineSlices_init : LineSlices (pureInit φ) := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d.step = 0) → ∀ acc : PureLine, LineSlices acc →
      LineSlices (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (lineSlices_insertPure acc x _ h (tablesSound_initSeed x "" (hx x List.mem_cons_self)))
  exact main _ (fun d hd => mapNodes_step φ 0 d hd) [] (fun _ h => absurd h List.not_mem_nil)

theorem lineSlices_steps (hwf : WF φ) (hF : FilterSlices φ) :
    ∀ (n : Nat) (k : Int) (L : PureLine), LineInv φ k L → LineSlices L →
      LineSlices (pureStepsW φ n L) := by
  intro n
  induction n with
  | zero => intro _ L _ hs; exact hs
  | succ n ih =>
    intro k L hl hs
    exact ih (k + 1) _ (LineInv_pureAdvanceW φ hwf k L hl) (lineSlices_advance φ hwf hF k L hl hs)

/-- **Every state of the run has slices for tables**, given the filter step. -/
theorem run_slices (hwf : WF φ) (hF : FilterSlices φ) : LineSlices (pureRunW φ) :=
  lineSlices_steps φ hwf hF _ 0 (pureInit φ) (LineInv_init φ hwf) (lineSlices_init φ)

-- ============================================================
-- The verdict
-- ============================================================

/-- **The Improves verdict from the slice invariant.** If pinning and reviewing keeps every table a
slice, a valid reader's state gives a model of `φ`: it has a global owner, which owns itself, and its
slice holds a whole path. -/
theorem sat_of_slices (hwf : WF φ) (hF : FilterSlices φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hl := (LineInv_steps φ hwf (stepCount φ - 1).toNat 0 (pureInit φ) (LineInv_init φ hwf))
  have hcast : (0 : Int) + (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by
    have := ConservationCore.stepCount_pos φ; omega
  rw [hcast] at hl
  have hsk := hl.1.2 kv hkv
  have hts := hF _ kv hsk hm (run_slices φ hwf hF kv hkv) [] [] hv
  have hfw : filterWeakAll kv.2 [] = kv.2 := rfl
  rw [hfw] at hts
  let G := filterAllAgg kv.2 []
  have hRG : ReadableAgg G := ⟨kv.2, [], hm.rctx, rfl⟩
  have rcG := RCtx_of_readableAgg G hRG
  have ctxG := Reader.Ctx_of_readable G (readable_of_readableAgg G hRG) hv
  have hpos := ConservationCore.stepCount_pos φ
  have hcsG : G.current_step = stepCount φ := by
    rw [(pruned_filterAllAgg kv.2 []).step_eq, hstep]
  obtain ⟨q, hq, hq0⟩ := gowner_of_isValid G hv 0 (Int.le_refl _) (by rw [hcsG]; omega)
  obtain ⟨m, hmm, hmid⟩ := rcG.gn q hq
  have hqm : G.node? q = some m := by rw [← hmid]; exact node?_of_mem rcG.nodup m hmm
  have hself : q ∈ m.owners := ctxG.self q m hqm
  obtain ⟨sel, hcs, _, _⟩ := hts q m hqm (by omega) (by rw [hcsG]; omega) q (by omega)
    (by rw [hcsG]; omega) hself
  exact NoDeadEndVerdict.sat_of_denotS φ hwf kv hkv ⟨_, sel, hcs, rfl⟩

/-- info: 'AbsSat.GraphPath.Model.SliceInvariant.sat_of_slices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_slices

end AbsSat.GraphPath.Model.SliceInvariant
