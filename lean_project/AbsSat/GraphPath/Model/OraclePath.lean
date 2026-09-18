-- lean_project/AbsSat/GraphPath/Model/OraclePath.lean
import AbsSat.GraphPath.Model.SendDistrib

/-!
# The machine as the compressed oracle: a valid state holds a whole oracle path

The author's reading (v139): the machine uses abstraction to avoid the space explosion, but what it
builds is, abstractly, the set of paths a brute-force oracle would check one by one. The probe
`helly oracle` measures it literally: every state of the run is, table by table, the join of the
single-path runs (one map node pinned at every step) that reach its key valid.

This module proves the two halves of that reading that the verdict needs.

* **`sat_of_oracle_path`** — *no hypothesis*: if the run restricted to one oracle path (a pin at every
  step) reaches the final key valid, `φ` is satisfiable. With every step pinned no choice is left, and
  the reader reads the path.
* **`exists_oracle_path`** — under the distributive equations (`SendDistrib`, `ReviewDistrib`): a valid
  final state holds a whole oracle path that reaches it valid **on its own**. It is `split_branch`
  applied at every step, from the bottom up.
* **`sat_of_oracle`** — together, the verdict: the machine answers SAT only if one of the oracle's
  paths survives by itself.
-/

namespace AbsSat.GraphPath.Model.OraclePath

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchLines
open AbsSat.GraphPath.Model.BranchCompat
open AbsSat.GraphPath.Model.BranchReader
open AbsSat.GraphPath.Model.SendDistrib
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice)

variable (φ : Cnf)

/-- **An oracle path**: a pin at every step of the map. -/
def FullPins (P : List NodeId) : Prop :=
  ∀ i : Nat, i ≤ (stepCount φ - 1).toNat → ∃ r ∈ P, r.step = (i : Int)

-- ============================================================
-- A valid oracle path is a model
-- ============================================================

theorem gowners_pinOneByOne_sub : ∀ (P : List NodeId) (g : GPathM),
    ∀ q ∈ (pinOneByOne g P).gowners, q ∈ g.gowners := by
  intro P
  induction P with
  | nil => intro g q hq; exact hq
  | cons r rest ih =>
    intro g q hq
    exact (pruned_filterAllAgg g [r]).gowners_sub q (ih (filterAllAgg g [r]) q hq)

/-- Once pinned, a step keeps only global owners carrying the pin. -/
theorem pinned_ids : ∀ (P : List NodeId) (g : GPathM), ∀ r ∈ P,
    ∀ q ∈ (pinOneByOne g P).gowners, q.id.step = r.step → q.id = r := by
  intro P
  induction P with
  | nil => intro g r hr; exact absurd hr List.not_mem_nil
  | cons r0 rest ih =>
    intro g r hr q hq hs
    rcases List.mem_cons.mp hr with rfl | hr'
    · have h1 := gowners_pinOneByOne_sub rest (filterAllAgg g [r]) q hq
      have h2 : q ∈ ([r].foldl filterRequire g).gowners :=
        (reviewOk_reviewAgg.pruned ([r].foldl filterRequire g)).gowners_sub q h1
      simp only [List.foldl_cons, List.foldl_nil, filterRequire, List.mem_filter] at h2
      have h3 := h2.2
      have hne : (q.id.step != r.step) = false := by rw [hs]; exact bne_self_eq_false _
      rw [hne, Bool.false_or] at h3
      exact eq_of_beq h3
    · exact ih (filterAllAgg g [r0]) r hr' q hq hs

/-- With a pin at every step, no choice is left. -/
theorem noChoice_of_fullPins (g : GPathM) (P : List NodeId)
    (hcs : (pinOneByOne g P).current_step = stepCount φ) (hP : FullPins φ P) :
    hasChoice (pinOneByOne g P) = false := by
  unfold hasChoice
  apply List.any_eq_false.mpr
  intro k hk hck
  have h0 := mem_intRange_lower hk
  have h1 := mem_intRange_upper hk
  obtain ⟨r, hr, hrs⟩ := hP k.toNat (by omega)
  have hrs' : r.step = k := by rw [hrs]; omega
  obtain ⟨x, hx, hx2⟩ := List.any_eq_true.mp hck
  obtain ⟨y, hy, hne⟩ := List.any_eq_true.mp hx2
  have hxs : x.id.step = k := eq_of_beq (List.mem_filter.mp hx).2
  have hys : y.id.step = k := eq_of_beq (List.mem_filter.mp hy).2
  have hxid := pinned_ids P g r hr x (List.mem_filter.mp hx).1 (by rw [hxs, hrs'])
  have hyid := pinned_ids P g r hr y (List.mem_filter.mp hy).1 (by rw [hys, hrs'])
  rw [hxid, hyid] at hne
  exact absurd hne (by simp)

theorem inhabited_of_pinOneByOne : ∀ (P : List NodeId) (g : GPathM), ReadableAgg g →
    Inhabited (pinOneByOne g P) → Inhabited g := by
  intro P
  induction P with
  | nil => intro g _ h; exact h
  | cons q rest ih =>
    intro g hR h
    obtain ⟨p, hp⟩ := ih (filterAllAgg g [q]) (ReadableAgg_filterAllAgg g hR [q]) h
    exact ⟨p, denot_of_pruned (pruned_filterAllAgg g [q]) (RCtx_of_readableAgg g hR).nodup p hp⟩

theorem pinOneByOne_step (g : GPathM) : ∀ P, (pinOneByOne g P).current_step = g.current_step := by
  intro P
  induction P generalizing g with
  | nil => rfl
  | cons q rest ih =>
    show (pinOneByOne (filterAllAgg g [q]) rest).current_step = g.current_step
    rw [ih, (pruned_filterAllAgg g [q]).step_eq]

/-- **A valid oracle path is a model** — with no hypothesis. If the run restricted to one oracle path
reaches the final key `K` valid, reading the machine's final state at `K` with that path's pins gives a
path, which decodes to a model of `φ`. -/
theorem sat_of_oracle_path (hwf : WF φ) (K : NodeId) (G : GPathM) (hG : (K, G) ∈ pureRunW φ)
    (P : List NodeId) (hP : FullPins φ P) (hb : BranchValid φ P K) : Satisfiable φ := by
  have hm := (ReaderAggRun.pureRunW_state φ hwf (K, G) hG).1
  have hGstep := (ReaderAggRun.pureRunW_state φ hwf (K, G) hG).2.1
  have hR₀ : ReadableAgg (filterAllAgg G []) := ⟨G, [], hm.rctx, rfl⟩
  have hRP := readable_pinOneByOne _ hR₀ P
  have hvP := valid_of_branchValid φ hwf K G hG P hb
  have hcs : (pinOneByOne (filterAllAgg G []) P).current_step = stepCount φ := by
    rw [pinOneByOne_step, (pruned_filterAllAgg G []).step_eq]; exact hGstep
  have hnc := noChoice_of_fullPins φ _ P hcs hP
  have hinh := Reader.inhabited_of_noChoice_readable _ (readable_of_readableAgg _ hRP) hvP hnc
  obtain ⟨p, hp⟩ := inhabited_of_pinOneByOne P _ hR₀ hinh
  exact ReaderAggRun.sat_of_denot_final φ hwf (K, G) hG p
    (denot_of_pruned (pruned_filterAllAgg G []) hm.rctx.nodup p hp)

-- ============================================================
-- A valid state holds an oracle path
-- ============================================================

/-- **A valid branch holds a whole oracle path**, under the distributive equations: pinning, step after
step, the piece that stays valid on its own. -/
theorem oracle_path_of_branch (hwf : WF φ) (hS : SendDistrib φ) (hR : ReviewDistrib φ) (K : NodeId) :
    ∀ j : Nat, j ≤ (stepCount φ - 1).toNat + 1 → ∀ P, BranchValid φ P K →
      ∃ P', (∀ i : Nat, i < j → ∃ r ∈ P', r.step = (i : Int)) ∧ (∀ r ∈ P, r ∈ P') ∧ BranchValid φ P' K := by
  intro j
  induction j with
  | zero => intro _ P hb; exact ⟨P, fun i hi => absurd hi (Nat.not_lt_zero i), fun _ h => h, hb⟩
  | succ j ih =>
    intro hj P hb
    obtain ⟨P1, hcov, hsub, hb1⟩ := ih (by omega) P hb
    obtain ⟨x, hx, hbx⟩ := split_branch φ hwf hS hR P1 K j (by omega) hb1
    have hxs := bline_key_step φ hwf P1 j x hx
    refine ⟨P1 ++ [x.1], fun i hi => ?_, fun r hr => List.mem_append_left _ (hsub r hr), hbx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · obtain ⟨r, hr, hrs⟩ := hcov i hi
      exact ⟨r, List.mem_append_left _ hr, hrs⟩
    · exact ⟨x.1, List.mem_append_right _ List.mem_cons_self, by rw [hxs, hi]⟩

/-- **A valid final state holds an oracle path that reaches it valid on its own.** -/
theorem exists_oracle_path (hwf : WF φ) (hS : SendDistrib φ) (hR : ReviewDistrib φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    ∃ P, FullPins φ P ∧ BranchValid φ P kv.1 := by
  have hb₀ : BranchValid φ [] kv.1 := ⟨kv, by rw [branchRun_nil]; exact hkv, rfl, hv⟩
  obtain ⟨P, hcov, _, hb⟩ := oracle_path_of_branch φ hwf hS hR kv.1 _ (Nat.le_refl _) [] hb₀
  exact ⟨P, fun i hi => hcov i (by omega), hb⟩

/-- **The verdict, as the compressed oracle**: a valid final state holds an oracle path that survives on
its own, and a surviving oracle path is a model. -/
theorem sat_of_oracle (hwf : WF φ) (hS : SendDistrib φ) (hR : ReviewDistrib φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ := by
  obtain ⟨P, hP, hb⟩ := exists_oracle_path φ hwf hS hR kv hkv hv
  exact sat_of_oracle_path φ hwf kv.1 kv.2 hkv P hP hb

/-- info: 'AbsSat.GraphPath.Model.OraclePath.sat_of_oracle_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_oracle_path

/-- info: 'AbsSat.GraphPath.Model.OraclePath.sat_of_oracle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_oracle

end AbsSat.GraphPath.Model.OraclePath
