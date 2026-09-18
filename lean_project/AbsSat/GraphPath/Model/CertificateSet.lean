-- lean_project/AbsSat/GraphPath/Model/CertificateSet.lean
import AbsSat.GraphPath.Model.NoDeadEndVerdict
import AbsSat.GraphPath.Model.EmptinessReduction

/-!
# The machine computes the set of certificates, exactly

The author's question (v136): the machine works on **sets** of partial paths, the problem speaks of
**one** path. Redefine the problem at the level of sets — *return a set holding every certificate*,
as the oracle did — and reduce one problem to the other.

This file does that for the *Improves* machine, and the answer has two halves.

**The set is exact, with no hypothesis.** Call `MachineSet φ` the paths of the reader's states on the
last line of the run (the union, over final keys, of `denotS` of each reader state).

* `machineSet_complete` — every satisfying assignment's path is in it (the conservation law,
  `chainSound_alongW`, carried through the reader's filter by `ChainSound_filterAllAgg`).
* `machineSet_sound` — every path in it spells a model (`CnfChain.decode` of its chain).
* `machineSet_nonempty_iff` — so the set is non-empty **iff** `φ` is satisfiable.

The set problem is therefore solved: the machine returns — in compressed form — exactly the
certificates, as the oracle did in explicit form.

**The reduction back to SAT is the emptiness test.** The machine does not look at the set; it keeps
a state when `isValid` holds on its tables. `isValid_of_denotS` gives one direction for free (a
non-empty set makes the state valid). The other direction is the only statement left:

* `ValidDecidesEmpty φ` — at every reader state of the last line, validity implies a path.
* `verdict_iff` — under it, *some reader state is valid* **iff** `φ` is satisfiable. The `⇐` half is
  unconditional (`exists_valid_of_sat`).
* `validDecidesEmpty_of_commonOwner` — `CommonOwner` at the valid reader states gives it.

In the vocabulary of knowledge compilation: the tables are a compiled representation of the model
set, the compilation is proved exact, and `CommonOwner` is the property that would make the
**consistency query** (is the represented set empty?) answerable locally — the role decomposability
plays in DNNF.
-/

namespace AbsSat.GraphPath.Model.CertificateSet

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.Hereditary
open AbsSat.GraphPath.Model.HereditaryBuild
open AbsSat.GraphPath.Model.SubsetSemantics (denotS)
open AbsSat.GraphPath.Model.MapReachable (ChainOnMap chainOnMap_of_nodesOnMap)

variable (φ : Cnf)

/-- The reader's state of a final state: the review with no pins. -/
abbrev reader (g : GPathM) : GPathM := filterAllAgg g []

/-- **The set the machine computes**: the paths of the reader's states on the run's last line. -/
def MachineSet (p : List NodeId) : Prop :=
  ∃ kv ∈ pureRunW φ, denotS (reader kv.2) p

/-- **The certificate of an assignment**: the path its choices spell on the map, top step first. -/
def certPath (a : Assign) : List NodeId :=
  (intRange 0 (stepCount φ - 1)).reverse.map (selOfAssign φ a)

-- ============================================================
-- Completeness: every certificate is in the set
-- ============================================================

/-- **Every satisfying assignment's path is in the machine's set.** -/
theorem machineSet_complete (hwf : WF φ) (a : Assign) (hsat : Sat a φ) :
    MachineSet φ (certPath φ a) := by
  obtain ⟨g, hmem, hal, hcs⟩ := ConservationImproves.pureRunW_carries φ a hwf hsat
  obtain ⟨sel, hsel, hids⟩ := ConservationImproves.chainSound_alongW φ a hwf hsat g hal
  have hr : ChainSound (reader g) sel :=
    ChainSound_filterAllAgg g [] sel hsel (fun _ h => absurd h List.not_mem_nil)
  have hstep : (reader g).current_step = stepCount φ := by
    rw [(pruned_filterAllAgg g []).step_eq, hcs]
  refine ⟨_, hmem, sel, hr, ?_⟩
  simp only [certPath, pathOf, hstep]
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_reverse.mp hk
  exact (hids k (mem_intRange_lower hk') (by have := mem_intRange_upper hk'; omega)).symm

-- ============================================================
-- Soundness: everything in the set is a certificate
-- ============================================================

/-- A path through a state of the final line spells a model, and the model is the decoding of the
chain that spells the path. -/
theorem model_of_denot_final (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (p : List NodeId) (hp : denot kv.2 p) :
    ∃ sel, p = pathOf sel kv.2 ∧ Sat (CnfChain.decode sel) φ := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  obtain ⟨sel, hchain, howned, hpe⟩ := hp
  have hrs := ReaderAggRun.reqSatisfying_of_MInv φ kv.2 hm sel hchain howned
  have hcm : ChainOnMap φ kv.2 sel := chainOnMap_of_nodesOnMap φ kv.2 hm.onMap sel hchain
  refine ⟨sel, hpe, PartialPaths.sat_of_satUpTo_final φ _ ?_⟩
  intro j c hj hle
  have hjlt : j < φ.clauses.length := by
    rcases Nat.lt_or_ge j φ.clauses.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  exact PrefixDecode.satClause_of_reqSat_prefix φ kv.2 sel hwf hchain hrs hcm j hjlt c hj
    (by rw [hstep]; omega)

/-- **Every path in the machine's set spells a model of `φ`.** -/
theorem machineSet_sound (hwf : WF φ) (p : List NodeId) (h : MachineSet φ p) :
    ∃ kv ∈ pureRunW φ, ∃ sel, p = pathOf sel (reader kv.2) ∧ Sat (CnfChain.decode sel) φ := by
  obtain ⟨kv, hkv, hd⟩ := h
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf _ hkv
  have hpr := pruned_filterAllAgg kv.2 []
  obtain ⟨sel, hpe, hsat⟩ := model_of_denot_final φ hwf _ hkv p
    (denot_of_pruned hpr hm.rctx.nodup p (NoDeadEndVerdict.denot_of_denotS hd))
  refine ⟨kv, hkv, sel, ?_, hsat⟩
  rw [hpe]
  simp only [pathOf, hpr.step_eq]

/-- **The machine's set is non-empty iff `φ` is satisfiable.** The set problem is solved exactly. -/
theorem machineSet_nonempty_iff (hwf : WF φ) : (∃ p, MachineSet φ p) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨p, h⟩
    obtain ⟨_, _, sel, _, hsat⟩ := machineSet_sound φ hwf p h
    exact ⟨_, hsat⟩
  · rintro ⟨a, hsat⟩
    exact ⟨_, machineSet_complete φ hwf a hsat⟩

-- ============================================================
-- The reduction back to SAT: the emptiness test
-- ============================================================

/-- **The one statement left**: at every reader state of the last line, validity of the tables
implies that the state's part of the set is non-empty. -/
def ValidDecidesEmpty : Prop :=
  ∀ kv ∈ pureRunW φ, isValid (reader kv.2) = true → ∃ p, denotS (reader kv.2) p

/-- **Validity is necessary**, with no hypothesis: a satisfiable formula leaves a valid reader state
on the last line. -/
theorem exists_valid_of_sat (hwf : WF φ) (h : Satisfiable φ) :
    ∃ kv ∈ pureRunW φ, isValid (reader kv.2) = true := by
  obtain ⟨p, kv, hkv, hd⟩ := (machineSet_nonempty_iff φ hwf).mpr h
  exact ⟨kv, hkv, EmptinessReduction.isValid_of_denotS _ p hd⟩

/-- On each reader state, validity and non-emptiness coincide under `ValidDecidesEmpty`. -/
theorem valid_iff_nonempty (h : ValidDecidesEmpty φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) :
    isValid (reader kv.2) = true ↔ ∃ p, denotS (reader kv.2) p :=
  ⟨h kv hkv, fun ⟨p, hp⟩ => EmptinessReduction.isValid_of_denotS _ p hp⟩

/-- **The verdict, as the reduction from the set problem.** Under `ValidDecidesEmpty`, some reader
state of the last line is valid iff `φ` is satisfiable. -/
theorem verdict_iff (hwf : WF φ) (h : ValidDecidesEmpty φ) :
    (∃ kv ∈ pureRunW φ, isValid (reader kv.2) = true) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨kv, hkv, hv⟩
    obtain ⟨p, hp⟩ := h kv hkv hv
    exact (machineSet_nonempty_iff φ hwf).mp ⟨p, kv, hkv, hp⟩
  · exact exists_valid_of_sat φ hwf

/-- **`CommonOwner` settles the emptiness test.** At a valid reader state of the last line,
`CommonOwner` gives no dead ends, the top anchor is free, and the descent yields a path. -/
theorem nonempty_of_commonOwner (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (reader kv.2) = true) (hco : Descent.CommonOwner (reader kv.2)) :
    ∃ p, denotS (reader kv.2) p := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  obtain ⟨hR, _, hp, hn⟩ := Fw_facts kv.2 hm.rctx hm.smp hm.pms hm.sn []
  have hfw : Fw kv.2 [] = filterAllAgg kv.2 [] := by
    simp only [Fw, PureDriverImproves.filterWeakAll_nil]
  rw [hfw] at hR hp hn
  have a := AdjacentOwners.adj_of_readable _ hR hv hp hn
  have hpos : 0 < (reader kv.2).current_step := by
    rw [(pruned_filterAllAgg kv.2 []).step_eq, hstep]
    exact ConservationCore.stepCount_pos φ
  have ha := NoDeadEnd.topAnchor_of _ hv hpos a.rc.gn a.rc.oos a.rc.shape a.rc.rootz
    (fun q d hd => a.ctx.nodeval q d hd)
  have hok := AggFixpoint.aggOk_reviewAgg _ hv
  exact NoDeadEnd.nonempty_of_noDeadEnd _ hpos ha (Descent.noDeadEnd_of_commonOwner _ a hok hco)

theorem validDecidesEmpty_of_commonOwner (hwf : WF φ)
    (h : ∀ kv ∈ pureRunW φ, isValid (reader kv.2) = true → Descent.CommonOwner (reader kv.2)) :
    ValidDecidesEmpty φ :=
  fun kv hkv hv => nonempty_of_commonOwner φ hwf kv hkv hv (h kv hkv hv)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.CertificateSet.machineSet_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms machineSet_complete

/-- info: 'AbsSat.GraphPath.Model.CertificateSet.machineSet_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms machineSet_sound

/-- info: 'AbsSat.GraphPath.Model.CertificateSet.machineSet_nonempty_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms machineSet_nonempty_iff

/-- info: 'AbsSat.GraphPath.Model.CertificateSet.verdict_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdict_iff

/-- info: 'AbsSat.GraphPath.Model.CertificateSet.validDecidesEmpty_of_commonOwner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms validDecidesEmpty_of_commonOwner

end AbsSat.GraphPath.Model.CertificateSet
