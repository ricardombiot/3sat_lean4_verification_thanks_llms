-- lean_project/AbsSat/GraphPath/Model/PinDeath.lean
import AbsSat.GraphPath.Model.PinClause

/-!
# The direct death of an entry under a pin

Probe `splittri` (report v161): at a union by key, three nodes can be owners two by two with no side
holding the three pairs. When the next UP pins the third, each such entry either stays on one side or dies
**directly**: at some step, every node common to its two ends already excludes the pinned value.

This module proves the mechanical half. After pins and the aggressive review, a surviving entry has, at
every step, a common node of its two ends that owns a node of the pinned map node — in the pinned state,
hence already in the unpinned one. Read backwards: **one step where every common node excludes the pin
kills the entry.**
-/

namespace AbsSat.GraphPath.Model.PinDeath

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv)
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Rel)
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.ConservationPrefix (SatBelow)
open AbsSat.GraphPath.Model.BranchLines (sent)
open AbsSat.GraphPath.Model.PinHistory (branchLine branchLine_inv PinIdsBelow)
open AbsSat.GraphPath.Model.PinVar (canon Agrees)
open AbsSat.GraphPath.Model.PinClause (SideKeepAt LineSoundL Full)

variable (φ : Cnf)

/-- An entry of a pruned state is an entry of the state it was pruned from. -/
theorem rel_of_pruned (J X : GPathM) (hnd : (J.nodes.map (·.id)).Nodup) (pr : Pruned J X)
    (a b : PathNodeId) (h : Rel X a b) : Rel J a b := by
  have memJ : ∀ c n, X.node? c = some n → ∃ n0, J.node? c = some n0 ∧ ∀ q ∈ n.owners, q ∈ n0.owners := by
    intro c n hn
    obtain ⟨n0, hn0, hid, hown, _⟩ := pr.nodes_derived n (List.mem_of_find?_eq_some hn)
    refine ⟨n0, ?_, hown⟩
    rw [← node?_id_eq X c n hn, hid]; exact node?_of_mem hnd n0 hn0
  obtain ⟨n, hn, hb, ⟨nb, hnb⟩⟩ := h
  obtain ⟨n0, hn0, hown⟩ := memJ a n hn
  obtain ⟨nb0, hnb0, _⟩ := memJ b nb hnb
  exact ⟨n0, hn0, hown b hb, nb0, hnb0⟩

/-- **What a pinned survivor keeps.** An entry `x → v` that survives the pin of `r` and the aggressive
review has, at every step `l`, a node `z` common to `x` and `v` that owns a node `ρ` of the map node
`r` — and all of it is already in the unpinned state. -/
theorem pinned_common (J : GPathM) (hmJ : MInv φ J) (r : NodeId) (h0r : 0 ≤ r.step)
    (hrc : r.step < J.current_step) (hvX : isValid (filterAllAgg J [r]) = true)
    (x v : PathNodeId) (hxv : Rel (filterAllAgg J [r]) x v) :
    ∀ l, 0 ≤ l → l < J.current_step →
      ∃ z ρ, z.id.step = l ∧ Rel J x z ∧ Rel J v z ∧ Rel J z ρ ∧ ρ.id = r := by
  intro l hl0 hl1
  have hRX : ReadableAgg (filterAllAgg J [r]) := ⟨J, [r], hmJ.rctx, rfl⟩
  have okX : AggFixpoint.AggOk (filterAllAgg J [r]) := AggFixpoint.aggOk_reviewAgg _ hvX
  have smpX := AnchoredSurvive.SMP_filterAllAgg J hmJ.smp hmJ.rctx.shape.notroot [r]
  have pmsX := AggInvariants.PMS_filterAllAgg J [r] hmJ.pms
  have snX := AggInvariants.SN_filterAllAgg J [r] hmJ.sn
  have prX : Pruned J (filterAllAgg J [r]) := pruned_filterAllAgg _ _
  have cleanX : ∀ q, q ∈ (filterAllAgg J [r]).gowners → q.id.step = r.step → q.id = r :=
    fun q hq hs => ReaderAggRun.filterAllAgg_cleans J [r] r List.mem_cons_self q hq hs
  generalize filterAllAgg J [r] = X at hRX hvX okX smpX pmsX snX prX cleanX hxv
  have adX := AdjacentOwners.adj_of_readable X hRX hvX pmsX snX
  have supX := LinkedChain.sup_self X adX okX smpX
  have hcs : X.current_step = J.current_step := prX.step_eq
  obtain ⟨z, hxz, hvz, hzs⟩ := supX.agg x v hxv l hl0 (by rw [hcs]; exact hl1)
  obtain ⟨ρ, hzρ, hρs⟩ := supX.cov z (supX.dom x z hxz).2 r.step h0r (by rw [hcs]; exact hrc)
  have hρ := cleanX ρ (supX.gow ρ (supX.dom z ρ hzρ).2) hρs
  have R := rel_of_pruned J X hmJ.rctx.nodup prX
  exact ⟨z, ρ, hzs, R _ _ hxz, R _ _ hvz, R _ _ hzρ, hρ⟩

/-- **The direct death.** If at some step every node common to `x` and `v` excludes the pinned map node
`r`, the pin of `r` and the aggressive review remove the entry `x → v`. -/
theorem direct_death (J : GPathM) (hmJ : MInv φ J) (r : NodeId) (h0r : 0 ≤ r.step)
    (hrc : r.step < J.current_step) (hvX : isValid (filterAllAgg J [r]) = true)
    (x v : PathNodeId) (l : Int) (hl0 : 0 ≤ l) (hl1 : l < J.current_step)
    (hk : ∀ z ρ, z.id.step = l → Rel J x z → Rel J v z → Rel J z ρ → ρ.id ≠ r) :
    ¬ Rel (filterAllAgg J [r]) x v := by
  intro hxv
  obtain ⟨z, ρ, hzs, hxz, hvz, hzρ, hρ⟩ := pinned_common φ J hmJ r h0r hrc hvX x v hxv l hl0 hl1
  exact hk z ρ hzs hxz hvz hzρ hρ

/-- info: 'AbsSat.GraphPath.Model.PinDeath.direct_death' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms direct_death

-- ============================================================
-- The witness row
-- ============================================================

/-- **The witness row, at line `m`.** Take an entry `x → v` of a union by key, and a literal value `r`
such that, at every step, some node common to `x` and `v` owns a node of `r` (what the pin and the review
leave to a survivor, `pinned_common`). Then some genuine path of the union passes `x`, `v` and `r`.

Read backwards, this is the probe's observation: if no path passes the three, then at some step — a
clause row — every common node already excludes `r`, and the entry dies directly (`direct_death`). It is
a statement about the union alone, before any pin. -/
def RowWitnessAt (m : Nat) : Prop :=
  ∀ (P : List NodeId) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ p J, (p, J) ∈ pureAdvanceW φ (branchLine φ P m) →
      ∀ x v, Rel J x v →
        (∀ l, 0 ≤ l → l < (m : Int) + 2 →
          ∃ z ρ, z.id.step = l ∧ Rel J x z ∧ Rel J v z ∧ Rel J z ρ ∧ ρ.id = r) →
        ∃ b : Assign, SatBelow φ b ((m : Int) + 2) ∧ selOfAssign φ b ((m : Int) + 1) = p ∧
          Agrees φ P b ((m : Int) + 1) ∧ canon φ b x.id.step = x ∧ canon φ b v.id.step = v ∧
          selOfAssign φ b r.step = r

/-- **The direct death and the witness row give nothing borrowed.** A survivor of the pin keeps a common
node owning the pin at every step (`pinned_common`); the witness row turns that into a genuine path
through the entry and the pin, and that path lies in one side's pinned send. -/
theorem sideKeep_of_row (hwf : WF φ) (m : Nat) (hW : RowWitnessAt φ m) : SideKeepAt φ m := by
  intro P r h0r hrm hrl p J hJ hvX x v hxv
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  have hle : (m : Int) + 2 ≤ stepCount φ := by
    have := PinVar.lt_of_mapNodes φ _ p hsJ.onMap; omega
  have hrc : r.step < J.current_step := by rw [hcsJ]; omega
  have com := pinned_common φ J hmJ r h0r hrc hvX x v hxv
  have hxvJ := rel_of_pruned J _ hmJ.rctx.nodup (pruned_filterAllAgg J [r]) x v hxv
  have bnd : ∀ a, Mem J a → 0 ≤ a.id.step ∧ a.id.step < (m : Int) + 2 := by
    intro a ⟨na, hna⟩
    have hmem := List.mem_of_find?_eq_some hna
    rw [← node?_id_eq J a na hna, ← hcsJ]
    exact ⟨hmJ.rctx.snn na hmem, hmJ.rctx.below na hmem⟩
  obtain ⟨nx, hnx, hvnx, hvm⟩ := id hxvJ
  have bx := bnd x ⟨nx, hnx⟩
  have bv := bnd v hvm
  obtain ⟨b, hsat, hbp, hag, cx, cv, hr⟩ := hW P r h0r hrm hrl p J hJ x v hxvJ
    (fun l h0 h1 => com l h0 (by rw [hcsJ]; exact h1))
  obtain ⟨kv, hkv, hson, hvS, hsc⟩ := PinVar.side_of_path φ hwf P m hle r p b hsat hr hbp hag
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hsS := ConservationFilter.StateOkF_sent φ (ConservationFilter.Fsac φ 0) reviewAgg
    (ConservationFilter.prunes_Fsac φ 0) m kv hsok p hson hvS
  have hsS' : (sent φ kv.2 p).current_step = (m : Int) + 1 + 1 := hsS.step
  have hcsY : (filterAllAgg (sent φ kv.2 p) [r]).current_step = (m : Int) + 2 := by
    rw [(pruned_filterAllAgg _ _).step_eq, hsS']; omega
  have hrel := JoinSide.rel_of_chain _ _ hsc v.id.step x.id.step bv.1 (by rw [hcsY]; exact bv.2) bx.1
    (by rw [hcsY]; exact bx.2)
  rw [cx, cv] at hrel
  exact ⟨kv, hkv, hson, hvS, PickInduction.isValid_of_ChainG _ _ hsc.chain, hrel⟩

/-- **The verdict from the witness row.** The witness row is only needed where the joint induction has
already made the union exact (every entry on a path of one side). -/
theorem sat_of_rowWitness (hwf : WF φ)
    (hW : ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 →
      (∀ P, LineSoundL Full (pureAdvanceW φ (branchLine φ P m))) → RowWitnessAt φ m)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ := by
  have hE := (PinClause.joint φ hwf (fun m h hC hadv =>
    PinClause.flipSat_of_sideKeep φ hwf m hC hadv (sideKeep_of_row φ hwf m (hW m h hadv)))
    (stepCount φ - 1).toNat).1 []
  rw [PinHistory.branchLine_nil] at hE
  refine RunInhabited.sat_of_lineSound φ hwf (fun kv' hkv' => ?_) kv hkv hv
  intro x n hx hx0 hx1 q hq0 hq1 _ hqn
  exact hE kv' hkv' x n hx hx0 hx1 q hq0 hq1 trivial hqn

/-- info: 'AbsSat.GraphPath.Model.PinDeath.sat_of_rowWitness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_rowWitness

end AbsSat.GraphPath.Model.PinDeath
