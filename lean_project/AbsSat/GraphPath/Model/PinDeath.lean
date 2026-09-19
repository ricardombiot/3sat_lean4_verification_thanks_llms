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
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.RunInhabited (SoundAt)

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

-- ============================================================
-- The side is chosen by its top
-- ============================================================

/-- The top node a side leaves in the union: the key, over the side's own key. -/
def topOf (p k : NodeId) : PathNodeId := { id := p, parent_id := some k }

/-- **The top keeps its side, at line `m`.** In a pinned union, if both ends of an entry own the top node
of one side, and the entry was already in that side, that side's pinned send keeps the entry. (Probe
`topkeep`, report v163: 0 failures. Without the last premise it fails: the pair may come from another
side while both ends belong to this one.) -/
def TopKeepAt (m : Nat) : Prop :=
  ∀ (P : List NodeId) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ p J, (p, J) ∈ pureAdvanceW φ (branchLine φ P m) → isValid (filterAllAgg J [r]) = true →
      ∀ kv ∈ branchLine φ P m, p ∈ mapSons φ kv.1.step kv.1.index → isValid (sent φ kv.2 p) = true →
        ∀ x v, Rel (filterAllAgg J [r]) x v →
          Rel (filterAllAgg J [r]) x (topOf p kv.1) → Rel (filterAllAgg J [r]) v (topOf p kv.1) →
          Rel (sent φ kv.2 p) x v →
          isValid (filterAllAgg (sent φ kv.2 p) [r]) = true ∧ Rel (filterAllAgg (sent φ kv.2 p) [r]) x v

/-- **A carrying top, at line `m`.** A survivor of the pin has a side whose top both ends own and which
already carried the entry. (Probe `topkeep`: 0 failures.) `top_is_side` gives a common top of a side for
free; what this adds is that some such side carries the entry itself. -/
def TopSideAt (m : Nat) : Prop :=
  ∀ (P : List NodeId) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ p J, (p, J) ∈ pureAdvanceW φ (branchLine φ P m) → isValid (filterAllAgg J [r]) = true →
      ∀ x v, Rel (filterAllAgg J [r]) x v →
        ∃ kv ∈ branchLine φ P m, p ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 p) = true ∧
          Rel (filterAllAgg J [r]) x (topOf p kv.1) ∧ Rel (filterAllAgg J [r]) v (topOf p kv.1) ∧
          Rel (sent φ kv.2 p) x v

/-- **Every top node of an exact union is the top of a side.** -/
theorem top_is_side (hwf : WF φ) (P : List NodeId) (m : Nat)
    (hE : LineSoundL Full (pureAdvanceW φ (branchLine φ P m))) (p : NodeId) (J : GPathM)
    (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m)) (x z : PathNodeId) (hxz : Rel J x z)
    (hz : z.id.step = (m : Int) + 1) :
    ∃ kv ∈ branchLine φ P m, p ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 p) = true ∧
      z = topOf p kv.1 := by
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  have hle : (m : Int) + 2 ≤ stepCount φ := by
    have := PinVar.lt_of_mapNodes φ _ p hsJ.onMap; omega
  have bnd : ∀ a, Mem J a → 0 ≤ a.id.step ∧ a.id.step < (m : Int) + 2 := by
    intro a ⟨na, hna⟩
    have hmem := List.mem_of_find?_eq_some hna
    rw [← node?_id_eq J a na hna, ← hcsJ]
    exact ⟨hmJ.rctx.snn na hmem, hmJ.rctx.below na hmem⟩
  obtain ⟨n, hn, hzn, hzm⟩ := id hxz
  have bx := bnd x ⟨n, hn⟩
  have bz := bnd z hzm
  obtain ⟨s, hs, _, hsz⟩ := (hE _ hJ) x n hn bx.1 (by rw [hcsJ]; exact bx.2) z bz.1
    (by rw [hcsJ]; exact bz.2) trivial hzn
  have hpins := PinHistory.pinIds_advance φ P m _ hl (PinHistory.pinIds_branch φ hwf P m) _ hJ
  obtain ⟨b, hb, hbp, hbP, hsat⟩ := PinVar.path_facts φ hwf P m p J hsJ hmJ hpins hle s hs
  have hm0 : (0 : Int) ≤ (m : Int) := by omega
  have hlt1 : (m : Int) + 1 < stepCount φ := by omega
  obtain ⟨g, hmem, _, _⟩ := PinVar.branch_carries φ hwf P b ((m : Int) + 1) (by omega)
    (ConservationPrefix.satBelow_mono hsat (by omega)) hbP m (Int.le_refl _)
  have hson : p ∈ mapSons φ (selOfAssign φ b (m : Int)).step (selOfAssign φ b (m : Int)).index := by
    rw [selOfAssign_step, ← hbp]
    exact ConservationPrefix.selOfAssign_son_below φ b m hsat hm0 hlt1
  have hgen : RunNoBorrow.Genuine φ ((m : Int) + 2) (canon φ b) := ⟨b, hsat, fun k _ _ => ⟨rfl, rfl⟩⟩
  obtain ⟨hvS, _⟩ := PinVar.branch_send_chain φ hwf P m hle (selOfAssign φ b (m : Int), g) hmem p hson
    (canon φ b) hgen rfl hbp hbP
  refine ⟨(selOfAssign φ b (m : Int), g), hmem, hson, hvS, ?_⟩
  obtain ⟨h1, h2⟩ := hb ((m : Int) + 1) (by omega) (by omega)
  have hne : ¬ ((m : Int) + 1 = 0) := by omega
  rw [hz] at hsz
  rw [hsz] at h1 h2
  rw [if_neg hne, show (m : Int) + 1 - 1 = (m : Int) by omega] at h2
  cases z with
  | mk zi zp =>
    simp only at h1 h2
    simp only [topOf, h1, h2, hbp]

/-- **Nothing borrowed, from the top.** -/
theorem sideKeep_of_top (m : Nat) (hS : TopSideAt φ m) (hT : TopKeepAt φ m) : SideKeepAt φ m := by
  intro P r h0r hrm hrl p J hJ hvX x v hxv
  obtain ⟨kv, hkv, hson, hvS, hxt, hvt, hS'⟩ := hS P r h0r hrm hrl p J hJ hvX x v hxv
  obtain ⟨hvY, hrel⟩ := hT P r h0r hrm hrl p J hJ hvX kv hkv hson hvS x v hxv hxt hvt hS'
  exact ⟨kv, hkv, hson, hvS, hvY, hrel⟩

/-- **The verdict from the top.** -/
theorem sat_of_topKeep (hwf : WF φ)
    (hT : ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 →
      (∀ P, LineSoundL Full (pureAdvanceW φ (branchLine φ P m))) → TopSideAt φ m ∧ TopKeepAt φ m)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ := by
  have hE := (PinClause.joint φ hwf (fun m h hC hadv =>
    PinClause.flipSat_of_sideKeep φ hwf m hC hadv (sideKeep_of_top φ m (hT m h hadv).1 (hT m h hadv).2))
    (stepCount φ - 1).toNat).1 []
  rw [PinHistory.branchLine_nil] at hE
  refine RunInhabited.sat_of_lineSound φ hwf (fun kv' hkv' => ?_) kv hkv hv
  intro x n hx hx0 hx1 q hq0 hq1 _ hqn
  exact hE kv' hkv' x n hx hx0 hx1 q hq0 hq1 trivial hqn

/-- info: 'AbsSat.GraphPath.Model.PinDeath.sat_of_topKeep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_topKeep

-- ============================================================
-- The union's table is the pair table of its genuine paths
-- ============================================================

/-- The genuine paths of the union by key `p` of line `m + 1`, on branch `P`. -/
def InUnion (P : List NodeId) (m : Nat) (p : NodeId) (b : Assign) : Prop :=
  SatBelow φ b ((m : Int) + 2) ∧ selOfAssign φ b ((m : Int) + 1) = p ∧ Agrees φ P b ((m : Int) + 1)

/-- **Completeness of the union.** Any two nodes of a genuine path through the key are an entry of the
union. -/
theorem union_complete (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId) (J : GPathM)
    (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m)) (b : Assign) (hb : InUnion φ P m p b)
    (i j : Int) (hi0 : 0 ≤ i) (hi1 : i < (m : Int) + 2) (hj0 : 0 ≤ j) (hj1 : j < (m : Int) + 2) :
    Rel J (canon φ b i) (canon φ b j) := by
  obtain ⟨hsat, hbp, hag⟩ := hb
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hle : (m : Int) + 2 ≤ stepCount φ := by
    have := PinVar.lt_of_mapNodes φ _ p hsJ.onMap; omega
  have hm0 : (0 : Int) ≤ (m : Int) := by omega
  have hlt1 : (m : Int) + 1 < stepCount φ := by omega
  obtain ⟨g, hmem, _, _⟩ := PinVar.branch_carries φ hwf P b ((m : Int) + 1) (by omega)
    (ConservationPrefix.satBelow_mono hsat (by omega)) hag m (Int.le_refl _)
  have hson : p ∈ mapSons φ (selOfAssign φ b (m : Int)).step (selOfAssign φ b (m : Int)).index := by
    rw [selOfAssign_step, ← hbp]
    exact ConservationPrefix.selOfAssign_son_below φ b m hsat hm0 hlt1
  have hgen : RunNoBorrow.Genuine φ ((m : Int) + 2) (canon φ b) := ⟨b, hsat, fun k _ _ => ⟨rfl, rfl⟩⟩
  obtain ⟨hvS, hsc⟩ := PinVar.branch_send_chain φ hwf P m hle (selOfAssign φ b (m : Int), g) hmem p hson
    (canon φ b) hgen rfl hbp hag
  obtain ⟨J', hJ', hg⟩ := BranchLines.full_reach φ hwf m _ hl _ hmem p hson hvS
  have hJJ : J' = J := BranchLines.key_unique _ hadv.1.1 p J' J hJ' hJ
  rw [hJJ] at hg
  have e := BranchRun.embedded_of_grown (BranchLines.embedded_refl _) hg
  have hcsS : (sent φ g p).current_step = (m : Int) + 2 := by rw [e.step, hsJ.step]; omega
  obtain ⟨nS, hnS, hq, hqm⟩ := JoinSide.rel_of_chain _ _ hsc j i hj0 (by rw [hcsS]; exact hj1) hi0
    (by rw [hcsS]; exact hi1)
  obtain ⟨n, hn, hown, _⟩ := e.node _ nS hnS
  obtain ⟨mq, hmq⟩ := hqm
  obtain ⟨nq, hnq, _, _⟩ := e.node _ mq hmq
  exact ⟨n, hn, hown _ hq ⟨mq, hmq⟩, nq, hnq⟩

/-- **The union's table is exactly the pair table of its genuine paths**, once the union is exact. -/
theorem union_rel_iff (hwf : WF φ) (P : List NodeId) (m : Nat)
    (hE : LineSoundL Full (pureAdvanceW φ (branchLine φ P m))) (p : NodeId) (J : GPathM)
    (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m)) (x v : PathNodeId)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < (m : Int) + 2) (hv0 : 0 ≤ v.id.step)
    (hv1 : v.id.step < (m : Int) + 2) :
    Rel J x v ↔ ∃ b, InUnion φ P m p b ∧ canon φ b x.id.step = x ∧ canon φ b v.id.step = v := by
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  have hle : (m : Int) + 2 ≤ stepCount φ := by
    have := PinVar.lt_of_mapNodes φ _ p hsJ.onMap; omega
  have bnd : ∀ a, Mem J a → 0 ≤ a.id.step ∧ a.id.step < (m : Int) + 2 := by
    intro a ⟨na, hna⟩
    have hmem := List.mem_of_find?_eq_some hna
    rw [← node?_id_eq J a na hna, ← hcsJ]
    exact ⟨hmJ.rctx.snn na hmem, hmJ.rctx.below na hmem⟩
  constructor
  · intro hxv
    obtain ⟨n, hn, hvn, hvm⟩ := id hxv
    have bx := bnd x ⟨n, hn⟩
    have bv := bnd v hvm
    obtain ⟨s, hs, hsx, hsv⟩ := (hE _ hJ) x n hn bx.1 (by rw [hcsJ]; exact bx.2) v bv.1
      (by rw [hcsJ]; exact bv.2) trivial hvn
    have hpins := PinHistory.pinIds_advance φ P m _ hl (PinHistory.pinIds_branch φ hwf P m) _ hJ
    obtain ⟨b, hb, hbp, hbP, hsat⟩ := PinVar.path_facts φ hwf P m p J hsJ hmJ hpins hle s hs
    refine ⟨b, ⟨hsat, hbp, hbP⟩, ?_, ?_⟩
    · rw [PinClause.canon_of_path φ b s _ hb x.id.step bx.1 bx.2, hsx]
    · rw [PinClause.canon_of_path φ b s _ hb v.id.step bv.1 bv.2, hsv]
  · rintro ⟨b, hb, hx, hv⟩
    have h := union_complete φ hwf P m p J hJ b hb x.id.step v.id.step hx0 hx1 hv0 hv1
    rwa [hx, hv] at h

end AbsSat.GraphPath.Model.PinDeath
