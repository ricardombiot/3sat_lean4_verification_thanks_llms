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

-- ============================================================
-- The witness, without the machine
-- ============================================================

/-- Two nodes are **compatible** when one genuine path of the union passes both. -/
def Compat (P : List NodeId) (m : Nat) (p : NodeId) (a b : PathNodeId) : Prop :=
  ∃ β, InUnion φ P m p β ∧ canon φ β a.id.step = a ∧ canon φ β b.id.step = b

/-- **The semantic witness, at line `m`.** A statement about the genuine paths of the union alone — no
owners, no review. If `x` and `v` are compatible and every step has a node compatible with `x`, `v` and a
node of the literal value `r`, then one genuine path passes `x`, `v` and `r`. (Probe traces of the choice
formulas, 2026-09-19: whenever the triple was impossible, some step had no such
node.) -/
def SemWitnessAt (m : Nat) : Prop :=
  ∀ (P : List NodeId) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ (p : NodeId) (x v : PathNodeId), Compat φ P m p x v →
      (∀ l, 0 ≤ l → l < (m : Int) + 2 →
        ∃ z ρ, z.id.step = l ∧ Compat φ P m p x z ∧ Compat φ P m p v z ∧ Compat φ P m p z ρ ∧ ρ.id = r) →
      ∃ β, InUnion φ P m p β ∧ canon φ β x.id.step = x ∧ canon φ β v.id.step = v ∧
        selOfAssign φ β r.step = r

/-- An entry of an exact union is a compatible pair. -/
theorem compat_of_rel (hwf : WF φ) (P : List NodeId) (m : Nat)
    (hE : LineSoundL Full (pureAdvanceW φ (branchLine φ P m))) (p : NodeId) (J : GPathM)
    (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m)) (a b : PathNodeId) (h : Rel J a b) :
    Compat φ P m p a b := by
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  have bnd : ∀ c, Mem J c → 0 ≤ c.id.step ∧ c.id.step < (m : Int) + 2 := by
    intro c ⟨nc, hnc⟩
    have hmem := List.mem_of_find?_eq_some hnc
    rw [← node?_id_eq J c nc hnc, ← hcsJ]
    exact ⟨hmJ.rctx.snn nc hmem, hmJ.rctx.below nc hmem⟩
  obtain ⟨n, hn, _, hbm⟩ := id h
  have ba := bnd a ⟨n, hn⟩
  have bb := bnd b hbm
  exact (union_rel_iff φ hwf P m hE p J hJ a b ba.1 ba.2 bb.1 bb.2).mp h

/-- **The witness row from the semantic witness.** Every `Rel` of the union is rewritten as
compatibility (`union_rel_iff`). -/
theorem rowWitness_of_sem (hwf : WF φ) (m : Nat)
    (hE : ∀ P, LineSoundL Full (pureAdvanceW φ (branchLine φ P m))) (hS : SemWitnessAt φ m) :
    RowWitnessAt φ m := by
  intro P r h0r hrm hrl p J hJ x v hxv hcom
  have C := compat_of_rel φ hwf P m (hE P) p J hJ
  obtain ⟨β, hβ, hx, hv, hr⟩ := hS P r h0r hrm hrl p x v (C x v hxv) (fun l h0 h1 => by
    obtain ⟨z, ρ, hz, hxz, hvz, hzρ, hρ⟩ := hcom l h0 h1
    exact ⟨z, ρ, hz, C x z hxz, C v z hvz, C z ρ hzρ, hρ⟩)
  exact ⟨β, hβ.1, hβ.2.1, hβ.2.2, hx, hv, hr⟩

/-- **The verdict from the semantic witness**: everything about the machine is proved; what is left is a
property of the genuine paths of each union. -/
theorem sat_of_semWitness (hwf : WF φ) (hS : ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 → SemWitnessAt φ m)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ :=
  sat_of_rowWitness φ hwf (fun m h hE => rowWitness_of_sem φ hwf m hE (hS m h)) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PinDeath.sat_of_semWitness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_semWitness

-- ============================================================
-- The semantic witness: the ends that fix the variable are free
-- ============================================================

/-- At the pinned step, a node compatible with a node of `r` *is* that node. -/
theorem compat_pin_eq (P : List NodeId) (m : Nat) (p : NodeId) (z ρ : PathNodeId)
    (hz : z.id.step = ρ.id.step) (h : Compat φ P m p z ρ) : z = ρ := by
  obtain ⟨β, _, hβz, hβρ⟩ := h
  rw [← hβz, ← hβρ, hz]

/-- **The semantic witness for the wide ends only.** Stated constructively, like `SideKeepFarAt`: the
case where `x` or `v` fixes the pinned variable is given. -/
def SemWitnessFarAt (m : Nat) : Prop :=
  ∀ (P : List NodeId) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ (p : NodeId) (x v : PathNodeId), Compat φ P m p x v →
      (∀ l, 0 ≤ l → l < (m : Int) + 2 →
        ∃ z ρ, z.id.step = l ∧ Compat φ P m p x z ∧ Compat φ P m p v z ∧ Compat φ P m p z ρ ∧ ρ.id = r) →
      let Goal := ∃ β, InUnion φ P m p β ∧ canon φ β x.id.step = x ∧ canon φ β v.id.step = v ∧
        selOfAssign φ β r.step = r
      ((PinClause.Fixes φ x (r.step / 2).toNat ∨ PinClause.Fixes φ v (r.step / 2).toNat) → Goal) → Goal

/-- **An end that fixes the pinned variable closes the witness.** At `r`'s own step the common node is a
node of `r` (`compat_pin_eq`), so there is a path through that end and `r`; the end fixes the variable, so
the path of `x → v` takes `r` too. -/
theorem semWitness_of_far (m : Nat) (hS : SemWitnessFarAt φ m) : SemWitnessAt φ m := by
  intro P r h0r hrm hrl p x v hxv hcom
  refine hS P r h0r hrm hrl p x v hxv hcom (fun hfix => ?_)
  obtain ⟨β₁, hβ₁, cx, cv⟩ := hxv
  obtain ⟨z, ρ, hzs, hxz, hvz, hzρ, hρ⟩ := hcom r.step h0r (by omega)
  have hzρs : z.id.step = ρ.id.step := by rw [hzs, hρ]
  have e := compat_pin_eq φ P m p z ρ hzρs hzρ
  subst e
  -- a path through the fixing end `y` and the node of `r`
  have close : ∀ y, canon φ β₁ y.id.step = y → Compat φ P m p y z →
      PinClause.Fixes φ y (r.step / 2).toNat → selOfAssign φ β₁ r.step = r := by
    intro y cy hyz hfy
    obtain ⟨β₂, _, c2y, c2z⟩ := hyz
    have hr2 : selOfAssign φ β₂ r.step = r := by
      have e1 : selOfAssign φ β₂ r.step = (canon φ β₂ r.step).id := rfl
      rw [e1, ← hzs, c2z, hρ]
    rw [PinVar.sel_local φ β₁ β₂ r.step h0r hrl (hfy β₁ β₂ cy c2y)]; exact hr2
  refine ⟨β₁, hβ₁, cx, cv, ?_⟩
  rcases hfix with hfx | hfv
  · exact close x cx hxz hfx
  · exact close v cv hvz hfv

/-- **The verdict from the wide semantic witness.** -/
theorem sat_of_semWitnessFar (hwf : WF φ)
    (hS : ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 → SemWitnessFarAt φ m)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ :=
  sat_of_semWitness φ hwf (fun m h => semWitness_of_far φ m (hS m h)) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PinDeath.sat_of_semWitnessFar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_semWitnessFar

-- ============================================================
-- The witness with closure
-- ============================================================

/-- **A closed family at `r`.** A relation between nodes that only relates compatible nodes, is symmetric,
has at every step a node common to the two ends of each of its pairs *inside the family*, and at `r`'s
step only reaches nodes of `r`. It is what the aggressive review leaves after pinning `r`, read without the
machine (`sideKeep_of_closed`). The link rules (parents and sons) are left out. -/
structure ClosedAt (P : List NodeId) (m : Nat) (p r : NodeId) (R : PathNodeId → PathNodeId → Prop) : Prop where
  compat : ∀ a b, R a b → Compat φ P m p a b
  sym : ∀ a b, R a b → R b a
  agg : ∀ a b, R a b → ∀ l, 0 ≤ l → l < (m : Int) + 2 → ∃ z, z.id.step = l ∧ R a z ∧ R b z
  pin : ∀ a z, R a z → z.id.step = r.step → z.id = r

/-- **The witness with closure, at line `m`.** Every pair of a closed family at `r` lies on one genuine
path through `r`. (Probe trace of the constructed case, 2026-09-19: the one-level witness `SemWitnessAt`
fails there, the aggressive review's fixpoint does not keep the entry.) -/
def ClosedWitnessAt (m : Nat) : Prop :=
  ∀ (P : List NodeId) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ (p : NodeId) (R : PathNodeId → PathNodeId → Prop), ClosedAt φ P m p r R →
      ∀ x v, R x v → ∃ β, InUnion φ P m p β ∧ canon φ β x.id.step = x ∧ canon φ β v.id.step = v ∧
        selOfAssign φ β r.step = r

/-- **Nothing borrowed, from the closed witness.** The pinned union's own relation is a closed family at
`r`: compatible by exactness, symmetric and closed by the aggressive review's fixpoint, and pinned by the
pin. -/
theorem sideKeep_of_closed (hwf : WF φ) (m : Nat)
    (hE : ∀ P, LineSoundL Full (pureAdvanceW φ (branchLine φ P m))) (hC : ClosedWitnessAt φ m) :
    SideKeepAt φ m := by
  intro P r h0r hrm hrl p J hJ hvX x v hxv
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  have hle : (m : Int) + 2 ≤ stepCount φ := by
    have := PinVar.lt_of_mapNodes φ _ p hsJ.onMap; omega
  have C := compat_of_rel φ hwf P m (hE P) p J hJ
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
  have hcs : X.current_step = (m : Int) + 2 := by rw [prX.step_eq, hcsJ]
  have RJ := rel_of_pruned J X hmJ.rctx.nodup prX
  have hcl : ClosedAt φ P m p r (Rel X) :=
    { compat := fun a b h => C a b (RJ a b h)
      sym := supX.sym
      agg := fun a b h l h0 h1 => by
        obtain ⟨z, haz, hbz, hz⟩ := supX.agg a b h l h0 (by rw [hcs]; exact h1)
        exact ⟨z, hz, haz, hbz⟩
      pin := fun a z h hz => cleanX z (supX.gow z (supX.dom a z h).2) hz }
  obtain ⟨β, hβ, hx, hv, hr⟩ := hC P r h0r hrm hrl p (Rel X) hcl x v hxv
  have bnd : ∀ a, Mem X a → 0 ≤ a.id.step ∧ a.id.step < (m : Int) + 2 := by
    intro a ha; have := EmbeddedSupport.mem_bounds X adX ha; rw [hcs] at this; exact this
  have bx := bnd x (supX.dom x v hxv).1
  have bv := bnd v (supX.dom x v hxv).2
  obtain ⟨kv, hkv, hson, hvS, hsc⟩ := PinVar.side_of_path φ hwf P m hle r p β hβ.1 hr hβ.2.1 hβ.2.2
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hsS := ConservationFilter.StateOkF_sent φ (ConservationFilter.Fsac φ 0) reviewAgg
    (ConservationFilter.prunes_Fsac φ 0) m kv hsok p hson hvS
  have hsS' : (sent φ kv.2 p).current_step = (m : Int) + 1 + 1 := hsS.step
  have hcsY : (filterAllAgg (sent φ kv.2 p) [r]).current_step = (m : Int) + 2 := by
    rw [(pruned_filterAllAgg _ _).step_eq, hsS']; omega
  have hrel := JoinSide.rel_of_chain _ _ hsc v.id.step x.id.step bv.1 (by rw [hcsY]; exact bv.2) bx.1
    (by rw [hcsY]; exact bx.2)
  rw [hx, hv] at hrel
  exact ⟨kv, hkv, hson, hvS, PickInduction.isValid_of_ChainG _ _ hsc.chain, hrel⟩

/-- **The verdict from the witness with closure.** -/
theorem sat_of_closedWitness (hwf : WF φ)
    (hC : ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 → ClosedWitnessAt φ m)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ := by
  have hE := (PinClause.joint φ hwf (fun m h hCm hadv =>
    PinClause.flipSat_of_sideKeep φ hwf m hCm hadv (sideKeep_of_closed φ hwf m hadv (hC m h)))
    (stepCount φ - 1).toNat).1 []
  rw [PinHistory.branchLine_nil] at hE
  refine RunInhabited.sat_of_lineSound φ hwf (fun kv' hkv' => ?_) kv hkv hv
  intro x n hx hx0 hx1 q hq0 hq1 _ hqn
  exact hE kv' hkv' x n hx hx0 hx1 q hq0 hq1 trivial hqn

/-- info: 'AbsSat.GraphPath.Model.PinDeath.sat_of_closedWitness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_closedWitness

-- ============================================================
-- The side, read from the chain of common owners
-- ============================================================

section ChainSide

open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Rel)
open AbsSat.GraphPath.Model.PinClause (SideKeepAt)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)

/-- The global owners an UP leaves: the old ones and the new top. -/
theorem addNode_gowners (g : GPathM) (d : NodeId) (t : String) :
    (addNode g d t).gowners = g.gowners ++ [newPid g d] := rfl

/-- **A chain of common owners, upwards.** From `a` to a node of the last step, every link is a parent
link of the state, both ends own each other, and every node owns `z`. The identifiers of the chain
(`map node`, `parent map node`) name a history: at the last step the chain's end is the top of one side
of the union. -/
inductive ChainUp (X : GPathM) (z : PathNodeId) : PathNodeId → PathNodeId → Prop where
  | top (t : PathNodeId) (h : t.id.step = X.current_step - 1) : ChainUp X z t t
  | link (c s t : PathNodeId) (ns : PNodeM) (hns : X.node? s = some ns) (hpar : c ∈ ns.parents)
      (h1 : Rel X c s) (h2 : Rel X s c) (h3 : Rel X s z) (hrest : ChainUp X z s t) : ChainUp X z c t

/-- **A chain of common owners of a pair.** Like `ChainUp`, but every node of the chain owns both ends
of the pair. Probe `chainfam` (2026-09-19): the family of pairs whose chain ends at a given top, kept
only where the side itself carries them, satisfies every closure rule of a support — 0 failures. -/
inductive ChainUp2 (X : GPathM) (a z : PathNodeId) : PathNodeId → PathNodeId → Prop where
  | top (t : PathNodeId) (h : t.id.step = X.current_step - 1) : ChainUp2 X a z t t
  | link (c s t : PathNodeId) (ns : PNodeM) (hns : X.node? s = some ns) (hpar : c ∈ ns.parents)
      (h1 : Rel X c s) (h2 : Rel X s c) (h3 : Rel X s a) (h4 : Rel X s z)
      (hrest : ChainUp2 X a z s t) : ChainUp2 X a z c t

/-- **The family a top names**: pairs the pinned union keeps, that hang on the top `t`, that the side's
send carries both ways, and whose chain of common owners reaches `t`. -/
def ChainFam (X S : GPathM) (t a b : PathNodeId) : Prop :=
  Rel X a b ∧ Rel X a t ∧ Rel X b t ∧ Rel S a b ∧ Rel S b a ∧
    (ChainUp2 X a b a t ∨ ChainUp2 X b a b t)

/-- **The side of a live pair, read from its chain, at line `m`.** Every entry of a pinned union has a
chain of common owners up to the top of a side, and that side's pinned send keeps the entry.

Measured (probes `chainside`, `chainside2`, `history`, 2026-09-19): 13.4 M live entries, 0 entries
without such a chain, 0 entries whose chain's side fails to carry them, and — following the chain back
line by line — 16.2 M checks of "the entry is in the table of the state the chain names", 0 failures. -/
def ChainSideAt (m : Nat) : Prop :=
  ∀ (P : List NodeId) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ p J, (p, J) ∈ pureAdvanceW φ (branchLine φ P m) → isValid (filterAllAgg J [r]) = true →
      ∀ x v, Rel (filterAllAgg J [r]) x v →
        ∃ kv ∈ branchLine φ P m, p ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 p) = true ∧
          ChainUp (filterAllAgg J [r]) v x (topOf p kv.1) ∧
          isValid (filterAllAgg (sent φ kv.2 p) [r]) = true ∧
          Rel (filterAllAgg (sent φ kv.2 p) [r]) x v

/-- **Every top node of a union comes from a side** — with no exactness, straight from how the line is
built: a send adds exactly one node at the new step, `⟨p, key⟩`, and a union only merges nodes. -/
theorem advance_top_node (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId) (J : GPathM)
    (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m)) (n : PNodeM) (hn : n ∈ J.nodes)
    (hts : n.id.id.step = (m : Int) + 1) :
    ∃ kv ∈ branchLine φ P m, p ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 p) = true ∧
      n.id = topOf p kv.1 ∧
      ∃ ns, (sent φ kv.2 p).node? n.id = some ns ∧ ∀ q ∈ n.owners, q ∈ ns.owners := by
  have hl := branchLine_inv φ hwf P m
  have step : ∀ kv ∈ branchLine φ P m, ∀ d ∈ mapSons φ kv.1.step kv.1.index, ∀ acc,
      (∀ d' B', (d', B') ∈ acc → ∀ n' ∈ B'.nodes, n'.id.id.step = (m : Int) + 1 →
        ∃ kv' ∈ branchLine φ P m, d' ∈ mapSons φ kv'.1.step kv'.1.index ∧
          isValid (sent φ kv'.2 d') = true ∧ n'.id = topOf d' kv'.1 ∧
          ∃ ns, (sent φ kv'.2 d').node? n'.id = some ns ∧ ∀ q ∈ n'.owners, q ∈ ns.owners) →
      (∀ d' B', (d', B') ∈ sendToW φ kv.2 acc d → ∀ n' ∈ B'.nodes, n'.id.id.step = (m : Int) + 1 →
        ∃ kv' ∈ branchLine φ P m, d' ∈ mapSons φ kv'.1.step kv'.1.index ∧
          isValid (sent φ kv'.2 d') = true ∧ n'.id = topOf d' kv'.1 ∧
          ∃ ns, (sent φ kv'.2 d').node? n'.id = some ns ∧ ∀ q ∈ n'.owners, q ∈ ns.owners) := by
    intro kv hkv d hd acc hacc
    rw [BranchLines.sendToW_eq]
    by_cases hv : isValid (sent φ kv.2 d) = true
    · rw [if_pos hv]
      -- the only node of the send at the new step is its top
      have hsok : StateOkF φ m kv := hl.1.2 kv hkv
      have hmkv : MInv φ kv.2 := hl.2 kv hkv
      have hvF := ClauseReview.valid_pinned φ kv.2 d hv
      have heq : sent φ kv.2 d = addNode (ClauseReview.pinnedAt φ kv.2 d) d "" := by
        rw [ClauseReview.sent_eq]; unfold GPathM.up; rw [hvF]; rfl
      have hprF : Pruned kv.2 (ClauseReview.pinnedAt φ kv.2 d) :=
        Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
      have hcsF : (ClauseReview.pinnedAt φ kv.2 d).current_step = (m : Int) + 1 := by
        rw [hprF.step_eq, hsok.step]
      have hmpF : (ClauseReview.pinnedAt φ kv.2 d).map_parent = some kv.1 := by
        rw [hprF.map_parent_eq, hsok.par]
      have hRF : ReadableAgg (ClauseReview.pinnedAt φ kv.2 d) :=
        ⟨_, _, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmkv.rctx, rfl⟩
      have hbelow : ∀ x ∈ (ClauseReview.pinnedAt φ kv.2 d).nodes,
          x.id.id.step < (ClauseReview.pinnedAt φ kv.2 d).current_step :=
        (RCtx_of_readableAgg _ hRF).below
      have htopSent : ∀ n' ∈ (sent φ kv.2 d).nodes, n'.id.id.step = (m : Int) + 1 →
          n'.id = topOf d kv.1 := by
        intro n' hn' hs
        rw [heq] at hn'
        have := RunNoBorrow.tops_addNode (ClauseReview.pinnedAt φ kv.2 d) d "" hbelow n' hn'
          (by rw [hcsF]; exact hs)
        rw [this, hmpF]; rfl
      have hndS : NodupIds (sent φ kv.2 d) :=
        (ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv d hd hv).rctx.nodup
      intro d' B' hB' n' hn' hs'
      rcases BranchLines.insert_src acc d (sent φ kv.2 d) d' B' hB' with ⟨hdd, hcase⟩ | ⟨hmem, _⟩
      · subst hdd
        rcases hcase with rfl | ⟨e, he, rfl⟩
        · exact ⟨kv, hkv, hd, hv, htopSent n' hn' hs', n',
            node?_of_mem hndS n' hn', fun q hq => hq⟩
        · unfold doJoin at hn'
          by_cases hok : okJoin e (sent φ kv.2 d') = true
          · rw [if_pos hok] at hn'
            rcases BranchRun.mem_join_nodes_src hn' with ⟨a, ha, hid, hown, _⟩ | hsent
            · obtain ⟨kv', hkv', hson', hv', hid', ns, hns, hsub⟩ :=
                hacc _ _ he a ha (by rw [← hid]; exact hs')
              refine ⟨kv', hkv', hson', hv', by rw [hid]; exact hid', ns, by rw [hid]; exact hns,
                fun q hq => ?_⟩
              rcases hown q hq with hqa | ⟨b, hb, hbid, hqb⟩
              · exact hsub q hqa
              · -- the other side's node with the same id is this side's top, so the sides agree
                have hbs : b.id.id.step = (m : Int) + 1 := by rw [hbid, ← hid]; exact hs'
                have hbtop : b.id = topOf d' kv.1 := htopSent b hb hbs
                have hkeys : kv'.1 = kv.1 := by
                  have heq : topOf d' kv'.1 = topOf d' kv.1 := by rw [← hid', ← hbid, hbtop]
                  simpa [topOf] using heq
                have hsame : kv' = kv := PureDriver.key_inj _ hl.1.1 kv' hkv' kv hkv hkeys
                subst hsame
                have hb2 : (sent φ kv'.2 d').node? a.id = some b := by
                  rw [← hbid]; exact node?_of_mem hndS b hb
                rw [hns] at hb2
                have : ns = b := Option.some.inj hb2
                rw [this]; exact hqb
            · exact ⟨kv, hkv, hd, hv, htopSent n' hsent hs', n',
                node?_of_mem hndS n' hsent, fun q hq => hq⟩
          · rw [if_neg hok] at hn'
            exact hacc _ _ he n' hn' hs'
      · exact hacc d' B' hmem n' hn' hs'
    · rw [if_neg hv]; exact hacc
  exact BranchLines.advance_inv φ
    (fun acc => ∀ d' B', (d', B') ∈ acc → ∀ n' ∈ B'.nodes, n'.id.id.step = (m : Int) + 1 →
      ∃ kv' ∈ branchLine φ P m, d' ∈ mapSons φ kv'.1.step kv'.1.index ∧
        isValid (sent φ kv'.2 d') = true ∧ n'.id = topOf d' kv'.1 ∧
        ∃ ns, (sent φ kv'.2 d').node? n'.id = some ns ∧ ∀ q ∈ n'.owners, q ∈ ns.owners)
    (branchLine φ P m) step (by intro d B hB; cases hB) p J hJ n hn hts

/-- **The owners of a live top belong to its own side.** The top of a side exists only in that side, so
everything the pinned union hangs on it is a node of that side's send — no union mixes in. -/
theorem top_owner_in_side (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId) (J : GPathM)
    (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m)) (Q : List NodeId)
    (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m)
    (a : PathNodeId) (ha : Rel (filterAllAgg J Q) (topOf p kv.1) a) :
    ∃ ns, (sent φ kv.2 p).node? (topOf p kv.1) = some ns ∧ a ∈ ns.owners := by
  have hl := branchLine_inv φ hwf P m
  obtain ⟨n, hn, hao, _⟩ := ha
  obtain ⟨n0, hn0, hid, hown, _⟩ := (pruned_filterAllAgg J Q).nodes_derived n
    (List.mem_of_find?_eq_some hn)
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hps : p.step = (m : Int) + 1 := mapNodes_step φ _ p hsJ.onMap
  have hts : n0.id.id.step = (m : Int) + 1 := by
    have hnid : n.id = topOf p kv.1 := node?_id_eq _ _ n hn
    rw [← hid, hnid]
    show p.step = (m : Int) + 1
    exact hps
  obtain ⟨kv', hkv', hson', hv', hid', ns, hns, hsub⟩ := advance_top_node φ hwf P m p J hJ n0 hn0 hts
  have hne : n0.id = topOf p kv.1 := by rw [← hid]; exact node?_id_eq _ _ n hn
  have hkeys : kv'.1 = kv.1 := by
    have heq : topOf p kv'.1 = topOf p kv.1 := by rw [← hid', hne]
    simpa [topOf] using heq
  have hsame : kv' = kv := PureDriver.key_inj _ hl.1.1 kv' hkv' kv hkv hkeys
  subst hsame
  exact ⟨ns, by rw [← hne]; exact hns, hsub a (hown a hao)⟩

/-- **A send keeps its owners among its global owners.** The state under the new top is a review
fixpoint, where this holds, and the new top is a global owner of the send. -/
theorem sent_ownGow (hwf : WF φ) (m : Nat) (kv : NodeId × GPathM) (hsok : StateOkF φ m kv)
    (hmkv : MInv φ kv.2) (p : NodeId) (hson : p ∈ mapSons φ kv.1.step kv.1.index)
    (hvS : isValid (sent φ kv.2 p) = true) :
    ∀ pid n, (sent φ kv.2 p).node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < (sent φ kv.2 p).current_step → q ∈ (sent φ kv.2 p).gowners := by
  have hvF := ClauseReview.valid_pinned φ kv.2 p hvS
  have heq : sent φ kv.2 p = addNode (ClauseReview.pinnedAt φ kv.2 p) p "" := by
    rw [ClauseReview.sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  have hrcW : Reader.RCtx (filterWeakAll kv.2 (weakReqOfCnf φ p)) :=
    RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmkv.rctx
  obtain ⟨h0, _, hform⟩ := ReaderAgg.filterAllAgg_form (filterWeakAll kv.2 (weakReqOfCnf φ p)) hrcW
    (reqOfCnf φ p)
  have hFgow : ∀ pid n, (ClauseReview.pinnedAt φ kv.2 p).node? pid = some n → ∀ q ∈ n.owners,
      0 ≤ q.id.step → q.id.step < (ClauseReview.pinnedAt φ kv.2 p).current_step →
      q ∈ (ClauseReview.pinnedAt φ kv.2 p).gowners := by
    intro pid n hn q hq hq0 hq1
    show q ∈ (ClauseReview.pinnedAt φ kv.2 p).gowners
    rw [show ClauseReview.pinnedAt φ kv.2 p = review h0 from hform] at hn hq1 ⊢
    exact Candidates.owner_mem_gowners h0 (by rw [← hform]; exact hvF) pid n hn q hq hq0 hq1
  have hbelowF := (RCtx_of_readableAgg _
    (show ReadableAgg (ClauseReview.pinnedAt φ kv.2 p) from ⟨_, _, hrcW, rfl⟩)).below
  have hmS := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv p hson hvS
  have hrcF := RCtx_of_readableAgg _
    (show ReadableAgg (ClauseReview.pinnedAt φ kv.2 p) from ⟨_, _, hrcW, rfl⟩)
  have hgow : (sent φ kv.2 p).gowners
      = (ClauseReview.pinnedAt φ kv.2 p).gowners ++ [newPid (ClauseReview.pinnedAt φ kv.2 p) p] := by
    rw [heq, addNode_gowners]
  have hcs : (sent φ kv.2 p).current_step = (ClauseReview.pinnedAt φ kv.2 p).current_step + 1 := by
    rw [heq, addNode_current]
  intro pid n hn q hq hq0 hq1
  have hnmem : n ∈ (sent φ kv.2 p).nodes := List.mem_of_find?_eq_some hn
  rw [hgow]
  -- the new top is always a global owner
  have newOk : q = newPid (ClauseReview.pinnedAt φ kv.2 p) p → q ∈
      (ClauseReview.pinnedAt φ kv.2 p).gowners ++ [newPid (ClauseReview.pinnedAt φ kv.2 p) p] := by
    intro h; exact List.mem_append_right _ (by rw [h]; exact List.mem_singleton_self _)
  -- an owner below the new step is a global owner of the state under it
  have oldOk : ∀ n0 ∈ (ClauseReview.pinnedAt φ kv.2 p).nodes, q ∈ n0.owners →
      q ∈ (ClauseReview.pinnedAt φ kv.2 p).gowners ++ [newPid (ClauseReview.pinnedAt φ kv.2 p) p] := by
    intro n0 hn0 hq0'
    by_cases hstep : q.id.step < (ClauseReview.pinnedAt φ kv.2 p).current_step
    · exact List.mem_append_left _
        (hFgow n0.id n0 (node?_of_mem hrcF.nodup n0 hn0) q hq0' hq0 hstep)
    · -- at the new step, the only node is the new top
      obtain ⟨nq, hnq, hnqid⟩ := hmS.own n hnmem q hq
      refine newOk ?_
      have hqs : nq.id.id.step = (ClauseReview.pinnedAt φ kv.2 p).current_step := by
        rw [hnqid]; rw [hcs] at hq1; omega
      have hnq2 : nq ∈ (addNode (ClauseReview.pinnedAt φ kv.2 p) p "").nodes := by
        rw [← heq]; exact hnq
      have htop := RunNoBorrow.tops_addNode (ClauseReview.pinnedAt φ kv.2 p) p "" hrcF.below nq hnq2 hqs
      rw [hnqid] at htop
      exact htop
  have hnmem2 : n ∈ ((ClauseReview.pinnedAt φ kv.2 p).nodes.map
      (upMap (ClauseReview.pinnedAt φ kv.2 p) p) ++
      [addOwner (newPid (ClauseReview.pinnedAt φ kv.2 p) p)
        (upNode (ClauseReview.pinnedAt φ kv.2 p) p "")]) := by
    rw [← addNode_nodes, ← heq]; exact hnmem
  rcases List.mem_append.mp hnmem2 with hold | hnew
  · obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp hold
    rw [upMap_owners] at hq
    rcases List.mem_append.mp hq with hq' | hq'
    · exact oldOk n0 hn0 hq'
    · exact newOk (List.mem_singleton.mp hq')
  · rw [List.mem_singleton.mp hnew] at hq
    show q ∈ _ ++ _
    simp only [addOwner, upNode] at hq
    rcases List.mem_append.mp hq with hq' | hq'
    · exact List.mem_append_left _ hq'
    · exact newOk (List.mem_singleton.mp hq')

/-- **What hangs on a live top is a global owner and a node of that side.** This is the `gow` and `node`
part of a support of the side: no closure rule involved. -/
theorem top_owner_gowner (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId) (J : GPathM)
    (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m)) (Q : List NodeId)
    (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m)
    (hson : p ∈ mapSons φ kv.1.step kv.1.index) (hvS : isValid (sent φ kv.2 p) = true)
    (a : PathNodeId) (ha : Rel (filterAllAgg J Q) (topOf p kv.1) a)
    (h0 : 0 ≤ a.id.step) (h1 : a.id.step < (sent φ kv.2 p).current_step) :
    a ∈ (sent φ kv.2 p).gowners ∧ Mem (sent φ kv.2 p) a := by
  have hl := branchLine_inv φ hwf P m
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  obtain ⟨ns, hns, hmem⟩ := top_owner_in_side φ hwf P m p J hJ Q kv hkv a ha
  have hg := sent_ownGow φ hwf m kv hsok hmkv p hson hvS (topOf p kv.1) ns hns a hmem h0 h1
  have hmS := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv p hson hvS
  exact ⟨hg, JoinSide.mem_of_hasNode hmS.rctx.nodup (hmS.rctx.gn a hg)⟩

/-- **The only top a top hangs on is itself.** A side's top owns only its own side's nodes, and that
side has exactly one node at the last step. -/
theorem tops_unique (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId) (J : GPathM)
    (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m)) (Q : List NodeId)
    (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m)
    (hson : p ∈ mapSons φ kv.1.step kv.1.index) (hvS : isValid (sent φ kv.2 p) = true)
    (t' : PathNodeId) (ht' : Rel (filterAllAgg J Q) (topOf p kv.1) t')
    (hts : t'.id.step = (m : Int) + 1) : t' = topOf p kv.1 := by
  have hl := branchLine_inv φ hwf P m
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  obtain ⟨ns, hns, hmem⟩ := top_owner_in_side φ hwf P m p J hJ Q kv hkv t' ht'
  have hmS := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv p hson hvS
  obtain ⟨nq, hnq, hnqid⟩ := hmS.own ns (List.mem_of_find?_eq_some hns) t' hmem
  have hvF := ClauseReview.valid_pinned φ kv.2 p hvS
  have heq : sent φ kv.2 p = addNode (ClauseReview.pinnedAt φ kv.2 p) p "" := by
    rw [ClauseReview.sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  have hrcW : Reader.RCtx (filterWeakAll kv.2 (weakReqOfCnf φ p)) :=
    RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmkv.rctx
  have hrcF := RCtx_of_readableAgg _
    (show ReadableAgg (ClauseReview.pinnedAt φ kv.2 p) from ⟨_, _, hrcW, rfl⟩)
  have hcsF : (ClauseReview.pinnedAt φ kv.2 p).current_step = (m : Int) + 1 := by
    rw [(Pruned.trans (ConservationCore.pruned_filterWeakAll _ _)
      (pruned_filterAllAgg _ _) : Pruned kv.2 (ClauseReview.pinnedAt φ kv.2 p)).step_eq, hsok.step]
  have hmpF : (ClauseReview.pinnedAt φ kv.2 p).map_parent = some kv.1 := by
    rw [(Pruned.trans (ConservationCore.pruned_filterWeakAll _ _)
      (pruned_filterAllAgg _ _) : Pruned kv.2 (ClauseReview.pinnedAt φ kv.2 p)).map_parent_eq, hsok.par]
  have hnq2 : nq ∈ (addNode (ClauseReview.pinnedAt φ kv.2 p) p "").nodes := by
    rw [← heq]; exact hnq
  have htop := RunNoBorrow.tops_addNode (ClauseReview.pinnedAt φ kv.2 p) p "" hrcF.below nq hnq2
    (by rw [hnqid, hcsF]; exact hts)
  rw [hnqid, hmpF] at htop
  exact htop

/-- **Nothing borrowed, when the chain names the side.** -/
theorem sideKeep_of_chainSide (m : Nat) (hC : ChainSideAt φ m) : SideKeepAt φ m := by
  intro P r h0r hrm hrl p J hJ hvX x v hxv
  obtain ⟨kv, hkv, hson, hvS, _, hvY, hrel⟩ := hC P r h0r hrm hrl p J hJ hvX x v hxv
  exact ⟨kv, hkv, hson, hvS, hvY, hrel⟩

/-- **The verdict when the chain names the side.** -/
theorem sat_of_chainSide (hwf : WF φ) (hC : ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 → ChainSideAt φ m)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ :=
  PinClause.sat_of_sideKeep φ hwf (fun m h => sideKeep_of_chainSide φ m (hC m h)) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PinDeath.sat_of_chainSide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_chainSide

end ChainSide

end AbsSat.GraphPath.Model.PinDeath
