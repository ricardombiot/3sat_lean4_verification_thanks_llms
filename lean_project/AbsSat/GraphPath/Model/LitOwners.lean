-- lean_project/AbsSat/GraphPath/Model/LitOwners.lean
import AbsSat.GraphPath.Model.ParentOwners
import AbsSat.GraphPath.Model.UnitPropagation

/-!
# Owners agree with the literals a node's id fixes

A node `n` fixes literals through the requirements of its own map node and of its parent's map node
(`FixMap n m`). The owners table agrees with those literals, in every state the machine builds
(`LitInv_reachable`):

* `own` — an owner of `n` with a requirement at the step of a fixed literal `l` requires exactly `l`;
* `twin` — an owner of `n` at the step of a requirement of a fixed literal `l` is that requirement.

For the map of a formula, where a negation node requires its value node, these say that the owners
of `n` at the value step and at the negation step of a variable `n` fixes both carry the value `n`
fixes.

Both come from `addNode`. The new node is handed the global owners of a valid filtered state `F`;
every global owner of `F` is a valid node whose owners reach every step inside the global owners,
and the global owners at a fixed literal's step are that literal (the pins of the new node, or the
key's requirements). `ReqFiltered` gives `own`, and `OwnedCompatible` gives `twin`.

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210, 9,885 kept and filtered states): the
value-step/negation-step agreement holds in 679,824 checks with no exception.
-/

namespace AbsSat.GraphPath.Model.LitOwners

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.ParentOwners

/-- `m` is the node's own map node or its parent's. -/
def FixMap (n : PNodeM) (m : NodeId) : Prop := m = n.id.id ∨ n.id.parent_id = some m

section Inv

variable (reqOf : NodeId → List NodeId)

structure LitInv (g : GPathM) : Prop where
  own : ∀ n ∈ g.nodes, ∀ m, FixMap n m → ∀ l ∈ reqOf m, ∀ w ∈ n.owners, ∀ req ∈ reqOf w.id,
    req.step = l.step → req = l
  twin : ∀ n ∈ g.nodes, ∀ m, FixMap n m → ∀ l ∈ reqOf m, ∀ req ∈ reqOf l, ∀ w ∈ n.owners,
    w.id.step = req.step → w.id = req

theorem LitInv_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : LitInv reqOf g) :
    LitInv reqOf g' where
  own := fun n' hn' m hm l hl w hw req hreq hs => by
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
    have hm' : FixMap n m := by unfold FixMap at hm ⊢; rw [hid] at hm; exact hm
    exact h.own n hn m hm' l hl w (hown w hw) req hreq hs
  twin := fun n' hn' m hm l hl req hreq w hw hs => by
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
    have hm' : FixMap n m := by unfold FixMap at hm ⊢; rw [hid] at hm; exact hm
    exact h.twin n hn m hm' l hl req hreq w (hown w hw) hs

theorem LitInv_join (g₁ g₂ : GPathM) (h₁ : LitInv reqOf g₁) (h₂ : LitInv reqOf g₂) :
    LitInv reqOf (join g₁ g₂) := by
  refine ⟨?_, ?_⟩
  · intro n hn m hm l hl w hw req hreq hs
    rcases mem_join_nodes' hn with ⟨a, ha, hid, hown⟩ | hn2
    · have hma : FixMap a m := by unfold FixMap at hm ⊢; rw [hid] at hm; exact hm
      rcases hown w hw with hwa | ⟨b, hb, hbid, hwb⟩
      · exact h₁.own a ha m hma l hl w hwa req hreq hs
      · have hmb : FixMap b m := by unfold FixMap at hma ⊢; rw [hbid]; exact hma
        exact h₂.own b hb m hmb l hl w hwb req hreq hs
    · exact h₂.own n hn2 m hm l hl w hw req hreq hs
  · intro n hn m hm l hl req hreq w hw hs
    rcases mem_join_nodes' hn with ⟨a, ha, hid, hown⟩ | hn2
    · have hma : FixMap a m := by unfold FixMap at hm ⊢; rw [hid] at hm; exact hm
      rcases hown w hw with hwa | ⟨b, hb, hbid, hwb⟩
      · exact h₁.twin a ha m hma l hl req hreq w hwa hs
      · have hmb : FixMap b m := by unfold FixMap at hma ⊢; rw [hbid]; exact hma
        exact h₂.twin b hb m hmb l hl req hreq w hwb hs
    · exact h₂.twin n hn2 m hm l hl req hreq w hw hs

theorem LitInv_initSeed (hback : ∀ x, ∀ r ∈ reqOf x, r.step < x.step)
    (hdist : ∀ x, ∀ r₁ ∈ reqOf x, ∀ r₂ ∈ reqOf x, r₁.step = r₂.step → r₁ = r₂)
    (d : NodeId) (title : String) (hd : d.step = 0) : LitInv reqOf (initSeed d title) := by
  have hseed : initSeed d title = addNode empty d title := rfl
  have hnode : ∀ n ∈ (initSeed d title).nodes,
      n = PNodeM.mk { id := d, parent_id := none } title [] []
        [{ id := d, parent_id := none }] := by
    intro n hn
    rw [initSeed_nodes d title] at hn
    exact List.mem_singleton.mp hn
  have hfix : ∀ n ∈ (initSeed d title).nodes, ∀ m, FixMap n m → m = d := by
    intro n hn m hm
    rw [hnode n hn] at hm
    rcases hm with hm | hm
    · exact hm
    · exact absurd hm (by simp)
  have hown : ∀ n ∈ (initSeed d title).nodes, ∀ w ∈ n.owners,
      w = ({ id := d, parent_id := none } : PathNodeId) := by
    intro n hn w hw
    rw [hnode n hn] at hw
    exact List.mem_singleton.mp hw
  refine ⟨?_, ?_⟩
  · intro n hn m hm l hl w hw req hreq hs
    have hmd := hfix n hn m hm
    subst hmd
    have hwz := hown n hn w hw
    subst hwz
    exact hdist _ req hreq l hl hs
  · intro n hn m hm l hl req hreq w hw hs
    have hmd := hfix n hn m hm
    subst hmd
    have hwz := hown n hn w hw
    subst hwz
    have h1 := hback l req hreq
    have h2 := hback _ l hl
    have h3 : ({ id := m, parent_id := none } : PathNodeId).id.step = m.step := rfl
    omega

theorem LitInv_addNode (hback : ∀ x, ∀ r ∈ reqOf x, r.step < x.step)
    (hnonneg : ∀ x, ∀ r ∈ reqOf x, 0 ≤ r.step)
    (hdist : ∀ x, ∀ r₁ ∈ reqOf x, ∀ r₂ ∈ reqOf x, r₁.step = r₂.step → r₁ = r₂)
    (F : GPathM) (d : NodeId) (title : String) (h : LitInv reqOf F)
    (hd : d.step = F.current_step) (hbelow : ∀ n ∈ F.nodes, n.id.id.step < F.current_step)
    (hv : isValid F = true)
    (hownF : ∀ n ∈ F.nodes, ∀ k, 0 ≤ k → k < F.current_step →
      ∃ u ∈ n.owners, u.id.step = k ∧ u ∈ F.gowners)
    (hgn : ∀ q ∈ F.gowners, ∃ n ∈ F.nodes, n.id = q)
    (hrf : ReqFiltered reqOf F) (hoc : UnitPropagation.OwnedCompatible reqOf F)
    (hpi : ParentInv reqOf F)
    (hpin : ∀ q ∈ F.gowners, ∀ req ∈ reqOf d, q.id.step = req.step → q.id = req)
    (hkey : ∀ p, F.map_parent = some p → p.step + 1 = F.current_step)
    (htl : ParentId.TL F) (hpos : 0 < F.current_step) :
    LitInv reqOf (addNode F d title) := by
  -- a row identifier's parent record is `map_parent`, by `TL`
  have hrowpar : ∀ pid ∈ newRowIds F d, ∀ p, pid.parent_id = some p → F.map_parent = some p := by
    intro pid hpid p hp
    obtain ⟨r, hr, rfl⟩ := exists_shift_of_mem_newRowIds F d pid hpos hpid
    have hrp : (some r.id : Option NodeId) = some p := hp
    unfold newParents at hr
    rw [if_pos hpos] at hr
    obtain ⟨nr, hnr, hnrid⟩ := List.mem_map.mp hr
    have := htl nr (List.mem_filter.mp hnr).1 (eq_of_beq (List.mem_filter.mp hnr).2)
    rw [hnrid, hrp] at this
    exact this.symm
  -- the new node's fixed literals are pinned in `F`'s global owners, and sit below the top
  have hzfix : ∀ pid ∈ newRowIds F d, ∀ m, FixMap (rowNode F d title pid) m → ∀ l ∈ reqOf m,
      (∀ q ∈ F.gowners, q.id.step = l.step → q.id = l) ∧ 0 ≤ l.step ∧ l.step < F.current_step := by
    intro pid hpid m hm l hl
    rcases hm with hm | hm
    · have hmd : m = d := by
        rw [hm, rowNode_id, mapId_of_mem_newRowIds F d pid hpid]
      subst hmd
      exact ⟨fun q hq hs => hpin q hq l hl hs, hnonneg _ l hl, by have := hback _ l hl; omega⟩
    · have hp : F.map_parent = some m := hrowpar pid hpid m hm
      exact ⟨fun q hq hs => hpi.kp m hp q hq l hl hs, hnonneg _ l hl,
        by have := hback _ l hl; have := hkey m hp; omega⟩
  -- an old node's fixed literals: its owners there are the literal, and they sit below its step
  have hnfix : ∀ n ∈ F.nodes, ∀ m, FixMap n m → ∀ l ∈ reqOf m,
      (∀ u ∈ n.owners, u.id.step = l.step → u.id = l) ∧ 0 ≤ l.step ∧ l.step < n.id.id.step := by
    intro n hn m hm l hl
    rcases hm with hm | hm
    · subst hm
      exact ⟨fun u hu hs => hrf n hn l hl u hu hs, hnonneg _ l hl, hback _ l hl⟩
    · exact ⟨fun u hu hs => hpi.pr n hn m hm l hl u hu hs, hnonneg _ l hl,
        by have := hback _ l hl; have := hpi.ps n hn m hm; omega⟩
  refine ⟨?_, ?_⟩
  · intro n' hn' m hm l hl w hw req hreq hs
    rcases mem_addNode_nodes hn' with ⟨n, hn, rfl⟩ | ⟨pid, hpid, rfl⟩
    · have hmn : FixMap n m := by unfold FixMap at hm ⊢; rw [upMap_id] at hm; exact hm
      rw [upMap_owners] at hw
      rcases List.mem_append.mp hw with hw | hw
      · exact h.own n hn m hmn l hl w hw req hreq hs
      · -- the gained owner is a row id, so its requirements are `reqOf d`
        have hwd : w.id = d := mapId_of_mem_newRowIds F d w (gainedOwners_subset F d n w hw)
        rw [hwd] at hreq
        obtain ⟨hlit, hl0, hlt⟩ := hnfix n hn m hmn l hl
        obtain ⟨u, hu, hus, hug⟩ := hownF n hn l.step hl0 (by have := hbelow n hn; omega)
        have hul := hlit u hu hus
        have hureq := hpin u hug req hreq (by rw [hus, hs])
        rw [← hureq, hul]
    · rw [rowNode_owners] at hw
      obtain ⟨hpinned, hl0, hlt⟩ := hzfix pid hpid m hm l hl
      rcases rowOwners_mem_gowners_or_self F d pid w hw with hw | rfl
      · obtain ⟨x, hx, hxid⟩ := hgn w hw
        obtain ⟨u, hu, hus, hug⟩ := hownF x hx l.step hl0 hlt
        have hul := hpinned u hug hus
        have hreqx : req ∈ reqOf x.id.id := by rw [hxid]; exact hreq
        have hureq := hrf x hx req hreqx u hu (by rw [hus, hs])
        rw [← hureq, hul]
      · have hwd : w.id = d := mapId_of_mem_newRowIds F d w hpid
        have hreqd : req ∈ reqOf d := by rwa [hwd] at hreq
        rcases hm with hm | hm
        · have hmd : m = d := by rw [hm, rowNode_id, hwd]
          subst hmd
          exact hdist _ req hreqd l hl hs
        · have hent := hasStepEntry_of_isValid F hv l.step hl0 hlt
          simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
          obtain ⟨q, hq, hqs⟩ := hent
          have hql := hpinned q hq hqs
          have hqr := hpin q hq req hreqd (by rw [hqs, hs])
          rw [← hqr, hql]
  · intro n' hn' m hm l hl req hreq w hw hs
    rcases mem_addNode_nodes hn' with ⟨n, hn, rfl⟩ | ⟨pid, hpid, rfl⟩
    · have hmn : FixMap n m := by unfold FixMap at hm ⊢; rw [upMap_id] at hm; exact hm
      rw [upMap_owners] at hw
      rcases List.mem_append.mp hw with hw | hw
      · exact h.twin n hn m hmn l hl req hreq w hw hs
      · exfalso
        obtain ⟨_, _, hlt⟩ := hnfix n hn m hmn l hl
        have h1 := hback l req hreq
        have h2 := hbelow n hn
        rw [mapId_of_mem_newRowIds F d w (gainedOwners_subset F d n w hw)] at hs
        rw [hd] at hs
        omega
    · rw [rowNode_owners] at hw
      obtain ⟨hpinned, hl0, hlt⟩ := hzfix pid hpid m hm l hl
      rcases rowOwners_mem_gowners_or_self F d pid w hw with hw | rfl
      · obtain ⟨x, hx, hxid⟩ := hgn w hw
        obtain ⟨u, hu, hus, hug⟩ := hownF x hx l.step hl0 hlt
        have hul := hpinned u hug hus
        have hrequ : req ∈ reqOf u.id := by rw [hul]; exact hreq
        have hx' := hoc x hx u hu req hrequ (by rw [hxid]; exact hs)
        rw [← hxid]
        exact hx'
      · exfalso
        have h1 := hback l req hreq
        rw [mapId_of_mem_newRowIds F d w hpid] at hs
        rw [hd] at hs
        omega

/-- **Owners agree with the literals a node's id fixes, in every state the machine builds.** -/
theorem LitInv_reachable (hback : ∀ x, ∀ r ∈ reqOf x, r.step < x.step)
    (hnonneg : ∀ x, ∀ r ∈ reqOf x, 0 ≤ r.step)
    (hdist : ∀ x, ∀ r₁ ∈ reqOf x, ∀ r₂ ∈ reqOf x, r₁.step = r₂.step → r₁ = r₂)
    (g : GPathM) (h : Reachable reqOf g) : LitInv reqOf g := by
  induction h with
  | seed d title hstep _ => exact LitInv_initSeed reqOf hback hdist d title hstep
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    have hF := LitInv_of_pruned reqOf hpr ih
    dsimp only [GPathM.upFiltering, GPathM.up]
    split
    · next hv =>
      have hnd : NodupIds (filterAll g (reqOf d)) :=
        NodeIds.NodupIds_filterAll g (Reader.NodupIds_reachable reqOf g hr) (reqOf d)
      have htk := NodeInvariant.TopKey_of_pruned hpr (NodeInvariant.TopKey_reachable reqOf g hr)
      have hkey : ∀ p, (filterAll g (reqOf d)).map_parent = some p →
          p.step + 1 = (filterAll g (reqOf d)).current_step := by
        intro p hp
        have hpos : 0 < (filterAll g (reqOf d)).current_step := by
          rw [hpr.step_eq]; exact NodeInvariant.pos_reachable reqOf g hr
        have hent := hasStepEntry_of_isValid _ hv ((filterAll g (reqOf d)).current_step - 1)
          (by omega) (by omega)
        simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
        obtain ⟨q, hq, hqs⟩ := hent
        have htop := htk.2.2 q hq hqs
        rw [hp] at htop
        have hpq : p = q.id := Option.some.inj htop
        rw [hpq]
        omega
      refine LitInv_addNode reqOf hback hnonneg hdist _ d title hF
        (by rw [hpr.step_eq]; exact hstep)
        (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hr)) hv ?_ ?_
        (filterAll_preserves_ReqFiltered reqOf (L1 reqOf hr) (reqOf d))
        (UnitPropagation.OwnedCompatible_of_pruned reqOf hpr
          (UnitPropagation.OwnedCompatible_reachable reqOf hback hnonneg g hr))
        (ParentInv_of_pruned reqOf hpr (ParentInv_reachable reqOf hback g hr))
        (fun q hq req hreq hs => filterAll_cleans_gowner g (reqOf d) req q hreq hq hs) hkey
        (ParentId.TL_of_pruned hpr (ParentId.TL_reachable reqOf g hr))
        (by rw [hpr.step_eq]; exact NodeInvariant.pos_reachable reqOf g hr)
      · intro n hn k h0 hk
        have hnode := node?_of_mem hnd n hn
        have hvalid := review_node_valid ((reqOf d).foldl filterRequire g) hv n.id n hnode
        have hfix := review_owners_within_gowners ((reqOf d).foldl filterRequire g) hv n.id n hnode
        exact UnitPropagation.owner_at_step g (reqOf d) hv n hvalid hfix k h0
          (by rw [← hpr.step_eq]; exact hk)
      · intro q hq
        exact GownersNodes.GN_filterAll g (reqOf d) (GownersNodes.GN_reachable reqOf g hr) q hq
    · exact hF
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact LitInv_join reqOf g₁ g₂ ih₁ ih₂

end Inv

/-- info: 'AbsSat.GraphPath.Model.LitOwners.LitInv_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LitInv_reachable

end AbsSat.GraphPath.Model.LitOwners
