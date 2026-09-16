-- lean_project/AbsSat/GraphPath/Model/ConservationCore.lean
import AbsSat.GraphPath.Model.PureDriverImproves

/-!
# The conservation argument, minus the filter

What `ConservationImproves`, `ConservationPins` and `ConservationFilter` all need before any
particular filter enters: the shape facts a state carries (`ShapeOk`), the `up` step over an
arbitrary narrowing (`chainSound_up_of_pruned`), and the two facts about the weak filter every one
of them instantiates.

Split out so the conservation law can be proved once, generically, without the module that proves it
having to import one of its own instances.
-/

namespace AbsSat.GraphPath.Model.ConservationCore

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf weakReqOfCnf_sound)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit mem_insertPure
  mem_insertPure_of_ne key_inj isValid_of_grown insertPure_keys_some insertPure_keys_none
  isValid_initSeed)
open AbsSat.GraphPath.Model.PureDriverImproves

-- ============================================================
-- The weak filter is a pruning
-- ============================================================

theorem pruned_filterWeak (g : GPathM) (e : Int × List NodeId) : Pruned g (filterWeak g e) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n hn := ⟨n, hn, rfl, fun _ hq => hq, fun _ hp => hp⟩

theorem pruned_filterWeakAll (g : GPathM) (ws : List (Int × List NodeId)) :
    Pruned g (filterWeakAll g ws) :=
  pruned_foldl _ pruned_filterWeak ws g

-- ============================================================
-- A sound chain through the weak sets survives the weak filter
-- ============================================================

theorem ChainSound_filterWeak (g : GPathM) (e : Int × List NodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (he : ∀ k, 0 ≤ k → k < g.current_step → k = e.1 → (sel k).id ∈ e.2) :
    ChainSound (filterWeak g e) sel := by
  obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
  refine ⟨⟨hchain, howned, ?_⟩, hself, hson, hroot⟩
  intro k hlo hhi
  simp only [filterWeak, List.mem_filter]
  refine ⟨hgow k hlo hhi, ?_⟩
  have hstepk := (hchain.1 k hlo hhi).2
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem]
  by_cases hk : k = e.1
  · exact Or.inr (he k hlo hhi hk)
  · exact Or.inl (by rw [hstepk]; exact hk)

theorem ChainSound_filterWeakAll (ws : List (Int × List NodeId)) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      (∀ e ∈ ws, ∀ k, 0 ≤ k → k < g.current_step → k = e.1 → (sel k).id ∈ e.2) →
      ChainSound (filterWeakAll g ws) sel := by
  induction ws with
  | nil => intro g sel h _; exact h
  | cons e rest ih =>
    intro g sel h hws
    exact ih (filterWeak g e) sel (ChainSound_filterWeak g e sel h (hws e List.mem_cons_self))
      (fun e' he' => hws e' (List.mem_cons_of_mem _ he'))

-- ============================================================
-- The shape facts the conservation argument reads
-- ============================================================

/-- Nodes below the current step, and `MachineOk`: all `ChainSound_upFiltering`
asks of the state besides the chain. -/
def ShapeOk (g : GPathM) : Prop :=
  (∀ n ∈ g.nodes, n.id.id.step < g.current_step) ∧ MachineOk g

theorem ShapeOk_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : ShapeOk g) : ShapeOk g' :=
  ⟨Certifies.nodes_below_of_pruned hpr h.1, MachineOk_of_pruned hpr h.2⟩

theorem ShapeOk_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    ShapeOk (GPathM.initSeed d title) := by
  refine ⟨?_, Certifies.MachineOk_initSeed d title⟩
  intro n hn
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  rw [initSeed_current]
  show d.step < 1
  omega

theorem ShapeOk_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (h : ShapeOk g) : ShapeOk (addNode g d title) := by
  refine ⟨?_, MachineOk_addNode g d title h.2⟩
  intro n hn
  rw [addNode_current]
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with hmem | hmem
  · obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hmem
    have hid : n.id = m.id := by rw [← hEq]; exact upMap_id g d m
    rw [hid]
    have := h.1 m hm
    omega
  · rcases List.mem_singleton.mp hmem with rfl
    have hid : (addOwner (newPid g d) (upNode g d title)).id.id = d := rfl
    rw [hid]
    omega

theorem ShapeOk_upFilteringWeak (g : GPathM) (ws : List (Int × List NodeId))
    (reqs : List NodeId) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (h : ShapeOk g) :
    ShapeOk (upFilteringWeak g ws reqs d title) := by
  have hpr : Pruned g (filterAll (filterWeakAll g ws) reqs) :=
    Pruned.trans (pruned_filterWeakAll g ws) (pruned_filterAll _ reqs)
  have hf := ShapeOk_of_pruned hpr h
  simp only [upFilteringWeak, GPathM.up]
  split
  · exact ShapeOk_addNode _ d title (by rw [hpr.step_eq]; exact hd) hf
  · exact hf

theorem ShapeOk_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : ShapeOk g₁) (h₂ : ShapeOk g₂) : ShapeOk (join g₁ g₂) := by
  refine ⟨?_, Certifies.MachineOk_join g₁ g₂ h₁.2⟩
  have hcs₂ : g₂.current_step = g₁.current_step := (grown_join_right g₁ g₂ hok).step_eq.symm
  intro n hn
  show n.id.id.step < g₁.current_step
  rw [GownersNodes.join_nodes] at hn
  rcases List.mem_append.mp hn with hmem | hmem
  · obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hmem
    have hid : n.id = m.id := by
      rw [← hEq]
      cases g₂.node? m.id with
      | some q => rfl
      | none => rfl
    rw [hid]
    exact h₁.1 m hm
  · have := h₂.1 n (List.mem_filter.mp hmem).1
    omega


variable (φ : Cnf) (a : Assign)

/-- **`Conservation`'s `up` step, on any pruning of the state.** If `gw` narrows
`g` and still carries the assignment's chain, the hard filter, the review and
`addNode` keep it, extended by the assignment's next node. -/
theorem chainSound_up_of_pruned (hwf : WF φ) (g gw : GPathM) (hpr : Pruned g gw)
    (hshape : ShapeOk g) (sel : Int → PathNodeId) (hselw : ChainSound gw sel)
    (hids : ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k)
    (title : String) :
    ∃ sel', ChainSound (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
          (selOfAssign φ a g.current_step) title) sel'
      ∧ (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
          (selOfAssign φ a g.current_step) title).current_step = g.current_step + 1
      ∧ ∀ k, 0 ≤ k → k < g.current_step + 1 → (sel' k).id = selOfAssign φ a k := by
  have hgs : gw.current_step = g.current_step := hpr.step_eq
  have hreqs : ∀ req ∈ reqOfCnf φ (selOfAssign φ a g.current_step),
      0 ≤ req.step → req.step < gw.current_step → (sel req.step).id = req := by
    intro req hreq hr0 hr1
    rw [hids req.step hr0 (by omega)]
    exact reqSat_selOfAssign φ hwf a g.current_step req hreq
  have hpf := pruned_filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))
  have hfil : ChainSound (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) sel :=
    ChainSound_filterAll gw _ sel hselw hreqs
  have hvalid : isValid (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) = true :=
    PickInduction.isValid_of_ChainG _ sel hfil.chain
  have hshf : ShapeOk (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) :=
    ShapeOk_of_pruned (Pruned.trans hpr hpf) hshape
  have hd : (selOfAssign φ a g.current_step).step
      = (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))).current_step := by
    rw [hpf.step_eq, hgs, selOfAssign_step]
  have hshapeEq : upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title
      = addNode (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) title := by
    simp only [upFiltering, GPathM.up, hvalid, if_pos]
  have hcur : (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title).current_step = g.current_step + 1 := by
    rw [hshapeEq, addNode_current, hpf.step_eq, hgs]
  refine ⟨extend (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
    (selOfAssign φ a g.current_step) sel, ?_, hcur, ?_⟩
  · exact ChainSound_upFiltering gw _ _ title hvalid hd hshf.1 hshf.2 sel hselw hreqs
  · intro k hk0 hk
    if he : k = g.current_step then
      have hextend : extend (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
          (selOfAssign φ a g.current_step) sel g.current_step
          = newPid (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
            (selOfAssign φ a g.current_step) := by
        simp only [extend, if_pos (hpf.step_eq.trans hgs).symm]
      rw [he, hextend]
      rfl
    else
      rw [extend_below (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) sel k (by rw [hpf.step_eq, hgs]; omega)]
      exact hids k hk0 (by omega)

theorem stepCount_pos : (0 : Int) < stepCount φ := by
  simp only [stepCount]; omega

end AbsSat.GraphPath.Model.ConservationCore
