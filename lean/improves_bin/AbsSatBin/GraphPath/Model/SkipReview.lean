-- lean/improves_bin/AbsSatBin/GraphPath/Model/SkipReview.lean
import AbsSatBin.GraphPath.Model.NodeInvariant
import AbsSatBin.GraphPath.Model.MapReachable

/-!
# `SkipExact`, reduced to the surviving old nodes — **new** (bin map)

`SkipExact` (in `NodeInvariant`) asks: when the UP skips a prohibited window, the review that
follows leaves every node on a sound chain. This module proves everything in that statement
except one clause, and names the clause.

**What is proved.**

* The review keeps every sound chain (`ChainSound_review`), so a node of the reviewed state that
  already lay on a sound chain of the un-reviewed state still does (`SupportedS_review_of_chains`).
* Every node of the **new row** lies on a sound chain of `addNode`: the chain of one of its
  parents, extended — and that extension is the row node itself, which is not prohibited
  (`row_supported`).
* An **old node** lies on a sound chain of `addNode` as soon as it lies on a sound chain of the
  state before whose extension is not prohibited (`old_supported`).

**What is left** is `SkipChain`: every old node that *survives the review* lies on a sound chain
of the state before whose extension is not prohibited. `SkipExact_of_SkipChain` closes the gap.

On the bin map an extension is prohibited exactly when the chain stands on `L2 = 0` with `L1 = 0`
below it and goes to `L3 = 0` (`CnfMapBin.clauseWindow_prohibited_iff`). So `SkipChain` says:
**the survivors of the review lie on a sound chain that picks `L1 = 1`** — a one-value pin two
steps below the top, the same shape as the pins of `HardStepExact`.
-/

namespace AbsSatBin.GraphPath.Model.SkipReview

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.NodeInvariant

/-- **The review only needs the chains that were already there.** -/
theorem SupportedS_review_of_chains (h : GPathM)
    (hchains : ∀ pid n, (review h).node? pid = some n →
      ∃ sel, ChainSound h sel ∧ sel pid.id.step = pid) :
    SupportedS (review h) := by
  intro pid n hn
  obtain ⟨sel, hsel, htop⟩ := hchains pid n hn
  exact ⟨sel, ChainSound_review h sel hsel, htop⟩

/-- **A node of the new row lies on a sound chain of `addNode`**, whatever was skipped: the chain
of one of its parents, extended, ends on it, and it is in the row, so not prohibited. -/
theorem row_supported (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (hsup : SupportedS g) (hinh : ∃ sel, ChainSound g sel)
    (q : PathNodeId) (hq : q ∈ newRowIds g d forb) :
    ∃ sel, ChainSound (addNode g d title forb) sel ∧ sel q.id.step = q := by
  have hqf : forb q = false := not_forb_of_mem_newRowIds g d forb q hq
  have hstepq : q.id.step = g.current_step := by
    rw [mapId_of_mem_newRowIds g d forb q hq]; exact hd
  by_cases hpos : 0 < g.current_step
  · obtain ⟨p, hp⟩ : ∃ p, p ∈ rowParents g d q := by
      obtain ⟨r, hr', hrq⟩ := exists_shift_of_mem_newRowIds g d forb q hpos hq
      exact ⟨r, List.mem_filter.mpr ⟨hr', beq_iff_eq.mpr hrq.symm⟩⟩
    have hpmem : p ∈ newParents g := rowParents_subset g d q p hp
    have hpline : p ∈ (g.line (g.current_step - 1)).map (·.id) := by
      unfold newParents at hpmem; rwa [if_pos hpos] at hpmem
    obtain ⟨np, hnp, hnq⟩ := List.mem_map.mp hpline
    have hmemp : np ∈ g.nodes := (List.mem_filter.mp hnp).1
    have hsomep : (g.node? p).isSome = true := by
      have := node?_isSome_of_mem g np hmemp; rwa [hnq] at this
    obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp hsomep
    obtain ⟨sel, hsel, htop⟩ := hsup p mp hmp
    have hpstep : p.id.step = g.current_step - 1 := by
      rw [← hnq]; exact eq_of_beq (List.mem_filter.mp hnp).2
    have hselp : sel (g.current_step - 1) = p := by rw [← hpstep]; exact htop
    have hext : extendPid g d sel = q := by
      unfold extendPid
      rw [if_pos hpos, hselp]
      exact shiftPid_of_mem_rowParents g d q p hp
    refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hsel
      (by rw [hext]; exact hqf), ?_⟩
    rw [hstepq, extend_top, hext]
  · obtain ⟨sel, hsel⟩ := hinh
    have hext : extendPid g d sel = q := by
      unfold extendPid
      rw [if_neg hpos]
      exact (eq_root_of_mem_newRowIds_zero g d forb hpos q hq).symm
    refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hsel
      (by rw [hext]; exact hqf), ?_⟩
    rw [hstepq, extend_top, hext]

/-- **An old node rides up any sound chain whose extension is allowed.** -/
theorem old_supported (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (pid : PathNodeId) (hstep : pid.id.step < g.current_step)
    (sel : Int → PathNodeId) (hsel : ChainSound g sel) (htop : sel pid.id.step = pid)
    (hf : forb (extendPid g d sel) = false) :
    ∃ sel', ChainSound (addNode g d title forb) sel' ∧ sel' pid.id.step = pid :=
  ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hsel hf,
    by rw [extend_below g d sel pid.id.step hstep]; exact htop⟩

variable (reqOf : NodeId → List NodeId) (forb : PathNodeId → Bool)

/-- **What is left of `SkipExact`.** Every *old* node that survives the review after a skipped
window lies on a sound chain of the filtered state whose extension is not prohibited. -/
def SkipChain : Prop :=
  ∀ (g : GPathM) (d : NodeId) (title : String), Reachable reqOf forb g →
    d.step = g.current_step → isValid g = true → SupportedS g →
    isValid (filterAll g (reqOf d)) = true → SupportedS (filterAll g (reqOf d)) →
    skipsWindow (filterAll g (reqOf d)) d forb = true →
    isValid (review (addNode (filterAll g (reqOf d)) d title forb)) = true →
    ∀ pid n, (review (addNode (filterAll g (reqOf d)) d title forb)).node? pid = some n →
      pid.id.step < g.current_step →
      ∃ sel, ChainSound (filterAll g (reqOf d)) sel ∧ sel pid.id.step = pid ∧
        forb (extendPid (filterAll g (reqOf d)) d sel) = false

/-- **`SkipExact` reduces to `SkipChain`.** Row nodes and the review are handled here; only the
surviving old nodes are left to `SkipChain`. -/
theorem SkipExact_of_SkipChain (h : SkipChain reqOf forb) : SkipExact reqOf forb := by
  intro g d title hr hstep hgv hsup hfv hfsup hsk hv
  have hpr := pruned_filterAll g (reqOf d)
  have hbelow := Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf forb hr)
  have hmok := MachineOk_of_pruned hpr (Certifies.MachineOk_reachable reqOf forb g hr)
  have hpos : 0 < (filterAll g (reqOf d)).current_step := by
    rw [hpr.step_eq]; exact pos_reachable reqOf forb g hr
  have hinh := chain_of_SupportedS _ (GownersNodes.GN_filterAll g (reqOf d)
    (GownersNodes.GN_reachable reqOf forb g hr)) hfsup hfv hpos
  have hd : d.step = (filterAll g (reqOf d)).current_step := by rw [hpr.step_eq]; exact hstep
  apply SupportedS_review_of_chains
  intro pid n hn
  -- `pid` is a node of `addNode` (the review only removes)
  have hmem : n ∈ (review (addNode (filterAll g (reqOf d)) d title forb)).nodes :=
    List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq _ pid n hn
  obtain ⟨m, hm, hmid, _, _⟩ := (pruned_review _).nodes_derived n hmem
  rw [addNode_nodes] at hm
  rcases List.mem_append.mp hm with hl | hrow
  · -- an old node: `SkipChain`
    obtain ⟨m₀, hm₀, hEq⟩ := List.mem_map.mp hl
    have hstepp : pid.id.step < g.current_step := by
      have := hbelow m₀ hm₀
      rw [hpr.step_eq] at this
      rw [← hid, hmid, ← hEq, upMap_id]
      exact this
    obtain ⟨sel, hsel, htop, hf⟩ := h g d title hr hstep hgv hsup hfv hfsup hsk hv pid n hn hstepp
    exact old_supported _ d title forb hd hbelow hmok pid (by rw [hpr.step_eq]; exact hstepp)
      sel hsel htop hf
  · -- a node of the new row
    obtain ⟨q, hq, rfl⟩ := (mem_newRow_iff _ d title forb m).mp hrow
    rw [rowNode_id] at hmid
    have hqp : q = pid := by rw [← hmid, hid]
    subst hqp
    exact row_supported _ d title forb hd hbelow hmok hfsup hinh q hq

/-- info: 'AbsSatBin.GraphPath.Model.SkipReview.SkipExact_of_SkipChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkipExact_of_SkipChain

-- ============================================================
-- On the bin map: the survivors must lie on a chain that picks `L1 = 1`
-- ============================================================

section Bin

open AbsSatBin.Cnf AbsSatBin.GraphMap.CnfMapBin

/-- **`SkipChain` on the bin map.** Every old node that survives the review after a skipped
window lies on a sound chain of the filtered state that picks index `1` two steps below the top
— the first literal `L1` of the clause whose window was skipped. -/
def SkipChainBin (φ : Cnf) : Prop :=
  ∀ (g : GPathM) (d : NodeId) (title : String),
    Reachable (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ) g →
    d.step = g.current_step → isValid g = true → SupportedS g →
    isValid (filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)) = true →
    SupportedS (filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)) →
    skipsWindow (filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)) d (isProhibited φ) = true →
    isValid (review (addNode (filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)) d title
      (isProhibited φ))) = true →
    ∀ pid n, (review (addNode (filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)) d title
        (isProhibited φ))).node? pid = some n →
      pid.id.step < g.current_step →
      ∃ sel, ChainSound (filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)) sel ∧
        sel pid.id.step = pid ∧ (sel (g.current_step - 2)).id.index ≠ 0

/-- **A chain that does not pick `0` two steps below the top has an allowed extension.** The
extension's grandparent is the chain's pick two steps below (parent coherence), and a
prohibited window needs it to be `0`. -/
theorem extendPid_not_prohibited (φ : Cnf) (g : GPathM) (d : NodeId) (sel : Int → PathNodeId)
    (hsel : ChainSound g sel) (hpmp : ParentId.PMP g)
    (h2 : 2 ≤ g.current_step → (sel (g.current_step - 2)).id.index ≠ 0) :
    isProhibited φ (extendPid g d sel) = false := by
  unfold extendPid
  by_cases hpos : 0 < g.current_step
  · rw [if_pos hpos]
    by_cases h1 : 1 < g.current_step
    · have hpar := ParentId.parentId_coherent g hpmp sel hsel.chain.1 (g.current_step - 2)
        (by omega) (by omega)
      rw [show g.current_step - 2 + 1 = g.current_step - 1 by omega] at hpar
      have hidx := h2 (by omega)
      cases hp : isProhibited φ (shiftPid (sel (g.current_step - 1)) d) with
      | false => rfl
      | true =>
        exfalso
        simp only [isProhibited, shiftPid, Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨_, hgp⟩ := hp
        rw [hpar] at hgp
        simp only [Option.some.injEq] at hgp
        exact hidx (by rw [hgp])
    · have hz : g.current_step - 1 = 0 := by omega
      have hroot : (sel (g.current_step - 1)).parent_id = none := by rw [hz]; exact hsel.root_shape.1
      simp [isProhibited, shiftPid, hroot]
  · rw [if_neg hpos]
    exact MapReachable.isProhibited_root φ d

/-- **`SkipChainBin` gives `SkipChain`, hence `SkipExact`.** -/
theorem SkipChain_of_bin (φ : Cnf) (h : SkipChainBin φ) :
    SkipChain (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ) := by
  intro g d title hr hstep hgv hsup hfv hfsup hsk hv pid n hn hstepp
  obtain ⟨sel, hsel, htop, hidx⟩ := h g d title hr hstep hgv hsup hfv hfsup hsk hv pid n hn hstepp
  have hpr := pruned_filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)
  have hpmp := ParentId.PMP_filterAll (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ) g
    (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d) hr
  refine ⟨sel, hsel, htop, extendPid_not_prohibited φ _ d sel hsel hpmp ?_⟩
  intro _
  rw [hpr.step_eq]
  exact hidx

theorem SkipExact_of_bin (φ : Cnf) (h : SkipChainBin φ) :
    SkipExact (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ) :=
  SkipExact_of_SkipChain _ _ (SkipChain_of_bin φ h)

end Bin

/-- info: 'AbsSatBin.GraphPath.Model.SkipReview.SkipExact_of_bin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkipExact_of_bin

end AbsSatBin.GraphPath.Model.SkipReview
