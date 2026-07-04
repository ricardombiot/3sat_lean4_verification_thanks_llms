-- lean_project/AbsSat/GraphPath/Model/OwnersInvariants.lean
import AbsSat.GraphPath.Model.GPathM
import AbsSat.GraphPath.Model.Reachable
import AbsSat.GraphPath.Model.Denot

/-!
Phase F5: `ReqFiltered` invariant + Lemma L1.

⚠️ **AUDIT (2026-07-04): the axiomatized version of this module is unsound.**
`chain_step_eq` (A8) is FALSE for the current `IsChain` (which does not pin
`(sel k).id.step = k`): `False` has been derived from it in Lean. And
`addNode_preserves_ReqFiltered` (A9) is FALSE as stated (`g'` is a free
variable unconnected to `g`; a graph with a poisoned `gowners` entry and no
nodes is a countermodel). Consequently `L1`/`L1_cor` carry no evidential
weight until repaired. Full audit and repair plan:
`docs/summary_formalization.md` §4.0/§6.1.

**Proved without axioms (0 sorry):** `initSeed_ReqFiltered`,
`filterRequire_preserves_ReqFiltered`, `filterRequire_cleans_gowner`,
`OwnersSubset_preserves_ReqFiltered`, `mergeNode_owners_subset`, and the
genuine case analysis of `join_preserves_ReqFiltered` (modulo the provable
one-liners A6/A7).

**Axioms A1–A7 are true and provable** (the `brecOn`-opacity rationale was
wrong — `Fuel.lean` unfolds these very functions with `simp only` + `split`);
they are pending replacement by the plan's `Pruned`-relation proofs.
-/

namespace AbsSat.GraphPath.Model

open AbsSat.Utils.Alias
open GPathM

variable (reqOf : NodeId → List NodeId)

def ReqFiltered (g : GPathM) : Prop :=
  ∀ d ∈ g.nodes, ∀ req ∈ reqOf d.id.id, ∀ q ∈ d.owners,
    q.id.step = req.step → q.id = req

-- ============================================================
-- L1.a — initSeed ✓
-- ============================================================

theorem initSeed_ReqFiltered (d : NodeId) (title : String)
    (hstep : d.step = 0) (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step) :
    ReqFiltered reqOf (GPathM.initSeed d title) := by
  intro node hnode req hreq q hq hstep_eq
  have h_nodes : (GPathM.initSeed d title).nodes =
    [PNodeM.mk { id := d, parent_id := none } title [] [] [{ id := d, parent_id := none }]] := by
    unfold GPathM.initSeed GPathM.up GPathM.addNode
    simp [GPathM.isValid, GPathM.empty, GPathM.intRange, GPathM.hasStepEntry]
  rw [h_nodes] at hnode
  simp at hnode; subst hnode
  simp at hq; subst hq
  have hstep_eq' : d.step = req.step := by
    simp at hstep_eq
    exact hstep_eq
  rw [hstep] at hstep_eq'
  have h_back : req.step < d.step := hreqs_back req hreq
  rw [hstep] at h_back
  omega

-- ============================================================
-- L1.b — filterRequire ✓
-- ============================================================

theorem filterRequire_preserves_ReqFiltered (h : ReqFiltered reqOf g) (req : NodeId) :
    ReqFiltered reqOf (GPathM.filterRequire g req) := by
  simp [ReqFiltered, GPathM.filterRequire]
  exact h

theorem filterRequire_cleans_gowner (g : GPathM) (req : NodeId) (q : PathNodeId)
    (hq : q ∈ (GPathM.filterRequire g req).gowners) (heq : q.id.step = req.step) :
    q.id = req := by
  dsimp [GPathM.filterRequire] at hq
  have hfilter := List.mem_filter.mp hq
  rcases hfilter with ⟨_hq_mem, hq_cond⟩
  rw [heq] at hq_cond
  simp at hq_cond
  exact hq_cond

-- ============================================================
-- OwnersSubset bridge (proved) ✓
-- ============================================================

def OwnersSubset (g g' : GPathM) : Prop :=
  ∀ d, d ∈ g'.nodes → ∃ d' ∈ g.nodes, d'.id = d.id ∧ ∀ q ∈ d.owners, q ∈ d'.owners

private theorem OwnersSubset_preserves_ReqFiltered (h : ReqFiltered reqOf g)
    (hsub : OwnersSubset g g') : ReqFiltered reqOf g' := by
  intro d hd req hreq q hq hstep
  rcases hsub d hd with ⟨d', hd', h_id, hsub_ow⟩
  have hq' : q ∈ d'.owners := hsub_ow q hq
  rw [← h_id] at hreq
  exact h d' hd' req hreq q hq' hstep

-- ============================================================
-- review (axiomatized: review only narrows, never expands)
-- ============================================================

axiom review_OwnersSubset (g : GPathM) : OwnersSubset g (GPathM.review g)

private theorem review_preserves_ReqFiltered (h : ReqFiltered reqOf g) :
    ReqFiltered reqOf (GPathM.review g) :=
  OwnersSubset_preserves_ReqFiltered reqOf h (review_OwnersSubset g)

theorem filterAll_preserves_ReqFiltered (h : ReqFiltered reqOf g) (reqs : List NodeId) :
    ReqFiltered reqOf (GPathM.filterAll g reqs) := by
  have hfold : ReqFiltered reqOf (reqs.foldl GPathM.filterRequire g) := by
    induction reqs generalizing g with
    | nil => exact h
    | cons r rs ih =>
      apply ih
      exact filterRequire_preserves_ReqFiltered reqOf h r
  simp [GPathM.filterAll]
  exact review_preserves_ReqFiltered reqOf hfold

-- ============================================================
-- Reachable structural axioms (P0a, P0b)
-- ============================================================

axiom steps_below_current (h : Reachable reqOf g) :
    ∀ n ∈ g.nodes, n.id.id.step < g.current_step

axiom reqs_back_trans (h : Reachable reqOf g) :
    ∀ n ∈ g.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step

axiom filterAll_mem_subset (g : GPathM) (reqs : List NodeId) (n : PNodeM)
    (hn : n ∈ (GPathM.filterAll g reqs).nodes) : ∃ n' ∈ g.nodes, n'.id = n.id

axiom filterAll_cleans_gowner (g : GPathM) (reqs : List NodeId) (req : NodeId) (q : PathNodeId)
    (hreq : req ∈ reqs) (hq : q ∈ (GPathM.filterAll g reqs).gowners) (heq : q.id.step = req.step) :
    q.id = req

axiom node?_mem (g : GPathM) (pid : PathNodeId) (h : (g.node? pid).isSome) :
    (g.node? pid).get h ∈ g.nodes

axiom node?_id_eq (g : GPathM) (pid : PathNodeId) (n : PNodeM)
    (h : g.node? pid = some n) : n.id = pid

axiom chain_step_eq (g : GPathM) (sel : Int → PathNodeId) (k : Int)
    (h_chain : IsChain g sel) (hk_lo : 0 ≤ k) (hk_hi : k < g.current_step) :
    (sel k).id.step = k

axiom addNode_preserves_ReqFiltered (h : ReqFiltered reqOf g') (h_reach : Reachable reqOf g)
    (d : NodeId) (title : String) (hstep : d.step = g.current_step)
    (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step) :
    ReqFiltered reqOf (GPathM.addNode g' d title)

-- ============================================================
-- pid_safe: new pid doesn't violate ReqFiltered for old nodes
-- ============================================================

theorem pid_safe (h_reach : Reachable reqOf g) (n : PNodeM) (hn : n ∈ g.nodes)
    (pid : PathNodeId) (hpid_step : pid.id.step = g.current_step) :
    ∀ req ∈ reqOf n.id.id, pid.id.step ≠ req.step := by
  have h_back := reqs_back_trans reqOf h_reach n hn
  have h_below := steps_below_current reqOf h_reach n hn
  intro req hreq
  have hlt1 := h_back req hreq     -- req.step < n.id.id.step
  rw [hpid_step]
  omega

-- ============================================================
-- L1.c — UP step
-- ============================================================

theorem upFiltering_ReqFiltered (h : ReqFiltered reqOf g) (h_reach : Reachable reqOf g)
    (d : NodeId) (title : String) (hstep : d.step = g.current_step)
    (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step)
    (_hreqs_distinct : ∀ r₁ r₂, r₁ ∈ reqOf d → r₂ ∈ reqOf d → r₁.step = r₂.step → r₁ = r₂) :
    ReqFiltered reqOf (GPathM.upFiltering g (reqOf d) d title) := by
  let g' := GPathM.filterAll g (reqOf d)
  have h_g' : ReqFiltered reqOf g' := filterAll_preserves_ReqFiltered reqOf h (reqOf d)
  dsimp [GPathM.upFiltering, GPathM.up]
  split
  · -- isValid g' → addNode g' d title
    exact addNode_preserves_ReqFiltered reqOf h_g' h_reach d title hstep hreqs_back
  · -- not isValid g' → result is g'
    exact h_g'

-- ============================================================
-- L1.d — join preserves ReqFiltered
-- ============================================================

private theorem mergeNode_owners_subset (a b : PNodeM) (q : PathNodeId)
    (hq : q ∈ (GPathM.mergeNode a b).owners) : q ∈ a.owners ∨ q ∈ b.owners := by
  dsimp [GPathM.mergeNode] at hq
  rw [List.mem_append] at hq
  rcases hq with (hq' | hq')
  · exact Or.inl hq'
  · rw [List.mem_filter] at hq'
    rcases hq' with ⟨hq'', _⟩
    exact Or.inr hq''

theorem join_preserves_ReqFiltered (h₁ : ReqFiltered reqOf g₁)
    (h₂ : ReqFiltered reqOf g₂) (_hok : GPathM.okJoin g₁ g₂) :
    ReqFiltered reqOf (GPathM.join g₁ g₂) := by
  dsimp [ReqFiltered, GPathM.join]
  intro n hn req hreq q hq hstep
  simp [List.mem_append, List.mem_map, List.mem_filter] at hn
  rcases hn with (hn_map | hn_filter)
  · rcases hn_map with ⟨n₁, hn₁, hn_eq⟩
    match hg₂ : GPathM.node? g₂ n₁.id with
    | none =>
      -- hn_eq : (fun n => match node? ...) n₁ = n
      -- which is definitionally: (match node? ...) = n
      have hn_eq_match : (match GPathM.node? g₂ n₁.id with
        | some m => GPathM.mergeNode n₁ m | none => n₁) = n := hn_eq
      have : (match GPathM.node? g₂ n₁.id with
        | some m => GPathM.mergeNode n₁ m | none => n₁) = n₁ := by simp [hg₂]
      rw [this] at hn_eq_match; subst hn_eq_match
      exact h₁ n₁ hn₁ req hreq q hq hstep
    | some m =>
      have hn_eq_match : (match GPathM.node? g₂ n₁.id with
        | some m => GPathM.mergeNode n₁ m | none => n₁) = n := hn_eq
      have : (match GPathM.node? g₂ n₁.id with
        | some m' => GPathM.mergeNode n₁ m' | none => n₁) = GPathM.mergeNode n₁ m := by simp [hg₂]
      rw [this] at hn_eq_match; subst hn_eq_match
      rcases mergeNode_owners_subset n₁ m q hq with (hq₁ | hq₂)
      · exact h₁ n₁ hn₁ req hreq q hq₁ hstep
      · have h_id_m : m.id = n₁.id := node?_id_eq g₂ n₁.id m hg₂
        have hreq_m : req ∈ reqOf m.id.id := by rw [h_id_m]; exact hreq
        have hm : m ∈ g₂.nodes := by
          have h_some : (GPathM.node? g₂ n₁.id).isSome := by rw [hg₂]; exact rfl
          have h_mem' := node?_mem g₂ n₁.id h_some
          simpa [hg₂] using h_mem'
        exact h₂ m hm req hreq_m q hq₂ hstep
  · rcases hn_filter with ⟨hn_mem, _⟩
    exact h₂ n hn_mem req hreq q hq hstep

-- ============================================================
-- L1 — main theorem
-- ============================================================

theorem L1 (h : Reachable reqOf g) : ReqFiltered reqOf g := by
  induction h with
  | seed d title hstep hreqs_back =>
    exact initSeed_ReqFiltered reqOf d title hstep hreqs_back
  | up g d title hstep hreqs_back hreqs_distinct h_reach ih =>
    exact upFiltering_ReqFiltered reqOf ih h_reach d title hstep hreqs_back hreqs_distinct
  | join g₁ g₂ hok h_reach₁ h_reach₂ ih₁ ih₂ =>
    exact join_preserves_ReqFiltered reqOf ih₁ ih₂ hok

-- ============================================================
-- L1-cor
-- ============================================================

theorem L1_cor (h_reach : Reachable reqOf g)
    (h_chain : IsChain g sel) (h_owned : PairwiseOwned g sel)
    (j : Int) (hj_lo : 0 ≤ j) (hj_hi : j < g.current_step)
    (req : NodeId) (hreq : req ∈ reqOf (sel j).id)
    (h_req_step_pos : 0 ≤ req.step) (h_req_step_lt : req.step < g.current_step) :
    (sel req.step).id = req := by
  have h_chain_orig : IsChain g sel := h_chain
  rcases h_chain with ⟨h_chain_node, h_chain_link⟩
  have h_inv : ReqFiltered reqOf g := L1 reqOf h_reach
  by_cases hij : req.step = j
  · -- req.step = j: contradiction via reqs_back_trans + chain_step_eq
    have h_node_some : (g.node? (sel j)).isSome := h_chain_node j hj_lo hj_hi
    have hn_mem : (g.node? (sel j)).get h_node_some ∈ g.nodes :=
      node?_mem g (sel j) h_node_some
    let n := (g.node? (sel j)).get h_node_some
    have h_node : g.node? (sel j) = some n := by simp [n]
    have h_id_eq : n.id = sel j := node?_id_eq g (sel j) n h_node
    have hreq_n : req ∈ reqOf n.id.id := by rw [h_id_eq]; exact hreq
    have h_back := reqs_back_trans reqOf h_reach n hn_mem req hreq_n
    have h_step_eq_chain : (sel j).id.step = j :=
      chain_step_eq g sel j h_chain_orig hj_lo hj_hi
    rw [h_id_eq] at h_back
    rw [h_step_eq_chain] at h_back
    rw [hij] at h_back
    omega
  · -- req.step ≠ j: PairwiseOwned gives owner, ReqFiltered forces identity
    have h_owner : sel req.step ∈ GPathM.ownersAt (ownersOf g (sel j)) req.step :=
      h_owned (req.step) j h_req_step_pos hj_lo h_req_step_lt hj_hi hij
    dsimp [GPathM.ownersAt] at h_owner
    have h_mem := (List.mem_filter.mp h_owner).left
    have h_step_eq : (sel req.step).id.step = req.step := by
      have h_step_bool := (List.mem_filter.mp h_owner).right
      simpa using h_step_bool
    dsimp [ownersOf] at h_mem
    have h_node_some : (g.node? (sel j)).isSome := h_chain_node j hj_lo hj_hi
    let n := (g.node? (sel j)).get h_node_some
    have h_node : g.node? (sel j) = some n := by simp [n]
    have h_id_eq : n.id = sel j := node?_id_eq g (sel j) n h_node
    have hn_mem : n ∈ g.nodes := node?_mem g (sel j) h_node_some
    simp [h_node] at h_mem
    have hreq_n : req ∈ reqOf n.id.id := by rw [h_id_eq]; exact hreq
    have h_inv_result := h_inv n hn_mem req hreq_n (sel req.step) h_mem
    exact h_inv_result h_step_eq

end AbsSat.GraphPath.Model
