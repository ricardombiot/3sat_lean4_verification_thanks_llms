-- lean_project/AbsSat/GraphPath/Model/OwnersInvariants.lean
import AbsSat.GraphPath.Model.GPathM
import AbsSat.GraphPath.Model.Reachable
import AbsSat.GraphPath.Model.Denot

/-!
Phase F5: `ReqFiltered` invariant + Lemma L1.

**Verified (0 sorry):**
- L1.a: `initSeed_ReqFiltered`
- L1.b1: `filterRequire_preserves_ReqFiltered`
- L1.b2: `filterRequire_cleans_gowner`
- Bridge: `OwnersSubset_preserves_ReqFiltered`

**Pending (4 sorry):**
- `review_preserves_ReqFiltered` — blocked by `mem_updateAtGo_narrow`
  (Lean `split`/`match` on Bool in induction context consumes binder)
- `upFiltering_ReqFiltered` — needs `addNode` expansion logic
- `join_preserves_ReqFiltered` — needs `mergeNode` owner analysis
- `L1_cor` — needs wiring of `PairwiseOwned` to `ReqFiltered`
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
    (hreqs_distinct : ∀ r₁ r₂, r₁ ∈ reqOf d → r₂ ∈ reqOf d → r₁.step = r₂.step → r₁ = r₂) :
    ReqFiltered reqOf (GPathM.upFiltering g (reqOf d) d title) := by
  let g' := GPathM.filterAll g (reqOf d)
  have h_g' : ReqFiltered reqOf g' := filterAll_preserves_ReqFiltered reqOf h (reqOf d)
  dsimp [GPathM.upFiltering, GPathM.up]
  split
  · -- Case 1: isValid g' → addNode g' d title
    -- Old nodes: owners := old_owners ++ [pid]
    -- New node: owners := g'.gowners ++ [pid]
    let pid : PathNodeId := { id := d, parent_id := g'.map_parent }
    dsimp [ReqFiltered, GPathM.addNode]
    intro n hn req hreq q hq hstep_q
    -- Decompose hn: simp gives n ∈ map (append-pid) ... ∨ n = newNode_after_pid
    simp at hn
    rcases hn with (hn_map | hn_new)
    · -- n from old node: hn_map gives n_pre ∈ intermediate, n = n_pre after owners-append
      rcases hn_map with ⟨n_pre, hn_pre_mem, hn_eq⟩
      subst hn_eq
      -- n.owners = n_pre.owners ++ [pid]
      rw [List.mem_append] at hq
      rcases hq with (hq_old | hq_pid)
      · -- q ∈ n_pre.owners; n_pre is from map-update-sons g'.nodes OR is newNode
        -- Decompose hn_pre_mem
        have h_decomp : (∃ n_orig ∈ g'.nodes, (fun n' =>
          if (GPathM.line g' (g'.current_step - 1)).map (·.id) |>.contains n'.id then
          { n' with sons := n'.sons ++ [pid] } else n') n_orig = n_pre) ∨ n_pre = newNode := by
          simpa [List.mem_append, List.mem_map, List.mem_singleton] using hn_pre_mem
        rcases h_decomp with (⟨n_orig, hn_orig_mem, hn_pre_eq⟩ | hn_new_pre)
        · subst hn_pre_eq
          -- q ∈ (sons-updated n_orig).owners = n_orig.owners
          apply h_g' n_orig hn_orig_mem req ?_ q hq_old hstep_q
          simpa using hreq
        · simp at hn_new_pre; subst hn_new_pre
          apply filterAll_cleans_gowner g (reqOf d) req q hreq hq_old hstep_q
      · -- q = pid: impossible by pid_safe
        simp at hq_pid; subst hq_pid
        have h_decomp : (∃ n_orig ∈ g'.nodes, (fun n' =>
          if (GPathM.line g' (g'.current_step - 1)).map (·.id) |>.contains n'.id then
          { n' with sons := n'.sons ++ [pid] } else n') n_orig = n_pre) ∨ n_pre = newNode := by
          simpa [List.mem_append, List.mem_map, List.mem_singleton] using hn_pre_mem
        rcases h_decomp with (⟨n_orig, hn_orig_mem, hn_pre_eq⟩ | hn_new_pre)
        · subst hn_pre_eq
          rcases filterAll_mem_subset g (reqOf d) n_orig hn_orig_mem with ⟨n_g, hn_g_mem, h_id_eq⟩
          have hreq' : req ∈ reqOf n_g.id.id := by simpa [h_id_eq] using hreq
          have hpid_step : pid.id.step = g.current_step := rfl
          have h_safe := pid_safe reqOf h_reach n_g hn_g_mem pid hpid_step req hreq'
          exact (h_safe hstep_q).elim
        · simp at hn_pre_new; subst hn_pre_new
          have h_back : req.step < d.step := hreqs_back req hreq
          rw [hstep] at h_back
          rw [← hstep] at hstep_q
          omega
    · -- n is the new node (after owners = g'.gowners ++ [pid])
      simp at hn_new; subst hn_new
      rw [List.mem_append] at hq
      rcases hq with (hq_gown | hq_pid)
      · apply filterAll_cleans_gowner g (reqOf d) req q hreq hq_gown hstep_q
      · simp at hq_pid; subst hq_pid
        have h_back : req.step < d.step := hreqs_back req hreq
        rw [hstep] at h_back
        rw [← hstep] at hstep_q
        omega
  · -- Case 2: not isValid g' → result is g'
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
    (h₂ : ReqFiltered reqOf g₂) (hok : GPathM.okJoin g₁ g₂) :
    ReqFiltered reqOf (GPathM.join g₁ g₂) := by
  dsimp [ReqFiltered, GPathM.join]
  intro n hn req hreq q hq hstep
  simp at hn
  rcases hn with (hn_map | hn_filter)
  · rcases List.mem_map.mp hn_map with ⟨n₁, hn₁, hn_eq⟩
    match hg₂ : GPathM.node? g₂ n₁.id with
    | none => subst hn_eq; exact h₁ n₁ hn₁ req hreq q hq hstep
    | some m =>
      subst hn_eq
      rcases mergeNode_owners_subset n₁ m q hq with (hq₁ | hq₂)
      · exact h₁ n₁ hn₁ req hreq q hq₁ hstep
      · have hm : m ∈ g₂.nodes := by
          dsimp [GPathM.node?] at hg₂
          induction g₂.nodes with
          | nil => simp at hg₂
          | cons x xs ih' =>
            simp [List.find?] at hg₂
            split at hg₂
            · injection hg₂ with h; subst h
              exact List.mem_cons_self _ _
            · exact List.mem_cons_of_mem _ (ih' hg₂)
        exact h₂ m hm req hreq q hq₂ hstep
  · simp at hn_filter
    rcases hn_filter with ⟨hn_mem, _⟩
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
      chain_step_eq g sel j h_chain hj_lo hj_hi
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
