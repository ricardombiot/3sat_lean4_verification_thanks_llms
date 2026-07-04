-- lean_project/AbsSat/GraphPath/Model/OwnersInvariants.lean
import AbsSat.GraphPath.Model.GPathM
import AbsSat.GraphPath.Model.Pruned
import AbsSat.GraphPath.Model.Reachable
import AbsSat.GraphPath.Model.Denot

/-!
Phase F5: `ReqFiltered` invariant + Lemma L1 — **axiom-free**
(`#print axioms L1` = `[propext, Quot.sound]`, guard-pinned below).

History: a first version of this module reached L1/L1_cor through 9 axioms,
two of which were false as stated (`chain_step_eq`, because `IsChain` did not
pin the selected node's step — `False` was derived from it — and
`addNode_preserves_ReqFiltered`, whose `g'` was unconnected to `g`). The
2026-07-04 audit (`docs/summary_formalization.md` §4.0) mandated the repair
executed here on 2026-07-05:

* `IsChain` now pins `(sel k).id.step = k`, so `chain_step_eq` is a
  projection, not an axiom;
* the addNode preservation lemma is stated over `filterAll g (reqOf d)` —
  the graph it is actually applied to — and proved;
* the remaining axioms (review narrowing, reachable structure, `node?`
  facts) are proved via the `Pruned` relation (`Pruned.lean`), using the
  same `simp only` + `split` technique as `Fuel.lean`.

The `#guard_msgs` blocks at the end of this file pin the axiom closure of
`L1` and `L1_cor` to Lean's built-ins only; the build fails if any project
axiom ever reappears.
-/

namespace AbsSat.GraphPath.Model

open AbsSat.Utils.Alias
open GPathM

variable (reqOf : NodeId → List NodeId)

def ReqFiltered (g : GPathM) : Prop :=
  ∀ d ∈ g.nodes, ∀ req ∈ reqOf d.id.id, ∀ q ∈ d.owners,
    q.id.step = req.step → q.id = req

-- ============================================================
-- initSeed: computed shape
-- ============================================================

private theorem initSeed_nodes (d : NodeId) (title : String) :
    (GPathM.initSeed d title).nodes =
      [PNodeM.mk { id := d, parent_id := none } title [] [] [{ id := d, parent_id := none }]] := by
  unfold GPathM.initSeed GPathM.up GPathM.addNode
  simp [GPathM.isValid, GPathM.empty, GPathM.intRange, GPathM.hasStepEntry]

private theorem initSeed_current (d : NodeId) (title : String) :
    (GPathM.initSeed d title).current_step = 1 := by
  unfold GPathM.initSeed GPathM.up GPathM.addNode
  simp [GPathM.isValid, GPathM.empty, GPathM.intRange, GPathM.hasStepEntry]

-- ============================================================
-- L1.a — initSeed
-- ============================================================

theorem initSeed_ReqFiltered (d : NodeId) (title : String)
    (hstep : d.step = 0) (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step) :
    ReqFiltered reqOf (GPathM.initSeed d title) := by
  intro node hnode req hreq q hq hstep_eq
  rw [initSeed_nodes] at hnode
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
-- L1.b — filterRequire
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
-- OwnersSubset bridge
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
-- review narrows (was axiom A1 — now via Pruned)
-- ============================================================

theorem review_OwnersSubset (g : GPathM) : OwnersSubset g (GPathM.review g) := by
  intro d hd
  obtain ⟨n, hn, hid, hown⟩ := (pruned_review g).nodes_derived d hd
  exact ⟨n, hn, hid.symm, hown⟩

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
-- filterAll facts (were axioms A4/A5 — now via Pruned)
-- ============================================================

theorem filterAll_mem_subset (g : GPathM) (reqs : List NodeId) (n : PNodeM)
    (hn : n ∈ (GPathM.filterAll g reqs).nodes) : ∃ n' ∈ g.nodes, n'.id = n.id := by
  obtain ⟨n', hn', hid, _⟩ := (pruned_filterAll g reqs).nodes_derived n hn
  exact ⟨n', hn', hid.symm⟩

private theorem foldl_filterRequire_cleans (g : GPathM) (reqs : List NodeId) :
    ∀ req ∈ reqs, ∀ q ∈ (reqs.foldl GPathM.filterRequire g).gowners,
      q.id.step = req.step → q.id = req := by
  induction reqs generalizing g with
  | nil => intro req h; cases h
  | cons r rs ih =>
    intro req hreq q hq heq
    simp only [List.foldl_cons] at hq
    rcases List.mem_cons.mp hreq with rfl | hmem
    · have hpr : Pruned (GPathM.filterRequire g req)
          (rs.foldl GPathM.filterRequire (GPathM.filterRequire g req)) :=
        pruned_foldl _ pruned_filterRequire rs _
      exact filterRequire_cleans_gowner g req q (hpr.gowners_sub q hq) heq
    · exact ih (GPathM.filterRequire g r) req hmem q hq heq

theorem filterAll_cleans_gowner (g : GPathM) (reqs : List NodeId) (req : NodeId) (q : PathNodeId)
    (hreq : req ∈ reqs) (hq : q ∈ (GPathM.filterAll g reqs).gowners) (heq : q.id.step = req.step) :
    q.id = req := by
  have hq' : q ∈ (reqs.foldl GPathM.filterRequire g).gowners := by
    have hpr : Pruned (reqs.foldl GPathM.filterRequire g) (GPathM.filterAll g reqs) := by
      dsimp only [GPathM.filterAll]
      exact pruned_review _
    exact hpr.gowners_sub q hq
  exact foldl_filterRequire_cleans g reqs req hreq q hq' heq

-- ============================================================
-- addNode membership decomposition
-- ============================================================

private theorem mem_addNode {g : GPathM} {d : NodeId} {title : String} {n' : PNodeM}
    (hn' : n' ∈ (GPathM.addNode g d title).nodes) :
    (∃ n ∈ g.nodes, n'.id = n.id ∧ n'.owners = n.owners ++ [⟨d, g.map_parent⟩]) ∨
    (n'.id = ⟨d, g.map_parent⟩ ∧ n'.owners = g.gowners ++ [⟨d, g.map_parent⟩]) := by
  simp only [GPathM.addNode] at hn'
  rcases List.mem_map.mp hn' with ⟨m, hm, hEq⟩
  subst hEq
  rcases List.mem_append.mp hm with hold | hnew
  · rcases List.mem_map.mp hold with ⟨n, hn, hEq2⟩
    subst hEq2
    refine Or.inl ⟨n, hn, ?_, ?_⟩
    · dsimp only
      split <;> split <;> rfl
    · dsimp only
      split <;> split <;> rfl
  · have hm' := List.mem_singleton.mp hnew
    subst hm'
    exact Or.inr ⟨rfl, rfl⟩

-- ============================================================
-- join membership decomposition
-- ============================================================

private theorem mem_join_nodes {g₁ g₂ : GPathM} {n : PNodeM}
    (hn : n ∈ (GPathM.join g₁ g₂).nodes) :
    (∃ n₁ ∈ g₁.nodes, n = n₁) ∨
    (∃ n₁ ∈ g₁.nodes, ∃ m ∈ g₂.nodes, m.id = n₁.id ∧ n = GPathM.mergeNode n₁ m) ∨
    n ∈ g₂.nodes := by
  dsimp only [GPathM.join] at hn
  rcases List.mem_append.mp hn with hmap | hfil
  · rcases List.mem_map.mp hmap with ⟨n₁, hn₁, hEq⟩
    match hg : GPathM.node? g₂ n₁.id with
    | none =>
      have hred : (match GPathM.node? g₂ n₁.id with
        | some m => GPathM.mergeNode n₁ m | none => n₁) = n := hEq
      have hstep : (match GPathM.node? g₂ n₁.id with
        | some m => GPathM.mergeNode n₁ m | none => n₁) = n₁ := by simp [hg]
      rw [hstep] at hred
      exact Or.inl ⟨n₁, hn₁, hred.symm⟩
    | some m =>
      have hred : (match GPathM.node? g₂ n₁.id with
        | some m' => GPathM.mergeNode n₁ m' | none => n₁) = n := hEq
      have hstep : (match GPathM.node? g₂ n₁.id with
        | some m' => GPathM.mergeNode n₁ m' | none => n₁) = GPathM.mergeNode n₁ m := by
        simp [hg]
      rw [hstep] at hred
      have hmm : m ∈ g₂.nodes := by
        have hs : (GPathM.node? g₂ n₁.id).isSome := by rw [hg]; rfl
        have hmem := node?_mem g₂ n₁.id hs
        simpa [hg] using hmem
      exact Or.inr (Or.inl ⟨n₁, hn₁, m, hmm, node?_id_eq g₂ n₁.id m hg, hred.symm⟩)
  · exact Or.inr (Or.inr (List.mem_filter.mp hfil).1)

-- ============================================================
-- Reachable structure (were axioms A2/A3 — now by induction)
-- ============================================================

/-- Steps are honest and requirements point strictly backward — one property
bundle so the `Reachable` induction is done once. -/
private def NodeStructure (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes,
    n.id.id.step < g.current_step ∧
    ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step

private theorem structure_pruned {g g' : GPathM} (hpr : Pruned g g')
    (h : NodeStructure reqOf g) : NodeStructure reqOf g' := by
  intro n' hn'
  obtain ⟨n, hn, hid, _⟩ := hpr.nodes_derived n' hn'
  obtain ⟨h1, h2⟩ := h n hn
  rw [hid, hpr.step_eq]
  exact ⟨h1, h2⟩

private theorem structure_addNode {g' : GPathM} (h : NodeStructure reqOf g')
    {d : NodeId} {title : String} (hd : d.step = g'.current_step)
    (hback : ∀ req, req ∈ reqOf d → req.step < d.step) :
    NodeStructure reqOf (GPathM.addNode g' d title) := by
  intro n' hn'
  have hcs : (GPathM.addNode g' d title).current_step = g'.current_step + 1 := rfl
  rcases mem_addNode hn' with ⟨n, hn, hid, _⟩ | ⟨hid, _⟩
  · obtain ⟨h1, h2⟩ := h n hn
    have hids : n'.id.id.step = n.id.id.step := by rw [hid]
    constructor
    · rw [hcs]; omega
    · intro req hreq
      have hreq' : req ∈ reqOf n.id.id := by rw [← hid]; exact hreq
      have := h2 req hreq'
      omega
  · have hids : n'.id.id = d := by rw [hid]
    constructor
    · rw [hcs, hids]; omega
    · intro req hreq
      rw [hids] at hreq ⊢
      exact hback req hreq

private theorem reachable_structure (h : Reachable reqOf g) : NodeStructure reqOf g := by
  induction h with
  | seed d title hstep hreqs_back =>
    intro n hn
    rw [initSeed_nodes] at hn
    simp at hn; subst hn
    refine ⟨?_, ?_⟩
    · rw [initSeed_current]
      show d.step < 1
      omega
    · intro req hreq
      show req.step < d.step
      exact hreqs_back req hreq
  | up g d title hstep hreqs_back hreqs_distinct h_reach ih =>
    have hpr : Pruned g (GPathM.filterAll g (reqOf d)) := pruned_filterAll g (reqOf d)
    have hstruct' : NodeStructure reqOf (GPathM.filterAll g (reqOf d)) :=
      structure_pruned reqOf hpr ih
    dsimp only [GPathM.upFiltering, GPathM.up]
    split
    · exact structure_addNode reqOf hstruct' (hstep.trans hpr.step_eq.symm) hreqs_back
    · exact hstruct'
  | join g₁ g₂ hok h₁ h₂ ih₁ ih₂ =>
    intro n hn
    have hcs : (GPathM.join g₁ g₂).current_step = g₁.current_step := rfl
    have hcs₂ : g₂.current_step = g₁.current_step := by
      have hok' := hok
      simp only [GPathM.okJoin, Bool.and_eq_true, beq_iff_eq] at hok'
      omega
    rcases mem_join_nodes hn with ⟨n₁, hn₁, rfl⟩ | ⟨n₁, hn₁, m, hm, _hmid, rfl⟩ | hg₂
    · obtain ⟨a, b⟩ := ih₁ n hn₁
      rw [hcs]
      exact ⟨a, b⟩
    · have hid : (GPathM.mergeNode n₁ m).id = n₁.id := rfl
      obtain ⟨a, b⟩ := ih₁ n₁ hn₁
      rw [hcs, hid]
      exact ⟨a, b⟩
    · obtain ⟨a, b⟩ := ih₂ n hg₂
      rw [hcs]
      exact ⟨by omega, b⟩

theorem steps_below_current (h : Reachable reqOf g) :
    ∀ n ∈ g.nodes, n.id.id.step < g.current_step :=
  fun n hn => (reachable_structure reqOf h n hn).1

theorem reqs_back_trans (h : Reachable reqOf g) :
    ∀ n ∈ g.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step :=
  fun n hn => (reachable_structure reqOf h n hn).2

-- ============================================================
-- Chain step (was the inconsistent axiom A8 — now a projection
-- of the repaired IsChain)
-- ============================================================

theorem chain_step_eq (g : GPathM) (sel : Int → PathNodeId) (k : Int)
    (h_chain : IsChain g sel) (hk_lo : 0 ≤ k) (hk_hi : k < g.current_step) :
    (sel k).id.step = k :=
  (h_chain.1 k hk_lo hk_hi).2

-- ============================================================
-- pid_safe: new pid doesn't violate ReqFiltered for old nodes
-- ============================================================

theorem pid_safe (h_reach : Reachable reqOf g) (n : PNodeM) (hn : n ∈ g.nodes)
    (pid : PathNodeId) (hpid_step : pid.id.step = g.current_step) :
    ∀ req ∈ reqOf n.id.id, pid.id.step ≠ req.step := by
  have h_back := reqs_back_trans reqOf h_reach n hn
  have h_below := steps_below_current reqOf h_reach n hn
  intro req hreq
  have hlt1 := h_back req hreq
  rw [hpid_step]
  omega

-- ============================================================
-- L1.c — UP step (was the false axiom A9 — now stated over the
-- graph it is actually applied to, and proved)
-- ============================================================

private theorem addNode_ReqFiltered {g : GPathM} (h_reach : Reachable reqOf g)
    (d : NodeId) (title : String)
    (hRF : ReqFiltered reqOf (GPathM.filterAll g (reqOf d)))
    (hstep : d.step = g.current_step)
    (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step) :
    ReqFiltered reqOf (GPathM.addNode (GPathM.filterAll g (reqOf d)) d title) := by
  intro n' hn' req hreq q hq hstepq
  have hpr : Pruned g (GPathM.filterAll g (reqOf d)) := pruned_filterAll g (reqOf d)
  rcases mem_addNode hn' with ⟨m, hm, hid, hown⟩ | ⟨hid, hown⟩
  · -- Old node: its owners either predate the UP (invariant transfers) or
    -- are the fresh pid, whose step is beyond every old requirement.
    have hreqm : req ∈ reqOf m.id.id := by rw [← hid]; exact hreq
    rw [hown] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hRF m hm req hreqm q hq hstepq
    · have hq' := List.mem_singleton.mp hq
      exfalso
      obtain ⟨n₀, hn₀, hid₀, _⟩ := hpr.nodes_derived m hm
      have hreq₀ : req ∈ reqOf n₀.id.id := by rw [← hid₀]; exact hreqm
      obtain ⟨h2, hback⟩ := reachable_structure reqOf h_reach n₀ hn₀
      have h1 : req.step < n₀.id.id.step := hback req hreq₀
      have h3 : q.id.step = d.step := by rw [hq']
      omega
  · -- New node: its inherited owners were cleaned by filterAll, and its own
    -- pid sits at d.step, strictly beyond its backward requirements.
    have hids : n'.id.id = d := by rw [hid]
    rw [hids] at hreq
    rw [hown] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact filterAll_cleans_gowner g (reqOf d) req q hreq hq hstepq
    · have hq' := List.mem_singleton.mp hq
      exfalso
      have h1 : req.step < d.step := hreqs_back req hreq
      have h3 : q.id.step = d.step := by rw [hq']
      omega

theorem upFiltering_ReqFiltered (h : ReqFiltered reqOf g) (h_reach : Reachable reqOf g)
    (d : NodeId) (title : String) (hstep : d.step = g.current_step)
    (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step)
    (_hreqs_distinct : ∀ r₁ r₂, r₁ ∈ reqOf d → r₂ ∈ reqOf d → r₁.step = r₂.step → r₁ = r₂) :
    ReqFiltered reqOf (GPathM.upFiltering g (reqOf d) d title) := by
  have h_g' : ReqFiltered reqOf (GPathM.filterAll g (reqOf d)) :=
    filterAll_preserves_ReqFiltered reqOf h (reqOf d)
  dsimp only [GPathM.upFiltering, GPathM.up]
  split
  · exact addNode_ReqFiltered reqOf h_reach d title h_g' hstep hreqs_back
  · exact h_g'

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
  intro n hn req hreq q hq hstep
  rcases mem_join_nodes hn with ⟨n₁, hn₁, rfl⟩ | ⟨n₁, hn₁, m, hm, hmid, rfl⟩ | hg₂
  · exact h₁ n hn₁ req hreq q hq hstep
  · rcases mergeNode_owners_subset n₁ m q hq with hq₁ | hq₂
    · exact h₁ n₁ hn₁ req hreq q hq₁ hstep
    · have hreq_m : req ∈ reqOf m.id.id := by
        rw [hmid]
        exact hreq
      exact h₂ m hm req hreq_m q hq₂ hstep
  · exact h₂ n hg₂ req hreq q hq hstep

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
    have h_node_some : (g.node? (sel j)).isSome := (h_chain_node j hj_lo hj_hi).1
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
    have h_node_some : (g.node? (sel j)).isSome := (h_chain_node j hj_lo hj_hi).1
    let n := (g.node? (sel j)).get h_node_some
    have h_node : g.node? (sel j) = some n := by simp [n]
    have h_id_eq : n.id = sel j := node?_id_eq g (sel j) n h_node
    have hn_mem : n ∈ g.nodes := node?_mem g (sel j) h_node_some
    simp [h_node] at h_mem
    have hreq_n : req ∈ reqOf n.id.id := by rw [h_id_eq]; exact hreq
    have h_inv_result := h_inv n hn_mem req hreq_n (sel req.step) h_mem
    exact h_inv_result h_step_eq

-- ============================================================
-- Axiom guards: the build fails if any project axiom ever
-- reappears in the closure of L1 or L1_cor (only Lean's
-- built-in propext/Quot.sound are allowed).
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.L1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms L1

/-- info: 'AbsSat.GraphPath.Model.L1_cor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms L1_cor

end AbsSat.GraphPath.Model
