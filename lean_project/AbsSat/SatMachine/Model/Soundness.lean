import AbsSat.SatMachine.Model.Problem
import AbsSat.SatMachine.Model.Axioms

namespace AbsSat.SatMachine.Model

open AbsSat.SatMachine.Model

-- Basic Logic Helpers
instance : LawfulBEq Nat := inferInstance

theorem list_contains_iff_mem {α} [BEq α] [LawfulBEq α] (l : List α) (x : α) :
  list_contains l x = true ↔ x ∈ l := by
  simp [list_contains]
  rw [List.any_eq_true]
  constructor
  . intro h; rcases h with ⟨y, hy, heq⟩; rw [beq_iff_eq] at heq; subst heq; exact hy
  . intro h; exists x; constructor; exact h; rw [beq_iff_eq]

theorem satisfies_requirements_iff (path : PurePath) (reqs : List Requirement) :
  satisfies_requirements path reqs = true ↔
  ∀ r ∈ reqs, ∃ n ∈ path.visited_nodes, n = r.nodeId := by
  simp [satisfies_requirements]
  rw [List.all_eq_true]
  apply Iff.intro
  . intro h r hr; specialize h r hr; rw [List.any_eq_true] at h;
    rcases h with ⟨n, hn, heq⟩; exists n; constructor; exact hn; rw [beq_iff_eq] at heq; exact heq
  . intro h r hr; specialize h r hr; rcases h with ⟨n, hn, heq⟩;
    rw [List.any_eq_true]; exists n; constructor; exact hn; rw [beq_iff_eq]; exact heq

-- Lemma: Monotonicity
theorem satisfies_monotonic (sub full : PurePath) (reqs : List Requirement) :
  (∀ x, x ∈ sub.visited_nodes → x ∈ full.visited_nodes) →
  satisfies_requirements sub reqs = true → satisfies_requirements full reqs = true := by
  intro h_subset h_sat
  rw [satisfies_requirements_iff] at *
  intro r hr
  rcases h_sat r hr with ⟨n, hn_sub, hn_eq⟩
  exists n
  constructor
  . apply h_subset; exact hn_sub
  . exact hn_eq

-- Inductive Lemma: run_layers produces valid paths
-- We define validity incrementally.
def valid_for_layers (past_nodes : List (List PureNode)) (p : PurePath) : Prop :=
  all_layers_covered past_nodes p = true ∧
  all_requirements_met { layers := past_nodes } p = true

-- Axiom application helper
theorem valid_extension (past : List (List PureNode)) (layer : List PureNode) (p : PurePath) (n : PureNode) :
  valid_for_layers past p ->
  n ∈ layer ->
  satisfies_requirements p n.requirements = true ->
  valid_for_layers (past ++ [layer]) { visited_nodes := n.id :: p.visited_nodes } := by
  intro h_valid_p h_n_in_layer h_n_reqs
  rcases h_valid_p with ⟨h_cov, h_req⟩
  simp [valid_for_layers]
  constructor
  . -- Coverage
    have h_cov_past : all_layers_covered past { visited_nodes := n.id :: p.visited_nodes } = true :=
      coverage_monotonicity past p n h_cov

    have h_cov_new : layer_covered layer { visited_nodes := n.id :: p.visited_nodes } = true :=
      coverage_extension layer p n h_n_in_layer

    exact combine_coverage past layer { visited_nodes := n.id :: p.visited_nodes } h_cov_past h_cov_new

  . -- Requirements
    have h_req_past : all_requirements_met { layers := past } { visited_nodes := n.id :: p.visited_nodes } = true :=
      requirements_preservation past p n h_req

    have h_req_new : satisfies_requirements { visited_nodes := n.id :: p.visited_nodes } n.requirements = true :=
      new_node_requirements_met p n h_n_reqs

    -- Use the new signature of combine_requirements
    apply combine_requirements past layer { visited_nodes := n.id :: p.visited_nodes } n h_req_past h_req_new

theorem run_layers_sound (layers : List (List PureNode)) (paths : List PurePath) (past : List (List PureNode)) :
  (∀ p ∈ paths, valid_for_layers past p) ->
  ∀ p_final ∈ run_layers layers paths, valid_for_layers (past ++ layers) p_final := by
  intro h_valid_input p_final h_in_run
  induction layers generalizing paths past with
  | nil =>
    unfold run_layers at h_in_run
    simp at h_in_run
    specialize h_valid_input p_final h_in_run
    rw [List.append_nil]
    exact h_valid_input
  | cons layer rest ih =>
    unfold run_layers at h_in_run
    simp at h_in_run
    let next_paths := run_step_nodes layer paths
    if h_empty : next_paths.isEmpty then
      rw [h_empty] at h_in_run
      simp at h_in_run
      contradiction
    else
      rw [Bool.false_eq_true] at h_empty
      simp [h_empty] at h_in_run
      -- Use IH
      apply ih next_paths (past ++ [layer])
      . intro p_next h_p_next
        -- Axiom: run_step_semantics
        have h_sem := run_step_semantics layer paths p_next h_p_next
        rcases h_sem with ⟨p_orig, h_orig_in, n, h_n_in, h_sat, h_eq⟩
        rw [h_eq]
        apply valid_extension past layer p_orig n (h_valid_input p_orig h_orig_in) h_n_in h_sat
      . exact h_in_run

-- Main Soundness
theorem soundness_theorem (gmap : PureGMap) (p : PurePath) :
  list_contains (run_pure gmap) p = true -> is_valid_solution gmap p = true := by
  intro h_in
  rw [list_contains_iff_mem] at h_in
  unfold run_pure at h_in
  have h_init : valid_for_layers [] { visited_nodes := [] } := by
    simp [valid_for_layers, all_layers_covered, all_requirements_met, List.all_eq_true]
  have h_res := run_layers_sound gmap.layers [{ visited_nodes := [] }] []
  specialize h_res (by intro p hp; simp at hp; subst hp; exact h_init) p h_in
  -- valid_for_layers (gmap.layers) p => is_valid_solution gmap p
  unfold valid_for_layers at h_res
  rcases h_res with ⟨h_cov, h_req⟩
  simp [is_valid_solution]
  constructor
  . exact h_cov
  . rw [List.nil_append] at h_req
    exact h_req
