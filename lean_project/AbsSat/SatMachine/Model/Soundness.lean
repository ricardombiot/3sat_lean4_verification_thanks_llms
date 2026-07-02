import AbsSat.SatMachine.Model.Problem
import AbsSat.SatMachine.Model.Axioms

namespace AbsSat.SatMachine.Model

open AbsSat.SatMachine.Model

-- ============================================================
-- BASIC LOGIC HELPERS
-- ============================================================

-- list_contains_iff_mem: direct from simp in Lean 4.31
-- (List.any_eq_true + beq_iff_eq are both @[simp] in Std4)
theorem list_contains_iff_mem {α} [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    list_contains l x = true ↔ x ∈ l := by
  simp [list_contains]

theorem satisfies_requirements_iff (path : PurePath) (reqs : List Requirement) :
    satisfies_requirements path reqs = true ↔
    ∀ r ∈ reqs, ∃ n ∈ path.visited_nodes, n = r.nodeId := by
  simp [satisfies_requirements, List.any_eq_true, List.all_eq_true]

-- ============================================================
-- MONOTONICITY LEMMA
-- ============================================================

-- satisfies_monotonic: more visited nodes → more requirements satisfied
theorem satisfies_monotonic (sub full : PurePath) (reqs : List Requirement) :
    (∀ x, x ∈ sub.visited_nodes → x ∈ full.visited_nodes) →
    satisfies_requirements sub reqs = true →
    satisfies_requirements full reqs = true := by
  intro h_subset h_sat
  rw [satisfies_requirements_iff] at *
  intro r hr
  rcases h_sat r hr with ⟨n, hn_sub, hn_eq⟩
  exact ⟨n, h_subset n hn_sub, hn_eq⟩

-- ============================================================
-- VALID_FOR_LAYERS DEFINITION AND EXTENSION
-- ============================================================

-- Validity predicate: a path covers all past layers, meets all requirements,
-- and every id it has visited traces back to one of those past layers.
def valid_for_layers (past_nodes : List (List PureNode)) (p : PurePath) : Prop :=
  all_layers_covered past_nodes p = true ∧
  all_requirements_met { layers := past_nodes } p = true ∧
  path_confined_to past_nodes p

-- valid_extension: extending a valid path with a requirements-satisfying node
-- from the layer immediately following `past` (inside a well-formed GMap)
-- stays valid.
theorem valid_extension (gmap : PureGMap) (hwf : WellFormedGMap gmap)
    (past rest : List (List PureNode)) (layer : List PureNode)
    (hdecomp : past ++ layer :: rest = gmap.layers)
    (p : PurePath) (n : PureNode) :
    valid_for_layers past p →
    n ∈ layer →
    satisfies_requirements p n.requirements = true →
    valid_for_layers (past ++ [layer]) { visited_nodes := n.id :: p.visited_nodes } := by
  intro h_valid_p h_n_in_layer h_n_reqs
  rcases h_valid_p with ⟨h_cov, h_req, h_conf⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Coverage: past layers still covered + new layer covered by n
    have h_cov_past := coverage_monotonicity past p n h_cov
    have h_cov_new  := coverage_extension layer p n h_n_in_layer
    exact combine_coverage past layer { visited_nodes := n.id :: p.visited_nodes } h_cov_past h_cov_new
  · -- Requirements: closed by the well-formedness-dependent theorem.
    exact combine_requirements gmap hwf past rest layer hdecomp p n h_n_in_layer h_conf h_req h_n_reqs
  · -- Confinement: every id in the extended path traces to `past ++ [layer]`.
    intro id hid
    rcases List.mem_cons.mp hid with rfl | hid'
    · exact ⟨layer, List.mem_append_right _ List.mem_cons_self, n, h_n_in_layer, rfl⟩
    · rcases h_conf id hid' with ⟨layer', hlayer'_in, m, hm_in, hm_eq⟩
      exact ⟨layer', List.mem_append_left _ hlayer'_in, m, hm_in, hm_eq⟩

-- ============================================================
-- SOUNDNESS OF run_layers
-- ============================================================

theorem run_layers_sound (gmap : PureGMap) (hwf : WellFormedGMap gmap)
    (layers : List (List PureNode)) (paths : List PurePath) (past : List (List PureNode))
    (hdecomp : past ++ layers = gmap.layers) :
    (∀ p ∈ paths, valid_for_layers past p) →
    ∀ p_final ∈ run_layers layers paths, valid_for_layers (past ++ layers) p_final := by
  intro h_valid_input p_final h_in_run
  induction layers generalizing paths past with
  | nil =>
    simp only [run_layers] at h_in_run
    rw [List.append_nil]
    exact h_valid_input p_final h_in_run
  | cons layer rest ih =>
    simp only [run_layers] at h_in_run
    -- Case split on Bool: is the next step empty?
    cases heq : (run_step_nodes layer paths).isEmpty with
    | true =>
      -- Empty: h_in_run : p_final ∈ [] → contradiction
      simp [heq] at h_in_run
    | false =>
      -- Non-empty: h_in_run : p_final ∈ run_layers rest (run_step_nodes layer paths)
      simp [heq] at h_in_run
      have h_result := ih (run_step_nodes layer paths) (past ++ [layer])
        (by rw [List.append_assoc]; simpa using hdecomp)
        (fun p_next h_p_next => by
          rcases run_step_semantics layer paths p_next h_p_next with ⟨p_orig, h_orig_in, n, h_n_in, h_sat, h_eq⟩
          rw [h_eq]
          exact valid_extension gmap hwf past rest layer hdecomp p_orig n
            (h_valid_input p_orig h_orig_in) h_n_in h_sat)
        h_in_run
      simpa [List.append_assoc, List.singleton_append] using h_result

-- ============================================================
-- MAIN SOUNDNESS THEOREM
-- ============================================================

/--
  Soundness Theorem: Every path returned by run_pure is a valid solution,
  provided the GMap is well-formed (globally unique node ids, honestly
  labeled layers). This is provable without any remaining axioms about the
  proof structure — it uses only the proved lemmas from Axioms.lean plus
  the single remaining completeness axiom, which soundness does not need.
-/
theorem soundness_theorem (gmap : PureGMap) (hwf : WellFormedGMap gmap) (p : PurePath) :
    list_contains (run_pure gmap) p = true → is_valid_solution gmap p = true := by
  intro h_in
  rw [list_contains_iff_mem] at h_in
  unfold run_pure at h_in
  have h_init : valid_for_layers [] { visited_nodes := [] } := by
    refine ⟨?_, ?_, ?_⟩
    · simp [all_layers_covered]
    · simp [all_requirements_met]
    · intro id hid; cases hid
  have h_res := run_layers_sound gmap hwf gmap.layers [{ visited_nodes := [] }] [] (by simp)
  specialize h_res (by intro p hp; simp at hp; subst hp; exact h_init) p h_in
  rcases h_res with ⟨h_cov, h_req, _⟩
  simp only [List.nil_append] at h_cov h_req
  simp [is_valid_solution]
  exact ⟨h_cov, h_req⟩

end AbsSat.SatMachine.Model
