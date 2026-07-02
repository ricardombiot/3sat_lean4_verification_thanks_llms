import AbsSat.SatMachine.Model.Problem

namespace AbsSat.SatMachine.Model

open AbsSat.SatMachine.Model

-- ============================================================
-- HELPER LEMMAS
-- ============================================================

-- Monotonicity of list_contains: adding an element to a list cannot lose membership.
private theorem list_contains_mono {α} [BEq α] (l : List α) (y x : α) :
    list_contains l x = true → list_contains (y :: l) x = true := by
  intro h
  simp only [list_contains, List.any_cons, Bool.or_eq_true]
  exact Or.inr h

-- Bool/Prop bridge for `list_contains` over `List Nat` (used throughout below
-- to avoid manual boolean case analysis).
private theorem list_contains_iff_mem (l : List Nat) (x : Nat) :
    list_contains l x = true ↔ x ∈ l := by
  simp [list_contains]

private theorem list_contains_eq_false_iff (l : List Nat) (x : Nat) :
    list_contains l x = false ↔ x ∉ l := by
  constructor
  · intro h hmem
    have := (list_contains_iff_mem l x).mpr hmem
    rw [h] at this
    exact absurd this (by decide)
  · intro h
    cases hc : list_contains l x with
    | false => rfl
    | true => exact absurd ((list_contains_iff_mem l x).mp hc) h

-- Monotonicity of layer_covered: extending visited_nodes cannot lose coverage.
private theorem layer_covered_mono (nodes : List PureNode) (p : PurePath) (n : PureNode) :
    layer_covered nodes p = true →
    layer_covered nodes { visited_nodes := n.id :: p.visited_nodes } = true := by
  simp only [layer_covered, List.any_eq_true]
  intro ⟨m, hm_in, hm_covers⟩
  exact ⟨m, hm_in, list_contains_mono _ _ _ hm_covers⟩

-- Monotonicity of satisfies_requirements: more visited nodes means more requirements met.
private theorem satisfies_requirements_mono (path : PurePath) (n_new : PureNode) (reqs : List Requirement) :
    satisfies_requirements path reqs = true →
    satisfies_requirements { visited_nodes := n_new.id :: path.visited_nodes } reqs = true := by
  simp only [satisfies_requirements, List.all_eq_true, List.any_eq_true]
  intro h req hreq
  rcases h req hreq with ⟨id, hid_in, hid_eq⟩
  exact ⟨id, List.mem_cons_of_mem _ hid_in, hid_eq⟩

-- Membership characterization of list_bind.
theorem mem_list_bind {α β} (l : List α) (f : α → List β) (x : β) :
    x ∈ list_bind l f ↔ ∃ a ∈ l, x ∈ f a := by
  induction l with
  | nil => simp [list_bind]
  | cons a rest ih =>
    simp only [list_bind, List.mem_append, ih]
    constructor
    · rintro (h | ⟨b, hb_in, hb_mem⟩)
      · exact ⟨a, List.mem_cons_self, h⟩
      · exact ⟨b, List.mem_cons_of_mem _ hb_in, hb_mem⟩
    · rintro ⟨b, hb_in, hb_mem⟩
      rcases List.mem_cons.mp hb_in with rfl | hb_rest
      · exact Or.inl hb_mem
      · exact Or.inr ⟨b, hb_rest, hb_mem⟩

-- Membership characterization of evolve_path_nodes.
theorem mem_evolve_path_nodes (nodes : List PureNode) (path : PurePath) (p_next : PurePath) :
    p_next ∈ evolve_path_nodes nodes path ↔
    ∃ n ∈ nodes, satisfies_requirements path n.requirements = true ∧
      p_next = { visited_nodes := n.id :: path.visited_nodes } := by
  simp only [evolve_path_nodes, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨n, ⟨hn_in, hn_sat⟩, rfl⟩
    exact ⟨n, hn_in, hn_sat, rfl⟩
  · rintro ⟨n, hn_in, hn_sat, rfl⟩
    exact ⟨n, ⟨hn_in, hn_sat⟩, rfl⟩

-- Folding `List.append` over layers is the same as flattening them.
private theorem foldl_append_eq_flatten (l : List (List PureNode)) (init : List PureNode) :
    List.foldl List.append init l = init ++ l.flatten := by
  induction l generalizing init with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, List.flatten_cons]
    rw [ih]
    simp [List.append_assoc]

private theorem mem_requirements_nodes {n' : PureNode} {layers : List (List PureNode)} :
    n' ∈ List.foldl List.append [] layers ↔ ∃ layer ∈ layers, n' ∈ layer := by
  rw [foldl_append_eq_flatten]
  simp [List.mem_flatten]

-- ============================================================
-- THEOREMS (previously axioms — now formally proved)
-- ============================================================

/--
  Theorem: Coverage Monotonicity
  Extending a path with a new node preserves coverage of all past layers.
  Proved by induction: List.any is monotone with respect to list extension.
-/
theorem coverage_monotonicity (past : List (List PureNode)) (p : PurePath) (n : PureNode) :
    all_layers_covered past p = true →
    all_layers_covered past { visited_nodes := n.id :: p.visited_nodes } = true := by
  induction past with
  | nil => simp [all_layers_covered]
  | cons layer rest ih =>
    simp only [all_layers_covered, Bool.and_eq_true]
    intro ⟨h_layer, h_rest⟩
    exact ⟨layer_covered_mono layer p n h_layer, ih h_rest⟩

/--
  Theorem: Coverage Extension
  If n is in layer, then the path { n.id :: _ } covers that layer.
  Proved directly from the definitions of layer_covered and list_contains.
-/
theorem coverage_extension (layer : List PureNode) (p : PurePath) (n : PureNode) :
    n ∈ layer →
    layer_covered layer { visited_nodes := n.id :: p.visited_nodes } = true := by
  intro h_in
  simp only [layer_covered, List.any_eq_true]
  exact ⟨n, h_in, by simp [list_contains, List.any_cons]⟩

/--
  Theorem: Combine Coverage
  If a path covers `past` and covers `layer` separately, it covers their concatenation.
  Proved by induction on `past`.
-/
theorem combine_coverage (past : List (List PureNode)) (layer : List PureNode) (p : PurePath) :
    all_layers_covered past p = true →
    layer_covered layer p = true →
    all_layers_covered (past ++ [layer]) p = true := by
  induction past with
  | nil =>
    intro _ h_layer
    simp [all_layers_covered, h_layer]
  | cons head rest ih =>
    simp only [List.cons_append, all_layers_covered, Bool.and_eq_true]
    intro ⟨h_head, h_rest⟩ h_layer
    exact ⟨h_head, ih h_rest h_layer⟩

/--
  Theorem: New Node Requirements Met
  If p already satisfies n's requirements, then (n.id :: p) also satisfies them.
  Proved by monotonicity: List.any on a longer list is still true.
-/
theorem new_node_requirements_met (p : PurePath) (n : PureNode) :
    satisfies_requirements p n.requirements = true →
    satisfies_requirements { visited_nodes := n.id :: p.visited_nodes } n.requirements = true :=
  satisfies_requirements_mono p n n.requirements

/--
  Theorem: Run Step Semantics
  Any path produced by run_step_nodes is an extension of an existing path
  by exactly one node from the layer whose requirements are satisfied.
  Proved by unfolding list_bind and evolve_path_nodes.
-/
theorem run_step_semantics (layer : List PureNode) (paths : List PurePath) (p_next : PurePath) :
    p_next ∈ (run_step_nodes layer paths) →
    ∃ p_orig ∈ paths, ∃ n ∈ layer,
      satisfies_requirements p_orig n.requirements = true ∧
      p_next = { visited_nodes := n.id :: p_orig.visited_nodes } := by
  unfold run_step_nodes
  rw [mem_list_bind]
  intro ⟨p_orig, h_orig, h_evol⟩
  rw [mem_evolve_path_nodes] at h_evol
  rcases h_evol with ⟨n, hn_in, hn_sat, hn_eq⟩
  exact ⟨p_orig, h_orig, n, hn_in, hn_sat, hn_eq⟩

-- ============================================================
-- WELL-FORMEDNESS-DEPENDENT THEOREMS
-- ============================================================

/--
  Theorem: Id Disjointness Across the Past/Current Boundary
  In a well-formed GMap, a node consumed in `past` and a node from the
  layer immediately following `past` can never share an id. This is the
  structural fact that eliminates `requirements_preservation` and
  `combine_requirements` as axioms.
-/
theorem id_disjoint_past_current (gmap : PureGMap) (hwf : WellFormedGMap gmap)
    (past rest : List (List PureNode)) (layer : List PureNode)
    (hdecomp : past ++ layer :: rest = gmap.layers)
    (layer' : List PureNode) (hlayer' : layer' ∈ past)
    (n1 : PureNode) (hn1 : n1 ∈ layer')
    (n2 : PureNode) (hn2 : n2 ∈ layer) :
    n1.id ≠ n2.id := by
  intro heq
  have hn1_all : n1 ∈ gmap.all_nodes :=
    mem_all_nodes (hdecomp ▸ List.mem_append_left _ hlayer') hn1
  have hn2_all : n2 ∈ gmap.all_nodes :=
    mem_all_nodes (hdecomp ▸ List.mem_append_right _ List.mem_cons_self) hn2
  have heqn : n1 = n2 := hwf.unique_ids n1 hn1_all n2 hn2_all heq
  have hlabel : LayersLabeledFrom (past ++ layer :: rest) 0 := hdecomp ▸ hwf.layers_labeled
  have h1 : n1.layer < 0 + past.length :=
    past_nodes_below past (layer :: rest) 0 hlabel layer' hlayer' n1 hn1
  have hlabel_drop : LayersLabeledFrom (layer :: rest) (0 + past.length) :=
    layers_labeled_drop past (layer :: rest) 0 hlabel
  have h2 : n2.layer = 0 + past.length := hlabel_drop.1 n2 hn2
  rw [heqn] at h1
  omega

/--
  Theorem: Requirements Preservation
  Adding n (from the layer immediately after `past`) to the path preserves
  requirement satisfaction for all nodes already consumed in `past`: by
  well-formedness, n's id cannot collide with any id visible in `past`, so
  the `if` guard in `all_requirements_met` is unaffected for those nodes.
-/
theorem requirements_preservation (gmap : PureGMap) (hwf : WellFormedGMap gmap)
    (past rest : List (List PureNode)) (layer : List PureNode)
    (hdecomp : past ++ layer :: rest = gmap.layers)
    (p : PurePath) (n : PureNode) (hn : n ∈ layer) :
    all_requirements_met { layers := past } p = true →
    all_requirements_met { layers := past } { visited_nodes := n.id :: p.visited_nodes } = true := by
  intro h
  unfold all_requirements_met at h ⊢
  simp only [List.all_eq_true] at h ⊢
  intro n' hn'_mem
  rcases mem_requirements_nodes.mp hn'_mem with ⟨layer', hlayer'_in, hn'_in_layer'⟩
  by_cases hcontains : n'.id ∈ p.visited_nodes
  · -- n' was already visited in p: monotonicity carries the old satisfaction forward.
    have hc : list_contains p.visited_nodes n'.id = true := (list_contains_iff_mem _ _).mpr hcontains
    have hsat := h n' hn'_mem
    simp only [hc, if_true] at hsat
    have hsat' := satisfies_requirements_mono p n n'.requirements hsat
    have hc' : list_contains (n.id :: p.visited_nodes) n'.id = true :=
      list_contains_mono p.visited_nodes n.id n'.id hc
    simp only [hc', if_true]
    exact hsat'
  · -- n' was not visited in p, and by well-formedness it cannot suddenly equal n's id either.
    have hne : n'.id ≠ n.id :=
      id_disjoint_past_current gmap hwf past rest layer hdecomp layer' hlayer'_in n' hn'_in_layer' n hn
    have hc : list_contains (n.id :: p.visited_nodes) n'.id = false := by
      rw [list_contains_eq_false_iff]
      intro hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · exact hne heq
      · exact hcontains hmem'
    simp [hc]

/--
  Theorem: Combine Requirements
  If all requirements for `past` are met, and node n's own requirements are
  met by `p`, then all requirements for `past ++ [layer]` are met by the
  extended path. The remaining gap in the old axiom — other nodes of
  `layer` whose id might coincidentally already be visited — is closed by
  `path_confined_to`: any id visited so far traces back to `past`, so by
  well-formedness it can never coincide with a *different* node of `layer`.
-/
theorem combine_requirements (gmap : PureGMap) (hwf : WellFormedGMap gmap)
    (past rest : List (List PureNode)) (layer : List PureNode)
    (hdecomp : past ++ layer :: rest = gmap.layers)
    (p : PurePath) (n : PureNode) (hn : n ∈ layer)
    (hconf : path_confined_to past p)
    (h_past : all_requirements_met { layers := past } p = true)
    (h_n : satisfies_requirements p n.requirements = true) :
    all_requirements_met { layers := past ++ [layer] } { visited_nodes := n.id :: p.visited_nodes } = true := by
  have h_past' := requirements_preservation gmap hwf past rest layer hdecomp p n hn h_past
  have h_n' := new_node_requirements_met p n h_n
  unfold all_requirements_met at h_past' ⊢
  simp only [List.all_eq_true] at h_past' ⊢
  intro m hm_mem
  have hm_mem' : m ∈ List.foldl List.append [] past ∨ m ∈ layer := by
    have := mem_requirements_nodes.mp hm_mem
    rcases this with ⟨layer'', hlayer''_in, hm_in⟩
    rcases List.mem_append.mp hlayer''_in with h | h
    · exact Or.inl (mem_requirements_nodes.mpr ⟨layer'', h, hm_in⟩)
    · right; rw [List.mem_singleton.mp h] at hm_in; exact hm_in
  rcases hm_mem' with hm_past | hm_layer
  · exact h_past' m hm_past
  · by_cases heq : m.id = n.id
    · have hm_all : m ∈ gmap.all_nodes :=
        mem_all_nodes (hdecomp ▸ List.mem_append_right _ List.mem_cons_self) hm_layer
      have hn_all : n ∈ gmap.all_nodes :=
        mem_all_nodes (hdecomp ▸ List.mem_append_right _ List.mem_cons_self) hn
      have hmn : m = n := hwf.unique_ids m hm_all n hn_all heq
      subst hmn
      have hc : list_contains (m.id :: p.visited_nodes) m.id = true := by
        rw [list_contains_iff_mem]; exact List.mem_cons_self
      simp only [hc, if_true]
      exact h_n'
    · have hnot : m.id ∉ p.visited_nodes := by
        intro hmem
        obtain ⟨layer', hlayer'_in, n'', hn''_in, hn''_eq⟩ := hconf m.id hmem
        exact (id_disjoint_past_current gmap hwf past rest layer hdecomp layer' hlayer'_in n'' hn''_in m hm_layer) hn''_eq
      have hc : list_contains (n.id :: p.visited_nodes) m.id = false := by
        rw [list_contains_eq_false_iff]
        intro hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact heq h
        · exact hnot h
      simp [hc]

-- ============================================================
-- COMPLETENESS: evolve_path_nodes IS EXHAUSTIVE
-- ============================================================

-- `evolve_path_nodes`/`run_step_nodes` never drop a candidate: extending
-- any single path already present in `paths` survives into the batched
-- result over the whole list. This is what makes the algorithm exhaustive
-- rather than merely "some" valid extensions.
theorem mem_run_step_nodes_of_mem (nodes : List PureNode) (paths : List PurePath)
    (p : PurePath) (hp : p ∈ paths) (p' : PurePath) (hp' : p' ∈ evolve_path_nodes nodes p) :
    p' ∈ run_step_nodes nodes paths := by
  unfold run_step_nodes
  rw [mem_list_bind]
  exact ⟨p, hp, hp'⟩

/--
  Theorem: `run_layers` Completeness
  If `prefix_path` is one of the currently tracked `paths`, and there is a
  valid choice sequence for the remaining `layers` starting from
  `prefix_path`, then the corresponding solution path is reachable in
  `run_layers layers paths` — no candidate is ever lost, because
  `evolve_path_nodes` keeps every node whose requirements are satisfied
  (it filters, it never picks just one).
-/
theorem run_layers_mem_complete (layers : List (List PureNode)) (paths : List PurePath)
    (prefix_path : PurePath) (hmem : prefix_path ∈ paths) (choices : List PureNode) :
    ChoicesValid layers choices prefix_path →
    fold_choices choices prefix_path ∈ run_layers layers paths := by
  induction layers generalizing choices prefix_path paths with
  | nil =>
    intro h
    cases choices with
    | nil => simpa [fold_choices, run_layers] using hmem
    | cons c cs => cases h
  | cons layer rest ih =>
    intro h
    cases choices with
    | nil => cases h
    | cons c cs =>
      obtain ⟨hc_in, hc_sat, hc_rest⟩ := h
      have hc_evolve : { visited_nodes := c.id :: prefix_path.visited_nodes } ∈ evolve_path_nodes layer prefix_path :=
        (mem_evolve_path_nodes layer prefix_path _).mpr ⟨c, hc_in, hc_sat, rfl⟩
      have hc_next : { visited_nodes := c.id :: prefix_path.visited_nodes } ∈ run_step_nodes layer paths :=
        mem_run_step_nodes_of_mem layer paths prefix_path hmem _ hc_evolve
      have hnonempty : (run_step_nodes layer paths).isEmpty = false := by
        cases hcase : (run_step_nodes layer paths).isEmpty with
        | false => rfl
        | true =>
          rw [List.isEmpty_iff] at hcase
          rw [hcase] at hc_next
          simp at hc_next
      simp only [run_layers, hnonempty, Bool.false_eq_true, if_false]
      have := ih (run_step_nodes layer paths) { visited_nodes := c.id :: prefix_path.visited_nodes } hc_next cs hc_rest
      simpa [fold_choices] using this

/--
  Theorem: `run_pure` Completeness (was axiom `valid_prefix_maintained`)
  Any valid choice sequence over `gmap.layers` produces a path that
  `run_pure` actually finds.
-/
theorem run_pure_complete (gmap : PureGMap) (choices : List PureNode) :
    ChoicesValid gmap.layers choices { visited_nodes := [] } →
    fold_choices choices { visited_nodes := [] } ∈ run_pure gmap := by
  intro h
  unfold run_pure
  exact run_layers_mem_complete gmap.layers [{ visited_nodes := [] }] { visited_nodes := [] }
    (by simp) choices h

end AbsSat.SatMachine.Model
