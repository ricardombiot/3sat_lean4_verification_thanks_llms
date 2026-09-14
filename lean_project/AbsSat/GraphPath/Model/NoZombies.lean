-- lean_project/AbsSat/GraphPath/Model/NoZombies.lean
import AbsSat.GraphPath.Model.ChainFabric
import AbsSat.GraphPath.Model.JoinSound
import AbsSat.GraphPath.Model.L6

/-!
# No zombies, as an invariant of the construction

`NoZombie g` — every node of `g` lies on a full `ChainSound` chain of `g`.

The induction over `Reachable`:

* **seed** — the seed's only node is on its own one-step chain (`ChainSound_initSeed`).
* **join** — a chain of either side is a chain of the join (`ChainSound_join_left` / `_right`), and
  every node of the join comes from one side.
* **addNode** — a chain of the old state, extended by the new node, is a chain of the new state
  (`ChainSound_addNode`); it passes through every old node it passed through, and through the new
  node.
* **filter** — under `NoZombieOutside` for the pinned state, a node survives the filter iff it lies
  on a full chain through the pins (`ChainFabric.survives_iff_onChain`), and that chain survives the
  review (`ChainSound_review`).

The only hypothesis left is `LossInClosure`: at every valid filter of a reachable state with no
zombies, every node of the pinned state is in the removal closure or keeps a full chain.
`noZombie_reachable` proves every valid reachable state has no zombies under it; with
`Fabric_chains` that also gives `FabricInduction.FullFabric`, and at every valid filter the filter
keeps exactly the nodes on full chains through the pins (`filter_keeps_chains`).

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210): 0 zombies among 92,985 nodes of the
3,774 valid kept states; at the 6,111 valid filters, the 41,501 nodes that lose every chain once
pinned are all in the closure, and the closure has exactly 41,501 nodes.
-/

namespace AbsSat.GraphPath.Model.NoZombies

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.ReviewNodes
open AbsSat.GraphPath.Model.ChainFabric

/-- Every node lies on a full sound chain. -/
def NoZombie (g : GPathM) : Prop := ∀ x, (g.node? x).isSome = true → ChainS g x

/-- At every valid filter of a reachable state with no zombies, every node of the pinned state is
in the removal closure or keeps a full chain. -/
def LossInClosure (reqOf : NodeId → List NodeId) : Prop :=
  ∀ (g : GPathM) (reqs : List NodeId), Reachable reqOf g → NoZombie g →
    isValid (filterAll g reqs) = true → NoZombieOutside (reqs.foldl filterRequire g)

-- ============================================================
-- The construction steps
-- ============================================================

theorem noZombie_initSeed (d : NodeId) (title : String) (hd : d.step = 0) :
    NoZombie (initSeed d title) := by
  intro x hx
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
  have hmem := List.mem_of_find?_eq_some hn
  have hid := node?_id_eq _ x n hn
  have hseed : initSeed d title = addNode empty d title := rfl
  rw [hseed, addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with h1 | h1
  · simp [empty] at h1
  · rw [List.mem_singleton.mp h1] at hid
    refine ⟨_, ChainSound_initSeed d title hd, 0, Int.le_refl 0,
      by rw [initSeed_current]; decide, ?_⟩
    rw [← hid]
    rfl

theorem noZombie_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : NoZombie g₁) (h₂ : NoZombie g₂) : NoZombie (join g₁ g₂) := by
  intro x hx
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
  rcases join_node?_source g₁ g₂ x n hn with h | h
  · obtain ⟨sel, hs, k, hk0, hk1, hk⟩ := h₁ x h
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hs, k, hk0,
      by rw [(grown_join_left g₁ g₂).step_eq]; exact hk1, hk⟩
  · obtain ⟨sel, hs, k, hk0, hk1, hk⟩ := h₂ x h
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hs, k, hk0,
      by rw [(grown_join_right g₁ g₂ hok).step_eq]; exact hk1, hk⟩

theorem noZombie_addNode (F : GPathM) (d : NodeId) (title : String) (h : NoZombie F)
    (hd : d.step = F.current_step) (hbelow : ∀ n ∈ F.nodes, n.id.id.step < F.current_step)
    (hmok : MachineOk F) (hne : ∃ p, (F.node? p).isSome = true) :
    NoZombie (addNode F d title) := by
  intro x hx
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
  have hmem := List.mem_of_find?_eq_some hn
  have hid := node?_id_eq _ x n hn
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with h1 | h1
  · obtain ⟨m, hm, hmn⟩ := List.mem_map.mp h1
    rw [← hmn, upMap_id] at hid
    have hsome := node?_isSome_of_mem F m hm
    rw [hid] at hsome
    obtain ⟨sel, hs, k, hk0, hk1, hk⟩ := h x hsome
    refine ⟨extend F d sel, ChainSound_addNode F d title hd hbelow hmok sel hs, k, hk0,
      by rw [addNode_current]; omega, ?_⟩
    rw [extend_below F d sel k hk1]
    exact hk
  · rw [List.mem_singleton.mp h1] at hid
    obtain ⟨p, hp⟩ := hne
    obtain ⟨sel, hs, _⟩ := h p hp
    refine ⟨extend F d sel, ChainSound_addNode F d title hd hbelow hmok sel hs, F.current_step,
      hmok.1, by rw [addNode_current]; omega, ?_⟩
    rw [extend_top, ← hid]
    rfl

/-- **The filter step.** Under `NoZombieOutside` for the pinned state, the filtered state has no
zombies. -/
theorem noZombie_filterAll (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true)
    (hnz : NoZombieOutside (reqs.foldl filterRequire g)) : NoZombie (filterAll g reqs) := by
  intro x hx
  have hpr : Pruned (reqs.foldl filterRequire g) (filterAll g reqs) := pruned_review _
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hn)
  have hnid : n.id = x := node?_id_eq _ x n hn
  have hsomeP : ((reqs.foldl filterRequire g).node? x).isSome = true := by
    have := node?_isSome_of_mem _ m hm
    rw [← hid, hnid] at this
    exact this
  obtain ⟨sel, hs, k, hk0, hk1, hk⟩ := (survives_iff_onChain reqOf g hr reqs hv hnz x hsomeP).mp hx
  have hsf : ChainSound (filterAll g reqs) sel := ChainSound_review _ sel hs
  exact ⟨sel, hsf, k, hk0, by rw [hpr.step_eq]; exact hk1, hk⟩

-- ============================================================
-- The induction
-- ============================================================

/-- **Every valid reachable state has no zombies**, under `LossInClosure`. -/
theorem noZombie_reachable (reqOf : NodeId → List NodeId) (hloss : LossInClosure reqOf)
    (g : GPathM) (hr : Reachable reqOf g) : isValid g = true → NoZombie g := by
  induction hr with
  | seed d title hstep _ => intro _; exact noZombie_initSeed d title hstep
  | up g d title hstep _ _ hrg ih =>
    intro hv
    have hpr := pruned_filterAll g (reqOf d)
    cases hF : isValid (filterAll g (reqOf d)) with
    | false =>
      simp only [upFiltering, GPathM.up, hF] at hv
      exact absurd hv (by simp [hF])
    | true =>
      have hg : isValid g = true := FabricInduction.isValid_of_pruned hpr hF
      have hFz := noZombie_filterAll reqOf g hrg (reqOf d) hF (hloss g (reqOf d) hrg (ih hg) hF)
      have hshape : upFiltering g (reqOf d) d title = addNode (filterAll g (reqOf d)) d title := by
        simp only [upFiltering, GPathM.up, hF, if_pos]
      rw [hshape]
      have hpos : 0 < (filterAll g (reqOf d)).current_step := by
        rw [hpr.step_eq]; exact NodeInvariant.pos_reachable reqOf g hrg
      have hne : ∃ p, ((filterAll g (reqOf d)).node? p).isSome = true := by
        have hent := hasStepEntry_of_isValid _ hF 0 (Int.le_refl 0) hpos
        simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
        obtain ⟨q, hq, _⟩ := hent
        exact ⟨q, (GownersNodes.hasNode_iff _ q).mp
          (GownersNodes.GN_filterAll g (reqOf d) (GownersNodes.GN_reachable reqOf g hrg) q hq)⟩
      exact noZombie_addNode _ d title hFz (by rw [hpr.step_eq]; exact hstep)
        (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hrg))
        (MachineOk_of_pruned hpr (SubsetSemantics.MachineOk_reachable reqOf g hrg)) hne
  | join g₁ g₂ hok _ _ ih₁ ih₂ =>
    intro _
    have hok' : okJoin g₁ g₂ = true := hok
    simp only [okJoin, Bool.and_eq_true] at hok
    obtain ⟨⟨_, hv₁⟩, hv₂⟩ := hok
    exact noZombie_join g₁ g₂ hok' (ih₁ hv₁) (ih₂ hv₂)

-- ============================================================
-- What it gives
-- ============================================================

/-- No zombies gives a fabric over every node. -/
theorem fullFabric_of_noZombie (g : GPathM) (h : NoZombie g) : FabricInduction.FullFabric g :=
  ⟨_, _, Fabric_chains g, h⟩

/-- **At every valid filter, the filter keeps exactly the nodes on full chains through the pins**,
under `LossInClosure`. -/
theorem filter_keeps_chains (reqOf : NodeId → List NodeId) (hloss : LossInClosure reqOf)
    (g : GPathM) (hr : Reachable reqOf g) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) (x : PathNodeId)
    (hx : ((reqs.foldl filterRequire g).node? x).isSome = true) :
    ((filterAll g reqs).node? x).isSome = true ↔ ChainS (reqs.foldl filterRequire g) x :=
  survives_iff_onChain reqOf g hr reqs hv
    (hloss g reqs hr (noZombie_reachable reqOf hloss g hr
      (FabricInduction.isValid_of_pruned (pruned_filterAll g reqs) hv)) hv) x hx

/-- info: 'AbsSat.GraphPath.Model.NoZombies.noZombie_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noZombie_reachable

/-- info: 'AbsSat.GraphPath.Model.NoZombies.filter_keeps_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filter_keeps_chains

end AbsSat.GraphPath.Model.NoZombies
