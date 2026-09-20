-- lean_project/AbsSat/GraphPath/Model/FabricInduction.lean
import AbsSat.GraphPath.Model.ReviewNodes
import AbsSat.GraphPath.Model.FabricAdd

/-!
# Every valid machine state is covered by a fabric — given the filter step

`FullFabric g` — some `Fabric` (`Fabric.lean`) has every node of `g` as a member.

The induction over `Reachable`:

* **seed** — `FabricAdd.Fabric_initSeed`, and the seed's only node is its member.
* **join** — `FabricAdd.Fabric_join_left` / `_right` carry each side's fabric into the join, and
  `fabric_union` joins the two fabrics: every clause of a fabric is local, so a union of fabrics
  is a fabric. Every node of the join comes from one side.
* **up** — `upFiltering g reqs d = addNode (filterAll g reqs) d` when the filter is valid.
  `FabricAdd.Fabric_addNode` extends a fabric by the new node. The filter step is
  `fullFabric_filterAll`: under `ReviewNodes.FabricOutside` for the pinned state, the review keeps
  that fabric (`Fabric.FOk_review`) and removes every other node (`unsupported_removed`), so the
  filtered state is covered again.

The only hypothesis left is `FilterFabric`: at every valid filter of a reachable state covered by a
fabric, the nodes outside the removal closure carry a fabric. `fullFabric_reachable` proves every
valid reachable state is covered, under `FilterFabric`.

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210): every kept state is covered
(3,774 of 3,774), and `FabricOutside` holds at every valid filter (6,111 of 6,111). Restricting the
kept state's greatest fabric to the nodes outside the closure is already a fabric in 6,090 of those;
in the other 21, 118 entries lose their only parent or son backer to the closure, and each such node
keeps another backed entry at the same step.
-/

namespace AbsSat.GraphPath.Model.FabricInduction

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.ReviewNodes

/-- Some fabric has every node as a member. -/
def FullFabric (g : GPathM) : Prop :=
  ∃ S T, Fabric.Fabric g S T ∧ ∀ x, (g.node? x).isSome = true → S x

/-- **A union of fabrics is a fabric.** -/
theorem fabric_union {g : GPathM} {S₁ S₂ : PathNodeId → Prop}
    {T₁ T₂ : PathNodeId → PathNodeId → Prop}
    (h₁ : Fabric.Fabric g S₁ T₁) (h₂ : Fabric.Fabric g S₂ T₂) :
    Fabric.Fabric g (fun p => S₁ p ∨ S₂ p) (fun p v => (S₁ p ∧ T₁ p v) ∨ (S₂ p ∧ T₂ p v)) where
  gow := fun p hp => hp.elim (h₁.gow p) (h₂.gow p)
  node := fun p hp => hp.elim (h₁.node p) (h₂.node p)
  inS := fun p v _ hT => hT.elim
    (fun ⟨hp, ht⟩ => Or.inl (h₁.inS p v hp ht)) (fun ⟨hp, ht⟩ => Or.inr (h₂.inS p v hp ht))
  symm := fun p v _ hT => hT.elim
    (fun ⟨hp, ht⟩ => Or.inl ⟨h₁.inS p v hp ht, h₁.symm p v hp ht⟩)
    (fun ⟨hp, ht⟩ => Or.inr ⟨h₂.inS p v hp ht, h₂.symm p v hp ht⟩)
  self := fun p hp => hp.elim (fun h => Or.inl ⟨h, h₁.self p h⟩) (fun h => Or.inr ⟨h, h₂.self p h⟩)
  sub := fun p n hn _ v hT => hT.elim
    (fun ⟨hp, ht⟩ => h₁.sub p n hn hp v ht) (fun ⟨hp, ht⟩ => h₂.sub p n hn hp v ht)
  support := fun p hp l hl0 hl => hp.elim
    (fun h => let ⟨v, hv, hs⟩ := h₁.support p h l hl0 hl; ⟨v, Or.inl ⟨h, hv⟩, hs⟩)
    (fun h => let ⟨v, hv, hs⟩ := h₂.support p h l hl0 hl; ⟨v, Or.inr ⟨h, hv⟩, hs⟩)
  up := fun p n hn _ hpr v hT => hT.elim
    (fun ⟨hp, ht⟩ =>
      let ⟨c, hc, hpc, hcv⟩ := h₁.up p n hn hp hpr v ht
      ⟨c, hc, Or.inl ⟨hp, hpc⟩, Or.inl ⟨h₁.inS p c hp hpc, hcv⟩⟩)
    (fun ⟨hp, ht⟩ =>
      let ⟨c, hc, hpc, hcv⟩ := h₂.up p n hn hp hpr v ht
      ⟨c, hc, Or.inr ⟨hp, hpc⟩, Or.inr ⟨h₂.inS p c hp hpc, hcv⟩⟩)
  down := fun p _ htop v hT => hT.elim
    (fun ⟨hp, ht⟩ =>
      let ⟨c, m, hcm, hpm, hpc, hcv⟩ := h₁.down p hp htop v ht
      ⟨c, m, hcm, hpm, Or.inl ⟨hp, hpc⟩, Or.inl ⟨h₁.inS p c hp hpc, hcv⟩⟩)
    (fun ⟨hp, ht⟩ =>
      let ⟨c, m, hcm, hpm, hpc, hcv⟩ := h₂.down p hp htop v ht
      ⟨c, m, hcm, hpm, Or.inr ⟨hp, hpc⟩, Or.inr ⟨h₂.inS p c hp hpc, hcv⟩⟩)

-- ============================================================
-- The three construction steps
-- ============================================================

theorem fullFabric_initSeed (d : NodeId) (title : String) (hd : d.step = 0) :
    FullFabric (initSeed d title) := by
  refine ⟨_, _, FabricAdd.Fabric_initSeed d title hd, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
  have hmem := List.mem_of_find?_eq_some hn
  have hid := node?_id_eq _ x n hn
  rw [initSeed_nodes d title] at hmem
  rw [List.mem_singleton.mp hmem] at hid
  exact hid.symm

theorem fullFabric_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : FullFabric g₁) (h₂ : FullFabric g₂) : FullFabric (join g₁ g₂) := by
  obtain ⟨S₁, T₁, hf₁, hc₁⟩ := h₁
  obtain ⟨S₂, T₂, hf₂, hc₂⟩ := h₂
  refine ⟨_, _, fabric_union (FabricAdd.Fabric_join_left g₁ g₂ S₁ T₁ hf₁)
    (FabricAdd.Fabric_join_right g₁ g₂ hok S₂ T₂ hf₂), ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
  rcases join_node?_source g₁ g₂ x n hn with h | h
  · exact Or.inl (hc₁ x h)
  · exact Or.inr (hc₂ x h)

theorem fullFabric_addNode (F : GPathM) (d : NodeId) (title : String) (h : FullFabric F)
    (hd : d.step = F.current_step) (hbelow : ∀ n ∈ F.nodes, n.id.id.step < F.current_step)
    (_hne : ∃ p, (F.node? p).isSome = true) (hpos : 0 < F.current_step)
    (hoos : SelfOwn.OOS F) :
    FullFabric (addNode F d title) := by
  obtain ⟨S, T, hf, hcov⟩ := h
  refine ⟨_, _, FabricAdd.Fabric_addNode title hf hd hbelow hpos hcov hoos, ?_⟩
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
    exact Or.inl (hcov x hsome)
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff F d title n).mp h1
    rw [rowNode_id] at hid
    rw [← hid]
    exact Or.inr hpid

-- ============================================================
-- The filter step
-- ============================================================

theorem isValid_of_pruned {g g' : GPathM} (hpr : Pruned g g') (hv : isValid g' = true) :
    isValid g = true :=
  PickInduction.isValid_of_gowner g (fun k h0 hk => by
    have hent := hasStepEntry_of_isValid g' hv k h0 (by rw [hpr.step_eq]; exact hk)
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
    obtain ⟨q, hq, hqs⟩ := hent
    exact ⟨q, hpr.gowners_sub q hq, hqs⟩)

/-- **The filter step.** Under `FabricOutside` for the pinned state, the filtered state is
covered by a fabric. -/
theorem fullFabric_filterAll (reqOf : NodeId → List NodeId) (g : GPathM)
    (hr : Reachable reqOf g) (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true)
    (hfo : FabricOutside (reqs.foldl filterRequire g)) : FullFabric (filterAll g reqs) := by
  obtain ⟨S, T, hf, hcov⟩ := hfo
  have hok : Fabric.FOk (reqs.foldl filterRequire g) S T :=
    ⟨hf, smp_pins reqOf g hr reqs, notRoot_pins reqOf g hr reqs⟩
  have hF : Fabric.Fabric (filterAll g reqs) S T := (Fabric.FOk_review _ S T hok).fab
  refine ⟨S, T, hF, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
  have hpr : Pruned (reqs.foldl filterRequire g) (filterAll g reqs) := pruned_review _
  obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hn)
  have hnid : n.id = x := node?_id_eq _ x n hn
  have hsomeP : ((reqs.foldl filterRequire g).node? x).isSome = true := by
    have := node?_isSome_of_mem _ m hm
    rw [← hid, hnid] at this
    exact this
  rcases hcov x hsomeP with hu | hs
  · have hnone := unsupported_removed reqOf g hr reqs hv hu
    rw [hnone] at hx
    exact absurd hx (by simp)
  · exact hs

-- ============================================================
-- The induction
-- ============================================================

/-- At every valid filter of a reachable state covered by a fabric, the nodes outside the removal
closure carry a fabric. -/
def FilterFabric (reqOf : NodeId → List NodeId) : Prop :=
  ∀ (g : GPathM) (reqs : List NodeId), Reachable reqOf g → FullFabric g →
    isValid (filterAll g reqs) = true → FabricOutside (reqs.foldl filterRequire g)

/-- **Every valid reachable state is covered by a fabric**, under `FilterFabric`. -/
theorem fullFabric_reachable (reqOf : NodeId → List NodeId) (hff : FilterFabric reqOf)
    (g : GPathM) (hr : Reachable reqOf g) : isValid g = true → FullFabric g := by
  induction hr with
  | seed d title hstep _ => intro _; exact fullFabric_initSeed d title hstep
  | up g d title hstep _ _ hrg ih =>
    intro hv
    have hpr := pruned_filterAll g (reqOf d)
    cases hF : isValid (filterAll g (reqOf d)) with
    | false =>
      simp only [upFiltering, GPathM.up, hF] at hv
      exact absurd hv (by simp [hF])
    | true =>
      have hg : isValid g = true := isValid_of_pruned hpr hF
      have hFF := fullFabric_filterAll reqOf g hrg (reqOf d) hF (hff g (reqOf d) hrg (ih hg) hF)
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
      exact fullFabric_addNode _ d title hFF (by rw [hpr.step_eq]; exact hstep)
        (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hrg)) hne hpos
        (SelfOwn.OOS_of_pruned hpr (SelfOwn.OOS_reachable reqOf g hrg))
  | join g₁ g₂ hok _ _ ih₁ ih₂ =>
    intro _
    have hok' : okJoin g₁ g₂ = true := hok
    simp only [okJoin, Bool.and_eq_true] at hok
    obtain ⟨⟨_, hv₁⟩, hv₂⟩ := hok
    exact fullFabric_join g₁ g₂ hok' (ih₁ hv₁) (ih₂ hv₂)

/-- info: 'AbsSat.GraphPath.Model.FabricInduction.fullFabric_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullFabric_filterAll

/-- info: 'AbsSat.GraphPath.Model.FabricInduction.fullFabric_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullFabric_reachable

end AbsSat.GraphPath.Model.FabricInduction
