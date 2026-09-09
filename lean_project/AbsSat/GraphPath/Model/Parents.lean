-- lean_project/AbsSat/GraphPath/Model/Parents.lean
import AbsSat.GraphPath.Model.Candidates

/-!
**The three shape invariants a path needs**, in the idiom of `GownersNodes.lean`.

v26 left `FilteredChain` split into "are there candidates" (proved) and "can
they be chosen together" (open). The second splits again, into the *path*
(parent-linked) and the *co-ownership* (pairwise). This module supplies what
the path needs:

* `PN` — every parent of a surviving node is a surviving node;
* `PBelow` — a parent sits exactly one step below;
* `NotRoot` — a node above step 0 is not a root, so `isValidNode` forces it to
  have parents.

`PBelow` and `NotRoot` come free from `Pruned` (parents only shrink, ids never
change), so they only need proving at `initSeed`, `addNode` and `join`. `PN`
does not: `Pruned` records that parents shrink, not that the *nodes* they name
survive — which is true (`removeNode` unlinks the id it drops) but has to be
proved per operation.
-/

namespace AbsSat.GraphPath.Model.Parents

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.GownersNodes (HasNode hasNode_iff)

-- ============================================================
-- Parents point at surviving nodes
-- ============================================================

def PN (h : GPathM) : Prop := ∀ n ∈ h.nodes, ∀ p ∈ n.parents, HasNode h p

theorem PN_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hid : ∀ n, (f n).id = n.id) (hpar : ∀ n, (f n).parents = n.parents) (h : PN g) :
    PN (updateAt g id f) := by
  intro n' hn' p hp
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  have hpar' : n'.parents = n.parents := by
    rw [← hEq]; cases n.id == id with
    | true => exact hpar n
    | false => rfl
  rw [hpar'] at hp
  obtain ⟨m, hm, hmid⟩ := h n hn p hp
  refine ⟨(match m.id == id with | true => f m | false => m), List.mem_map_of_mem hm, ?_⟩
  cases m.id == id with
  | true => exact (hid m).trans hmid
  | false => exact hmid

theorem PN_removeNode (g : GPathM) (id : PathNodeId) (h : PN g) :
    PN (removeNode g id) := by
  intro n' hn' p hp
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  have hnmem := List.mem_filter.mp hn
  have hpar : n'.parents = n.parents.filter (fun q => q != id) := by rw [← hEq]
  rw [hpar] at hp
  have hp' := List.mem_filter.mp hp
  obtain ⟨m, hm, hmid⟩ := h n hnmem.1 p hp'.1
  have hmne : m.id ≠ id := by rw [hmid]; exact bne_iff_ne.mp hp'.2
  exact ⟨_, List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, bne_iff_ne.mpr hmne⟩), hmid⟩

theorem PN_filterRequire (g : GPathM) (req : NodeId) (h : PN g) :
    PN (filterRequire g req) := h

theorem PN_cleanInvalidGo (ids : List PathNodeId) :
    ∀ g : GPathM, PN g → PN (cleanInvalidGo g ids) := by
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGo]
    split
    · exact ih g h
    · next d _ =>
      have h₁ : PN (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners g.gowners })) :=
        PN_updateAt g id _ (fun _ => rfl) (fun _ => rfl) h
      split
      · exact ih _ h₁
      · exact ih _ (PN_removeNode _ id h₁)

theorem PN_cleanInvalid (g : GPathM) (h : PN g) : PN (cleanInvalid g) :=
  PN_cleanInvalidGo _ g h

theorem PN_reviewNode (nb : PNodeM → List PathNodeId) (id : PathNodeId) (g : GPathM)
    (h : PN g) : PN (reviewNode g nb id) := by
  simp only [reviewNode]
  split
  · exact h
  · next d _ =>
    split
    · have h₁ : PN (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) :=
        PN_updateAt g id _ (fun _ => rfl) (fun _ => rfl) h
      split
      · exact h₁
      · exact PN_removeNode _ id h₁
    · exact PN_removeNode g id h

private theorem PN_foldl {β : Type} (f : GPathM → β → GPathM)
    (hf : ∀ g b, PN g → PN (f g b)) :
    ∀ (l : List β) (g : GPathM), PN g → PN (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons b bs ih =>
    intro g h; simp only [List.foldl_cons]; exact ih _ (hf g b h)

theorem PN_reviewLine (nb : PNodeM → List PathNodeId) (k : Int) (g : GPathM)
    (h : PN g) : PN (reviewLine g nb k) :=
  PN_foldl (fun g id => reviewNode g nb id) (fun g id => PN_reviewNode nb id g) _ g h

theorem PN_reviewSteps (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, PN g → PN (reviewSteps g nb ks) := by
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    simp only [reviewSteps]
    split
    · exact ih _ (PN_reviewLine nb k g h)
    · exact h

theorem PN_reviewPass (g : GPathM) (h : PN g) : PN (reviewPass g) := by
  simp only [reviewPass]
  exact PN_reviewSteps _ _ _ (PN_reviewSteps _ _ _ (PN_cleanInvalid g h))

theorem PN_reviewFuel : ∀ (fuel : Nat) (g : GPathM), PN g → PN (reviewFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewFuel]
    split
    · split
      · exact ih _ (PN_reviewPass g h)
      · exact PN_reviewPass g h
    · exact h

theorem PN_review (g : GPathM) (h : PN g) : PN (review g) := PN_reviewFuel _ g h

theorem PN_filterAll (g : GPathM) (reqs : List NodeId) (h : PN g) :
    PN (filterAll g reqs) := by
  exact PN_review _ (PN_foldl filterRequire (fun g r => PN_filterRequire g r) reqs g h)

-- ============================================================
-- Growth: `addNode` and `join`
-- ============================================================

theorem mem_line_step (g : GPathM) (k : Int) (p : PathNodeId)
    (h : p ∈ (g.line k).map (·.id)) : p.id.step = k := by
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp h
  have := (List.mem_filter.mp hn).2
  rw [← hEq]; exact eq_of_beq this

theorem mem_nodes_of_mem_line (g : GPathM) (k : Int) (p : PathNodeId)
    (h : p ∈ (g.line k).map (·.id)) : ∃ n ∈ g.nodes, n.id = p := by
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp h
  exact ⟨n, (List.mem_filter.mp hn).1, hEq⟩

theorem PN_addNode (g : GPathM) (d : NodeId) (title : String) (h : PN g) :
    PN (addNode g d title) := by
  intro n' hn' p hp
  rw [addNode_nodes] at hn'
  show ∃ m ∈ (addNode g d title).nodes, m.id = p
  rw [addNode_nodes]
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    rw [← hEq, upMap_parents] at hp
    obtain ⟨m, hm, hmid⟩ := h n hn p hp
    exact ⟨upMap g d m, List.mem_append_left _ (List.mem_map_of_mem hm),
      (upMap_id g d m).trans hmid⟩
  · rcases List.mem_singleton.mp hmem with rfl
    have hpar : (addOwner (newPid g d) (upNode g d title)).parents = newParents g := rfl
    rw [hpar] at hp
    unfold newParents at hp
    split at hp
    · obtain ⟨m, hm, hmid⟩ := mem_nodes_of_mem_line g (g.current_step - 1) p hp
      exact ⟨upMap g d m, List.mem_append_left _ (List.mem_map_of_mem hm),
        (upMap_id g d m).trans hmid⟩
    · exact absurd hp List.not_mem_nil

theorem hasNode_join_left (g₁ g₂ : GPathM) (p : PathNodeId) (h : HasNode g₁ p) :
    HasNode (join g₁ g₂) p := by
  obtain ⟨n, hn, hid⟩ := h
  show ∃ m ∈ (join g₁ g₂).nodes, m.id = p
  rw [GownersNodes.join_nodes]
  refine ⟨(match g₂.node? n.id with | some m => mergeNode n m | none => n),
    List.mem_append_left _ (List.mem_map_of_mem hn), ?_⟩
  cases g₂.node? n.id with
  | some m => exact hid
  | none => exact hid

theorem hasNode_join_right (g₁ g₂ : GPathM) (p : PathNodeId) (h : HasNode g₂ p) :
    HasNode (join g₁ g₂) p := by
  obtain ⟨n, hn, hid⟩ := h
  show ∃ m ∈ (join g₁ g₂).nodes, m.id = p
  rw [GownersNodes.join_nodes]
  cases hg : g₁.node? n.id with
  | some m =>
    have hmid : m.id = n.id := node?_id_eq g₁ n.id m hg
    refine ⟨(match g₂.node? m.id with | some m' => mergeNode m m' | none => m),
      List.mem_append_left _ (List.mem_map_of_mem (List.mem_of_find?_eq_some hg)), ?_⟩
    cases g₂.node? m.id with
    | some m' => exact hmid.trans hid
    | none => exact hmid.trans hid
  | none =>
    exact ⟨n, List.mem_append_right _ (List.mem_filter.mpr ⟨hn, by rw [hg]; rfl⟩), hid⟩

theorem PN_join (g₁ g₂ : GPathM) (h₁ : PN g₁) (h₂ : PN g₂) : PN (join g₁ g₂) := by
  intro n' hn' p hp
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    cases hg : g₂.node? n.id with
    | none =>
      rw [← hEq, hg] at hp
      exact hasNode_join_left g₁ g₂ p (h₁ n hn p hp)
    | some m =>
      rw [← hEq, hg] at hp
      have hpar : (mergeNode n m).parents =
          n.parents ++ m.parents.filter (fun q => !n.parents.contains q) := rfl
      rw [hpar, List.mem_append] at hp
      rcases hp with hp | hp
      · exact hasNode_join_left g₁ g₂ p (h₁ n hn p hp)
      · exact hasNode_join_right g₁ g₂ p
          (h₂ m (List.mem_of_find?_eq_some hg) p (List.mem_filter.mp hp).1)
  · exact hasNode_join_right g₁ g₂ p (h₂ n' (List.mem_filter.mp hmem).1 p hp)

theorem PN_initSeed (d : NodeId) (title : String) : PN (GPathM.initSeed d title) := by
  intro n hn p hp
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  exact absurd hp List.not_mem_nil

theorem PN_up (g : GPathM) (d : NodeId) (title : String) (h : PN g) :
    PN (up g d title) := by
  simp only [GPathM.up]
  split
  · exact PN_addNode g d title h
  · exact h

theorem PN_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (h : PN g) : PN (upFiltering g reqs d title) :=
  PN_up _ d title (PN_filterAll g reqs h)

-- ============================================================
-- A parent sits one step below, and nothing above step 0 is a root
-- ============================================================

def PBelow (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ p ∈ n.parents, p.id.step = n.id.id.step - 1

def NotRoot (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, 0 < n.id.id.step → n.id.parent_id ≠ none

/-- Both come free from `Pruned`: parents only shrink and ids never change. -/
theorem PBelow_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : PBelow g) : PBelow g' := by
  intro n' hn' p hp
  obtain ⟨n, hn, hid, _, hpar⟩ := hpr.nodes_derived n' hn'
  rw [hid]
  exact h n hn p (hpar p hp)

theorem NotRoot_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : NotRoot g) :
    NotRoot g' := by
  intro n' hn' hpos
  obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived n' hn'
  rw [hid] at hpos ⊢
  exact h n hn hpos

theorem PBelow_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (h : PBelow g) : PBelow (addNode g d title) := by
  intro n' hn' p hp
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    rw [← hEq, upMap_parents] at hp
    rw [← hEq, upMap_id]
    exact h n hn p hp
  · rcases List.mem_singleton.mp hmem with rfl
    have hpar : (addOwner (newPid g d) (upNode g d title)).parents = newParents g := rfl
    rw [hpar] at hp
    unfold newParents at hp
    split at hp
    · have hstep := mem_line_step g (g.current_step - 1) p hp
      show p.id.step = d.step - 1
      rw [hstep, hd]
    · exact absurd hp List.not_mem_nil

theorem NotRoot_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (hmok : MachineOk g) (h : NotRoot g) :
    NotRoot (addNode g d title) := by
  intro n' hn' hpos
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    rw [← hEq, upMap_id] at hpos ⊢
    exact h n hn hpos
  · rcases List.mem_singleton.mp hmem with rfl
    show (newPid g d).parent_id ≠ none
    show g.map_parent ≠ none
    refine hmok.2.2 ?_
    rw [← hd]
    exact hpos

theorem PBelow_join (g₁ g₂ : GPathM) (h₁ : PBelow g₁) (h₂ : PBelow g₂) :
    PBelow (join g₁ g₂) := by
  intro n' hn' p hp
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    cases hg : g₂.node? n.id with
    | none => rw [← hEq, hg] at hp ⊢; exact h₁ n hn p hp
    | some m =>
      rw [← hEq, hg] at hp ⊢
      have hpar : (mergeNode n m).parents =
          n.parents ++ m.parents.filter (fun q => !n.parents.contains q) := rfl
      rw [hpar, List.mem_append] at hp
      have hmid : m.id = n.id := node?_id_eq g₂ n.id m hg
      rcases hp with hp | hp
      · exact h₁ n hn p hp
      · have := h₂ m (List.mem_of_find?_eq_some hg) p (List.mem_filter.mp hp).1
        rw [hmid] at this; exact this
  · exact h₂ n' (List.mem_filter.mp hmem).1 p hp

theorem NotRoot_join (g₁ g₂ : GPathM) (h₁ : NotRoot g₁) (h₂ : NotRoot g₂) :
    NotRoot (join g₁ g₂) := by
  intro n' hn' hpos
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    cases hg : g₂.node? n.id with
    | none => rw [← hEq, hg] at hpos ⊢; exact h₁ n hn hpos
    | some m => rw [← hEq, hg] at hpos ⊢; exact h₁ n hn hpos
  · exact h₂ n' (List.mem_filter.mp hmem).1 hpos

theorem PBelow_initSeed (d : NodeId) (title : String) : PBelow (GPathM.initSeed d title) := by
  intro n hn p hp
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  exact absurd hp List.not_mem_nil

theorem NotRoot_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    NotRoot (GPathM.initSeed d title) := by
  intro n hn hpos
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  have hz : (0 : Int) < d.step := hpos
  rw [hstep] at hz
  exact absurd hz (by omega)

-- ============================================================
-- The three, over the machine
-- ============================================================

structure Shape (h : GPathM) : Prop where
  pn : PN h
  pbelow : PBelow h
  notroot : NotRoot h

theorem Shape_of_pruned_pn {g g' : GPathM} (hpr : Pruned g g') (hpn : PN g')
    (h : Shape g) : Shape g' :=
  ⟨hpn, PBelow_of_pruned hpr h.pbelow, NotRoot_of_pruned hpr h.notroot⟩

variable (reqOf : NodeId → List NodeId)

theorem Shape_upFiltering (g : GPathM) (d : NodeId) (title : String)
    (hstep : d.step = g.current_step) (hmok : MachineOk g) (h : Shape g) :
    Shape (upFiltering g (reqOf d) d title) := by
  have hf : Shape (filterAll g (reqOf d)) :=
    Shape_of_pruned_pn (pruned_filterAll g (reqOf d))
      (PN_filterAll g (reqOf d) h.pn) h
  have hmokf : MachineOk (filterAll g (reqOf d)) :=
    MachineOk_of_pruned (pruned_filterAll g (reqOf d)) hmok
  have hd : d.step = (filterAll g (reqOf d)).current_step := by
    rw [(pruned_filterAll g (reqOf d)).step_eq]; exact hstep
  show Shape (up (filterAll g (reqOf d)) d title)
  simp only [GPathM.up]
  split
  · exact ⟨PN_addNode _ d title hf.pn, PBelow_addNode _ d title hd hf.pbelow,
      NotRoot_addNode _ d title hd hmokf hf.notroot⟩
  · exact hf

/-- **The three shape invariants, of every state the machine builds.** -/
theorem Shape_reachable (g : GPathM) (h : Reachable reqOf g) : Shape g := by
  induction h with
  | seed d title hstep _ =>
    exact ⟨PN_initSeed d title, PBelow_initSeed d title, NotRoot_initSeed d title hstep⟩
  | up g d title hstep _ _ hr ih =>
    exact Shape_upFiltering reqOf g d title hstep
      (Certifies.MachineOk_reachable reqOf g hr) ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ =>
    exact ⟨PN_join g₁ g₂ ih₁.pn ih₂.pn, PBelow_join g₁ g₂ ih₁.pbelow ih₂.pbelow,
      NotRoot_join g₁ g₂ ih₁.notroot ih₂.notroot⟩

/-- And on the filtered intermediates, where the obligation lives. -/
theorem Shape_filterAll (g : GPathM) (reqs : List NodeId) (h : Reachable reqOf g) :
    Shape (filterAll g reqs) :=
  Shape_of_pruned_pn (pruned_filterAll g reqs)
    (PN_filterAll g reqs (Shape_reachable reqOf g h).pn) (Shape_reachable reqOf g h)

/-- info: 'AbsSat.GraphPath.Model.Parents.Shape_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shape_reachable

end AbsSat.GraphPath.Model.Parents
