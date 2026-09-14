-- lean_project/AbsSat/GraphPath/Model/DescentInvariant.lean
import AbsSat.GraphPath.Model.NoDeadEnd

/-!
# No dead ends from any step, as an invariant of the construction

`NoDeadEnd` (in `NoDeadEnd.lean`) asks that a partial chain hanging from the **top** step
always extends downwards. To prove it by induction over how the machine builds a state, the
property is stated from **any** step:

* `SoundOn g sel lo hi` — `SoundFrom` with the top replaced by `hi`.
* `DescendAll g` — every such partial chain with `0 < lo` extends by one pick at `lo - 1`.
* `noDeadEnd_of_descendAll` — `DescendAll` gives `NoDeadEnd`.

The induction has three cases: `addNode`, `join` and `filterAll`. This module does the first:

* `descendAll_addNode` — **`addNode` keeps `DescendAll`**, given the top anchor of the state
  it extends. A chain below the new step is a chain of the old state. A chain ending at the
  new node `z` is a chain of the old state plus `z`: `addNode` makes `z` an owner of every
  node and gives `z` every global owner, so any extension found below stays compatible with
  `z`. A chain made of `z` alone extends through the top anchor.
-/

namespace AbsSat.GraphPath.Model.DescentInvariant

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.NoDeadEnd

/-- The picks on steps `lo .. hi` satisfy `ChainSound`'s conditions on those steps. -/
structure SoundOn (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop where
  node : ∀ k, lo ≤ k → k ≤ hi → (g.node? (sel k)).isSome ∧ (sel k).id.step = k
  parent_link : ∀ k, lo ≤ k → k + 1 ≤ hi →
    sel k ∈ ((g.node? (sel (k + 1))).map PNodeM.parents).getD []
  owned : ∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
    sel i ∈ ownersAt (ownersOf g (sel j)) i
  gowner : ∀ k, lo ≤ k → k ≤ hi → sel k ∈ g.gowners
  self_owned : ∀ k, lo ≤ k → k ≤ hi → sel k ∈ ownersOf g (sel k)
  son_link : ∀ k, lo ≤ k → k + 1 ≤ hi → sel (k + 1) ∈ sonsOf g (sel k)
  root_shape : ∀ k, lo ≤ k → k ≤ hi → ((sel k).parent_id = none ↔ k = 0)

/-- **No dead ends from any step.** -/
def DescendAll (g : GPathM) : Prop :=
  ∀ sel lo hi, 0 < lo → lo ≤ hi → hi < g.current_step → SoundOn g sel lo hi →
    ∃ c, SoundOn g (upd sel (lo - 1) c) (lo - 1) hi

-- ============================================================
-- Generalities
-- ============================================================

theorem soundOn_congr {g : GPathM} {sel sel' : Int → PathNodeId} {lo hi : Int}
    (hag : ∀ k, lo ≤ k → k ≤ hi → sel k = sel' k) (h : SoundOn g sel lo hi) :
    SoundOn g sel' lo hi where
  node := fun k h1 h2 => by rw [← hag k h1 h2]; exact h.node k h1 h2
  parent_link := fun k h1 h2 => by
    rw [← hag k h1 (by omega), ← hag (k + 1) (by omega) h2]; exact h.parent_link k h1 h2
  owned := fun i j hi hj hi2 hj2 hne => by
    rw [← hag i hi hi2, ← hag j hj hj2]; exact h.owned i j hi hj hi2 hj2 hne
  gowner := fun k h1 h2 => by rw [← hag k h1 h2]; exact h.gowner k h1 h2
  self_owned := fun k h1 h2 => by rw [← hag k h1 h2]; exact h.self_owned k h1 h2
  son_link := fun k h1 h2 => by
    rw [← hag k h1 (by omega), ← hag (k + 1) (by omega) h2]; exact h.son_link k h1 h2
  root_shape := fun k h1 h2 => by rw [← hag k h1 h2]; exact h.root_shape k h1 h2

theorem soundOn_mono_hi {g : GPathM} {sel : Int → PathNodeId} {lo hi : Int} (hi' : Int)
    (h : SoundOn g sel lo hi) (hle : hi' ≤ hi) : SoundOn g sel lo hi' :=
  ⟨fun k h1 h2 => h.node k h1 (by omega), fun k h1 h2 => h.parent_link k h1 (by omega),
   fun i j hi1 hj1 hi2 hj2 hne => h.owned i j hi1 hj1 (by omega) (by omega) hne,
   fun k h1 h2 => h.gowner k h1 (by omega), fun k h1 h2 => h.self_owned k h1 (by omega),
   fun k h1 h2 => h.son_link k h1 (by omega), fun k h1 h2 => h.root_shape k h1 (by omega)⟩

theorem soundOn_of_soundFrom {g : GPathM} {sel : Int → PathNodeId} {lo : Int}
    (h : SoundFrom g sel lo) : SoundOn g sel lo (g.current_step - 1) :=
  ⟨fun k h1 h2 => h.node k h1 (by omega), fun k h1 h2 => h.parent_link k h1 (by omega),
   fun i j hi1 hj1 hi2 hj2 hne => h.owned i j hi1 hj1 (by omega) (by omega) hne,
   fun k h1 h2 => h.gowner k h1 (by omega), fun k h1 h2 => h.self_owned k h1 (by omega),
   fun k h1 h2 => h.son_link k h1 (by omega), fun k h1 h2 => h.root_shape k h1 (by omega)⟩

theorem soundFrom_of_soundOn {g : GPathM} {sel : Int → PathNodeId} {lo : Int}
    (h : SoundOn g sel lo (g.current_step - 1)) : SoundFrom g sel lo :=
  ⟨fun k h1 h2 => h.node k h1 (by omega), fun k h1 h2 => h.parent_link k h1 (by omega),
   fun i j hi1 hj1 hi2 hj2 hne => h.owned i j hi1 hj1 (by omega) (by omega) hne,
   fun k h1 h2 => h.gowner k h1 (by omega), fun k h1 h2 => h.self_owned k h1 (by omega),
   fun k h1 h2 => h.son_link k h1 (by omega), fun k h1 h2 => h.root_shape k h1 (by omega)⟩

/-- `DescendAll` gives `NoDeadEnd`. -/
theorem noDeadEnd_of_descendAll (g : GPathM) (h : DescendAll g) : NoDeadEnd g :=
  fun sel lo hlo hlc hs =>
    let ⟨c, hc⟩ := h sel lo (g.current_step - 1) hlo hlc (by omega) (soundOn_of_soundFrom hs)
    ⟨c, soundFrom_of_soundOn hc⟩

-- ============================================================
-- `addNode`
-- ============================================================

section AddNode

variable (g : GPathM) (d : NodeId) (title : String)

/-- The only node at the new step is the new node. -/
theorem eq_newPid_of_step (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    {p : PathNodeId} (hsome : ((addNode g d title).node? p).isSome = true)
    (hstep : p.id.step = g.current_step) : p = newPid g d := by
  obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := List.mem_of_find?_eq_some hn'
  have hid := node?_id_eq _ p n' hn'
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with h1 | h1
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h1
    rw [upMap_id] at hid
    have hb := hbelow m hm
    rw [hid] at hb
    omega
  · rw [List.mem_singleton.mp h1] at hid
    rw [← hid]
    rfl

/-- A partial chain of the extended state below the new step is a partial chain of the old
state. -/
theorem soundOn_of_addNode (hd : d.step = g.current_step) {sel : Int → PathNodeId}
    {lo hi : Int} (hhi : hi < g.current_step) (h : SoundOn (addNode g d title) sel lo hi) :
    SoundOn g sel lo hi := by
  have hlook : ∀ k, lo ≤ k → k ≤ hi → ∃ n, g.node? (sel k) = some n ∧
      (addNode g d title).node? (sel k) = some (upMap g d n) := by
    intro k h1 h2
    obtain ⟨hsome, hstep⟩ := h.node k h1 h2
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨n, hn, rfl⟩ := addNode_node?_below g d title hd _ n' hn' (by omega)
    exact ⟨n, hn, hn'⟩
  have hne : ∀ k, lo ≤ k → k ≤ hi → sel k ≠ newPid g d := by
    intro k h1 h2 heq
    have hstep := (h.node k h1 h2).2
    rw [heq] at hstep
    simp only [newPid] at hstep
    omega
  refine ⟨fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun i j hi1 hj1 hi2 hj2 hij => ?_,
    fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩
  · obtain ⟨n, hn, _⟩ := hlook k h1 h2
    exact ⟨by rw [hn]; rfl, (h.node k h1 h2).2⟩
  · obtain ⟨n, hn, hn'⟩ := hlook (k + 1) (by omega) h2
    have hp := h.parent_link k h1 h2
    rw [hn'] at hp
    have hp' : sel k ∈ (upMap g d n).parents := hp
    rw [upMap_parents] at hp'
    rw [hn]
    exact hp'
  · obtain ⟨n, hn, hn'⟩ := hlook j hj1 hj2
    have ho := h.owned i j hi1 hj1 hi2 hj2 hij
    simp only [ownersOf, hn', upMap_owners, ownersAt, List.mem_filter] at ho
    simp only [ownersOf, hn, ownersAt, List.mem_filter]
    refine ⟨?_, ho.2⟩
    rcases List.mem_append.mp ho.1 with h3 | h3
    · exact h3
    · exact absurd (List.mem_singleton.mp h3) (hne i hi1 hi2)
  · have hg := h.gowner k h1 h2
    rw [addNode_gowners] at hg
    rcases List.mem_append.mp hg with h3 | h3
    · exact h3
    · exact absurd (List.mem_singleton.mp h3) (hne k h1 h2)
  · obtain ⟨n, hn, hn'⟩ := hlook k h1 h2
    have ho := h.self_owned k h1 h2
    simp only [ownersOf, hn', upMap_owners] at ho
    simp only [ownersOf, hn]
    rcases List.mem_append.mp ho with h3 | h3
    · exact h3
    · exact absurd (List.mem_singleton.mp h3) (hne k h1 h2)
  · obtain ⟨n, hn, hn'⟩ := hlook k h1 (by omega)
    have hs := h.son_link k h1 h2
    simp only [sonsOf, hn', upMap_sons] at hs
    simp only [sonsOf, hn]
    rcases SubsetSemantics.mem_upSons_sons_cases g d n _ hs with h3 | h3
    · exact h3
    · exact absurd h3 (hne (k + 1) (by omega) h2)
  · exact h.root_shape k h1 h2

/-- A partial chain of the old state is a partial chain of the extended state. -/
theorem soundOn_addNode_of {sel : Int → PathNodeId} {lo hi : Int} (h : SoundOn g sel lo hi) :
    SoundOn (addNode g d title) sel lo hi := by
  have hlook : ∀ k, lo ≤ k → k ≤ hi → ∃ n, g.node? (sel k) = some n ∧
      (addNode g d title).node? (sel k) = some (upMap g d n) := by
    intro k h1 h2
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node k h1 h2).1
    exact ⟨n, hn, addNode_node?_old g d title _ n hn⟩
  refine ⟨fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun i j hi1 hj1 hi2 hj2 hij => ?_,
    fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩
  · obtain ⟨n, _, hn'⟩ := hlook k h1 h2
    exact ⟨by rw [hn']; rfl, (h.node k h1 h2).2⟩
  · obtain ⟨n, hn, hn'⟩ := hlook (k + 1) (by omega) h2
    have hp := h.parent_link k h1 h2
    rw [hn] at hp
    rw [hn']
    show sel k ∈ (upMap g d n).parents
    rw [upMap_parents]
    exact hp
  · obtain ⟨n, hn, hn'⟩ := hlook j hj1 hj2
    have ho := h.owned i j hi1 hj1 hi2 hj2 hij
    simp only [ownersOf, hn, ownersAt, List.mem_filter] at ho
    simp only [ownersOf, hn', upMap_owners, ownersAt, List.mem_filter]
    exact ⟨List.mem_append_left _ ho.1, ho.2⟩
  · rw [addNode_gowners]
    exact List.mem_append_left _ (h.gowner k h1 h2)
  · obtain ⟨n, hn, hn'⟩ := hlook k h1 h2
    have ho := h.self_owned k h1 h2
    simp only [ownersOf, hn] at ho
    simp only [ownersOf, hn', upMap_owners]
    exact List.mem_append_left _ ho
  · obtain ⟨n, hn, hn'⟩ := hlook k h1 (by omega)
    have hs := h.son_link k h1 h2
    simp only [sonsOf, hn] at hs
    simp only [sonsOf, hn', upMap_sons]
    exact mem_upSons_sons g d n _ hs
  · exact h.root_shape k h1 h2

/-- A partial chain of the old state reaching its top step, followed by the new node, is a
partial chain of the extended state. -/
theorem soundOn_addNode_top (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hmok : MachineOk g)
    {sel : Int → PathNodeId} {lo : Int} (h : SoundOn g sel lo (g.current_step - 1))
    (hlo : 0 ≤ lo) (hlocs : lo ≤ g.current_step - 1)
    (htop : sel g.current_step = newPid g d) :
    SoundOn (addNode g d title) sel lo g.current_step := by
  have hl := soundOn_addNode_of g d title h
  have hnew := addNode_node?_new g d title hd hbelow
  have hown_new : ownersOf (addNode g d title) (newPid g d) = g.gowners ++ [newPid g d] := by
    simp only [ownersOf, hnew]
    rfl
  refine ⟨fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun i j hi1 hj1 hi2 hj2 hij => ?_,
    fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩
  · rcases int_eq_or_ne k g.current_step with hk | hk
    · rw [hk, htop, hnew]
      exact ⟨rfl, hd⟩
    · exact hl.node k h1 (by omega)
  · rcases int_eq_or_ne (k + 1) g.current_step with hk | hk
    · obtain ⟨hsome, hstep⟩ := h.node k h1 (by omega)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      rw [hk, htop, hnew]
      show sel k ∈ newParents g
      simp only [newParents, if_pos (show g.current_step > 0 by omega)]
      exact mem_line_of_node? g (sel k) n hn (g.current_step - 1) (by rw [hstep]; omega)
    · exact hl.parent_link k h1 (by omega)
  · rcases int_eq_or_ne i g.current_step with hi | hi
    · obtain ⟨hsome, _⟩ := h.node j hj1 (by omega)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      rw [hi, htop]
      simp only [ownersOf, addNode_node?_old g d title _ n hn, upMap_owners, ownersAt,
        List.mem_filter]
      exact ⟨List.mem_append_right _ (List.mem_singleton_self _), beq_iff_eq.mpr hd⟩
    · rcases int_eq_or_ne j g.current_step with hj | hj
      · obtain ⟨_, histep⟩ := h.node i hi1 (by omega)
        rw [hj, htop, hown_new]
        simp only [ownersAt, List.mem_filter]
        exact ⟨List.mem_append_left _ (h.gowner i hi1 (by omega)), beq_iff_eq.mpr histep⟩
      · exact hl.owned i j hi1 hj1 (by omega) (by omega) hij
  · rw [addNode_gowners]
    rcases int_eq_or_ne k g.current_step with hk | hk
    · rw [hk, htop]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (h.gowner k h1 (by omega))
  · rcases int_eq_or_ne k g.current_step with hk | hk
    · rw [hk, htop, hown_new]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact hl.self_owned k h1 (by omega)
  · rcases int_eq_or_ne (k + 1) g.current_step with hk | hk
    · obtain ⟨hsome, hstep⟩ := h.node k h1 (by omega)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      rw [hk, htop]
      simp only [sonsOf, addNode_node?_old g d title _ n hn, upMap_sons]
      refine newPid_mem_upSons_sons g d n ?_
      have hmem := mem_line_of_node? g (sel k) n hn (g.current_step - 1) (by rw [hstep]; omega)
      rw [node?_id_eq g (sel k) n hn]
      simp only [newParents, if_pos (show g.current_step > 0 by omega)]
      exact List.elem_eq_true_of_mem hmem
    · exact hl.son_link k h1 (by omega)
  · rcases int_eq_or_ne k g.current_step with hk | hk
    · rw [hk, htop]
      simp only [newPid]
      constructor
      · intro hnone
        exact absurd hnone (hmok.2.2 (by omega))
      · intro hz
        omega
    · exact hl.root_shape k h1 (by omega)

/-- **`addNode` keeps `DescendAll`**, given the top anchor of the state it extends. -/
theorem descendAll_addNode (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hmok : MachineOk g)
    (ha : 0 < g.current_step → TopAnchor g) (h : DescendAll g) :
    DescendAll (addNode g d title) := by
  intro sel lo hi hlo hlohi hhi hs
  rw [addNode_current] at hhi
  rcases int_eq_or_ne hi g.current_step with hhc | hhc
  · subst hhc
    have htop : sel g.current_step = newPid g d :=
      eq_newPid_of_step g d title hbelow (hs.node _ (by omega) (Int.le_refl _)).1
        (hs.node _ (by omega) (Int.le_refl _)).2
    if hlc : lo ≤ g.current_step - 1 then
      have hs' := soundOn_of_addNode g d title hd (by omega)
        (soundOn_mono_hi (g.current_step - 1) hs (by omega))
      obtain ⟨c, hc⟩ := h sel lo (g.current_step - 1) hlo hlc (by omega) hs'
      refine ⟨c, soundOn_addNode_top g d title hd hbelow hmok hc (by omega) (by omega) ?_⟩
      unfold upd
      rw [if_neg (by omega)]
      exact htop
    else
      obtain ⟨q, hq⟩ := ha (by omega)
      have hq' : SoundOn g (upd sel (lo - 1) q) (lo - 1) (g.current_step - 1) := by
        have hlo' : lo - 1 = g.current_step - 1 := by omega
        rw [hlo']
        refine soundOn_congr (fun k h1 h2 => ?_) (soundOn_of_soundFrom hq)
        unfold upd
        rw [if_pos (by omega)]
      refine ⟨q, soundOn_addNode_top g d title hd hbelow hmok hq' (by omega) (by omega) ?_⟩
      unfold upd
      rw [if_neg (by omega)]
      exact htop
  · have hs' := soundOn_of_addNode g d title hd (by omega) hs
    obtain ⟨c, hc⟩ := h sel lo hi hlo hlohi (by omega) hs'
    exact ⟨c, soundOn_addNode_of g d title hc⟩

end AddNode

/-- info: 'AbsSat.GraphPath.Model.DescentInvariant.noDeadEnd_of_descendAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_of_descendAll

/-- info: 'AbsSat.GraphPath.Model.DescentInvariant.descendAll_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms descendAll_addNode

end AbsSat.GraphPath.Model.DescentInvariant
