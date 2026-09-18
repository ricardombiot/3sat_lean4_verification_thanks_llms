-- lean_project/AbsSat/GraphPath/Model/DescentUp.lean
import AbsSat.GraphPath.Model.Descent
import AbsSat.GraphPath.Model.L6Up

/-!
# The descent through an `up`, by construction

The verdict rests on the descent (`NoDeadEndVerdict.sat_of_noDeadEnd`), and v132 measured that no
local rule decides it. So the attack is by construction, and this file does the `up` case with the
fact `RunEnv` made precise: **the node an `up` creates owns every global owner of the state** — its
table is exactly `gowners` at birth — and every old node gains the new node in its own table.

So the new node constrains the descent not at all:

* `soundFrom_g_of_A`, `soundFrom_A_of_g` — a partial chain of `addNode g d` below the new step is a
  partial chain of `g`, and back: a partial chain of `g` whose top pick is the new node is one of
  `addNode g d`. The tables differ only by the new node, which sits above every old step.
* `noDeadEnd_addNode` — **an `up` keeps the descent.** The extension `g` provides is owned by the
  new node because it is a global owner of `g`, and it owns the new node because `addNode` appends
  it to every table. The first step, from the new node alone, is any node of `g`'s top line.

What is left of the induction over the construction is the filter and the join.
-/

namespace AbsSat.GraphPath.Model.DescentUp

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.NoDeadEnd (SoundFrom upd NoDeadEnd)

variable (g : GPathM) (d : NodeId) (title : String)

/-- What a node of `addNode g d title` can be: the new one, or an old one with the new id added. -/
theorem node_addNode_cases (hnd : NodupIds g)
    {y : PathNodeId} {n : PNodeM} (hn : (addNode g d title).node? y = some n) :
    (y = newPid g d ∧ n = addOwner (newPid g d) (upNode g d title)) ∨
      ∃ m, g.node? y = some m ∧ n = upMap g d m := by
  have hnB : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = y := node?_id_eq _ y n hn
  rw [addNode_nodes] at hnB
  rcases List.mem_append.mp hnB with hl | hr
  · obtain ⟨n₀, hn₀, heq⟩ := List.mem_map.mp hl
    have hid₀ : n₀.id = y := by rw [← hid, ← heq, upMap_id]
    refine Or.inr ⟨n₀, ?_, heq.symm⟩
    have := node?_of_mem hnd n₀ hn₀
    rw [hid₀] at this
    exact this
  · have hsing : n = addOwner (newPid g d) (upNode g d title) := List.eq_of_mem_singleton hr
    refine Or.inl ⟨?_, hsing⟩
    rw [hsing] at hid
    exact hid.symm

/-- The new node's table: the state's global owners, plus itself. -/
theorem owners_new (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) :
    ownersOf (addNode g d title) (newPid g d) = g.gowners ++ [newPid g d] := by
  simp only [ownersOf, addNode_node?_new g d title hd hbelow]
  rfl

/-- An old node's table: its own, plus the new node. -/
theorem owners_old {y : PathNodeId} {m : PNodeM} (hm : g.node? y = some m) :
    ownersOf (addNode g d title) y = m.owners ++ [newPid g d] := by
  simp only [ownersOf, addNode_node?_old g d title y m hm]
  exact upMap_owners g d m

/-- The step of the new node. -/
theorem newPid_step (hd : d.step = g.current_step) : (newPid g d).id.step = g.current_step := by
  simp only [newPid]; exact hd

/-- **Below the new step, a partial chain of the extended state is one of the state.** -/
theorem soundFrom_g_of_A (hnd : NodupIds g) (hd : d.step = g.current_step)
    {sel : Int → PathNodeId} {lo : Int}
    (hs : SoundFrom (addNode g d title) sel lo) : SoundFrom g sel lo := by
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  have hnp := newPid_step g d hd
  -- an old pick is a node of `g`
  have hold : ∀ k, lo ≤ k → k < g.current_step → ∃ m, g.node? (sel k) = some m := by
    intro k hk0 hk1
    obtain ⟨hsome, hstep⟩ := hs.node k hk0 (by rw [hcsA]; omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    rcases node_addNode_cases g d title hnd hn with ⟨hy, _⟩ | ⟨m, hm, _⟩
    · exfalso; rw [hy, hnp] at hstep; omega
    · exact ⟨m, hm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk0 hk1
    obtain ⟨m, hm⟩ := hold k hk0 hk1
    obtain ⟨_, hstep⟩ := hs.node k hk0 (by rw [hcsA]; omega)
    exact ⟨by rw [hm]; rfl, hstep⟩
  · intro k hk0 hk1
    obtain ⟨m, hm⟩ := hold (k + 1) (by omega) hk1
    have hpl := hs.parent_link k hk0 (by rw [hcsA]; omega)
    rw [addNode_node?_old g d title (sel (k + 1)) m hm] at hpl
    simp only [Option.map_some, Option.getD_some, upMap_parents] at hpl
    rw [hm]
    simpa only [Option.map_some, Option.getD_some] using hpl
  · intro i j hi0 hj0 hi1 hj1 hij
    obtain ⟨m, hm⟩ := hold j hj0 hj1
    have how := hs.owned i j hi0 hj0 (by rw [hcsA]; omega) (by rw [hcsA]; omega) hij
    rw [owners_old g d title hm] at how
    obtain ⟨hmem, hstep⟩ := List.mem_filter.mp how
    have hne : sel i ≠ newPid g d := by
      intro hc
      rw [hc, hnp] at hstep
      have : i = g.current_step := (eq_of_beq hstep).symm
      omega
    rcases List.mem_append.mp hmem with hl | hr
    · rw [ownersOf, hm]
      exact List.mem_filter.mpr ⟨hl, hstep⟩
    · exact absurd (List.mem_singleton.mp hr) hne
  · intro k hk0 hk1
    have hg := hs.gowner k hk0 (by rw [hcsA]; omega)
    obtain ⟨_, hstep⟩ := hs.node k hk0 (by rw [hcsA]; omega)
    have hgA : (addNode g d title).gowners = g.gowners ++ [newPid g d] := rfl
    rw [hgA] at hg
    rcases List.mem_append.mp hg with hl | hr
    · exact hl
    · exfalso
      have := List.mem_singleton.mp hr
      rw [this, hnp] at hstep
      omega
  · intro k hk0 hk1
    obtain ⟨m, hm⟩ := hold k hk0 hk1
    have hso := hs.self_owned k hk0 (by rw [hcsA]; omega)
    rw [owners_old g d title hm] at hso
    obtain ⟨_, hstep⟩ := hs.node k hk0 (by rw [hcsA]; omega)
    rcases List.mem_append.mp hso with hl | hr
    · rw [ownersOf, hm]; exact hl
    · exfalso
      have := List.mem_singleton.mp hr
      rw [this, hnp] at hstep
      omega
  · intro k hk0 hk1
    obtain ⟨m, hm⟩ := hold k hk0 (by omega)
    have hsl := hs.son_link k hk0 (by rw [hcsA]; omega)
    simp only [sonsOf, addNode_node?_old g d title (sel k) m hm] at hsl
    obtain ⟨_, hstep⟩ := hs.node (k + 1) (by omega) (by rw [hcsA]; omega)
    have hne : sel (k + 1) ≠ newPid g d := by
      intro hc
      rw [hc, hnp] at hstep
      omega
    simp only [upMap, addOwner, upSons] at hsl
    split at hsl
    · simp only at hsl
      rcases List.mem_append.mp hsl with hl | hr
      · simp only [sonsOf, hm]; exact hl
      · exact absurd (List.mem_singleton.mp hr) hne
    · simp only [sonsOf, hm]; exact hsl
  · intro k hk0 hk1
    exact hs.root_shape k hk0 (by rw [hcsA]; omega)

/-- **And back: a partial chain of the state whose top pick is the new node is one of the extended
state.** This is where the new node's birth table does the work: it owns every global owner, so the
picks below it are all in its table, and it is in theirs because `addNode` appends it. -/
theorem soundFrom_A_of_g (hmok : MachineOk g)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    {sel : Int → PathNodeId} {lo : Int}
    (htop : sel g.current_step = newPid g d)
    (hs : SoundFrom g sel lo) : SoundFrom (addNode g d title) sel lo := by
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  have hnp := newPid_step g d hd
  have hnodeA := addNode_node?_new g d title hd hbelow
  -- the old picks, as nodes of `g`
  have hold : ∀ k, lo ≤ k → k < g.current_step → ∃ m, g.node? (sel k) = some m := by
    intro k hk0 hk1
    obtain ⟨hsome, _⟩ := hs.node k hk0 hk1
    exact Option.isSome_iff_exists.mp hsome
  have hownNew : ownersOf (addNode g d title) (newPid g d) = g.gowners ++ [newPid g d] :=
    owners_new g d title hd hbelow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- node
    intro k hk0 hk1
    rcases int_eq_or_ne k g.current_step with rfl | hne
    · rw [htop]
      exact ⟨by rw [hnodeA]; rfl, hnp⟩
    · obtain ⟨m, hm⟩ := hold k hk0 (by rw [hcsA] at hk1; omega)
      obtain ⟨_, hstep⟩ := hs.node k hk0 (by rw [hcsA] at hk1; omega)
      exact ⟨by rw [addNode_node?_old g d title (sel k) m hm]; rfl, hstep⟩
  · -- parent link
    intro k hk0 hk1
    rcases int_eq_or_ne (k + 1) g.current_step with heq | hne
    · -- the new node's parents are the top line of `g`
      rw [heq, htop, hnodeA]
      simp only [Option.map_some, Option.getD_some, addOwner, upNode, newParents, if_pos hpos]
      obtain ⟨m, hm⟩ := hold k hk0 (by omega)
      obtain ⟨_, hstep⟩ := hs.node k hk0 (by omega)
      refine List.mem_map.mpr ⟨m, ?_, node?_id_eq g (sel k) m hm⟩
      refine List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hm, ?_⟩
      have hid := node?_id_eq g (sel k) m hm
      rw [hid, hstep]
      exact beq_iff_eq.mpr (by omega)
    · obtain ⟨m, hm⟩ := hold (k + 1) (by omega) (by rw [hcsA] at hk1; omega)
      have hpl := hs.parent_link k hk0 (by rw [hcsA] at hk1; omega)
      rw [hm] at hpl
      simp only [Option.map_some, Option.getD_some] at hpl
      rw [addNode_node?_old g d title (sel (k + 1)) m hm]
      simpa only [Option.map_some, Option.getD_some, upMap_parents] using hpl
  · -- pairwise ownership
    intro i j hi0 hj0 hi1 hj1 hij
    rcases int_eq_or_ne j g.current_step with rfl | hnej
    · -- `j` is the new node: it owns every global owner
      rw [htop, hownNew]
      have hgi := hs.gowner i hi0 (by rw [hcsA] at hi1; omega)
      obtain ⟨_, hstep⟩ := hs.node i hi0 (by rw [hcsA] at hi1; omega)
      exact List.mem_filter.mpr ⟨List.mem_append_left _ hgi, beq_iff_eq.mpr hstep⟩
    · obtain ⟨m, hm⟩ := hold j hj0 (by rw [hcsA] at hj1; omega)
      rw [owners_old g d title hm]
      rcases int_eq_or_ne i g.current_step with rfl | hnei
      · -- `i` is the new node: every table gains it
        rw [htop]
        exact List.mem_filter.mpr ⟨List.mem_append_right _ (List.mem_singleton_self _),
          beq_iff_eq.mpr hnp⟩
      · have how := hs.owned i j hi0 hj0 (by rw [hcsA] at hi1; omega)
          (by rw [hcsA] at hj1; omega) hij
        rw [ownersOf, hm] at how
        obtain ⟨hmem, hstep⟩ := List.mem_filter.mp how
        exact List.mem_filter.mpr ⟨List.mem_append_left _ hmem, hstep⟩
  · -- global owner
    intro k hk0 hk1
    have hgA : (addNode g d title).gowners = g.gowners ++ [newPid g d] := rfl
    rw [hgA]
    rcases int_eq_or_ne k g.current_step with rfl | hne
    · rw [htop]; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (hs.gowner k hk0 (by rw [hcsA] at hk1; omega))
  · -- self ownership
    intro k hk0 hk1
    rcases int_eq_or_ne k g.current_step with rfl | hne
    · rw [htop, hownNew]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · obtain ⟨m, hm⟩ := hold k hk0 (by rw [hcsA] at hk1; omega)
      rw [owners_old g d title hm]
      have hso := hs.self_owned k hk0 (by rw [hcsA] at hk1; omega)
      rw [ownersOf, hm] at hso
      exact List.mem_append_left _ hso
  · -- son link
    intro k hk0 hk1
    obtain ⟨m, hm⟩ := hold k hk0 (by rw [hcsA] at hk1; omega)
    simp only [sonsOf, addNode_node?_old g d title (sel k) m hm, upMap, addOwner, upSons]
    rcases int_eq_or_ne (k + 1) g.current_step with heq | hne
    · -- the new node is a son of every node of the top line
      have hid := node?_id_eq g (sel k) m hm
      obtain ⟨_, hstep⟩ := hs.node k hk0 (by omega)
      have hmemtop : (newParents g).contains (sel k) = true := by
        simp only [newParents, if_pos hpos]
        refine List.elem_eq_true_of_mem (List.mem_map.mpr ⟨m, ?_, hid⟩)
        refine List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hm, ?_⟩
        rw [hid, hstep]
        exact beq_iff_eq.mpr (by omega)
      rw [hid]
      simp only [hmemtop, if_pos]
      rw [heq, htop]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · have hsl := hs.son_link k hk0 (by rw [hcsA] at hk1; omega)
      simp only [sonsOf, hm] at hsl
      have hid := node?_id_eq g (sel k) m hm
      rw [hid]
      split
      · exact List.mem_append_left _ hsl
      · exact hsl
  · -- root shape
    intro k hk0 hk1
    rcases int_eq_or_ne k g.current_step with rfl | hne
    · rw [htop]
      constructor
      · intro hroot
        exfalso
        have hmp : (newPid g d).parent_id = g.map_parent := rfl
        rw [hmp] at hroot
        obtain ⟨_, _, hsome⟩ := hmok
        have := hsome hpos
        rw [hroot] at this
        exact absurd this (by simp)
      · intro hz; omega
    · exact hs.root_shape k hk0 (by rw [hcsA] at hk1; omega)


/-- **The seed has nothing to descend**: its only step is the top one. -/
theorem noDeadEnd_initSeed (e : NodeId) (t : String) : NoDeadEnd (initSeed e t) := by
  intro sel lo hlo0 hlo _
  exfalso
  have hcs : (initSeed e t).current_step = 1 := initSeed_current e t
  rw [hcs] at hlo
  omega

/-- **An `up` keeps the descent.** The extension the state provides is owned by the new node
because it is a global owner there, and it owns the new node because `addNode` appends the new id
to every table. The first step, from the new node alone, is any node of the top line. -/
theorem noDeadEnd_addNode (ctx : Pinned.Ctx g) (hnd : NodupIds g) (hmok : MachineOk g)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step) (hv : isValid g = true)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (h : NoDeadEnd g) : NoDeadEnd (addNode g d title) := by
  intro sel lo hlo0 hlo hs
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  have hnp := newPid_step g d hd
  rw [hcsA] at hlo
  -- the pick at the new step is the new node: nothing else lives there
  have htop : sel g.current_step = newPid g d := by
    obtain ⟨hsome, hstep⟩ := hs.node g.current_step (by omega) (by rw [hcsA]; omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    rcases node_addNode_cases g d title hnd hn with ⟨hy, _⟩ | ⟨m, hm, _⟩
    · exact hy
    · exfalso
      have hidm := node?_id_eq g (sel g.current_step) m hm
      have hb := hbelow m (List.mem_of_find?_eq_some hm)
      rw [hidm, hstep] at hb
      omega
  rcases int_eq_or_ne lo g.current_step with rfl | hne
  · -- the chain is the new node alone
    have hent := hasStepEntry_of_isValid g hv (g.current_step - 1) (by omega) (by omega)
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
    obtain ⟨q, hq, hqs⟩ := hent
    obtain ⟨t, ht, htid⟩ := ctx.gn q hq
    have htnode : g.node? q = some t := by rw [← htid]; exact node?_of_mem hnd t ht
    have hupd : upd sel (g.current_step - 1) q (g.current_step - 1) = q := by
      show (if (g.current_step - 1) = g.current_step - 1 then q else sel (g.current_step - 1)) = q
      rw [if_pos rfl]
    have hsg : SoundFrom g (upd sel (g.current_step - 1) q) (g.current_step - 1) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk0 hk1
        have hk : k = g.current_step - 1 := by omega
        subst hk
        rw [hupd]
        exact ⟨by rw [htnode]; rfl, hqs⟩
      · intro k _ hk1; omega
      · intro i j hi0 hj0 hi1 hj1 hij
        exfalso; omega
      · intro k hk0 hk1
        have hk : k = g.current_step - 1 := by omega
        subst hk
        rw [hupd]; exact hq
      · intro k hk0 hk1
        have hk : k = g.current_step - 1 := by omega
        subst hk
        rw [hupd]
        simpa only [ownersOf, htnode] using ctx.self q t htnode
      · intro k _ hk1; omega
      · intro k hk0 hk1
        have hk : k = g.current_step - 1 := by omega
        subst hk
        rw [hupd]
        constructor
        · intro hroot
          by_cases h0 : q.id.step = 0
          · omega
          · exfalso
            have hnr := ctx.shape.notroot t (List.mem_of_find?_eq_some htnode)
              (by rw [node?_id_eq g q t htnode]; omega)
            rw [node?_id_eq g q t htnode] at hnr
            exact hnr hroot
        · intro hz
          have := ctx.rootz t (List.mem_of_find?_eq_some htnode)
            (by rw [node?_id_eq g q t htnode]; omega)
          rw [node?_id_eq g q t htnode] at this
          exact this
    refine ⟨q, soundFrom_A_of_g g d title hmok hd hpos hbelow ?_ hsg⟩
    show (if g.current_step = g.current_step - 1 then q else sel g.current_step) = newPid g d
    rw [if_neg (show ¬(g.current_step = g.current_step - 1) from by omega)]
    exact htop
  · -- the chain has picks in the state, and the state extends it
    have hsg : SoundFrom g sel lo := soundFrom_g_of_A g d title hnd hd hs
    obtain ⟨c, hc⟩ := h sel lo hlo0 (by omega) hsg
    refine ⟨c, soundFrom_A_of_g g d title hmok hd hpos hbelow ?_ hc⟩
    show (if g.current_step = lo - 1 then c else sel g.current_step) = newPid g d
    rw [if_neg (show ¬(g.current_step = lo - 1) from by omega)]
    exact htop

/-- info: 'AbsSat.GraphPath.Model.DescentUp.noDeadEnd_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_addNode

/-- info: 'AbsSat.GraphPath.Model.DescentUp.noDeadEnd_initSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_initSeed

end AbsSat.GraphPath.Model.DescentUp
