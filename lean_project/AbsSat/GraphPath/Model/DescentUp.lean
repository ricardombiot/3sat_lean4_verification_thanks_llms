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

/-- What a node of `addNode g d title` can be: one of the new row, or an old one
with the row ids that own it added. -/
theorem node_addNode_cases (hnd : NodupIds g)
    {y : PathNodeId} {n : PNodeM} (hn : (addNode g d title).node? y = some n) :
    (y ∈ newRowIds g d ∧ n = rowNode g d title y) ∨
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
  · obtain ⟨z, hz, rfl⟩ := (mem_newRow_iff g d title n).mp hr
    rw [rowNode_id] at hid
    rw [← hid]
    exact Or.inl ⟨hz, rfl⟩

/-- A row node's table: what its parents own, cut to the global owners, plus itself. -/
theorem owners_new (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    {z : PathNodeId} (hz : z ∈ newRowIds g d) :
    ownersOf (addNode g d title) z = rowOwners g d z := by
  simp only [ownersOf, addNode_node?_new g d title hd hbelow z hz]
  rfl

/-- An old node's table: its own, plus the row ids that own it. -/
theorem owners_old {y : PathNodeId} {m : PNodeM} (hm : g.node? y = some m) :
    ownersOf (addNode g d title) y = m.owners ++ gainedOwners g d m := by
  simp only [ownersOf, addNode_node?_old g d title y m hm]
  exact upMap_owners g d m

/-- The step of a row node. -/
theorem row_step (hd : d.step = g.current_step) {z : PathNodeId} (hz : z ∈ newRowIds g d) :
    z.id.step = g.current_step := by
  rw [mapId_of_mem_newRowIds g d z hz]; exact hd

/-- **Below the new step, a partial chain of the extended state is one of the state.** -/
theorem soundFrom_g_of_A (hnd : NodupIds g) (hd : d.step = g.current_step)
    {sel : Int → PathNodeId} {lo : Int}
    (hs : SoundFrom (addNode g d title) sel lo) : SoundFrom g sel lo := by
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  -- an old pick is a node of `g`
  have hold : ∀ k, lo ≤ k → k < g.current_step → ∃ m, g.node? (sel k) = some m := by
    intro k hk0 hk1
    obtain ⟨hsome, hstep⟩ := hs.node k hk0 (by rw [hcsA]; omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    rcases node_addNode_cases g d title hnd hn with ⟨hy, _⟩ | ⟨m, hm, _⟩
    · exfalso; rw [row_step g d hd hy] at hstep; omega
    · exact ⟨m, hm⟩
  have hnerow : ∀ k, lo ≤ k → k < g.current_step → sel k ∉ newRowIds g d := by
    intro k hk0 hk1 hmem
    obtain ⟨_, hstep⟩ := hs.node k hk0 (by rw [hcsA]; omega)
    rw [row_step g d hd hmem] at hstep
    omega
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
    rcases List.mem_append.mp hmem with hl | hr
    · rw [ownersOf, hm]
      exact List.mem_filter.mpr ⟨hl, hstep⟩
    · exact absurd (gainedOwners_subset g d m _ hr) (hnerow i hi0 hi1)
  · intro k hk0 hk1
    have hg := hs.gowner k hk0 (by rw [hcsA]; omega)
    rw [addNode_gowners] at hg
    rcases List.mem_append.mp hg with hl | hr
    · exact hl
    · exact absurd hr (hnerow k hk0 hk1)
  · intro k hk0 hk1
    obtain ⟨m, hm⟩ := hold k hk0 hk1
    have hso := hs.self_owned k hk0 (by rw [hcsA]; omega)
    rw [owners_old g d title hm] at hso
    rcases List.mem_append.mp hso with hl | hr
    · rw [ownersOf, hm]; exact hl
    · exact absurd (gainedOwners_subset g d m _ hr) (hnerow k hk0 hk1)
  · intro k hk0 hk1
    obtain ⟨m, hm⟩ := hold k hk0 (by omega)
    have hsl := hs.son_link k hk0 (by rw [hcsA]; omega)
    simp only [sonsOf, addNode_node?_old g d title (sel k) m hm, upMap_sons] at hsl
    rcases List.mem_append.mp hsl with hl | hr
    · simp only [sonsOf, hm]; exact hl
    · exact absurd (gainedSons_subset g d m _ hr) (hnerow (k + 1) (by omega) hk1)
  · intro k hk0 hk1
    exact hs.root_shape k hk0 (by rw [hcsA]; omega)

/-- **And back: a partial chain of the state, continued into the row node its own
last pick shifts to, is a partial chain of the extended state.** This is where the
row's birth table does the work — and where it differs from the single new node:
the row node owns only what *its* parents owned, so the chain that reaches it must
be the one that came up through one of them. -/
theorem soundFrom_A_of_g (_hmok : MachineOk g)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    {sel : Int → PathNodeId} {lo : Int} (hlocs : lo ≤ g.current_step - 1)
    (htop : sel g.current_step = shiftPid (sel (g.current_step - 1)) d)
    (hs : SoundFrom g sel lo) : SoundFrom (addNode g d title) sel lo := by
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  -- the chain's last pick is a parent of the row node it reaches
  obtain ⟨hsomeL, hstepL⟩ := hs.node (g.current_step - 1) (by omega) (by omega)
  obtain ⟨nL, hnL⟩ := Option.isSome_iff_exists.mp hsomeL
  have hLmem : sel (g.current_step - 1) ∈ newParents g := by
    simp only [newParents, if_pos hpos]
    exact mem_line_of_node? g _ nL hnL (g.current_step - 1) hstepL
  have hzrow : sel g.current_step ∈ newRowIds g d := by
    rw [htop]; exact mem_newRowIds_of_mem_newParents g d _ hpos hLmem
  have hzpar : sel (g.current_step - 1) ∈ rowParents g d (sel g.current_step) := by
    rw [htop]; exact mem_rowParents_of_mem_newParents g d _ hLmem
  have hnp : (sel g.current_step).id.step = g.current_step := row_step g d hd hzrow
  have hownNew : ownersOf (addNode g d title) (sel g.current_step)
      = rowOwners g d (sel g.current_step) := owners_new g d title hd hbelow hzrow
  have hold : ∀ k, lo ≤ k → k < g.current_step → ∃ m, g.node? (sel k) = some m := by
    intro k hk0 hk1
    obtain ⟨hsome, _⟩ := hs.node k hk0 hk1
    exact Option.isSome_iff_exists.mp hsome
  -- everything the chain picked below is owned by the row node it reaches
  have hpicks : ∀ i, lo ≤ i → i < g.current_step →
      sel i ∈ rowOwners g d (sel g.current_step) := by
    intro i hi1 hi2
    have hmem : sel i ∈ nL.owners := by
      rcases int_eq_or_ne i (g.current_step - 1) with hii | hii
      · have := hs.self_owned (g.current_step - 1) (by omega) (by omega)
        simp only [ownersOf, hnL] at this
        rw [hii]; exact this
      · have := hs.owned i (g.current_step - 1) hi1 (by omega) hi2 (by omega) hii
        simp only [ownersAt, List.mem_filter, ownersOf, hnL] at this
        exact this.1
    refine (mem_rowOwners_iff g d _ _).mpr (Or.inl ⟨?_, hs.gowner i hi1 hi2⟩)
    exact mem_unionOwnersOf g _ _ nL _ hzpar hnL hmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- node
    intro k hk0 hk1
    rcases int_eq_or_ne k g.current_step with rfl | hne
    · exact ⟨by rw [addNode_node?_new g d title hd hbelow _ hzrow]; rfl, hnp⟩
    · obtain ⟨m, hm⟩ := hold k hk0 (by rw [hcsA] at hk1; omega)
      obtain ⟨_, hstep⟩ := hs.node k hk0 (by rw [hcsA] at hk1; omega)
      exact ⟨by rw [addNode_node?_old g d title (sel k) m hm]; rfl, hstep⟩
  · -- parent link
    intro k hk0 hk1
    rcases int_eq_or_ne (k + 1) g.current_step with heq | hne
    · rw [heq, addNode_node?_new g d title hd hbelow _ hzrow]
      simp only [Option.map_some, Option.getD_some, rowNode_parents]
      rw [show k = g.current_step - 1 by omega]
      exact hzpar
    · obtain ⟨m, hm⟩ := hold (k + 1) (by omega) (by rw [hcsA] at hk1; omega)
      have hpl := hs.parent_link k hk0 (by rw [hcsA] at hk1; omega)
      rw [hm] at hpl
      simp only [Option.map_some, Option.getD_some] at hpl
      rw [addNode_node?_old g d title (sel (k + 1)) m hm]
      simpa only [Option.map_some, Option.getD_some, upMap_parents] using hpl
  · -- pairwise ownership
    intro i j hi0 hj0 hi1 hj1 hij
    rcases int_eq_or_ne j g.current_step with rfl | hnej
    · rw [hownNew]
      obtain ⟨_, hstep⟩ := hs.node i hi0 (by rw [hcsA] at hi1; omega)
      exact List.mem_filter.mpr
        ⟨hpicks i hi0 (by rw [hcsA] at hi1; omega), beq_iff_eq.mpr hstep⟩
    · obtain ⟨m, hm⟩ := hold j hj0 (by rw [hcsA] at hj1; omega)
      rw [owners_old g d title hm]
      rcases int_eq_or_ne i g.current_step with rfl | hnei
      · refine List.mem_filter.mpr ⟨List.mem_append_right _ (List.mem_filter.mpr ⟨hzrow, ?_⟩),
          beq_iff_eq.mpr hnp⟩
        rw [node?_id_eq g _ m hm]
        exact List.elem_eq_true_of_mem (hpicks j hj0 (by rw [hcsA] at hj1; omega))
      · have how := hs.owned i j hi0 hj0 (by rw [hcsA] at hi1; omega)
          (by rw [hcsA] at hj1; omega) hij
        rw [ownersOf, hm] at how
        obtain ⟨hmem, hstep⟩ := List.mem_filter.mp how
        exact List.mem_filter.mpr ⟨List.mem_append_left _ hmem, hstep⟩
  · -- global owner
    intro k hk0 hk1
    rw [addNode_gowners]
    rcases int_eq_or_ne k g.current_step with rfl | hne
    · exact List.mem_append_right _ hzrow
    · exact List.mem_append_left _ (hs.gowner k hk0 (by rw [hcsA] at hk1; omega))
  · -- self ownership
    intro k hk0 hk1
    rcases int_eq_or_ne k g.current_step with rfl | hne
    · rw [hownNew]; exact self_mem_rowOwners g d _
    · obtain ⟨m, hm⟩ := hold k hk0 (by rw [hcsA] at hk1; omega)
      rw [owners_old g d title hm]
      have hso := hs.self_owned k hk0 (by rw [hcsA] at hk1; omega)
      rw [ownersOf, hm] at hso
      exact List.mem_append_left _ hso
  · -- son link
    intro k hk0 hk1
    obtain ⟨m, hm⟩ := hold k hk0 (by rw [hcsA] at hk1; omega)
    simp only [sonsOf, addNode_node?_old g d title (sel k) m hm, upMap_sons]
    rcases int_eq_or_ne (k + 1) g.current_step with heq | hne
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨by rw [heq]; exact hzrow, ?_⟩)
      rw [node?_id_eq g _ m hm, show k = g.current_step - 1 by omega]
      rw [show g.current_step - 1 + 1 = g.current_step by omega]
      exact List.elem_eq_true_of_mem hzpar
    · have hsl := hs.son_link k hk0 (by rw [hcsA] at hk1; omega)
      simp only [sonsOf, hm] at hsl
      exact List.mem_append_left _ hsl
  · -- root shape
    intro k hk0 hk1
    rcases int_eq_or_ne k g.current_step with rfl | hne
    · constructor
      · intro hroot
        exact absurd hroot (parent_id_ne_none_of_mem_newRowIds g d _ hpos hzrow)
      · intro hz; omega
    · exact hs.root_shape k hk0 (by rw [hcsA] at hk1; omega)

/-- **The seed has nothing to descend**: its only step is the top one. -/
theorem noDeadEnd_initSeed (e : NodeId) (t : String) : NoDeadEnd (initSeed e t) := by
  intro sel lo hlo0 hlo _
  exfalso
  have hcs : (initSeed e t).current_step = 1 := initSeed_current e t
  rw [hcs] at hlo
  omega

/-- **An `up` keeps the descent.** With a single new node the first step down
could be *any* node of the top line; with the row it must be a parent of the row
node the chain reached — which is what the row node's table allows, and there is
always one. -/
theorem noDeadEnd_addNode (ctx : Pinned.Ctx g) (hnd : NodupIds g) (hmok : MachineOk g)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step) (_hv : isValid g = true)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (h : NoDeadEnd g) : NoDeadEnd (addNode g d title) := by
  intro sel lo hlo0 hlo hs
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  rw [hcsA] at hlo
  -- the pick at the new step is one of the row
  have hzrow : sel g.current_step ∈ newRowIds g d := by
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
  · -- the chain is the row node alone: descend into one of *its* parents
    obtain ⟨q, hq⟩ := exists_rowParent g d hpos hzrow
    obtain ⟨hqn, hqs⟩ := rowParent_node g d hpos hq
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hqn
    have hqgow : q ∈ g.gowners :=
      ctx.ownGow q t ht q (ctx.self q t ht) (by rw [hqs]; omega) (by rw [hqs]; omega)
    have hupd : upd sel (g.current_step - 1) q (g.current_step - 1) = q := by
      show (if (g.current_step - 1) = g.current_step - 1 then q else sel (g.current_step - 1)) = q
      rw [if_pos rfl]
    have hsg : SoundFrom g (upd sel (g.current_step - 1) q) (g.current_step - 1) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk0 hk1
        have hk : k = g.current_step - 1 := by omega
        subst hk
        rw [hupd]
        exact ⟨by rw [ht]; rfl, hqs⟩
      · intro k _ hk1; omega
      · intro i j hi0 hj0 hi1 hj1 hij; exfalso; omega
      · intro k hk0 hk1
        have hk : k = g.current_step - 1 := by omega
        subst hk
        rw [hupd]; exact hqgow
      · intro k hk0 hk1
        have hk : k = g.current_step - 1 := by omega
        subst hk
        rw [hupd]
        simpa only [ownersOf, ht] using ctx.self q t ht
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
            have hnr := ctx.shape.notroot t (List.mem_of_find?_eq_some ht)
              (by rw [node?_id_eq g q t ht]; omega)
            rw [node?_id_eq g q t ht] at hnr
            exact hnr hroot
        · intro hz
          have := ctx.rootz t (List.mem_of_find?_eq_some ht)
            (by rw [node?_id_eq g q t ht]; omega)
          rw [node?_id_eq g q t ht] at this
          exact this
    refine ⟨q, soundFrom_A_of_g g d title hmok hd hpos hbelow (by omega) ?_ hsg⟩
    rw [hupd]
    show (if g.current_step = g.current_step - 1 then q else sel g.current_step)
      = shiftPid q d
    rw [if_neg (show ¬(g.current_step = g.current_step - 1) from by omega)]
    exact (shiftPid_of_mem_rowParents g d _ q hq).symm
  · -- the chain has picks in the state, and the state extends it
    have hsg : SoundFrom g sel lo := soundFrom_g_of_A g d title hnd hd hs
    obtain ⟨c, hc⟩ := h sel lo hlo0 (by omega) hsg
    have hlink := hs.parent_link (g.current_step - 1) (by omega) (by rw [hcsA]; omega)
    rw [show g.current_step - 1 + 1 = g.current_step by omega,
      addNode_node?_new g d title hd hbelow _ hzrow] at hlink
    simp only [Option.map_some, Option.getD_some, rowNode_parents] at hlink
    refine ⟨c, soundFrom_A_of_g g d title hmok hd hpos hbelow (by omega) ?_ hc⟩
    show (if g.current_step = lo - 1 then c else sel g.current_step)
      = shiftPid (if g.current_step - 1 = lo - 1 then c else sel (g.current_step - 1)) d
    rw [if_neg (show ¬(g.current_step = lo - 1) from by omega),
      if_neg (show ¬(g.current_step - 1 = lo - 1) from by omega)]
    exact (shiftPid_of_mem_rowParents g d _ _ hlink).symm

/-- info: 'AbsSat.GraphPath.Model.DescentUp.noDeadEnd_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_addNode

/-- info: 'AbsSat.GraphPath.Model.DescentUp.noDeadEnd_initSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_initSeed

end AbsSat.GraphPath.Model.DescentUp
