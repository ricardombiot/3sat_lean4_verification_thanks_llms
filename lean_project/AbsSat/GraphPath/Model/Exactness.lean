-- lean_project/AbsSat/GraphPath/Model/Exactness.lean
import AbsSat.GraphPath.Model.AddNode
import AbsSat.GraphPath.Model.JoinSound
import AbsSat.GraphPath.Model.L6
import AbsSat.GraphPath.Model.L6Up
import AbsSat.GraphPath.Model.Join
import AbsSat.GraphPath.Model.GownersNodes
import AbsSat.GraphPath.Model.Filter

/-!
# Exact tables: the construction route

`CommonOwner` (v133, v134) is the one statement the SAT verdict rests on, and it is equivalent to
the **exactness** of the machine's tables: the owners of a node are exactly the choices that some
complete path through it makes. This file takes exactness as the invariant and attacks it **by
construction**, one operation at a time.

Exactness splits in two halves, and they are very different:

* `Realizes g x q` — some `ChainSound` chain of `g` passes through `x` and picks `q`.
* `TablesComplete` (realizable ⇒ in the table) — **a theorem for every state, with no induction at
  all** (`tablesComplete`): a chain is pairwise owned, so whatever it picks is already in the table.
* `TablesSound` (in the table ⇒ realizable) — the half that carries the weight. Closed here for
  three of the four operations:
  * `tablesSound_initSeed` — the seed.
  * `tablesSound_addNode` — **an `up`**: the chain that realized an old entry extends with the new
    node (`ChainSound_addNode`), and the new node's own table is the state's global owners, each of
    them realized by the chain through itself.
  * `tablesSound_join` — **a join**, and this one is free: every entry of a joined node comes from
    one side (`join_owners_source`), the chain realizing it there is a chain of the join
    (`ChainSound_join_left` / `_right`), and it passes through the same nodes.

What is left is **one operation and one direction**: `FilterSound`, the filter's soundness half. An
entry that survives the pins and the review was realizable before, but its realizer may break the
pin, and re-realizing it is the descent itself.
-/

namespace AbsSat.GraphPath.Model.Exactness

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- **`q` is realized at `x`**: a complete chain of `g` passes through `x` and picks `q`. -/
def Realizes (g : GPathM) (x q : PathNodeId) : Prop :=
  ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel q.id.step = q

/-- **Nothing realizable is missing from the tables.** -/
def TablesComplete (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → 0 ≤ x.id.step → x.id.step < g.current_step →
    ∀ q, 0 ≤ q.id.step → q.id.step < g.current_step → Realizes g x q → q ∈ n.owners

/-- **Nothing in the tables is unrealizable.** -/
def TablesSound (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → 0 ≤ x.id.step → x.id.step < g.current_step →
    ∀ q, 0 ≤ q.id.step → q.id.step < g.current_step → q ∈ n.owners → Realizes g x q

/-- The tables say exactly what the paths say. -/
def Exact (g : GPathM) : Prop := TablesComplete g ∧ TablesSound g

-- ============================================================
-- The easy half, for every state and with no induction
-- ============================================================

/-- **Whatever a chain picks is already in the table.** A `ChainSound` chain is pairwise owned, so
this half of exactness holds of *every* state: there is nothing to carry along the construction. -/
theorem tablesComplete (g : GPathM) : TablesComplete g := by
  intro x n hx hx0 hx1 q hq0 hq1 ⟨sel, hcs, hxs, hqs⟩
  rcases int_eq_or_ne q.id.step x.id.step with heq | hne
  · -- same step: the pick is `x` itself, and a node owns itself along a chain
    have hqx : q = x := by rw [← hqs, heq, hxs]
    rw [hqx]
    have hself := hcs.self_owned x.id.step hx0 hx1
    rw [hxs] at hself
    simpa only [ownersOf, hx] using hself
  · have how := hcs.chain.2.1 q.id.step x.id.step hq0 hx0 hq1 hx1 hne
    rw [hqs, hxs] at how
    have h' := (List.mem_filter.mp how).1
    simpa only [ownersOf, hx] using h'

-- ============================================================
-- The seed
-- ============================================================

/-- **The seed's table is exact.** Its only node owns only itself, and the constant chain realizes
that. -/
theorem tablesSound_initSeed (d : NodeId) (title : String) (hd : d.step = 0) :
    TablesSound (initSeed d title) := by
  intro x n hx _ hx1 q hq0 hq1 hqn
  have hcs : (initSeed d title).current_step = 1 := initSeed_current d title
  rw [hcs] at hx1 hq1
  -- the seed has exactly one node
  have hnodes := initSeed_nodes d title
  have hmem : n ∈ (initSeed d title).nodes := List.mem_of_find?_eq_some hx
  rw [hnodes, List.mem_singleton] at hmem
  have hid : n.id = x := node?_id_eq _ x n hx
  have hxroot : x = { id := d, parent_id := none } := by rw [← hid, hmem]
  have hqroot : q = { id := d, parent_id := none } := by
    rw [hmem] at hqn
    exact List.mem_singleton.mp hqn
  refine ⟨fun _ => { id := d, parent_id := none }, ChainSound_initSeed d title hd, ?_, ?_⟩
  · rw [hxroot]
  · rw [hqroot]

-- ============================================================
-- The `up`
-- ============================================================

/-- The extended chain still passes through an old node. -/
private theorem extend_old (g : GPathM) (d : NodeId) (sel : Int → PathNodeId) {y : PathNodeId}
    (hy : y.id.step < g.current_step) (hsel : sel y.id.step = y) :
    extend g d sel y.id.step = y := by
  show (if y.id.step = g.current_step then extendPid g d sel else sel y.id.step) = y
  rw [if_neg (show ¬(y.id.step = g.current_step) from by omega)]
  exact hsel

/-- **An `up` keeps the tables sound.** The chain that realized an entry extends with the new node,
and the new node's table is the state's global owners, each realized by the chain through itself. -/
theorem tablesSound_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (_hnd : NodupIds g) (_hv : isValid g = true)
    (hself : ∀ y m, g.node? y = some m → y ∈ m.owners)
    (hownBelow : ∀ y m, g.node? y = some m → ∀ w ∈ m.owners, w.id.step < g.current_step)
    (_hgn : GownersNodes.GN g)
    (h : TablesSound g) : TablesSound (addNode g d title) := by
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  -- A chain of `g` through a node, extended, is a chain of the extended state through it.
  have hlift : ∀ (y q : PathNodeId), y.id.step < g.current_step → q.id.step < g.current_step →
      Realizes g y q → Realizes (addNode g d title) y q := by
    intro y q hy hq ⟨sel, hcs, hys, hqs⟩
    refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, ?_, ?_⟩
    · exact extend_old g d sel hy hys
    · exact extend_old g d sel hq hqs
  -- **The row version of `htop`.** Which node of the row the extended chain reaches is
  -- decided by the chain's own last pick, so it is reached only by the chains that come
  -- up through one of its parents.
  have htop : ∀ (sel : Int → PathNodeId) (p pid : PathNodeId), p ∈ rowParents g d pid →
      sel (g.current_step - 1) = p → pid.id.step = g.current_step →
      extend g d sel pid.id.step = pid := by
    intro sel p pid hp hsel hstep
    rw [hstep, extend_top]
    unfold extendPid
    rw [if_pos hpos, hsel]
    exact shiftPid_of_mem_rowParents g d pid p hp
  -- A parent of a row node carries a chain of `g` ending at it.
  have hparent : ∀ pid ∈ newRowIds g d, ∀ p ∈ rowParents g d pid,
      ∃ mp, g.node? p = some mp ∧ p.id.step = g.current_step - 1 := by
    intro pid _ p hp
    have hpmem : p ∈ newParents g := rowParents_subset g d pid p hp
    unfold newParents at hpmem
    rw [if_pos hpos] at hpmem
    obtain ⟨np, hnp, hnpid⟩ := List.mem_map.mp hpmem
    have hmemp : np ∈ g.nodes := (List.mem_filter.mp hnp).1
    have hsomep : (g.node? p).isSome = true := by
      have := node?_isSome_of_mem g np hmemp; rwa [hnpid] at this
    obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp hsomep
    exact ⟨mp, hmp, by rw [← hnpid]; exact eq_of_beq (List.mem_filter.mp hnp).2⟩
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  rw [hcsA] at hx1 hq1
  by_cases hxnew : x ∈ newRowIds g d
  · -- a node of the new row: its table is what its parents own, plus itself
    have hxstep : x.id.step = g.current_step := by
      rw [mapId_of_mem_newRowIds g d x hxnew]; exact hd
    rw [addNode_node?_new g d title hd hbelow x hxnew] at hx
    have hn' : n = rowNode g d title x := (Option.some_inj.mp hx).symm
    have hqn' : q ∈ rowOwners g d x := by rw [hn'] at hqn; exact hqn
    rcases (mem_rowOwners_iff g d x q).mp hqn' with ⟨hinh, _⟩ | rfl
    · -- inherited: the parent that owns `q` carries the chain
      obtain ⟨p, hp, mp, hmp, hqmp⟩ := exists_owner_of_mem_unionOwnersOf g _ q hinh
      obtain ⟨_, _, hpstep⟩ := hparent x hxnew p hp
      have hqstep : q.id.step < g.current_step := hownBelow p mp hmp q hqmp
      obtain ⟨sel, hcs, hps, hqs⟩ :=
        h p mp hmp (by omega) (by omega) q hq0 hqstep hqmp
      refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, ?_, ?_⟩
      · exact htop sel p x hp (by rw [← hpstep]; exact hps) hxstep
      · exact extend_old g d sel hqstep hqs
    · -- itself: any parent's chain will do
      obtain ⟨p, hp⟩ : ∃ p, p ∈ rowParents g d q := by
        obtain ⟨r, hr, hrq⟩ := exists_shift_of_mem_newRowIds g d q hpos hxnew
        exact ⟨r, List.mem_filter.mpr ⟨hr, beq_iff_eq.mpr hrq.symm⟩⟩
      obtain ⟨mp, hmp, hpstep⟩ := hparent q hxnew p hp
      obtain ⟨sel, hcs, hps, _⟩ :=
        h p mp hmp (by omega) (by omega) p (by omega) (by omega) (hself p mp hmp)
      have htp := htop sel p q hp (by rw [← hpstep]; exact hps) hxstep
      exact ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, htp, htp⟩
  · -- an old node: its table is its own, plus the row ids that own it
    have hold : ∃ m, g.node? x = some m := by
      have hnB : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hx
      have hid : n.id = x := node?_id_eq _ x n hx
      rw [addNode_nodes] at hnB
      rcases List.mem_append.mp hnB with hl | hr
      · obtain ⟨n₀, hn₀, heq⟩ := List.mem_map.mp hl
        have hid₀ : n₀.id = x := by rw [← hid, ← heq, upMap_id]
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_mem g n₀ hn₀)
        rw [hid₀] at hm
        exact ⟨m, hm⟩
      · exfalso
        obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title n).mp hr
        exact hxnew (by rw [← hid]; exact hpid)
    obtain ⟨m, hm⟩ := hold
    have hxstep : x.id.step < g.current_step := by
      have hid := node?_id_eq g x m hm
      have := hbelow m (List.mem_of_find?_eq_some hm)
      rw [hid] at this
      exact this
    rw [addNode_node?_old g d title x m hm] at hx
    have hn' : n = upMap g d m := (Option.some_inj.mp hx).symm
    have how : n.owners = m.owners ++ gainedOwners g d m := by rw [hn']; exact upMap_owners g d m
    have hqn' : q ∈ m.owners ++ gainedOwners g d m := by rw [← how]; exact hqn
    rcases List.mem_append.mp hqn' with hq | hnew
    · -- an old entry: lift its realizer
      have hqstep : q.id.step < g.current_step := hownBelow x m hm q hq
      exact hlift x q hxstep hqstep (h x m hm hx0 hxstep q hq0 hqstep hq)
    · -- a row id that owns `x`: the chain is the one through the parent that owns `x`
      have hqrow : q ∈ newRowIds g d := gainedOwners_subset g d m q hnew
      have hqstep : q.id.step = g.current_step := by
        rw [mapId_of_mem_newRowIds g d q hqrow]; exact hd
      have hxown : x ∈ rowOwners g d q := by
        have := (List.mem_filter.mp hnew).2
        have hmid : m.id = x := node?_id_eq g x m hm
        rw [hmid] at this
        simpa using this
      rcases (mem_rowOwners_iff g d q x).mp hxown with ⟨hinh, _⟩ | rfl
      · obtain ⟨p, hp, mp, hmp, hxmp⟩ := exists_owner_of_mem_unionOwnersOf g _ x hinh
        obtain ⟨_, _, hpstep⟩ := hparent q hqrow p hp
        obtain ⟨sel, hcs, hps, hxs⟩ :=
          h p mp hmp (by omega) (by omega) x hx0 hxstep hxmp
        refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, ?_, ?_⟩
        · exact extend_old g d sel hxstep hxs
        · exact htop sel p q hp (by rw [← hpstep]; exact hps) hqstep
      · exact absurd hxstep (by rw [hqstep]; omega)

-- ============================================================
-- The join
-- ============================================================

/-- **A join keeps the tables sound, for free.** Every entry of a joined node comes from one of the
sides; the chain that realizes it there is a chain of the join, through the same nodes. -/
theorem tablesSound_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : TablesSound g₁) (h₂ : TablesSound g₂) : TablesSound (join g₁ g₂) := by
  have hs1 : (join g₁ g₂).current_step = g₁.current_step := (grown_join_left g₁ g₂).step_eq
  have hs2 : (join g₁ g₂).current_step = g₂.current_step := (grown_join_right g₁ g₂ hok).step_eq
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  rcases join_owners_source g₁ g₂ x n hx q hqn with ⟨m, hm, hqm⟩ | ⟨m, hm, hqm⟩
  · obtain ⟨sel, hcs, hxs, hqs⟩ := h₁ x m hm hx0 (by rw [← hs1]; exact hx1) q hq0
      (by rw [← hs1]; exact hq1) hqm
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hcs, hxs, hqs⟩
  · obtain ⟨sel, hcs, hxs, hqs⟩ := h₂ x m hm hx0 (by rw [← hs2]; exact hx1) q hq0
      (by rw [← hs2]; exact hq1) hqm
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hcs, hxs, hqs⟩

-- ============================================================
-- What is left
-- ============================================================

/-- **The residue of the construction route**: the filter's soundness half. An entry that survives
the pins and the aggressive review is realizable in the filtered state. Everything else about
exactness is proved: the completeness half for every state (`tablesComplete`), and the soundness
half for the seed, the `up` and the join. -/
def FilterSound (φFilter : GPathM → GPathM) : Prop :=
  ∀ g, TablesSound g → TablesSound (φFilter g)

/-- info: 'AbsSat.GraphPath.Model.Exactness.tablesComplete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesComplete

/-- info: 'AbsSat.GraphPath.Model.Exactness.tablesSound_initSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_initSeed

/-- info: 'AbsSat.GraphPath.Model.Exactness.tablesSound_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_addNode

/-- info: 'AbsSat.GraphPath.Model.Exactness.tablesSound_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_join

end AbsSat.GraphPath.Model.Exactness
