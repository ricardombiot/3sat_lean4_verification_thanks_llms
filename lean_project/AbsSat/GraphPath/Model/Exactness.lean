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
  show (if y.id.step = g.current_step then newPid g d else sel y.id.step) = y
  rw [if_neg (show ¬(y.id.step = g.current_step) from by omega)]
  exact hsel

/-- **An `up` keeps the tables sound.** The chain that realized an entry extends with the new node,
and the new node's table is the state's global owners, each realized by the chain through itself. -/
theorem tablesSound_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (hnd : NodupIds g) (hv : isValid g = true)
    (hself : ∀ y m, g.node? y = some m → y ∈ m.owners)
    (hownBelow : ∀ y m, g.node? y = some m → ∀ w ∈ m.owners, w.id.step < g.current_step)
    (hgn : GownersNodes.GN g)
    (h : TablesSound g) : TablesSound (addNode g d title) := by
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  have hnp : (newPid g d).id.step = g.current_step := by simp only [newPid]; exact hd
  have hnodeA := addNode_node?_new g d title hd hbelow
  -- the chain of `g` through a node, extended, is a chain of `addNode g d` through it
  have hlift : ∀ (y q : PathNodeId), y.id.step < g.current_step → q.id.step < g.current_step →
      Realizes g y q → Realizes (addNode g d title) y q := by
    intro y q hy hq ⟨sel, hcs, hys, hqs⟩
    refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, ?_, ?_⟩
    · exact extend_old g d sel hy hys
    · exact extend_old g d sel hq hqs
  -- and the extended chain picks the new node at the new step
  have htop : ∀ (sel : Int → PathNodeId), extend g d sel (newPid g d).id.step = newPid g d := by
    intro sel
    rw [hnp]
    exact extend_top g d sel
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  rw [hcsA] at hx1 hq1
  by_cases hxnew : x = newPid g d
  · -- the new node: its table is `gowners`, plus itself
    subst hxnew
    rw [hnodeA] at hx
    have hn' : n = addOwner (newPid g d) (upNode g d title) := (Option.some_inj.mp hx).symm
    have how : n.owners = g.gowners ++ [newPid g d] := by rw [hn']; rfl
    have hqn' : q ∈ g.gowners ++ [newPid g d] := by rw [← how]; exact hqn
    rcases List.mem_append.mp hqn' with hgow | hnew
    · -- an old global owner: it is a node, realized by the chain through itself
      obtain ⟨mq, hmq, hmqid⟩ := hgn q hgow
      have hqnode : g.node? q = some mq := by rw [← hmqid]; exact node?_of_mem hnd mq hmq
      have hqstep : q.id.step < g.current_step := by
        have := hbelow mq hmq
        rw [hmqid] at this
        exact this
      obtain ⟨sel, hcs, _, hqs⟩ := h q mq hqnode hq0 hqstep q hq0 hqstep (hself q mq hqnode)
      refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, ?_, ?_⟩
      · exact htop sel
      · exact extend_old g d sel hqstep hqs
    · -- the new node itself: extend any chain of the state
      have hqeq : q = newPid g d := List.mem_singleton.mp hnew
      subst hqeq
      have hent := hasStepEntry_of_isValid g hv (g.current_step - 1) (by omega) (by omega)
      simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
      obtain ⟨t, htg, hts⟩ := hent
      obtain ⟨mt, hmt, hmtid⟩ := hgn t htg
      have htnode : g.node? t = some mt := by rw [← hmtid]; exact node?_of_mem hnd mt hmt
      have ht0 : 0 ≤ t.id.step := by rw [hts]; omega
      have htstep : t.id.step < g.current_step := by rw [hts]; omega
      obtain ⟨sel, hcs, _, _⟩ :=
        h t mt htnode ht0 htstep t ht0 htstep (hself t mt htnode)
      exact ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs,
        htop sel, htop sel⟩
  · -- an old node: its table is its own, plus the new node
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
        have hsing : n = addOwner (newPid g d) (upNode g d title) := List.eq_of_mem_singleton hr
        rw [hsing] at hid
        exact hxnew (by rw [← hid]; rfl)
    obtain ⟨m, hm⟩ := hold
    have hxstep : x.id.step < g.current_step := by
      have hid := node?_id_eq g x m hm
      have := hbelow m (List.mem_of_find?_eq_some hm)
      rw [hid] at this
      exact this
    rw [addNode_node?_old g d title x m hm] at hx
    have hn' : n = upMap g d m := (Option.some_inj.mp hx).symm
    have how : n.owners = m.owners ++ [newPid g d] := by rw [hn']; exact upMap_owners g d m
    have hqn' : q ∈ m.owners ++ [newPid g d] := by rw [← how]; exact hqn
    rcases List.mem_append.mp hqn' with hq | hnew
    · -- an old entry: lift its realizer
      have hqstep : q.id.step < g.current_step := hownBelow x m hm q hq
      exact hlift x q hxstep hqstep (h x m hm hx0 hxstep q hq0 hqstep hq)
    · -- the new node: extend the chain through `x`
      have hqeq : q = newPid g d := List.mem_singleton.mp hnew
      subst hqeq
      obtain ⟨sel, hcs, hxs, _⟩ := h x m hm hx0 hxstep x hx0 hxstep (hself x m hm)
      refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, ?_, ?_⟩
      · exact extend_old g d sel hxstep hxs
      · exact htop sel

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
