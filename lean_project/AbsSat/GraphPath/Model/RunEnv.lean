-- lean_project/AbsSat/GraphPath/Model/RunEnv.lean
import AbsSat.GraphPath.Model.Up
import AbsSat.GraphPath.Model.Join
import AbsSat.GraphPath.Model.AggressiveReview

/-!
# Nothing is invented: the tables a node may ever carry

The author's design fact. A `PathNodeId` is a pair **(destination, origin)**, an `up` is tied to
exactly one such pair, and the keys of a line are unique (`PureDriver.key_inj`), so the node
`(d, q)` is created by **one** `up`, from the one state keyed `q`. A node's table can therefore
only ever be a pruning of the table that `up` gave it — the destination may be reached by many
histories, but each of them enters through a node the identifier names.

This file carries that as a run invariant, in the form the proof needs: a **bound** on the tables.

* `Env`, `Within` — a bound per node id, and a state whose every table sits inside it.
* `Within_of_pruned` — every pruning stays inside the bound: filters and reviews only remove.
* `Within_join` — **a join stays inside the bound**: by `Join.join_owners_source` every entry of a
  joined node comes from one of the two sides, so the union of two bounded tables is bounded. This
  is the formal content of "the join unites different histories of the same destination without
  inventing anything".
* `Within_addNode` — an `up` stays inside the bound once the bound is extended by the new node,
  which is what `addNode` appends to every table.

The payoff for `JoinSplit` (v128–v130): at a join, the two sides' tables for a node they share are
**prunings of one and the same table**, so an entry only one side carries is one the other side
*pruned* — not one it never had.
-/

namespace AbsSat.GraphPath.Model.RunEnv

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- A bound on the tables: for each node id, the entries it may own. -/
abbrev Env := PathNodeId → List PathNodeId

/-- Every table of the state sits inside the bound. -/
def Within (E : Env) (g : GPathM) : Prop :=
  ∀ y n, g.node? y = some n → ∀ w ∈ n.owners, w ∈ E y

/-- A wider bound is still a bound. -/
theorem Within_mono {E E' : Env} {g : GPathM} (hsub : ∀ y, ∀ w ∈ E y, w ∈ E' y)
    (h : Within E g) : Within E' g :=
  fun y n hn w hw => hsub y w (h y n hn w hw)

/-- **Every pruning stays inside the bound.** The filters and the reviews only remove. -/
theorem Within_of_pruned {E : Env} {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (h : Within E g) : Within E g' := by
  intro y n hn w hw
  have hnB : n ∈ g'.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = y := node?_id_eq g' y n hn
  obtain ⟨n₀, hn₀, hids, hown, _⟩ := hpr.nodes_derived n hnB
  have h₀ : g.node? y = some n₀ := by
    have := node?_of_mem hnd n₀ hn₀
    rw [← hids, hid] at this
    exact this
  exact h y n₀ h₀ w (hown w hw)

/-- **A join stays inside the bound.** Every entry of a joined node comes from one of the two
sides, so a common bound for the sides bounds the join: the union of two histories of the same
destination invents nothing. -/
theorem Within_join {E : Env} {g₁ g₂ : GPathM} (h₁ : Within E g₁) (h₂ : Within E g₂) :
    Within E (join g₁ g₂) := by
  intro y n hn w hw
  rcases join_owners_source g₁ g₂ y n hn w hw with ⟨m, hm, hwm⟩ | ⟨m, hm, hwm⟩
  · exact h₁ y m hm w hwm
  · exact h₂ y m hm w hwm

-- ============================================================
-- The `up`
-- ============================================================

/-- The bound `addNode` needs: every old node gains the new id, and the new node gains the state's
global owners. -/
def upEnv (E : Env) (g : GPathM) (d : NodeId) : Env := fun y =>
  if y == newPid g d then g.gowners ++ [newPid g d] else E y ++ [newPid g d]

/-- The record `addNode` gives the new node. -/
private theorem addNode_node?_new (g : GPathM) (d : NodeId) (title : String)
    (hnone : g.node? (newPid g d) = none) :
    (addNode g d title).node? (newPid g d) = some (addOwner (newPid g d) (upNode g d title)) := by
  have hp : (fun x : PNodeM => (upMap g d x).id == newPid g d)
      = (fun x : PNodeM => x.id == newPid g d) := by
    funext x; rw [upMap_id]
  have hnodes : g.nodes.find? (fun x : PNodeM => x.id == newPid g d) = none := hnone
  simp only [node?, addNode_nodes, List.find?_append, List.find?_map, Function.comp_def, hp,
    hnodes, Option.map_none, Option.none_or, List.find?_cons]
  have hid : (addOwner (newPid g d) (upNode g d title)).id = newPid g d := rfl
  simp only [hid, beq_self_eq_true]

/-- **An `up` stays inside the extended bound.** -/
theorem Within_addNode {E : Env} (g : GPathM) (d : NodeId) (title : String)
    (hnone : g.node? (newPid g d) = none) (h : Within E g) :
    Within (upEnv E g d) (addNode g d title) := by
  intro y n hn w hw
  by_cases hy : y = newPid g d
  · subst hy
    rw [addNode_node?_new g d title hnone] at hn
    have hn' : n = addOwner (newPid g d) (upNode g d title) := (Option.some_inj.mp hn).symm
    have how : n.owners = g.gowners ++ [newPid g d] := by rw [hn']; rfl
    rw [how] at hw
    simp only [upEnv, beq_self_eq_true, if_pos]
    exact hw
  · have hold : ∃ m, g.node? y = some m := by
      have hnB : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn
      have hid : n.id = y := node?_id_eq _ y n hn
      rw [addNode_nodes] at hnB
      rcases List.mem_append.mp hnB with hl | hr
      · obtain ⟨n₀, hn₀, heq⟩ := List.mem_map.mp hl
        have hid₀ : n₀.id = y := by rw [← hid, ← heq, upMap_id]
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_mem g n₀ hn₀)
        rw [hid₀] at hm
        exact ⟨m, hm⟩
      · exfalso
        have hsing : n = addOwner (newPid g d) (upNode g d title) := List.eq_of_mem_singleton hr
        rw [hsing] at hid
        exact hy (by rw [← hid]; rfl)
    obtain ⟨m, hm⟩ := hold
    rw [addNode_node?_old g d title y m hm] at hn
    have hn' : n = upMap g d m := (Option.some_inj.mp hn).symm
    have how : n.owners = m.owners ++ [newPid g d] := by rw [hn']; exact upMap_owners g d m
    rw [how] at hw
    simp only [upEnv, show (y == newPid g d) = false from by
      cases hb : (y == newPid g d) with
      | true => exact absurd (eq_of_beq hb) hy
      | false => rfl]
    rcases List.mem_append.mp hw with hl | hr
    · exact List.mem_append_left _ (h y m hm w hl)
    · exact List.mem_append_right _ hr


-- ============================================================
-- The stable form: bound only the past
-- ============================================================

/-- **The bound on the past of each node.** An `up` appends the new top node to every table, so a
bound on the whole table has to grow at every step; a bound on the entries **at or below the
node's own step** does not. That is the stable form of the invariant, and the one the proof uses:
the past of a node is bounded by the past its birth state had. -/
def WithinBelow (E : Env) (g : GPathM) : Prop :=
  ∀ y n, g.node? y = some n → ∀ w ∈ n.owners, w.id.step ≤ y.id.step → w ∈ E y

theorem WithinBelow_of_pruned {E : Env} {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (h : WithinBelow E g) : WithinBelow E g' := by
  intro y n hn w hw hstep
  have hnB : n ∈ g'.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = y := node?_id_eq g' y n hn
  obtain ⟨n₀, hn₀, hids, hown, _⟩ := hpr.nodes_derived n hnB
  have h₀ : g.node? y = some n₀ := by
    have hq := node?_of_mem hnd n₀ hn₀
    rw [← hids, hid] at hq
    exact hq
  exact h y n₀ h₀ w (hown w hw) hstep

/-- **A join keeps the bound on the past**, with no extension: the two sides' tables for a node
they share are prunings of one and the same table, so their union is too. -/
theorem WithinBelow_join {E : Env} {g₁ g₂ : GPathM} (h₁ : WithinBelow E g₁)
    (h₂ : WithinBelow E g₂) : WithinBelow E (join g₁ g₂) := by
  intro y n hn w hw hstep
  rcases join_owners_source g₁ g₂ y n hn w hw with ⟨m, hm, hwm⟩ | ⟨m, hm, hwm⟩
  · exact h₁ y m hm w hwm hstep
  · exact h₂ y m hm w hwm hstep

/-- The bound at birth: the new node's past is the state's global owners, plus itself. -/
def bornEnv (E : Env) (g : GPathM) (d : NodeId) : Env := fun y =>
  if y == newPid g d then g.gowners ++ [newPid g d] else E y

/-- **An `up` keeps the bound on the past**, extended only at the node it creates. The old nodes
gain the new top node, which lies *above* them, so their bound is untouched — that is what makes
this form of the invariant stable along the whole run. -/
theorem WithinBelow_addNode {E : Env} (g : GPathM) (d : NodeId) (title : String)
    (hnone : g.node? (newPid g d) = none) (hd : g.current_step ≤ d.step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (h : WithinBelow E g) : WithinBelow (bornEnv E g d) (addNode g d title) := by
  have hnp : (newPid g d).id.step = d.step := rfl
  intro y n hn w hw hstep
  by_cases hy : y = newPid g d
  · subst hy
    rw [addNode_node?_new g d title hnone] at hn
    have hn' : n = addOwner (newPid g d) (upNode g d title) := (Option.some_inj.mp hn).symm
    have how : n.owners = g.gowners ++ [newPid g d] := by rw [hn']; rfl
    rw [how] at hw
    simpa only [bornEnv, beq_self_eq_true, if_pos] using hw
  · have hold : ∃ m, g.node? y = some m := by
      have hnB : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn
      have hid : n.id = y := node?_id_eq _ y n hn
      rw [addNode_nodes] at hnB
      rcases List.mem_append.mp hnB with hl | hr
      · obtain ⟨n₀, hn₀, heq⟩ := List.mem_map.mp hl
        have hid₀ : n₀.id = y := by rw [← hid, ← heq, upMap_id]
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_mem g n₀ hn₀)
        rw [hid₀] at hm
        exact ⟨m, hm⟩
      · exfalso
        have hsing : n = addOwner (newPid g d) (upNode g d title) := List.eq_of_mem_singleton hr
        rw [hsing] at hid
        exact hy (by rw [← hid]; rfl)
    obtain ⟨m, hm⟩ := hold
    have hybelow : y.id.step < g.current_step := by
      have hmem := List.mem_of_find?_eq_some hm
      have hid := node?_id_eq g y m hm
      have := hbelow m hmem
      rw [hid] at this
      exact this
    rw [addNode_node?_old g d title y m hm] at hn
    have hn' : n = upMap g d m := (Option.some_inj.mp hn).symm
    have how : n.owners = m.owners ++ [newPid g d] := by rw [hn']; exact upMap_owners g d m
    rw [how] at hw
    simp only [bornEnv, show (y == newPid g d) = false from by
      cases hb : (y == newPid g d) with
      | true => exact absurd (eq_of_beq hb) hy
      | false => rfl]
    rcases List.mem_append.mp hw with hl | hr
    · exact h y m hm w hl hstep
    · exfalso
      have hwe := List.mem_singleton.mp hr
      rw [hwe, hnp] at hstep
      omega

/-- A wider bound on the past is still a bound. -/
theorem WithinBelow_mono {E E' : Env} {g : GPathM} (hsub : ∀ y, ∀ w ∈ E y, w ∈ E' y)
    (h : WithinBelow E g) : WithinBelow E' g :=
  fun y n hn w hw hstep => hsub y w (h y n hn w hw hstep)

/-- **The birth of a node touches the bound of no other node.** With the keys of a line unique,
an `up` is tied to one pair (destination, origin), so the extensions of different sends never
collide: this is what lets the bound be carried along the whole run. -/
theorem bornEnv_ne {E : Env} (g : GPathM) (d : NodeId) {y : PathNodeId} (hy : y ≠ newPid g d) :
    bornEnv E g d y = E y := by
  simp only [bornEnv, show (y == newPid g d) = false from by
    cases hb : (y == newPid g d) with
    | true => exact absurd (eq_of_beq hb) hy
    | false => rfl, Bool.false_eq_true, if_false]

/-- Every state of a line is bounded on its past by one common bound. -/
def LineWithinBelow (E : Env) (L : List (NodeId × GPathM)) : Prop :=
  ∀ kv ∈ L, WithinBelow E kv.2

/-- info: 'AbsSat.GraphPath.Model.RunEnv.WithinBelow_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WithinBelow_join

/-- info: 'AbsSat.GraphPath.Model.RunEnv.Within_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Within_join

/-- info: 'AbsSat.GraphPath.Model.RunEnv.Within_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Within_addNode

/-- info: 'AbsSat.GraphPath.Model.RunEnv.WithinBelow_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WithinBelow_addNode

end AbsSat.GraphPath.Model.RunEnv
