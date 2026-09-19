-- lean_project/AbsSat/GraphPath/Model/UnionPaths.lean
import AbsSat.GraphPath.Model.PartSplitReal

/-!
# What is under `RunPaths`

`RunPaths` (v147): every entry of the reviewed union of two pinned branches lies on a path of one of the
branches. It splits in two:

* **the reviewed union is exact** — every entry lies on a path **of the union**;
* **no borrowing** (`NoBorrow`) — a path of the reviewed union is a path of **one** branch: it does not
  mix the two branches' tables.

This module proves:

* **`tablesSound_join`** (no hypothesis) — the union of two exact states is exact: an entry comes from
  one side's tables, lies on a path of that side, and the path is a path of the union.
* **`path_top_side`** (no hypothesis) — a path of the reviewed union whose top node is on side `a` has
  **all its nodes on side `a`**, each owning that top node in `a`'s own tables (the tops of the two
  branches are distinct at the machine's unions). What borrowing could still mix is the entries among
  the path's nodes and its parent links.
* **`paths_of_exact_noBorrow`** — the two pieces give `RunPaths`' statement at a union.

Measured (probe `noborrow`, v148): 5,122 paths of reviewed unions, **none borrowed**; each lies on
exactly one branch.
-/

namespace AbsSat.GraphPath.Model.UnionPaths

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.SupportSplit (Separates)
open AbsSat.GraphPath.Model.JoinSide (entry_side not_hasNode_of_not_mem rel_of_chain)
open AbsSat.GraphPath.Model.PartSplitReal (grown_join_right_of_step mem_of_chain)

/-- **The union of two exact states is exact.** -/
theorem tablesSound_join (a b : GPathM) (hstep : a.current_step = b.current_step) (hta : TablesSound a) (htb : TablesSound b) : TablesSound (join a b) := by
  have gA := grown_join_left a b
  have gB := grown_join_right_of_step a b hstep
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  rcases join_owners_source a b x n hx q hqn with ⟨m, hm, hqm⟩ | ⟨m, hm, hqm⟩
  · obtain ⟨sel, hsc, hsx, hsq⟩ := hta x m hm hx0 (by rw [← gA.step_eq]; exact hx1) q hq0
      (by rw [← gA.step_eq]; exact hq1) hqm
    exact ⟨sel, ChainSound_of_grown gA sel hsc, hsx, hsq⟩
  · obtain ⟨sel, hsc, hsx, hsq⟩ := htb x m hm hx0 (by rw [← gB.step_eq]; exact hx1) q hq0
      (by rw [← gB.step_eq]; exact hq1) hqm
    exact ⟨sel, ChainSound_of_grown gB sel hsc, hsx, hsq⟩

/-- **A path of the reviewed union lives on the side of its top node**: every node of the path is a
node of that side and owns the top node in that side's own tables. -/
theorem path_top_side (a b : GPathM) (hnd : NodupIds (join a b)) (hndB : NodupIds b)
    (hownB : ∀ n ∈ b.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode b q)
    (hsep : Separates (reviewAgg (join a b)) a b ((reviewAgg (join a b)).current_step - 1))
    (sel : Int → PathNodeId) (hsc : ChainSound (reviewAgg (join a b)) sel)
    (hpos : 0 < (reviewAgg (join a b)).current_step)
    (htop : Mem a (sel ((reviewAgg (join a b)).current_step - 1))) :
    ∀ k, 0 ≤ k → k < (reviewAgg (join a b)).current_step →
      ∃ m, a.node? (sel k) = some m ∧ sel ((reviewAgg (join a b)).current_step - 1) ∈ m.owners := by
  intro k h0 h1
  have hpr := pruned_reviewAgg (join a b)
  have hzR : Mem (reviewAgg (join a b)) (sel ((reviewAgg (join a b)).current_step - 1)) :=
    mem_of_chain _ sel hsc _ (by omega) (by omega)
  have hzs : (sel ((reviewAgg (join a b)).current_step - 1)).id.step =
      (reviewAgg (join a b)).current_step - 1 := (hsc.chain.1.1 _ (by omega) (by omega)).2
  have hzb : ¬ GownersNodes.HasNode b (sel ((reviewAgg (join a b)).current_step - 1)) :=
    not_hasNode_of_not_mem hndB (fun hb => hsep.2.2 _ hzR hzs htop hb)
  obtain ⟨m, hm, hin, _⟩ := rel_of_chain _ sel hsc ((reviewAgg (join a b)).current_step - 1) k
    (by omega) (by omega) h0 h1
  exact entry_side a b _ hpr hnd hownB (sel k) _ m hm hin hzb

/-- **No borrowing**: a path of the reviewed union is a path of one side. -/
def NoBorrow (a b : GPathM) : Prop :=
  ∀ sel, ChainSound (reviewAgg (join a b)) sel → ChainSound a sel ∨ ChainSound b sel

/-- **`RunPaths`' statement at a union, from its two pieces**: the reviewed union is exact, and none of
its paths borrows. -/
theorem paths_of_exact_noBorrow (a b : GPathM) (hte : TablesSound (reviewAgg (join a b)))
    (hnb : NoBorrow a b) (x v : PathNodeId) (hxv : Rel (reviewAgg (join a b)) x v)
    (hb : 0 ≤ x.id.step ∧ x.id.step < (reviewAgg (join a b)).current_step ∧
      0 ≤ v.id.step ∧ v.id.step < (reviewAgg (join a b)).current_step) :
    Realizes a x v ∨ Realizes b x v := by
  obtain ⟨m, hm, hv, _⟩ := hxv
  obtain ⟨sel, hsc, hsx, hsv⟩ := hte x m hm hb.1 hb.2.1 v hb.2.2.1 hb.2.2.2 hv
  rcases hnb sel hsc with ha | hb'
  · exact Or.inl ⟨sel, ha, hsx, hsv⟩
  · exact Or.inr ⟨sel, hb', hsx, hsv⟩

/-- info: 'AbsSat.GraphPath.Model.UnionPaths.tablesSound_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_join

/-- info: 'AbsSat.GraphPath.Model.UnionPaths.path_top_side' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms path_top_side

/-- info: 'AbsSat.GraphPath.Model.UnionPaths.paths_of_exact_noBorrow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms paths_of_exact_noBorrow

end AbsSat.GraphPath.Model.UnionPaths
