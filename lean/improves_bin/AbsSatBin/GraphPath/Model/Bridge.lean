-- lean/improves_bin/AbsSatBin/GraphPath/Model/Bridge.lean
import AbsSatBin.GraphPath.Model.ParentId

/-!
**The bridge between the owners ledger and the parents ledger, as a theorem.**

v36 measured the two ledgers apart: 37 stale parent links and 71 stale son
links per ~328,000, because ownership pruning never unlinked a neighbour. The
author identified that as a bug and gave the semantics — *pruning the owners
must unlink the incompatible parents, and a node left without parents is
invalid and must go*. The executable does it (`unlink_incompatible!`, validated
800/800 against the brute-force oracle) and the mirror now does it too
(`GPathM.unlinkIncompatible`, wired into `cleanInvalidGo` and `reviewNode`).

This module states what the fix buys and proves it.

    LinksInOwners h : every parent and every son of a node is one of its owners

**`linksInOwners_review` proves it of every valid `review` fixpoint** — which
is where `filterAll` lands, and so where every obligation about the machine's
states lives. What was refuted in v36 (`ParentId.ParentIsOwner`) is now a
theorem about the fixed machine.

The route is short because the migration did the work: at the fixpoint every
node is its own cut (`Fuel.review_cut_fixed`), and the cut keeps a link only
when the node's own cut table admits it.
-/

namespace AbsSatBin.GraphPath.Model.Bridge

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM

/-- **The bridge.** Every parent and every son of a node is one of its owners.
Refuted before the author's fix (`ParentId.ParentIsOwner`, 37 witnesses that
scaled with campaign size); a theorem after it. -/
def LinksInOwners (h : GPathM) : Prop :=
  ∀ pid d, h.node? pid = some d →
    (∀ p ∈ d.parents, p ∈ d.owners) ∧ (∀ s ∈ d.sons, s ∈ d.owners)

/-- A node whose re-link is the identity already had its links inside its
owners. -/
theorem links_of_relinkSelf_eq (d : PNodeM) (h : relinkSelf d = d) :
    (∀ p ∈ d.parents, p ∈ d.owners) ∧ (∀ s ∈ d.sons, s ∈ d.owners) := by
  have hp : d.parents.filter (fun p => d.owners.contains p) = d.parents :=
    congrArg PNodeM.parents h
  have hs : d.sons.filter (fun s => d.owners.contains s) = d.sons :=
    congrArg PNodeM.sons h
  constructor
  · intro p hpm
    rw [← hp] at hpm
    exact List.elem_iff.mp (List.mem_filter.mp hpm).2
  · intro s hsm
    rw [← hs] at hsm
    exact List.elem_iff.mp (List.mem_filter.mp hsm).2

/-- **The bridge holds of every valid `review` fixpoint.** At the fixpoint every node is its own
cut (`Fuel.review_cut_fixed`), and the cut keeps a link only when the node's own cut table admits
it — so the links were already inside the owners. -/
theorem linksInOwners_review (g : GPathM) (hv : isValid (review g) = true) :
    LinksInOwners (review g) := by
  intro pid d hd
  have hcut := (review_cut_fixed g hv pid d hd).2
  have hd_id : d.id = pid := node?_id_eq _ pid d hd
  have hself : ∀ x, admits (review g).gowners (review g) d.id x = true → x ∈ d.owners := by
    intro x hx
    unfold admits at hx
    rw [hd_id, hd] at hx
    exact (List.mem_filter.mp (List.mem_of_elem_eq_true hx)).1
  constructor
  · intro p hp
    have hp' : p ∈ (cutNode (review g).gowners (review g) d).parents := by rw [hcut]; exact hp
    simp only [cutNode, List.mem_filter, Bool.and_eq_true] at hp'
    exact hself p hp'.2.1
  · intro s hs
    have hs' : s ∈ (cutNode (review g).gowners (review g) d).sons := by rw [hcut]; exact hs
    simp only [cutNode, List.mem_filter, Bool.and_eq_true] at hs'
    exact hself s hs'.2.1

/-- And therefore of the graphs the obligation is about: `filterAll g reqs` is
a `review` result by construction. -/
theorem linksInOwners_filterAll (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) : LinksInOwners (filterAll g reqs) :=
  linksInOwners_review _ hv

/-- info: 'AbsSatBin.GraphPath.Model.Bridge.linksInOwners_review' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linksInOwners_review

end AbsSatBin.GraphPath.Model.Bridge
