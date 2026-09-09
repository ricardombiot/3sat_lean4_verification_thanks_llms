-- lean_project/AbsSat/GraphPath/Model/Bridge.lean
import AbsSat.GraphPath.Model.ParentId

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

The route is short because the migration did the work: at the fixpoint each
`cleanStep` is the identity (`Fuel.review_cleanStep_fixed`), hence so is the
unlink inside it (`Fuel.intersectOrDrop_valid_branch`), hence a node's links
were already inside its owners (`Fuel.relinkSelf_eq_self_of_fixed`).
-/

namespace AbsSat.GraphPath.Model.Bridge

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

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

/-- **The bridge holds of every valid `review` fixpoint.** At the fixpoint the
clean step is the identity, so the unlink inside it found nothing to do — which
means the links were already inside the owners. -/
theorem linksInOwners_review (g : GPathM) (hv : isValid (review g) = true) :
    LinksInOwners (review g) := by
  intro pid d hd
  refine links_of_relinkSelf_eq d (relinkSelf_eq_self_of_fixed (review g) pid d hd ?_)
  have hstep := review_cleanStep_fixed g hv pid d hd
  have hd_mem : d ∈ (review g).nodes := List.mem_of_find?_eq_some hd
  have hd_id : d.id = pid := node?_id_eq _ pid d hd
  have hstep' : measure (intersectOrDrop (review g) pid (review g).gowners d)
      = measure (review g) := by
    have hc : cleanStep (review g) pid
        = intersectOrDrop (review g) pid (review g).gowners d := by
      simp only [cleanStep, hd]
    rw [← hc, hstep]
  exact (intersectOrDrop_valid_branch (review g) pid (review g).gowners d
    hd_mem hd_id hstep').2.1

/-- And therefore of the graphs the obligation is about: `filterAll g reqs` is
a `review` result by construction. -/
theorem linksInOwners_filterAll (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) : LinksInOwners (filterAll g reqs) :=
  linksInOwners_review _ hv

/-- info: 'AbsSat.GraphPath.Model.Bridge.linksInOwners_review' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linksInOwners_review

end AbsSat.GraphPath.Model.Bridge
