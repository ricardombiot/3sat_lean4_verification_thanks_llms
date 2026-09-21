-- lean_project/AbsSat/GraphPath/Model/NoDeadEndVerdict.lean
import AbsSat.GraphPath.Model.NoDeadEnd
import AbsSat.GraphPath.Model.HereditaryBuild
import AbsSat.GraphPath.Model.Descent

/-!
# The verdict from one step: no dead ends in the final state

Every reduction of the *Improves* SAT verdict so far asks for something about **pins, joins or
pairs**: exact pins (v119), stable `Spc` (v122), a chain per owner pair (v123), branches that do
not borrow (v127), hereditary pin validity and joins that split (v128). This file reduces the
verdict to the most primitive statement of them all, about **one state and one step**:

* **`sat_of_noDeadEnd`** — if the reader's state has **no dead ends** (`NoDeadEnd`: every partial
  chain from the top step down extends by one pick), then reading it gives a model of `φ`.

Nothing else is needed: the **top anchor** of such a chain always exists (`NoDeadEnd.topAnchor_of`,
already proved — a valid state has a global owner at the top step, `GN` makes it a node, and
`OOS`, `Shape` and `RootAtZero` give its shape), so the descent needs only the one-step extension,
and a chain that reaches step 0 is exactly a `ChainSound` chain, which decodes to a model.

So the whole open problem is: *a partial chain of a valid state extends one step down.* That is
the author's own claim — every node lies on at least one path, and the review is what keeps it
true — with no quantifier over pins, pairs or joins.
-/

namespace AbsSat.GraphPath.Model.NoDeadEndVerdict

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.Hereditary
open AbsSat.GraphPath.Model.HereditaryBuild
open AbsSat.GraphPath.Model.SubsetSemantics (denotS)

variable (φ : Cnf)

/-- A subset path is a denotation: a `ChainSound` chain is in particular a chain with pairwise
ownership. -/
theorem denot_of_denotS {g : GPathM} {p : List NodeId} (h : denotS g p) : denot g p := by
  obtain ⟨sel, hcs, hp⟩ := h
  exact ⟨sel, hcs.chain.1, hcs.chain.2.1, hp⟩

/-- **The minimal form.** The verdict is sound as soon as the reader's state **denotes** a path:
one `ChainSound` chain is enough, and it decodes to a model. Everything else in the chain of
reductions is a way of producing that one chain. -/
theorem sat_of_denotS (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (h : ∃ p, denotS (filterAllAgg kv.2 []) p) : Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  obtain ⟨p, hpd⟩ := h
  exact ReaderAggRun.sat_of_denot_final φ hwf kv hkv p
    (denot_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup p (denot_of_denotS hpd))

/-- **The Improves verdict from one step.** If the reader's state has no dead ends, the path it
reads decodes to a model of `φ`. -/
theorem sat_of_noDeadEnd (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hnd : NoDeadEnd.NoDeadEnd (filterAllAgg kv.2 [])) : Satisfiable φ := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  -- the reader's state, with its facts
  obtain ⟨hR, _, hp, hn⟩ := Fw_facts kv.2 hm.rctx hm.smp hm.pms hm.sn []
  have hfw : Fw kv.2 [] = filterAllAgg kv.2 [] := by
    simp only [Fw, PureDriverImproves.filterWeakAll_nil]
  rw [hfw] at hR hp hn
  have a := AdjacentOwners.adj_of_readable _ hR hv hp hn
  have hpos : 0 < (filterAllAgg kv.2 []).current_step := by
    rw [(pruned_filterAllAgg kv.2 []).step_eq, hstep]
    exact ConservationCore.stepCount_pos φ
  -- the anchor at the top step is free, the descent is the hypothesis
  have ha := NoDeadEnd.topAnchor_of _ hv hpos a.rc.gn a.rc.oos a.rc.shape a.rc.rootz
    (fun q d hd => a.ctx.nodeval q d hd)
  obtain ⟨p, hpd⟩ := NoDeadEnd.nonempty_of_noDeadEnd _ hpos ha hnd
  exact ReaderAggRun.sat_of_denot_final φ hwf kv hkv p
    (denot_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup p (denot_of_denotS hpd))

/-- **The verdict from the one statement left.** If the picks of every partial chain of the
reader's state have an owner in common on the step below, reading gives a model of `φ`. Everything
else on the way is proved: the anchor at the top step, the descent step from a common owner, and
the decoding of a complete chain. -/
theorem sat_of_commonOwner (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hco : Descent.CommonOwner (filterAllAgg kv.2 [])) : Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  obtain ⟨hR, _, hp, hn⟩ := Fw_facts kv.2 hm.rctx hm.smp hm.pms hm.sn []
  have hfw : Fw kv.2 [] = filterAllAgg kv.2 [] := by
    simp only [Fw, PureDriverImproves.filterWeakAll_nil]
  rw [hfw] at hR hp hn
  have a := AdjacentOwners.adj_of_readable _ hR hv hp hn
  have hok := AggFixpoint.aggOk_reviewAgg _ hv
  exact sat_of_noDeadEnd φ hwf kv hkv hv
    (Descent.noDeadEnd_of_commonOwner _ a hok hco)

/-- **The verdict, with no hypothesis left, on the states whose nodes have one parent.** `SingleParents`
is the only thing assumed, and it is a property of the state the machine hands over, not a conjecture
about the review: it says the previous line holds no two nodes with the same two-step history. Where it
holds the descent is not a search — the past of every node is forced (`ParentWitness.owners_below_unique`)
— and the verdict follows. -/
theorem sat_of_singleParents (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hsp : ParentWitness.SingleParents (filterAllAgg kv.2 [])) : Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  obtain ⟨hR, _, hp, hn⟩ := Fw_facts kv.2 hm.rctx hm.smp hm.pms hm.sn []
  have hfw : Fw kv.2 [] = filterAllAgg kv.2 [] := by
    simp only [Fw, PureDriverImproves.filterWeakAll_nil]
  rw [hfw] at hR hp hn
  have a := AdjacentOwners.adj_of_readable _ hR hv hp hn
  have hok := AggFixpoint.aggOk_reviewAgg _ hv
  exact sat_of_commonOwner φ hwf kv hkv hv (Descent.commonOwner_of_singleParents _ a hok hsp)

/-- info: 'AbsSat.GraphPath.Model.NoDeadEndVerdict.sat_of_singleParents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_singleParents

/-- info: 'AbsSat.GraphPath.Model.NoDeadEndVerdict.sat_of_commonOwner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_commonOwner

/-- info: 'AbsSat.GraphPath.Model.NoDeadEndVerdict.sat_of_noDeadEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_noDeadEnd

/-- info: 'AbsSat.GraphPath.Model.NoDeadEndVerdict.sat_of_denotS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_denotS

end AbsSat.GraphPath.Model.NoDeadEndVerdict
