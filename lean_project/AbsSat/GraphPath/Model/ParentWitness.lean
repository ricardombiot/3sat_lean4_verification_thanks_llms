-- lean_project/AbsSat/GraphPath/Model/ParentWitness.lean
import AbsSat.GraphPath.Model.AdjacentOwners
import AbsSat.GraphPath.Model.LocalContradiction

/-!
# The parent witness, by design of the identifier

A `PathNodeId` is a map node plus **the map node of its parent**, so an identifier already
carries one step of its parent chain, and `ParentId.PMP` turns that into a state invariant:

* `parents_id_eq` — **every parent of a node carries the map node its own identifier names.** All
  parents of a node agree on their map node; two of them can differ only in *their* parent, one
  step further down.

That is what the pair-to-triple step of v122/v129 was missing. The `par` condition of a support
relation (`AnchoredSurvive.Sup`) asks for one parent of `x` linked to `x` and to a second member
`v`; restricting the relation to a slice needs that parent linked to the slice's anchor `z` too —
a witness for a *triple*, which pair consistency does not give. But by `parents_id_eq` the two
witnesses pair consistency does give, one for `v` and one for `z`, carry the **same map node**:

* `par_witness_triple` — so when the node has a single parent they are the same node, and pair
  consistency yields the triple.

The gap is therefore not "which map node": the identifier fixes it. It is one level deeper, at a
node whose parents come from several *grandparent* histories — exactly where two branches merged.
-/

namespace AbsSat.GraphPath.Model.ParentWitness

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview (sharesEveryStep)
open AbsSat.GraphPath.Model.AggFixpoint (AggOk)
open AbsSat.GraphPath.Model.AdjacentOwners (Adj owners_below_iff_parents mem_union_of_coherent)

/-- **Every parent of a node carries the map node the node's own identifier names.** -/
theorem parents_id_eq {g : GPathM} (hpmp : ParentId.PMP g) {n : PNodeM} (hn : n ∈ g.nodes)
    {c c' : PathNodeId} (hc : c ∈ n.parents) (hc' : c' ∈ n.parents) : c.id = c'.id :=
  Option.some_inj.mp ((hpmp n hn c hc).trans (hpmp n hn c' hc').symm)

/-- **Two parents differ only below.** They name the same map node, so they part company at
*their* parent — one more step down the chain the identifiers build. -/
theorem parents_differ_below {g : GPathM} (hpmp : ParentId.PMP g) {n : PNodeM} (hn : n ∈ g.nodes)
    {c c' : PathNodeId} (hc : c ∈ n.parents) (hc' : c' ∈ n.parents) (hne : c ≠ c') :
    c.id = c'.id ∧ c.parent_id ≠ c'.parent_id := by
  refine ⟨parents_id_eq hpmp hn hc hc', fun hp => hne ?_⟩
  have hid := parents_id_eq hpmp hn hc hc'
  cases c; cases c'; simp only [PathNodeId.mk.injEq] at *
  exact ⟨hid, hp⟩

/-- A node with one parent: by `parents_id_eq` this is the same as having one parent *history*,
since the map node is fixed by the identifier either way. -/
def SingleParent (n : PNodeM) : Prop := ∀ c ∈ n.parents, ∀ c' ∈ n.parents, c = c'

/-- The owner pair consistency of the sweep, at one step: a common owner of `x` and `v`. -/
private theorem shared_owner {g : GPathM} (a : Adj g) (hok : AggOk g)
    {x v : PathNodeId} {n nv : PNodeM} (hx : g.node? x = some n) (hv : g.node? v = some nv)
    (hx0 : 0 ≤ x.id.step) (hxs : x.id.step < g.current_step)
    (hv0 : 0 ≤ v.id.step) (hvs : v.id.step < g.current_step) (hvx : v ∈ n.owners)
    (k : Int) (hk0 : 0 ≤ k) (hks : k < g.current_step) :
    ∃ c, c ∈ n.owners ∧ c ∈ nv.owners ∧ c.id.step = k := by
  obtain ⟨_, hsh⟩ := hok x n v nv hx hv hx0 hxs hv0 hvs hvx
    (a.ctx.nodeval x n hx) (a.ctx.nodeval v nv hv)
  have hall : (intRange 0 (g.current_step - 1)).all
      (fun j => !hasStepEntry nv.owners j || (ownersAt n.owners j).any
        (fun r => nv.owners.contains r)) = true := by
    simpa only [sharesEveryStep] using hsh
  have hcl := List.all_eq_true.mp hall k (mem_intRange hk0 (by omega))
  have hent : hasStepEntry nv.owners k = true :=
    LocalContradiction.ownersOk_of_isValidNode g nv (a.ctx.nodeval v nv hv) k hk0 hks
  simp only [hent, Bool.not_true, Bool.false_or] at hcl
  obtain ⟨c, hc, hcv⟩ := List.any_eq_true.mp hcl
  exact ⟨c, (List.mem_filter.mp hc).1, List.mem_of_elem_eq_true hcv,
    eq_of_beq (List.mem_filter.mp hc).2⟩

/-- **Pair consistency gives the triple, when the node has a single parent.** The witness for `v`
and the witness for `z` are both parents of `x`, so they name the same map node
(`parents_id_eq`); with one parent they are the same node, and it is linked to all three. -/
theorem par_witness_triple (g : GPathM) (a : Adj g) (hok : AggOk g)
    {x v z : PathNodeId} {n nv nz : PNodeM} (hsp : SingleParent n)
    (hx : g.node? x = some n) (hv : g.node? v = some nv) (hz : g.node? z = some nz)
    (hx1 : 1 ≤ x.id.step) (hxs : x.id.step < g.current_step)
    (hv0 : 0 ≤ v.id.step) (hvs : v.id.step < g.current_step)
    (hz0 : 0 ≤ z.id.step) (hzs : z.id.step < g.current_step)
    (hvx : v ∈ n.owners) (hzx : z ∈ n.owners) :
    ∃ c ∈ n.parents, c ∈ n.owners ∧ c ∈ nv.owners ∧ c ∈ nz.owners := by
  have hk0 : (0:Int) ≤ x.id.step - 1 := by omega
  obtain ⟨c, hcn, hcv, hcs⟩ :=
    shared_owner a hok hx hv (by omega) hxs hv0 hvs hvx (x.id.step - 1) hk0 (by omega)
  obtain ⟨c', hc'n, hc'z, hc's⟩ :=
    shared_owner a hok hx hz (by omega) hxs hz0 hzs hzx (x.id.step - 1) hk0 (by omega)
  have hcp : c ∈ n.parents :=
    (owners_below_iff_parents g a x n hx hx1 c (by omega)).mp hcn
  have hc'p : c' ∈ n.parents :=
    (owners_below_iff_parents g a x n hx hx1 c' (by omega)).mp hc'n
  have heq : c' = c := hsp c' hc'p c hcp
  exact ⟨c, hcp, hcn, hcv, by rw [← heq]; exact hc'z⟩


-- ============================================================
-- With one parent, the past of a node is a unique path
-- ============================================================

/-- Every node of the state has a single parent. -/
def SingleParents (g : GPathM) : Prop := ∀ n ∈ g.nodes, SingleParent n

/-- The union of a node's parents' tables has an entry on every step below the node. -/
private theorem union_entry_below {g : GPathM} (a : Adj g) {x : PathNodeId} {n : PNodeM}
    (hx : g.node? x = some n) (hx1 : 1 ≤ x.id.step) (k : Int) (hk0 : 0 ≤ k)
    (hk1 : k < g.current_step) :
    hasStepEntry (unionOwnersOf g n.parents) k = true := by
  have hmem := List.mem_of_find?_eq_some hx
  have hid := node?_id_eq g x n hx
  have hroot : n.id.parent_id.isNone = false := by
    have hnr := a.rc.shape.notroot n hmem (by rw [hid]; omega)
    cases hp : n.id.parent_id with
    | none => exact absurd hp hnr
    | some _ => rfl
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _
    (SymTriReview.have_parents_of_isValidNode g n (a.ctx.nodeval x n hx) hroot)
  obtain ⟨mc, hmc, hmcid⟩ := a.rc.shape.pn n hmem c hc
  have hcnode : g.node? c = some mc := by rw [← hmcid]; exact node?_of_mem a.rc.nodup mc hmc
  have hent : hasStepEntry mc.owners k = true :=
    LocalContradiction.ownersOk_of_isValidNode g mc (a.ctx.nodeval c mc hcnode) k hk0 hk1
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hent
  exact List.any_eq_true.mpr
    ⟨q, mem_unionOwnersOf g n.parents c mc q hc hcnode hq, hqs⟩

/-- **With one parent per node, the past of a node is a unique path.** A node has at most one
owner on each step below it: on the step just below they are its parents, which are equal, and
deeper down they both come from that same parent, by the coherence of the review.

This is the design chain of the identifiers, as a theorem: where the merging of branches does not
intervene, the history of a node is forced, so the chain that `PairChain` asks for below a node is
not a choice at all. -/
theorem owners_below_unique (g : GPathM) (a : Adj g) (hsp : SingleParents g) :
    ∀ (m : Nat) (x : PathNodeId) (n : PNodeM), g.node? x = some n →
      ∀ k, 0 ≤ k → x.id.step - k = (m : Int) + 1 →
      ∀ w ∈ n.owners, ∀ w' ∈ n.owners, w.id.step = k → w'.id.step = k → w = w' := by
  intro m
  induction m with
  | zero =>
    intro x n hx k hk0 hgap w hw w' hw' hws hw's
    have hx1 : 1 ≤ x.id.step := by omega
    have hwp := (owners_below_iff_parents g a x n hx hx1 w (by omega)).mp hw
    have hw'p := (owners_below_iff_parents g a x n hx hx1 w' (by omega)).mp hw'
    exact hsp n (List.mem_of_find?_eq_some hx) w hwp w' hw'p
  | succ j ih =>
    intro x n hx k hk0 hgap w hw w' hw' hws hw's
    have hmem := List.mem_of_find?_eq_some hx
    have hid := node?_id_eq g x n hx
    have hx1 : 1 ≤ x.id.step := by omega
    have hbelow := a.rc.below n hmem
    rw [hid] at hbelow
    have hk1 : k < g.current_step := by omega
    have hkstep : x.id.step ∈ intRange 1 (g.current_step - 1) := mem_intRange hx1 (by omega)
    have hcoh := a.cohP _ hkstep x (Threaded.mem_line_of_node? g x n hx) n hx
    have hent := union_entry_below a hx hx1 k hk0 hk1
    obtain ⟨c, hc, mc, hmc, hwc⟩ :=
      mem_union_of_coherent g n.parents n.owners w hcoh hw (by rw [hws]; exact hent)
    obtain ⟨c', hc', mc', hmc', hw'c⟩ :=
      mem_union_of_coherent g n.parents n.owners w' hcoh hw' (by rw [hw's]; exact hent)
    have hcc : c' = c := hsp n hmem c' hc' c hc
    have hmceq : mc' = mc := by
      rw [hcc] at hmc'
      exact Option.some_inj.mp (hmc'.symm.trans hmc)
    have hcstep : c.id.step = x.id.step - 1 := by rw [← hid]; exact a.rc.shape.pbelow n hmem c hc
    exact ih c mc hmc k hk0 (by omega) w hwc w' (by rw [← hmceq]; exact hw'c) hws hw's

/-- info: 'AbsSat.GraphPath.Model.ParentWitness.par_witness_triple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms par_witness_triple

/-- info: 'AbsSat.GraphPath.Model.ParentWitness.owners_below_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owners_below_unique

end AbsSat.GraphPath.Model.ParentWitness
