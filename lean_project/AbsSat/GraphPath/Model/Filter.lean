-- lean_project/AbsSat/GraphPath/Model/Filter.lean
import AbsSat.GraphPath.Model.Denot
import AbsSat.GraphPath.Model.Fuel
import AbsSat.GraphPath.Model.Pruned

/-!
Bridge lemma **L2** (`formal_bridge_owners_runpure.md` §5): the filter respects
the denotation.

    denot (filter g {req}) = { p ∈ denot g | p goes through req }

and `(filter g {req}).valid = true ↔ that set is non-empty`.

**A correction to the plan.** The bridge document splits L2 into
"`filter_require` (prunes the step's owners — direct) + `make_review_owners`
(the closure — needs L5/L6)". In `GPathM` the first summand contributes
*nothing*: `denot` is defined from `nodes` and `current_step` only, and
`filterRequire` rewrites `gowners` alone, so it is denotationally inert — and
inert *definitionally*, which is why `denot_filterRequire` below is `Iff.rfl`.
All of L2's content lives in `review`, which is where `cleanInvalid` first
carries the pinned global owners into the nodes' own owners lists.

**What is proved here** is L2's soundness direction, in the form that matters:
`chain_selects_req` — in a valid filtered graph, *every* co-owned chain selects
exactly `req` at `req`'s step. The route is the one the book describes: the
filter pins `req` in the global owners, `review` pushes the global owners into
every node's owners (F2.c, `review_owners_within_gowners`), and pairwise
ownership carries that from the nodes to the chain's own selection.

Also proved: the **narrowing direction**, `denot_review_subset` /
`denot_filterAll_subset` — every path the reviewed graph denotes was already
denoted before the review. Narrowing can only lose chains, never invent them.
`Pruned` now carries parent narrowing alongside id and owner narrowing, which
is what lets `IsChain` transfer backwards.

That transfer needs `NodupIds`, and the hypothesis is real rather than
bureaucratic: `node?` returns the *first* node with a given id, so if ids
repeat, pruning can delete the first one and leave `node?` pointing at a
different node whose parents and owners have no relation to the original's.
The pure model already assumes unique ids (`WellFormedGMap`), so this is the
same assumption, made explicit at the mirror level.

**What is not proved here** is the **⊇ direction** — no chain that goes
through `req` is lost by the filter. That is exactly lemma **L6** ("no
zombies"), the make-or-break of the whole bridge, and it is not attacked
here.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

-- ============================================================
-- `filterRequire` is denotationally inert (definitionally)
-- ============================================================

theorem IsChain_filterRequire (g : GPathM) (req : NodeId) (sel : Int → PathNodeId) :
    IsChain (filterRequire g req) sel ↔ IsChain g sel := Iff.rfl

theorem PairwiseOwned_filterRequire (g : GPathM) (req : NodeId) (sel : Int → PathNodeId) :
    PairwiseOwned (filterRequire g req) sel ↔ PairwiseOwned g sel := Iff.rfl

theorem pathOf_filterRequire (g : GPathM) (req : NodeId) (sel : Int → PathNodeId) :
    pathOf sel (filterRequire g req) = pathOf sel g := rfl

/-- Pruning the global owners alone changes no path of the denotation. -/
theorem denot_filterRequire (g : GPathM) (req : NodeId) (p : List NodeId) :
    denot (filterRequire g req) p ↔ denot g p := Iff.rfl

-- ============================================================
-- intRange membership
-- ============================================================

theorem mem_intRange {lo hi k : Int} (h1 : lo ≤ k) (h2 : k ≤ hi) : k ∈ intRange lo hi := by
  simp only [intRange, List.mem_map, List.mem_range]
  refine ⟨(k - lo).toNat, by omega, ?_⟩
  have htn : ((k - lo).toNat : Int) = k - lo := Int.toNat_of_nonneg (by omega)
  simp only [Int.ofNat_eq_natCast, htn]
  omega

-- ============================================================
-- isValid gives a global owner at every in-range step
-- ============================================================

theorem hasStepEntry_of_isValid (g : GPathM) (h : isValid g = true)
    (k : Int) (hlo : 0 ≤ k) (hhi : k < g.current_step) :
    hasStepEntry g.gowners k = true := by
  simp only [isValid, List.all_eq_true] at h
  exact h k (mem_intRange hlo (by omega))

-- ============================================================
-- owners ⊆ gowners, upgraded from the intersectOwners form
-- ============================================================

theorem owners_mem_gowners (g : GPathM) (d : PNodeM)
    (hfix : intersectOwners d.owners g.gowners = d.owners)
    (q : PathNodeId) (hq : q ∈ d.owners)
    (hstep : hasStepEntry g.gowners q.id.step = true) :
    q ∈ g.gowners := by
  have hall := List.filter_eq_self.mp hfix q hq
  simp only [hstep, Bool.not_true, Bool.false_or] at hall
  exact List.mem_of_elem_eq_true hall

-- ============================================================
-- The required node is pinned in the global owners
-- ============================================================

theorem filterRequire_gowners_pinned (g : GPathM) (req : NodeId) (q : PathNodeId)
    (hq : q ∈ (filterRequire g req).gowners) (hstep : q.id.step = req.step) : q.id = req := by
  simp only [filterRequire] at hq
  have hpred := (List.mem_filter.mp hq).2
  rw [hstep] at hpred
  simpa using hpred

-- ============================================================
-- L2, soundness half: every chain of the filtered graph goes
-- through the required node
-- ============================================================

/-- If the global owners pin `req` as the only visitable map node of its step,
then after `review` every co-owned chain selects exactly `req` there.

The `j` is any other in-range step: pairwise ownership is what carries the
global constraint (the pinned global owners) into a statement about the
chain's own selection. -/
theorem chain_selects_pinned (h : GPathM) (req : NodeId)
    (hpin : ∀ q ∈ h.gowners, q.id.step = req.step → q.id = req)
    (hvalid : isValid (review h) = true)
    (sel : Int → PathNodeId)
    (hchain : IsChain (review h) sel)
    (howned : PairwiseOwned (review h) sel)
    (hlo : 0 ≤ req.step) (hhi : req.step < (review h).current_step)
    (j : Int) (hj_lo : 0 ≤ j) (hj_hi : j < (review h).current_step)
    (hne : req.step ≠ j) :
    (sel req.step).id = req := by
  -- pairwise ownership: the node chosen at step j owns the one chosen at req.step
  have hmem := howned req.step j hlo hj_lo hhi hj_hi hne
  simp only [ownersAt, List.mem_filter] at hmem
  obtain ⟨hown, hstep_eq⟩ := hmem
  have hstep : (sel req.step).id.step = req.step := by simpa using hstep_eq
  -- that node is still in the graph, so `ownersOf` is its owners list
  obtain ⟨hsome, _⟩ := hchain.1 j hj_lo hj_hi
  obtain ⟨d, hd⟩ : ∃ d, (review h).node? (sel j) = some d := Option.isSome_iff_exists.mp hsome
  rw [ownersOf, hd] at hown
  -- after review those owners are inside the global owners
  have hfix := review_owners_within_gowners h hvalid (sel j) d hd
  have hentry : hasStepEntry (review h).gowners (sel req.step).id.step = true := by
    rw [hstep]; exact hasStepEntry_of_isValid _ hvalid _ hlo hhi
  have hg : sel req.step ∈ (review h).gowners :=
    owners_mem_gowners (review h) d hfix _ hown hentry
  exact hpin _ ((pruned_review h).gowners_sub _ hg) hstep

/-- The same, for the filter as the machine actually calls it. -/
theorem chain_selects_req (g : GPathM) (req : NodeId)
    (hvalid : isValid (filterAll g [req]) = true)
    (sel : Int → PathNodeId)
    (hchain : IsChain (filterAll g [req]) sel)
    (howned : PairwiseOwned (filterAll g [req]) sel)
    (hlo : 0 ≤ req.step) (hhi : req.step < (filterAll g [req]).current_step)
    (j : Int) (hj_lo : 0 ≤ j) (hj_hi : j < (filterAll g [req]).current_step)
    (hne : req.step ≠ j) :
    (sel req.step).id = req :=
  chain_selects_pinned (filterRequire g req) req
    (filterRequire_gowners_pinned g req) hvalid sel hchain howned hlo hhi j hj_lo hj_hi hne

/-- Node ids are unique. `node?` returns the *first* match, so without this a
node can be shadowed and `node?` will not find it. -/
def NodupIds (g : GPathM) : Prop := (g.nodes.map (·.id)).Nodup

private theorem find?_id_of_mem (l : List PNodeM) (hnd : (l.map (·.id)).Nodup)
    (n : PNodeM) (hn : n ∈ l) : l.find? (fun m => m.id == n.id) = some n := by
  induction l with
  | nil => exact absurd hn List.not_mem_nil
  | cons a as ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hnd'⟩ := hnd
    rcases List.mem_cons.mp hn with rfl | hn'
    · simp
    · have hne : (a.id == n.id) = false := by
        cases hb : (a.id == n.id) with
        | false => rfl
        | true =>
          have heq : a.id = n.id := eq_of_beq hb
          have hmem : a.id ∈ as.map (fun m : PNodeM => m.id) := by
            rw [heq]; exact List.mem_map_of_mem hn'
          exact absurd hmem hnotin
      have hskip : List.find? (fun m => m.id == n.id) (a :: as)
          = List.find? (fun m => m.id == n.id) as := by
        simp [hne]
      rw [hskip]
      exact ih hnd' hn'

theorem node?_of_mem {g : GPathM} (hnd : NodupIds g) (n : PNodeM) (hn : n ∈ g.nodes) :
    g.node? n.id = some n :=
  find?_id_of_mem g.nodes hnd n hn

-- ============================================================
-- Transferring the denotation back across a narrowing
-- ============================================================

theorem IsChain_of_pruned {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (sel : Int → PathNodeId) (h : IsChain g' sel) : IsChain g sel := by
  have hnode : ∀ pid n', g'.node? pid = some n' →
      ∃ n, g.node? pid = some n ∧ (∀ q ∈ n'.owners, q ∈ n.owners)
        ∧ (∀ q ∈ n'.parents, q ∈ n.parents) := by
    intro pid n' hn'
    have hn'_mem : n' ∈ g'.nodes := List.mem_of_find?_eq_some hn'
    have hn'_id : n'.id = pid := node?_id_eq g' pid n' hn'
    obtain ⟨n, hn, hid, hown, hpar⟩ := hpr.nodes_derived n' hn'_mem
    have hnid : n.id = pid := by rw [← hid]; exact hn'_id
    exact ⟨n, by rw [← hnid]; exact node?_of_mem hnd n hn, hown, hpar⟩
  constructor
  · intro k hlo hhi
    obtain ⟨hsome, hstep⟩ := h.1 k hlo (by rw [hpr.step_eq]; exact hhi)
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨n, hn, _, _⟩ := hnode _ _ hn'
    exact ⟨by rw [hn]; rfl, hstep⟩
  · intro k hlo hhi
    have hlink := h.2 k hlo (by rw [hpr.step_eq]; exact hhi)
    cases hn' : g'.node? (sel (k + 1)) with
    | none => rw [hn'] at hlink; exact absurd hlink List.not_mem_nil
    | some n' =>
      obtain ⟨n, hn, _, hpar⟩ := hnode _ _ hn'
      rw [hn' ] at hlink
      rw [hn]
      exact hpar _ hlink

theorem PairwiseOwned_of_pruned {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (sel : Int → PathNodeId) (h : PairwiseOwned g' sel) : PairwiseOwned g sel := by
  intro i j hi hj hi' hj' hne
  have hmem := h i j hi hj (by rw [hpr.step_eq]; exact hi') (by rw [hpr.step_eq]; exact hj') hne
  simp only [ownersAt, List.mem_filter] at hmem ⊢
  obtain ⟨hown, hstep⟩ := hmem
  refine ⟨?_, hstep⟩
  simp only [ownersOf] at hown ⊢
  cases hn' : g'.node? (sel j) with
  | none => rw [hn'] at hown; exact absurd hown List.not_mem_nil
  | some n' =>
    rw [hn'] at hown
    have hn'_mem : n' ∈ g'.nodes := List.mem_of_find?_eq_some hn'
    have hn'_id : n'.id = sel j := node?_id_eq g' (sel j) n' hn'
    obtain ⟨n, hn, hid, hsub, _⟩ := hpr.nodes_derived n' hn'_mem
    have hnid : n.id = sel j := by rw [← hid]; exact hn'_id
    rw [show g.node? (sel j) = some n by rw [← hnid]; exact node?_of_mem hnd n hn]
    exact hsub _ hown

/-- **L2, the narrowing direction**: every path the reviewed graph denotes was
already denoted before the review. Narrowing can only lose chains, never
invent them. -/
theorem denot_of_pruned {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (p : List NodeId) (h : denot g' p) : denot g p := by
  obtain ⟨sel, hchain, howned, hpath⟩ := h
  refine ⟨sel, IsChain_of_pruned hpr hnd sel hchain,
    PairwiseOwned_of_pruned hpr hnd sel howned, ?_⟩
  rw [hpath]
  simp only [pathOf, hpr.step_eq]

theorem denot_review_subset (g : GPathM) (hnd : NodupIds g) (p : List NodeId)
    (h : denot (review g) p) : denot g p :=
  denot_of_pruned (pruned_review g) hnd p h

theorem denot_filterAll_subset (g : GPathM) (hnd : NodupIds g) (reqs : List NodeId)
    (p : List NodeId) (h : denot (filterAll g reqs) p) : denot g p :=
  denot_of_pruned (pruned_filterAll g reqs) hnd p h

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.chain_selects_req' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_selects_req

/-- info: 'AbsSat.GraphPath.Model.denot_filterRequire' does not depend on any axioms -/
#guard_msgs in
#print axioms denot_filterRequire

/-- info: 'AbsSat.GraphPath.Model.denot_review_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denot_review_subset

/-- info: 'AbsSat.GraphPath.Model.denot_filterAll_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denot_filterAll_subset

end AbsSat.GraphPath.Model
