-- lean_project/AbsSat/GraphPath/Model/LocalContradiction.lean
import AbsSat.GraphPath.Model.Filter
import AbsSat.GraphPath.Model.MapReachable

/-!
# A contradiction inside one clause kills the state

v93 measured, on case 17 of seed 90210, that pinning two values no solution
combines leaves the pin itself harmless, but the review then empties the clause
steps and the state is invalid. This module proves the reach-one version of that
mechanism.

* `invalid_filterAll_of_blocked` — generic: if every node at some step requires an
  id that no global owner keeps after the pins, `filterAll` leaves the state
  invalid. The argument: a surviving global owner at that step is a node (`GN`);
  the review leaves it a valid node, so it owns something at its blocked
  requirement's step; by `L1` that owner *is* the requirement; and after the review
  owners are global owners — which the pins ruled out.
* `invalid_filterAll_of_clause_blocked` — on a 3SAT map: if, after the pins, none of
  a seen clause's three literals can be *true* (`litReq l 1`), `filterAll` leaves
  the state invalid. Every row of the clause names some literal as true
  (`bits_not_all_zero`), so every row is blocked.
* `excluded_of_pin`, `excluded_of_excluded` — the two ways a value ends up ruled
  out: a pin fixes the other value at that step, or the state had already lost it.

Reach one only: the contradiction has to sit inside a single clause. This is local
consistency, not `ClauseStepExact`.
-/

namespace AbsSat.GraphPath.Model.LocalContradiction

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable

/-- No global owner of `g` carries the map node `r`. -/
def Excluded (g : GPathM) (r : NodeId) : Prop := ∀ q ∈ g.gowners, q.id ≠ r

theorem mem_foldl_filterRequire (reqs : List NodeId) : ∀ (g : GPathM) (q : PathNodeId),
    q ∈ (reqs.foldl filterRequire g).gowners →
      q ∈ g.gowners ∧ ∀ req ∈ reqs, q.id.step ≠ req.step ∨ q.id = req := by
  induction reqs with
  | nil => intro g q hq; exact ⟨hq, fun _ h => absurd h List.not_mem_nil⟩
  | cons r rs ih =>
    intro g q hq
    obtain ⟨hq1, hrs⟩ := ih (filterRequire g r) q hq
    simp only [filterRequire, List.mem_filter, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at hq1
    refine ⟨hq1.1, fun req hreq => ?_⟩
    rcases List.mem_cons.mp hreq with rfl | hreq
    · exact hq1.2
    · exact hrs req hreq

/-- A pin at `r`'s step on a different map node rules `r` out. -/
theorem excluded_of_pin (g : GPathM) (reqs : List NodeId) (req r : NodeId)
    (hreq : req ∈ reqs) (hstep : req.step = r.step) (hne : req ≠ r) :
    Excluded (reqs.foldl filterRequire g) r := by
  intro q hq hqr
  rcases (mem_foldl_filterRequire reqs g q hq).2 req hreq with h | h
  · exact h (by rw [hqr, hstep])
  · exact hne (h.symm.trans hqr)

/-- Pins only shrink the global owners, so what the state had already lost stays
lost. -/
theorem excluded_of_excluded (g : GPathM) (reqs : List NodeId) (r : NodeId)
    (h : Excluded g r) : Excluded (reqs.foldl filterRequire g) r :=
  fun q hq => h q (mem_foldl_filterRequire reqs g q hq).1

theorem ownersOk_of_isValidNode (g : GPathM) (n : PNodeM) (h : isValidNode g n = true)
    (k : Int) (h0 : 0 ≤ k) (hk : k < g.current_step) :
    hasStepEntry n.owners k = true := by
  have hall : (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry n.owners k) = true := by
    simp only [isValidNode] at h
    cases h1 : n.id.parent_id.isNone <;> cases h2 : (n.id.id.step == g.current_step - 1) <;>
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h <;>
      first | exact h | exact h.1 | exact h.1.1
  simp only [List.all_eq_true] at hall
  exact hall k (mem_intRange h0 (by omega))

/-- **Blocked requirements kill the state.** If every node of `g` at step `k`
requires some map node that no global owner keeps once the pins are applied, the
filtered state is invalid. -/
theorem invalid_filterAll_of_blocked (reqOf : NodeId → List NodeId) (g : GPathM)
    (hreach : Reachable reqOf g) (reqs : List NodeId) (k : Int)
    (hk0 : 0 ≤ k) (hk : k < g.current_step)
    (hblock : ∀ d ∈ g.nodes, d.id.id.step = k →
      ∃ r ∈ reqOf d.id.id, 0 ≤ r.step ∧ r.step < g.current_step ∧
        Excluded (reqs.foldl filterRequire g) r) :
    isValid (filterAll g reqs) = false := by
  cases hv : isValid (filterAll g reqs) with
  | false => rfl
  | true =>
    exfalso
    have hpr := pruned_filterAll g reqs
    have hstep : (filterAll g reqs).current_step = g.current_step := hpr.step_eq
    -- A global owner survives at step `k`, and it is a node.
    have hent := hasStepEntry_of_isValid _ hv k hk0 (by rw [hstep]; exact hk)
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
    obtain ⟨o, ho, hos⟩ := hent
    obtain ⟨n, hn, hnid⟩ :=
      GownersNodes.GN_filterAll g reqs (GownersNodes.GN_reachable reqOf g hreach) o ho
    have hsome : ((filterAll g reqs).node? o).isSome := by
      simp only [node?, List.find?_isSome]
      exact ⟨n, hn, by simp [hnid]⟩
    obtain ⟨d, hdnode⟩ := Option.isSome_iff_exists.mp hsome
    have hdmem : d ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hdnode
    have hdid : d.id = o := node?_id_eq _ o d hdnode
    -- Back in `g`, the same node is blocked.
    obtain ⟨d0, hd0, hid0, _, _⟩ := hpr.nodes_derived d hdmem
    obtain ⟨r, hr, hr0, hrk, hexcl⟩ :=
      hblock d0 hd0 (by rw [← hid0, hdid]; exact hos)
    -- The review leaves `d` valid, so it owns something at `r`'s step ...
    have hvalid : isValidNode (filterAll g reqs) d = true :=
      review_node_valid (reqs.foldl filterRequire g) hv o d hdnode
    have hown := ownersOk_of_isValidNode _ d hvalid r.step hr0 (by rw [hstep]; exact hrk)
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hown
    obtain ⟨q, hq, hqs⟩ := hown
    -- ... which by `L1` is `r` itself ...
    have hrf := filterAll_preserves_ReqFiltered reqOf (L1 reqOf hreach) reqs
    have hqr : q.id = r := hrf d hdmem r (by rw [hid0]; exact hr) q hq hqs
    -- ... and is a global owner, which the pins ruled out.
    have hfix := review_owners_within_gowners (reqs.foldl filterRequire g) hv o d hdnode
    have hqg : q ∈ (filterAll g reqs).gowners :=
      owners_mem_gowners _ d hfix q hq
        (hasStepEntry_of_isValid _ hv _ (by rw [hqs]; exact hr0)
          (by rw [hqs, hstep]; exact hrk))
    exact hexcl q ((pruned_review (reqs.foldl filterRequire g)).gowners_sub q hqg) hqr

theorem lit_step_nonneg (l : Lit) : 0 ≤ l.step := by
  cases hp : l.pos
  · rw [negStep_eq l hp]; simp only [negStep]; omega
  · rw [varStep_eq l hp]; simp only [varStep]; omega

/-- **A clause ruled false kills the state.** On a 3SAT map, if after the pins no
global owner lets any of a seen clause's three literals be true, the filtered state
is invalid: every row of the clause names some literal as true, so every row is
blocked. -/
theorem invalid_filterAll_of_clause_blocked (φ : Cnf) (hwf : WF φ) (g : GPathM)
    (hmr : MapReachable φ g) (reqs : List NodeId) (j : Nat) (c : Clause)
    (hjlt : j < φ.clauses.length) (hj : φ.clauses[j]? = some c)
    (hk : clauseStep φ j < g.current_step)
    (h1 : Excluded (reqs.foldl filterRequire g) (litReq c.l1 1))
    (h2 : Excluded (reqs.foldl filterRequire g) (litReq c.l2 1))
    (h3 : Excluded (reqs.foldl filterRequire g) (litReq c.l3 1)) :
    isValid (filterAll g reqs) = false := by
  have hc : c ∈ φ.clauses := List.mem_iff_getElem?.mpr ⟨j, hj⟩
  have hcwf := hwf c hc
  have hlit : ∀ l : Lit, l.v < φ.nVars → 0 ≤ l.step ∧ l.step < g.current_step := by
    intro l hv
    have hlt := lit_step_lt φ l hv
    have hk' := hk
    simp only [litBlock] at hlt
    simp only [clauseStep] at hk'
    exact ⟨lit_step_nonneg l, by omega⟩
  apply invalid_filterAll_of_blocked (reqOfCnf φ) g (reachable_of_mapReachable φ hwf g hmr) reqs
    (clauseStep φ j) (by simp only [clauseStep]; omega) hk
  intro d hd hdk
  have hon := nodesOnMap_of_mapReachable φ g hmr d hd
  rw [hdk] at hon
  obtain ⟨hlo, hhi⟩ := index_range_of_clauseNode φ j hjlt d.id.id hon
  have hreq := reqOfCnf_clause φ d.id.id j c hjlt hj hdk
  rcases bits_not_all_zero d.id.id.index hlo hhi with hb | hb | hb
  · exact ⟨litReq c.l1 1, by rw [hreq, hb]; simp, (hlit c.l1 hcwf.1.1).1,
      (hlit c.l1 hcwf.1.1).2, h1⟩
  · exact ⟨litReq c.l2 1, by rw [hreq, hb]; simp, (hlit c.l2 hcwf.1.2.1).1,
      (hlit c.l2 hcwf.1.2.1).2, h2⟩
  · exact ⟨litReq c.l3 1, by rw [hreq, hb]; simp, (hlit c.l3 hcwf.1.2.2).1,
      (hlit c.l3 hcwf.1.2.2).2, h3⟩

/-- info: 'AbsSat.GraphPath.Model.LocalContradiction.invalid_filterAll_of_blocked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms invalid_filterAll_of_blocked

/-- info: 'AbsSat.GraphPath.Model.LocalContradiction.invalid_filterAll_of_clause_blocked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms invalid_filterAll_of_clause_blocked

/-- info: 'AbsSat.GraphPath.Model.LocalContradiction.excluded_of_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms excluded_of_pin

/-- info: 'AbsSat.GraphPath.Model.LocalContradiction.excluded_of_excluded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms excluded_of_excluded

end AbsSat.GraphPath.Model.LocalContradiction
