-- lean_project/AbsSat/GraphPath/Model/UnitPropagation.lean
import AbsSat.GraphPath.Model.LocalContradiction
import AbsSat.GraphPath.Model.SelfOwn

/-!
# The review contains unit propagation

Measured first (v93 follow-up, 15,022 random pin sets and 404 constructed chains of
up to four propagation rounds on `SatMachinePure`): whenever unit propagation from
the pinned values reaches a conflict, `filterAll` leaves the state invalid. This
module proves it, by showing that the review's valid fixpoint is closed under
propagation — so the agreement is mechanical, not luck.

## The invariant the proof needs: `OwnedCompatible`, the dual of `L1`

`L1` says a node's owners at its requirements' steps are exactly its requirements.
The dual looks the other way: **a node never owns a later node whose requirement at
the node's own step is a different node.**

It holds for every reachable state because of the order inside `upFiltering`: the
destination's requirements are pinned and the review runs *before* `addNode` makes
the new node an owner of everyone, and `up` only adds the node if that filtered
state is valid. In a valid filtered state every node at a pinned step carries the
pinned id (`pinned_step_pure`, from `OOS` and the pin), so nobody incompatible is
left to receive the new owner.

## The four fixpoint facts

For `G = filterAll g reqs` valid, `g` reachable on a well-formed 3SAT map:

* `clause_supported` — every seen clause keeps some literal able to be true;
* `forcing1/2/3` — if two literals of a seen clause cannot be true, the third
  literal's false value loses its global owner (this is where the dual is used);
* `link_forward`/`link_backward` — `(2v, b)` survives iff `(2v+1, 1-b)` survives;
* `var_has_value` — every variable keeps a value.

## Unit propagation

`Refuted` is unit propagation as an inductive relation: a value is refuted if the
pinned state already lacks it, or if a seen clause has its other two literals
refuted true. `UPConflict` is a variable with both values refuted or a clause with
all three literals refuted true. `invalid_filterAll_of_UPConflict`: a conflict
leaves the filtered state invalid.

This is unit propagation, which does not decide SAT by itself; it does not touch
`ClauseStepExact`.
-/

namespace AbsSat.GraphPath.Model.UnitPropagation

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.LocalContradiction

-- ============================================================
-- The dual of L1
-- ============================================================

section Dual

variable (reqOf : NodeId → List NodeId)

/-- A node never owns a node whose requirement at the node's own step differs from
it. -/
def OwnedCompatible (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, ∀ q ∈ n.owners, ∀ req ∈ reqOf q.id,
    n.id.id.step = req.step → n.id.id = req

theorem OwnedCompatible_of_pruned {g g' : GPathM} (hpr : Pruned g g')
    (h : OwnedCompatible reqOf g) : OwnedCompatible reqOf g' := by
  intro n' hn' q hq req hreq hstep
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
  rw [hid] at hstep ⊢
  exact h n hn q (hown q hq) req hreq hstep

/-- **After a valid filter, a pinned step is pure.** Every node left at the step of
a pin carries the pinned id: it owns something at its own step, `OOS` says that is
itself, the review keeps it a global owner, and the pin removed every global owner
with another id. -/
theorem pinned_step_pure (g : GPathM) (hoos : SelfOwn.OOS g) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) (req : NodeId) (hreq : req ∈ reqs)
    (hlt : req.step < g.current_step) (h0 : 0 ≤ req.step)
    (n : PNodeM) (hn : n ∈ (filterAll g reqs).nodes) (hstep : n.id.id.step = req.step) :
    n.id.id = req := by
  have hpr := pruned_filterAll g reqs
  have hsome : ((filterAll g reqs).node? n.id).isSome := by
    simp only [node?, List.find?_isSome]
    exact ⟨n, hn, by simp⟩
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
  have hdmem : d ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hd
  have hdid : d.id = n.id := node?_id_eq _ n.id d hd
  have hvalid : isValidNode (filterAll g reqs) d = true :=
    review_node_valid (reqs.foldl filterRequire g) hv n.id d hd
  have hown := ownersOk_of_isValidNode _ d hvalid req.step h0 (by rw [hpr.step_eq]; exact hlt)
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hown
  obtain ⟨q, hq, hqs⟩ := hown
  have hqd : q = d.id := SelfOwn.OOS_filterAll g reqs hoos d hdmem q hq (by rw [hqs, hdid, hstep])
  have hfix := review_owners_within_gowners (reqs.foldl filterRequire g) hv n.id d hd
  have hqg : q ∈ (filterAll g reqs).gowners :=
    owners_mem_gowners _ d hfix q hq
      (hasStepEntry_of_isValid _ hv _ (by rw [hqs]; exact h0) (by rw [hqs, hpr.step_eq]; exact hlt))
  have hq0 := (pruned_review (reqs.foldl filterRequire g)).gowners_sub q hqg
  rcases (mem_foldl_filterRequire reqs g q hq0).2 req hreq with h | h
  · exact absurd hqs h
  · rw [← hdid, ← hqd]; exact h

theorem OwnedCompatible_addNode (hback : ∀ x, ∀ r ∈ reqOf x, r.step < x.step)
    (g : GPathM) (d : NodeId) (title : String) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hgn : GownersNodes.GN g)
    (hpure : ∀ n ∈ g.nodes, ∀ req ∈ reqOf d, n.id.id.step = req.step → n.id.id = req)
    (h : OwnedCompatible reqOf g) : OwnedCompatible reqOf (addNode g d title) := by
  intro n' hn' q hq req hreq hstep
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    have hni : n'.id = n.id := by rw [← hEq]; exact upMap_id g d n
    have hno : n'.owners = n.owners ++ gainedOwners g d n := by
      rw [← hEq]; exact upMap_owners g d n
    rw [hno, List.mem_append] at hq
    rw [hni] at hstep ⊢
    rcases hq with hq | hq
    · exact h n hn q hq req hreq hstep
    · rw [mapId_of_mem_newRowIds g d q (gainedOwners_subset g d n q hq)] at hreq
      exact hpure n hn req hreq hstep
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title n').mp hmem
    have hid : (rowNode g d title pid).id.id.step = d.step := by
      rw [rowNode_id, mapId_of_mem_newRowIds g d pid hpid]
    rw [rowNode_owners] at hq
    exfalso
    rcases (mem_rowOwners_iff g d pid q).mp hq with ⟨_, hgow⟩ | hqp
    · obtain ⟨m, hm, hmid⟩ := hgn q hgow
      have h1 := hbelow m hm
      have h2 := hback q.id req hreq
      rw [hmid] at h1
      rw [hid, hd] at hstep
      omega
    · have h2 := hback q.id req hreq
      have hqd : q.id = d := by rw [hqp]; exact mapId_of_mem_newRowIds g d pid hpid
      rw [hid] at hstep
      rw [hqd] at h2
      omega

theorem OwnedCompatible_join (g₁ g₂ : GPathM) (h₁ : OwnedCompatible reqOf g₁)
    (h₂ : OwnedCompatible reqOf g₂) : OwnedCompatible reqOf (join g₁ g₂) := by
  intro n' hn' q hq req hreq hstep
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    cases hg : g₂.node? n.id with
    | none =>
      have hni : n'.id = n.id := by rw [← hEq, hg]
      have hno : n'.owners = n.owners := by rw [← hEq, hg]
      rw [hni] at hstep ⊢; rw [hno] at hq
      exact h₁ n hn q hq req hreq hstep
    | some m =>
      have hni : n'.id = n.id := by rw [← hEq, hg]; rfl
      have hno : n'.owners = n.owners ++ m.owners.filter (fun r => !n.owners.contains r) := by
        rw [← hEq, hg]; rfl
      have hmid : m.id = n.id := node?_id_eq g₂ n.id m hg
      rw [hno, List.mem_append] at hq
      rw [hni] at hstep ⊢
      rcases hq with hq | hq
      · exact h₁ n hn q hq req hreq hstep
      · have := h₂ m (List.mem_of_find?_eq_some hg) q (List.mem_filter.mp hq).1 req hreq
          (by rw [hmid]; exact hstep)
        rw [← hmid]; exact this
  · exact h₂ n' (List.mem_filter.mp hmem).1 q hq req hreq hstep

theorem OwnedCompatible_initSeed (d : NodeId) (title : String)
    (hback : ∀ r ∈ reqOf d, r.step < d.step) :
    OwnedCompatible reqOf (GPathM.initSeed d title) := by
  intro n hn q hq req hreq hstep
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  rcases List.mem_singleton.mp hq with rfl
  exfalso
  have := hback req hreq
  simp only at hstep this
  omega

/-- **The dual of `L1` holds for every reachable state.** -/
theorem OwnedCompatible_reachable (hback : ∀ x, ∀ r ∈ reqOf x, r.step < x.step)
    (hnonneg : ∀ x, ∀ r ∈ reqOf x, 0 ≤ r.step)
    (g : GPathM) (h : Reachable reqOf g) : OwnedCompatible reqOf g := by
  induction h with
  | seed d title _ hreqs_back => exact OwnedCompatible_initSeed reqOf d title hreqs_back
  | up g d title hstep hreqs_back _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    show OwnedCompatible reqOf (up (filterAll g (reqOf d)) d title)
    simp only [GPathM.up]
    split
    · next hv =>
      exact OwnedCompatible_addNode reqOf hback _ d title (by rw [hpr.step_eq]; exact hstep)
        (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hr))
        (GownersNodes.GN_filterAll g (reqOf d) (GownersNodes.GN_reachable reqOf g hr))
        (fun n hn req hreq hs =>
          pinned_step_pure g (SelfOwn.OOS_reachable reqOf g hr) (reqOf d) hv req hreq
            (by have := hreqs_back req hreq; omega) (hnonneg d req hreq) n hn hs)
        (OwnedCompatible_of_pruned reqOf hpr ih)
    · exact OwnedCompatible_of_pruned reqOf hpr ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact OwnedCompatible_join reqOf g₁ g₂ ih₁ ih₂

end Dual

theorem reqOfCnf_nonneg (φ : Cnf) (d : NodeId) : ∀ r ∈ reqOfCnf φ d, 0 ≤ r.step := by
  intro r hr
  unfold reqOfCnf at hr
  split at hr
  · simp at hr
  · split at hr
    · split at hr
      · simp at hr
      · simp only [List.mem_singleton] at hr
        subst hr
        simp only
        omega
    · split at hr
      · simp at hr
      · split at hr
        · simp at hr
        · split at hr
          · simp at hr
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> exact lit_step_nonneg _

-- ============================================================
-- Reading the valid fixpoint
-- ============================================================

/-- The map node `r` is carried by some global owner of `g`. -/
def Present (g : GPathM) (r : NodeId) : Prop := ∃ q ∈ g.gowners, q.id = r

theorem fix_facts (φ : Cnf) (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g)
    (reqs : List NodeId) :
    ReqFiltered (reqOfCnf φ) (filterAll g reqs) ∧ GownersNodes.GN (filterAll g reqs) ∧
    OwnedCompatible (reqOfCnf φ) (filterAll g reqs) ∧ NodesOnMap φ (filterAll g reqs) := by
  have hr := reachable_of_mapReachable φ hwf g hmr
  exact ⟨filterAll_preserves_ReqFiltered (reqOfCnf φ) (L1 (reqOfCnf φ) hr) reqs,
    GownersNodes.GN_filterAll g reqs (GownersNodes.GN_reachable (reqOfCnf φ) g hr),
    OwnedCompatible_of_pruned (reqOfCnf φ) (pruned_filterAll g reqs)
      (OwnedCompatible_reachable (reqOfCnf φ) (fun x r hr => reqOfCnf_backward φ hwf x r hr)
        (fun x r hr => reqOfCnf_nonneg φ x r hr) g hr),
    NodesOnMap_filterAll φ g reqs (nodesOnMap_of_mapReachable φ g hmr)⟩

theorem node_of_gowner (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) (hgn : GownersNodes.GN (filterAll g reqs))
    (o : PathNodeId) (ho : o ∈ (filterAll g reqs).gowners) :
    ∃ d ∈ (filterAll g reqs).nodes, d.id = o ∧ isValidNode (filterAll g reqs) d = true ∧
      intersectOwners d.owners (filterAll g reqs).gowners = d.owners := by
  obtain ⟨n, hn, hnid⟩ := hgn o ho
  have hsome : ((filterAll g reqs).node? o).isSome := by
    simp only [node?, List.find?_isSome]
    exact ⟨n, hn, by simp [hnid]⟩
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨d, List.mem_of_find?_eq_some hd, node?_id_eq _ o d hd,
    review_node_valid (reqs.foldl filterRequire g) hv o d hd,
    review_owners_within_gowners (reqs.foldl filterRequire g) hv o d hd⟩

theorem owner_at_step (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) (d : PNodeM)
    (hvalid : isValidNode (filterAll g reqs) d = true)
    (hfix : intersectOwners d.owners (filterAll g reqs).gowners = d.owners)
    (k : Int) (h0 : 0 ≤ k) (hk : k < g.current_step) :
    ∃ q ∈ d.owners, q.id.step = k ∧ q ∈ (filterAll g reqs).gowners := by
  have hstep := (pruned_filterAll g reqs).step_eq
  have hown := ownersOk_of_isValidNode _ d hvalid k h0 (by rw [hstep]; exact hk)
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hown
  obtain ⟨q, hq, hqs⟩ := hown
  exact ⟨q, hq, hqs, owners_mem_gowners _ d hfix q hq
    (hasStepEntry_of_isValid _ hv _ (by rw [hqs]; exact h0) (by rw [hqs, hstep]; exact hk))⟩

theorem gowner_at_step (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) (k : Int) (h0 : 0 ≤ k) (hk : k < g.current_step) :
    ∃ o ∈ (filterAll g reqs).gowners, o.id.step = k := by
  have hent := hasStepEntry_of_isValid _ hv k h0
    (by rw [(pruned_filterAll g reqs).step_eq]; exact hk)
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  exact hent

theorem lit_bounds (φ : Cnf) (l : Lit) (hv : l.v < φ.nVars) (K : Int) (hK : litBlock φ < K) :
    0 ≤ l.step ∧ l.step < K :=
  ⟨lit_step_nonneg l, by have := lit_step_lt φ l hv; omega⟩

section Fixpoint

variable (φ : Cnf) (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g) (reqs : List NodeId)
  (hv : isValid (filterAll g reqs) = true)

include hwf hmr hv

/-- A surviving row of a seen clause keeps, for each literal it names as true, that
literal's true node. -/
theorem row_true_owned (j : Nat) (c : Clause) (hjlt : j < φ.clauses.length)
    (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < g.current_step)
    (e : PNodeM) (he : e ∈ (filterAll g reqs).nodes)
    (hvalid : isValidNode (filterAll g reqs) e = true)
    (hfix : intersectOwners e.owners (filterAll g reqs).gowners = e.owners)
    (hestep : e.id.id.step = clauseStep φ j) :
    1 ≤ e.id.id.index ∧ e.id.id.index ≤ 7 ∧
    (b1 e.id.id.index = 1 → Present (filterAll g reqs) (litReq c.l1 1)) ∧
    (b2 e.id.id.index = 1 → Present (filterAll g reqs) (litReq c.l2 1)) ∧
    (b3 e.id.id.index = 1 → Present (filterAll g reqs) (litReq c.l3 1)) := by
  obtain ⟨hrf, _, _, hmap⟩ := fix_facts φ hwf g hmr reqs
  have hon := hmap e he
  rw [hestep] at hon
  obtain ⟨hlo, hhi⟩ := index_range_of_clauseNode φ j hjlt e.id.id hon
  have hreq := reqOfCnf_clause φ e.id.id j c hjlt hj hestep
  have hcwf := hwf c (List.mem_iff_getElem?.mpr ⟨j, hj⟩)
  have hK : litBlock φ < g.current_step := by
    simp only [clauseStep] at hk; simp only [litBlock]; omega
  have key : ∀ (l : Lit) (bl : Int), l.v < φ.nVars →
      litReq l bl ∈ reqOfCnf φ e.id.id → bl = 1 → Present (filterAll g reqs) (litReq l 1) := by
    intro l bl hlv hmem hbl
    obtain ⟨h0, hlt⟩ := lit_bounds φ l hlv g.current_step hK
    obtain ⟨q, hq, hqs, hqg⟩ := owner_at_step g reqs hv e hvalid hfix l.step h0 hlt
    have hqid := hrf e he (litReq l bl) hmem q hq (by rw [hqs]; rfl)
    exact ⟨q, hqg, by rw [hqid, hbl]⟩
  exact ⟨hlo, hhi, key c.l1 _ hcwf.1.1 (by rw [hreq]; simp),
    key c.l2 _ hcwf.1.2.1 (by rw [hreq]; simp), key c.l3 _ hcwf.1.2.2 (by rw [hreq]; simp)⟩

/-- **Every seen clause keeps a literal that can be true.** -/
theorem clause_supported (j : Nat) (c : Clause) (hjlt : j < φ.clauses.length)
    (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < g.current_step) :
    Present (filterAll g reqs) (litReq c.l1 1) ∨ Present (filterAll g reqs) (litReq c.l2 1) ∨
      Present (filterAll g reqs) (litReq c.l3 1) := by
  obtain ⟨_, hgn, _, _⟩ := fix_facts φ hwf g hmr reqs
  have h0 : 0 ≤ clauseStep φ j := by simp only [clauseStep]; omega
  obtain ⟨o, ho, hos⟩ := gowner_at_step g reqs hv _ h0 hk
  obtain ⟨e, he, heid, hvalid, hfix⟩ := node_of_gowner g reqs hv hgn o ho
  obtain ⟨hlo, hhi, r1, r2, r3⟩ :=
    row_true_owned φ hwf g hmr reqs hv j c hjlt hj hk e he hvalid hfix (by rw [heid]; exact hos)
  rcases bits_not_all_zero _ hlo hhi with hb | hb | hb
  · exact Or.inl (r1 hb)
  · exact Or.inr (Or.inl (r2 hb))
  · exact Or.inr (Or.inr (r3 hb))

/-- A surviving false value of one of a clause's literals is owned by a surviving row
that does not make that literal true — the dual of `L1` at work. -/
theorem row_of_false_lit (j : Nat) (c : Clause) (hjlt : j < φ.clauses.length)
    (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < g.current_step)
    (x : Lit) (bx : Int → Int)
    (hmem : ∀ idx, litReq x (bx idx) ∈
      [litReq c.l1 (b1 idx), litReq c.l2 (b2 idx), litReq c.l3 (b3 idx)])
    (hpres : Present (filterAll g reqs) (litReq x 0)) :
    ∃ idx : Int, 1 ≤ idx ∧ idx ≤ 7 ∧ bx idx = 0 ∧
      (b1 idx = 1 → Present (filterAll g reqs) (litReq c.l1 1)) ∧
      (b2 idx = 1 → Present (filterAll g reqs) (litReq c.l2 1)) ∧
      (b3 idx = 1 → Present (filterAll g reqs) (litReq c.l3 1)) := by
  obtain ⟨_, hgn, hoc, _⟩ := fix_facts φ hwf g hmr reqs
  obtain ⟨o, ho, hoid⟩ := hpres
  obtain ⟨d, hd, hdid, hdvalid, hdfix⟩ := node_of_gowner g reqs hv hgn o ho
  have h0 : 0 ≤ clauseStep φ j := by simp only [clauseStep]; omega
  obtain ⟨q, hq, hqs, hqg⟩ := owner_at_step g reqs hv d hdvalid hdfix _ h0 hk
  obtain ⟨e, he, heid, hevalid, hefix⟩ := node_of_gowner g reqs hv hgn q hqg
  have hestep : e.id.id.step = clauseStep φ j := by rw [heid]; exact hqs
  obtain ⟨hlo, hhi, r1, r2, r3⟩ :=
    row_true_owned φ hwf g hmr reqs hv j c hjlt hj hk e he hevalid hefix hestep
  have hreq := reqOfCnf_clause φ e.id.id j c hjlt hj hestep
  have hqe : q.id = e.id.id := by rw [heid]
  have hdx : d.id.id = litReq x 0 := by rw [hdid]; exact hoid
  have hcomp := hoc d hd q hq (litReq x (bx e.id.id.index))
    (by rw [hqe, hreq]; exact hmem _) (by rw [hdx]; rfl)
  rw [hdx] at hcomp
  have hidx : (0 : Int) = bx e.id.id.index := congrArg NodeId.index hcomp
  exact ⟨e.id.id.index, hlo, hhi, hidx.symm, r1, r2, r3⟩

theorem forcing1 (j : Nat) (c : Clause) (hjlt : j < φ.clauses.length)
    (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < g.current_step)
    (h2 : ¬ Present (filterAll g reqs) (litReq c.l2 1))
    (h3 : ¬ Present (filterAll g reqs) (litReq c.l3 1)) :
    ¬ Present (filterAll g reqs) (litReq c.l1 0) := by
  intro hp
  obtain ⟨idx, hlo, hhi, hb, _, r2, r3⟩ :=
    row_of_false_lit φ hwf g hmr reqs hv j c hjlt hj hk c.l1 b1 (fun _ => by simp) hp
  rcases bits_not_all_zero idx hlo hhi with h | h | h
  · omega
  · exact h2 (r2 h)
  · exact h3 (r3 h)

theorem forcing2 (j : Nat) (c : Clause) (hjlt : j < φ.clauses.length)
    (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < g.current_step)
    (h1 : ¬ Present (filterAll g reqs) (litReq c.l1 1))
    (h3 : ¬ Present (filterAll g reqs) (litReq c.l3 1)) :
    ¬ Present (filterAll g reqs) (litReq c.l2 0) := by
  intro hp
  obtain ⟨idx, hlo, hhi, hb, r1, _, r3⟩ :=
    row_of_false_lit φ hwf g hmr reqs hv j c hjlt hj hk c.l2 b2 (fun _ => by simp) hp
  rcases bits_not_all_zero idx hlo hhi with h | h | h
  · exact h1 (r1 h)
  · omega
  · exact h3 (r3 h)

theorem forcing3 (j : Nat) (c : Clause) (hjlt : j < φ.clauses.length)
    (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < g.current_step)
    (h1 : ¬ Present (filterAll g reqs) (litReq c.l1 1))
    (h2 : ¬ Present (filterAll g reqs) (litReq c.l2 1)) :
    ¬ Present (filterAll g reqs) (litReq c.l3 0) := by
  intro hp
  obtain ⟨idx, hlo, hhi, hb, r1, r2, _⟩ :=
    row_of_false_lit φ hwf g hmr reqs hv j c hjlt hj hk c.l3 b3 (fun _ => by simp) hp
  rcases bits_not_all_zero idx hlo hhi with h | h | h
  · exact h1 (r1 h)
  · exact h2 (r2 h)
  · omega

variable (hlit : litBlock φ < g.current_step)

include hlit

theorem link_forward (v : Nat) (hv' : v < φ.nVars) (b : Int)
    (hp : Present (filterAll g reqs) ⟨varStep v, b⟩) :
    Present (filterAll g reqs) ⟨negStep v, 1 - b⟩ := by
  obtain ⟨_, hgn, hoc, _⟩ := fix_facts φ hwf g hmr reqs
  obtain ⟨o, ho, hoid⟩ := hp
  obtain ⟨d, hd, hdid, hdvalid, hdfix⟩ := node_of_gowner g reqs hv hgn o ho
  have hns0 : 0 ≤ negStep v := by simp only [negStep]; omega
  have hnslt : negStep v < g.current_step := by
    simp only [litBlock] at hlit; simp only [negStep]; omega
  obtain ⟨q, hq, hqs, hqg⟩ := owner_at_step g reqs hv d hdvalid hdfix _ hns0 hnslt
  obtain ⟨e, he, heid, _, _⟩ := node_of_gowner g reqs hv hgn q hqg
  have hestep : e.id.id.step = negStep v := by rw [heid]; exact hqs
  have hreq := reqOfCnf_neg φ e.id.id v hv' hestep
  have hqe : q.id = e.id.id := by rw [heid]
  have hdx : d.id.id = ⟨varStep v, b⟩ := by rw [hdid]; exact hoid
  have hcomp := hoc d hd q hq ⟨varStep v, 1 - e.id.id.index⟩
    (by rw [hqe, hreq]; simp) (by rw [hdx])
  rw [hdx] at hcomp
  have hb : b = 1 - e.id.id.index := congrArg NodeId.index hcomp
  refine ⟨q, hqg, ?_⟩
  rw [hqe]
  cases hei : e.id.id with
  | mk s i =>
    rw [hei] at hestep hb
    simp only at hestep hb
    rw [hestep]
    congr 1
    omega

theorem link_backward (v : Nat) (hv' : v < φ.nVars) (i : Int)
    (hp : Present (filterAll g reqs) ⟨negStep v, i⟩) :
    Present (filterAll g reqs) ⟨varStep v, 1 - i⟩ := by
  obtain ⟨hrf, hgn, _, _⟩ := fix_facts φ hwf g hmr reqs
  obtain ⟨o, ho, hoid⟩ := hp
  obtain ⟨e, he, heid, hevalid, hefix⟩ := node_of_gowner g reqs hv hgn o ho
  have hestep : e.id.id.step = negStep v := by rw [heid, hoid]
  have hreq := reqOfCnf_neg φ e.id.id v hv' hestep
  have hvs0 : 0 ≤ varStep v := by simp only [varStep]; omega
  have hvslt : varStep v < g.current_step := by
    simp only [litBlock] at hlit; simp only [varStep]; omega
  obtain ⟨r, hr, hrs, hrg⟩ := owner_at_step g reqs hv e hevalid hefix _ hvs0 hvslt
  have hrid := hrf e he ⟨varStep v, 1 - e.id.id.index⟩ (by rw [hreq]; simp) r hr (by rw [hrs])
  have hidx : e.id.id.index = i := by rw [heid, hoid]
  exact ⟨r, hrg, by rw [hrid, hidx]⟩

theorem var_has_value (v : Nat) (hv' : v < φ.nVars) :
    Present (filterAll g reqs) ⟨varStep v, 0⟩ ∨ Present (filterAll g reqs) ⟨varStep v, 1⟩ := by
  obtain ⟨_, hgn, _, hmap⟩ := fix_facts φ hwf g hmr reqs
  have h0 : 0 ≤ varStep v := by simp only [varStep]; omega
  have hlt : varStep v < litBlock φ := by simp only [varStep, litBlock]; omega
  obtain ⟨o, ho, hos⟩ := gowner_at_step g reqs hv _ h0 (by omega)
  obtain ⟨d, hd, hdid, _, _⟩ := node_of_gowner g reqs hv hgn o ho
  have hon := hmap d hd
  rw [hdid, hos, mapNodes_var φ _ h0 hlt] at hon
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
  rcases hon with h | h
  · exact Or.inl ⟨o, ho, h⟩
  · exact Or.inr ⟨o, ho, h⟩

end Fixpoint

-- ============================================================
-- Unit propagation, and why the review contains it
-- ============================================================

/-- The value of `x_v` that makes the literal true. -/
def tv (l : Lit) : Int := if l.pos then 1 else 0

/-- Unit propagation over the clauses seen below step `K`, starting from the map
nodes `P` still allows: `Refuted φ P K v b` rules out `x_v = b`. -/
inductive Refuted (φ : Cnf) (P : NodeId → Prop) (K : Int) : Nat → Int → Prop
  | base (v : Nat) (b : Int) (hv : v < φ.nVars) :
      ¬ (P ⟨varStep v, b⟩ ∧ P ⟨negStep v, 1 - b⟩) → Refuted φ P K v b
  | unit1 (j : Nat) (c : Clause) (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < K) :
      Refuted φ P K c.l2.v (tv c.l2) → Refuted φ P K c.l3.v (tv c.l3) →
      Refuted φ P K c.l1.v (1 - tv c.l1)
  | unit2 (j : Nat) (c : Clause) (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < K) :
      Refuted φ P K c.l1.v (tv c.l1) → Refuted φ P K c.l3.v (tv c.l3) →
      Refuted φ P K c.l2.v (1 - tv c.l2)
  | unit3 (j : Nat) (c : Clause) (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < K) :
      Refuted φ P K c.l1.v (tv c.l1) → Refuted φ P K c.l2.v (tv c.l2) →
      Refuted φ P K c.l3.v (1 - tv c.l3)

/-- Unit propagation reaches a conflict: a variable with both values refuted, or a
seen clause with every literal refuted true. -/
def UPConflict (φ : Cnf) (P : NodeId → Prop) (K : Int) : Prop :=
  (∃ v, Refuted φ P K v 0 ∧ Refuted φ P K v 1) ∨
  (∃ j c, φ.clauses[j]? = some c ∧ clauseStep φ j < K ∧
    Refuted φ P K c.l1.v (tv c.l1) ∧ Refuted φ P K c.l2.v (tv c.l2) ∧
    Refuted φ P K c.l3.v (tv c.l3))

theorem Refuted.lt {φ : Cnf} {P : NodeId → Prop} {K : Int} (hwf : WF φ) {v : Nat} {b : Int}
    (h : Refuted φ P K v b) : v < φ.nVars := by
  cases h with
  | base _ _ hv _ => exact hv
  | unit1 j c hj _ _ _ => exact (hwf c (List.mem_iff_getElem?.mpr ⟨j, hj⟩)).1.1
  | unit2 j c hj _ _ _ => exact (hwf c (List.mem_iff_getElem?.mpr ⟨j, hj⟩)).1.2.1
  | unit3 j c hj _ _ _ => exact (hwf c (List.mem_iff_getElem?.mpr ⟨j, hj⟩)).1.2.2

section Soundness

variable (φ : Cnf) (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g) (reqs : List NodeId)
  (hv : isValid (filterAll g reqs) = true) (hlit : litBlock φ < g.current_step)

include hwf hmr hv hlit

theorem true_iff (l : Lit) (hlv : l.v < φ.nVars) :
    Present (filterAll g reqs) (litReq l 1) ↔ Present (filterAll g reqs) ⟨varStep l.v, tv l⟩ := by
  cases hp : l.pos
  · have hst : litReq l 1 = ⟨negStep l.v, 1⟩ := by simp only [litReq, negStep_eq l hp]
    have htv : tv l = 0 := by simp [tv, hp]
    rw [hst, htv]
    constructor
    · intro h
      have := link_backward φ hwf g hmr reqs hv hlit l.v hlv 1 h
      simpa using this
    · intro h
      have := link_forward φ hwf g hmr reqs hv hlit l.v hlv 0 h
      simpa using this
  · have hst : litReq l 1 = ⟨varStep l.v, 1⟩ := by simp only [litReq, varStep_eq l hp]
    have htv : tv l = 1 := by simp [tv, hp]
    rw [hst, htv]

theorem false_iff (l : Lit) (hlv : l.v < φ.nVars) :
    Present (filterAll g reqs) (litReq l 0) ↔
      Present (filterAll g reqs) ⟨varStep l.v, 1 - tv l⟩ := by
  cases hp : l.pos
  · have hst : litReq l 0 = ⟨negStep l.v, 0⟩ := by simp only [litReq, negStep_eq l hp]
    have htv : tv l = 0 := by simp [tv, hp]
    rw [hst, htv]
    constructor
    · intro h
      have := link_backward φ hwf g hmr reqs hv hlit l.v hlv 0 h
      simpa using this
    · intro h
      have := link_forward φ hwf g hmr reqs hv hlit l.v hlv 1 h
      simpa using this
  · have hst : litReq l 0 = ⟨varStep l.v, 0⟩ := by simp only [litReq, varStep_eq l hp]
    have htv : tv l = 1 := by simp [tv, hp]
    have e : (1 : Int) - 1 = 0 := by omega
    rw [hst, htv, e]

/-- **What unit propagation refutes, the review has already removed.** -/
theorem refuted_absent {v : Nat} {b : Int}
    (h : Refuted φ (Present (reqs.foldl filterRequire g)) g.current_step v b) :
    ¬ Present (filterAll g reqs) ⟨varStep v, b⟩ := by
  induction h with
  | base v b hv' hnot =>
    intro hp
    apply hnot
    have hsub : ∀ r, Present (filterAll g reqs) r → Present (reqs.foldl filterRequire g) r :=
      fun r ⟨q, hq, hqr⟩ => ⟨q, (pruned_review _).gowners_sub q hq, hqr⟩
    exact ⟨hsub _ hp, hsub _ (link_forward φ hwf g hmr reqs hv hlit v hv' b hp)⟩
  | unit1 j c hj hk _ _ ih2 ih3 =>
    obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hj
    have hcwf := hwf c (List.mem_iff_getElem?.mpr ⟨j, hj⟩)
    intro hp
    rw [← false_iff φ hwf g hmr reqs hv hlit c.l1 hcwf.1.1] at hp
    exact forcing1 φ hwf g hmr reqs hv j c hjlt hj hk
      (fun h => ih2 ((true_iff φ hwf g hmr reqs hv hlit c.l2 hcwf.1.2.1).mp h))
      (fun h => ih3 ((true_iff φ hwf g hmr reqs hv hlit c.l3 hcwf.1.2.2).mp h)) hp
  | unit2 j c hj hk _ _ ih1 ih3 =>
    obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hj
    have hcwf := hwf c (List.mem_iff_getElem?.mpr ⟨j, hj⟩)
    intro hp
    rw [← false_iff φ hwf g hmr reqs hv hlit c.l2 hcwf.1.2.1] at hp
    exact forcing2 φ hwf g hmr reqs hv j c hjlt hj hk
      (fun h => ih1 ((true_iff φ hwf g hmr reqs hv hlit c.l1 hcwf.1.1).mp h))
      (fun h => ih3 ((true_iff φ hwf g hmr reqs hv hlit c.l3 hcwf.1.2.2).mp h)) hp
  | unit3 j c hj hk _ _ ih1 ih2 =>
    obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hj
    have hcwf := hwf c (List.mem_iff_getElem?.mpr ⟨j, hj⟩)
    intro hp
    rw [← false_iff φ hwf g hmr reqs hv hlit c.l3 hcwf.1.2.2] at hp
    exact forcing3 φ hwf g hmr reqs hv j c hjlt hj hk
      (fun h => ih1 ((true_iff φ hwf g hmr reqs hv hlit c.l1 hcwf.1.1).mp h))
      (fun h => ih2 ((true_iff φ hwf g hmr reqs hv hlit c.l2 hcwf.1.2.1).mp h)) hp

end Soundness

/-- **The review contains unit propagation.** If unit propagation over the seen
clauses, starting from the values the pins leave, reaches a conflict, then
`filterAll` leaves the state invalid. -/
theorem invalid_filterAll_of_UPConflict (φ : Cnf) (hwf : WF φ) (g : GPathM)
    (hmr : MapReachable φ g) (reqs : List NodeId) (hlit : litBlock φ < g.current_step)
    (hc : UPConflict φ (Present (reqs.foldl filterRequire g)) g.current_step) :
    isValid (filterAll g reqs) = false := by
  cases hv : isValid (filterAll g reqs) with
  | false => rfl
  | true =>
    exfalso
    rcases hc with ⟨v, h0, h1⟩ | ⟨j, c, hj, hk, h1, h2, h3⟩
    · rcases var_has_value φ hwf g hmr reqs hv hlit v (Refuted.lt hwf h0) with hp | hp
      · exact refuted_absent φ hwf g hmr reqs hv hlit h0 hp
      · exact refuted_absent φ hwf g hmr reqs hv hlit h1 hp
    · obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hj
      have hcwf := hwf c (List.mem_iff_getElem?.mpr ⟨j, hj⟩)
      rcases clause_supported φ hwf g hmr reqs hv j c hjlt hj hk with hp | hp | hp
      · exact refuted_absent φ hwf g hmr reqs hv hlit h1
          ((true_iff φ hwf g hmr reqs hv hlit c.l1 hcwf.1.1).mp hp)
      · exact refuted_absent φ hwf g hmr reqs hv hlit h2
          ((true_iff φ hwf g hmr reqs hv hlit c.l2 hcwf.1.2.1).mp hp)
      · exact refuted_absent φ hwf g hmr reqs hv hlit h3
          ((true_iff φ hwf g hmr reqs hv hlit c.l3 hcwf.1.2.2).mp hp)

/-- info: 'AbsSat.GraphPath.Model.UnitPropagation.OwnedCompatible_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnedCompatible_reachable

/-- info: 'AbsSat.GraphPath.Model.UnitPropagation.refuted_absent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refuted_absent

/-- info: 'AbsSat.GraphPath.Model.UnitPropagation.invalid_filterAll_of_UPConflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms invalid_filterAll_of_UPConflict

end AbsSat.GraphPath.Model.UnitPropagation
