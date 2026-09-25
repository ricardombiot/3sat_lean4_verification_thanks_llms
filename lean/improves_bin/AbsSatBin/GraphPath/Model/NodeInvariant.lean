-- lean/improves_bin/AbsSatBin/GraphPath/Model/NodeInvariant.lean
import AbsSatBin.GraphPath.Model.Certifies
import AbsSatBin.GraphPath.Model.Pinned
import AbsSatBin.GraphMap.CnfMapBin
import AbsSatBin.GraphPath.Model.ArcConsistency

/-!
# The node invariant

v66 measured, against the clauses seen so far, that **every node of every valid
machine state lies on a solution living inside it** — 0 exceptions in 188,435
nodes. In graph terms that is `SupportedS`: every node lies on a sound chain.
This module runs the induction over the construction.

## What closes, and what does not

`Reachable` builds a state by three moves: `seed`, `join`, and `up` — which is
`filterAll` by the destination's requirements followed by `addNode`. Everything
but one case closes:

* `seed` — one node, one chain;
* `join` — `SupportedS_join`: chains survive the merge;
* `addNode` — a chain extends by the new node (`ChainSound_addNode`), and the
  new node sits on the extension of any chain;
* the review inside `filterAll` — `SupportedS_review`;
* the `filterRequire` pins, **when the step's requirements are easy**: none at
  all, or a single one on the step just below. On a 3SAT map that is every
  literal step and both fusion steps. A negation node pins its own positive
  step, which is the top of the state it is sent from, and the top of a machine
  state carries a single map id — its key (`TopKey`, proved here). So that pin
  either changes nothing or empties the top and kills the state.

What remains is the pin at a step with **hard** requirements — on a 3SAT map,
exactly the **clause steps**, three requirements on literals far below. There
the obligation is

    HardStepExact : every node that survives the filter lies on a sound chain

and it is not proved. It is the one place a proof has to be found, and the one
place a counterexample could live.

`owns_required` states exactly what the filter *does* guarantee: a surviving
node owns, at each required step, a node with the required id — one
requirement at a time. `ClauseStepExact` needs all three on a single chain. The
distance between the two is a Helly-type property, known to fail in general
(v13's 164 witnesses, `ExtendUp`'s dead ends), and `Decision.lean` shows what
closing it would be worth: with it, the machine decides 3SAT, in polynomial
time.
-/

namespace AbsSatBin.GraphPath.Model.NodeInvariant

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM

-- ============================================================
-- The top of a machine state carries its key
-- ============================================================

/-- Global owners sit at non-negative steps below the current one, and those
at the top step carry the map id the state is keyed by. -/
def TopKey (g : GPathM) : Prop :=
  0 ≤ g.current_step ∧
  (∀ q ∈ g.gowners, 0 ≤ q.id.step ∧ q.id.step < g.current_step) ∧
  (∀ q ∈ g.gowners, q.id.step = g.current_step - 1 → g.map_parent = some q.id)

theorem TopKey_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (h : TopKey g) : TopKey (addNode g d title forb) := by
  obtain ⟨h0, hb, ht⟩ := h
  have hcs : (addNode g d title forb).current_step = g.current_step + 1 := rfl
  have hmp : (addNode g d title forb).map_parent = some d := rfl
  refine ⟨by rw [hcs]; omega, ?_, ?_⟩
  · intro q hq
    rw [addNode_gowners] at hq
    rw [hcs]
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨hq0, hq1⟩ := hb q hq
      exact ⟨hq0, by omega⟩
    · rw [mapId_of_mem_newRowIds g d forb q hq]
      show 0 ≤ d.step ∧ d.step < g.current_step + 1
      exact ⟨by omega, by omega⟩
  · intro q hq hqs
    rw [addNode_gowners] at hq
    rw [hcs] at hqs
    rw [hmp]
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨_, hq1⟩ := hb q hq
      exact absurd hqs (by omega)
    · rw [mapId_of_mem_newRowIds g d forb q hq]

theorem TopKey_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : TopKey g) : TopKey g' := by
  obtain ⟨h0, hb, ht⟩ := h
  refine ⟨by rw [hpr.step_eq]; exact h0, ?_, ?_⟩
  · intro q hq
    rw [hpr.step_eq]; exact hb q (hpr.gowners_sub q hq)
  · intro q hq hqs
    rw [hpr.step_eq] at hqs
    rw [hpr.map_parent_eq]; exact ht q (hpr.gowners_sub q hq) hqs

theorem TopKey_empty : TopKey empty :=
  ⟨Int.le_refl 0, fun _ hq => absurd hq List.not_mem_nil, fun _ hq => absurd hq List.not_mem_nil⟩

theorem TopKey_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    TopKey (GPathM.initSeed d title) := by
  have : GPathM.initSeed d title = addNode empty d title noForb := by
    unfold GPathM.initSeed GPathM.up
    rw [if_pos (by rfl : isValid empty = true), skipsWindow_noForb]
    rfl
  rw [this]
  exact TopKey_addNode empty d title noForb hstep TopKey_empty

theorem okJoin_parts {g₁ g₂ : GPathM} (h : okJoin g₁ g₂ = true) :
    g₁.current_step = g₂.current_step ∧ g₁.map_parent = g₂.map_parent := by
  unfold GPathM.okJoin at h
  have h1 := (Bool.and_eq_true _ _).mp h
  have h2 := (Bool.and_eq_true _ _).mp h1.1
  have h3 := (Bool.and_eq_true _ _).mp h2.1
  exact ⟨eq_of_beq h3.1, eq_of_beq h3.2⟩

theorem TopKey_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : TopKey g₁) (h₂ : TopKey g₂) : TopKey (join g₁ g₂) := by
  obtain ⟨hcs, hmp⟩ := okJoin_parts hok
  have hjcs : (join g₁ g₂).current_step = g₁.current_step := rfl
  have hjmp : (join g₁ g₂).map_parent = g₁.map_parent := rfl
  have hmem : ∀ q ∈ (join g₁ g₂).gowners, q ∈ g₁.gowners ∨ q ∈ g₂.gowners := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (List.mem_filter.mp hq).1
  refine ⟨by rw [hjcs]; exact h₁.1, ?_, ?_⟩
  · intro q hq
    rw [hjcs]
    rcases hmem q hq with hq | hq
    · exact h₁.2.1 q hq
    · rw [hcs]; exact h₂.2.1 q hq
  · intro q hq hqs
    rw [hjcs] at hqs; rw [hjmp]
    rcases hmem q hq with hq | hq
    · exact h₁.2.2 q hq hqs
    · rw [hmp]; exact h₂.2.2 q hq (by rw [← hcs]; exact hqs)

variable (reqOf : NodeId → List NodeId) (forb : PathNodeId → Bool)

/-- **Every machine state is keyed at its top.** -/
theorem TopKey_reachable (g : GPathM) (h : Reachable reqOf forb g) : TopKey g := by
  induction h with
  | seed d title hstep _ => exact TopKey_initSeed d title hstep
  | up g d title hstep _ _ _ ih =>
    have hf : TopKey (filterAll g (reqOf d)) := TopKey_of_pruned (pruned_filterAll g (reqOf d)) ih
    unfold GPathM.upFiltering GPathM.up
    cases hv : isValid (filterAll g (reqOf d)) with
    | true =>
      rw [if_pos rfl]
      have hadd := TopKey_addNode _ d title forb
        (by rw [(pruned_filterAll g (reqOf d)).step_eq]; exact hstep) hf
      split
      · exact TopKey_of_pruned (pruned_review _) hadd
      · exact hadd
    | false => rw [if_neg Bool.false_ne_true]; exact hf
  | join g₁ g₂ hok _ _ ih₁ ih₂ => exact TopKey_join g₁ g₂ hok ih₁ ih₂

-- ============================================================
-- The easy pins
-- ============================================================

/-- The requirements of a step are **easy** when there are none, or a single
one on the step just below — the top of the state the node is sent from. -/
def Easy (g : GPathM) (reqs : List NodeId) : Prop :=
  reqs = [] ∨ ∃ r, reqs = [r] ∧ r.step = g.current_step - 1

/-- **An easy pin cannot leave a node off every chain.** No requirement: the
filter is the review, and the review preserves support. A pin on the top: the
top carries one map id, so the pin either changes nothing or kills the state. -/
theorem SupportedS_filterAll_easy (g : GPathM) (reqs : List NodeId) (htk : TopKey g)
    (hsup : SupportedS g) (heasy : Easy g reqs)
    (hv : isValid (filterAll g reqs) = true) : SupportedS (filterAll g reqs) := by
  rcases heasy with rfl | ⟨r, rfl, hr⟩
  · exact SupportedS_review g hsup
  · have hshape : filterAll g [r] = review (filterRequire g r) := rfl
    obtain ⟨h0, hb, ht⟩ := htk
    -- the pin changes nothing: every top global owner already is `r`
    have hpin : ∀ q ∈ g.gowners, q.id.step = r.step → q.id = r := by
      intro q hq hqs
      have hlo : 0 ≤ r.step := by rw [← hqs]; exact (hb q hq).1
      have hvf : isValid (filterRequire g r) = true :=
        Certifies.isValid_of_pruned (pruned_review _) (by rw [← hshape]; exact hv)
      obtain ⟨q', hq', hq's⟩ := PickInduction.gowner_of_isValid _ hvf r.step hlo
        (by show r.step < g.current_step; omega)
      have hq'f := List.mem_filter.mp hq'
      have hq'r : q'.id = r := by
        have := hq'f.2
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
        rcases this with h | h
        · exact absurd hq's h
        · exact h
      have e1 := ht q hq (by rw [hqs, hr])
      have e2 := ht q' hq'f.1 (by rw [hq's, hr])
      rw [e1] at e2
      rw [Option.some.inj e2, hq'r]
    rw [hshape, PickInduction.filterRequire_eq_self_of_pinned g r hpin]
    exact SupportedS_review g hsup

-- ============================================================
-- The `up` move
-- ============================================================

/-- `addNode` keeps support: old nodes ride their chains up, the new node rides
any chain.

**Bin map:** when no window is skipped (`hnoskip`). With a skipped window an old node may be left
without a son, off every chain, until the review prunes it — that case is `SkipExact`. -/
theorem SupportedS_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (hsup : SupportedS g) (hinh : ∃ sel, ChainSound g sel)
    (hnoskip : skipsWindow g d forb = false) :
    SupportedS (addNode g d title forb) := by
  have hnf : ∀ sel, IsChain g sel → forb (extendPid g d sel) = false := by
    intro sel hc
    have hmem := extendPid_mem_shiftRowIds g d sel hc
    cases hfb : forb (extendPid g d sel) with
    | false => rfl
    | true =>
      exfalso
      have : skipsWindow g d forb = true := List.any_eq_true.mpr ⟨_, hmem, hfb⟩
      rw [hnoskip] at this
      exact Bool.false_ne_true this
  intro pid n hn
  have hmem : n ∈ (addNode g d title forb).nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq _ pid n hn
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · obtain ⟨n₁, hn₁, hEq⟩ := List.mem_map.mp hl
    have hsame : n.id = n₁.id := by rw [← hEq, upMap_id]
    have hstep : pid.id.step < g.current_step := by rw [← hid, hsame]; exact hbelow n₁ hn₁
    obtain ⟨n₀, hn₀, _⟩ := addNode_node?_below g d title forb hd pid n hn hstep
    obtain ⟨sel, hsel, htop⟩ := hsup pid n₀ hn₀
    refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hsel
      (hnf sel hsel.chain.1), ?_⟩
    rw [extend_below g d sel pid.id.step hstep]
    exact htop
  · -- a node of the new row: the chain that supports one of its parents
    obtain ⟨q, hq, rfl⟩ := (mem_newRow_iff g d title forb n).mp hr
    rw [rowNode_id] at hid
    subst hid
    have hstepq : q.id.step = g.current_step := by
      rw [mapId_of_mem_newRowIds g d forb q hq]; exact hd
    by_cases hpos : 0 < g.current_step
    · obtain ⟨p, hp⟩ : ∃ p, p ∈ rowParents g d q := by
        obtain ⟨r, hr', hrq⟩ := exists_shift_of_mem_newRowIds g d forb q hpos hq
        exact ⟨r, List.mem_filter.mpr ⟨hr', beq_iff_eq.mpr hrq.symm⟩⟩
      have hpmem : p ∈ newParents g := rowParents_subset g d q p hp
      have hpline : p ∈ (g.line (g.current_step - 1)).map (·.id) := by
        unfold newParents at hpmem; rwa [if_pos hpos] at hpmem
      obtain ⟨np, hnp, hnq⟩ := List.mem_map.mp hpline
      have hmemp : np ∈ g.nodes := (List.mem_filter.mp hnp).1
      have hsomep : (g.node? p).isSome = true := by
        have := node?_isSome_of_mem g np hmemp; rwa [hnq] at this
      obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp hsomep
      obtain ⟨sel, hsel, htop⟩ := hsup p mp hmp
      have hpstep : p.id.step = g.current_step - 1 := by
        rw [← hnq]; exact eq_of_beq (List.mem_filter.mp hnp).2
      have hselp : sel (g.current_step - 1) = p := by rw [← hpstep]; exact htop
      refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hsel
        (hnf sel hsel.chain.1), ?_⟩
      rw [hstepq, extend_top]
      unfold extendPid
      rw [if_pos hpos, hselp]
      exact shiftPid_of_mem_rowParents g d q p hp
    · obtain ⟨sel, hsel⟩ := hinh
      refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hsel
        (hnf sel hsel.chain.1), ?_⟩
      rw [hstepq, extend_top]
      unfold extendPid
      rw [if_neg hpos]
      exact (eq_root_of_mem_newRowIds_zero g d forb hpos q hq).symm

/-- A valid state with support has a chain: take any global owner at step 0. -/
theorem chain_of_SupportedS (g : GPathM) (hgn : GownersNodes.GN g) (hsup : SupportedS g)
    (hv : isValid g = true) (hpos : 0 < g.current_step) : ∃ sel, ChainSound g sel := by
  obtain ⟨q, hq, _⟩ := PickInduction.gowner_of_isValid g hv 0 (Int.le_refl 0) hpos
  obtain ⟨n, hn, hnid⟩ := hgn q hq
  have hs : (g.node? q).isSome = true := by rw [← hnid]; exact node?_isSome_of_mem g n hn
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨sel, hsel, _⟩ := hsup q m hm
  exact ⟨sel, hsel⟩

-- ============================================================
-- The node invariant
-- ============================================================

/-- A machine state always has at least one step. -/
theorem pos_reachable (g : GPathM) (h : Reachable reqOf forb g) : 0 < g.current_step := by
  induction h with
  | seed d title _ _ => rw [initSeed_current]; decide
  | up g d title _ _ _ _ ih =>
    unfold GPathM.upFiltering GPathM.up
    cases hv : isValid (filterAll g (reqOf d)) with
    | true =>
      rw [if_pos rfl]
      split
      · rw [(pruned_review _).step_eq, addNode_current, (pruned_filterAll g (reqOf d)).step_eq]
        omega
      · rw [addNode_current, (pruned_filterAll g (reqOf d)).step_eq]; omega
    | false =>
      rw [if_neg Bool.false_ne_true, (pruned_filterAll g (reqOf d)).step_eq]; exact ih
  | join g₁ g₂ _ _ _ ih₁ _ => exact ih₁

/-- **The node invariant**: every node of a valid state lies on a sound chain. -/
def NodeInv (g : GPathM) : Prop := isValid g = true → SupportedS g

/-- **The one obligation**: at a step whose requirements are not easy, the
filter leaves every surviving node on a sound chain. -/
def HardStepExact : Prop :=
  ∀ (g : GPathM) (d : NodeId), Reachable reqOf forb g → d.step = g.current_step →
    isValid g = true → SupportedS g →
    ¬ Easy g (reqOf d) → isValid (filterAll g (reqOf d)) = true →
    SupportedS (filterAll g (reqOf d))

/-- **The second obligation (bin map)**: when the UP skips a prohibited window, the review that
follows leaves every node on a sound chain. The UP can leave an old node without a son (error 4
of the Julia report); this says the review prunes it and breaks nothing else. -/
def SkipExact : Prop :=
  ∀ (g : GPathM) (d : NodeId) (title : String), Reachable reqOf forb g →
    d.step = g.current_step → isValid g = true → SupportedS g →
    isValid (filterAll g (reqOf d)) = true → SupportedS (filterAll g (reqOf d)) →
    skipsWindow (filterAll g (reqOf d)) d forb = true →
    isValid (review (addNode (filterAll g (reqOf d)) d title forb)) = true →
    SupportedS (review (addNode (filterAll g (reqOf d)) d title forb))

/-- Easy or not, decided without choice. -/
theorem easy_or_not (g : GPathM) (reqs : List NodeId) : Easy g reqs ∨ ¬ Easy g reqs := by
  match reqs with
  | [] => exact Or.inl (Or.inl rfl)
  | [r] =>
    if hr : r.step = g.current_step - 1 then exact Or.inl (Or.inr ⟨r, rfl, hr⟩)
    else
      refine Or.inr ?_
      rintro (h | ⟨r', h, hr'⟩)
      · exact List.cons_ne_nil _ _ h
      · have : r = r' := List.head_eq_of_cons_eq h
        exact hr (this ▸ hr')
  | a :: b :: rest =>
    refine Or.inr ?_
    rintro (h | ⟨r', h, _⟩)
    · exact List.cons_ne_nil _ _ h
    · exact List.cons_ne_nil _ _ (List.tail_eq_of_cons_eq h)

/-- **The node invariant holds in every state the machine builds**, given the
one obligation at the hard steps. -/
theorem NodeInv_reachable (hhard : HardStepExact reqOf forb) (hskip : SkipExact reqOf forb)
    (g : GPathM) (h : Reachable reqOf forb g) : NodeInv g := by
  induction h with
  | seed d title hstep _ =>
    intro _ pid n hn
    have hmem : n ∈ (GPathM.initSeed d title).nodes := List.mem_of_find?_eq_some hn
    rw [initSeed_nodes] at hmem
    have hid : n.id = pid := node?_id_eq _ pid n hn
    rw [List.mem_singleton.mp hmem] at hid
    exact ⟨_, ChainSound_initSeed d title hstep, by rw [← hid]⟩
  | up g d title hstep hback hdist hr ih =>
    intro hv
    have hgv : isValid g = true := Certifies.isValid_of_upFiltering g (reqOf d) d title forb hv
    have hfv : isValid (filterAll g (reqOf d)) = true :=
      Certifies.isValid_of_filterAll_of_upFiltering g (reqOf d) d title forb hv
    have hsup := ih hgv
    have hfsup : SupportedS (filterAll g (reqOf d)) := by
      rcases easy_or_not g (reqOf d) with he | he
      · exact SupportedS_filterAll_easy g _ (TopKey_reachable reqOf forb g hr) hsup he hfv
      · exact hhard g d hr hstep hgv hsup he hfv
    have hpr := pruned_filterAll g (reqOf d)
    have hbelow := Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf forb hr)
    have hmok := MachineOk_of_pruned hpr (Certifies.MachineOk_reachable reqOf forb g hr)
    have hpos : 0 < (filterAll g (reqOf d)).current_step := by
      rw [hpr.step_eq]; exact pos_reachable reqOf forb g hr
    revert hv
    simp only [upFiltering, up, hfv, if_true]
    split
    · rename_i hsk
      intro hv
      exact hskip g d title hr hstep hgv hsup hfv hfsup hsk hv
    · rename_i hsk
      intro _
      exact SupportedS_addNode _ d title forb (by rw [hpr.step_eq]; exact hstep) hbelow hmok hfsup
        (chain_of_SupportedS _ (GownersNodes.GN_filterAll g (reqOf d)
          (GownersNodes.GN_reachable reqOf forb g hr)) hfsup hfv hpos)
        (by simpa using hsk)
  | join g₁ g₂ hok _ _ ih₁ ih₂ =>
    intro _
    have hv₁ := Certifies.isValid_left_of_okJoin hok
    have hv₂ : isValid g₂ = true := by
      unfold GPathM.okJoin at hok
      exact ((Bool.and_eq_true _ _).mp hok).2
    exact SupportedS_join g₁ g₂ hok (ih₁ hv₁) (ih₂ hv₂)


/-- info: 'AbsSatBin.GraphPath.Model.NodeInvariant.NodeInv_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NodeInv_reachable

/-- info: 'AbsSatBin.GraphPath.Model.NodeInvariant.SupportedS_filterAll_easy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SupportedS_filterAll_easy

-- ============================================================
-- What the clause filter does guarantee — and the gap
-- ============================================================

theorem gowners_foldl_filterRequire (reqs : List NodeId) :
    ∀ (g : GPathM) (q : PathNodeId), q ∈ (reqs.foldl filterRequire g).gowners →
      q ∈ g.gowners ∧ ∀ r ∈ reqs, q.id.step = r.step → q.id = r := by
  induction reqs with
  | nil => intro g q hq; exact ⟨hq, fun _ hr => absurd hr List.not_mem_nil⟩
  | cons r rest ih =>
    intro g q hq
    simp only [List.foldl_cons] at hq
    obtain ⟨hq1, hrest⟩ := ih (filterRequire g r) q hq
    have hf := List.mem_filter.mp hq1
    refine ⟨hf.1, ?_⟩
    intro r' hr' hs
    rcases List.mem_cons.mp hr' with rfl | hr'
    · have := hf.2
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
      rcases this with h | h
      · exact absurd hs h
      · exact h
    · exact hrest r' hr' hs

/-- **What the clause filter guarantees.** A node that survives the filter owns,
at every required step, a node carrying the required map id — one requirement
at a time.

`ClauseStepExact` asks for more: a single sound chain through the node that
carries **all three** required ids at once. The review establishes the three
pairs; nothing in it assembles them into one solution. That is the gap between
this theorem and `ClauseStepExact`, and it is the whole of the wall. -/
theorem owns_required (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf forb g)
    (hv : isValid (filterAll g reqs) = true) (p : PathNodeId) (n : PNodeM)
    (hn : (filterAll g reqs).node? p = some n) (r : NodeId) (hr : r ∈ reqs)
    (hr0 : 0 ≤ r.step) (hr1 : r.step < g.current_step) :
    ∃ q ∈ n.owners, q.id = r := by
  have ctx := Pinned.ctx_filterAll reqOf forb g reqs hreach hv
  have hcs : (filterAll g reqs).current_step = g.current_step := (pruned_filterAll g reqs).step_eq
  have hok := owners_ok_of_isValidNode _ n (ctx.nodeval p n hn)
  have hk : r.step ∈ intRange 0 ((filterAll g reqs).current_step - 1) :=
    mem_intRange hr0 (by rw [hcs]; omega)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hok r.step hk)
  have hqs' : q.id.step = r.step := eq_of_beq hqs
  have hgow : q ∈ (filterAll g reqs).gowners :=
    ctx.ownGow p n hn q hq (by rw [hqs']; exact hr0) (by rw [hqs', hcs]; exact hr1)
  have hgow' : q ∈ (reqs.foldl filterRequire g).gowners :=
    (pruned_review (reqs.foldl filterRequire g)).gowners_sub q hgow
  exact ⟨q, hq, (gowners_foldl_filterRequire reqs g q hgow').2 r hr hqs'⟩

/-- info: 'AbsSatBin.GraphPath.Model.NodeInvariant.owns_required' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owns_required

-- ============================================================
-- On the bin map, the hard steps are the literal steps of the clauses
-- ============================================================

/-!
**Bin map.** Every literal step `Lₚ` of a clause has a *single* requirement, but on a literal
far below — not the step just below — so it is not `Easy`: the hard steps are the `3m` literal
steps, where `lean_project` had the `m` seven-row clause steps. The variable and fusion steps
are easy exactly as before. And the bin map adds `SkipExact`, the review after a skipped window.
-/

open AbsSatBin.Cnf AbsSatBin.GraphMap.CnfMapBin in
/-- **The obligations, for the bin map**: the literal steps of the clauses, and the review after
a skipped window. -/
def ClauseStepExact (φ : Cnf) : Prop :=
  (∀ (g : GPathM) (d : NodeId), Reachable (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ) g → d.step = g.current_step →
    isValid g = true → SupportedS g →
    midFusion φ < d.step → d.step < fusionTop φ →
    isValid (filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)) = true → SupportedS (filterAll g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d)))
  ∧ SkipExact (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ)

open AbsSatBin.Cnf AbsSatBin.GraphMap.CnfMapBin in
/-- Every non-clause step of the bin map is easy: the root, positive literals and the fusion
steps have no requirements, and a negation node's single requirement is its own positive step,
the top of the state it is sent from. -/
theorem easy_of_not_clause (φ : Cnf) (g : GPathM) (d : NodeId) (hstep : d.step = g.current_step)
    (h : ¬ (midFusion φ < d.step ∧ d.step < fusionTop φ)) : Easy g (AbsSatBin.GraphMap.CnfMapBin.reqOf φ d) := by
  unfold AbsSatBin.GraphMap.CnfMapBin.reqOf
  if h0 : d.step ≤ 0 then
    rw [if_pos h0]; exact Or.inl rfl
  else
    rw [if_neg h0]
    if h1 : d.step < midFusion φ then
      rw [if_pos h1]
      if h2 : d.step % 2 = 1 then  -- idx: bin parity of a positive literal (2v+1), the same test as `CnfMapBin.reqOf`
        rw [if_pos h2]; exact Or.inl rfl
      else
        rw [if_neg h2]
        exact Or.inr ⟨_, rfl, by show d.step - 1 = g.current_step - 1; omega⟩  -- idx: a negation node requires the step just below
    else
      rw [if_neg h1]
      if h3 : d.step = midFusion φ then
        rw [if_pos h3]; exact Or.inl rfl
      else
        rw [if_neg h3]
        if h4 : fusionTop φ ≤ d.step then
          rw [if_pos h4]; exact Or.inl rfl
        else
          exact absurd ⟨by omega, by omega⟩ h

open AbsSatBin.Cnf AbsSatBin.GraphMap.CnfMapBin in
theorem HardStepExact_of_ClauseStepExact (φ : Cnf) (h : ClauseStepExact φ) :
    HardStepExact (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ) := by
  intro g d hr hstep hv hsup hne hfv
  have hclause : midFusion φ < d.step ∧ d.step < fusionTop φ := by
    cases Int.decLt (midFusion φ) d.step with
    | isFalse hlt =>
      exact absurd (easy_of_not_clause φ g d hstep (fun ⟨a, _⟩ => hlt a)) hne
    | isTrue hlt =>
      cases Int.decLt d.step (fusionTop φ) with
      | isFalse hgt =>
        exact absurd (easy_of_not_clause φ g d hstep (fun ⟨_, b⟩ => hgt b)) hne
      | isTrue hgt => exact ⟨hlt, hgt⟩
  exact h.1 g d hr hstep hv hsup hclause.1 hclause.2 hfv

open AbsSatBin.Cnf AbsSatBin.GraphMap.CnfMapBin in
/-- **The node invariant on the bin map, reduced to its two obligations.** -/
theorem NodeInv_of_ClauseStepExact (φ : Cnf) (h : ClauseStepExact φ) (g : GPathM)
    (hr : Reachable (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ) g) : NodeInv g :=
  NodeInv_reachable (AbsSatBin.GraphMap.CnfMapBin.reqOf φ) (isProhibited φ) (HardStepExact_of_ClauseStepExact φ h) h.2 g hr

/-- info: 'AbsSatBin.GraphPath.Model.NodeInvariant.NodeInv_of_ClauseStepExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NodeInv_of_ClauseStepExact

end AbsSatBin.GraphPath.Model.NodeInvariant
