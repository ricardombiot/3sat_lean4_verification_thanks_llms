-- lean_project/AbsSat/GraphPath/Model/ClauseFilter.lean
import AbsSat.GraphPath.Model.Decision

/-!
# The clause filter, in small parts

`ClauseStepExact` asks: after a clause node's three requirements are pinned and
the review has run, every surviving node lies on a sound chain. This module
splits it.

**Part 1 — one requirement at a time.** A surviving node starts with *some*
chain (support before the filter). Add the requirements one by one: from a
chain through the node matching some of them, get one matching one more. After
the last, push the chain through the filter (`ChainSound_filterAll`). So the
whole obligation is `OneReqStep`, one requirement at a time — and the same
statement is what the reader's own pin needs.

**Part 2 — the cases of one step.** Given a chain through the surviving node
`p` that matches the requirements so far, and the next requirement `r`:

* (a) `p` sits at `r`'s own step — then `p` *is* `r`: the filter left it an
  owner carrying `r` there (`owns_required`), and at its own step a node owns
  only itself (`OOS`). Every chain through `p` matches. **Proved.**
* (b) the chain already carries `r` at its step. **Proved** (nothing to do).
* (c) every global owner at `r`'s step already carries `r` — the step is
  pinned before the filter. Every sound chain lives in the global owners, so it
  matches. **Proved.**
* (d) otherwise the chain carries the *other* value at `r`'s step: a literal
  has to be **flipped**, and the flipped chain has to exist.

**Part 3 — the core.** Case (d) is `FlipCore`, and it is the only thing not
proved. On a 3SAT map it says: if `p` survives, there is a solution of the
clauses seen so far that agrees with `p`, with the requirements so far, and
with the flipped literal. That is a satisfiability question with a handful of
literals fixed, and the machine answers it with a polynomial, local check. It
is where the whole difficulty lives.
-/

namespace AbsSat.GraphPath.Model.ClauseFilter

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.NodeInvariant

-- ============================================================
-- Part 1: one requirement at a time
-- ============================================================

/-- A selection carries the given requirements (those inside the range). -/
def Matches (g : GPathM) (sel : Int → PathNodeId) (S : List NodeId) : Prop :=
  ∀ r ∈ S, 0 ≤ r.step → r.step < g.current_step → (sel r.step).id = r

/-- `p` lies on a sound chain of `g` carrying the requirements `S`. -/
def ChainThrough (g : GPathM) (p : PathNodeId) (S : List NodeId) : Prop :=
  ∃ sel, ChainSound g sel ∧ sel p.id.step = p ∧ Matches g sel S

/-- The per-requirement obligation, for the survivors of one filter. -/
def OneReqStep (g : GPathM) (reqs : List NodeId) : Prop :=
  ∀ p, ((filterAll g reqs).node? p).isSome = true →
    ∀ (S : List NodeId) (r : NodeId), r ∈ reqs →
      ChainThrough g p S → ChainThrough g p (r :: S)

/-- A survivor of the filter is a node of the graph filtered. -/
theorem node_of_survivor (g : GPathM) (reqs : List NodeId) (p : PathNodeId)
    (hp : ((filterAll g reqs).node? p).isSome = true) : ∃ n, g.node? p = some n := by
  obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hp
  have hmem : n' ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hn'
  obtain ⟨n, hn, hid, _, _⟩ := (pruned_filterAll g reqs).nodes_derived n' hmem
  have hs : (g.node? p).isSome = true := by
    rw [← node?_id_eq _ p n' hn', hid]; exact node?_isSome_of_mem g n hn
  exact Option.isSome_iff_exists.mp hs

/-- **Part 1.** One requirement at a time suffices: support before the filter,
plus `OneReqStep`, gives support after it. -/
theorem SupportedS_filterAll_of_OneReqStep (g : GPathM) (reqs : List NodeId)
    (hsup : SupportedS g) (hone : OneReqStep g reqs) : SupportedS (filterAll g reqs) := by
  intro p n' hn'
  have hp : ((filterAll g reqs).node? p).isSome = true := by rw [hn']; rfl
  obtain ⟨n, hn⟩ := node_of_survivor g reqs p hp
  obtain ⟨sel₀, hs₀, ht₀⟩ := hsup p n hn
  -- add the requirements one by one
  have build : ∀ (l : List NodeId), (∀ r ∈ l, r ∈ reqs) → ChainThrough g p l := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨sel₀, hs₀, ht₀, fun _ hr => absurd hr List.not_mem_nil⟩
    | cons r rest ih =>
      intro hl
      exact hone p hp rest r (hl r List.mem_cons_self)
        (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)))
  obtain ⟨sel, hsel, htop, hmatch⟩ := build reqs (fun _ hr => hr)
  exact ⟨sel, ChainSound_filterAll g reqs sel hsel hmatch, htop⟩

/-- info: 'AbsSat.GraphPath.Model.ClauseFilter.SupportedS_filterAll_of_OneReqStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SupportedS_filterAll_of_OneReqStep

-- ============================================================
-- Part 2: the cases of one step
-- ============================================================

variable (reqOf : NodeId → List NodeId)

/-- **Case (a).** A survivor at the requirement's own step *is* the required
node, so every chain through it matches. -/
theorem step_case_self (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true) (p : PathNodeId)
    (hp : ((filterAll g reqs).node? p).isSome = true) (r : NodeId) (hr : r ∈ reqs)
    (hstep : p.id.step = r.step) (hr0 : 0 ≤ r.step) (hr1 : r.step < g.current_step) :
    p.id = r := by
  obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨q, hq, hqr⟩ := owns_required reqOf g reqs hreach hv p n' hn' r hr hr0 hr1
  have hoos : SelfOwn.OOS (filterAll g reqs) :=
    SelfOwn.OOS_of_pruned (pruned_filterAll g reqs) (SelfOwn.OOS_reachable reqOf g hreach)
  have hnid : n'.id = p := node?_id_eq _ p n' hn'
  have hqp : q = n'.id :=
    hoos n' (List.mem_of_find?_eq_some hn') q hq (by rw [hqr, hnid, hstep])
  rw [← hnid, ← hqp, hqr]

/-- **Case (c).** At a step every global owner of which already carries `r`,
every sound chain carries `r`. -/
theorem step_case_pinned (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (r : NodeId) (hpin : ∀ q ∈ g.gowners, q.id.step = r.step → q.id = r)
    (hr0 : 0 ≤ r.step) (hr1 : r.step < g.current_step) : (sel r.step).id = r :=
  hpin (sel r.step) (h.chain.2.2 r.step hr0 hr1) (h.chain.1.1 r.step hr0 hr1).2

/-- **Part 3, the core.** Case (d): the chain carries the other value at the
requirement's step, the survivor is not at that step, and the step is not
pinned. Then a chain with the literal flipped has to exist. -/
def FlipCore (g : GPathM) (reqs : List NodeId) : Prop :=
  ∀ p, ((filterAll g reqs).node? p).isSome = true →
    ∀ (S : List NodeId) (r : NodeId), r ∈ reqs →
      ∀ sel, ChainSound g sel → sel p.id.step = p → Matches g sel S →
        0 ≤ r.step → r.step < g.current_step →
        p.id.step ≠ r.step →
        ¬ (∀ q ∈ g.gowners, q.id.step = r.step → q.id = r) →
        (sel r.step).id ≠ r →
        ChainThrough g p (r :: S)

/-- **Part 2, assembled.** Cases (a), (b), (c) are proved; `FlipCore` is case
(d). Together they give `OneReqStep`. -/
theorem OneReqStep_of_FlipCore (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true) (hcore : FlipCore g reqs) :
    OneReqStep g reqs := by
  intro p hp S r hr ⟨sel, hsel, htop, hmatch⟩
  -- a requirement outside the range constrains nothing
  if hrange : 0 ≤ r.step ∧ r.step < g.current_step then
    obtain ⟨hr0, hr1⟩ := hrange
    have extend : (sel r.step).id = r → ChainThrough g p (r :: S) := by
      intro hsr
      refine ⟨sel, hsel, htop, ?_⟩
      intro x hx hx0 hx1
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hsr
      · exact hmatch x hx hx0 hx1
    -- case (b)
    if hb : (sel r.step).id = r then exact extend hb
    else
      -- case (a)
      if ha : p.id.step = r.step then
        have hpr := step_case_self reqOf g reqs hreach hv p hp r hr ha hr0 hr1
        exact extend (by rw [← ha, htop]; exact hpr)
      else
        -- case (c)
        if hc : ∀ q ∈ g.gowners, q.id.step = r.step → q.id = r then
          exact extend (step_case_pinned g sel hsel r hc hr0 hr1)
        else
          -- case (d): the core
          exact hcore p hp S r hr sel hsel htop hmatch hr0 hr1 ha hc hb
  else
    refine ⟨sel, hsel, htop, ?_⟩
    intro x hx hx0 hx1
    rcases List.mem_cons.mp hx with rfl | hx
    · exact absurd ⟨hx0, hx1⟩ hrange
    · exact hmatch x hx hx0 hx1

/-- info: 'AbsSat.GraphPath.Model.ClauseFilter.OneReqStep_of_FlipCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OneReqStep_of_FlipCore

-- ============================================================
-- Assembly: the clause filter from the core
-- ============================================================

open AbsSat.Cnf AbsSat.GraphMap.CnfMap in
/-- **The clause filter, reduced to its core.** -/
theorem ClauseStepExact_of_FlipCore (φ : Cnf)
    (hcore : ∀ (g : GPathM) (d : NodeId), Reachable (reqOfCnf φ) g →
      d.step = g.current_step → isValid g = true → SupportedS g →
      litBlock φ < d.step → d.step < fusionTop φ →
      isValid (filterAll g (reqOfCnf φ d)) = true → FlipCore g (reqOfCnf φ d)) :
    ClauseStepExact φ := by
  intro g d hr hstep hv hsup hlo hhi hfv
  exact SupportedS_filterAll_of_OneReqStep g _ hsup
    (OneReqStep_of_FlipCore (reqOfCnf φ) g _ hr hfv (hcore g d hr hstep hv hsup hlo hhi hfv))

open AbsSat.Cnf AbsSat.GraphMap.CnfMap in
/-- **And therefore the decision procedure, from the core alone.** -/
theorem decides_of_FlipCore (φ : Cnf) (hwf : WF φ) (hzero : (0 : Int) < stepCount φ)
    (hcore : ∀ (g : GPathM) (d : NodeId), Reachable (reqOfCnf φ) g →
      d.step = g.current_step → isValid g = true → SupportedS g →
      litBlock φ < d.step → d.step < fusionTop φ →
      isValid (filterAll g (reqOfCnf φ d)) = true → FlipCore g (reqOfCnf φ d)) :
    Satisfiable φ ↔ ∃ kv ∈ PureDriver.pureRun φ, isValid kv.2 = true :=
  Decision.decides_of_ClauseStepExact φ hwf hzero (ClauseStepExact_of_FlipCore φ hcore)

/-- info: 'AbsSat.GraphPath.Model.ClauseFilter.decides_of_FlipCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decides_of_FlipCore

end AbsSat.GraphPath.Model.ClauseFilter
