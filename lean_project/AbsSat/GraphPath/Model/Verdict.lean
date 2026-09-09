-- lean_project/AbsSat/GraphPath/Model/Verdict.lean
import AbsSat.GraphPath.Model.Certificate

/-!
**Route D — splitting L6 into the half the verdict needs and the half it does
not.**

`L6.lean` states two properties and treats them as one lemma:

* `Supported g` — *every* node lies on a complete co-owned chain ("no
  zombies");
* `Inhabited g` — the graph denotes *something*.

They are not equally hard and they do not buy the same thing.

## What each one buys

| | consumed by |
|---|---|
| `Inhabited g` | the **SAT/UNSAT verdict**: a surviving graph means a solution exists |
| `Supported g` | the **reader**: every reading step must succeed, because it cannot retry |

**The reader does not backtrack.** `Reader/PathReader.lean` picks *any*
surviving node at the current step (`ids.toList.head?`), filters by it, and if
that filter invalidates the graph it sets `error` and stops — it never tries
another node. `Reader/PathExpReader.lean` forks per candidate, and **one
errored fork aborts the whole enumeration**. The Julia original throws
`GRAVE ERROR READER... GPATH INVALID` there, and its own comment states the
design invariant: *every surviving node is extendable to a full solution*.

So a zombie is not a slowdown. It is a **hard stop**, and in the exponential
reader a single one destroys the entire solution set rather than one path.
`Supported` is therefore a **correctness precondition of the reader** —
completeness of the enumeration — not a performance property.

What is *not* affected is the verdict: `DiffTest.run_case` takes SAT/UNSAT from
`have_solution` (the graph's own validity), not from the reader. So `Inhabited`
really is what the verdict consumes, and the localization below stands.

**And the reader needs slightly more than `Supported` at one graph.** Because
it re-filters after every selection, what it needs is `Supported` *preserved by
that filter* — `ReadStable` below. That is the same statement the bridge is
already stuck on ("filtering never kills a chain through a surviving node"), so
the reader's requirement and L6's open case are one obligation, not two.

A zombie still cannot make the machine *invent* a solution: `denot` is defined
as the set of complete co-owned chains, so a node on none of them contributes
nothing — `denot_has_no_zombies` below. Soundness of what is read survives a
zombie; completeness of the reading does not.

## The localization

The main result here is that `Inhabited` is **L6 at a single node**:

    Inhabited g  ↔  ∃ pid, (g.node? pid).isSome ∧ SupportedAt g pid   (0 < current_step)

`Supported` quantifies that same `SupportedAt` over *all* nodes. So the open
problem does not have to be solved in general to get the verdict — it has to
be solved *once*, at one node of your choosing. That is a strictly weaker
obligation, and it admits attacks the universal statement does not: you get to
pick the node (say, one at the top step, or the one with the smallest owner
sets), whereas `Supported` must survive an adversary picking it for you.

## And it is certifiable more cheaply

Combined with route C (`Certificate.lean`), the practical consequence is a
sharp difference in cost. Certifying `Supported` costs one certificate per
node; certifying `Inhabited` costs **one certificate, full stop**
(`Certificate.Inhabited_of_isCert`). A run that cannot afford the first can
still afford the second.

## What is still missing after this

Nothing here connects `denot` to satisfying assignments of the original CNF.
That link — "every chain decodes to a model of the formula" — is a separate
obligation, and it lives on the map side (`GraphMap.MapReqs`, and phase L7).
`Inhabited` gives you *a chain*; turning that into *a solution* is the other
half of the verdict claim and is not proved here.
-/

namespace AbsSat.GraphPath.Model.Verdict

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- L6, one node at a time
-- ============================================================

/-- **L6 at a single node**: `pid` lies on a complete co-owned chain. -/
def SupportedAt (g : GPathM) (pid : PathNodeId) : Prop :=
  ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ sel pid.id.step = pid

/-- `Supported` is exactly `SupportedAt` quantified over every node. -/
theorem Supported_iff (g : GPathM) :
    Supported g ↔ ∀ pid, (g.node? pid).isSome → SupportedAt g pid := by
  constructor
  · intro h pid hs
    exact h pid ((g.node? pid).get hs) (Option.some_get hs).symm
  · intro h pid n hn
    exact h pid (by rw [hn]; rfl)

-- ============================================================
-- The localization: `Inhabited` is L6 at *one* node
-- ============================================================

/-- One supported node is enough to make the graph denote something. -/
theorem Inhabited_of_SupportedAt (g : GPathM) (pid : PathNodeId)
    (h : SupportedAt g pid) : AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨sel, hchain, howned, _⟩ := h
  exact ⟨pathOf sel g, sel, hchain, howned, rfl⟩

/-- And conversely: a graph that denotes something has a supported node —
namely the one its chain picks at step 0. -/
theorem SupportedAt_of_Inhabited (g : GPathM) (hpos : 0 < g.current_step)
    (h : AbsSat.GraphPath.Model.Inhabited g) :
    ∃ pid, (g.node? pid).isSome ∧ SupportedAt g pid := by
  obtain ⟨_, sel, hchain, howned, _⟩ := h
  obtain ⟨hsome, hstep⟩ := hchain.1 0 (Int.le_refl 0) hpos
  refine ⟨sel 0, hsome, sel, hchain, howned, ?_⟩
  rw [hstep]

/-- **The split, as an equivalence.** The verdict half of L6 is the universal
half restricted to a single node. -/
theorem Inhabited_iff_SupportedAt (g : GPathM) (hpos : 0 < g.current_step) :
    AbsSat.GraphPath.Model.Inhabited g ↔ ∃ pid, (g.node? pid).isSome ∧ SupportedAt g pid :=
  ⟨SupportedAt_of_Inhabited g hpos, fun ⟨pid, _, h⟩ => Inhabited_of_SupportedAt g pid h⟩

/-- The easy direction of the split: the hard half implies the easy one, as
soon as there is any node at all. -/
theorem Inhabited_of_Supported (g : GPathM) (pid : PathNodeId) (n : PNodeM)
    (hn : g.node? pid = some n) (h : Supported g) :
    AbsSat.GraphPath.Model.Inhabited g :=
  Inhabited_of_SupportedAt g pid (h pid n hn)

-- ============================================================
-- What a non-backtracking reader actually needs
-- ============================================================

/-- **The reader's real obligation.** After each selection the reader filters
by the chosen map node and demands the graph stay valid; it has no way to try
another. So it needs `Supported` to be an *invariant of that filter*, not just
to hold of the graph it starts from.

Stated, not proved — and deliberately: this is the same statement as L6's open
`up` case and L2's ⊇ direction. Recording it here makes explicit that the
reader's correctness and the bridge's remaining gap are one obligation. -/
def ReadStable (g : GPathM) : Prop :=
  ∀ mid : NodeId, (∃ n ∈ g.nodes, n.id.id = mid) →
    isValid (filterAll g [mid]) = true ∧ Supported (filterAll g [mid])

/-- `ReadStable` is at least as strong as validity being preserved, which is
exactly the condition the mirror reader tests before continuing
(`MirrorTest.readWork`). -/
theorem readStep_valid_of_ReadStable (g : GPathM) (mid : NodeId)
    (hmem : ∃ n ∈ g.nodes, n.id.id = mid) (h : ReadStable g) :
    isValid (filterAll g [mid]) = true := (h mid hmem).1

-- ============================================================
-- Why a zombie cannot make the answer wrong
-- ============================================================

/-- **Zombies do not pollute the denotation.** Anything `denot` produces comes
from a genuine complete co-owned chain, whether or not other nodes lie on one.
True by definition — and that is the content: a failure of `Supported` is a
failure of *efficiency*, not of *soundness*. -/
theorem denot_has_no_zombies (g : GPathM) (p : List NodeId) (h : denot g p) :
    ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ p = pathOf sel g := h

/-- A node on no chain contributes nothing: it never appears in any path the
denotation contains, at its own step or anywhere else. -/
theorem not_in_denot_of_not_SupportedAt (g : GPathM) (pid : PathNodeId)
    (h : ¬ SupportedAt g pid) :
    ∀ sel, IsChain g sel → PairwiseOwned g sel → sel pid.id.step ≠ pid := by
  intro sel hchain howned hEq
  exact h ⟨sel, hchain, howned, hEq⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.Verdict.Inhabited_iff_SupportedAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inhabited_iff_SupportedAt

/-- info: 'AbsSat.GraphPath.Model.Verdict.Supported_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms Supported_iff

/-- info: 'AbsSat.GraphPath.Model.Verdict.not_in_denot_of_not_SupportedAt' does not depend on any axioms -/
#guard_msgs in
#print axioms not_in_denot_of_not_SupportedAt

end AbsSat.GraphPath.Model.Verdict
