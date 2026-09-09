-- lean_project/AbsSat/GraphPath/Model/Certifies.lean
import AbsSat.GraphPath.Model.PickInduction
import AbsSat.GraphPath.Model.Join

/-!
**The design invariant, stated where it belongs: at construction time.**

The author's own account of the machine, and it corrects the regime the earlier
modules were reasoning in:

> If the machine ends up holding a **valid** set — after the whole step-by-step
> construction, reviews included — it is because there is at least one solution
> certificate the Reader can read. UNSAT is filtered out *before* the Reader:
> the machine simply cannot build a valid set for an unsatisfiable formula. The
> filter the Reader runs is there because selecting a valid node narrows away
> the *other* valid paths — the ones that node is not part of.

Two consequences, and the second is a correction.

1. The obligation is an **invariant of the construction**, not something the
   Reader has to re-establish:

       Reachable reqOf g → isValid g = true → Inhabited g

2. A review that invalidates during **reading** is therefore *not* an UNSAT
   verdict — it is an invariant violation. UNSAT is decided by `upFiltering`
   while the graph is being built. `PickInduction`'s docstring for
   `not_isValid_removeNode_of_only` read those two regimes as one; the boundary
   it marks is real, but it belongs to the construction, not to the read.

## The ledger

`Certifies_of_upStep` below does the induction over `Reachable`:

| case | status |
|---|---|
| `seed` | **proved** — `initSeed` holds one node, and it is its own chain |
| `join` | **proved** — `okJoin` already demands both sides valid, and join only grows |
| `up` | the obligation |

So the whole of the author's claim rests on one step: *a valid graph obtained by
`upFiltering` from a valid, certified graph is itself certified.* That is the
same wall as before — but it is now the only entry in the ledger, and it is
stated at the point where the machine actually decides UNSAT.
-/

namespace AbsSat.GraphPath.Model.Certifies

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PickInduction (isValid_of_gowner gowner_of_isValid)

-- ============================================================
-- Validity only ever moves downwards
-- ============================================================

/-- Pruning cannot make an invalid graph valid: it only removes global owners.
Contrapositive of the obvious, and what lets the induction below use its
hypothesis. -/
theorem isValid_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : isValid g' = true) :
    isValid g = true := by
  refine isValid_of_gowner _ ?_
  intro k hlo hhi
  obtain ⟨q, hq, hstep⟩ := gowner_of_isValid g' h k hlo (by rw [hpr.step_eq]; exact hhi)
  exact ⟨q, hpr.gowners_sub q hq, hstep⟩

theorem isValid_of_filterAll (g : GPathM) (reqs : List NodeId)
    (h : isValid (filterAll g reqs) = true) : isValid g = true :=
  isValid_of_pruned (pruned_filterAll g reqs) h

/-- A valid `upFiltering` result can only have come from a valid graph: if the
filter had invalidated it, `up` would have handed the invalid graph straight
back. -/
theorem isValid_of_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId)
    (title : String) (h : isValid (upFiltering g reqs d title) = true) :
    isValid g = true := by
  refine isValid_of_filterAll g reqs ?_
  unfold GPathM.upFiltering GPathM.up at h
  cases hv : isValid (filterAll g reqs) with
  | true => rfl
  | false => rw [if_neg (by rw [hv]; exact Bool.false_ne_true)] at h; exact absurd h (by rw [hv]; exact Bool.false_ne_true)

-- ============================================================
-- The seed case
-- ============================================================

theorem node?_initSeed (d : NodeId) (title : String) :
    (GPathM.initSeed d title).node? { id := d, parent_id := none } =
      some (PNodeM.mk { id := d, parent_id := none } title [] []
              [{ id := d, parent_id := none }]) := by
  show List.find? _ (GPathM.initSeed d title).nodes = _
  rw [initSeed_nodes]
  exact List.find?_cons_of_pos (beq_iff_eq.mpr rfl)

/-- **Seed case.** The seed holds exactly one node, and that node is its own
complete co-owned chain. -/
theorem Inhabited_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    AbsSat.GraphPath.Model.Inhabited (GPathM.initSeed d title) :=
  Verdict.Inhabited_of_Supported _ _ _ (node?_initSeed d title)
    (Supported_initSeed d title hstep)

-- ============================================================
-- The join case
-- ============================================================

theorem isValid_left_of_okJoin {g₁ g₂ : GPathM} (h : okJoin g₁ g₂ = true) :
    isValid g₁ = true := by
  unfold GPathM.okJoin at h
  exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2

/-- **Join case.** `okJoin` already demands both sides valid — which is what
makes the induction hypothesis usable on the left branch — and join only grows
the graph, so the left side's certificate is a certificate of the join. Growth
alone carries it, so `okJoin` is not needed here, only at the call site. -/
theorem Inhabited_join (g₁ g₂ : GPathM)
    (h₁ : AbsSat.GraphPath.Model.Inhabited g₁) :
    AbsSat.GraphPath.Model.Inhabited (join g₁ g₂) := by
  obtain ⟨p, hp⟩ := h₁
  exact ⟨p, denot_join_of_left g₁ g₂ p hp⟩

-- ============================================================
-- The invariant, and what is left of it
-- ============================================================

variable (reqOf : NodeId → List NodeId)

/-- **The author's claim, formally.** A valid graph the machine has actually
built carries at least one certificate. -/
def Certifies : Prop :=
  ∀ g, Reachable reqOf g → isValid g = true → AbsSat.GraphPath.Model.Inhabited g

/-- **The one step it rests on.** A valid graph reached by `upFiltering` from a
valid, certified graph is itself certified. -/
def UpCertifies : Prop :=
  ∀ (g : GPathM) (d : NodeId) (title : String), Reachable reqOf g → isValid g = true →
    AbsSat.GraphPath.Model.Inhabited g →
    isValid (GPathM.upFiltering g (reqOf d) d title) = true →
    AbsSat.GraphPath.Model.Inhabited (GPathM.upFiltering g (reqOf d) d title)

/-- **The ledger, closed except for `up`.** Seed and join are discharged; the
construction invariant reduces to the single `up` step. -/
theorem Certifies_of_upStep (hup : UpCertifies reqOf) : Certifies reqOf := by
  intro g hreach
  induction hreach with
  | seed d title hstep _ => intro _; exact Inhabited_initSeed d title hstep
  | up g d title _ _ _ hr ih =>
    intro hv
    have hgv : isValid g = true := isValid_of_upFiltering g (reqOf d) d title hv
    exact hup g d title hr hgv (ih hgv) hv
  | join g₁ g₂ hok _ _ ih₁ _ =>
    intro _
    exact Inhabited_join g₁ g₂ (ih₁ (isValid_left_of_okJoin hok))

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.Certifies.Inhabited_initSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_initSeed

/-- info: 'AbsSat.GraphPath.Model.Certifies.Inhabited_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_join

/-- info: 'AbsSat.GraphPath.Model.Certifies.Certifies_of_upStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Certifies_of_upStep

end AbsSat.GraphPath.Model.Certifies
