-- lean_project/AbsSat/GraphPath/Model/Certifies.lean
import AbsSat.GraphPath.Model.PickInduction
import AbsSat.GraphPath.Model.Join
import AbsSat.GraphPath.Model.JoinSound
import AbsSat.GraphPath.Model.AddNode
import AbsSat.GraphPath.Model.OwnersInvariants
import AbsSat.GraphPath.Model.ArcConsistency

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

/-- The filtered graph is where a valid `upFiltering` gets its validity from. -/
theorem isValid_of_filterAll_of_upFiltering (g : GPathM) (reqs : List NodeId)
    (d : NodeId) (title : String) (h : isValid (upFiltering g reqs d title) = true) :
    isValid (filterAll g reqs) = true := by
  unfold GPathM.upFiltering GPathM.up at h
  cases hv : isValid (filterAll g reqs) with
  | true => rfl
  | false =>
    rw [if_neg (by rw [hv]; exact Bool.false_ne_true)] at h
    exact absurd h (by rw [hv]; exact Bool.false_ne_true)

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

-- ============================================================
-- The same ledger in `ChainSound` currency — where the machinery lives
-- ============================================================

/-!
`Certifies_of_upStep` leaves one obligation, but stated in `Inhabited`
currency it cannot use anything already proved about `upFiltering`: the
existing results (`ChainSound_addNode`, `ChainSound_filterAll`,
`ChainSound_upFiltering`) are all about `ChainSound` chains. Restating the
invariant in that currency lets them all be plugged in, and the obligation
shrinks to exactly what none of them supplies.
-/

/-- The construction invariant, with `ChainSound` witnesses. -/
def CertifiesS : Prop :=
  ∀ g, Reachable reqOf g → isValid g = true → ∃ sel, ChainSound g sel

theorem Inhabited_of_ChainSound (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : AbsSat.GraphPath.Model.Inhabited g :=
  ⟨pathOf sel g, sel, h.chain.1, h.chain.2.1, rfl⟩

theorem Certifies_of_CertifiesS (h : CertifiesS reqOf) : Certifies reqOf := by
  intro g hr hv
  obtain ⟨sel, hsel⟩ := h g hr hv
  exact Inhabited_of_ChainSound g sel hsel

-- ============================================================
-- The structural side conditions `ChainSound_upFiltering` asks for
-- ============================================================

theorem MachineOk_join (g₁ g₂ : GPathM) (h : MachineOk g₁) : MachineOk (join g₁ g₂) := h

theorem MachineOk_initSeed (d : NodeId) (title : String) :
    MachineOk (GPathM.initSeed d title) := by
  unfold GPathM.initSeed GPathM.up
  rw [if_pos (by rfl : isValid empty = true)]
  exact MachineOk_addNode empty d title MachineOk_empty

theorem MachineOk_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId)
    (title : String) (h : MachineOk g) : MachineOk (upFiltering g reqs d title) := by
  have hf : MachineOk (filterAll g reqs) := MachineOk_of_pruned (pruned_filterAll g reqs) h
  unfold GPathM.upFiltering GPathM.up
  cases hv : isValid (filterAll g reqs) with
  | true => rw [if_pos rfl]; exact MachineOk_addNode _ d title hf
  | false => rw [if_neg Bool.false_ne_true]; exact hf

/-- Every state the machine builds has the shape `addNode` needs. -/
theorem MachineOk_reachable (g : GPathM) (h : Reachable reqOf g) : MachineOk g := by
  induction h with
  | seed d title _ _ => exact MachineOk_initSeed d title
  | up g d title _ _ _ _ ih => exact MachineOk_upFiltering g (reqOf d) d title ih
  | join g₁ g₂ _ _ _ ih₁ _ => exact MachineOk_join g₁ g₂ ih₁

/-- Nodes stay below the current step across a pruning. -/
theorem nodes_below_of_pruned {g g' : GPathM} (hpr : Pruned g g')
    (h : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) :
    ∀ n ∈ g'.nodes, n.id.id.step < g'.current_step := by
  intro n hn
  obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived n hn
  rw [hpr.step_eq, hid]
  exact h m hm

-- ============================================================
-- What the `up` case actually still owes
-- ============================================================

/-- **The obligation, at its smallest.** If the machine holds a valid,
certified graph and the filter for the next node leaves it valid, then the
graph has a sound chain that *satisfies those requirements*.

This is all `ChainSound_upFiltering` is missing. It says nothing about
`addNode`, nothing about the review passes, nothing about the new node: only
that the validity the machine checks after filtering is witnessed by an actual
chain through the required nodes. -/
def ReqChain : Prop :=
  ∀ (g : GPathM) (d : NodeId), Reachable reqOf g → isValid g = true →
    (∃ sel, ChainSound g sel) →
    isValid (filterAll g (reqOf d)) = true →
    ∃ sel, ChainSound g sel ∧
      ∀ req ∈ reqOf d, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req

/-- **The ledger, closed down to `ReqChain`.** `seed` is `ChainSound_initSeed`,
`join` is `ChainSound_join_left`, and `up` is `ChainSound_upFiltering` once
`ReqChain` supplies the chain it needs. -/
theorem CertifiesS_of_ReqChain (h : ReqChain reqOf) : CertifiesS reqOf := by
  intro g hreach
  induction hreach with
  | seed d title hstep _ =>
    intro _; exact ⟨_, ChainSound_initSeed d title hstep⟩
  | up g d title hstep _ _ hr ih =>
    intro hv
    have hgv : isValid g = true := isValid_of_upFiltering g (reqOf d) d title hv
    have hfv : isValid (filterAll g (reqOf d)) = true :=
      isValid_of_filterAll_of_upFiltering g (reqOf d) d title hv
    obtain ⟨sel, hsel, hreqs⟩ := h g d hr hgv (ih hgv) hfv
    refine ⟨_, ChainSound_upFiltering g (reqOf d) d title hfv ?_ ?_ ?_ sel hsel hreqs⟩
    · rw [(pruned_filterAll g (reqOf d)).step_eq]; exact hstep
    · exact nodes_below_of_pruned (pruned_filterAll g (reqOf d))
        (steps_below_current reqOf hr)
    · exact MachineOk_of_pruned (pruned_filterAll g (reqOf d))
        (MachineOk_reachable reqOf g hr)
  | join g₁ g₂ hok _ _ ih₁ _ =>
    intro _
    obtain ⟨sel, hsel⟩ := ih₁ (isValid_left_of_okJoin hok)
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel⟩

/-- And therefore the author's claim, in `Inhabited` currency. -/
theorem Certifies_of_ReqChain (h : ReqChain reqOf) : Certifies reqOf :=
  Certifies_of_CertifiesS reqOf (CertifiesS_of_ReqChain reqOf h)

/-- info: 'AbsSat.GraphPath.Model.Certifies.CertifiesS_of_ReqChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiesS_of_ReqChain

/-- info: 'AbsSat.GraphPath.Model.Certifies.MachineOk_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MachineOk_reachable

-- ============================================================
-- Asking for less: the chain is needed in the *filtered* graph
-- ============================================================

/-!
`ReqChain` asks for a sound chain of `g` that satisfies the requirements. But
tracing what `ChainSound_upFiltering` does with it, that chain is immediately
pushed through `ChainSound_filterAll` — the only thing ever used is the
resulting chain of `filterAll g reqs`. So the obligation can be stated one
step later, and asking for it there is **strictly weaker**: `ReqChain` implies
it (that is `ReqChain_gives_FilteredChain`), and the converse would need a
`ChainSound` transfer backwards across a pruning, which nothing supplies.
-/

/-- `ChainSound_upFiltering` with the chain taken where it is actually used. -/
theorem ChainSound_upFiltering_of_filtered (g : GPathM) (reqs : List NodeId)
    (d : NodeId) (title : String)
    (hvalid : isValid (filterAll g reqs) = true)
    (hd : d.step = (filterAll g reqs).current_step)
    (hbelow : ∀ n ∈ (filterAll g reqs).nodes,
      n.id.id.step < (filterAll g reqs).current_step)
    (hmok : MachineOk (filterAll g reqs))
    (sel : Int → PathNodeId) (h : ChainSound (filterAll g reqs) sel) :
    ChainSound (upFiltering g reqs d title) (extend (filterAll g reqs) d sel) := by
  have hshape : upFiltering g reqs d title = addNode (filterAll g reqs) d title := by
    simp only [upFiltering, up, hvalid, if_pos]
  rw [hshape]
  exact ChainSound_addNode _ d title hd hbelow hmok sel h

/-- **The obligation, one step later and strictly weaker.** -/
def FilteredChain : Prop :=
  ∀ (g : GPathM) (d : NodeId), Reachable reqOf g → isValid g = true →
    (∃ sel, ChainSound g sel) →
    isValid (filterAll g (reqOf d)) = true →
    ∃ sel, ChainSound (filterAll g (reqOf d)) sel

theorem ReqChain_gives_FilteredChain (h : ReqChain reqOf) : FilteredChain reqOf := by
  intro g d hr hv hex hfv
  obtain ⟨sel, hsel, hreqs⟩ := h g d hr hv hex hfv
  exact ⟨sel, ChainSound_filterAll g (reqOf d) sel hsel hreqs⟩

/-- **The ledger, closed down to `FilteredChain`.** -/
theorem CertifiesS_of_FilteredChain (h : FilteredChain reqOf) : CertifiesS reqOf := by
  intro g hreach
  induction hreach with
  | seed d title hstep _ =>
    intro _; exact ⟨_, ChainSound_initSeed d title hstep⟩
  | up g d title hstep _ _ hr ih =>
    intro hv
    have hgv : isValid g = true := isValid_of_upFiltering g (reqOf d) d title hv
    have hfv : isValid (filterAll g (reqOf d)) = true :=
      isValid_of_filterAll_of_upFiltering g (reqOf d) d title hv
    obtain ⟨sel, hsel⟩ := h g d hr hgv (ih hgv) hfv
    refine ⟨_, ChainSound_upFiltering_of_filtered g (reqOf d) d title hfv ?_ ?_ ?_ sel hsel⟩
    · rw [(pruned_filterAll g (reqOf d)).step_eq]; exact hstep
    · exact nodes_below_of_pruned (pruned_filterAll g (reqOf d))
        (steps_below_current reqOf hr)
    · exact MachineOk_of_pruned (pruned_filterAll g (reqOf d))
        (MachineOk_reachable reqOf g hr)
  | join g₁ g₂ hok _ _ ih₁ _ =>
    intro _
    obtain ⟨sel, hsel⟩ := ih₁ (isValid_left_of_okJoin hok)
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel⟩

theorem Certifies_of_FilteredChain (h : FilteredChain reqOf) : Certifies reqOf :=
  Certifies_of_CertifiesS reqOf (CertifiesS_of_FilteredChain reqOf h)

-- ============================================================
-- The one statement everything has collapsed to
-- ============================================================

/-- **`ValidHasChain`** — a valid graph carries a sound chain.

Every obligation this project has chased is this statement about a different
graph: `Supported`, `Extendable`, `PickValid`, `UpCertifies`, `ReqChain`,
`FilteredChain`. Stated once, it is what the machine's whole claim rests on.

And `FilteredChain` needs it on a **narrower class than any of the others**:
only on graphs of the form `filterAll g reqs`, which are `review` fixpoints
(`review_idempotent`). That matters, because the fixpoint is exactly where the
arc-consistency facts hold — `review_node_valid`, `review_owners_within_gowners`,
`review_owners_coherent_parents` / `_sons` in `Fuel.lean`. So the final
obligation is, in one line:

> a valid, arc-consistent `review` fixpoint carries a complete co-owned chain. -/
def ValidHasChain (h : GPathM) : Prop := isValid h = true → ∃ sel, ChainSound h sel

theorem FilteredChain_of_ValidHasChain
    (h : ∀ (g : GPathM) (d : NodeId), Reachable reqOf g →
      ValidHasChain (filterAll g (reqOf d))) : FilteredChain reqOf :=
  fun g d hr _ _ hfv => h g d hr hfv

/-- The filtered graph really is a `review` fixpoint, so the obligation only
ever has to be met there. -/
theorem filterAll_is_review_fixpoint (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) :
    review (filterAll g reqs) = filterAll g reqs :=
  review_idempotent _ hv

theorem Certifies_of_ValidHasChain
    (h : ∀ (g : GPathM) (d : NodeId), Reachable reqOf g →
      ValidHasChain (filterAll g (reqOf d))) : Certifies reqOf :=
  Certifies_of_FilteredChain reqOf (FilteredChain_of_ValidHasChain reqOf h)

/-- info: 'AbsSat.GraphPath.Model.Certifies.CertifiesS_of_FilteredChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiesS_of_FilteredChain

/-- info: 'AbsSat.GraphPath.Model.Certifies.Certifies_of_ValidHasChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Certifies_of_ValidHasChain

-- ============================================================
-- The obligation, in the classical CSP currency
-- ============================================================

/-- `review_arcConsistent` needs `Reachable` only to reach `ReqFiltered` through
lemma L1. The filtered intermediates are not themselves reachable, so this is
the same construction with that hypothesis taken directly. -/
theorem arcConsistent_of_ReqFiltered (g : GPathM) (h : isValid (review g) = true)
    (hrf : ReqFiltered reqOf (review g)) : ArcConsistent reqOf (review g) where
  supported := review_arcSupported g h
  pinned := hrf
  coherent_parents := fun k hk id hid d hd =>
    review_owners_coherent_parents g h k hk id hid d hd
  coherent_sons := fun k hk id hid d hd =>
    review_owners_coherent_sons g h k hk id hid d hd

/-- **Every graph the obligation is about is arc consistent.** The filtered
intermediates inherit `ReqFiltered` from `g` (lemma L1 plus
`filterAll_preserves_ReqFiltered`), and the review fixpoint supplies the rest. -/
theorem arcConsistent_filterAll (g : GPathM) (reqs : List NodeId)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true) :
    ArcConsistent reqOf (filterAll g reqs) :=
  arcConsistent_of_ReqFiltered reqOf _ hv
    (filterAll_preserves_ReqFiltered reqOf (L1 reqOf hreach) reqs)

/-- **The whole claim, with every machine-specific hypothesis discharged.**

    a valid, arc-consistent `review` fixpoint carries a complete co-owned chain

Nothing about `addNode`, the fuel loop, `join`, the seed, `MachineOk`, node
ranges, or `Reachable` is left in it — all of that is proved. What remains is
the classical CSP statement, for the constraint network the map generates:
local consistency implies a global solution.

Which is false for arbitrary networks, and is the reason the whole project
comes down to the *class* of networks `ImportCnf` builds — where
`GraphMap.MapReqs.Functional` says every requirement set is 0/1/all. -/
def ArcImpliesChain : Prop :=
  ∀ h : GPathM, ArcConsistent reqOf h → isValid h = true → review h = h →
    ∃ sel, ChainSound h sel

theorem Certifies_of_ArcImpliesChain (h : ArcImpliesChain reqOf) : Certifies reqOf :=
  Certifies_of_ValidHasChain reqOf (fun g d hr hv =>
    h _ (arcConsistent_filterAll reqOf g (reqOf d) hr hv) hv
      (filterAll_is_review_fixpoint g (reqOf d) hv))

/-- info: 'AbsSat.GraphPath.Model.Certifies.arcConsistent_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arcConsistent_filterAll

/-- info: 'AbsSat.GraphPath.Model.Certifies.Certifies_of_ArcImpliesChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Certifies_of_ArcImpliesChain

end AbsSat.GraphPath.Model.Certifies
