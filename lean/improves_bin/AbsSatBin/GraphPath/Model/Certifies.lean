-- lean/improves_bin/AbsSatBin/GraphPath/Model/Certifies.lean
import AbsSatBin.GraphPath.Model.PickInduction
import AbsSatBin.GraphPath.Model.Join
import AbsSatBin.GraphPath.Model.JoinSound
import AbsSatBin.GraphPath.Model.AddNode
import AbsSatBin.GraphPath.Model.OwnersInvariants
import AbsSatBin.GraphPath.Model.ArcConsistency

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

       Reachable reqOf forb g → isValid g = true → Inhabited g

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

namespace AbsSatBin.GraphPath.Model.Certifies

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PickInduction (isValid_of_gowner gowner_of_isValid)

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
    (title : String) (forb : PathNodeId → Bool) (h : isValid (upFiltering g reqs d title forb) = true) :
    isValid g = true := by
  refine isValid_of_filterAll g reqs ?_
  unfold GPathM.upFiltering GPathM.up at h
  cases hv : isValid (filterAll g reqs) with
  | true => rfl
  | false => rw [if_neg (by rw [hv]; exact Bool.false_ne_true)] at h; exact absurd h (by rw [hv]; exact Bool.false_ne_true)

/-- The filtered graph is where a valid `upFiltering` gets its validity from. -/
theorem isValid_of_filterAll_of_upFiltering (g : GPathM) (reqs : List NodeId)
    (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (h : isValid (upFiltering g reqs d title forb) = true) :
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
    AbsSatBin.GraphPath.Model.Inhabited (GPathM.initSeed d title) :=
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
    (h₁ : AbsSatBin.GraphPath.Model.Inhabited g₁) :
    AbsSatBin.GraphPath.Model.Inhabited (join g₁ g₂) := by
  obtain ⟨p, hp⟩ := h₁
  exact ⟨p, denot_join_of_left g₁ g₂ p hp⟩

-- ============================================================
-- The invariant, and what is left of it
-- ============================================================

variable (reqOf : NodeId → List NodeId) (forb : PathNodeId → Bool)

/-- **The author's claim, formally.** A valid graph the machine has actually
built carries at least one certificate. -/
def Certifies : Prop :=
  ∀ g, Reachable reqOf forb g → isValid g = true → AbsSatBin.GraphPath.Model.Inhabited g

/-- **The one step it rests on.** A valid graph reached by `upFiltering` from a
valid, certified graph is itself certified. -/
def UpCertifies : Prop :=
  ∀ (g : GPathM) (d : NodeId) (title : String), Reachable reqOf forb g → isValid g = true →
    AbsSatBin.GraphPath.Model.Inhabited g →
    isValid (GPathM.upFiltering g (reqOf d) d title forb) = true →
    AbsSatBin.GraphPath.Model.Inhabited (GPathM.upFiltering g (reqOf d) d title forb)

/-- **The ledger, closed except for `up`.** Seed and join are discharged; the
construction invariant reduces to the single `up` step. -/
theorem Certifies_of_upStep (hup : UpCertifies reqOf forb) : Certifies reqOf forb := by
  intro g hreach
  induction hreach with
  | seed d title hstep _ => intro _; exact Inhabited_initSeed d title hstep
  | up g d title _ _ _ hr ih =>
    intro hv
    have hgv : isValid g = true := isValid_of_upFiltering g (reqOf d) d title forb hv
    exact hup g d title hr hgv (ih hgv) hv
  | join g₁ g₂ hok _ _ ih₁ _ =>
    intro _
    exact Inhabited_join g₁ g₂ (ih₁ (isValid_left_of_okJoin hok))

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.Inhabited_initSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_initSeed

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.Inhabited_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_join

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.Certifies_of_upStep' depends on axioms: [propext, Quot.sound] -/
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
  ∀ g, Reachable reqOf forb g → isValid g = true → ∃ sel, ChainSound g sel

theorem Inhabited_of_ChainSound (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : AbsSatBin.GraphPath.Model.Inhabited g :=
  ⟨pathOf sel g, sel, h.chain.1, h.chain.2.1, rfl⟩

theorem Certifies_of_CertifiesS (h : CertifiesS reqOf forb) : Certifies reqOf forb := by
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
  rw [if_pos (by rfl : isValid empty = true), skipsWindow_noForb]
  exact MachineOk_addNode empty d title noForb MachineOk_empty

theorem MachineOk_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId)
    (title : String) (forb : PathNodeId → Bool) (h : MachineOk g) :
    MachineOk (upFiltering g reqs d title forb) := by
  have hf : MachineOk (filterAll g reqs) := MachineOk_of_pruned (pruned_filterAll g reqs) h
  have hadd := MachineOk_addNode _ d title forb hf
  unfold GPathM.upFiltering GPathM.up
  cases hv : isValid (filterAll g reqs) with
  | true =>
    rw [if_pos rfl]
    split
    · exact MachineOk_of_pruned (pruned_review _) hadd
    · exact hadd
  | false => rw [if_neg Bool.false_ne_true]; exact hf

/-- Every state the machine builds has the shape `addNode` needs. -/
theorem MachineOk_reachable (g : GPathM) (h : Reachable reqOf forb g) : MachineOk g := by
  induction h with
  | seed d title _ _ => exact MachineOk_initSeed d title
  | up g d title _ _ _ _ ih => exact MachineOk_upFiltering g (reqOf d) d title forb ih
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
chain through the required nodes.

**Bin map:** and whose extension into the new row is not a prohibited window. Without that
conjunct the obligation would be false on the bin map: a chain can satisfy every requirement of
`L3 = 0` and still run into `(L1=0, L2=0, L3=0)`. -/
def ReqChain : Prop :=
  ∀ (g : GPathM) (d : NodeId), Reachable reqOf forb g → isValid g = true →
    (∃ sel, ChainSound g sel) →
    isValid (filterAll g (reqOf d)) = true →
    ∃ sel, ChainSound g sel ∧
      (∀ req ∈ reqOf d, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) ∧
      forb (extendPid (filterAll g (reqOf d)) d sel) = false

/-- **The ledger, closed down to `ReqChain`.** `seed` is `ChainSound_initSeed`,
`join` is `ChainSound_join_left`, and `up` is `ChainSound_upFiltering` once
`ReqChain` supplies the chain it needs. -/
theorem CertifiesS_of_ReqChain (h : ReqChain reqOf forb) : CertifiesS reqOf forb := by
  intro g hreach
  induction hreach with
  | seed d title hstep _ =>
    intro _; exact ⟨_, ChainSound_initSeed d title hstep⟩
  | up g d title hstep _ _ hr ih =>
    intro hv
    have hgv : isValid g = true := isValid_of_upFiltering g (reqOf d) d title forb hv
    have hfv : isValid (filterAll g (reqOf d)) = true :=
      isValid_of_filterAll_of_upFiltering g (reqOf d) d title forb hv
    obtain ⟨sel, hsel, hreqs, hf⟩ := h g d hr hgv (ih hgv) hfv
    refine ⟨_, ChainSound_upFiltering g (reqOf d) d title forb hfv ?_ ?_ ?_ sel hsel hreqs hf⟩
    · rw [(pruned_filterAll g (reqOf d)).step_eq]; exact hstep
    · exact nodes_below_of_pruned (pruned_filterAll g (reqOf d))
        (steps_below_current reqOf forb hr)
    · exact MachineOk_of_pruned (pruned_filterAll g (reqOf d))
        (MachineOk_reachable reqOf forb g hr)
  | join g₁ g₂ hok _ _ ih₁ _ =>
    intro _
    obtain ⟨sel, hsel⟩ := ih₁ (isValid_left_of_okJoin hok)
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel⟩

/-- And therefore the author's claim, in `Inhabited` currency. -/
theorem Certifies_of_ReqChain (h : ReqChain reqOf forb) : Certifies reqOf forb :=
  Certifies_of_CertifiesS reqOf forb (CertifiesS_of_ReqChain reqOf forb h)

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.CertifiesS_of_ReqChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiesS_of_ReqChain

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.MachineOk_reachable' depends on axioms: [propext, Quot.sound] -/
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
    (sel : Int → PathNodeId) (h : ChainSound (filterAll g reqs) sel)
    (forb : PathNodeId → Bool) (hf : forb (extendPid (filterAll g reqs) d sel) = false) :
    ChainSound (upFiltering g reqs d title forb) (extend (filterAll g reqs) d sel) := by
  have hadd := ChainSound_addNode _ d title forb hd hbelow hmok sel h hf
  simp only [upFiltering, up, hvalid, if_true]
  split
  · exact ChainSound_review _ _ hadd
  · exact hadd

/-- **The obligation, one step later and strictly weaker.** -/
def FilteredChain : Prop :=
  ∀ (g : GPathM) (d : NodeId), Reachable reqOf forb g → isValid g = true →
    (∃ sel, ChainSound g sel) →
    isValid (filterAll g (reqOf d)) = true →
    ∃ sel, ChainSound (filterAll g (reqOf d)) sel ∧
      forb (extendPid (filterAll g (reqOf d)) d sel) = false

theorem ReqChain_gives_FilteredChain (h : ReqChain reqOf forb) : FilteredChain reqOf forb := by
  intro g d hr hv hex hfv
  obtain ⟨sel, hsel, hreqs, hf⟩ := h g d hr hv hex hfv
  exact ⟨sel, ChainSound_filterAll g (reqOf d) sel hsel hreqs, hf⟩

/-- **The ledger, closed down to `FilteredChain`.** -/
theorem CertifiesS_of_FilteredChain (h : FilteredChain reqOf forb) : CertifiesS reqOf forb := by
  intro g hreach
  induction hreach with
  | seed d title hstep _ =>
    intro _; exact ⟨_, ChainSound_initSeed d title hstep⟩
  | up g d title hstep _ _ hr ih =>
    intro hv
    have hgv : isValid g = true := isValid_of_upFiltering g (reqOf d) d title forb hv
    have hfv : isValid (filterAll g (reqOf d)) = true :=
      isValid_of_filterAll_of_upFiltering g (reqOf d) d title forb hv
    obtain ⟨sel, hsel, hf⟩ := h g d hr hgv (ih hgv) hfv
    refine ⟨_, ChainSound_upFiltering_of_filtered g (reqOf d) d title hfv ?_ ?_ ?_ sel hsel forb hf⟩
    · rw [(pruned_filterAll g (reqOf d)).step_eq]; exact hstep
    · exact nodes_below_of_pruned (pruned_filterAll g (reqOf d))
        (steps_below_current reqOf forb hr)
    · exact MachineOk_of_pruned (pruned_filterAll g (reqOf d))
        (MachineOk_reachable reqOf forb g hr)
  | join g₁ g₂ hok _ _ ih₁ _ =>
    intro _
    obtain ⟨sel, hsel⟩ := ih₁ (isValid_left_of_okJoin hok)
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel⟩

theorem Certifies_of_FilteredChain (h : FilteredChain reqOf forb) : Certifies reqOf forb :=
  Certifies_of_CertifiesS reqOf forb (CertifiesS_of_FilteredChain reqOf forb h)

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

/-- **Bin map:** the chain must also extend into the row `d` opens without hitting a
prohibited window. -/
def ValidHasChainW (forb : PathNodeId → Bool) (h : GPathM) (d : NodeId) : Prop :=
  isValid h = true → ∃ sel, ChainSound h sel ∧ forb (extendPid h d sel) = false

theorem FilteredChain_of_ValidHasChain
    (h : ∀ (g : GPathM) (d : NodeId), Reachable reqOf forb g →
      ValidHasChainW forb (filterAll g (reqOf d)) d) : FilteredChain reqOf forb :=
  fun g d hr _ _ hfv => h g d hr hfv

/-- The filtered graph really is a `review` fixpoint, so the obligation only
ever has to be met there. -/
theorem filterAll_is_review_fixpoint (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) :
    review (filterAll g reqs) = filterAll g reqs :=
  review_idempotent _ hv

theorem Certifies_of_ValidHasChain
    (h : ∀ (g : GPathM) (d : NodeId), Reachable reqOf forb g →
      ValidHasChainW forb (filterAll g (reqOf d)) d) : Certifies reqOf forb :=
  Certifies_of_FilteredChain reqOf forb (FilteredChain_of_ValidHasChain reqOf forb h)

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.CertifiesS_of_FilteredChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiesS_of_FilteredChain

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.Certifies_of_ValidHasChain' depends on axioms: [propext, Quot.sound] -/
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
    (hreach : Reachable reqOf forb g) (hv : isValid (filterAll g reqs) = true) :
    ArcConsistent reqOf (filterAll g reqs) :=
  arcConsistent_of_ReqFiltered reqOf _ hv
    (filterAll_preserves_ReqFiltered reqOf (L1 reqOf forb hreach) reqs)

/-- ⚠ **FALSE as stated** — see `not_ArcImpliesChain` below, and use
`ArcImpliesChainOn` instead. Dropping `Reachable` admits graphs the machine
cannot build, and a node-less one refutes it. Kept because the refutation is
the point.

The whole claim, with every machine-specific hypothesis discharged.

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

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.arcConsistent_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arcConsistent_filterAll

-- ============================================================
-- ⚠ `ArcImpliesChain` as stated above is FALSE
-- ============================================================

/-!
Dropping `Reachable` from the obligation was not a weakening — it was a
strengthening, and it went too far. Without it the statement quantifies over
graphs the machine cannot build, and one of those refutes it outright: a graph
with a global owner at every step and **no nodes at all** is valid, is a
`review` fixpoint, and is arc consistent for free (every clause of
`ArcConsistent` quantifies over nodes), yet has no chain because there is
nothing to select.

That is a flaw in v23's framing, not in the machine. The repair is below:
state the obligation on the graphs it is actually applied to, keeping the
`Reachable` context — which is exactly `FilteredChain` with arc consistency
added as a free extra hypothesis.
-/

/-- A valid, arc-consistent `review` fixpoint with no nodes. -/
def degenerate : GPathM :=
  { nodes := [],
    gowners := [{ id := { step := 0, index := 0 }, parent_id := none }],
    current_step := 1,
    map_parent := none }

theorem degenerate_valid : isValid degenerate = true := rfl

theorem degenerate_fixpoint : review degenerate = degenerate := rfl

theorem degenerate_node? (pid : PathNodeId) : degenerate.node? pid = none := rfl

theorem degenerate_arcConsistent : ArcConsistent reqOf degenerate where
  supported := fun pid n hn => by rw [degenerate_node?] at hn; exact absurd hn (by simp)
  pinned := fun d hd => absurd hd List.not_mem_nil
  coherent_parents := fun k hk => absurd hk (by intro h; exact absurd h List.not_mem_nil)
  coherent_sons := fun k hk => absurd hk (by intro h; exact absurd h List.not_mem_nil)

theorem degenerate_no_chain : ¬ ∃ sel, ChainSound degenerate sel := by
  intro ⟨sel, hsel⟩
  have hsome := (hsel.chain.1.1 0 (by decide) (by decide)).1
  rw [degenerate_node?] at hsome
  exact Bool.false_ne_true hsome

/-- **`ArcImpliesChain` is false.** Proved, not suspected. -/
theorem not_ArcImpliesChain : ¬ ArcImpliesChain reqOf := fun h =>
  degenerate_no_chain (h degenerate (degenerate_arcConsistent reqOf)
    degenerate_valid degenerate_fixpoint)

/-- Bin map: `ArcImpliesChain` gives no control over the chain's extension, so the classic
route through `ValidHasChain` does not apply; since the premise is refuted anyway
(`not_ArcImpliesChain`, below), the implication is closed from that. -/
theorem Certifies_of_ArcImpliesChain (h : ArcImpliesChain reqOf) : Certifies reqOf forb :=
  (not_ArcImpliesChain reqOf h).elim

-- ============================================================
-- The repair: the obligation on the graphs it is applied to
-- ============================================================

/-- **The obligation, with every hypothesis the call site actually has.** This
is `FilteredChain` with arc consistency and the fixpoint added — both free, by
`arcConsistent_filterAll` and `filterAll_is_review_fixpoint` — and with the
`Reachable` context kept, which is what rules out `degenerate`. -/
def ArcImpliesChainOn : Prop :=
  ∀ (g : GPathM) (d : NodeId), Reachable reqOf forb g → isValid g = true →
    (∃ sel, ChainSound g sel) →
    ArcConsistent reqOf (filterAll g (reqOf d)) →
    review (filterAll g (reqOf d)) = filterAll g (reqOf d) →
    isValid (filterAll g (reqOf d)) = true →
    ∃ sel, ChainSound (filterAll g (reqOf d)) sel ∧
      forb (extendPid (filterAll g (reqOf d)) d sel) = false

theorem FilteredChain_of_ArcImpliesChainOn (h : ArcImpliesChainOn reqOf forb) :
    FilteredChain reqOf forb := fun g d hr hv hex hfv =>
  h g d hr hv hex (arcConsistent_filterAll reqOf forb g (reqOf d) hr hfv)
    (filterAll_is_review_fixpoint g (reqOf d) hfv) hfv

theorem Certifies_of_ArcImpliesChainOn (h : ArcImpliesChainOn reqOf forb) : Certifies reqOf forb :=
  Certifies_of_FilteredChain reqOf forb (FilteredChain_of_ArcImpliesChainOn reqOf forb h)

/-- And it *is* weaker than `FilteredChain`: the two extra hypotheses come for
free, so anything that proves `FilteredChain` proves this. -/
theorem ArcImpliesChainOn_of_FilteredChain (h : FilteredChain reqOf forb) :
    ArcImpliesChainOn reqOf forb := fun g d hr hv hex _ _ hfv => h g d hr hv hex hfv

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.not_ArcImpliesChain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms not_ArcImpliesChain

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.Certifies_of_ArcImpliesChainOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Certifies_of_ArcImpliesChainOn

-- ============================================================
-- What the counterexample actually names
-- ============================================================

/-- **Every global owner is a node.** This is the property `degenerate`
violates, and therefore the one `Reachable` was silently supplying. Any proof
of the obligation needs it explicitly: without it "there is an owner at every
step" says nothing about there being anything to select. -/
def GownersAreNodes (h : GPathM) : Prop := ∀ q ∈ h.gowners, (h.node? q).isSome = true

theorem not_GownersAreNodes_degenerate : ¬ GownersAreNodes degenerate := by
  intro h
  have hx := h { id := { step := 0, index := 0 }, parent_id := none } (by
    show _ ∈ [({ id := { step := 0, index := 0 }, parent_id := none } : PathNodeId)]
    exact List.mem_cons_self ..)
  rw [degenerate_node?] at hx
  exact Bool.false_ne_true hx

theorem initSeed_gowners (d : NodeId) (title : String) :
    (GPathM.initSeed d title).gowners = [{ id := d, parent_id := none }] := by
  unfold GPathM.initSeed GPathM.up GPathM.addNode
  simp [GPathM.isValid, GPathM.empty, GPathM.intRange, GPathM.hasStepEntry,
    GPathM.newRowIds, GPathM.shiftRowIds, GPathM.skipsWindow, GPathM.noForb]

/-- The seed satisfies it. The remaining ledger for this invariant is
`addNode`, `filterAll` and `join` — and `filterRequire` is where it can
*temporarily* fail, since it drops global owners without dropping the nodes
that carry them; `review` is what restores it by removing those nodes. -/
theorem GownersAreNodes_initSeed (d : NodeId) (title : String) :
    GownersAreNodes (GPathM.initSeed d title) := by
  intro q hq
  rw [initSeed_gowners] at hq
  rcases List.mem_singleton.mp hq with rfl
  rw [node?_initSeed]
  rfl

/-- info: 'AbsSatBin.GraphPath.Model.Certifies.not_GownersAreNodes_degenerate' does not depend on any axioms -/
#guard_msgs in
#print axioms not_GownersAreNodes_degenerate

end AbsSatBin.GraphPath.Model.Certifies
