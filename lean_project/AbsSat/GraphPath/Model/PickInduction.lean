-- lean_project/AbsSat/GraphPath/Model/PickInduction.lean
import AbsSat.GraphPath.Model.Extendable
import AbsSat.GraphPath.Model.Coherence

/-!
**Route A′ — route A with propagation.**

v18 refuted `Extendable`: pairwise co-ownership alone does not make the machine
backtrack-free, and `lake exe extend` exhibits 1,574 dead-end partial chains.
The same measurement showed that once the reader's own **propagation**
(`filterAll` after every selection) is included, nothing gets stuck.

So the induction has to be driven by the propagation, and this module sets it
up:

> Pick a map node the global owners still allow at a step where they still
> disagree, propagate, and land on a *strictly smaller* valid graph. Repeat
> until nothing is left to choose. If a graph with no choice left denotes
> something, so did the one you started from.

`Inhabited_of_descent` is that argument, proved. It reduces `Inhabited` — the
half of L6 the SAT/UNSAT verdict consumes (`Verdict.lean`) — to **one
obligation and a base case**:

* `PickValid` — selecting an allowed map node and propagating keeps the graph
  valid. This is `Verdict.ReadStable`'s one-step form, the statement
  `lake exe extend --read` finds no violation of.
* `NoChoice → Inhabited` — a valid graph whose global owners agree on one map
  node per step denotes something. Nothing is left to choose at the map level
  there, which makes it a different order of statement from L6.

**The measure decrease is not assumed.** `measure` counts `gowners` as well as
node weights, and `filterRequire` drops exactly the global owners that name a
different map node — so `measure_filterAll_lt` below is a theorem, not a
hypothesis. That is what makes this reduction cheaper than it looks: the
termination of the descent is free, and only the validity of each step is owed.

**And the transfer back is free too.** Filtering only prunes, so a chain of the
filtered graph is a chain of the original — `denot_filterAll_subset`, L2's
narrowing direction, already proved in `Filter.lean`.

## What `PickValid` has been ground down to (2026-09-09)

    Inhabited g
      ⟸ Inhabited_of_pickValid        PickValid + a no-choice base case
      ⟸ isValid_filterRequire         pinning is harmless — only `review` is left
      ⟸ isValid_review_of_pass        the fuel loop reduces to one pass
      ⟸ isValid_removeNode_of_other   one pass reduces to one node removal

so what is still owed is: **no removal the review makes is the last global
owner of its step** — in the regime where the graph is already valid, which is
the only regime `PickValid` speaks about. `not_isValid_removeNode_of_only`
records the exact shape of that failure. UNSAT lives elsewhere, in the
construction; see `Certifies.lean`.
-/

namespace AbsSat.GraphPath.Model.PickInduction

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- The measure, and why propagation strictly shrinks it
-- ============================================================

theorem intRange_bounds {lo hi k : Int} (h : k ∈ intRange lo hi) : lo ≤ k ∧ k ≤ hi := by
  simp only [intRange, List.mem_map, List.mem_range, Int.ofNat_eq_natCast] at h
  obtain ⟨i, hi', rfl⟩ := h
  exact ⟨by omega, by omega⟩

private theorem length_filter_lt {α : Type} (p : α → Bool) :
    ∀ (l : List α) (q : α), q ∈ l → p q = false → (l.filter p).length < l.length := by
  intro l
  induction l with
  | nil => intro q hq _; exact absurd hq List.not_mem_nil
  | cons a as ih =>
    intro q hq hp
    have hle : (as.filter p).length ≤ as.length := List.length_filter_le ..
    rcases List.mem_cons.mp hq with rfl | hq'
    · have hneg : ¬ (p q = true) := by rw [hp]; exact Bool.false_ne_true
      rw [List.filter_cons_of_neg hneg, List.length_cons]
      omega
    · have hlt := ih q hq' hp
      cases hpa : p a with
      | true =>
        rw [List.filter_cons_of_pos hpa, List.length_cons, List.length_cons]
        omega
      | false =>
        have hneg : ¬ (p a = true) := by rw [hpa]; exact Bool.false_ne_true
        rw [List.filter_cons_of_neg hneg, List.length_cons]
        omega

theorem filterRequire_nodes (g : GPathM) (req : NodeId) :
    (filterRequire g req).nodes = g.nodes := rfl

theorem filterRequire_gowners (g : GPathM) (req : NodeId) :
    (filterRequire g req).gowners =
      g.gowners.filter (fun q => q.id.step != req.step || q.id == req) := rfl

theorem measure_filterRequire_le (g : GPathM) (req : NodeId) :
    measure (filterRequire g req) ≤ measure g := by
  unfold GPathM.measure
  rw [filterRequire_nodes, filterRequire_gowners]
  have hle : (g.gowners.filter (fun q => q.id.step != req.step || q.id == req)).length
      ≤ g.gowners.length := List.length_filter_le ..
  omega

/-- **The descent, at the level of one filter.** `measure` counts `gowners`,
and `filterRequire` drops exactly the global owners at `req`'s step that name a
different map node. So a step where the owners still disagree strictly shrinks
the measure — no hypothesis needed. -/
theorem measure_filterRequire_lt (g : GPathM) (req : NodeId) (r : PathNodeId)
    (hr : r ∈ g.gowners) (hstep : r.id.step = req.step) (hne : r.id ≠ req) :
    measure (filterRequire g req) < measure g := by
  have h1 : (r.id.step != req.step) = false := by
    show (!(r.id.step == req.step)) = false
    rw [beq_iff_eq.mpr hstep]
    rfl
  have h2 : (r.id == req) = false := by
    cases hb : (r.id == req) with
    | false => rfl
    | true => exact absurd (eq_of_beq hb) hne
  have hfalse : (r.id.step != req.step || r.id == req) = false := by rw [h1, h2]; rfl
  have hlt := length_filter_lt
    (fun q : PathNodeId => q.id.step != req.step || q.id == req) g.gowners r hr hfalse
  unfold GPathM.measure
  rw [filterRequire_nodes, filterRequire_gowners]
  omega

theorem measure_reviewFuel_le : ∀ (n : Nat) (g : GPathM),
    measure (reviewFuel n g) ≤ measure g := by
  intro n
  induction n with
  | zero => intro g; exact Nat.le_refl _
  | succ n ih =>
    intro g
    simp only [reviewFuel]
    split
    · split
      · exact Nat.le_trans (ih (reviewPass g)) (measure_reviewPass_le g)
      · exact measure_reviewPass_le g
    · exact Nat.le_refl _

theorem measure_review_le (g : GPathM) : measure (review g) ≤ measure g :=
  measure_reviewFuel_le _ g

/-- **The descent, for the filter as the machine calls it.** -/
theorem measure_filterAll_lt (g : GPathM) (mid : NodeId) (r : PathNodeId)
    (hr : r ∈ g.gowners) (hstep : r.id.step = mid.step) (hne : r.id ≠ mid) :
    measure (filterAll g [mid]) < measure g := by
  refine Nat.lt_of_le_of_lt (measure_review_le _) ?_
  simp only [List.foldl_cons, List.foldl_nil]
  exact measure_filterRequire_lt g mid r hr hstep hne

-- ============================================================
-- Is there anything left to choose?
-- ============================================================

/-- Two global owners at step `k` naming different map nodes: a real choice is
still open there. -/
def choiceAt (g : GPathM) (k : Int) : Bool :=
  (ownersAt g.gowners k).any (fun q =>
    (ownersAt g.gowners k).any (fun r => q.id != r.id))

def hasChoice (g : GPathM) : Bool :=
  (intRange 0 (g.current_step - 1)).any (choiceAt g)

/-- Propagation has left the global owners agreeing on one map node per step.
**The base case's hypothesis** — and a much smaller statement than L6, because
there is nothing left to choose at the map level. -/
def NoChoice (g : GPathM) : Prop := hasChoice g = false

/-- **The one obligation that remains.** Selecting a map node the global owners
still allow *at a step that still has a choice*, and propagating, keeps the
graph valid. `Verdict.ReadStable`'s one-step form — the statement
`lake exe extend --read` finds no violation of.

The `choiceAt` guard is not cosmetic: the induction only ever picks at such a
step, and `filterRequire_eq_self_of_pinned` below shows a pick at a step
without a choice narrows nothing at all. So this is the smallest form of the
obligation the descent actually needs. -/
def PickValid (g : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < g.current_step → choiceAt g k = true → ∀ q ∈ ownersAt g.gowners k,
    isValid (filterAll g [q.id]) = true

-- ============================================================
-- Validity, in terms of the global owners
-- ============================================================

theorem isValid_of_gowner (g : GPathM)
    (h : ∀ k, 0 ≤ k → k < g.current_step → ∃ q ∈ g.gowners, q.id.step = k) :
    isValid g = true := by
  unfold GPathM.isValid
  refine List.all_eq_true.mpr ?_
  intro k hk
  obtain ⟨hlo, hhi⟩ := intRange_bounds hk
  obtain ⟨q, hq, hstep⟩ := h k hlo (by omega)
  exact List.any_eq_true.mpr ⟨q, hq, beq_iff_eq.mpr hstep⟩

theorem gowner_of_isValid (g : GPathM) (h : isValid g = true)
    (k : Int) (hlo : 0 ≤ k) (hhi : k < g.current_step) :
    ∃ q ∈ g.gowners, q.id.step = k := by
  unfold GPathM.isValid at h
  have hx := List.all_eq_true.mp h k (mem_intRange hlo (by omega))
  obtain ⟨q, hq, hs⟩ := List.any_eq_true.mp hx
  exact ⟨q, hq, eq_of_beq hs⟩

-- ============================================================
-- Half of `PickValid` is free: pinning never invalidates
-- ============================================================

/-- **`filterRequire` cannot invalidate a graph.** Pinning a step to a map node
the global owners already allow leaves every other step untouched, and leaves
the pinned step with the very owner that was picked.

This is what makes `PickValid` a statement about `review` alone: the filter's
first half is harmless, and all the difficulty is in the review passes that
follow it — the node removals, not the owner pinning. -/
theorem isValid_filterRequire (g : GPathM) (req : NodeId) (q₀ : PathNodeId)
    (hq₀ : q₀ ∈ g.gowners) (hq₀id : q₀.id = req) (hv : isValid g = true) :
    isValid (filterRequire g req) = true := by
  refine isValid_of_gowner _ ?_
  intro k hlo hhi
  rw [filterRequire_gowners]
  if hk : k = req.step then
    refine ⟨q₀, List.mem_filter.mpr ⟨hq₀, ?_⟩, by rw [hq₀id, ← hk]⟩
    rw [hq₀id, beq_iff_eq.mpr (rfl : req = req)]
    exact Bool.or_true _
  else
    obtain ⟨q, hq, hstep⟩ := gowner_of_isValid g hv k hlo hhi
    refine ⟨q, List.mem_filter.mpr ⟨hq, ?_⟩, hstep⟩
    have : (q.id.step != req.step) = true := bne_iff_ne.mpr (by rw [hstep]; exact hk)
    rw [this]
    exact Bool.true_or _

/-- A pick at a step where the global owners already agree narrows nothing:
the filter keeps every one of them. This is why `PickValid` may be guarded by
`choiceAt` without weakening `Inhabited_of_descent`. -/
theorem filterRequire_eq_self_of_pinned (g : GPathM) (req : NodeId)
    (h : ∀ q ∈ g.gowners, q.id.step = req.step → q.id = req) :
    filterRequire g req = g := by
  have hall : g.gowners.filter (fun q => q.id.step != req.step || q.id == req) = g.gowners := by
    refine List.filter_eq_self.mpr ?_
    intro q hq
    if hs : q.id.step = req.step then
      rw [beq_iff_eq.mpr (h q hq hs)]
      exact Bool.or_true _
    else
      rw [show (q.id.step != req.step) = true from bne_iff_ne.mpr hs]
      exact Bool.true_or _
  unfold GPathM.filterRequire
  rw [hall]

-- ============================================================
-- The other half is exactly L6 again — said precisely
-- ============================================================

/-- A graph carrying a chain that lives inside its global owners is valid. -/
theorem isValid_of_ChainG (g : GPathM) (sel : Int → PathNodeId) (h : ChainG g sel) :
    isValid g = true :=
  isValid_of_gowner _ (fun k hlo hhi => ⟨sel k, h.2.2 k hlo hhi, (h.1.1 k hlo hhi).2⟩)

theorem filterAll_single (g : GPathM) (mid : NodeId) :
    filterAll g [mid] = review (filterRequire g mid) := rfl

/-- **`PickValid` at one pick, from a sound chain through it.** `review`
preserves a `ChainSound` chain (`Coherence.ChainSound_review`), and a chain
inside the global owners makes the graph valid — so a pinned graph that still
has a chain propagates to a valid graph.

**And this is where the honest accounting has to happen.** The hypothesis is
"the graph still has a complete co-owned chain through the pinned map node",
which is L6 read at the map level. So proving `PickValid` *this* way is
circular with what route A′ uses it for: A′ turns L6's `Inhabited` half into a
one-step statement, it does not reduce it to something weaker. The value of
the reduction is that the one-step statement is the kind of thing the review
passes can be attacked with directly — and `isValid_filterRequire` above has
already removed the pinning half of it from the account. -/
theorem isValid_filterAll_of_ChainSound (g : GPathM) (mid : NodeId)
    (sel : Int → PathNodeId) (h : ChainSound (filterRequire g mid) sel) :
    isValid (filterAll g [mid]) = true :=
  isValid_of_ChainG _ sel (ChainSound_review _ sel h).chain

/-- The pinned-chain hypothesis, named. `PickValid_of_PinnedSound` says this
implies the obligation; the docstring above says why that is not a way out. -/
def PinnedSound (g : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < g.current_step → ∀ q ∈ ownersAt g.gowners k,
    ∃ sel, ChainSound (filterRequire g q.id) sel

theorem PickValid_of_PinnedSound (g : GPathM) (h : PinnedSound g) : PickValid g := by
  intro k hlo hhi _ q hq
  obtain ⟨sel, hsel⟩ := h k hlo hhi q hq
  exact isValid_filterAll_of_ChainSound g q.id sel hsel

-- ============================================================
-- Grinding the remaining half down: from `review` to one pass,
-- and from one pass to one removal
-- ============================================================

/-- **`review` reduces to a single pass.** The fuel loop stops as soon as the
graph goes invalid, so if one pass preserves validity inside a class the loop
stays in, the whole review does. `Q` is that class. -/
theorem isValid_reviewFuel_of_pass (Q : GPathM → Prop)
    (hQpass : ∀ g, Q g → Q (reviewPass g))
    (hQvalid : ∀ g, Q g → isValid g = true → isValid (reviewPass g) = true) :
    ∀ (n : Nat) (g : GPathM), Q g → isValid g = true → isValid (reviewFuel n g) = true := by
  intro n
  induction n with
  | zero => intro g _ hv; exact hv
  | succ n ih =>
    intro g hQ hv
    simp only [reviewFuel, if_pos hv]
    split
    · exact ih (reviewPass g) (hQpass g hQ) (hQvalid g hQ hv)
    · exact hQvalid g hQ hv

theorem isValid_review_of_pass (Q : GPathM → Prop)
    (hQpass : ∀ g, Q g → Q (reviewPass g))
    (hQvalid : ∀ g, Q g → isValid g = true → isValid (reviewPass g) = true)
    (g : GPathM) (hQ : Q g) (hv : isValid g = true) : isValid (review g) = true :=
  isValid_reviewFuel_of_pass Q hQpass hQvalid _ g hQ hv

/-- And a pass is three sweeps, each of which only ever drops nodes. -/
theorem reviewPass_eq (g : GPathM) :
    reviewPass g = reviewSons (reviewParents (cleanInvalid g)) := rfl

theorem removeNode_gowners (g : GPathM) (id : PathNodeId) :
    (removeNode g id).gowners = g.gowners.filter (fun q => q != id) := rfl

/-- **The atom.** Every way the review can lose validity goes through
`removeNode`, and `removeNode` only drops the one id from the global owners.
So validity survives a removal exactly when every step keeps *some other*
global owner — which is the whole of what `PickValid` still owes, once
`isValid_filterRequire` has taken the pinning half off the account. -/
theorem isValid_removeNode_of_other (g : GPathM) (id : PathNodeId)
    (h : ∀ k, 0 ≤ k → k < g.current_step → ∃ q ∈ g.gowners, q.id.step = k ∧ q ≠ id) :
    isValid (removeNode g id) = true := by
  refine isValid_of_gowner _ ?_
  intro k hlo hhi
  obtain ⟨q, hq, hstep, hne⟩ := h k hlo hhi
  refine ⟨q, ?_, hstep⟩
  rw [removeNode_gowners]
  exact List.mem_filter.mpr ⟨hq, bne_iff_ne.mpr hne⟩

/-- Conversely, a removal that leaves a step with no owner invalidates the
graph. Stated so the two directions sit together — but read it in the right
regime.

**Correction (author, 2026-09-09).** An earlier version of this docstring said
the review "must be able to invalidate, since that is how the machine reports
UNSAT", and used that to argue `PickValid` cannot be discharged by ruling
removals out. The verdict half is right but it belongs to a different regime:
UNSAT is decided by `upFiltering` **while the graph is being built**, and an
unsatisfiable formula never yields a valid set at all. The picks `PickValid`
quantifies over happen on a graph that is *already* valid — the regime the
Reader works in — and there an invalidation is not a verdict, it is an
invariant violation. See `Certifies.lean`.

So what this lemma marks is not "some removals are legitimate verdicts" but
the exact shape of the failure to rule out: a step stripped bare. -/
theorem not_isValid_removeNode_of_only (g : GPathM) (id : PathNodeId) (k : Int)
    (hlo : 0 ≤ k) (hhi : k < g.current_step)
    (h : ∀ q ∈ g.gowners, q.id.step = k → q = id) :
    isValid (removeNode g id) = false := by
  cases hv : isValid (removeNode g id) with
  | false => rfl
  | true =>
    obtain ⟨q, hq, hstep⟩ := gowner_of_isValid _ hv k hlo hhi
    rw [removeNode_gowners] at hq
    have hq' := List.mem_filter.mp hq
    exact absurd (h q hq'.1 hstep) (bne_iff_ne.mp hq'.2)

-- ============================================================
-- Transferring the denotation back is free
-- ============================================================

theorem Inhabited_of_filterAll (g : GPathM) (hnd : NodupIds g) (reqs : List NodeId)
    (h : AbsSat.GraphPath.Model.Inhabited (filterAll g reqs)) :
    AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, denot_filterAll_subset g hnd reqs p hp⟩

-- ============================================================
-- The induction
-- ============================================================

/-- **Route A′, the reduction.** `Inhabited` follows from `PickValid` and the
no-choice base case, by induction on the measure. `P` is whatever class the
machine's states live in (`Reachable`, say); all that is asked of it is that
propagation keeps you inside it and that node ids stay unique. -/
theorem Inhabited_of_descent
    (P : GPathM → Prop)
    (hPf : ∀ g mid, P g → isValid g = true → P (filterAll g [mid]))
    (hnd : ∀ g, P g → NodupIds g)
    (hpick : ∀ g, P g → isValid g = true → PickValid g)
    (hbase : ∀ g, P g → isValid g = true → NoChoice g →
      AbsSat.GraphPath.Model.Inhabited g) :
    ∀ (m : Nat) (g : GPathM), measure g ≤ m → P g → isValid g = true →
      AbsSat.GraphPath.Model.Inhabited g := by
  intro m
  induction m with
  | zero =>
    intro g hm hP hv
    match hch : hasChoice g with
    | false => exact hbase g hP hv hch
    | true =>
      obtain ⟨k, hkmem, hck⟩ := List.any_eq_true.mp hch
      obtain ⟨hklo, hkhi⟩ := intRange_bounds hkmem
      obtain ⟨q, hq, hq2⟩ := List.any_eq_true.mp hck
      obtain ⟨r, hr, hne⟩ := List.any_eq_true.mp hq2
      have hrg : r ∈ g.gowners := (List.mem_filter.mp hr).1
      have hrstep : r.id.step = k := eq_of_beq (List.mem_filter.mp hr).2
      have hqstep : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
      have hne' : r.id ≠ q.id := fun h => (bne_iff_ne.mp hne) h.symm
      have hlt : measure (filterAll g [q.id]) < measure g :=
        measure_filterAll_lt g q.id r hrg (by rw [hrstep, hqstep]) hne'
      exact absurd hlt (by omega)
  | succ m ih =>
    intro g hm hP hv
    match hch : hasChoice g with
    | false => exact hbase g hP hv hch
    | true =>
      obtain ⟨k, hkmem, hck⟩ := List.any_eq_true.mp hch
      obtain ⟨hklo, hkhi⟩ := intRange_bounds hkmem
      obtain ⟨q, hq, hq2⟩ := List.any_eq_true.mp hck
      obtain ⟨r, hr, hne⟩ := List.any_eq_true.mp hq2
      have hrg : r ∈ g.gowners := (List.mem_filter.mp hr).1
      have hrstep : r.id.step = k := eq_of_beq (List.mem_filter.mp hr).2
      have hqstep : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
      have hne' : r.id ≠ q.id := fun h => (bne_iff_ne.mp hne) h.symm
      have hlt : measure (filterAll g [q.id]) < measure g :=
        measure_filterAll_lt g q.id r hrg (by rw [hrstep, hqstep]) hne'
      have hv' : isValid (filterAll g [q.id]) = true :=
        hpick g hP hv k hklo (by omega) hck q hq
      exact Inhabited_of_filterAll g (hnd g hP) [q.id]
        (ih (filterAll g [q.id]) (by omega) (hPf g q.id hP hv) hv')

-- ============================================================
-- What the descent actually consumes: one good pick, not every one
-- ============================================================

/-!
`Inhabited_of_descent` above asks for `PickValid` — **every** allowed map node
at **every** step with a choice propagates to a valid graph. Reading its proof,
it consumes exactly one successful pick per stage; it takes the first `k` and
the first `q` only because that is what was convenient to write.

So the honest obligation is the existential one below, which is what "the
machine never has to backtrack" says at its weakest. It is strictly weaker than
`PickValid`, and `Inhabited_of_pickSome` shows the descent runs on it.

**Measured** (`lake exe extend --pickvalid`, 40 instances): of 63,314 allowed
picks over 2,794 valid states with a choice left, **0** invalidate — so the ∀
form survives too, and the weakening buys plausibility rather than a counted
gap. It is still the smaller thing to owe.
-/

/-- Some allowed pick, at some step that still has a choice, keeps the graph
valid. -/
def PickSome (g : GPathM) : Prop :=
  hasChoice g = true → ∃ k, 0 ≤ k ∧ k < g.current_step ∧ choiceAt g k = true ∧
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAll g [q.id]) = true

theorem PickSome_of_PickValid (g : GPathM) (h : PickValid g) : PickSome g := by
  intro hch
  obtain ⟨k, hkmem, hck⟩ := List.any_eq_true.mp hch
  obtain ⟨hklo, hkhi⟩ := intRange_bounds hkmem
  obtain ⟨q, hq, _⟩ := List.any_eq_true.mp hck
  exact ⟨k, hklo, by omega, hck, q, hq, h k hklo (by omega) hck q hq⟩

/-- A step that still has a choice always offers, for any pick there, a rival
global owner naming a different map node — which is what makes the filter
strictly shrink the measure. -/
theorem measure_lt_of_choiceAt (g : GPathM) (k : Int) (hck : choiceAt g k = true)
    (q : PathNodeId) (hq : q ∈ ownersAt g.gowners k) :
    measure (filterAll g [q.id]) < measure g := by
  obtain ⟨x, hx, hx2⟩ := List.any_eq_true.mp hck
  obtain ⟨y, hy, hne⟩ := List.any_eq_true.mp hx2
  have hxs : x.id.step = k := eq_of_beq (List.mem_filter.mp hx).2
  have hys : y.id.step = k := eq_of_beq (List.mem_filter.mp hy).2
  have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
  have hxy : x.id ≠ y.id := bne_iff_ne.mp hne
  if hxq : x.id = q.id then
    refine measure_filterAll_lt g q.id y (List.mem_filter.mp hy).1 (by rw [hys, hqs]) ?_
    intro h; exact hxy (hxq.trans h.symm)
  else
    exact measure_filterAll_lt g q.id x (List.mem_filter.mp hx).1 (by rw [hxs, hqs]) hxq

/-- **Route A′, on the weaker obligation.** Identical to `Inhabited_of_descent`
except that only *one* good pick per stage is required. -/
theorem Inhabited_of_descent_some
    (P : GPathM → Prop)
    (hPf : ∀ g mid, P g → isValid g = true → P (filterAll g [mid]))
    (hnd : ∀ g, P g → NodupIds g)
    (hpick : ∀ g, P g → isValid g = true → PickSome g)
    (hbase : ∀ g, P g → isValid g = true → NoChoice g →
      AbsSat.GraphPath.Model.Inhabited g) :
    ∀ (m : Nat) (g : GPathM), measure g ≤ m → P g → isValid g = true →
      AbsSat.GraphPath.Model.Inhabited g := by
  intro m
  induction m with
  | zero =>
    intro g hm hP hv
    match hch : hasChoice g with
    | false => exact hbase g hP hv hch
    | true =>
      obtain ⟨k, _, _, hck, q, hq, _⟩ := hpick g hP hv hch
      exact absurd (measure_lt_of_choiceAt g k hck q hq) (by omega)
  | succ m ih =>
    intro g hm hP hv
    match hch : hasChoice g with
    | false => exact hbase g hP hv hch
    | true =>
      obtain ⟨k, _, _, hck, q, hq, hv'⟩ := hpick g hP hv hch
      have hlt := measure_lt_of_choiceAt g k hck q hq
      exact Inhabited_of_filterAll g (hnd g hP) [q.id]
        (ih (filterAll g [q.id]) (by omega) (hPf g q.id hP hv) hv')

theorem Inhabited_of_pickSome
    (P : GPathM → Prop)
    (hPf : ∀ g mid, P g → isValid g = true → P (filterAll g [mid]))
    (hnd : ∀ g, P g → NodupIds g)
    (hpick : ∀ g, P g → isValid g = true → PickSome g)
    (hbase : ∀ g, P g → isValid g = true → NoChoice g →
      AbsSat.GraphPath.Model.Inhabited g)
    (g : GPathM) (hP : P g) (hv : isValid g = true) :
    AbsSat.GraphPath.Model.Inhabited g :=
  Inhabited_of_descent_some P hPf hnd hpick hbase (measure g) g (Nat.le_refl _) hP hv

/-- info: 'AbsSat.GraphPath.Model.PickInduction.Inhabited_of_pickSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_pickSome

/-- The same, without the explicit fuel. -/
theorem Inhabited_of_pickValid
    (P : GPathM → Prop)
    (hPf : ∀ g mid, P g → isValid g = true → P (filterAll g [mid]))
    (hnd : ∀ g, P g → NodupIds g)
    (hpick : ∀ g, P g → isValid g = true → PickValid g)
    (hbase : ∀ g, P g → isValid g = true → NoChoice g →
      AbsSat.GraphPath.Model.Inhabited g)
    (g : GPathM) (hP : P g) (hv : isValid g = true) :
    AbsSat.GraphPath.Model.Inhabited g :=
  Inhabited_of_descent P hPf hnd hpick hbase (measure g) g (Nat.le_refl _) hP hv

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.PickInduction.measure_filterAll_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms measure_filterAll_lt

/-- info: 'AbsSat.GraphPath.Model.PickInduction.isValid_filterRequire' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_filterRequire

/-- info: 'AbsSat.GraphPath.Model.PickInduction.isValid_review_of_pass' does not depend on any axioms -/
#guard_msgs in
#print axioms isValid_review_of_pass

/-- info: 'AbsSat.GraphPath.Model.PickInduction.isValid_removeNode_of_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_removeNode_of_other

/-- info: 'AbsSat.GraphPath.Model.PickInduction.Inhabited_of_pickValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_pickValid

end AbsSat.GraphPath.Model.PickInduction
