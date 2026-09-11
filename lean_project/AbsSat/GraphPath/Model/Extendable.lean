-- lean_project/AbsSat/GraphPath/Model/Extendable.lean
import AbsSat.GraphPath.Model.Verdict

/-!
**Route A — replacing the global `∃` by a local `∀`.**

`Supported g` says *there exists* a complete co-owned chain through every node.
Induction on `Reachable` cannot reach it: the `up` case would have to conjure a
global object out of the one- and two-consistency that `upFiltering` and the
coherence passes maintain, and it does not reduce.

The standard move when an existential invariant is not inductive is to
**strengthen it until it is**. Here the strengthening is *backtrack-freeness*:

> `Extendable` — every consistent partial chain extends one more step.

That is a **one-step** property, the kind a filtering pass can plausibly
sustain, and `Supported` follows from it by induction on the step index rather
than on the construction. This module does that reduction:

    ExtendUp g → ExtendDown g → NodesInRange g → Supported g

so the open problem moves from "a global chain exists" to "nothing ever gets
stuck". This is Freuder's backtrack-free condition, stated as an invariant of
the mirror.

**Why this is the right target and not just a different one.** `Verdict.lean`
records that the reader does not backtrack: it picks a surviving node, filters,
and stops if that invalidates the graph. So what the reader needs is precisely
that every partial selection extends — `Extendable`, not `Supported`. And
v17's measurement (the map's constraint hypergraph is not α-acyclic) says the
proof cannot come from the map's static structure, which leaves the machine's
pruning: exactly what `Extendable` is about.

**`Extendable` is strictly stronger than `Supported`.** `Supported` allows a
pair of nodes that own each other while lying on no common chain; a
non-backtracking search that picks that pair is stuck even though every node
involved is supported.

## The measurement, and what it says (2026-09-09)

`ExtendSearch.lean` (`lake exe extend`) explores every consistent partial chain
of every valid state, in both directions. **`Extendable` is false.** Over 60
random instances: 14 with a stuck chain, **1,574 dead-end partial chains**
(1,517 upward, 57 downward). A witness on the phase-transition instance is a
*complete* partial chain from step 0 to step 12 with no continuation at 13.

So the reduction below is sound and its hypothesis is refuted: **route A in
this form is closed**, exactly as v13 closed v12's.

## But the refutation locates the missing ingredient

The search above checks only pairwise co-ownership. The machine's reader does
something more: after each pick it runs `filterAll`, which **propagates** —
prunes everything incompatible with the selection — and continues in the
filtered graph. Re-run with propagation (`lake exe extend --read`) and on the
very same instances **nothing ever gets stuck**, at every state and every
branch.

That is the finding, and it is sharper than "A fails":

> Pairwise ownership alone is *not* enough — which is why the width and
> hypergraph analyses kept coming up short. The propagation after each
> selection is what recovers it.

Which says the successor target is `PickStable` / `Determined` below — route A
restated *with* propagation, and the same statement as `Verdict.ReadStable`.
-/

namespace AbsSat.GraphPath.Model.Extendable

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Verdict (SupportedAt)

-- ============================================================
-- Selections, updated at one step
-- ============================================================

/-- Override a selection at one step. `Int` has decidable equality, so this
stays out of `Classical`. -/
def upd (sel : Int → PathNodeId) (j : Int) (c : PathNodeId) : Int → PathNodeId :=
  fun i => if i = j then c else sel i

theorem upd_self (sel : Int → PathNodeId) (j : Int) (c : PathNodeId) :
    upd sel j c j = c := by unfold upd; rw [if_pos rfl]

theorem upd_other (sel : Int → PathNodeId) (j : Int) (c : PathNodeId) {i : Int}
    (h : i ≠ j) : upd sel j c i = sel i := by unfold upd; rw [if_neg h]

-- ============================================================
-- Partial chains, over an interval of steps
-- ============================================================

/-- `sel` is a chain over the steps `[lo, hi]`: a real node at each step, and
parent-linked between consecutive ones. -/
def PartialChain (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop :=
  (∀ i, lo ≤ i → i ≤ hi → (g.node? (sel i)).isSome ∧ (sel i).id.step = i) ∧
  (∀ i, lo ≤ i → i + 1 ≤ hi →
    sel i ∈ ((g.node? (sel (i + 1))).map PNodeM.parents).getD [])

/-- Every pick in `[lo, hi]` owns every other. -/
def PartialOwned (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop :=
  ∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
    sel i ∈ ownersAt (ownersOf g (sel j)) i

/-- A partial chain spanning the whole range is a chain. -/
theorem isChain_of_partial (g : GPathM) (sel : Int → PathNodeId)
    (h : PartialChain g sel 0 (g.current_step - 1)) : IsChain g sel := by
  refine ⟨?_, ?_⟩
  · intro k hlo hhi; exact h.1 k hlo (by omega)
  · intro k hlo hhi; exact h.2 k hlo (by omega)

theorem pairwiseOwned_of_partial (g : GPathM) (sel : Int → PathNodeId)
    (h : PartialOwned g sel 0 (g.current_step - 1)) : PairwiseOwned g sel := by
  intro i j hi0 hj0 hi hj hne
  exact h i j hi0 hj0 (by omega) (by omega) hne

/-- The one-step selection at a node's own step. -/
theorem partial_singleton (g : GPathM) (pid : PathNodeId) (n : PNodeM)
    (hn : g.node? pid = some n) :
    PartialChain g (fun _ => pid) pid.id.step pid.id.step ∧
    PartialOwned g (fun _ => pid) pid.id.step pid.id.step := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hlo hhi
    have hi : i = pid.id.step := by omega
    refine ⟨by rw [hn]; rfl, ?_⟩
    rw [hi]
  · intro i _ _; omega
  · intro i j hi0 hj0 hi hj hne; omega

-- ============================================================
-- Backtrack-freeness
-- ============================================================

/-- **Nothing gets stuck going up**: any consistent partial chain over
`[lo, hi]` can be given a node at `hi + 1`. -/
def ExtendUp (g : GPathM) : Prop :=
  ∀ sel lo hi, 0 ≤ lo → lo ≤ hi → hi + 1 < g.current_step →
    PartialChain g sel lo hi → PartialOwned g sel lo hi →
    ∃ c, PartialChain g (upd sel (hi + 1) c) lo (hi + 1) ∧
         PartialOwned g (upd sel (hi + 1) c) lo (hi + 1)

/-- **Nothing gets stuck going down**: the same, towards step 0. Needed because
`Supported` asks for a chain through a node at an arbitrary step, not only
through a node at step 0. -/
def ExtendDown (g : GPathM) : Prop :=
  ∀ sel lo hi, 0 < lo → lo ≤ hi → hi < g.current_step →
    PartialChain g sel lo hi → PartialOwned g sel lo hi →
    ∃ c, PartialChain g (upd sel (lo - 1) c) (lo - 1) hi ∧
         PartialOwned g (upd sel (lo - 1) c) (lo - 1) hi

/-- Every node the machine holds sits at a step it is actually running. -/
def NodesInRange (g : GPathM) : Prop :=
  ∀ pid n, g.node? pid = some n → 0 ≤ pid.id.step ∧ pid.id.step < g.current_step

-- ============================================================
-- The reduction: induction on the step index, not on `Reachable`
-- ============================================================

theorem extendUpTo (g : GPathM) (hup : ExtendUp g) (m : Nat) :
    ∀ (sel : Int → PathNodeId) (lo hi : Int),
      (g.current_step - 1 - hi).toNat ≤ m →
      0 ≤ lo → lo ≤ hi → hi < g.current_step →
      PartialChain g sel lo hi → PartialOwned g sel lo hi →
      ∃ sel', (∀ i, lo ≤ i → i ≤ hi → sel' i = sel i) ∧
        PartialChain g sel' lo (g.current_step - 1) ∧
        PartialOwned g sel' lo (g.current_step - 1) := by
  induction m with
  | zero =>
    intro sel lo hi hm hlo hlohi hhi hc ho
    have hEq : hi = g.current_step - 1 := by omega
    subst hEq
    exact ⟨sel, fun _ _ _ => rfl, hc, ho⟩
  | succ m ih =>
    intro sel lo hi hm hlo hlohi hhi hc ho
    if hnext : hi + 1 < g.current_step then
      obtain ⟨c, hc', ho'⟩ := hup sel lo hi hlo hlohi hnext hc ho
      obtain ⟨sel', hagree, hc'', ho''⟩ :=
        ih (upd sel (hi + 1) c) lo (hi + 1) (by omega) hlo (by omega) hnext hc' ho'
      refine ⟨sel', ?_, hc'', ho''⟩
      intro i hi1 hi2
      rw [hagree i hi1 (by omega), upd_other sel (hi + 1) c (by omega)]
    else
      have hEq : hi = g.current_step - 1 := by omega
      subst hEq
      exact ⟨sel, fun _ _ _ => rfl, hc, ho⟩

theorem extendDownTo (g : GPathM) (hdown : ExtendDown g) (m : Nat) :
    ∀ (sel : Int → PathNodeId) (lo hi : Int),
      lo.toNat ≤ m →
      0 ≤ lo → lo ≤ hi → hi < g.current_step →
      PartialChain g sel lo hi → PartialOwned g sel lo hi →
      ∃ sel', (∀ i, lo ≤ i → i ≤ hi → sel' i = sel i) ∧
        PartialChain g sel' 0 hi ∧ PartialOwned g sel' 0 hi := by
  induction m with
  | zero =>
    intro sel lo hi hm hlo hlohi hhi hc ho
    have hEq : lo = 0 := by omega
    subst hEq
    exact ⟨sel, fun _ _ _ => rfl, hc, ho⟩
  | succ m ih =>
    intro sel lo hi hm hlo hlohi hhi hc ho
    if hpos : 0 < lo then
      obtain ⟨c, hc', ho'⟩ := hdown sel lo hi hpos hlohi hhi hc ho
      obtain ⟨sel', hagree, hc'', ho''⟩ :=
        ih (upd sel (lo - 1) c) (lo - 1) hi (by omega) (by omega) (by omega) hhi hc' ho'
      refine ⟨sel', ?_, hc'', ho''⟩
      intro i hi1 hi2
      rw [hagree i (by omega) hi2, upd_other sel (lo - 1) c (by omega)]
    else
      have hEq : lo = 0 := by omega
      subst hEq
      exact ⟨sel, fun _ _ _ => rfl, hc, ho⟩

/-- **Route A, the reduction.** Backtrack-freeness gives "no zombies" — by
induction on the step index, with no case analysis on how the graph was built. -/
theorem SupportedAt_of_Extend (g : GPathM) (hup : ExtendUp g) (hdown : ExtendDown g)
    (pid : PathNodeId) (n : PNodeM) (hn : g.node? pid = some n)
    (hlo : 0 ≤ pid.id.step) (hhi : pid.id.step < g.current_step) :
    SupportedAt g pid := by
  obtain ⟨hc0, ho0⟩ := partial_singleton g pid n hn
  obtain ⟨sel₁, hagree₁, hc₁, ho₁⟩ :=
    extendUpTo g hup (g.current_step - 1 - pid.id.step).toNat
      (fun _ => pid) pid.id.step pid.id.step (Nat.le_refl _) hlo (Int.le_refl _)
      hhi hc0 ho0
  obtain ⟨sel₂, hagree₂, hc₂, ho₂⟩ :=
    extendDownTo g hdown pid.id.step.toNat sel₁ pid.id.step (g.current_step - 1)
      (Nat.le_refl _) hlo (by omega) (by omega) hc₁ ho₁
  refine ⟨sel₂, isChain_of_partial g sel₂ hc₂, pairwiseOwned_of_partial g sel₂ ho₂, ?_⟩
  rw [hagree₂ pid.id.step (Int.le_refl _) (by omega),
    hagree₁ pid.id.step (Int.le_refl _) (Int.le_refl _)]

/-- And therefore `Supported` — the open lemma L6 — for any graph whose nodes
sit at steps it is running. -/
theorem Supported_of_Extend (g : GPathM) (hrange : NodesInRange g)
    (hup : ExtendUp g) (hdown : ExtendDown g) : Supported g := by
  intro pid n hn
  obtain ⟨hlo, hhi⟩ := hrange pid n hn
  exact SupportedAt_of_Extend g hup hdown pid n hn hlo hhi

-- ============================================================
-- The successor target: route A restated with propagation
-- ============================================================

/-- The map nodes still available at step `k`. -/
def mapIdsAt (g : GPathM) (k : Int) : List NodeId :=
  ((g.line k).map (·.id.id)).foldl
    (fun acc id => if acc.contains id then acc else acc ++ [id]) []

/-- **What the measurement says holds.** Selecting any surviving map node and
*propagating* (`filterAll`, which is `filterRequire` followed by the review
passes) leaves the graph valid. This is the one-step form of
`Verdict.ReadStable`, and `lake exe extend --read` finds no violation.

Stated, not proved. Unlike `ExtendUp`, it is not refuted. -/
def PickStable (g : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < g.current_step → ∀ mid ∈ mapIdsAt g k,
    isValid (filterAll g [mid]) = true

/-- A graph in which propagation has left one map node per step. The remaining
obligation, once `PickStable` drives the induction, is that such a graph
denotes something — a much smaller statement than the general case, because
there is nothing left to choose at the map level. -/
def Determined (g : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < g.current_step → ∃ mid, mapIdsAt g k = [mid]

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.Extendable.Supported_of_Extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Supported_of_Extend


-- ============================================================
-- The descent alone, anchored at the top
-- ============================================================

/-!
**Why this section exists.** `Supported_of_Extend` above needs both halves, and
`ExtendUp` is refuted (1,574 dead-end partial chains). But the verdict does not
need `Supported`: `Verdict.Inhabited_of_SupportedAt` needs the chain through
**one node of your choosing**. Choose one at the top step, and `extendUpTo`
becomes vacuous — only the descent is left.

That matters because the two halves do not measure alike. `ExtendDown` in full
generality is refuted too (57 of those dead ends are downward), but it
quantifies over partial chains ending anywhere. The composed proof only ever
descends from a chain that **already reaches the top step** — which is a strict
subset, and the one the reader actually walks.

`ExtendDownTop` below is that subset. Measured with `lake exe extend
--randomdowntop`, exhaustively over *every* downward partial chain from *every*
top-step node, three seeds:

| campaign | states | top anchors | chains to step 0 | dead ends |
|---|---|---|---|---|
| 8 cases, 2026, 3..5 vars | 472 | 657 | 1,095 | **0** |
| 12 cases, 31337, 3..6 vars | 1,069 | 1,673 | 4,324 | **0** |
| 10 cases, 4242, 4..6 vars | 834 | 1,389 | 3,912 | **0** |
| 10 cases, 90210, 5..7 vars | 967 | 1,674 | 6,424 | **0** |

**0 dead ends in 15,755 chains**, no search cut by budget. This is not a proof —
it is a hypothesis that has survived the measurement that killed its two
predecessors, and the reduction below says exactly what it would buy.
-/

/-- **Nothing gets stuck descending from the top.** `ExtendDown` restricted to
partial chains that already span `[lo, current_step - 1]`. -/
def ExtendDownTop (g : GPathM) : Prop :=
  ∀ sel lo, 0 < lo → lo ≤ g.current_step - 1 →
    PartialChain g sel lo (g.current_step - 1) →
    PartialOwned g sel lo (g.current_step - 1) →
    ∃ c, PartialChain g (upd sel (lo - 1) c) (lo - 1) (g.current_step - 1) ∧
         PartialOwned g (upd sel (lo - 1) c) (lo - 1) (g.current_step - 1)

theorem ExtendDownTop_of_ExtendDown (g : GPathM) (h : ExtendDown g) : ExtendDownTop g :=
  fun sel lo hpos hhi hc ho => h sel lo (g.current_step - 1) hpos hhi (by omega) hc ho

theorem extendDownTopTo (g : GPathM) (hdown : ExtendDownTop g) (m : Nat) :
    ∀ (sel : Int → PathNodeId) (lo : Int),
      lo.toNat ≤ m → 0 ≤ lo → lo ≤ g.current_step - 1 →
      PartialChain g sel lo (g.current_step - 1) →
      PartialOwned g sel lo (g.current_step - 1) →
      ∃ sel', (∀ i, lo ≤ i → i ≤ g.current_step - 1 → sel' i = sel i) ∧
        PartialChain g sel' 0 (g.current_step - 1) ∧
        PartialOwned g sel' 0 (g.current_step - 1) := by
  induction m with
  | zero =>
    intro sel lo hm hlo hlohi hc ho
    have hEq : lo = 0 := by omega
    subst hEq
    exact ⟨sel, fun _ _ _ => rfl, hc, ho⟩
  | succ m ih =>
    intro sel lo hm hlo hlohi hc ho
    if hpos : 0 < lo then
      obtain ⟨c, hc', ho'⟩ := hdown sel lo hpos hlohi hc ho
      obtain ⟨sel', hagree, hc'', ho''⟩ :=
        ih (upd sel (lo - 1) c) (lo - 1) (by omega) (by omega) (by omega) hc' ho'
      refine ⟨sel', ?_, hc'', ho''⟩
      intro i hi1 hi2
      rw [hagree i (by omega) hi2, upd_other sel (lo - 1) c (by omega)]
    else
      have hEq : lo = 0 := by omega
      subst hEq
      exact ⟨sel, fun _ _ _ => rfl, hc, ho⟩

/-- **A node at the top step is supported by the descent alone.** -/
theorem SupportedAt_top_of_ExtendDownTop (g : GPathM) (hdown : ExtendDownTop g)
    (pid : PathNodeId) (n : PNodeM) (hn : g.node? pid = some n)
    (htop : pid.id.step = g.current_step - 1) (hpos : 0 < g.current_step) :
    SupportedAt g pid := by
  obtain ⟨hc0, ho0⟩ := partial_singleton g pid n hn
  rw [htop] at hc0 ho0
  obtain ⟨sel, hagree, hc, ho⟩ :=
    extendDownTopTo g hdown (g.current_step - 1).toNat (fun _ => pid) (g.current_step - 1)
      (Nat.le_refl _) (by omega) (Int.le_refl _) hc0 ho0
  refine ⟨sel, isChain_of_partial g sel hc, pairwiseOwned_of_partial g sel ho, ?_⟩
  rw [htop, hagree (g.current_step - 1) (Int.le_refl _) (Int.le_refl _)]

-- ============================================================
-- The local statement the descent rests on
-- ============================================================

/-!
`ExtendDownTop` asks for a parent good for a whole history. `Threaded.hop_down`
delivers, for **each** owner of a node, **some** parent that owns it. The gap
is the swap ∀∃ -> ∃∀, and `lake exe extend --randomgoodparent` says it cannot
be closed by brute force: asking a parent to cover *every* owner above fails
for 134 of 6,947 nodes.

But the histories a chain can present are not arbitrary sets of owners. They
are **transversal cliques**: at most one node per step, pairwise mutually
owned. Restricted to those, the same measurement finds no failure at all — and
the exhaustive enumeration (`--randomclique`) checks every such set, not only
the maximal ones:

| campaign | nodes above step 0 | coherent demands | with no good parent |
|---|---|---|---|
| 8 cases, 2026, 3..5 vars | 6,947 | 154,635,941 | **0** |

(315 of the 6,947 enumerations were cut by the per-node budget.)

Two structural facts came out of the same run and are worth recording: the
parents of a node **always** share one map id (0 of 6,947 span two, which is
`parent_id` doing its job), but sibling parents do **not** share owner sets
(908 differing pairs) — so the swap is not free, and a proof has to use the
coherence of the demand.
-/

/-- A set of picks some chain could contain: distinct steps, pairwise mutual
ownership. -/
def Coherent (g : GPathM) (S : PathNodeId → Prop) : Prop :=
  ∀ a b, S a → S b → a ≠ b →
    a.id.step ≠ b.id.step ∧ a ∈ ownersOf g b ∧ b ∈ ownersOf g a

/-- **`GoodParentOnCliques`** — the local statement. Every node above step 0
has, for every coherent demand made of its own owners strictly above its step,
a parent mutually owned with the node *and* with the whole demand.

One node, its parents, its owners. No chains, no induction on the
construction, no global existential. -/
def GoodParentOnCliques (g : GPathM) : Prop :=
  ∀ (p : PathNodeId) (n : PNodeM), g.node? p = some n → 0 < p.id.step →
    ∀ S : PathNodeId → Prop,
      (∀ a, S a → p.id.step < a.id.step ∧ a ∈ ownersOf g p ∧ p ∈ ownersOf g a) →
      Coherent g S →
      ∃ c ∈ n.parents, c.id.step = p.id.step - 1 ∧
        (p ∈ ownersOf g c ∧ c ∈ ownersOf g p) ∧
        ∀ a, S a → (a ∈ ownersOf g c ∧ c ∈ ownersOf g a)

theorem mem_ownersAt {l : List PathNodeId} {q : PathNodeId} {k : Int}
    (hq : q ∈ l) (hs : q.id.step = k) : q ∈ ownersAt l k :=
  List.mem_filter.mpr ⟨hq, beq_iff_eq.mpr hs⟩

theorem node?_isSome_of_mem_ownersOf {g : GPathM} {c q : PathNodeId}
    (h : q ∈ ownersOf g c) : (g.node? c).isSome = true := by
  cases hcn : g.node? c with
  | none => rw [ownersOf, hcn] at h; exact absurd h List.not_mem_nil
  | some _ => rfl

/-- **The local statement gives the descent.** A partial chain's history is
exactly a coherent demand made of `sel lo`'s own owners, so the parent the
local statement produces is the extension. -/
theorem ExtendDownTop_of_GoodParentOnCliques (g : GPathM) (h : GoodParentOnCliques g) :
    ExtendDownTop g := by
  intro sel lo hpos hhi hc ho
  obtain ⟨hsome, hstep⟩ := hc.1 lo (Int.le_refl _) hhi
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have habove : ∀ a, (∃ j, lo < j ∧ j ≤ g.current_step - 1 ∧ sel j = a) →
      (sel lo).id.step < a.id.step ∧ a ∈ ownersOf g (sel lo) ∧ (sel lo) ∈ ownersOf g a := by
    rintro a ⟨j, hj1, hj2, rfl⟩
    obtain ⟨_, hjs⟩ := hc.1 j (by omega) hj2
    refine ⟨by rw [hstep, hjs]; exact hj1, ?_, ?_⟩
    · exact (List.mem_filter.mp (ho j lo (by omega) (Int.le_refl _) hj2 hhi (by omega))).1
    · exact (List.mem_filter.mp (ho lo j (Int.le_refl _) (by omega) hhi hj2 (by omega))).1
  have hcoh : Coherent g (fun a => ∃ j, lo < j ∧ j ≤ g.current_step - 1 ∧ sel j = a) := by
    rintro a b ⟨i, hi1, hi2, rfl⟩ ⟨j, hj1, hj2, rfl⟩ hne
    obtain ⟨_, his⟩ := hc.1 i (by omega) hi2
    obtain ⟨_, hjs⟩ := hc.1 j (by omega) hj2
    have hij : i ≠ j := fun heq => hne (by rw [heq])
    refine ⟨by rw [his, hjs]; exact hij, ?_, ?_⟩
    · exact (List.mem_filter.mp (ho i j (by omega) (by omega) hi2 hj2 hij)).1
    · exact (List.mem_filter.mp (ho j i (by omega) (by omega) hj2 hi2 (fun hh => hij hh.symm))).1
  obtain ⟨c, hcpar, hcstep, hcp, hcS⟩ :=
    h (sel lo) n hn (by omega) _ habove hcoh
  have hcstep' : c.id.step = lo - 1 := by rw [hcstep, hstep]
  have hcnode : (g.node? c).isSome = true := node?_isSome_of_mem_ownersOf hcp.1
  -- membership of the history's owners, by step
  have hown_c : ∀ j, lo ≤ j → j ≤ g.current_step - 1 → sel j ∈ ownersOf g c := by
    intro j hj1 hj2
    if hje : j = lo then rw [hje]; exact hcp.1
    else exact (hcS (sel j) ⟨j, by omega, hj2, rfl⟩).1
  have hc_own : ∀ j, lo ≤ j → j ≤ g.current_step - 1 → c ∈ ownersOf g (sel j) := by
    intro j hj1 hj2
    if hje : j = lo then rw [hje]; exact hcp.2
    else exact (hcS (sel j) ⟨j, by omega, hj2, rfl⟩).2
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro i hi1 hi2
    if hie : i = lo - 1 then
      subst hie
      rw [upd_self]
      exact ⟨hcnode, hcstep'⟩
    else
      rw [upd_other sel (lo - 1) c hie]
      exact hc.1 i (by omega) hi2
  · intro i hi1 hi2
    if hie : i = lo - 1 then
      subst hie
      rw [upd_self, upd_other sel (lo - 1) c (by omega)]
      have : lo - 1 + 1 = lo := by omega
      rw [this, hn]
      exact hcpar
    else
      rw [upd_other sel (lo - 1) c hie, upd_other sel (lo - 1) c (by omega)]
      exact hc.2 i (by omega) hi2
  · intro i j hi1 hj1 hi2 hj2 hne
    if hie : i = lo - 1 then
      subst hie
      have hjne : j ≠ lo - 1 := fun hh => hne hh.symm
      rw [upd_self, upd_other sel (lo - 1) c hjne]
      exact mem_ownersAt (hc_own j (by omega) hj2) hcstep'
    else
      rw [upd_other sel (lo - 1) c hie]
      obtain ⟨_, his⟩ := hc.1 i (by omega) hi2
      if hje : j = lo - 1 then
        subst hje
        rw [upd_self]
        exact mem_ownersAt (hown_c i (by omega) hi2) his
      else
        rw [upd_other sel (lo - 1) c hje]
        exact ho i j (by omega) (by omega) hi2 hj2 hne

/-- info: 'AbsSat.GraphPath.Model.Extendable.ExtendDownTop_of_GoodParentOnCliques' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ExtendDownTop_of_GoodParentOnCliques


end AbsSat.GraphPath.Model.Extendable
