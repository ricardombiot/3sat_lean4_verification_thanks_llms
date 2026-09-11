-- lean_project/AbsSat/GraphMap/CnfReducer.lean
import AbsSat.GraphMap.CnfMap

/-!
# The semi-join reducer, in the pure model

v71 measured the repair that a bounded-scope proof of `FlipCore` would perform,
and the measurement corrected it twice. What survived — 0 failures in 47.663
instances inside the class — was the classical procedure for acyclic CSPs:
**reduce by semi-joins to the fixpoint, then pick**. This module builds the
first half of that in the pure model.

## Scope: this is a procedure over **formulas**, not over the machine

**Nothing in this module mentions `owners`, `GPathM`, `filterAll` or `review`,
and nothing here is proved about them.** The reducer below is the classical
semi-join procedure over clause relations; the machine decides which nodes
survive by pruning `owners` tables, with the parents/sons coherence passes.
The two have the same *shape*, and v74 retracts the claim that they are the
same thing: that they compute the same survivors is exactly the inclusion
`owners ⊆ support` that `ArcConsistency.lean` states and leaves open since v11.
Read every comparison with the machine below as an analogy awaiting a bridge.

## The unit is the row

The first correction the measurement forced was that the repair cannot move one
*variable* at a time. A clause node of the map carries its three literals at
once, and so does the classical relation: the object that moves is a **row**.
The rows here reuse `CnfMap`'s numbering — the indices `1..7` with
`b1`/`b2`/`b3` reading off which literal each bit names true — so that a future
bridge has one translation less to do. Row `0`, the all-false row, is the one
the map omits and the one no solution uses. Reusing the numbering is *not* a
claim that the surviving rows coincide with the machine's surviving nodes.

## What a sweep does, and what is proved about it

A sweep drops from each clause's relation every row with no partner in some
other clause's relation — a semi-join, run to the fixpoint. Two facts matter,
and neither needs acyclicity:

* **Conservation** (`rowOfAssign_mem_reduce`): the reducer never drops a row
  that a solution uses. This is the same shape as every conservation result in
  this development — the witness comes from outside, and the machinery is only
  forbidden to destroy it — and it is what makes the reducer safe to put inside
  the argument at all. Its corollary is that a satisfiable prefix never leaves
  an empty relation.
* **Arc consistency of the fixpoint** (`arcConsistent_of_sweep_eq`): at the
  fixpoint every surviving row has a partner everywhere. This is the premise
  Beeri–Fagin–Maier–Yannakakis needs. `ArcConsistency.review_arcConsistent`
  proves a statement of the same shape for the machine's owners tables; the two
  are about different objects and neither implies the other.

What is **not** here is the other half — that on an α-acyclic hypergraph the
reduced relations can then be picked greedily without backtracking. That is
where `BoundedScope` enters, and it is the next piece.
-/

namespace AbsSat.GraphMap.CnfReducer

open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap

-- ============================================================
-- Rows, and the values they fix
-- ============================================================

/-- A bit, as the map writes it. -/
def bitOf (b : Bool) : Int := if b then 1 else 0

/-- The value a row gives a literal's **variable**. A bit of `1` names the
literal true, so a negated literal's variable goes the other way. -/
def varOfLit (l : Lit) (b : Int) : Bool :=
  if l.pos then b == 1 else !(b == 1)

/-- The three variable/value pairs a row of a clause fixes. -/
def rowPairs (c : Clause) (r : Int) : List (Nat × Bool) :=
  [(c.l1.v, varOfLit c.l1 (b1 r)), (c.l2.v, varOfLit c.l2 (b2 r)),
   (c.l3.v, varOfLit c.l3 (b3 r))]

/-- Two sets of variable/value pairs agree wherever they name the same
variable. -/
def pairsAgree (p q : List (Nat × Bool)) : Bool :=
  p.all (fun x => q.all (fun y => x.1 != y.1 || x.2 == y.2))

/-- A row is **self-consistent** when its three pairs do not contradict each
other. This is not vacuous: `WF` asks for distinct *steps*, not distinct
variables, so `x ∨ ¬x ∨ y` is well-formed and its rows that call both `x` and
`¬x` true fix one variable twice, differently. -/
def rowOk (c : Clause) (r : Int) : Bool := pairsAgree (rowPairs c r) (rowPairs c r)

/-- The seven rows the map builds: every one but the all-false row. -/
def allRows : List Int := [1, 2, 3, 4, 5, 6, 7]

/-- One clause's relation, before any reduction. -/
def initRows (c : Clause) : List Int := allRows.filter (fun r => rowOk c r)

/-- **The row an assignment uses**, in the map's own numbering: bit `i` is set
exactly when the assignment makes literal `i` true. -/
def rowOfAssign (a : Assign) (c : Clause) : Int :=
  4 * bitOf (litVal a c.l1) + 2 * bitOf (litVal a c.l2) + bitOf (litVal a c.l3)

-- ============================================================
-- The row of an assignment reads back as the assignment
-- ============================================================

/-! The three bits go in and come back out. Stated over plain booleans, so the
whole thing is eight concrete cases the kernel checks. -/

theorem b1_bits (x y z : Bool) : b1 (4 * bitOf x + 2 * bitOf y + bitOf z) = bitOf x := by
  cases x <;> cases y <;> cases z <;> decide

theorem b2_bits (x y z : Bool) : b2 (4 * bitOf x + 2 * bitOf y + bitOf z) = bitOf y := by
  cases x <;> cases y <;> cases z <;> decide

theorem b3_bits (x y z : Bool) : b3 (4 * bitOf x + 2 * bitOf y + bitOf z) = bitOf z := by
  cases x <;> cases y <;> cases z <;> decide

theorem b1_rowOfAssign (a : Assign) (c : Clause) :
    b1 (rowOfAssign a c) = bitOf (litVal a c.l1) := b1_bits _ _ _

theorem b2_rowOfAssign (a : Assign) (c : Clause) :
    b2 (rowOfAssign a c) = bitOf (litVal a c.l2) := b2_bits _ _ _

theorem b3_rowOfAssign (a : Assign) (c : Clause) :
    b3 (rowOfAssign a c) = bitOf (litVal a c.l3) := b3_bits _ _ _

/-- Reading a literal's bit back gives the assignment's own value for that
literal's variable. -/
theorem varOfLit_core (p v : Bool) :
    (if p = true then bitOf (if p = true then v else !v) == 1
     else !(bitOf (if p = true then v else !v) == 1)) = v := by
  cases p <;> cases v <;> decide

theorem varOfLit_bitOf (a : Assign) (l : Lit) :
    varOfLit l (bitOf (litVal a l)) = a l.v := varOfLit_core l.pos (a l.v)

/-- **Every pair a solution's row fixes is the solution's own value.** -/
theorem mem_rowPairs_rowOfAssign (a : Assign) (c : Clause) (p : Nat × Bool)
    (hp : p ∈ rowPairs c (rowOfAssign a c)) : p.2 = a p.1 := by
  simp only [rowPairs, b1_rowOfAssign, b2_rowOfAssign, b3_rowOfAssign] at hp
  rcases List.mem_cons.mp hp with rfl | hp1
  · exact varOfLit_bitOf a c.l1
  rcases List.mem_cons.mp hp1 with rfl | hp2
  · exact varOfLit_bitOf a c.l2
  rcases List.mem_cons.mp hp2 with rfl | hp3
  · exact varOfLit_bitOf a c.l3
  · exact absurd hp3 List.not_mem_nil

/-- **Solution rows always agree.** Two clauses read by the same assignment can
never contradict each other, because both only ever report that assignment. -/
theorem pairsAgree_rowOfAssign (a : Assign) (c d : Clause) :
    pairsAgree (rowPairs c (rowOfAssign a c)) (rowPairs d (rowOfAssign a d)) = true := by
  simp only [pairsAgree, List.all_eq_true]
  intro x hx
  intro y hy
  have hxa := mem_rowPairs_rowOfAssign a c x hx
  have hya := mem_rowPairs_rowOfAssign a d y hy
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  by_cases hvar : x.1 = y.1
  · exact Or.inr (by rw [hxa, hya, hvar])
  · exact Or.inl hvar

theorem rowOk_rowOfAssign (a : Assign) (c : Clause) : rowOk c (rowOfAssign a c) = true :=
  pairsAgree_rowOfAssign a c c

/-- **A satisfied clause's row is one of the seven.** The all-false row is the
one the map omits, and it is exactly the row of an assignment that fails the
clause. -/
theorem mem_allRows_of_bits (x y z : Bool) (h : x = true ∨ y = true ∨ z = true) :
    4 * bitOf x + 2 * bitOf y + bitOf z ∈ allRows := by
  revert h
  cases x <;> cases y <;> cases z <;> decide

theorem rowOfAssign_mem_allRows (a : Assign) (c : Clause) (h : SatClause a c) :
    rowOfAssign a c ∈ allRows :=
  mem_allRows_of_bits _ _ _ h

theorem rowOfAssign_mem_initRows (a : Assign) (c : Clause) (h : SatClause a c) :
    rowOfAssign a c ∈ initRows c :=
  List.mem_filter.mpr ⟨rowOfAssign_mem_allRows a c h, rowOk_rowOfAssign a c⟩

-- ============================================================
-- The sweep
-- ============================================================

/-- The relations: one per clause, carrying the rows still allowed. -/
abbrev Rels := List (Clause × List Int)

def initRels (C : List Clause) : Rels := C.map (fun c => (c, initRows c))

/-- A row is **supported** when every relation has a row agreeing with it. -/
def supported (c : Clause) (r : Int) (rels : Rels) : Bool :=
  rels.all (fun q => q.2.any (fun w => pairsAgree (rowPairs c r) (rowPairs q.1 w)))

/-- **One semi-join sweep**: every relation keeps only its supported rows. -/
def sweep (rels : Rels) : Rels :=
  rels.map (fun cr => (cr.1, cr.2.filter (fun r => supported cr.1 r rels)))

def totalRows (rels : Rels) : Nat := (rels.map (fun cr => cr.2.length)).sum

/-- A sweep with the support test held fixed. Pulling the test out is what lets
the measure argument below be an induction on the list: `sweep` mentions the
whole of `rels` inside the test, this does not. -/
def sweepWith (p : Clause → Int → Bool) (rels : Rels) : Rels :=
  rels.map (fun cr => (cr.1, cr.2.filter (p cr.1)))

theorem sweep_eq_sweepWith (rels : Rels) :
    sweep rels = sweepWith (fun c r => supported c r rels) rels := rfl

/-- Filtering a list either leaves it alone or makes it strictly shorter. -/
theorem length_filter_lt {α : Type} (p : α → Bool) (l : List α) (h : l.filter p ≠ l) :
    (l.filter p).length < l.length := by
  rcases Nat.lt_or_ge (l.filter p).length l.length with hlt | hge
  · exact hlt
  · exact absurd (List.filter_sublist.eq_of_length
      (Nat.le_antisymm (List.Sublist.length_le List.filter_sublist) hge)) h

theorem totalRows_sweepWith_le (p : Clause → Int → Bool) :
    ∀ rels : Rels, totalRows (sweepWith p rels) ≤ totalRows rels := by
  intro rels
  induction rels with
  | nil => exact Nat.le_refl _
  | cons cr rest ih =>
    simp only [sweepWith, totalRows, List.map_cons, List.sum_cons] at ih ⊢
    exact Nat.add_le_add (List.Sublist.length_le List.filter_sublist) ih

/-- **A sweep that changes anything removes a row.** This is the measure the
fixpoint argument descends on. -/
theorem totalRows_sweepWith_lt (p : Clause → Int → Bool) :
    ∀ rels : Rels, sweepWith p rels ≠ rels → totalRows (sweepWith p rels) < totalRows rels := by
  intro rels
  induction rels with
  | nil => intro h; exact absurd rfl h
  | cons cr rest ih =>
    intro hne
    simp only [sweepWith, totalRows, List.map_cons, List.sum_cons]
    by_cases hhead : cr.2.filter (p cr.1) = cr.2
    · have htail : sweepWith p rest ≠ rest := by
        intro heq
        apply hne
        simp only [sweepWith, List.map_cons]
        rw [show (cr.1, cr.2.filter (p cr.1)) = cr from by rw [hhead]]
        simp only [sweepWith] at heq
        rw [heq]
      have := ih htail
      simp only [sweepWith, totalRows] at this
      rw [hhead]
      exact Nat.add_lt_add_left this _
    · have hlt := length_filter_lt (p cr.1) cr.2 hhead
      have hle := totalRows_sweepWith_le p rest
      simp only [sweepWith, totalRows] at hle
      exact Nat.add_lt_add_of_lt_of_le hlt hle

/-- Iterate to the fixpoint. A sweep that changes anything removes at least one
row, so `totalRows + 1` rounds suffice. -/
def reduceGo : Nat → Rels → Rels
  | 0, rels => rels
  | n + 1, rels => let rels' := sweep rels; if rels' = rels then rels else reduceGo n rels'

def reduce (rels : Rels) : Rels := reduceGo (totalRows rels + 1) rels

-- ============================================================
-- Conservation: the reducer never drops a solution's row
-- ============================================================

/-- A sweep keeps every clause, in order. -/
theorem clauses_sweep (rels : Rels) : (sweep rels).map (fun cr => cr.1) = rels.map (fun cr => cr.1) := by
  simp only [sweep, List.map_map, Function.comp_def]

/-- Carrying a solution: every relation still holds the row that solution
uses. -/
def Carries (a : Assign) (rels : Rels) : Prop :=
  ∀ cr ∈ rels, rowOfAssign a cr.1 ∈ cr.2

/-- **Conservation, one sweep.** A semi-join cannot drop a row a solution uses,
and it needs nothing of the formula to say so: the partner every such row needs
is the row the *same* solution uses in the other relation. -/
theorem Carries_sweep (a : Assign) (rels : Rels) (h : Carries a rels) :
    Carries a (sweep rels) := by
  intro cr hcr
  simp only [sweep, List.mem_map] at hcr
  obtain ⟨dr, hdr, rfl⟩ := hcr
  refine List.mem_filter.mpr ⟨h dr hdr, ?_⟩
  simp only [supported, List.all_eq_true]
  intro q hq
  exact List.any_eq_true.mpr ⟨rowOfAssign a q.1, h q hq, pairsAgree_rowOfAssign a dr.1 q.1⟩

/-- **Conservation, all the way to the fixpoint.** -/
theorem Carries_reduceGo (a : Assign) : ∀ (n : Nat) (rels : Rels), Carries a rels →
    Carries a (reduceGo n rels) := by
  intro n
  induction n with
  | zero => intro rels h; exact h
  | succ m ih =>
    intro rels h
    simp only [reduceGo]
    split
    · exact h
    · exact ih (sweep rels) (Carries_sweep a rels h)

theorem Carries_reduce (a : Assign) (rels : Rels) (h : Carries a rels) :
    Carries a (reduce rels) := Carries_reduceGo a _ rels h

/-- The relations of a formula start out carrying every solution of it. -/
theorem Carries_initRels (a : Assign) (C : List Clause) (h : ∀ c ∈ C, SatClause a c) :
    Carries a (initRels C) := by
  intro cr hcr
  simp only [initRels, List.mem_map] at hcr
  obtain ⟨c, hc, rfl⟩ := hcr
  exact rowOfAssign_mem_initRows a c (h c hc)

/-- **Conservation, stated where it is used.** For every assignment satisfying
the clauses, the reducer leaves each clause holding the row that assignment
uses. -/
theorem rowOfAssign_mem_reduce (a : Assign) (C : List Clause) (h : ∀ c ∈ C, SatClause a c) :
    ∀ cr ∈ reduce (initRels C), rowOfAssign a cr.1 ∈ cr.2 :=
  Carries_reduce a _ (Carries_initRels a C h)

/-- **A satisfiable prefix never leaves an empty relation.** The contrapositive
is the one the machine would use: an empty relation is a proof of
unsatisfiability, never an artefact of the reduction. -/
theorem reduce_ne_nil_of_sat (a : Assign) (C : List Clause) (h : ∀ c ∈ C, SatClause a c) :
    ∀ cr ∈ reduce (initRels C), cr.2 ≠ [] := by
  intro cr hcr hnil
  exact absurd (rowOfAssign_mem_reduce a C h cr hcr) (by rw [hnil]; exact List.not_mem_nil)

-- ============================================================
-- The fixpoint is arc consistent
-- ============================================================

/-- A map that leaves a list alone leaves each of its entries alone. -/
theorem eq_of_map_eq_self {α : Type} {f : α → α} :
    ∀ {l : List α}, l.map f = l → ∀ x ∈ l, f x = x := by
  intro l
  induction l with
  | nil => intro _ x hx; exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    intro heq x hx
    simp only [List.map_cons, List.cons.injEq] at heq
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact heq.1
    · exact ih heq.2 x hx'

/-- **The reduction reaches a fixpoint.** The fuel is enough: every sweep that
changes anything removes a row, and there are only so many rows. Without this
the arc-consistency result below would rest on a hypothesis nobody discharges. -/
theorem sweep_reduceGo : ∀ (n : Nat) (rels : Rels), totalRows rels < n →
    sweep (reduceGo n rels) = reduceGo n rels := by
  intro n
  induction n with
  | zero => intro rels h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro rels h
    simp only [reduceGo]
    split
    · next heq => exact heq
    · next hne' =>
      refine ih (sweep rels) ?_
      have hlt : totalRows (sweepWith (fun c r => supported c r rels) rels)
          < totalRows rels :=
        totalRows_sweepWith_lt _ rels (by rw [← sweep_eq_sweepWith]; exact hne')
      rw [← sweep_eq_sweepWith] at hlt
      omega

theorem sweep_reduce (rels : Rels) : sweep (reduce rels) = reduce rels :=
  sweep_reduceGo _ rels (Nat.lt_succ_self _)

/-- **Arc consistency, in the reducer's own terms.** At a fixpoint of the
sweep, every surviving row of every relation has a partner in every relation.
This is the premise BFMY asks for. `ArcConsistency.review_arcConsistent` proves
a statement of the same shape about the machine's owners tables — a different
object, and no implication either way is proved. -/
theorem arcConsistent_of_sweep_eq (rels : Rels) (hfix : sweep rels = rels) :
    ∀ cr ∈ rels, ∀ r ∈ cr.2, ∀ q ∈ rels,
      ∃ w ∈ q.2, pairsAgree (rowPairs cr.1 r) (rowPairs q.1 w) = true := by
  intro cr hcr r hr q hq
  -- at a fixpoint the sweep leaves every relation exactly as it found it
  have hself := eq_of_map_eq_self hfix cr hcr
  have hrows : cr.2.filter (fun x => supported cr.1 x rels) = cr.2 :=
    congrArg (fun p => p.2) hself
  have hsup : supported cr.1 r rels = true := by
    have : r ∈ cr.2.filter (fun x => supported cr.1 x rels) := by rw [hrows]; exact hr
    exact (List.mem_filter.mp this).2
  simp only [supported, List.all_eq_true] at hsup
  exact List.any_eq_true.mp (hsup q hq)

/-- **The reducer's own theorem, with nothing left hanging.** It terminates,
and where it stops every surviving row of every relation has a partner in every
relation. No acyclicity and no hypotheses — about the relations of a formula,
not about the machine's tables. -/
theorem arcConsistent_reduce (rels : Rels) :
    ∀ cr ∈ reduce rels, ∀ r ∈ cr.2, ∀ q ∈ reduce rels,
      ∃ w ∈ q.2, pairsAgree (rowPairs cr.1 r) (rowPairs q.1 w) = true :=
  arcConsistent_of_sweep_eq (reduce rels) (sweep_reduce rels)

/-- **Both halves at once, on a formula.** For a satisfiable list of clauses
the reducer stops at an arc-consistent fixpoint that still holds, in every
clause, the row each solution uses. -/
theorem reduce_sound (a : Assign) (C : List Clause) (h : ∀ c ∈ C, SatClause a c) :
    (∀ cr ∈ reduce (initRels C), rowOfAssign a cr.1 ∈ cr.2) ∧
    (∀ cr ∈ reduce (initRels C), ∀ r ∈ cr.2, ∀ q ∈ reduce (initRels C),
      ∃ w ∈ q.2, pairsAgree (rowPairs cr.1 r) (rowPairs q.1 w) = true) :=
  ⟨rowOfAssign_mem_reduce a C h, arcConsistent_reduce (initRels C)⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphMap.CnfReducer.rowOfAssign_mem_reduce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rowOfAssign_mem_reduce

/-- info: 'AbsSat.GraphMap.CnfReducer.reduce_ne_nil_of_sat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reduce_ne_nil_of_sat

/-- info: 'AbsSat.GraphMap.CnfReducer.arcConsistent_of_sweep_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arcConsistent_of_sweep_eq

/-- info: 'AbsSat.GraphMap.CnfReducer.arcConsistent_reduce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arcConsistent_reduce

/-- info: 'AbsSat.GraphMap.CnfReducer.reduce_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reduce_sound

end AbsSat.GraphMap.CnfReducer
