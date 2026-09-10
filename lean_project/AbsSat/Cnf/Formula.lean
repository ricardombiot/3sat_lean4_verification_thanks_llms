-- lean_project/AbsSat/Cnf/Formula.lean

/-!
# 3SAT: the formula, and what it means to satisfy one

**Nothing in this development said what a 3SAT formula *is*.** Every theorem
proved so far — the owners invariants, the chain results, L1 — talks about a
graph. `Verdict.lean` says so plainly: *"Nothing here connects `denot` to
satisfying assignments of the original CNF."* This module is the first half of
that missing link (the v49 report calls it links 1 and 4 of five).

The design is deliberately small, and every choice is made for the proofs that
consume it:

* **`Lit.v` is 0-based.** The map puts variable `v` at step `2v` and its
  negation at `2v+1`, so a 0-based index makes every step a multiplication with
  no truncated `Nat` subtraction anywhere. DIMACS's 1-based numbering is
  converted once, at the parser boundary.
* **A clause is a triple, not a list.** There is no length side condition to
  carry, functionality of a requirement set is a 3×3 case split rather than a
  list induction, and the three fields line up one-for-one with the three
  `add_require!` calls of `GraphMap.add_gate_case!`.
* **`Assign` is `Nat → Bool`, total.** No `size` hypothesis, no `getElem`
  obligation, and the decoder can be a plain lambda. The `Array Bool` the mirror
  reader produces converts at the harness boundary only, never inside a proof.

**No `Std.HashSet` here, or anywhere downstream.** `MapReqs.lean`'s three
theorems carry `Classical.choice` purely because they use
`Std.HashSet.mem_insert`; keeping this side of the bridge free of hash sets is
what keeps its closure at `[propext, Quot.sound]` or tighter.
-/

namespace AbsSat.Cnf

-- ============================================================
-- Syntax
-- ============================================================

/-- A literal: a **0-based** variable index and a polarity. -/
structure Lit where
  v   : Nat
  pos : Bool
  deriving DecidableEq, Repr

/-- The map step a literal points at: `2v` for a positive literal, `2v+1` for a
negated one. This is `GraphMap.get_step_var`'s `+1` rule, as arithmetic. -/
def Lit.step (l : Lit) : Int := 2 * (l.v : Int) + (if l.pos then 0 else 1)

/-- A 3-clause, as a triple. -/
structure Clause where
  l1 : Lit
  l2 : Lit
  l3 : Lit
  deriving DecidableEq, Repr

structure Cnf where
  nVars   : Nat
  clauses : List Clause
  deriving Repr

-- ============================================================
-- Semantics
-- ============================================================

/-- A total truth assignment, indexed the way `Lit.v` is. -/
abbrev Assign := Nat → Bool

def litVal (a : Assign) (l : Lit) : Bool :=
  if l.pos then a l.v else !(a l.v)

def SatClause (a : Assign) (c : Clause) : Prop :=
  litVal a c.l1 = true ∨ litVal a c.l2 = true ∨ litVal a c.l3 = true

def Sat (a : Assign) (φ : Cnf) : Prop := ∀ c ∈ φ.clauses, SatClause a c

def Satisfiable (φ : Cnf) : Prop := ∃ a : Assign, Sat a φ

/-- The `Bool` evaluator, for `#guard` and for the differential harness.
`Sat` is decidable; `Satisfiable` is **not**, and must never be `decide`d. -/
def satB (a : Assign) (φ : Cnf) : Bool :=
  φ.clauses.all fun c => litVal a c.l1 || litVal a c.l2 || litVal a c.l3

theorem satB_iff (a : Assign) (φ : Cnf) : satB a φ = true ↔ Sat a φ := by
  simp only [satB, Sat, SatClause, List.all_eq_true, Bool.or_eq_true, or_assoc]

-- ============================================================
-- Well-formedness
-- ============================================================

/-- What the map needs of a clause, and no more.

The **bound** half makes a literal's step land below the clause's own step, so
requirements point backwards. The **distinct-steps** half is exactly
`GraphMap.MapReqs.Functional`'s hypothesis: two requirements at the same step
must coincide.

Note this is *distinct steps*, not *distinct variables* — strictly weaker, and
it admits `x ∨ ¬x ∨ y`, which the importer already encodes correctly (`x` goes
to step `2v`, `¬x` to `2v+1`). What it excludes is a repeated literal of the
same polarity, which `MapReqs.repeated_literal_not_functional` shows the
encoding genuinely cannot represent. -/
def Clause.WF (n : Nat) (c : Clause) : Prop :=
  (c.l1.v < n ∧ c.l2.v < n ∧ c.l3.v < n) ∧
  (c.l1.step ≠ c.l2.step ∧ c.l1.step ≠ c.l3.step ∧ c.l2.step ≠ c.l3.step)

def WF (φ : Cnf) : Prop := ∀ c ∈ φ.clauses, Clause.WF φ.nVars c

/-- Distinct variables is the stronger, more familiar reading. -/
theorem Clause.WF_of_distinct_vars (n : Nat) (c : Clause)
    (hb : c.l1.v < n ∧ c.l2.v < n ∧ c.l3.v < n)
    (h12 : c.l1.v ≠ c.l2.v) (h13 : c.l1.v ≠ c.l3.v) (h23 : c.l2.v ≠ c.l3.v) :
    Clause.WF n c := by
  refine ⟨hb, ?_, ?_, ?_⟩ <;>
    · simp only [Lit.step]
      intro hstep
      split at hstep <;> split at hstep <;> omega

-- ============================================================
-- List plumbing the decode direction consumes
-- ============================================================

theorem exists_index_of_mem {α : Type} (l : List α) (x : α) (h : x ∈ l) :
    ∃ j, j < l.length ∧ l[j]? = some x := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨0, Nat.succ_pos _, rfl⟩
    · obtain ⟨j, hjlt, hj⟩ := ih h'
      refine ⟨j + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [List.getElem?_cons_succ]
      exact hj

theorem satClause_of_getElem? (a : Assign) (φ : Cnf) (h : Sat a φ)
    (j : Nat) (c : Clause) (hj : φ.clauses[j]? = some c) : SatClause a c :=
  h c (List.mem_of_getElem? hj)

theorem wf_of_getElem? (φ : Cnf) (h : WF φ) (j : Nat) (c : Clause)
    (hj : φ.clauses[j]? = some c) : Clause.WF φ.nVars c :=
  h c (List.mem_of_getElem? hj)

-- ============================================================
-- Satisfaction only reads the variables the formula has
-- ============================================================

theorem litVal_congr (a b : Assign) (l : Lit) (h : a l.v = b l.v) :
    litVal a l = litVal b l := by
  simp only [litVal, h]

theorem sat_congr_below (φ : Cnf) (hwf : WF φ) (a b : Assign)
    (h : ∀ i, i < φ.nVars → a i = b i) : Sat a φ → Sat b φ := by
  intro hsat c hc
  obtain ⟨⟨h1, h2, h3⟩, _⟩ := hwf c hc
  have e1 := litVal_congr a b c.l1 (h c.l1.v h1)
  have e2 := litVal_congr a b c.l2 (h c.l2.v h2)
  have e3 := litVal_congr a b c.l3 (h c.l3.v h3)
  rcases hsat c hc with hh | hh | hh
  · exact Or.inl (by rw [← e1]; exact hh)
  · exact Or.inr (Or.inl (by rw [← e2]; exact hh))
  · exact Or.inr (Or.inr (by rw [← e3]; exact hh))

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.Cnf.satB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms satB_iff

/-- info: 'AbsSat.Cnf.sat_congr_below' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sat_congr_below

end AbsSat.Cnf
