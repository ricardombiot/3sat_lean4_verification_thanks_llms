-- lean_project/AbsSat/GraphMap/CnfHypergraph.lean
import AbsSat.Cnf.Formula
import AbsSat.GraphMap.Hypergraph

/-!
# The constraint hypergraph of a **formula**, and the class of bounded scope

`Hypergraph.lean` (route E, v17) built the hypergraph of a **map** and measured
it: not α-acyclic, so Beeri–Fagin–Maier–Yannakakis does not apply to 3SAT in
general. That was the honest answer to a question about *every* formula, and it
has to stay answered that way — a positive result there would have been the
whole claim.

This module asks a strictly smaller question, the one v70 left open as
*demostrable*: **for which formulas does it apply?** The object is the
formula's own constraint hypergraph — one edge per clause, over the three
variables the clause names — and `BoundedScope φ K` says that hypergraph is
α-acyclic and that the GYO reduction empties it in at most `K` rounds.

## Why this hypergraph and not the map's

The map adds, per clause, a **clause step** that no other clause mentions. In
the hypergraph such a vertex occurs in exactly one edge, so the very first
`dropEars` strips it: the map's extra vertices cannot make an acyclic formula
cyclic. `Hypergraph.lean`'s own example pair shows both halves of this —
`[[1,2,3,100],[1,2,4,101]]` reduces while `[[1,2,3,100],[2,3,4,101],[1,3,4,102]]`
does not, "the cycle is the shared-variable structure of the CNF, not an
artefact of the construction". So the formula's hypergraph is where the
question actually lives.

## What `K` is for

α-acyclicity alone gives *global consistency from pairwise consistency*. The
clause filter needs more than a yes/no: the repair it performs when a literal
has to be flipped propagates from clause to clause, and the proof needs that
cascade to **terminate on a measure that does not grow with `φ.nVars`**. The
number of GYO rounds is that measure, and `gyoIter_gyoRounds` below is the
handle: `K` rounds of `gyoStep` empty the hypergraph.

`K` bounds *rounds*, not size. A disjoint union of arbitrarily many copies of
one small acyclic gadget has unbounded `nVars` and constant `gyoRounds`,
because every round peels every edge at once — which is what keeps the class
from being "small formulas only".

**Nothing here is claimed about formulas outside the class.** Parity over
expanders and large Tseitin formulas are exactly the ones whose hypergraph
keeps a cyclic core, and they stay outside; that is the point of the
definition, not a limitation hidden in it.
-/

namespace AbsSat.GraphMap.CnfHypergraph

open AbsSat.Cnf
open AbsSat.GraphMap.Hypergraph

-- ============================================================
-- The hypergraph of a CNF
-- ============================================================

/-- One clause's scope: the three variables it names, sorted and deduplicated
(a clause may repeat a variable under both polarities — `WF` allows it). -/
def clauseEdge (c : Clause) : Edge :=
  mkEdge [(c.l1.v : Int), (c.l2.v : Int), (c.l3.v : Int)]

/-- **The formula's constraint hypergraph**: one edge per clause, vertices are
variables. -/
def cnfEdges (φ : Cnf) : Hyper := φ.clauses.map clauseEdge

-- ============================================================
-- Counting the rounds of the reduction
-- ============================================================

/-- `gyoStep` applied `n` times, with no early exit. This is the iteration the
induction of a repair argument descends on; `gyoGo` is the same thing with a
fixpoint test, and the two agree at `gyoRounds` many steps. -/
def gyoIter : Nat → Hyper → Hyper
  | 0, h => h
  | n + 1, h => gyoIter n (gyoStep h)

/-- How many rounds `gyoGo` performs before it stalls. Mirrors `gyoGo`'s
recursion exactly, so the two cannot drift apart. -/
def gyoRoundsGo : Nat → Hyper → Nat
  | 0, _ => 0
  | n + 1, h => let h' := gyoStep h; if h' == h then 0 else gyoRoundsGo n h' + 1

/-- The number of effective GYO rounds, with `gyo`'s own fuel. -/
def gyoRounds (h : Hyper) : Nat := gyoRoundsGo (h.length + h.flatten.length + 1) h

/-- **The rounds count is the iteration count.** Running `gyoStep` exactly
`gyoRoundsGo n h` times reaches what `gyoGo n h` reaches — the early exit only
skips rounds that change nothing. -/
theorem gyoIter_gyoRoundsGo (n : Nat) (h : Hyper) :
    gyoIter (gyoRoundsGo n h) h = gyoGo n h := by
  induction n generalizing h with
  | zero => rfl
  | succ m ih =>
    simp only [gyoRoundsGo, gyoGo]
    split
    · rfl
    · simp only [gyoIter]
      exact ih (gyoStep h)

/-- The same, for the fuelled entry points. -/
theorem gyoIter_gyoRounds (h : Hyper) : gyoIter (gyoRounds h) h = gyo h :=
  gyoIter_gyoRoundsGo _ h

-- ============================================================
-- The class — over prefixes, because that is what the machine sees
-- ============================================================

/-! **Why prefixes, and not the formula alone.**

α-acyclicity is famously *not* hereditary: dropping an edge can turn an
α-acyclic hypergraph cyclic. The witness is two lines of this very code —
`{0,1}, {1,2}, {0,2}, {0,1,2}` reduces (the big edge subsumes the triangle)
while `{0,1}, {1,2}, {0,2}` does not. That is the whole reason β-acyclicity
exists.

It matters here because the machine processes clauses **in list order**: at the
clause step of clause `m` the state has seen `φ.clauses.take m` and nothing
more, and every chain of that state is a solution of *that* prefix
(`PrefixDecode.satUpTo_of_chain`). So a hypothesis about `φ` alone would not
reach the intermediate states where the clause filter actually runs. The class
asks for the property of every prefix.

Measured on the campaigns' own generator, the distinction costs nothing: of 800
random formulas, 281 are α-acyclic and the *same* 281 are prefix-acyclic — not
one is α-acyclic without being prefix-acyclic. It is the proof that needs the
stronger form, not the instances. -/

/-- The hypergraph of the first `m` clauses — what a state at clause step `m`
has seen. -/
def prefixEdges (φ : Cnf) (m : Nat) : Hyper :=
  cnfEdges { φ with clauses := φ.clauses.take m }

/-- Every prefix's hypergraph is α-acyclic. -/
def PrefixAcyclic (φ : Cnf) : Prop :=
  ∀ m ≤ φ.clauses.length, isAlphaAcyclic (prefixEdges φ m) = true

/-- **Bounded scope.** Every clause prefix has an α-acyclic constraint
hypergraph, and the GYO reduction empties each of them in at most `K` rounds.
`K` bounds rounds, not size: a disjoint union of copies of one gadget has
unbounded `nVars` and constant `K`. -/
def BoundedScope (φ : Cnf) (K : Nat) : Prop :=
  PrefixAcyclic φ ∧ ∀ m ≤ φ.clauses.length, gyoRounds (prefixEdges φ m) ≤ K

/-- The `Bool` form, for the measurement campaigns and for `decide`. -/
def boundedScopeB (φ : Cnf) (K : Nat) : Bool :=
  (List.range (φ.clauses.length + 1)).all (fun m =>
    isAlphaAcyclic (prefixEdges φ m) && Nat.ble (gyoRounds (prefixEdges φ m)) K)

theorem boundedScopeB_iff (φ : Cnf) (K : Nat) :
    boundedScopeB φ K = true ↔ BoundedScope φ K := by
  simp only [boundedScopeB, BoundedScope, PrefixAcyclic, List.all_eq_true, List.mem_range,
    Bool.and_eq_true, Nat.ble_eq, Nat.lt_succ_iff]
  constructor
  · intro h
    exact ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩
  · intro h m hm
    exact ⟨h.1 m hm, h.2 m hm⟩

instance (φ : Cnf) (K : Nat) : Decidable (BoundedScope φ K) :=
  decidable_of_decidable_of_iff (boundedScopeB_iff φ K)

/-- **What the class buys, stated once.** At every prefix — that is, at every
state where the clause filter runs — `K` rounds of the reduction leave
nothing. This is the finite measure a repair induction descends on, and it does
not mention `φ.nVars`. -/
theorem gyoIter_eq_nil_of_BoundedScope (φ : Cnf) (K : Nat) (h : BoundedScope φ K)
    (m : Nat) (hm : m ≤ φ.clauses.length) :
    ∃ r ≤ K, gyoIter r (prefixEdges φ m) = [] :=
  ⟨gyoRounds (prefixEdges φ m), h.2 m hm, by
    rw [gyoIter_gyoRounds]
    exact List.isEmpty_iff.mp (h.1 m hm)⟩

/-- The whole formula is the last prefix. -/
theorem alphaAcyclic_of_BoundedScope (φ : Cnf) (K : Nat) (h : BoundedScope φ K) :
    isAlphaAcyclic (cnfEdges φ) = true := by
  have := h.1 φ.clauses.length (Nat.le_refl _)
  simpa only [prefixEdges, List.take_length] using this

/-- A prefix of a prefix. -/
theorem prefixEdges_take (φ : Cnf) (n m : Nat) :
    prefixEdges { φ with clauses := φ.clauses.take n } m = prefixEdges φ (min m n) := by
  simp only [prefixEdges, cnfEdges, List.take_take, Nat.min_comm]

/-- **The class is closed under taking prefixes** — so an induction that walks
the clause steps of a run stays inside it. This is the form the machine needs:
at the clause step of clause `m` the state has seen `φ.clauses.take m`, and
that formula is in the class with the same `K`. -/
theorem BoundedScope_prefix (φ : Cnf) (K n : Nat) (h : BoundedScope φ K) :
    BoundedScope { φ with clauses := φ.clauses.take n } K := by
  have hlen : (φ.clauses.take n).length ≤ φ.clauses.length := by
    simp only [List.length_take]; omega
  constructor
  · intro m hm
    rw [prefixEdges_take]
    exact h.1 (min m n) (Nat.le_trans (Nat.le_trans (Nat.min_le_left m n) hm) hlen)
  · intro m hm
    rw [prefixEdges_take]
    exact h.2 (min m n) (Nat.le_trans (Nat.le_trans (Nat.min_le_left m n) hm) hlen)

-- ============================================================
-- Kernel-checked examples: the class is neither empty nor everything
-- ============================================================

section Examples

private def pl (v : Nat) : Lit := { v := v, pos := true }

private def cl (a b c : Nat) : Clause := { l1 := pl a, l2 := pl b, l3 := pl c }

/-- Two clauses sharing two variables: α-acyclic, two rounds. -/
example : BoundedScope { nVars := 4, clauses := [cl 0 1 2, cl 1 2 3] } 2 := by decide

/-- **The cycle that Tseitin builds.** Three clauses cycling over shared
variables have no ear and no containment — outside the class, at every `K`.
This is the shape parity formulas have, and why they stay out. -/
example : ¬ BoundedScope { nVars := 4, clauses := [cl 0 1 2, cl 1 2 3, cl 0 2 3] } 99 := by
  decide

/-- **The class does not mean "few variables".** Two disjoint copies of the
same gadget: twice the variables, same round count, because every round peels
every edge at once. -/
example : BoundedScope { nVars := 8, clauses := [cl 0 1 2, cl 1 2 3, cl 4 5 6, cl 5 6 7] } 2 := by
  decide

/-- Three gadgets, twelve variables, still two rounds. -/
example :
    BoundedScope
      { nVars := 12,
        clauses := [cl 0 1 2, cl 1 2 3, cl 4 5 6, cl 5 6 7, cl 8 9 10, cl 9 10 11] } 2 := by
  decide

/-- A star: one variable shared by four clauses, nine variables in all — the
round count still does not move. -/
example :
    BoundedScope
      { nVars := 9, clauses := [cl 0 1 2, cl 0 3 4, cl 0 5 6, cl 0 7 8] } 2 := by
  decide

end Examples

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphMap.CnfHypergraph.gyoIter_gyoRounds' does not depend on any axioms -/
#guard_msgs in
#print axioms gyoIter_gyoRounds

/-- info: 'AbsSat.GraphMap.CnfHypergraph.boundedScopeB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms boundedScopeB_iff

/-- info: 'AbsSat.GraphMap.CnfHypergraph.gyoIter_eq_nil_of_BoundedScope' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gyoIter_eq_nil_of_BoundedScope

end AbsSat.GraphMap.CnfHypergraph
