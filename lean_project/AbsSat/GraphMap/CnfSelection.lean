-- lean_project/AbsSat/GraphMap/CnfSelection.lean
import AbsSat.GraphMap.CnfReducer
import AbsSat.GraphMap.CnfHypergraph

/-!
# Selections: what is left to decide once the reducer has run

v72 put the semi-join reducer in the pure model and proved the two halves that
need no acyclicity — it never drops a row a solution uses, and where it stops
every surviving row has a partner everywhere. This module asks what remains.

A **selection** is one row per clause. It is *agreeing* when its rows never
give the same variable two values. The two results here are:

* **A selection that agrees denotes a solution** (`sat_of_agreeing`). This is
  the Helly content, in the formula's own currency: a row pins a variable or
  says nothing about it, and `ZeroOneAll.helly` is the abstract reason
  pairwise agreement is enough. It needs no acyclicity and no reducer.
* **The reducer loses nothing** (`satisfiable_iff_agreeing_in_reduce`): a
  formula is satisfiable exactly when an agreeing selection exists **with
  every row drawn from the reduced relations**. The `→` half is v72's
  conservation; the `←` half is the first bullet.

Together they say precisely what the bounded-scope theorem still has to
deliver, and it is now a statement about *choosing*, with no sweeps and no
graphs in it:

> after the reducer, if no relation is empty, the surviving rows admit an
> agreeing selection.

That is Beeri–Fagin–Maier–Yannakakis, and `NoBacktrack` below states it. It is
where acyclicity has to be spent, because arc consistency alone does not give
it: v72 measured three Tseitin families whose odd-parity formulas keep every
relation non-empty and have no solution at all.

**It is not, however, all that stands between this file and `FlipCore`** — v74
retracts that claim. Everything here is about the relations of a formula;
`FlipCore` is about a machine state, a surviving node and a chain sound in its
`owners` tables. The bridge between the two does not exist yet, and it carries
the inclusion `owners ⊆ support` left open since v11. Proving `NoBacktrack`
alone would give the 1983 result that acyclic CSPs are tractable, and would say
nothing about the machine.
-/

namespace AbsSat.GraphMap.CnfSelection

open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfReducer
open AbsSat.GraphMap.CnfHypergraph

-- ============================================================
-- Selections and the assignment they denote
-- ============================================================

/-- Every variable/value pair a selection fixes. -/
def allPairs (sel : List (Clause × Int)) : List (Nat × Bool) :=
  sel.flatMap (fun p => rowPairs p.1 p.2)

/-- The pairs never give one variable two values. -/
def PairsCoherent (l : List (Nat × Bool)) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, x.1 = y.1 → x.2 = y.2

/-- A selection **agrees** when the rows it picks are coherent as a whole. -/
def Agreeing (sel : List (Clause × Int)) : Prop := PairsCoherent (allPairs sel)

/-- The assignment a selection denotes: a variable takes the value some picked
row gives it, and `false` where nothing names it. -/
def assignOfSel (sel : List (Clause × Int)) : Assign := fun v =>
  match (allPairs sel).find? (fun x => x.1 == v) with
  | some x => x.2
  | none => false

/-- Pairwise agreement of the rows is coherence of the pairs. This is the
shape `arcConsistent_reduce` hands over. -/
theorem Agreeing_of_pairwise (sel : List (Clause × Int))
    (h : ∀ p ∈ sel, ∀ q ∈ sel, pairsAgree (rowPairs p.1 p.2) (rowPairs q.1 q.2) = true) :
    Agreeing sel := by
  intro x hx y hy hvar
  obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
  obtain ⟨q, hq, hyq⟩ := List.mem_flatMap.mp hy
  have := h p hp q hq
  simp only [pairsAgree, List.all_eq_true] at this
  have hxy := this x hxp y hyq
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hxy
  rcases hxy with hne | heq
  · exact absurd hvar hne
  · exact heq

/-- **The denoted assignment gives every named variable the value its row
names.** -/
theorem assignOfSel_eq (sel : List (Clause × Int)) (hco : Agreeing sel)
    (v : Nat) (b : Bool) (hmem : (v, b) ∈ allPairs sel) : assignOfSel sel v = b := by
  simp only [assignOfSel]
  cases hfind : (allPairs sel).find? (fun x => x.1 == v) with
  | none =>
    have hno := List.find?_eq_none.mp hfind (v, b) hmem
    exact absurd (beq_iff_eq.mpr rfl : ((v, b).1 == v) = true) hno
  | some x =>
    have hx : x ∈ allPairs sel := List.mem_of_find?_eq_some hfind
    have hv : x.1 = v := by
      have := List.find?_some (p := fun x : Nat × Bool => x.1 == v) hfind
      exact eq_of_beq this
    exact hco x hx (v, b) hmem hv

-- ============================================================
-- A selection that agrees denotes a solution
-- ============================================================

/-- The pairs of a picked row are pairs of the selection. -/
theorem mem_allPairs (sel : List (Clause × Int)) (p : Clause × Int) (hp : p ∈ sel)
    (x : Nat × Bool) (hx : x ∈ rowPairs p.1 p.2) : x ∈ allPairs sel :=
  List.mem_flatMap.mpr ⟨p, hp, hx⟩

/-- A bit of `1` on a literal makes that literal true under the denoted
assignment. -/
theorem litVal_of_bit_eq_one (sel : List (Clause × Int)) (hco : Agreeing sel)
    (p : Clause × Int) (hp : p ∈ sel) (l : Lit) (bit : Int)
    (hx : (l.v, varOfLit l bit) ∈ rowPairs p.1 p.2) (hbit : bit = 1) :
    litVal (assignOfSel sel) l = true := by
  have hval : assignOfSel sel l.v = varOfLit l bit :=
    assignOfSel_eq sel hco l.v _ (mem_allPairs sel p hp _ hx)
  simp only [litVal, hval, varOfLit, hbit]
  cases l.pos <;> decide

/-- **A selection that agrees denotes a solution.** Every clause is satisfied,
because its row is one of the seven the map builds — never the all-false one —
and the denoted assignment reads every bit back unchanged. -/
theorem sat_of_agreeing (sel : List (Clause × Int)) (hco : Agreeing sel)
    (hrows : ∀ p ∈ sel, p.2 ∈ allRows) :
    ∀ p ∈ sel, SatClause (assignOfSel sel) p.1 := by
  intro p hp
  have hr := hrows p hp
  have hrange : 1 ≤ p.2 ∧ p.2 ≤ 7 := by
    simp only [allRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h <;> rw [h] <;> exact ⟨by omega, by omega⟩
  rcases bits_not_all_zero p.2 hrange.1 hrange.2 with hb | hb | hb
  · exact Or.inl (litVal_of_bit_eq_one sel hco p hp p.1.l1 (b1 p.2)
      (by simp only [rowPairs]; exact List.mem_cons_self) hb)
  · exact Or.inr (Or.inl (litVal_of_bit_eq_one sel hco p hp p.1.l2 (b2 p.2)
      (by simp only [rowPairs]; exact List.mem_cons_of_mem _ List.mem_cons_self) hb))
  · exact Or.inr (Or.inr (litVal_of_bit_eq_one sel hco p hp p.1.l3 (b3 p.2)
      (by simp only [rowPairs]; exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hb))

-- ============================================================
-- The rows the reducer leaves are still rows of the map
-- ============================================================

/-- Every row of every relation is one of the seven. -/
def RowsInAll (rels : Rels) : Prop := ∀ cr ∈ rels, ∀ r ∈ cr.2, r ∈ allRows

theorem RowsInAll_initRels (C : List Clause) : RowsInAll (initRels C) := by
  intro cr hcr r hr
  simp only [initRels, List.mem_map] at hcr
  obtain ⟨c, _, rfl⟩ := hcr
  exact (List.mem_filter.mp hr).1

theorem RowsInAll_sweep (rels : Rels) (h : RowsInAll rels) : RowsInAll (sweep rels) := by
  intro cr hcr r hr
  simp only [sweep, List.mem_map] at hcr
  obtain ⟨dr, hdr, rfl⟩ := hcr
  exact h dr hdr r (List.mem_filter.mp hr).1

theorem RowsInAll_reduceGo : ∀ (n : Nat) (rels : Rels), RowsInAll rels →
    RowsInAll (reduceGo n rels) := by
  intro n
  induction n with
  | zero => intro rels h; exact h
  | succ m ih =>
    intro rels h
    simp only [reduceGo]
    split
    · exact h
    · exact ih (sweep rels) (RowsInAll_sweep rels h)

theorem RowsInAll_reduce (C : List Clause) : RowsInAll (reduce (initRels C)) :=
  RowsInAll_reduceGo _ _ (RowsInAll_initRels C)

/-- The relations keep their clauses, in order, all the way to the fixpoint. -/
theorem clauses_reduceGo : ∀ (n : Nat) (rels : Rels),
    (reduceGo n rels).map (fun cr => cr.1) = rels.map (fun cr => cr.1) := by
  intro n
  induction n with
  | zero => intro rels; rfl
  | succ m ih =>
    intro rels
    simp only [reduceGo]
    split
    · rfl
    · rw [ih (sweep rels), clauses_sweep]

theorem clauses_reduce (rels : Rels) :
    (reduce rels).map (fun cr => cr.1) = rels.map (fun cr => cr.1) := clauses_reduceGo _ rels

-- ============================================================
-- The reducer loses nothing: the iff
-- ============================================================

/-- A selection **drawn from** the relations: one row per relation, taken from
that relation's surviving rows. -/
def DrawnFrom (sel : List (Clause × Int)) (rels : Rels) : Prop :=
  sel.length = rels.length ∧
  ∀ i : Nat, ∀ p ∈ sel[i]?, ∀ cr ∈ rels[i]?, p.1 = cr.1 ∧ p.2 ∈ cr.2

/-- The selection a solution induces, on the clauses of `C`. -/
def selOfAssign (a : Assign) (C : List Clause) : List (Clause × Int) :=
  C.map (fun c => (c, rowOfAssign a c))

theorem map_fst_initRels (C : List Clause) :
    (initRels C).map (fun cr => cr.1) = C := by
  induction C with
  | nil => rfl
  | cons c cs ih =>
    simp only [initRels, List.map_cons] at ih ⊢
    rw [ih]

theorem map_fst_selOfAssign (a : Assign) (C : List Clause) :
    (selOfAssign a C).map (fun p => p.1) = C := by
  induction C with
  | nil => rfl
  | cons c cs ih =>
    simp only [selOfAssign, List.map_cons] at ih ⊢
    rw [ih]

theorem mem_selOfAssign (a : Assign) (C : List Clause) (p : Clause × Int)
    (hp : p ∈ selOfAssign a C) : p.1 ∈ C ∧ p.2 = rowOfAssign a p.1 := by
  simp only [selOfAssign, List.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  exact ⟨hc, rfl⟩

/-- A solution's own selection agrees. -/
theorem Agreeing_selOfAssign (a : Assign) (C : List Clause) :
    Agreeing (selOfAssign a C) := by
  refine Agreeing_of_pairwise _ (fun p hp q hq => ?_)
  obtain ⟨_, hpr⟩ := mem_selOfAssign a C p hp
  obtain ⟨_, hqr⟩ := mem_selOfAssign a C q hq
  rw [hpr, hqr]
  exact pairsAgree_rowOfAssign a p.1 q.1

/-- **What is left to decide, named.** After the reducer, an agreeing choice
among the surviving rows exists. This is Beeri–Fagin–Maier–Yannakakis in the
narrowest form this development needs: no sweeps, no graph, just *choosing*.
Arc consistency alone does not give it — the odd-parity Tseitin formulas keep
every relation non-empty and have no solution — so this is exactly where
`BoundedScope` has to be spent. -/
def NoBacktrack (C : List Clause) : Prop :=
  (∀ cr ∈ reduce (initRels C), cr.2 ≠ []) →
    ∃ sel : List (Clause × Int),
      sel.map (fun p => p.1) = C ∧ Agreeing sel ∧
      ∀ p ∈ sel, ∃ cr ∈ reduce (initRels C), cr.1 = p.1 ∧ p.2 ∈ cr.2

/-- **Half of the bridge, unconditionally: an agreeing selection is a
solution.** -/
theorem satisfiable_of_agreeing (C : List Clause) (sel : List (Clause × Int))
    (hcl : sel.map (fun p => p.1) = C) (hco : Agreeing sel)
    (hrows : ∀ p ∈ sel, p.2 ∈ allRows) :
    ∃ a : Assign, ∀ c ∈ C, SatClause a c := by
  refine ⟨assignOfSel sel, ?_⟩
  intro c hc
  rw [← hcl] at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact sat_of_agreeing sel hco hrows p hp

/-- **The other half: a solution's rows survive the reducer and agree.** -/
theorem agreeing_of_satisfiable (C : List Clause) (a : Assign)
    (hsat : ∀ c ∈ C, SatClause a c) :
    (selOfAssign a C).map (fun p => p.1) = C ∧ Agreeing (selOfAssign a C) ∧
      ∀ p ∈ selOfAssign a C, ∃ cr ∈ reduce (initRels C), cr.1 = p.1 ∧ p.2 ∈ cr.2 := by
  refine ⟨map_fst_selOfAssign a C, Agreeing_selOfAssign a C, ?_⟩
  intro p hp
  obtain ⟨hc, hrow⟩ := mem_selOfAssign a C p hp
  -- the clause is still carried by some relation of the fixpoint
  have hcl : p.1 ∈ (reduce (initRels C)).map (fun cr => cr.1) := by
    rw [clauses_reduce, map_fst_initRels]; exact hc
  obtain ⟨cr, hcr, hcr1⟩ := List.mem_map.mp hcl
  exact ⟨cr, hcr, hcr1, by rw [hrow, ← hcr1]; exact rowOfAssign_mem_reduce a C hsat cr hcr⟩

/-- **The reducer loses nothing.** A list of clauses is satisfiable exactly
when an agreeing selection exists with every row drawn from the reduced
relations. Searching inside the fixpoint is therefore no weaker than searching
everywhere — which is what makes `NoBacktrack` the whole of what remains. -/
theorem satisfiable_iff_agreeing_in_reduce (C : List Clause) :
    (∃ a : Assign, ∀ c ∈ C, SatClause a c) ↔
    (∃ sel : List (Clause × Int),
      sel.map (fun p => p.1) = C ∧ Agreeing sel ∧
      ∀ p ∈ sel, ∃ cr ∈ reduce (initRels C), cr.1 = p.1 ∧ p.2 ∈ cr.2) := by
  constructor
  · rintro ⟨a, hsat⟩
    exact ⟨selOfAssign a C, agreeing_of_satisfiable C a hsat⟩
  · rintro ⟨sel, hcl, hco, hdraw⟩
    refine satisfiable_of_agreeing C sel hcl hco (fun p hp => ?_)
    obtain ⟨cr, hcr, _, hmem⟩ := hdraw p hp
    exact RowsInAll_reduce C cr hcr p.2 hmem

/-- **And so: the class decides, from `NoBacktrack` alone.** Inside a formula
for which the remaining obligation holds, an empty relation is exactly
unsatisfiability — the `←` half is v72's conservation, already proved. -/
theorem satisfiable_iff_nonempty_of_NoBacktrack (C : List Clause) (h : NoBacktrack C) :
    (∃ a : Assign, ∀ c ∈ C, SatClause a c) ↔ ∀ cr ∈ reduce (initRels C), cr.2 ≠ [] := by
  constructor
  · rintro ⟨a, hsat⟩
    exact reduce_ne_nil_of_sat a C hsat
  · intro hne
    exact (satisfiable_iff_agreeing_in_reduce C).mpr (h hne)

-- ============================================================
-- The base case: where the reducer leaves no choice
-- ============================================================

/-! The obligation splits the way this development has split every obligation
before it — a case with no choice, and a case with one. v19 and v40 did exactly
this for the machine (`NoChoice`, then `pairwiseOwned_of_fullyPinned`: in a
fully pinned state there is one node per step, and pairwise ownership follows
for free). The same thing happens here — as a resemblance of arguments, not as
a transfer of results — and it is the base case of the descent the next piece
has to build. -/

/-- The selection a relation set forces, when each relation offers one row. -/
def forcedSel (rels : Rels) : List (Clause × Int) :=
  rels.filterMap (fun cr => cr.2.head?.map (fun r => (cr.1, r)))

theorem mem_forcedSel (rels : Rels) (p : Clause × Int) (hp : p ∈ forcedSel rels) :
    ∃ cr ∈ rels, cr.1 = p.1 ∧ p.2 ∈ cr.2 := by
  simp only [forcedSel, List.mem_filterMap] at hp
  obtain ⟨cr, hcr, hmap⟩ := hp
  cases hh : cr.2.head? with
  | none => rw [hh] at hmap; exact absurd hmap (by simp)
  | some r =>
    rw [hh] at hmap
    simp only [Option.map_some, Option.some.injEq] at hmap
    exact ⟨cr, hcr, by rw [← hmap], by rw [← hmap]; exact List.mem_of_mem_head? hh⟩

/-- With every relation non-empty, the forced selection covers every clause. -/
theorem map_fst_forcedSel (rels : Rels) (hne : ∀ cr ∈ rels, cr.2 ≠ []) :
    (forcedSel rels).map (fun p => p.1) = rels.map (fun cr => cr.1) := by
  induction rels with
  | nil => rfl
  | cons cr rest ih =>
    have hcr : cr.2 ≠ [] := hne cr List.mem_cons_self
    cases hh : cr.2 with
    | nil => exact absurd hh hcr
    | cons r rows =>
      simp only [forcedSel, List.filterMap_cons, hh, List.head?_cons, Option.map_some,
        List.map_cons]
      rw [show (List.filterMap (fun cr => cr.2.head?.map (fun r => (cr.1, r))) rest)
          = forcedSel rest from rfl,
        ih (fun x hx => hne x (List.mem_cons_of_mem _ hx))]

/-- **The base case, proved.** Where the reducer leaves one row per relation,
the forced selection agrees — arc consistency has to point at that one row,
because there is nothing else to point at. -/
theorem Agreeing_forcedSel (rels : Rels)
    (hac : ∀ cr ∈ rels, ∀ r ∈ cr.2, ∀ q ∈ rels,
      ∃ w ∈ q.2, pairsAgree (rowPairs cr.1 r) (rowPairs q.1 w) = true)
    (hsingle : ∀ cr ∈ rels, ∀ r ∈ cr.2, ∀ r' ∈ cr.2, r = r') :
    Agreeing (forcedSel rels) := by
  refine Agreeing_of_pairwise _ (fun p hp q hq => ?_)
  obtain ⟨cr, hcr, hcr1, hcr2⟩ := mem_forcedSel rels p hp
  obtain ⟨dr, hdr, hdr1, hdr2⟩ := mem_forcedSel rels q hq
  obtain ⟨w, hw, hagree⟩ := hac cr hcr p.2 hcr2 dr hdr
  have hwq : w = q.2 := hsingle dr hdr w hw q.2 hdr2
  rw [← hcr1, ← hdr1, ← hwq]
  exact hagree

/-- **And so the remaining obligation holds wherever the reducer pins
everything.** -/
theorem NoBacktrack_of_singletons (C : List Clause)
    (hsingle : ∀ cr ∈ reduce (initRels C), ∀ r ∈ cr.2, ∀ r' ∈ cr.2, r = r') :
    NoBacktrack C := by
  intro hne
  refine ⟨forcedSel (reduce (initRels C)), ?_, ?_, ?_⟩
  · rw [map_fst_forcedSel _ hne, clauses_reduce, map_fst_initRels]
  · exact Agreeing_forcedSel _ (arcConsistent_reduce (initRels C)) hsingle
  · intro p hp
    obtain ⟨cr, hcr, h1, h2⟩ := mem_forcedSel _ p hp
    exact ⟨cr, hcr, h1, h2⟩

/-- The decision procedure on a pinned formula, with nothing assumed. -/
theorem satisfiable_iff_nonempty_of_singletons (C : List Clause)
    (hsingle : ∀ cr ∈ reduce (initRels C), ∀ r ∈ cr.2, ∀ r' ∈ cr.2, r = r') :
    (∃ a : Assign, ∀ c ∈ C, SatClause a c) ↔ ∀ cr ∈ reduce (initRels C), cr.2 ≠ [] :=
  satisfiable_iff_nonempty_of_NoBacktrack C (NoBacktrack_of_singletons C hsingle)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphMap.CnfSelection.sat_of_agreeing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_agreeing

/-- info: 'AbsSat.GraphMap.CnfSelection.satisfiable_iff_agreeing_in_reduce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms satisfiable_iff_agreeing_in_reduce

/-- info: 'AbsSat.GraphMap.CnfSelection.satisfiable_iff_nonempty_of_NoBacktrack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms satisfiable_iff_nonempty_of_NoBacktrack

/-- info: 'AbsSat.GraphMap.CnfSelection.Agreeing_forcedSel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agreeing_forcedSel

/-- info: 'AbsSat.GraphMap.CnfSelection.NoBacktrack_of_singletons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NoBacktrack_of_singletons

end AbsSat.GraphMap.CnfSelection
