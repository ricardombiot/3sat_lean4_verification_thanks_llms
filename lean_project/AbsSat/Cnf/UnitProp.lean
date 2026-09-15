import AbsSat.Cnf.Formula

/-!
# Unit propagation

`Forced cls U l` — unit propagation derives the literal `l` from the clauses `cls` and the asserted
literals `U`: `l` is asserted, or some clause containing `l` has every other literal refuted.
`Conflict cls U` — some literal and its negation are both derived.

* `forced_true` — under an assignment satisfying `cls` and `U`, every derived literal is true;
* `not_conflict_of_model` — so a satisfiable set of clauses and units has no conflict;
* `conflict_of_clause` — a clause whose literals are all refuted gives a conflict;
* `forced_mono` — more clauses or more units derive more.

`Lit.vv` reads a literal as the `(variable, value)` pair the machine's ids fix: value `1` for a
positive literal, `0` for a negative one (`CnfChain.decode` reads index `1` as true).
-/

namespace AbsSat.Cnf

/-- The opposite literal. -/
def Lit.neg (l : Lit) : Lit := { l with pos := !l.pos }

theorem Lit.neg_neg (l : Lit) : l.neg.neg = l := by
  cases l with
  | mk v pos => cases pos <;> rfl

theorem Lit.neg_ne (l : Lit) : l.neg ≠ l := by
  cases l with
  | mk v pos => cases pos <;> simp [Lit.neg]

theorem litVal_neg (a : Assign) (l : Lit) : litVal a l.neg = !(litVal a l) := by
  cases l with
  | mk v pos => cases pos <;> simp [litVal, Lit.neg]

/-- The three literals of a clause. -/
def Clause.lits (c : Clause) : List Lit := [c.l1, c.l2, c.l3]

theorem satClause_iff (a : Assign) (c : Clause) :
    SatClause a c ↔ ∃ l ∈ c.lits, litVal a l = true := by
  simp [SatClause, Clause.lits]

/-- The `(variable, value)` pair a literal asserts. -/
def Lit.vv (l : Lit) : Int × Int := ((l.v : Int), if l.pos then 1 else 0)

theorem Lit.vv_neg (l : Lit) : l.neg.vv = (l.vv.1, 1 - l.vv.2) := by
  cases l with
  | mk v pos => cases pos <;> rfl

-- ============================================================
-- Unit propagation
-- ============================================================

/-- **The literals unit propagation derives** from the clauses `cls` and the asserted literals `U`. -/
inductive Forced (cls : List Clause) (U : List Lit) : Lit → Prop where
  | unit (l : Lit) (h : l ∈ U) : Forced cls U l
  | prop (c : Clause) (hc : c ∈ cls) (l : Lit) (hl : l ∈ c.lits)
      (h : ∀ l' ∈ c.lits, l' ≠ l → Forced cls U l'.neg) : Forced cls U l

/-- **Unit propagation reaches a contradiction.** -/
def Conflict (cls : List Clause) (U : List Lit) : Prop :=
  ∃ l, Forced cls U l ∧ Forced cls U l.neg

/-- **Every derived literal is true under a model of the clauses and the units.** -/
theorem forced_true {cls : List Clause} {U : List Lit} (a : Assign)
    (hcls : ∀ c ∈ cls, SatClause a c) (hU : ∀ l ∈ U, litVal a l = true) {l : Lit}
    (h : Forced cls U l) : litVal a l = true := by
  induction h with
  | unit l hl => exact hU l hl
  | prop c hc l hl _ ih =>
    obtain ⟨l0, hl0, hv⟩ := (satClause_iff a c).mp (hcls c hc)
    by_cases heq : l0 = l
    · rw [← heq]
      exact hv
    · have hneg := ih l0 hl0 heq
      rw [litVal_neg, hv] at hneg
      exact absurd hneg (by decide)

/-- **A model of the clauses and the units leaves no conflict.** -/
theorem not_conflict_of_model {cls : List Clause} {U : List Lit} (a : Assign)
    (hcls : ∀ c ∈ cls, SatClause a c) (hU : ∀ l ∈ U, litVal a l = true) : ¬ Conflict cls U := by
  intro ⟨l, h1, h2⟩
  have e1 := forced_true a hcls hU h1
  have e2 := forced_true a hcls hU h2
  rw [litVal_neg, e1] at e2
  exact absurd e2 (by decide)

/-- **A clause whose literals are all refuted is a conflict.** -/
theorem conflict_of_clause {cls : List Clause} {U : List Lit} (c : Clause) (hc : c ∈ cls)
    (h : ∀ l ∈ c.lits, Forced cls U l.neg) : Conflict cls U :=
  ⟨c.l1, Forced.prop c hc c.l1 (by simp [Clause.lits]) (fun l' hl' _ => h l' hl'),
    h c.l1 (by simp [Clause.lits])⟩

/-- **More clauses and more units derive more.** -/
theorem forced_mono {cls cls' : List Clause} {U U' : List Lit}
    (hc : ∀ c ∈ cls, c ∈ cls') (hu : ∀ l ∈ U, l ∈ U') {l : Lit} (h : Forced cls U l) :
    Forced cls' U' l := by
  induction h with
  | unit l hl => exact Forced.unit l (hu l hl)
  | prop c hcm l hl _ ih => exact Forced.prop c (hc c hcm) l hl ih

theorem conflict_mono {cls cls' : List Clause} {U U' : List Lit}
    (hc : ∀ c ∈ cls, c ∈ cls') (hu : ∀ l ∈ U, l ∈ U') (h : Conflict cls U) : Conflict cls' U' := by
  obtain ⟨l, h1, h2⟩ := h
  exact ⟨l, forced_mono hc hu h1, forced_mono hc hu h2⟩

/-- info: 'AbsSat.Cnf.forced_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms forced_true

/-- info: 'AbsSat.Cnf.not_conflict_of_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_conflict_of_model

/-- info: 'AbsSat.Cnf.conflict_of_clause' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conflict_of_clause

end AbsSat.Cnf
