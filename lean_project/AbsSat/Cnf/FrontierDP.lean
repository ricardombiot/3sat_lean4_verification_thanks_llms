-- lean_project/AbsSat/Cnf/FrontierDP.lean
import AbsSat.Cnf.ClauseOrder

/-!
# The frontier invariant, as a theorem about CNF

Walk the clauses of `φ` in order. After the first `j` clauses, the **frontier** is the
set of variables occurring both in those `j` clauses and in the remaining ones.

`InT φ j τ` says the frontier values of `τ` extend to an assignment satisfying the first
`j` clauses. This is the exact table the frontier remembers: only the frontier values of
`τ` matter.

**The step** (`inT_succ`). Extending by clause `j` and forgetting what leaves the frontier
is exact: `τ'` is in the table after `j + 1` clauses iff some `b` in the table after `j`
satisfies clause `j` and agrees with `τ'` on the new frontier.

The proof is the running intersection of the frontier: a variable of the first `j`
clauses that also occurs in clause `j` or later is on the frontier after `j`, so an
assignment for the prefix and one for the new clause can be glued on it.

**The ends.** Every `τ` is in the table after no clauses (`inT_zero`), and after all of
them the frontier is empty and the table is non-empty iff `φ` is satisfiable
(`inT_all_iff`). So an empty table at any step is a proof of unsatisfiability.

Nothing here mentions the machine: this is the object a proof about the machine's
emptiness can aim at.
-/

namespace AbsSat.Cnf.FrontierDP

open AbsSat.Cnf
open AbsSat.Cnf.ClauseOrder (vars varsOf)

-- ============================================================
-- Definitions
-- ============================================================

def prefixVars (φ : Cnf) (j : Nat) : List Nat := varsOf (φ.clauses.take j)

def suffixVars (φ : Cnf) (j : Nat) : List Nat := varsOf (φ.clauses.drop j)

/-- `v` is on the frontier after the first `j` clauses. -/
def Frontier (φ : Cnf) (j : Nat) (v : Nat) : Prop := v ∈ prefixVars φ j ∧ v ∈ suffixVars φ j

def SatPrefix (a : Assign) (φ : Cnf) (j : Nat) : Prop := ∀ c ∈ φ.clauses.take j, SatClause a c

/-- **The frontier table.** The frontier values of `τ` extend to a model of the first `j` clauses. -/
def InT (φ : Cnf) (j : Nat) (τ : Assign) : Prop :=
  ∃ a, SatPrefix a φ j ∧ ∀ v, Frontier φ j v → a v = τ v

/-- **One step of the table**: extend by clause `j`, forget what leaves the frontier. -/
def StepT (φ : Cnf) (j : Nat) (P : Assign → Prop) (τ' : Assign) : Prop :=
  ∃ c, φ.clauses[j]? = some c ∧ ∃ b, P b ∧ SatClause b c ∧ ∀ v, Frontier φ (j + 1) v → b v = τ' v

-- ============================================================
-- List plumbing
-- ============================================================

theorem mem_varsOf {cs : List Clause} {v : Nat} : v ∈ varsOf cs ↔ ∃ c ∈ cs, v ∈ vars c := by
  unfold varsOf
  exact List.mem_flatMap

theorem take_succ_of_get (cs : List Clause) (j : Nat) (c : Clause) (hc : cs[j]? = some c) :
    cs.take (j + 1) = cs.take j ++ [c] := by
  rw [List.take_add_one, hc]
  rfl

theorem mem_drop_of_get (cs : List Clause) (j : Nat) (c : Clause) (hc : cs[j]? = some c) :
    c ∈ cs.drop j := by
  have hj : j < cs.length := by
    cases Nat.lt_or_ge j cs.length with
    | inl h => exact h
    | inr h => rw [List.getElem?_eq_none h] at hc; cases hc
  rw [List.drop_eq_getElem_cons hj]
  have : cs[j] = c := by
    have h2 : cs[j]? = some cs[j] := List.getElem?_eq_getElem hj
    rw [hc] at h2
    exact (Option.some.inj h2).symm
  rw [this]
  exact List.mem_cons_self

theorem mem_drop_succ (cs : List Clause) (j : Nat) (c : Clause) (h : c ∈ cs.drop (j + 1)) :
    c ∈ cs.drop j := by
  rw [← List.drop_drop] at h
  exact List.mem_of_mem_drop h

theorem suffix_succ_sub (φ : Cnf) (j : Nat) (v : Nat) (h : v ∈ suffixVars φ (j + 1)) :
    v ∈ suffixVars φ j := by
  obtain ⟨c, hc, hv⟩ := mem_varsOf.mp h
  exact mem_varsOf.mpr ⟨c, mem_drop_succ φ.clauses j c hc, hv⟩

-- ============================================================
-- A clause only reads its own variables
-- ============================================================

theorem litVal_congr (a b : Assign) (l : Lit) (h : a l.v = b l.v) : litVal a l = litVal b l := by
  unfold litVal
  rw [h]

theorem satClause_congr (a b : Assign) (c : Clause) (h : ∀ v ∈ vars c, a v = b v)
    (hs : SatClause a c) : SatClause b c := by
  have h1 := litVal_congr a b c.l1 (h _ (by simp [vars]))
  have h2 := litVal_congr a b c.l2 (h _ (by simp [vars]))
  have h3 := litVal_congr a b c.l3 (h _ (by simp [vars]))
  unfold SatClause at hs ⊢
  rw [← h1, ← h2, ← h3]
  exact hs

-- ============================================================
-- The step is exact
-- ============================================================

/-- **The frontier step is exact.** -/
theorem inT_succ (φ : Cnf) (j : Nat) (hj : j < φ.clauses.length) (τ' : Assign) :
    InT φ (j + 1) τ' ↔ StepT φ j (InT φ j) τ' := by
  obtain ⟨c, hc⟩ : ∃ c, φ.clauses[j]? = some c := ⟨φ.clauses[j], List.getElem?_eq_getElem hj⟩
  have htake := take_succ_of_get φ.clauses j c hc
  constructor
  · rintro ⟨a, hsat, hag⟩
    refine ⟨c, hc, a, ⟨a, fun c' hc' => hsat c' ?_, fun _ _ => rfl⟩, hsat c ?_, hag⟩
    · rw [htake]; exact List.mem_append_left _ hc'
    · rw [htake]; exact List.mem_append_right _ List.mem_cons_self
  · rintro ⟨c₀, hc₀, b, ⟨a, hsat, hag⟩, hcl, hτ⟩
    rw [hc] at hc₀
    obtain rfl := Option.some.inj hc₀
    let a' : Assign := fun v => if v ∈ prefixVars φ j then a v else b v
    have hcd : c ∈ φ.clauses.drop j := mem_drop_of_get φ.clauses j c hc
    refine ⟨a', ?_, ?_⟩
    · intro c' hc'
      rw [htake] at hc'
      rcases List.mem_append.mp hc' with hin | hin
      · -- a clause of the prefix: a' is a there
        refine satClause_congr a a' c' (fun v hv => ?_) (hsat c' hin)
        have hp : v ∈ prefixVars φ j := mem_varsOf.mpr ⟨c', hin, hv⟩
        show a v = (if v ∈ prefixVars φ j then a v else b v)
        rw [if_pos hp]
      · -- the new clause: a' is b there, by the running intersection
        rcases List.mem_singleton.mp hin with rfl
        refine satClause_congr b a' c' (fun v hv => ?_) hcl
        show b v = (if v ∈ prefixVars φ j then a v else b v)
        by_cases hp : v ∈ prefixVars φ j
        · rw [if_pos hp]
          exact (hag v ⟨hp, mem_varsOf.mpr ⟨c', hcd, hv⟩⟩).symm
        · rw [if_neg hp]
    · intro v ⟨hp1, hs⟩
      show (if v ∈ prefixVars φ j then a v else b v) = τ' v
      by_cases hp : v ∈ prefixVars φ j
      · rw [if_pos hp]
        rw [hag v ⟨hp, suffix_succ_sub φ j v hs⟩]
        exact hτ v ⟨hp1, hs⟩
      · rw [if_neg hp]
        exact hτ v ⟨hp1, hs⟩

-- ============================================================
-- The two ends
-- ============================================================

theorem inT_zero (φ : Cnf) (τ : Assign) : InT φ 0 τ := by
  refine ⟨τ, fun c hc => ?_, fun _ _ => rfl⟩
  simp at hc

theorem inT_all_iff (φ : Cnf) (τ : Assign) : InT φ φ.clauses.length τ ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, hsat, _⟩
    exact ⟨a, fun c hc => hsat c (by rw [List.take_length]; exact hc)⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, fun c hc => ha c (by rw [List.take_length] at hc; exact hc), fun v ⟨_, hs⟩ => ?_⟩
    obtain ⟨c, hc, _⟩ := mem_varsOf.mp hs
    simp at hc

/-- **An empty table refutes.** If no `τ` is in the table after `j` clauses, `φ` is unsatisfiable. -/
theorem unsat_of_empty (φ : Cnf) (j : Nat)
    (hempty : ∀ τ, ¬ InT φ j τ) : ¬ Satisfiable φ := by
  rintro ⟨a, ha⟩
  refine hempty a ⟨a, fun c hc => ha c (List.mem_of_mem_take hc), fun _ _ => rfl⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.Cnf.FrontierDP.inT_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inT_succ

/-- info: 'AbsSat.Cnf.FrontierDP.inT_all_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inT_all_iff

end AbsSat.Cnf.FrontierDP
