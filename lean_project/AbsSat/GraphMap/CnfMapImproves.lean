-- lean_project/AbsSat/GraphMap/CnfMapImproves.lean
import AbsSat.GraphMap.CnfSel
import AbsSat.GraphMap.CnfReducer

/-!
# Weak requirements: the map's free pairwise information

`CnfMap.reqOfCnf` gives each clause node its **hard** requirements: one node
per literal step, the 0/1/all class. Two clause nodes that talk about the same
variable carry more than that, and it costs nothing to read off the map: a row
of clause `Cⱼ` and a row of an earlier clause `Cⱼ'` either agree on every
variable they share or they cannot both be on a solution.

`weakReqOfCnf φ d` lists that information for a clause node `d`: for every
earlier clause step sharing at least one variable with `d`'s clause, the nodes
of that step whose row agrees with `d`'s row on **all** shared variables, read
on the variable with its polarity (`CnfReducer.rowPairs` / `pairsAgree`, so
`x` and `¬x` are linked with the bit inverted).

Three things to keep in view:

* **A step with no shared variable is absent**, not "all nodes". The list says
  nothing about it; the machine will leave that step untouched.
* **A weak set is a set**, not a single node — this is outside the 0/1/all class
  and outside `Reachable.up`'s `hreqs_distinct`. It can be empty: the node is
  then incompatible with every row of that clause, and the filter will kill it
  at once through `isValid`.
* **It is sound** (`weakReqOfCnf_sound`): a solution's selection always lands
  inside every weak set of the nodes it selects. So filtering by it never
  removes a solution. It is *not* complete — pairwise agreement is arc
  consistency, and the review is still needed for everything beyond pairs.

This module only defines the information. Feeding it to the machine is
`PureDriverImproves`.
-/

namespace AbsSat.GraphMap.CnfMapImproves

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (selOfAssign rowOf selOfAssign_step selOfAssign_clause)
open AbsSat.GraphMap.CnfReducer (rowPairs pairsAgree allRows pairsAgree_rowOfAssign
  rowOfAssign_mem_allRows)

-- ============================================================
-- Definitions
-- ============================================================

def clauseVars (c : Clause) : List Nat := [c.l1.v, c.l2.v, c.l3.v]

/-- Two clauses are linked when they mention a common variable, whatever the
polarities. -/
def sharesVar (c c' : Clause) : Bool :=
  (clauseVars c).any (fun v => (clauseVars c').contains v)

/-- The rows of `c'` that agree with row `r` of `c` on every shared variable. -/
def weakRows (c : Clause) (r : Int) (c' : Clause) : List Int :=
  allRows.filter (fun w => pairsAgree (rowPairs c r) (rowPairs c' w))

/-- The weak requirements of row `r` of `c` against the clauses before index `j`,
one entry per linked clause: its step, and the nodes allowed there. -/
def weakBefore (φ : Cnf) (c : Clause) (r : Int) (j : Nat) : List (Int × List NodeId) :=
  (List.range j).filterMap (fun j' =>
    match φ.clauses[j']? with
    | none => none
    | some c' =>
      if sharesVar c c' then
        some (clauseStep φ j', (weakRows c r c').map (fun w => ⟨clauseStep φ j', w⟩))
      else none)

/-- **The weak requirements of a map node.** Empty off the clause steps. -/
def weakReqOfCnf (φ : Cnf) (d : NodeId) : List (Int × List NodeId) :=
  if d.step ≤ litBlock φ then []
  else if fusionTop φ ≤ d.step then []
  else
    match clauseAt φ d.step with
    | none => []
    | some c => weakBefore φ c d.index (d.step - litBlock φ - 1).toNat

-- ============================================================
-- Shape
-- ============================================================

theorem mem_weakBefore (φ : Cnf) (c : Clause) (r : Int) (j : Nat) (e : Int × List NodeId)
    (he : e ∈ weakBefore φ c r j) :
    ∃ j' c', j' < j ∧ φ.clauses[j']? = some c' ∧ sharesVar c c' = true ∧
      e = (clauseStep φ j', (weakRows c r c').map (fun w => ⟨clauseStep φ j', w⟩)) := by
  simp only [weakBefore, List.mem_filterMap, List.mem_range] at he
  obtain ⟨j', hj', hsome⟩ := he
  split at hsome
  · simp at hsome
  · rename_i c' hc
    split at hsome
    · rename_i hs
      exact ⟨j', c', hj', hc, hs, (Option.some.inj hsome).symm⟩
    · simp at hsome

/-- Weak requirements point strictly backwards, and each entry's nodes live at
its step. -/
theorem weakReqOfCnf_backward (φ : Cnf) (d : NodeId) :
    ∀ e ∈ weakReqOfCnf φ d, e.1 < d.step ∧ ∀ n ∈ e.2, n.step = e.1 := by
  intro e he
  by_cases hlo : d.step ≤ litBlock φ
  · simp [weakReqOfCnf, hlo] at he
  by_cases htop : fusionTop φ ≤ d.step
  · simp [weakReqOfCnf, hlo, htop] at he
  cases hc : clauseAt φ d.step with
  | none => simp [weakReqOfCnf, hlo, htop, hc] at he
  | some c =>
    simp only [weakReqOfCnf, if_neg hlo, if_neg htop, hc] at he
    obtain ⟨j', c', hj', _, _, rfl⟩ := mem_weakBefore φ c d.index _ e he
    refine ⟨?_, ?_⟩
    · show clauseStep φ j' < d.step
      simp only [clauseStep, litBlock] at hj' hlo ⊢
      omega
    · intro n hn
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hn
      rfl

-- ============================================================
-- Soundness: a solution is never filtered out
-- ============================================================

/-- **Every weak set contains the solution's own node.** If `a` satisfies `φ`,
then for any node `a` selects, and any weak entry of that node, the node `a`
selects at the entry's step is one of the entry's nodes. -/
theorem weakReqOfCnf_sound (φ : Cnf) (a : Assign) (hsat : Sat a φ) (k : Int) :
    ∀ e ∈ weakReqOfCnf φ (selOfAssign φ a k), selOfAssign φ a e.1 ∈ e.2 := by
  intro e he
  have hstep : (selOfAssign φ a k).step = k := selOfAssign_step φ a k
  by_cases hlo : k ≤ litBlock φ
  · simp [weakReqOfCnf, hstep, hlo] at he
  by_cases htop : fusionTop φ ≤ k
  · simp [weakReqOfCnf, hstep, hlo, htop] at he
  cases hc : clauseAt φ k with
  | none => simp [weakReqOfCnf, hstep, hlo, htop, hc] at he
  | some c =>
    have hjc : φ.clauses[(k - litBlock φ - 1).toNat]? = some c := by
      simpa only [clauseAt, litBlock] using hc
    have hjlt : (k - litBlock φ - 1).toNat < φ.clauses.length := by
      cases Nat.lt_or_ge (k - litBlock φ - 1).toNat φ.clauses.length with
      | inl h => exact h
      | inr h => rw [List.getElem?_eq_none h] at hjc; simp at hjc
    have hk : clauseStep φ (k - litBlock φ - 1).toNat = k := by
      simp only [clauseStep, litBlock] at hlo ⊢
      omega
    have hsel := selOfAssign_clause φ a _ c hjlt hjc
    rw [hk] at hsel
    rw [hsel] at he
    simp only [weakReqOfCnf, if_neg hlo, if_neg htop, hc] at he
    obtain ⟨j', c', hj', hc', _, rfl⟩ := mem_weakBefore φ c _ _ e he
    have hj'lt : j' < φ.clauses.length := by omega
    show selOfAssign φ a (clauseStep φ j') ∈ _
    rw [selOfAssign_clause φ a j' c' hj'lt hc']
    exact List.mem_map.mpr ⟨rowOf a c',
      List.mem_filter.mpr ⟨rowOfAssign_mem_allRows a c' (hsat c' (List.mem_of_getElem? hc')),
        pairsAgree_rowOfAssign a c c'⟩, rfl⟩

-- ============================================================
-- The worked example
-- ============================================================

/-! Variables `x1..x9` are `0..8`; the clause steps start at `2·9 + 1 = 19`.

    C1 = ( x1 ∨  x2 ∨  x3)   step 19
    C2 = ( x1 ∨  x4 ∨  x5)   step 20
    C3 = ( x2 ∨  x4 ∨  x6)   step 21
    C4 = ( x1 ∨  x2 ∨  x7)   step 22   shares two variables with C1
    C5 = (¬x1 ∨  x8 ∨  x9)   step 23   negated x1
    C6 = (¬x1 ∨ ¬x2 ∨ ¬x3)   step 24   row 111 has no partner in C1 -/

private def pos (v : Nat) : Lit := ⟨v, true⟩
private def neg (v : Nat) : Lit := ⟨v, false⟩

private def example6 : Cnf :=
  { nVars := 9,
    clauses := [⟨pos 0, pos 1, pos 2⟩, ⟨pos 0, pos 3, pos 4⟩, ⟨pos 1, pos 3, pos 5⟩,
                ⟨pos 0, pos 1, pos 6⟩, ⟨neg 0, pos 7, pos 8⟩, ⟨neg 0, neg 1, neg 2⟩] }

private def weakIdx (φ : Cnf) (d : NodeId) : List (Int × List Int) :=
  (weakReqOfCnf φ d).map (fun e => (e.1, e.2.map (·.index)))

-- C3 = 101 (x2=1, x4=0): C1 rows with x2=1, C2 rows with x4=0.
#guard weakIdx example6 ⟨21, 5⟩ == [(19, [2, 3, 6, 7]), (20, [1, 4, 5])]

-- C4 = 101 (x1=1, x2=0): against C1 both shared variables must agree.
#guard weakIdx example6 ⟨22, 5⟩ == [(19, [4, 5]), (20, [4, 5, 6, 7]), (21, [1, 2, 3])]

-- C5 = 100 (¬x1 true, so x1=0); C3 shares nothing and is absent.
#guard weakIdx example6 ⟨23, 4⟩ == [(19, [1, 2, 3]), (20, [1, 2, 3]), (22, [1, 2, 3])]

-- C6 = 111 (x1=x2=x3=0): C1 would need row 000, so the weak set is empty.
#guard weakIdx example6 ⟨24, 7⟩ ==
  [(19, []), (20, [1, 2, 3]), (21, [1, 2, 3]), (22, [1]), (23, [4, 5, 6, 7])]

-- Off the clause steps there is nothing.
#guard weakIdx example6 ⟨3, 0⟩ == []
#guard weakIdx example6 ⟨19, 7⟩ == []

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphMap.CnfMapImproves.weakReqOfCnf_backward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms weakReqOfCnf_backward

/-- info: 'AbsSat.GraphMap.CnfMapImproves.weakReqOfCnf_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms weakReqOfCnf_sound

end AbsSat.GraphMap.CnfMapImproves
