-- lean/improves_bin/AbsSatBin/GraphMap/CnfSelBin.lean
import AbsSatBin.GraphMap.CnfMapBin

/-!
# The branch an assignment names, on the bin map — **rewritten** (`lean_project`'s `CnfSel`)

Given an assignment, read the selection it names: at a variable step the node carrying its
truth value, at the negation step the matching node, at a clause step `Lₚ` the node carrying the
truth value of literal `p`. Fusion steps have their single node.

**Where `Sat` enters moves.** In the classic map a clause step had seven rows and `Sat` was what
put the selection on the map (the row `000` does not exist). Here every clause step has both
values, so the selection is on the map for **any** assignment (`selOfAssign_onMap`, no `Sat`).
`Sat` enters in exactly one new place: the **window** the branch carries at the third literal
of a clause is not the prohibited `(0,0,0)` (`pidOfAssign_not_prohibited`).

**Indices.** Steps are only ever read through `CnfMapBin`'s functions (`varStep`, `negStep`,
`midFusion`, `clauseStep j p`, `fusionTop`, `clauseOf`); the one decoding of a variable step back
to its variable is `varOfStep` below, with its two round-trip lemmas.
-/

namespace AbsSatBin.GraphMap.CnfSelBin

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

/-- A bit as an `Int`. -/
def bit (b : Bool) : Int := if b then 1 else 0

theorem bit_true : bit true = 1 := rfl
theorem bit_false : bit false = 0 := rfl
theorem one_sub_bit_not (b : Bool) : 1 - bit (!b) = bit b := by cases b <;> decide
theorem bit_not (b : Bool) : bit (!b) = 1 - bit b := by cases b <;> decide

/-- The variable a literal-block step belongs to: `2v+1 ↦ v`, `2v+2 ↦ v`. -/
def varOfStep (k : Int) : Nat := ((k - 1) / 2).toNat

theorem varOfStep_varStep (v : Nat) : varOfStep (varStep v) = v := by
  simp only [varOfStep, varStep]; omega

theorem varOfStep_negStep (v : Nat) : varOfStep (negStep v) = v := by
  simp only [varOfStep, negStep]; omega

-- ============================================================
-- The selection
-- ============================================================

/-- The node an assignment selects at step `k`. -/
def selOfAssign (φ : Cnf) (a : Assign) (k : Int) : NodeId :=
  if k ≤ 0 then ⟨k, 0⟩
  else if k < midFusion φ then
    if k % 2 = 1 then ⟨k, bit (a (varOfStep k))⟩
    else ⟨k, bit (!(a (varOfStep k)))⟩
  else if k = midFusion φ then ⟨k, 0⟩
  else if fusionTop φ ≤ k then ⟨k, 0⟩
  else
    match clauseOf φ k with
    | none => ⟨k, 0⟩
    | some (c, p) => ⟨k, bit (litVal a (litAt c p))⟩

theorem selOfAssign_step (φ : Cnf) (a : Assign) (k : Int) : (selOfAssign φ a k).step = k := by
  unfold selOfAssign
  split
  · rfl
  · split
    · split <;> rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl

theorem selOfAssign_var (φ : Cnf) (a : Assign) (v : Nat) (hv : v < φ.nVars) :
    selOfAssign φ a (varStep v) = ⟨varStep v, bit (a v)⟩ := by
  have h0 : ¬ varStep v ≤ 0 := by simp only [varStep]; omega
  have h1 : varStep v < midFusion φ := by simp only [varStep, midFusion]; omega
  have h2 : varStep v % 2 = 1 := by simp only [varStep]; omega
  simp only [selOfAssign, if_neg h0, if_pos h1, if_pos h2, varOfStep_varStep]

theorem selOfAssign_neg (φ : Cnf) (a : Assign) (v : Nat) (hv : v < φ.nVars) :
    selOfAssign φ a (negStep v) = ⟨negStep v, bit (!(a v))⟩ := by
  have h0 : ¬ negStep v ≤ 0 := by simp only [negStep]; omega
  have h1 : negStep v < midFusion φ := by simp only [negStep, midFusion]; omega
  have h2 : ¬ negStep v % 2 = 1 := by simp only [negStep]; omega
  simp only [selOfAssign, if_neg h0, if_pos h1, if_neg h2, varOfStep_negStep]

/-- At a literal's own step the selection carries that literal's truth value. -/
theorem selOfAssign_lit (φ : Cnf) (a : Assign) (l : Lit) (hl : l.v < φ.nVars) :
    selOfAssign φ a l.binStep = ⟨l.binStep, bit (litVal a l)⟩ := by
  cases hp : l.pos with
  | true =>
    rw [varStep_eq l hp, selOfAssign_var φ a l.v hl]
    simp [litVal, hp]
  | false =>
    rw [negStep_eq l hp, selOfAssign_neg φ a l.v hl]
    simp [litVal, hp]

theorem selOfAssign_clause (φ : Cnf) (a : Assign) (j p : Nat) (c : Clause) (hp : p < 3)
    (hjlt : j < φ.clauses.length) (hj : φ.clauses[j]? = some c) :
    selOfAssign φ a (clauseStep φ j p) = ⟨clauseStep φ j p, bit (litVal a (litAt c p))⟩ := by
  have h0 : ¬ clauseStep φ j p ≤ 0 := by simp only [clauseStep]; omega
  have h1 : ¬ clauseStep φ j p < midFusion φ := by simp only [clauseStep, midFusion]; omega
  have h2 : ¬ clauseStep φ j p = midFusion φ := by simp only [clauseStep, midFusion]; omega
  have h3 : ¬ fusionTop φ ≤ clauseStep φ j p := by simp only [clauseStep, fusionTop]; omega
  simp only [selOfAssign, if_neg h0, if_neg h1, if_neg h2, if_neg h3,
    clauseOf_clauseStep φ j p c hp hj]

-- ============================================================
-- Every step is one of six kinds
-- ============================================================

theorem step_cases (φ : Cnf) (k : Int) :
    k ≤ 0
    ∨ (∃ v, v < φ.nVars ∧ k = varStep v)
    ∨ (∃ v, v < φ.nVars ∧ k = negStep v)
    ∨ k = midFusion φ
    ∨ (∃ j p c, p < 3 ∧ j < φ.clauses.length ∧ φ.clauses[j]? = some c ∧ k = clauseStep φ j p)
    ∨ fusionTop φ ≤ k := by
  by_cases h0 : k ≤ 0
  · exact Or.inl h0
  by_cases h1 : k < midFusion φ
  · simp only [midFusion] at h1
    by_cases hpar : k % 2 = 1
    · exact Or.inr (Or.inl ⟨varOfStep k, by simp only [varOfStep]; omega,
        by simp only [varStep, varOfStep]; omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨varOfStep k, by simp only [varOfStep]; omega,
        by simp only [negStep, varOfStep]; omega⟩))
  by_cases h2 : k = midFusion φ
  · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
  by_cases h3 : fusionTop φ ≤ k
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h3))))
  · obtain ⟨c, p, hp, hc⟩ := clauseOf_isSome φ k (by simp only [midFusion] at h1 h2 ⊢; omega)
      (by omega)
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    have hjlt : ((k - midFusion φ - 1) / 3).toNat < φ.clauses.length := by
      simp only [midFusion, fusionTop] at h1 h2 h3 ⊢; omega
    refine ⟨((k - midFusion φ - 1) / 3).toNat, ((k - midFusion φ - 1) % 3).toNat, c,
      by omega, hjlt, ?_, ?_⟩
    · simp only [clauseOf] at hc
      split at hc
      · exact absurd hc (by simp)
      · next c' hc' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rw [hc']; rw [hc.1]
    · simp only [clauseStep, midFusion] at h1 h2 ⊢; omega

-- ============================================================
-- The requirements, and the map
-- ============================================================

/-- **The requirements are satisfied by *any* assignment's selection** — the map's bookkeeping
being consistent with itself. -/
theorem reqSat_selOfAssign (φ : Cnf) (hb : Bounded φ) (a : Assign) (k : Int) :
    ∀ req ∈ reqOf φ (selOfAssign φ a k), selOfAssign φ a req.step = req := by
  intro req hreq
  have hstep : (selOfAssign φ a k).step = k := selOfAssign_step φ a k
  rcases step_cases φ k with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | h | ⟨j, p, c, hp, hjlt, hj, rfl⟩ | h
  · rw [reqOf_nonpos φ _ (by rw [hstep]; exact h)] at hreq; exact absurd hreq List.not_mem_nil
  · rw [reqOf_var φ _ v hv hstep] at hreq; exact absurd hreq List.not_mem_nil
  · have hidx : (selOfAssign φ a (negStep v)).index = bit (!(a v)) := by
      rw [selOfAssign_neg φ a v hv]
    rw [reqOf_neg φ _ v hv hstep, hidx] at hreq
    rcases List.mem_singleton.mp hreq with rfl
    show selOfAssign φ a (varStep v) = _
    rw [selOfAssign_var φ a v hv, one_sub_bit_not]
  · rw [reqOf_mid φ _ (by rw [hstep]; exact h)] at hreq; exact absurd hreq List.not_mem_nil
  · have hidx : (selOfAssign φ a (clauseStep φ j p)).index = bit (litVal a (litAt c p)) := by
      rw [selOfAssign_clause φ a j p c hp hjlt hj]
    rw [reqOf_clause φ _ j p c hp hjlt hj hstep, hidx] at hreq
    rcases List.mem_singleton.mp hreq with rfl
    obtain ⟨h1, h2, h3⟩ := hb c (List.mem_of_getElem? hj)
    have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
    exact selOfAssign_lit φ a _ hv
  · rw [reqOf_above φ _ (by rw [hstep]; exact h)] at hreq; exact absurd hreq List.not_mem_nil

/-- **The selection is on the map, for any assignment.** No `Sat`: every step of the bin map
has both values (or is a single fusion node). -/
theorem selOfAssign_onMap (φ : Cnf) (a : Assign) (k : Int) (h0 : 0 ≤ k) (hk : k < stepCount φ) :
    selOfAssign φ a k ∈ mapNodes φ k := by
  have hstep := selOfAssign_step φ a k
  have hvals : ∀ i : Int, i = 0 ∨ i = 1 → (⟨k, i⟩ : NodeId) ∈ [⟨k, 0⟩, ⟨k, 1⟩] := by
    intro i hi; rcases hi with rfl | rfl <;> simp
  have hbit : ∀ b : Bool, bit b = 0 ∨ bit b = 1 := by intro b; cases b <;> simp [bit]
  rcases step_cases φ k with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | h | ⟨j, p, c, hp, hjlt, hj, rfl⟩ | h
  · have hk0 : k = 0 := by omega
    subst hk0
    rw [mapNodes_fusion φ 0 (Or.inl rfl)]
    simp [selOfAssign]
  · rw [selOfAssign_var φ a v hv, mapNodes_two φ _ (by simp only [varStep]; omega)
      (by simp only [varStep, midFusion]; omega) (by simp only [varStep, fusionTop]; omega)]
    exact hvals _ (hbit _)
  · rw [selOfAssign_neg φ a v hv, mapNodes_two φ _ (by simp only [negStep]; omega)
      (by simp only [negStep, midFusion]; omega) (by simp only [negStep, fusionTop]; omega)]
    exact hvals _ (hbit _)
  · rw [mapNodes_fusion φ k (Or.inr (Or.inl h))]
    have h1 : ¬ k ≤ 0 := by simp only [midFusion] at h; omega
    have h2 : ¬ k < midFusion φ := by omega
    have e : selOfAssign φ a k = ⟨k, 0⟩ := by
      unfold selOfAssign
      rw [if_neg h1, if_neg h2, if_pos h]
    rw [e]; exact List.mem_cons_self
  · rw [selOfAssign_clause φ a j p c hp hjlt hj, mapNodes_two φ _ (by simp only [clauseStep]; omega)
      (by simp only [clauseStep, midFusion]; omega) (by simp only [clauseStep, fusionTop]; omega)]
    exact hvals _ (hbit _)
  · rw [mapNodes_fusion φ k (Or.inr (Or.inr ⟨h, hk⟩))]
    have h1 : ¬ k ≤ 0 := by simp only [fusionTop] at h; omega
    have h2 : ¬ k < midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
    have h3 : ¬ k = midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
    have e : selOfAssign φ a k = ⟨k, 0⟩ := by
      unfold selOfAssign
      rw [if_neg h1, if_neg h2, if_neg h3, if_pos h]
    rw [e]; exact List.mem_cons_self

-- ============================================================
-- The branch follows the map's own edges
-- ============================================================

/-- **The assignment's branch is a path along the map's sons.** The crossed link of the variable
block (`"v=b"` has the single son `"!v=1-b"`) is where it needs the selection's own value. -/
theorem selOfAssign_son (φ : Cnf) (a : Assign) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ) :
    selOfAssign φ a (k + 1) ∈ sonsOf φ (selOfAssign φ a k) := by
  have hstep := selOfAssign_step φ a k
  unfold sonsOf
  rw [hstep]
  split
  · rename_i hvar
    obtain ⟨hpos, hlt, hodd⟩ := hvar
    obtain ⟨v, hv, rfl⟩ : ∃ v, v < φ.nVars ∧ k = varStep v :=
      ⟨varOfStep k, by simp only [varOfStep, midFusion] at hlt ⊢; omega,
        by simp only [varStep, varOfStep]; omega⟩
    have hk1 : varStep v + 1 = negStep v := by simp only [varStep, negStep]; omega
    rw [hk1, selOfAssign_neg φ a v hv, selOfAssign_var φ a v hv]
    simp only [bit_not, List.mem_singleton]
  · exact selOfAssign_onMap φ a (k + 1) (by omega) hk

-- ============================================================
-- The window the branch carries, and where `Sat` enters
-- ============================================================

/-- The path identifier the branch carries at step `k`: the window of three, most recent first
(`GPathM.shiftPid` builds exactly this along a chain). -/
def pidOfAssign (φ : Cnf) (a : Assign) (k : Int) : PathNodeId :=
  { id := selOfAssign φ a k,
    parent_id := if 0 < k then some (selOfAssign φ a (k - 1)) else none,
    gparent_id := if 1 < k then some (selOfAssign φ a (k - 2)) else none }

/-- **Where `Sat` enters, and the only place it does.** The window of a satisfying assignment's
branch is never prohibited: at the third literal of clause `j` its three values are the three
literals' truth values, and a satisfied clause has one of them true. -/
theorem pidOfAssign_not_prohibited (φ : Cnf) (a : Assign) (hsat : Sat a φ) (k : Int) :
    isProhibited φ (pidOfAssign φ a k) = false := by
  cases hpr : isProhibited φ (pidOfAssign φ a k) with
  | false => rfl
  | true =>
    exfalso
    simp only [isProhibited, isL3, pidOfAssign, selOfAssign_step, Bool.and_eq_true,
      beq_iff_eq] at hpr
    obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, hmod⟩, hidx⟩, hpar⟩, hgp⟩ := hpr
    have hlo := of_decide_eq_true hlo
    have hhi := of_decide_eq_true hhi
    have hmod := of_decide_eq_true hmod
    -- `k` is the third literal step of clause `j`
    obtain ⟨c, p, hp, hc⟩ := clauseOf_isSome φ k hlo hhi
    have hjlt : ((k - midFusion φ - 1) / 3).toNat < φ.clauses.length := by
      simp only [midFusion, fusionTop] at hlo hhi ⊢; omega
    obtain ⟨j, hjdef⟩ : ∃ j, j = ((k - midFusion φ - 1) / 3).toNat := ⟨_, rfl⟩
    rw [← hjdef] at hjlt
    have hcj : φ.clauses[j]? = some c := by
      simp only [clauseOf] at hc
      split at hc
      · exact absurd hc (by simp)
      · next c' hc' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rw [hjdef, hc']; rw [hc.1]
    have e3 : k = clauseStep φ j 2 := by simp only [hjdef, clauseStep, midFusion] at hlo hmod ⊢; omega
    have e2 : k - 1 = clauseStep φ j 1 := by rw [e3]; simp only [clauseStep]; omega
    have e1 : k - 2 = clauseStep φ j 0 := by rw [e3]; simp only [clauseStep]; omega
    have hk0 : 0 < k := by simp only [midFusion] at hlo; omega
    have hk1 : 1 < k := by simp only [midFusion] at hlo; omega
    rw [if_pos hk0] at hpar
    rw [if_pos hk1] at hgp
    simp only [Option.some.injEq] at hpar hgp
    -- read the three values
    have v3 := congrArg NodeId.index (selOfAssign_clause φ a j 2 c (by omega) hjlt hcj)
    have v2 := congrArg NodeId.index (selOfAssign_clause φ a j 1 c (by omega) hjlt hcj)
    have v1 := congrArg NodeId.index (selOfAssign_clause φ a j 0 c (by omega) hjlt hcj)
    rw [← e3] at v3
    rw [← e2] at v2
    rw [← e1] at v1
    have i3 : bit (litVal a c.l3) = 0 := by rw [← hidx]; exact v3.symm
    have i2 : bit (litVal a c.l2) = 0 := by
      have := congrArg NodeId.index hpar; simp only at this; rw [← this]; exact v2.symm
    have i1 : bit (litVal a c.l1) = 0 := by
      have := congrArg NodeId.index hgp; simp only at this; rw [← this]; exact v1.symm
    have hsc := hsat c (List.mem_of_getElem? hcj)
    rcases hsc with h | h | h
    · rw [h] at i1; exact absurd i1 (by decide)
    · rw [h] at i2; exact absurd i2 (by decide)
    · rw [h] at i3; exact absurd i3 (by decide)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSatBin.GraphMap.CnfSelBin.reqSat_selOfAssign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqSat_selOfAssign

/-- info: 'AbsSatBin.GraphMap.CnfSelBin.pidOfAssign_not_prohibited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pidOfAssign_not_prohibited

end AbsSatBin.GraphMap.CnfSelBin
