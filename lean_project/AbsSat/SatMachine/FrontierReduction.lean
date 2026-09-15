-- lean_project/AbsSat/SatMachine/FrontierReduction.lean
import AbsSat.SatMachine.PureProofs
import AbsSat.GraphPath.Model.PartialPaths
import AbsSat.GraphPath.Model.DriverPropagation
import AbsSat.Cnf.FrontierDP

/-!
# The SAT verdict, reduced to one frontier step

The open half of the machine's verdict is soundness: a non-empty last line should mean a
satisfiable formula. This module reduces it to a single, local, semantic obligation.

**The line invariant** (`PrefixSound`). After clause `j`, the key of every state — the row
of `C_j` it is parked at — extends to a model of the clauses `0..j`. It only reads keys, so
the joins that merge states never touch it.

**The obligation** (`FrontierSend`). When a state of a `PrefixSound` line is sent to a row
`d` of the next clause `C_j` and the filter is valid, some model of the clauses *before*
`C_j` has `d` as its row of `C_j`. It asks for a model of a prefix, not for a path inside a
state — weaker than `EmptinessReduction.SendExact` in what it produces.

**The reduction.** `FrontierSend` keeps `PrefixSound` from line to line
(`prefixSound_pureAdvance`): the new key is a row the map builds, so the model satisfies
`C_j` too. After the last clause the invariant gives a model of the whole formula, so a
non-empty last line is satisfiable (`sat_of_pureRun_ne_nil`), and with completeness the
machine decides (`run_pure_decides_of_FrontierSend`).

`FrontierSend` is the open part. Measured on the reference machine (7 random formulas, 232
clause lines, 756 states): the invariant it maintains never failed.
-/

namespace AbsSat.SatMachine.FrontierReduction

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.PartialPaths (lineAt lineAt_ok)
open AbsSat.Cnf.FrontierDP (SatPrefix take_succ_of_get)
open AbsSat.SatMachine.PureSatMachine

variable (φ : Cnf)

-- ============================================================
-- The invariant and the obligation
-- ============================================================

/-- After clause `j`, every key extends to a model of the clauses `0..j`. -/
def PrefixSound (line : PureLine) : Prop :=
  ∀ kv ∈ line, ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → kv.1.step = clauseStep φ j →
    ∃ a, SatPrefix a φ (j + 1) ∧ rowOf a c = kv.1.index

/-- **The frontier step.** A valid send from a `PrefixSound` line to a row `d` of clause `j`
has a model of the clauses before `j` whose row of clause `j` is `d`. -/
def FrontierSend : Prop :=
  ∀ (k : Int) (line : PureLine), LineOk φ k line → PrefixSound φ line →
    ∀ kv ∈ line, ∀ d ∈ mapSons φ kv.1.step kv.1.index,
      isValid (upFiltering kv.2 (reqOfCnf φ d) d "") = true →
      ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → d.step = clauseStep φ j →
        ∃ a, SatPrefix a φ j ∧ rowOf a c = d.index

-- ============================================================
-- Where a key of the next line comes from
-- ============================================================

def HasValidOrigin (line : PureLine) (key : NodeId) : Prop :=
  ∃ kv ∈ line, key ∈ mapSons φ kv.1.step kv.1.index ∧
    isValid (upFiltering kv.2 (reqOfCnf φ key) key "") = true

theorem sendTo_validOrigin (line : PureLine) (kv : NodeId × GPathM) (hkv : kv ∈ line)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (acc : PureLine) (hacc : ∀ e ∈ acc, HasValidOrigin φ line e.1) :
    ∀ e ∈ sendTo φ kv.2 acc d, HasValidOrigin φ line e.1 := by
  intro e he
  simp only [sendTo] at he
  split at he
  · next hval =>
    rcases DriverPropagation.insertPure_key_mem acc d _ e he with ⟨e0, he0, h0⟩ | hkey
    · rw [← h0]; exact hacc e0 he0
    · rw [hkey]; exact ⟨kv, hkv, hd, hval⟩
  · exact hacc e he

theorem sendAll_validOrigin (line : PureLine) (kv : NodeId × GPathM) (hkv : kv ∈ line)
    (acc : PureLine) (hacc : ∀ e ∈ acc, HasValidOrigin φ line e.1) :
    ∀ e ∈ sendAll φ kv acc, HasValidOrigin φ line e.1 := by
  simp only [sendAll]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, (∀ e ∈ acc, HasValidOrigin φ line e.1) →
        ∀ e ∈ l.foldl (sendTo φ kv.2) acc, HasValidOrigin φ line e.1 := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (sendTo_validOrigin φ line kv hkv x (hx x List.mem_cons_self) acc h)
  exact main _ (fun _ hd => hd) acc hacc

/-- Every key of the next line was sent to by a valid send from the current line. -/
theorem pureAdvance_validOrigin (line : PureLine) :
    ∀ e ∈ pureAdvance φ line, HasValidOrigin φ line e.1 := by
  simp only [pureAdvance]
  have main : ∀ (l : PureLine), (∀ kv ∈ l, kv ∈ line) →
      ∀ acc, (∀ e ∈ acc, HasValidOrigin φ line e.1) →
        ∀ e ∈ l.foldl (fun next kv => sendAll φ kv next) acc, HasValidOrigin φ line e.1 := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (sendAll_validOrigin φ line x (hx x List.mem_cons_self) acc h)
  exact main line (fun _ h => h) [] (fun e he => absurd he List.not_mem_nil)

-- ============================================================
-- The reduction
-- ============================================================

/-- A row the map builds names at least one literal true. -/
theorem satClause_of_rowOf_pos (a : Assign) (c : Clause) (h : 1 ≤ rowOf a c) : SatClause a c := by
  unfold SatClause
  cases h1 : litVal a c.l1 <;> cases h2 : litVal a c.l2 <;> cases h3 : litVal a c.l3 <;>
    simp only [rowOf, h1, h2, h3, bit_true, bit_false] at h <;>
    first | (exfalso; omega) | decide

theorem lt_of_getElem?_some {cs : List Clause} {j : Nat} {c : Clause} (hc : cs[j]? = some c) :
    j < cs.length := by
  cases Nat.lt_or_ge j cs.length with
  | inl h => exact h
  | inr h => rw [List.getElem?_eq_none h] at hc; cases hc

-- Step arithmetic, stated apart so that `omega` sees only numbers.

theorem clauseStep_ne_zero (j : Nat) : clauseStep φ j ≠ ((0 : Nat) : Int) := by
  intro h; unfold clauseStep at h; omega

theorem stepCount_sub_one_toNat (m : Nat) (hm : φ.clauses.length = m + 1) :
    (stepCount φ - 1).toNat = (clauseStep φ m).toNat + 1 := by
  unfold stepCount clauseStep; rw [hm]; omega

theorem clauseStep_toNat_cast (m : Nat) : (((clauseStep φ m).toNat : Nat) : Int) = clauseStep φ m := by
  unfold clauseStep; omega

theorem prefixSound_pureInit : PrefixSound φ (pureInit φ) := by
  intro kv hkv j c _ hstep
  have h0 : kv.1.step = ((0 : Nat) : Int) :=
    mapNodes_step φ _ kv.1 ((lineAt_ok φ 0).2 kv hkv).onMap
  exact absurd (hstep.symm.trans h0) (clauseStep_ne_zero φ j)

/-- **`FrontierSend` keeps the invariant from one line to the next.** -/
theorem prefixSound_pureAdvance (hFS : FrontierSend φ) (k : Int) (line : PureLine)
    (hl : LineOk φ k line) (hp : PrefixSound φ line) : PrefixSound φ (pureAdvance φ line) := by
  intro e he j c hc hstep
  obtain ⟨kv, hkv, hd, hval⟩ := pureAdvance_validOrigin φ line e he
  have hon : e.1 ∈ mapNodes φ (k + 1) := ((LineOk_pureAdvance φ k line hl).2 e he).onMap
  obtain ⟨a, hsat, hrow⟩ := hFS k line hl hp kv hkv e.1 hd hval j c hc hstep
  refine ⟨a, ?_, hrow⟩
  have hjlt := lt_of_getElem?_some hc
  have hkstep : k + 1 = clauseStep φ j := by rw [← mapNodes_step φ (k + 1) e.1 hon]; exact hstep
  have hrange := index_range_of_clauseNode φ j hjlt e.1 (by rw [← hkstep]; exact hon)
  have hcl : SatClause a c := satClause_of_rowOf_pos a c (by rw [hrow]; exact hrange.1)
  intro c' hc'
  rw [take_succ_of_get φ.clauses j c hc] at hc'
  rcases List.mem_append.mp hc' with h | h
  · exact hsat c' h
  · rcases List.mem_singleton.mp h with rfl
    exact hcl

theorem prefixSound_lineAt (hFS : FrontierSend φ) : ∀ n : Nat, PrefixSound φ (lineAt φ n) := by
  intro n
  induction n with
  | zero => exact prefixSound_pureInit φ
  | succ n ih =>
    show PrefixSound φ (pureSteps φ (n + 1) (pureInit φ))
    rw [PureProofs.pureSteps_succ']
    exact prefixSound_pureAdvance φ hFS n (lineAt φ n) (lineAt_ok φ n) ih

/-- **Soundness from `FrontierSend`.** A non-empty last line means a satisfiable formula. -/
theorem sat_of_pureRun_ne_nil (hFS : FrontierSend φ) (h : pureRun φ ≠ []) : Satisfiable φ := by
  cases hm : φ.clauses.length with
  | zero =>
    refine ⟨fun _ => true, fun c hc => ?_⟩
    rw [List.eq_nil_of_length_eq_zero hm] at hc
    exact absurd hc List.not_mem_nil
  | succ m =>
    have hmlt : m < φ.clauses.length := by rw [hm]; exact Nat.lt_succ_self m
    obtain ⟨c, hc⟩ : ∃ c, φ.clauses[m]? = some c :=
      ⟨φ.clauses[m], List.getElem?_eq_getElem hmlt⟩
    have hrun : pureRun φ = pureAdvance φ (lineAt φ (clauseStep φ m).toNat) := by
      show pureSteps φ (stepCount φ - 1).toNat (pureInit φ)
        = pureAdvance φ (pureSteps φ (clauseStep φ m).toNat (pureInit φ))
      rw [stepCount_sub_one_toNat φ m hm, PureProofs.pureSteps_succ']
    have hne : lineAt φ (clauseStep φ m).toNat ≠ [] := by
      intro h0
      apply h
      rw [hrun, h0]
      rfl
    obtain ⟨kv, hkv⟩ := List.exists_mem_of_ne_nil _ hne
    have hon := ((lineAt_ok φ (clauseStep φ m).toNat).2 kv hkv).onMap
    have hstep : kv.1.step = clauseStep φ m :=
      (mapNodes_step φ _ kv.1 hon).trans (clauseStep_toNat_cast φ m)
    obtain ⟨a, hsat, _⟩ := prefixSound_lineAt φ hFS _ kv hkv m c hc hstep
    have hlen : m + 1 = φ.clauses.length := hm.symm
    exact ⟨a, fun c' hc' => hsat c' (by rw [hlen, List.take_length]; exact hc')⟩

/-- **The machine's SAT answer is sound under `FrontierSend`.** -/
theorem soundness_of_FrontierSend (hFS : FrontierSend φ)
    (h : is_satisfiable (run_pure φ) = true) : Satisfiable φ :=
  sat_of_pureRun_ne_nil φ hFS ((PureProofs.is_satisfiable_run_pure_iff φ).mp h)

/-- **Under `FrontierSend`, the machine decides.** -/
theorem run_pure_decides_of_FrontierSend (hwf : WF φ) (hFS : FrontierSend φ) :
    is_satisfiable (run_pure φ) = true ↔ Satisfiable φ :=
  ⟨soundness_of_FrontierSend φ hFS, PureProofs.completeness_pure φ hwf⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.SatMachine.FrontierReduction.prefixSound_pureAdvance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prefixSound_pureAdvance

/-- info: 'AbsSat.SatMachine.FrontierReduction.sat_of_pureRun_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pureRun_ne_nil

/-- info: 'AbsSat.SatMachine.FrontierReduction.run_pure_decides_of_FrontierSend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_pure_decides_of_FrontierSend

end AbsSat.SatMachine.FrontierReduction
