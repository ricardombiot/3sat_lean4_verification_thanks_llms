import AbsSat.Cnf.UnitProp

/-!
# Horn clauses: no unit-propagation conflict gives a model

A clause is **Horn** when it has at most one positive literal. For Horn clauses unit propagation is
complete: if it reaches no conflict from the clauses `cls` and the units `U`, then the assignment
that makes true exactly the variables forward chaining derives satisfies both.

The model is computed, not chosen: `upIter` runs forward chaining from the all-false assignment,
and after `(heads cls U).length + 1` rounds it is closed (`hornModel_closed`), because each round
that is not a fixpoint turns on one more variable of the finite list `heads cls U`.

* `upIter_forced` — every variable forward chaining turns on is derived by `Forced`;
* `hornModel_closed` — the computed assignment is closed under the rules;
* `horn_model` — Horn clauses without a conflict: `hornModel` satisfies the clauses and the units;
* `horn_model_iff` — for Horn clauses, a model of clauses and units exists iff there is no conflict;
* `Cnf.horn_satisfiable_iff` — a Horn formula is satisfiable iff its clauses alone give no conflict.
-/

namespace AbsSat.Cnf

/-- A clause is **Horn** when it has at most one positive literal. -/
def Clause.Horn (c : Clause) : Prop :=
  ∀ l ∈ c.lits, ∀ l' ∈ c.lits, l.pos = true → l'.pos = true → l = l'

/-- A formula is Horn when all its clauses are. -/
def Cnf.Horn (φ : Cnf) : Prop := ∀ c ∈ φ.clauses, c.Horn

/-- The positive literal on `v`. -/
abbrev posLit (v : Nat) : Lit := ⟨v, true⟩

-- ============================================================
-- Forward chaining
-- ============================================================

/-- The variables of the positive literals of a list. -/
def posVars (ls : List Lit) : List Nat := (ls.filter (fun l => l.pos)).map (fun l => l.v)

theorem mem_posVars {ls : List Lit} {v : Nat} (h : posLit v ∈ ls) : v ∈ posVars ls :=
  List.mem_map.mpr ⟨posLit v, List.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

/-- The clause `ls` has head `v` and every other literal is negative on a true variable. -/
def headFires (a : Assign) (v : Nat) (ls : List Lit) : Bool :=
  decide (posLit v ∈ ls) && ls.all (fun l => decide (l = posLit v) || (!l.pos && a l.v))

/-- `v` is a positive unit, or the head of a clause whose body holds under `a`. -/
def fires (cls : List Clause) (U : List Lit) (a : Assign) (v : Nat) : Bool :=
  decide (posLit v ∈ U) || cls.any (fun c => headFires a v c.lits)

/-- One round of forward chaining. -/
def upStep (cls : List Clause) (U : List Lit) (a : Assign) : Assign :=
  fun v => a v || fires cls U a v

/-- `k` rounds of forward chaining from the all-false assignment. -/
def upIter (cls : List Clause) (U : List Lit) : Nat → Assign
  | 0 => fun _ => false
  | k + 1 => upStep cls U (upIter cls U k)

/-- Every variable that can fire. -/
def heads (cls : List Clause) (U : List Lit) : List Nat :=
  posVars U ++ cls.flatMap (fun c => posVars c.lits)

/-- **The Horn model**: forward chaining run to its fixpoint. -/
def hornModel (cls : List Clause) (U : List Lit) : Assign :=
  upIter cls U ((heads cls U).length + 1)

/-- `a` is closed under the rules. -/
def Closed (cls : List Clause) (U : List Lit) (a : Assign) : Prop :=
  ∀ v, fires cls U a v = true → a v = true

variable {cls : List Clause} {U : List Lit}

theorem fires_heads {a : Assign} {v : Nat} (h : fires cls U a v = true) : v ∈ heads cls U := by
  rcases Bool.or_eq_true_iff.mp h with hu | hc
  · exact List.mem_append_left _ (mem_posVars (of_decide_eq_true hu))
  · obtain ⟨c, hc, hf⟩ := List.any_eq_true.mp hc
    have hm := of_decide_eq_true (Bool.and_eq_true_iff.mp hf).1
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, mem_posVars hm⟩)

/-- **Forward chaining is unit propagation.** -/
theorem upIter_forced : ∀ k v, upIter cls U k v = true → Forced cls U (posLit v)
  | 0, _, h => by cases h
  | k + 1, v, h => by
    have ih := upIter_forced k
    have h' : (upIter cls U k v || fires cls U (upIter cls U k) v) = true := h
    rcases Bool.or_eq_true_iff.mp h' with ha | hf
    · exact ih v ha
    · rcases Bool.or_eq_true_iff.mp hf with hu | hc
      · exact Forced.unit _ (of_decide_eq_true hu)
      · obtain ⟨c, hc, hh⟩ := List.any_eq_true.mp hc
        obtain ⟨hm, hall⟩ := Bool.and_eq_true_iff.mp hh
        refine Forced.prop c hc (posLit v) (of_decide_eq_true hm) (fun l' hl' hne => ?_)
        have hl := List.all_eq_true.mp hall l' hl'
        rcases Bool.or_eq_true_iff.mp hl with hd | hn
        · exact absurd (of_decide_eq_true hd) hne
        · cases l' with
          | mk w p =>
            cases p with
            | true => cases hn
            | false => exact ih w (Bool.and_eq_true_iff.mp hn).2

-- ============================================================
-- Counting: a non-fixpoint round turns on a new head
-- ============================================================

/-- How many entries of `H` are true under `a`. -/
def count (a : Assign) : List Nat → Nat
  | [] => 0
  | x :: H => (a x).toNat + count a H

theorem count_le (a : Assign) : ∀ H : List Nat, count a H ≤ H.length
  | [] => Nat.le_refl 0
  | x :: H => by
    have ih := count_le a H
    show (a x).toNat + count a H ≤ H.length + 1
    cases a x with
    | true => show 1 + count a H ≤ H.length + 1; omega
    | false => show 0 + count a H ≤ H.length + 1; omega

theorem count_mono {a b : Assign} (hab : ∀ x, a x = true → b x = true) :
    ∀ H : List Nat, count a H ≤ count b H
  | [] => Nat.le_refl 0
  | x :: H => by
    have ih := count_mono hab H
    show (a x).toNat + count a H ≤ (b x).toNat + count b H
    cases ha : a x with
    | true => rw [hab x ha]; show 1 + count a H ≤ 1 + count b H; omega
    | false =>
      cases b x with
      | true => show 0 + count a H ≤ 1 + count b H; omega
      | false => show 0 + count a H ≤ 0 + count b H; omega

theorem count_strict {a b : Assign} (hab : ∀ x, a x = true → b x = true) {y : Nat}
    (hya : a y = false) (hyb : b y = true) : ∀ H : List Nat, y ∈ H → count a H + 1 ≤ count b H
  | [], h => absurd h List.not_mem_nil
  | x :: H, h => by
    have hm := count_mono hab H
    show (a x).toNat + count a H + 1 ≤ (b x).toNat + count b H
    rcases List.mem_cons.mp h with e | e
    · rw [← e, hya, hyb]; show 0 + count a H + 1 ≤ 1 + count b H; omega
    · have ih := count_strict hab hya hyb H e
      cases ha : a x with
      | true => rw [hab x ha]; show 1 + count a H + 1 ≤ 1 + count b H; omega
      | false =>
        cases b x with
        | true => show 0 + count a H + 1 ≤ 1 + count b H; omega
        | false => show 0 + count a H + 1 ≤ 0 + count b H; omega

-- ============================================================
-- The fixpoint
-- ============================================================

theorem upIter_mono (k : Nat) (v : Nat) (h : upIter cls U k v = true) :
    upIter cls U (k + 1) v = true := by
  show (upIter cls U k v || fires cls U (upIter cls U k) v) = true
  rw [h]
  rfl

theorem upStep_of_closed {a : Assign} (hc : Closed cls U a) : upStep cls U a = a :=
  funext fun v => by
    show (a v || fires cls U a v) = a v
    cases hf : fires cls U a v with
    | false => exact Bool.or_false _
    | true => rw [hc v hf]; rfl

theorem closed_of_any {a : Assign}
    (h : (heads cls U).any (fun v => fires cls U a v && !a v) = false) : Closed cls U a := by
  intro v hf
  have hn : ¬ (fires cls U a v && !a v) = true := List.any_eq_false.mp h v (fires_heads hf)
  cases ha : a v with
  | true => rfl
  | false => rw [hf, ha] at hn; exact absurd rfl hn

/-- Each round either is closed or has turned on at least one more head. -/
theorem upIter_progress :
    ∀ k, Closed cls U (upIter cls U k) ∨ k ≤ count (upIter cls U k) (heads cls U)
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
    have hstep : upIter cls U (k + 1) = upStep cls U (upIter cls U k) := rfl
    cases hany : (heads cls U).any (fun v => fires cls U (upIter cls U k) v && !upIter cls U k v) with
    | false =>
      have hc := closed_of_any hany
      rw [hstep, upStep_of_closed hc]
      exact Or.inl hc
    | true =>
      obtain ⟨y, hy, hyf⟩ := List.any_eq_true.mp hany
      obtain ⟨hf, hna⟩ := Bool.and_eq_true_iff.mp hyf
      have hya : upIter cls U k y = false := by
        cases h : upIter cls U k y with
        | false => rfl
        | true => rw [h] at hna; cases hna
      have hyb : upIter cls U (k + 1) y = true := by
        show (upIter cls U k y || fires cls U (upIter cls U k) y) = true
        rw [hf, Bool.or_true]
      rcases upIter_progress k with hc | hk
      · have e := hc y hf
        rw [hya] at e
        cases e
      · exact Or.inr (Nat.le_trans (Nat.succ_le_succ hk)
          (count_strict (upIter_mono k) hya hyb _ hy))

/-- **Forward chaining reaches its fixpoint** within `(heads cls U).length + 1` rounds. -/
theorem hornModel_closed : Closed cls U (hornModel cls U) := by
  rcases upIter_progress (cls := cls) (U := U) ((heads cls U).length + 1) with hc | hk
  · exact hc
  · exact absurd (Nat.le_trans hk (count_le _ _)) (Nat.not_succ_le_self _)

-- ============================================================
-- Horn completeness of unit propagation
-- ============================================================

theorem posLit_of_pos (l : Lit) (h : l.pos = true) : l = posLit l.v := by
  cases l with
  | mk w p =>
    cases p with
    | true => rfl
    | false => cases h

/-- A negative literal that is false has its variable true in the model, so its negation is forced. -/
theorem forced_neg_of_false {l : Lit} (hp : l.pos = false)
    (hl : ¬ litVal (hornModel cls U) l = true) : Forced cls U l.neg ∧
      (!l.pos && hornModel cls U l.v) = true := by
  cases l with
  | mk w p =>
    cases p with
    | true => cases hp
    | false =>
      cases ha : hornModel cls U w with
      | true => exact ⟨upIter_forced _ w ha, rfl⟩
      | false =>
        have e : litVal (hornModel cls U) ⟨w, false⟩ = true := by
          show (!hornModel cls U w) = true
          rw [ha]
          rfl
        exact absurd e hl

/-- **Horn clauses without a conflict are satisfied by the forward-chaining model**, together with
the units. -/
theorem horn_model (hh : ∀ c ∈ cls, c.Horn) (hnc : ¬ Conflict cls U) :
    (∀ c ∈ cls, SatClause (hornModel cls U) c) ∧ ∀ l ∈ U, litVal (hornModel cls U) l = true := by
  refine ⟨fun c hc => ?_, fun l hl => ?_⟩
  · cases hsat : c.lits.any (litVal (hornModel cls U)) with
    | true =>
      exact (satClause_iff _ c).mpr (List.any_eq_true.mp hsat)
    | false =>
      have hfalse : ∀ l ∈ c.lits, ¬ litVal (hornModel cls U) l = true :=
        List.any_eq_false.mp hsat
      cases hpos : c.lits.any (fun l => l.pos) with
      | true =>
        obtain ⟨y, hy, hyp⟩ := List.any_eq_true.mp hpos
        have hye := posLit_of_pos y hyp
        have hfire : headFires (hornModel cls U) y.v c.lits = true := by
          refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hye ▸ hy), ?_⟩
          refine List.all_eq_true.mpr (fun l hl => ?_)
          cases hd : decide (l = posLit y.v) with
          | true => rfl
          | false =>
            have hne : ¬ l = posLit y.v := of_decide_eq_false hd
            cases hlp : l.pos with
            | true => exact absurd ((hh c hc l hl y hy hlp hyp).trans hye) hne
            | false =>
              have e := (forced_neg_of_false hlp (hfalse l hl)).2
              rw [hlp] at e
              exact e
        have hf : fires cls U (hornModel cls U) y.v = true :=
          Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨c, hc, hfire⟩))
        have htrue : litVal (hornModel cls U) y = true := by
          rw [hye]
          exact hornModel_closed y.v hf
        exact absurd htrue (hfalse y hy)
      | false =>
        have hneg : ∀ l ∈ c.lits, ¬ l.pos = true := List.any_eq_false.mp hpos
        refine absurd (conflict_of_clause c hc (fun l hl => ?_)) hnc
        cases hlp : l.pos with
        | true => exact absurd hlp (hneg l hl)
        | false => exact (forced_neg_of_false hlp (hfalse l hl)).1
  · cases l with
    | mk w p =>
      cases p with
      | true =>
        have hf : fires cls U (hornModel cls U) w = true :=
          Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hl))
        exact hornModel_closed w hf
      | false =>
        show (!hornModel cls U w) = true
        cases ha : hornModel cls U w with
        | false => rfl
        | true => exact absurd ⟨⟨w, false⟩, Forced.unit _ hl, upIter_forced _ w ha⟩ hnc

/-- **For Horn clauses, unit propagation decides satisfiability** with units. -/
theorem horn_model_iff (hh : ∀ c ∈ cls, c.Horn) :
    (∃ a : Assign, (∀ c ∈ cls, SatClause a c) ∧ ∀ l ∈ U, litVal a l = true) ↔
      ¬ Conflict cls U :=
  ⟨fun ⟨a, hc, hu⟩ => not_conflict_of_model a hc hu,
    fun hnc => ⟨hornModel cls U, horn_model hh hnc⟩⟩

/-- **A Horn formula is satisfiable iff unit propagation over its clauses finds no conflict.** -/
theorem Cnf.horn_satisfiable_iff (φ : Cnf) (hh : φ.Horn) :
    Satisfiable φ ↔ ¬ Conflict φ.clauses [] :=
  ⟨fun ⟨a, ha⟩ => not_conflict_of_model a ha (fun _ h => absurd h List.not_mem_nil),
    fun hnc => ⟨hornModel φ.clauses [], (horn_model hh hnc).1⟩⟩

/-- info: 'AbsSat.Cnf.horn_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms horn_model

/-- info: 'AbsSat.Cnf.horn_model_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms horn_model_iff

/-- info: 'AbsSat.Cnf.Cnf.horn_satisfiable_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cnf.horn_satisfiable_iff

end AbsSat.Cnf
