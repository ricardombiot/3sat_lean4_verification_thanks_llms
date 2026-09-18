-- lean_project/AbsSat/GraphPath/Model/Answer.lean
import AbsSat.GraphPath.Model.DeclaredVerdict

/-!
# Every answer the machine gives is correct

The author's proposal (v141): answer SAT only together with a **certificate** — an assignment the
machine reads and that is checked against `φ`. Then no answer the machine gives can be wrong, with no
hypothesis at all; the only thing left open is whether it ever has to say *"I don't know"*.

* `readGreedy` — the author's reader, on the Improves machine: variable by variable, pin `v = 0`, review
  (`filterAllAgg`), and if the state is no longer valid pin `v = 1` instead; stop if neither is valid.
* `answer φ` — **UNSAT** if no reader's state of the last line is valid; **SAT a** if the reader reads an
  assignment `a` from some valid reader's state and `a` satisfies `φ` (checked by `satB`); **unknown**
  otherwise.

Theorems, all with **no hypothesis**:

* **`answer_unsat_sound`** — if the machine answers UNSAT, `φ` is unsatisfiable.
* **`answer_sat_sound`** — if the machine answers SAT `a`, `a` satisfies `φ`.
* **`answer_ne_unsat_of_sat`** — on a satisfiable formula the machine never answers UNSAT.

And under the declared hypothesis (`GhostsLine`, v141):

* **`answer_unsat_of_unsat`** — on an unsatisfiable formula the machine answers UNSAT.

So the only imperfection the machine could have is answering *unknown* on a satisfiable formula, i.e. the
reader getting stuck; measured, it never does.
-/

namespace AbsSat.GraphPath.Model.Answer

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.RoundInvariant (GhostsLine)

variable (φ : Cnf)

/-- The three answers. -/
inductive Answer where
  | unsat
  | sat (a : Assign)
  | unknown

/-- **The author's reader** on the Improves machine: pin each variable's value, `0` first, reviewing
after each pin; `none` if neither value keeps the state valid. -/
def readGreedy : Nat → Nat → GPathM → Option (List Bool)
  | 0, _, _ => some []
  | n + 1, v, g =>
    let g0 := filterAllAgg g [{ step := 2 * (v : Int), index := 0 }]
    if isValid g0 then (readGreedy n (v + 1) g0).map (false :: ·)
    else
      let g1 := filterAllAgg g [{ step := 2 * (v : Int), index := 1 }]
      if isValid g1 then (readGreedy n (v + 1) g1).map (true :: ·) else none

/-- The assignment a list of values spells. -/
def toAssign (bs : List Bool) : Assign := fun v => bs.getD v false

/-- Read an assignment from a reader's state and keep it only if it satisfies `φ`. -/
def certificate (g : GPathM) : Option Assign :=
  if isValid g then
    (readGreedy φ.nVars 0 g).bind (fun bs => if satB (toAssign bs) φ then some (toAssign bs) else none)
  else none

/-- **The machine's answer.** -/
def answer : Answer :=
  let readers := (pureRunW φ).map (fun kv => filterAllAgg kv.2 [])
  if readers.all (fun g => !isValid g) then .unsat
  else match readers.findSome? (certificate φ) with
    | some a => .sat a
    | none => .unknown

-- ============================================================
-- Every answer is correct
-- ============================================================

theorem all_invalid_of_answer_unsat (h : answer φ = .unsat) :
    ∀ kv ∈ pureRunW φ, isValid (filterAllAgg kv.2 []) = false := by
  unfold answer at h
  simp only at h
  split at h
  · next hall =>
    intro kv hkv
    have := List.all_eq_true.mp hall (filterAllAgg kv.2 []) (List.mem_map.mpr ⟨kv, hkv, rfl⟩)
    simpa using this
  · split at h <;> cases h

/-- **UNSAT is correct**, with no hypothesis: if the machine answers UNSAT, `φ` has no model. -/
theorem answer_unsat_sound (hwf : WF φ) (h : answer φ = .unsat) : ¬ Satisfiable φ := by
  intro hs
  obtain ⟨kv, hkv, hv⟩ := CertificateSet.exists_valid_of_sat φ hwf hs
  have := all_invalid_of_answer_unsat φ h kv hkv
  rw [hv] at this
  exact absurd this (by decide)

/-- **SAT is correct**, with no hypothesis: the certificate the machine returns satisfies `φ`. -/
theorem answer_sat_sound (a : Assign) (h : answer φ = .sat a) : Sat a φ := by
  unfold answer at h
  simp only at h
  split at h
  · cases h
  · split at h
    · next b hb =>
      cases h
      obtain ⟨g, _, hg⟩ := List.exists_of_findSome?_eq_some hb
      unfold certificate at hg
      split at hg
      · obtain ⟨bs, _, hbs⟩ := Option.bind_eq_some_iff.mp hg
        split at hbs
        · next hsat =>
          cases hbs
          exact (satB_iff _ φ).mp hsat
        · cases hbs
      · cases hg
    · cases h

/-- **On a satisfiable formula the machine never answers UNSAT**, with no hypothesis. -/
theorem answer_ne_unsat_of_sat (hwf : WF φ) (hs : Satisfiable φ) : answer φ ≠ .unsat :=
  fun h => answer_unsat_sound φ hwf h hs

/-- **On an unsatisfiable formula the machine answers UNSAT**, under the declared hypothesis. -/
theorem answer_unsat_of_unsat (hwf : WF φ) (hG : GhostsLine φ) (hns : ¬ Satisfiable φ) :
    answer φ = .unsat := by
  unfold answer
  simp only
  have hall : ((pureRunW φ).map (fun kv => filterAllAgg kv.2 [])).all (fun g => !isValid g) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hg
    cases hv : isValid (filterAllAgg kv.2 []) with
    | false => rfl
    | true => exact absurd (DeclaredVerdict.sat_sound φ hwf hG kv hkv hv) hns
  rw [if_pos hall]

/-- info: 'AbsSat.GraphPath.Model.Answer.answer_unsat_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_unsat_sound

/-- info: 'AbsSat.GraphPath.Model.Answer.answer_sat_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_sat_sound

/-- info: 'AbsSat.GraphPath.Model.Answer.answer_unsat_of_unsat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_unsat_of_unsat

end AbsSat.GraphPath.Model.Answer
