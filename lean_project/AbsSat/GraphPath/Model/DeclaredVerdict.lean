-- lean_project/AbsSat/GraphPath/Model/DeclaredVerdict.lean
import AbsSat.GraphPath.Model.RoundInvariant
import AbsSat.GraphPath.Model.CertificateSet

/-!
# The Improves verdict, with one declared hypothesis: the round invariant

This module states the final result of the verification of the *Improves* machine.

**The declared hypothesis** (`RoundInvariant.GhostsLine`), in words: *after one pass of the base review
on a pinned line state whose tables were exact, every compatibility that no surviving path holds is
asymmetric, or shares no owner at some step* — i.e. it is exactly what the two legs of the author's
aggressive filter detect.

It is measured with no exception (probe `helly ghosts`: 3,02 M ghost entries over every map pin of every
exact state of K4 and parity) and it speaks about **one pass of one operation** of the machine, not about
the machine's states as a whole. It replaces `Descent.CommonOwner` (v133) as the stated assumption.

With it:

* **`unsat_sound`** — *no hypothesis*: an empty last line means `φ` is unsatisfiable.
* **`sat_sound`** — under the declared hypothesis: a valid reader's state means `φ` is satisfiable.
* **`verdict_iff`** — under the declared hypothesis, the machine decides: some reader's state of the last
  line is valid **iff** `φ` is satisfiable (the `⇐` half with no hypothesis).
-/

namespace AbsSat.GraphPath.Model.DeclaredVerdict

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.RoundInvariant (GhostsLine sat_of_ghosts)

variable (φ : Cnf)

/-- **UNSAT is sound, with no hypothesis.** -/
theorem unsat_sound (hwf : WF φ) (h : pureRunW φ = []) : ¬ Satisfiable φ :=
  fun hs => ConservationImproves.pureRunW_ne_nil φ hwf hs h

/-- **SAT is sound, under the declared hypothesis.** -/
theorem sat_sound (hwf : WF φ) (hG : GhostsLine φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_ghosts φ hwf hG kv hkv hv

/-- **The machine decides, under the declared hypothesis.** Some reader's state of the last line is
valid iff `φ` is satisfiable; the `⇐` half holds with no hypothesis. -/
theorem verdict_iff (hwf : WF φ) (hG : GhostsLine φ) :
    (∃ kv ∈ pureRunW φ, isValid (filterAllAgg kv.2 []) = true) ↔ Satisfiable φ :=
  ⟨fun ⟨kv, hkv, hv⟩ => sat_sound φ hwf hG kv hkv hv,
   fun h => CertificateSet.exists_valid_of_sat φ hwf h⟩

/-- info: 'AbsSat.GraphPath.Model.DeclaredVerdict.unsat_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unsat_sound

/-- info: 'AbsSat.GraphPath.Model.DeclaredVerdict.verdict_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdict_iff

end AbsSat.GraphPath.Model.DeclaredVerdict
