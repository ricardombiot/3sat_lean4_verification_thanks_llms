-- lean/improves_bin/AbsSatBin/GraphPath/Model/ReaderExec.lean
import AbsSatBin.GraphPath.Model.Reader
import AbsSatBin.GraphPath.Model.Decision

/-!
# The reader without backtracking, as a program — **revised** for the bin map

The reading program is `lean_project`'s, with two changes:

* it reads the final line of the bin machine (`PureDriver.pureRun`: no weak requirements, UP with
  prohibited windows) instead of `pureRunW`, and its soundness goes through `L7.sat_of_inhabited`;
* **each pin is followed by the plain review** (`filterAll`), not the aggressive one. The review
  already carries the pair rule (`cleanPair`), and with it the aggressive sweep does nothing at the
  review's fixpoint (`lean_project`'s `PairHelly.aggInactive_of_revOk`); Julia dropped it too
  (commit `4c644ac`).

At each round the reader takes the first step that still has a choice, tries its nodes in order, pins
the first one that the review leaves valid, and goes on. **It never undoes a pin.** The rounds are
bounded by `measure` (every pin removes something).

* `readerVerdictW_sound` — **no hypothesis**: if the reader finishes on some state of the final line,
  the formula is satisfiable.
* Completeness lives in `ReaderPrefix` (the reader reads a prefix) and `PinChainBin`.
-/

namespace AbsSatBin.GraphPath.Model.ReaderExec

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PickInduction (choiceAt hasChoice)
open AbsSatBin.GraphPath.Model.PureDriver

-- ============================================================
-- The program
-- ============================================================

/-- The first step that still has a choice. -/
def firstChoice (g : GPathM) : Option Int := (intRange 0 (g.current_step - 1)).find? (choiceAt g)

/-- Pin the first node of step `k` that the review leaves valid. -/
def tryPins (g : GPathM) (k : Int) : Option GPathM :=
  (ownersAt g.gowners k).findSome? (fun q =>
    if isValid (filterAll g [q.id]) then some (filterAll g [q.id]) else none)

/-- The reading loop: never backtracks. -/
def readLoop : Nat → GPathM → Option GPathM
  | 0, g => if hasChoice g then none else some g
  | n + 1, g =>
    match firstChoice g with
    | none => some g
    | some k =>
      match tryPins g k with
      | none => none
      | some h => readLoop n h

def readG (g : GPathM) : Option GPathM := if isValid g then readLoop (measure g) g else none

/-- **The reader's verdict**: SAT when the reader finishes on some state of the final line. -/
def readerVerdictW (φ : Cnf) : Bool :=
  (pureRun φ).any (fun kv => (readG (filterAll kv.2 [])).isSome)

-- ============================================================
-- The pieces
-- ============================================================

theorem noChoice_of_firstChoice_none (g : GPathM) (h : firstChoice g = none) : hasChoice g = false := by
  unfold firstChoice at h
  unfold hasChoice
  rw [List.find?_eq_none] at h
  exact List.any_eq_false.mpr (fun k hk => by simpa using h k hk)

theorem choiceAt_of_firstChoice (g : GPathM) (k : Int) (h : firstChoice g = some k) :
    choiceAt g k = true := List.find?_some h

theorem firstChoice_of_hasChoice (g : GPathM) (h : hasChoice g = true) : ∃ k, firstChoice g = some k := by
  cases hf : firstChoice g with
  | none => rw [noChoice_of_firstChoice_none g hf] at h; cases h
  | some k => exact ⟨k, rfl⟩

theorem findSome_valid (g : GPathM) :
    ∀ (l : List PathNodeId) (h : GPathM),
      l.findSome? (fun q => if isValid (filterAll g [q.id]) then some (filterAll g [q.id]) else none)
        = some h → ∃ q ∈ l, h = filterAll g [q.id] ∧ isValid h = true := by
  intro l
  induction l with
  | nil => intro h hs; simp at hs
  | cons a rest ih =>
    intro h hs
    simp only [List.findSome?_cons] at hs
    by_cases hv : isValid (filterAll g [a.id]) = true
    · rw [if_pos hv] at hs
      cases hs
      exact ⟨a, List.mem_cons_self, rfl, hv⟩
    · rw [if_neg hv] at hs
      obtain ⟨q, hq, e, hvq⟩ := ih h hs
      exact ⟨q, List.mem_cons_of_mem _ hq, e, hvq⟩

theorem findSome_isSome (g : GPathM) :
    ∀ (l : List PathNodeId), (∃ q ∈ l, isValid (filterAll g [q.id]) = true) →
      (l.findSome? (fun q => if isValid (filterAll g [q.id]) then some (filterAll g [q.id])
        else none)).isSome = true := by
  intro l
  induction l with
  | nil => intro ⟨q, hq, _⟩; cases hq
  | cons a rest ih =>
    intro ⟨q, hq, hv⟩
    simp only [List.findSome?_cons]
    by_cases ha : isValid (filterAll g [a.id]) = true
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact absurd hv ha
      · exact ih ⟨q, hq', hv⟩

-- ============================================================
-- Soundness: no hypothesis
-- ============================================================

/-- **Whatever the reader finishes from denotes a path.** -/
theorem readLoop_sound : ∀ (n : Nat) (g h : GPathM), Reader.Readable g → isValid g = true →
    readLoop n g = some h → Inhabited g := by
  intro n
  induction n with
  | zero =>
    intro g h hR hv hs
    simp only [readLoop] at hs
    by_cases hc : hasChoice g = true
    · rw [if_pos hc] at hs; cases hs
    · have hc' : hasChoice g = false := by simpa using hc
      exact Reader.inhabited_of_noChoice_readable g hR hv hc'
  | succ n ih =>
    intro g h hR hv hs
    simp only [readLoop] at hs
    cases hf : firstChoice g with
    | none =>
      exact Reader.inhabited_of_noChoice_readable g hR hv
        (noChoice_of_firstChoice_none g hf)
    | some k =>
      cases ht : tryPins g k with
      | none => simp only [hf, ht] at hs; cases hs
      | some h' =>
        simp only [hf, ht] at hs
        obtain ⟨q, _, e, hv'⟩ := findSome_valid g _ h' ht
        subst e
        obtain ⟨p, hp⟩ := ih _ h (Reader.Readable_filterAll g hR [q.id]) hv' hs
        exact ⟨p, denot_of_pruned (pruned_filterAll g [q.id]) (Reader.RCtx_of_readable g hR).nodup p hp⟩

/-- **A positive verdict of the reader is always right.** -/
theorem readerVerdictW_sound (φ : Cnf) (hbd : Bounded φ) (h : readerVerdictW φ = true) :
    Satisfiable φ := by
  unfold readerVerdictW at h
  obtain ⟨kv, hkv, hs⟩ := List.any_eq_true.mp h
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hok := Decision.stateOk_pureRun φ hzero kv hkv
  have hreach : Reachable (reqOf φ) (isProhibited φ) kv.2 :=
    MapReachable.reachable_of_mapReachable φ hbd kv.2 hok.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have hrc := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) kv.2 hnd hreach
  unfold readG at hs
  by_cases hv : isValid (filterAll kv.2 []) = true
  · rw [if_pos hv] at hs
    obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨p, hp⟩ := readLoop_sound _ _ res ⟨kv.2, [], hrc, rfl⟩ hv hres
    exact L7.satisfiable_of_inhabited φ hbd kv.2 hok.reach (by rw [hok.step]; omega)
      ⟨p, denot_of_pruned (pruned_filterAll kv.2 []) hnd p hp⟩
  · rw [if_neg hv] at hs; cases hs

/-- info: 'AbsSatBin.GraphPath.Model.ReaderExec.readerVerdictW_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_sound

end AbsSatBin.GraphPath.Model.ReaderExec
