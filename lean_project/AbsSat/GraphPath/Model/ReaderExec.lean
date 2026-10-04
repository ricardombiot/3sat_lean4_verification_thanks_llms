-- lean_project/AbsSat/GraphPath/Model/ReaderExec.lean
import AbsSat.GraphPath.Model.PinDeath

/-!
# The reader without backtracking, as a program

`ReaderAgg` has the reading loop as a relation (`ReadFrom`, `PickSomeAgg`). This module runs it. At each
round the reader takes the first step that still has a choice, tries its nodes in order, pins the first
one that the aggressive review leaves valid, and goes on. **It never undoes a pin.** Each round costs at
most one review per node of the step, and the rounds are bounded by `measure` (every pin removes
something).

* `readerVerdictW_sound` — **no hypothesis**: if the reader finishes on some state of the final line, the
  formula is satisfiable. Whatever the tables borrowed, the reader only finishes on a state that denotes
  a path, and that path is a model.
* `readerVerdictW_complete` — the reader finishes as soon as, at every state it visits, the first step
  with a choice has a node whose pin keeps the graph valid (`ProgressAgg`). That is the one thing left
  open on this route: the reader never gets stuck.
-/

namespace AbsSat.GraphPath.Model.ReaderExec

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice)
open AbsSat.GraphPath.Model.PureDriverImproves

-- ============================================================
-- The program
-- ============================================================

/-- The first step that still has a choice. -/
def firstChoice (g : GPathM) : Option Int := (intRange 0 (g.current_step - 1)).find? (choiceAt g)

/-- Pin the first node of step `k` that the aggressive review leaves valid. -/
def tryPins (g : GPathM) (k : Int) : Option GPathM :=
  (ownersAt g.gowners k).findSome? (fun q =>
    if isValid (filterAllAgg g [q.id]) then some (filterAllAgg g [q.id]) else none)

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

def readAgg (g : GPathM) : Option GPathM := if isValid g then readLoop (measure g) g else none

/-- **The reader's verdict**: SAT when the reader finishes on some state of the final line. -/
def readerVerdictW (φ : Cnf) : Bool :=
  (pureRunW φ).any (fun kv => (readAgg (filterAllAgg kv.2 [])).isSome)

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
      l.findSome? (fun q => if isValid (filterAllAgg g [q.id]) then some (filterAllAgg g [q.id]) else none)
        = some h → ∃ q ∈ l, h = filterAllAgg g [q.id] ∧ isValid h = true := by
  intro l
  induction l with
  | nil => intro h hs; simp at hs
  | cons a rest ih =>
    intro h hs
    simp only [List.findSome?_cons] at hs
    by_cases hv : isValid (filterAllAgg g [a.id]) = true
    · rw [if_pos hv] at hs
      cases hs
      exact ⟨a, List.mem_cons_self, rfl, hv⟩
    · rw [if_neg hv] at hs
      obtain ⟨q, hq, e, hvq⟩ := ih h hs
      exact ⟨q, List.mem_cons_of_mem _ hq, e, hvq⟩

theorem findSome_isSome (g : GPathM) :
    ∀ (l : List PathNodeId), (∃ q ∈ l, isValid (filterAllAgg g [q.id]) = true) →
      (l.findSome? (fun q => if isValid (filterAllAgg g [q.id]) then some (filterAllAgg g [q.id])
        else none)).isSome = true := by
  intro l
  induction l with
  | nil => intro ⟨q, hq, _⟩; cases hq
  | cons a rest ih =>
    intro ⟨q, hq, hv⟩
    simp only [List.findSome?_cons]
    by_cases ha : isValid (filterAllAgg g [a.id]) = true
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact absurd hv ha
      · exact ih ⟨q, hq', hv⟩

-- ============================================================
-- Soundness: no hypothesis
-- ============================================================

/-- **Whatever the reader finishes from denotes a path.** -/
theorem readLoop_sound : ∀ (n : Nat) (g h : GPathM), ReadableAgg g → isValid g = true →
    readLoop n g = some h → Inhabited g := by
  intro n
  induction n with
  | zero =>
    intro g h hR hv hs
    simp only [readLoop] at hs
    by_cases hc : hasChoice g = true
    · rw [if_pos hc] at hs; cases hs
    · have hc' : hasChoice g = false := by simpa using hc
      exact Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv hc'
  | succ n ih =>
    intro g h hR hv hs
    simp only [readLoop] at hs
    cases hf : firstChoice g with
    | none =>
      exact Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv
        (noChoice_of_firstChoice_none g hf)
    | some k =>
      cases ht : tryPins g k with
      | none => simp only [hf, ht] at hs; cases hs
      | some h' =>
        simp only [hf, ht] at hs
        obtain ⟨q, _, e, hv'⟩ := findSome_valid g _ h' ht
        subst e
        obtain ⟨p, hp⟩ := ih _ h (ReadableAgg_filterAllAgg g hR [q.id]) hv' hs
        exact ⟨p, denot_of_pruned (pruned_filterAllAgg g [q.id]) (RCtx_of_readableAgg g hR).nodup p hp⟩

/-- **A positive verdict of the reader is always right.** -/
theorem readerVerdictW_sound (φ : Cnf) (hwf : WF φ) (h : readerVerdictW φ = true) : Satisfiable φ := by
  unfold readerVerdictW at h
  obtain ⟨kv, hkv, hs⟩ := List.any_eq_true.mp h
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  unfold readAgg at hs
  by_cases hv : isValid (filterAllAgg kv.2 []) = true
  · rw [if_pos hv] at hs
    obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨p, hp⟩ := readLoop_sound _ _ res ⟨kv.2, [], hm.rctx, rfl⟩ hv hres
    exact ReaderAggRun.sat_of_denot_final φ hwf kv hkv p
      (denot_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup p hp)
  · rw [if_neg hv] at hs; cases hs

-- ============================================================
-- Completeness: the reader never gets stuck
-- ============================================================

/-- **The reader never gets stuck**, from `g₀`: at every state it can visit, the first step with a
choice has a node whose pin keeps the graph valid. -/
def ProgressAgg (g₀ : GPathM) : Prop :=
  ∀ g, ReadFrom g₀ g → isValid g = true → ∀ k, firstChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAllAgg g [q.id]) = true

theorem readLoop_complete (g₀ : GPathM) (hP : ProgressAgg g₀) :
    ∀ (n : Nat) (g : GPathM), measure g ≤ n → ReadFrom g₀ g → isValid g = true →
      (readLoop n g).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro g hm hF hv
    simp only [readLoop]
    by_cases hc : hasChoice g = true
    · obtain ⟨k, hk⟩ := firstChoice_of_hasChoice g hc
      obtain ⟨q, hq, _⟩ := hP g hF hv k hk
      have := measure_lt_of_choiceAt g k (choiceAt_of_firstChoice g k hk) q hq
      omega
    · rw [if_neg hc]; rfl
  | succ n ih =>
    intro g hm hF hv
    simp only [readLoop]
    cases hf : firstChoice g with
    | none => rfl
    | some k =>
      obtain ⟨q₀, hq₀, hv₀⟩ := hP g hF hv k hf
      have hsome := findSome_isSome g (ownersAt g.gowners k) ⟨q₀, hq₀, hv₀⟩
      obtain ⟨h', ht⟩ := Option.isSome_iff_exists.mp hsome
      have ht' : tryPins g k = some h' := ht
      simp only [ht']
      obtain ⟨q, hq, e, hv'⟩ := findSome_valid g _ h' ht
      subst e
      have hlt := measure_lt_of_choiceAt g k (choiceAt_of_firstChoice g k hf) q hq
      exact ih _ (by omega) (ReadFrom.pin g q.id hF hv) hv'

/-- **The reader finishes on every valid state it never gets stuck on.** -/
theorem readAgg_complete (g₀ : GPathM) (hv : isValid g₀ = true) (hP : ProgressAgg g₀) :
    (readAgg g₀).isSome = true := by
  unfold readAgg
  rw [if_pos hv]
  exact readLoop_complete g₀ hP _ g₀ (Nat.le_refl _) ReadFrom.start hv

/-- **The reader's verdict is positive** on a state of the final line that one review leaves valid and
on which the reader never gets stuck. -/
theorem readerVerdictW_complete (φ : Cnf) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) (hP : ProgressAgg (filterAllAgg kv.2 [])) :
    readerVerdictW φ = true :=
  List.any_eq_true.mpr ⟨kv, hkv, readAgg_complete _ hv hP⟩

/-- info: 'AbsSat.GraphPath.Model.ReaderExec.readerVerdictW_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_sound

/-- info: 'AbsSat.GraphPath.Model.ReaderExec.readerVerdictW_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_complete

-- ============================================================
-- The reader never gets stuck where a chain survives
-- ============================================================

/-- **A chain gives the reader its pick.** At a step with a choice, pinning the chain's own node keeps
the chain, so it keeps the graph valid. -/
theorem pickSome_of_chain (g : GPathM) (sel : Int → PathNodeId) (hsc : ChainSound g sel) :
    PickSomeAgg g := by
  intro hch
  obtain ⟨k, hk, hck⟩ := List.any_eq_true.mp hch
  have h0 : 0 ≤ k := mem_intRange_lower hk
  have h1 : k < g.current_step := by have := mem_intRange_upper hk; omega
  obtain ⟨hsome, hstep⟩ := hsc.chain.1.1 k h0 h1
  refine ⟨k, h0, h1, hck, sel k, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨hsc.chain.2.2 k h0 h1, beq_iff_eq.mpr hstep⟩
  · refine PickInduction.isValid_of_ChainG _ sel (ChainSound_filterAllAgg g [(sel k).id] sel hsc ?_).chain
    intro req hreq _ _
    rw [List.mem_singleton.mp hreq, hstep]

/-- **The reader never gets stuck, from the chains.** If every valid state the reader can reach carries a
chain — what hereditary validity gives (`HereditaryValid.ValidWitAt`, through the branch's completeness)
— then the reader finishes. -/
theorem progressAgg_of_chains (g₀ : GPathM)
    (hC : ∀ g, ReadFrom g₀ g → isValid g = true → ∃ sel, ChainSound g sel) : ProgressAgg g₀ := by
  intro g hF hv k hk
  obtain ⟨sel, hsc⟩ := hC g hF hv
  have hmem := List.mem_of_find?_eq_some hk
  have h0 : 0 ≤ k := mem_intRange_lower hmem
  have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
  obtain ⟨hsome, hstep⟩ := hsc.chain.1.1 k h0 h1
  refine ⟨sel k, List.mem_filter.mpr ⟨hsc.chain.2.2 k h0 h1, beq_iff_eq.mpr hstep⟩, ?_⟩
  refine PickInduction.isValid_of_ChainG _ sel (ChainSound_filterAllAgg g [(sel k).id] sel hsc ?_).chain
  intro req hreq _ _
  rw [List.mem_singleton.mp hreq, hstep]

/-- **The reader's verdict is positive when chains survive.** -/
theorem readerVerdictW_of_chains (φ : Cnf) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hC : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → ∃ sel, ChainSound g sel) :
    readerVerdictW φ = true :=
  readerVerdictW_complete φ kv hkv hv (progressAgg_of_chains _ hC)

/-- info: 'AbsSat.GraphPath.Model.ReaderExec.pickSome_of_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pickSome_of_chain

end AbsSat.GraphPath.Model.ReaderExec
