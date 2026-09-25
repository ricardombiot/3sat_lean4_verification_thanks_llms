-- lean/improves_bin/AbsSatBin/GraphPath/Model/ReaderPrefix.lean
import AbsSatBin.GraphPath.Model.ReaderExec

/-!
# The reader reads a prefix: completeness reduced to one pin (`PinChain`)

The reader finishes when every valid state it visits carries a sound chain (it can then pin the
chain's own node). This module narrows the states and the obligation.

* **The states** (`ReadFirst`). The reader only pins
  at `firstChoice`, and only a pin the review leaves valid (`tryPins`). `ReadFirst` is that
  relation, and `readLoop_complete_first` runs the loop on it.
* **The prefix** (`PrefixUpTo`). Below `firstChoice` no step has a choice
  (`prefixUpTo_firstChoice`), and a pin at `k` removes the choice at `k` without adding one below
  (`prefixUpTo_pin`). So the first step with a choice only goes up (`firstChoice_pin_gt`): the reader
  fixes the steps `0, 1, 2, …` in order and never reopens one. On the bin map a choice step has
  two map nodes, so each pin fixes one bit.
* **The start** (`start_chain`). A satisfying assignment leaves a sound chain in the state the reader
  starts from (`Conservation.chainSound_along`, kept by `filterAll … []`).
* **The one open obligation** (`PinChain`). At a reader state with a chain and a fixed prefix, a pin
  at `firstChoice` that the review leaves valid keeps *some* sound chain.

`readerVerdictW_iff_of_pinChain`: with `Bounded φ` and `PinChain` on the starting states, the reader
decides `φ`. Nothing here uses `SegGood`, `TriExact`, `PairExact` or segments that do not start at 0.
-/

namespace AbsSatBin.GraphPath.Model.ReaderPrefix

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.PickInduction (choiceAt hasChoice)
open AbsSatBin.GraphPath.Model.PureDriver

-- ============================================================
-- The states the reader visits
-- ============================================================

/-- The states the reader visits from `g₀`: every pin is at the first step with a choice, of a live
node of that step, and leaves the graph valid (what `tryPins` returns). -/
inductive ReadFirst (g₀ : GPathM) : GPathM → Prop where
  | start : ReadFirst g₀ g₀
  | pin (g : GPathM) (k : Int) (q : PathNodeId) : ReadFirst g₀ g → isValid g = true →
      firstChoice g = some k → q ∈ ownersAt g.gowners k →
      isValid (filterAll g [q.id]) = true → ReadFirst g₀ (filterAll g [q.id])

/-- **The reader never gets stuck**, on the states it actually visits. -/
def ProgressFirst (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → ∀ k, firstChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAll g [q.id]) = true

theorem readLoop_complete_first (g₀ : GPathM) (hP : ProgressFirst g₀) :
    ∀ (n : Nat) (g : GPathM), measure g ≤ n → ReadFirst g₀ g → isValid g = true →
      (readLoop n g).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro g hm hF hv
    simp only [readLoop]
    by_cases hc : hasChoice g = true
    · obtain ⟨k, hk⟩ := firstChoice_of_hasChoice g hc
      obtain ⟨q, hq, _⟩ := hP g hF hv k hk
      have := PickInduction.measure_lt_of_choiceAt g k (choiceAt_of_firstChoice g k hk) q hq
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
      have hlt := PickInduction.measure_lt_of_choiceAt g k (choiceAt_of_firstChoice g k hf) q hq
      exact ih _ (by omega) (ReadFirst.pin g k q hF hv hf hq hv') hv'

theorem readG_complete_first (g₀ : GPathM) (hv : isValid g₀ = true) (hP : ProgressFirst g₀) :
    (readG g₀).isSome = true := by
  unfold readG
  rw [if_pos hv]
  exact readLoop_complete_first g₀ hP _ g₀ (Nat.le_refl _) ReadFirst.start hv

-- ============================================================
-- The prefix: fixed below the first choice, and growing
-- ============================================================

/-- No step below `k` has a choice: the steps `0 … k-1` are fixed. -/
def PrefixUpTo (g : GPathM) (k : Int) : Prop := ∀ i, 0 ≤ i → i < k → choiceAt g i = false

/-- `List.find?_range_eq_some` without `Classical.choice`: what `find?` skips is false. -/
theorem find?_range_below (p : Nat → Bool) :
    ∀ (n j : Nat), (List.range n).find? p = some j → ∀ i, i < j → p i = false := by
  intro n
  induction n with
  | zero => intro j h; simp at h
  | succ n ih =>
    intro j h i hij
    rw [List.range_succ, List.find?_append] at h
    cases h1 : (List.range n).find? p with
    | some j' =>
      rw [h1] at h
      cases h
      exact ih _ h1 i hij
    | none =>
      rw [h1] at h
      have hj : n = j := by
        simp only [Option.none_or, List.find?_cons, List.find?_nil] at h
        split at h
        · cases h; rfl
        · cases h
      have hn := List.find?_eq_none.mp h1 i (List.mem_range.mpr (by omega))
      cases hp : p i
      · rfl
      · exact absurd hp hn

theorem prefixUpTo_firstChoice (g : GPathM) (k : Int) (h : firstChoice g = some k) :
    PrefixUpTo g k := by
  intro i hi0 hik
  unfold firstChoice intRange at h
  rw [List.find?_map] at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
  have hlt := find?_range_below _ _ j hj
  have hij : i.toNat < j := by simp only [Int.ofNat_eq_natCast] at hik; omega
  have := hlt i.toNat hij
  have hcast : (0 : Int) + Int.ofNat i.toNat = i := by simp only [Int.ofNat_eq_natCast]; omega
  have hmax : max i 0 = i := by omega
  simpa [Function.comp, hcast, hmax] using this

theorem choiceAt_false_of_eq (g : GPathM) (k : Int) (d : NodeId)
    (h : ∀ x ∈ ownersAt g.gowners k, x.id = d) : choiceAt g k = false := by
  cases hc : choiceAt g k with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, hx2⟩ := List.any_eq_true.mp hc
    obtain ⟨y, hy, hne⟩ := List.any_eq_true.mp hx2
    rw [h x hx, h y hy] at hne
    simp at hne

theorem mem_ownersAt_of_pruned {g g' : GPathM} (hp : Pruned g g') (k : Int) (x : PathNodeId)
    (hx : x ∈ ownersAt g'.gowners k) : x ∈ ownersAt g.gowners k := by
  obtain ⟨hmem, hs⟩ := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨hp.gowners_sub x hmem, hs⟩

/-- Pruning never creates a choice. -/
theorem choiceAt_false_of_pruned {g g' : GPathM} (hp : Pruned g g') (k : Int)
    (h : choiceAt g k = false) : choiceAt g' k = false := by
  cases hc : choiceAt g' k with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, hx2⟩ := List.any_eq_true.mp hc
    obtain ⟨y, hy, hne⟩ := List.any_eq_true.mp hx2
    have : choiceAt g k = true :=
      List.any_eq_true.mpr ⟨x, mem_ownersAt_of_pruned hp k x hx,
        List.any_eq_true.mpr ⟨y, mem_ownersAt_of_pruned hp k y hy, hne⟩⟩
    rw [h] at this
    cases this

/-- After a pin at `q`, every live entry of `q`'s step is `q`'s map node. -/
theorem ownersAt_pin (g : GPathM) (q : PathNodeId) (x : PathNodeId)
    (hx : x ∈ ownersAt (filterAll g [q.id]).gowners q.id.step) : x.id = q.id := by
  have hp : Pruned (filterRequire g q.id) (filterAll g [q.id]) := pruned_review _
  obtain ⟨hmem, hs⟩ := List.mem_filter.mp (mem_ownersAt_of_pruned hp _ x hx)
  obtain ⟨_, hkeep⟩ := List.mem_filter.mp hmem
  have hstep : x.id.step = q.id.step := eq_of_beq hs
  simp only [hstep, bne_self_eq_false, Bool.false_or] at hkeep
  exact eq_of_beq hkeep

/-- **A pin at the first choice extends the fixed prefix by one step.** -/
theorem prefixUpTo_pin (g : GPathM) (k : Int) (q : PathNodeId) (hf : firstChoice g = some k)
    (hq : q ∈ ownersAt g.gowners k) : PrefixUpTo (filterAll g [q.id]) (k + 1) := by
  have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
  intro i hi0 hik
  by_cases hik' : i < k
  · exact choiceAt_false_of_pruned (pruned_filterAll g [q.id]) i
      (prefixUpTo_firstChoice g k hf i hi0 hik')
  · have hi : i = k := by omega
    subst hi
    exact choiceAt_false_of_eq _ _ q.id (fun x hx => ownersAt_pin g q x (by rw [hqs]; exact hx))

/-- **The first choice only goes up**: the reader never reopens a step it has fixed. -/
theorem firstChoice_pin_gt (g : GPathM) (k k' : Int) (q : PathNodeId) (hf : firstChoice g = some k)
    (hq : q ∈ ownersAt g.gowners k) (hf' : firstChoice (filterAll g [q.id]) = some k') :
    k < k' := by
  have hc := choiceAt_of_firstChoice _ k' hf'
  have h0 : 0 ≤ k' := by
    unfold firstChoice at hf'
    exact mem_intRange_lower (List.mem_of_find?_eq_some hf')
  by_cases hlt : k < k'
  · exact hlt
  · rw [prefixUpTo_pin g k q hf hq k' h0 (by omega)] at hc
    cases hc

-- ============================================================
-- The one open obligation, and what it gives
-- ============================================================

/-- **`PinChain`**: at a state the reader visits, with a sound chain and the steps below the first
choice fixed, a pin at the first choice that the review leaves valid keeps some sound
chain. On the bin map the pin fixes one bit of a fixed prefix. -/
def PinChain (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → (∃ sel, ChainSound g sel) →
    ∀ k, firstChoice g = some k → PrefixUpTo g k →
      ∀ q ∈ ownersAt g.gowners k, isValid (filterAll g [q.id]) = true →
        ∃ sel, ChainSound (filterAll g [q.id]) sel

/-- Every state the reader visits keeps a chain. -/
theorem chain_of_pinChain (g₀ : GPathM) (h₀ : ∃ sel, ChainSound g₀ sel) (hP : PinChain g₀) :
    ∀ g, ReadFirst g₀ g → ∃ sel, ChainSound g sel := by
  intro g hF
  induction hF with
  | start => exact h₀
  | pin g k q hF hv hf hq hv' ih =>
    exact hP g hF hv ih k hf (prefixUpTo_firstChoice g k hf) q hq hv'

/-- A chain gives the reader its pick at the first choice: its own node there. -/
theorem progressFirst_of_chains (g₀ : GPathM) (hC : ∀ g, ReadFirst g₀ g → ∃ sel, ChainSound g sel) :
    ProgressFirst g₀ := by
  intro g hF _ k hk
  obtain ⟨sel, hsc⟩ := hC g hF
  have hmem := List.mem_of_find?_eq_some hk
  have h0 : 0 ≤ k := mem_intRange_lower hmem
  have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
  obtain ⟨_, hstep⟩ := hsc.chain.1.1 k h0 h1
  refine ⟨sel k, List.mem_filter.mpr ⟨hsc.chain.2.2 k h0 h1, beq_iff_eq.mpr hstep⟩, ?_⟩
  refine PickInduction.isValid_of_ChainG _ sel (ChainSound_filterAll g [(sel k).id] sel hsc ?_).chain
  intro req hreq _ _
  rw [List.mem_singleton.mp hreq, hstep]

/-- **The start**: a satisfying assignment leaves a sound chain in some state the reader starts from. -/
theorem start_chain (φ : Cnf) (hbd : Bounded φ) (h : Satisfiable φ) :
    ∃ kv ∈ pureRun φ, ∃ sel, ChainSound (filterAll kv.2 []) sel := by
  obtain ⟨a, hsat⟩ := h
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  obtain ⟨g, hmem, hal, _⟩ := pureRun_carries φ a hbd hsat hzero
  obtain ⟨sel, hsc, _⟩ := Conservation.chainSound_along φ a hbd hsat hzero g hal
  exact ⟨_, hmem, sel, ChainSound_filterAll g [] sel hsc (fun _ h => by cases h)⟩

/-- **The reader decides `φ`, with one open obligation**: `PinChain` at the states it starts from. -/
theorem readerVerdictW_iff_of_pinChain (φ : Cnf) (hbd : Bounded φ)
    (hpin : ∀ kv ∈ pureRun φ, PinChain (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ := by
  refine ⟨readerVerdictW_sound φ hbd, fun h => ?_⟩
  obtain ⟨kv, hkv, sel, hsc⟩ := start_chain φ hbd h
  have hC := chain_of_pinChain _ ⟨sel, hsc⟩ (hpin kv hkv)
  have hv := PickInduction.isValid_of_ChainG _ sel hsc.chain
  exact List.any_eq_true.mpr ⟨kv, hkv, readG_complete_first _ hv (progressFirst_of_chains _ hC)⟩

/-- info: 'AbsSatBin.GraphPath.Model.ReaderPrefix.firstChoice_pin_gt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms firstChoice_pin_gt

/-- info: 'AbsSatBin.GraphPath.Model.ReaderPrefix.readerVerdictW_iff_of_pinChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pinChain

end AbsSatBin.GraphPath.Model.ReaderPrefix
