-- lean/improves_bin/AbsSatBin/GraphPath/Model/PinChainBin.lean
import AbsSatBin.GraphPath.Model.ReaderPrefix

/-!
# `PinChain` on the bin map: only the other bit is left

`ReaderPrefix.readerVerdictW_iff_of_pinChain` leaves one obligation: a valid pin at the first choice
keeps a sound chain. This module splits it with the shape of the bin map.

* **Two bits** (`entry_bit`). Every state the reader visits keeps its nodes on the map (`BinCtx`), and
  a step of the bin map has the nodes `⟨k,0⟩` and `⟨k,1⟩` at most. So a choice is between two bits.
* **The chain's own bit is free** (`chainSound_pin_same`). Pinning the bit of a chain the state
  already has keeps that chain.
* **What is left is the other bit** (`OtherBit`). At a reader state with a chain `sel` and a fixed
  prefix, if the pin at the flipped bit `⟨k, 1 - (sel k).id.index⟩` is valid, some chain of the
  state goes through that bit.
* **And it is also necessary** (`chainG_through_pin`). A chain of the pinned state is a chain of the
  state before the pin, through the pinned bit. So `PinChain` asks for exactly this: *the aggressive
  review leaves a pin valid only if a solution extends the fixed prefix with that bit.*

`readerVerdictW_iff_of_otherBit`: with `Bounded φ` and `OtherBit` on the starting states, the reader
decides `φ`.
-/

namespace AbsSatBin.GraphPath.Model.PinChainBin

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.PureDriver

variable (φ : Cnf)

-- ============================================================
-- The reader's states stay on the map
-- ============================================================

/-- What the reader's states keep: the reader's context, and every node on the bin map. -/
structure BinCtx (g : GPathM) : Prop where
  rctx  : Reader.RCtx g
  onMap : NodesOnMap φ g

theorem binCtx_filterAll (g : GPathM) (h : BinCtx φ g) (reqs : List NodeId) :
    BinCtx φ (filterAll g reqs) where
  rctx  := Reader.RCtx_filterAll g h.rctx reqs
  onMap := NodesOnMap_of_pruned φ (pruned_filterAll g reqs) h.onMap

theorem binCtx_start (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ) :
    BinCtx φ (filterAll kv.2 []) := by
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hok := Decision.stateOk_pureRun φ hzero kv hkv
  have hreach := reachable_of_mapReachable φ hbd kv.2 hok.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  exact binCtx_filterAll φ kv.2
    ⟨Reader.RCtx_reachable (reqOf φ) (isProhibited φ) kv.2 hnd hreach,
     nodesOnMap_of_mapReachable φ kv.2 hok.reach⟩ []

theorem binCtx_readFirst (g₀ : GPathM) (h₀ : BinCtx φ g₀) (g : GPathM) (hF : ReadFirst g₀ g) :
    BinCtx φ g := by
  induction hF with
  | start => exact h₀
  | pin g _ q _ _ _ _ _ ih => exact binCtx_filterAll φ g ih [q.id]

-- ============================================================
-- Two bits per step
-- ============================================================

/-- **A live entry of step `k` is one of the two bits of `k`.** -/
theorem entry_bit (g : GPathM) (h : BinCtx φ g) (k : Int) (q : PathNodeId)
    (hq : q ∈ ownersAt g.gowners k) : q.id = ⟨k, 0⟩ ∨ q.id = ⟨k, 1⟩ := by
  obtain ⟨hmem, hs⟩ := List.mem_filter.mp hq
  have hstep : q.id.step = k := eq_of_beq hs
  obtain ⟨n, hn, hid⟩ := h.rctx.gn q hmem
  have hon := h.onMap n hn
  rw [hid] at hon
  have e : q.id = ⟨q.id.step, q.id.index⟩ := rfl
  rcases mapNodes_index φ _ _ hon with hi | hi
  · left; rw [e, hstep, hi]
  · right; rw [e, hstep, hi]

/-- **Two different live entries of a step are the two bits**: one is the other flipped. -/
theorem entry_flip (g : GPathM) (h : BinCtx φ g) (k : Int) (q r : PathNodeId)
    (hq : q ∈ ownersAt g.gowners k) (hr : r ∈ ownersAt g.gowners k) (hne : q.id ≠ r.id) :
    q.id = ⟨k, 1 - r.id.index⟩ := by
  rcases entry_bit φ g h k q hq with h1 | h1 <;> rcases entry_bit φ g h k r hr with h2 | h2 <;>
    rw [h1, h2] at hne ⊢ <;> first | exact absurd rfl hne | rfl

-- ============================================================
-- The chain's own bit, and the necessity
-- ============================================================

/-- **Pinning the chain's own bit keeps the chain.** -/
theorem chainSound_pin_same (g : GPathM) (sel : Int → PathNodeId) (hsc : ChainSound g sel)
    (q : PathNodeId) (hq : (sel q.id.step).id = q.id) :
    ChainSound (filterAll g [q.id]) sel :=
  ChainSound_filterAll g [q.id] sel hsc (by
    intro req hreq _ _
    rw [List.mem_singleton.mp hreq]
    exact hq)

/-- **A chain of the pinned state is a chain of the state, through the pinned bit.** So a valid pin
with no chain through its bit can never be repaired by the review: `PinChain` holds exactly when the
review leaves no such pin valid. -/
theorem chainG_through_pin (g : GPathM) (hc : Reader.RCtx g) (k : Int) (q : PathNodeId)
    (hq : q ∈ ownersAt g.gowners k) (hk0 : 0 ≤ k) (hk : k < g.current_step)
    (sel : Int → PathNodeId) (hsc : ChainSound (filterAll g [q.id]) sel) :
    ChainG g sel ∧ (sel k).id = q.id := by
  have hpr := pruned_filterAll g [q.id]
  have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
  refine ⟨⟨IsChain_of_pruned hpr hc.nodup sel hsc.chain.1,
    PairwiseOwned_of_pruned hpr hc.nodup sel hsc.chain.2.1,
    fun i hi0 hi1 => hpr.gowners_sub _ (hsc.chain.2.2 i hi0 (by rw [hpr.step_eq]; exact hi1))⟩, ?_⟩
  have hk' : k < (filterAll g [q.id]).current_step := by rw [hpr.step_eq]; exact hk
  have hmem : sel k ∈ ownersAt (filterAll g [q.id]).gowners q.id.step := by
    rw [hqs]
    exact List.mem_filter.mpr ⟨hsc.chain.2.2 k hk0 hk', beq_iff_eq.mpr (hsc.chain.1.1 k hk0 hk').2⟩
  exact ownersAt_pin g q (sel k) hmem

-- ============================================================
-- The piece left: the other bit
-- ============================================================

/-- **`OtherBit`**: at a reader state with a chain `sel` and a fixed prefix below the first choice
`k`, if the pin at the flipped bit is valid, some chain of the state goes through that bit. -/
def OtherBit (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → ∀ sel, ChainSound g sel →
    ∀ k, firstChoice g = some k → PrefixUpTo g k →
      ∀ q ∈ ownersAt g.gowners k, q.id = ⟨k, 1 - (sel k).id.index⟩ →
        isValid (filterAll g [q.id]) = true →
        ∃ sel', ChainSound g sel' ∧ (sel' k).id = q.id

theorem pinChain_of_otherBit (g₀ : GPathM) (h₀ : BinCtx φ g₀) (hob : OtherBit g₀) :
    PinChain g₀ := by
  intro g hF hv ⟨sel, hsc⟩ k hf hpre q hq hvq
  have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
  have hmem := List.mem_of_find?_eq_some hf
  have h0 : 0 ≤ k := mem_intRange_lower hmem
  have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
  by_cases hsame : (sel k).id = q.id
  · exact ⟨sel, chainSound_pin_same g sel hsc q (by rw [hqs]; exact hsame)⟩
  · have hsk : sel k ∈ ownersAt g.gowners k :=
      List.mem_filter.mpr ⟨hsc.chain.2.2 k h0 h1, beq_iff_eq.mpr (hsc.chain.1.1 k h0 h1).2⟩
    have hflip := entry_flip φ g (binCtx_readFirst φ g₀ h₀ g hF) k q (sel k) hq hsk
      (fun e => hsame e.symm)
    obtain ⟨sel', hsc', hk'⟩ := hob g hF hv sel hsc k hf hpre q hq hflip hvq
    exact ⟨sel', chainSound_pin_same g sel' hsc' q (by rw [hqs]; exact hk')⟩

/-- **The reader decides `φ`, with the other bit as the one open obligation.** -/
theorem readerVerdictW_iff_of_otherBit (hbd : Bounded φ)
    (hob : ∀ kv ∈ pureRun φ, OtherBit (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_pinChain φ hbd
    (fun kv hkv => pinChain_of_otherBit φ _ (binCtx_start φ hbd kv hkv) (hob kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.PinChainBin.chainG_through_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainG_through_pin

/-- info: 'AbsSatBin.GraphPath.Model.PinChainBin.readerVerdictW_iff_of_otherBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_otherBit

end AbsSatBin.GraphPath.Model.PinChainBin
