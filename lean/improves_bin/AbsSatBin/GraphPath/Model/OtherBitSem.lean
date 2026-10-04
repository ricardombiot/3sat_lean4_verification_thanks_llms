-- lean/improves_bin/AbsSatBin/GraphPath/Model/OtherBitSem.lean
import AbsSatBin.GraphPath.Model.PinChainBin

/-!
# `OtherBit` stated on the formula

The reader pins map nodes in step order, and on the bin map a map node of step `k` is one value of the
literal (or variable) that step reads. So the list of pins is a **partial assignment**, and an
assignment `a` agrees with it when it names the same map node at every pinned step
(`AgreesAll φ a ps`: `selOfAssign φ a p.step = p`).

* **The one line** (`carried_unique`). Every state of `pureRun φ` sits at the top fusion, whose single
  map node is what every assignment names there; the keys of the line are distinct. So the line has
  one state, and it carries **every** solution (`AlongAssign`).
* **A solution that agrees with the pins keeps its chain** (`chain_of_agrees`). Conservation puts the
  solution's chain in the machine's state, and each pin agrees with it, so the review keeps it.
* **`OtherBitSem`**: at a state the reader visits with a solution `a` that agrees with the pins, if
  pinning a *different* value at the first choice leaves the machine valid, then some solution agrees
  with the pins and that value. It speaks only of `φ`, the pins and the machine's validity.
* `readerVerdictW_iff_of_otherBitSem`: with `Bounded φ` and `OtherBitSem`, the reader decides `φ`.
  The proof carries *a solution* along the reader, not a chain: no decoding is needed.
-/

namespace AbsSatBin.GraphPath.Model.OtherBitSem

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.Conservation (AlongAssign)

variable (φ : Cnf)

-- ============================================================
-- The reader's pins
-- ============================================================

/-- `ReadFirst`, remembering the map nodes pinned so far (most recent first). -/
inductive ReadPins (g₀ : GPathM) : List NodeId → GPathM → Prop where
  | start : ReadPins g₀ [] g₀
  | pin (g : GPathM) (k : Int) (q : PathNodeId) (ps : List NodeId) : ReadPins g₀ ps g →
      isValid g = true → firstChoice g = some k → q ∈ ownersAt g.gowners k →
      isValid (filterAll g [q.id]) = true → ReadPins g₀ (q.id :: ps) (filterAll g [q.id])

theorem readPins_of_readFirst (g₀ g : GPathM) (h : ReadFirst g₀ g) : ∃ ps, ReadPins g₀ ps g := by
  induction h with
  | start => exact ⟨[], ReadPins.start⟩
  | pin g k q _ hv hf hq hv' ih =>
    obtain ⟨ps, hp⟩ := ih
    exact ⟨q.id :: ps, ReadPins.pin g k q ps hp hv hf hq hv'⟩

/-- An assignment agrees with the pins: it names the pinned map node at every pinned step. -/
def AgreesAll (a : Assign) (ps : List NodeId) : Prop := ∀ p ∈ ps, selOfAssign φ a p.step = p

-- ============================================================
-- The line carries every solution
-- ============================================================

theorem lineOk_pureRun (hzero : (0 : Int) < stepCount φ) : LineOk φ (stepCount φ - 1) (pureRun φ) := by
  have h := Decision.LineOk_pureSteps φ (stepCount φ - 1).toNat 0 (pureInit φ) (Decision.LineOk_pureInit φ)
  have hcast : (0 : Int) + (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  rw [hcast] at h
  exact h

theorem top_key (hzero : (0 : Int) < stepCount φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ) :
    kv.1 = ⟨stepCount φ - 1, 0⟩ := by
  have hon := (Decision.stateOk_pureRun φ hzero kv hkv).onMap
  rw [mapNodes_fusion φ _ (Or.inr (Or.inr ⟨by simp only [fusionTop, stepCount]; omega, by omega⟩))]
    at hon
  exact List.mem_singleton.mp hon

theorem selOfAssign_top (a : Assign) : selOfAssign φ a (stepCount φ - 1) = ⟨stepCount φ - 1, 0⟩ := by
  unfold selOfAssign
  have h1 : ¬ (stepCount φ - 1 ≤ 0) := by simp only [stepCount]; omega
  have h2 : ¬ (stepCount φ - 1 < midFusion φ) := by simp only [stepCount, midFusion]; omega
  have h3 : ¬ (stepCount φ - 1 = midFusion φ) := by simp only [stepCount, midFusion]; omega
  have h4 : fusionTop φ ≤ stepCount φ - 1 := by simp only [stepCount, fusionTop]; omega
  simp only [h1, h2, h3, h4, if_false, if_true]

/-- **The final line carries every solution** in each of its states. -/
theorem carried_unique (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (a : Assign) (hsat : Sat a φ) : AlongAssign φ a kv.2 := by
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  obtain ⟨g, hmem, hal, _⟩ := pureRun_carries φ a hbd hsat hzero
  have hnd := (lineOk_pureRun φ hzero).1
  have heq := key_inj _ hnd kv hkv _ hmem (by rw [top_key φ hzero kv hkv, selOfAssign_top])
  rw [heq]
  exact hal

-- ============================================================
-- A solution that agrees with the pins keeps its chain
-- ============================================================

theorem chain_of_agrees (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (a : Assign) (hsat : Sat a φ) :
    ∀ ps g, ReadPins (filterAll kv.2 []) ps g → AgreesAll φ a ps →
      ∃ sel, ChainSound g sel ∧ ∀ i, 0 ≤ i → i < g.current_step → (sel i).id = selOfAssign φ a i := by
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  intro ps g h
  induction h with
  | start =>
    intro _
    obtain ⟨sel, hsc, hids⟩ :=
      Conservation.chainSound_along φ a hbd hsat hzero kv.2 (carried_unique φ hbd kv hkv a hsat)
    refine ⟨sel, ChainSound_filterAll kv.2 [] sel hsc (fun _ h => by cases h), fun i h0 h1 => ?_⟩
    exact hids i h0 (by rw [← (pruned_filterAll kv.2 []).step_eq]; exact h1)
  | pin g k q ps _ _ _ _ _ ih =>
    intro hag
    obtain ⟨sel, hsc, hids⟩ := ih (fun p hp => hag p (List.mem_cons_of_mem _ hp))
    have hq : selOfAssign φ a q.id.step = q.id := hag q.id List.mem_cons_self
    refine ⟨sel, ChainSound_filterAll g [q.id] sel hsc ?_, fun i h0 h1 => ?_⟩
    · intro req hreq h0 h1
      rw [List.mem_singleton.mp hreq] at h0 h1 ⊢
      rw [hids _ h0 h1, hq]
    · exact hids i h0 (by rw [← (pruned_filterAll g [q.id]).step_eq]; exact h1)

-- ============================================================
-- The obligation, on the formula
-- ============================================================

/-- **`OtherBitSem`**: at a state the reader visits, with a solution `a` that agrees with the pins so
far, if pinning a map node of the first choice other than `a`'s leaves the machine valid, then some
solution agrees with the pins and that node. -/
def OtherBitSem (g₀ : GPathM) : Prop :=
  ∀ ps g, ReadPins g₀ ps g → isValid g = true →
    ∀ a, Sat a φ → AgreesAll φ a ps →
      ∀ k, firstChoice g = some k → ∀ q ∈ ownersAt g.gowners k, q.id ≠ selOfAssign φ a k →
        isValid (filterAll g [q.id]) = true →
        ∃ a', Sat a' φ ∧ AgreesAll φ a' (q.id :: ps)

/-- Along the reader, some solution always agrees with the pins. -/
theorem agrees_readPins (g₀ : GPathM) (hob : OtherBitSem φ g₀) (a₀ : Assign) (hsat : Sat a₀ φ) :
    ∀ ps g, ReadPins g₀ ps g → ∃ a, Sat a φ ∧ AgreesAll φ a ps := by
  intro ps g h
  induction h with
  | start => exact ⟨a₀, hsat, fun _ h => by cases h⟩
  | pin g k q ps hp hv hf hq hv' ih =>
    obtain ⟨a, ha, hag⟩ := ih
    have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
    by_cases hsame : q.id = selOfAssign φ a k
    · refine ⟨a, ha, fun p hp' => ?_⟩
      rcases List.mem_cons.mp hp' with rfl | hp'
      · rw [hqs]; exact hsame.symm
      · exact hag p hp'
    · exact hob ps g hp hv a ha hag k hf q hq hsame hv'

/-- **The reader decides `φ`, with `OtherBitSem` as the one open obligation.** -/
theorem readerVerdictW_iff_of_otherBitSem (hbd : Bounded φ)
    (hob : ∀ kv ∈ pureRun φ, OtherBitSem φ (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ := by
  refine ⟨readerVerdictW_sound φ hbd, fun ⟨a₀, hsat⟩ => ?_⟩
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  obtain ⟨g, hkv, _, _⟩ := pureRun_carries φ a₀ hbd hsat hzero
  have hC : ∀ h, ReadFirst (filterAll g []) h → ∃ sel, ChainSound h sel := by
    intro h hF
    obtain ⟨ps, hp⟩ := readPins_of_readFirst _ h hF
    obtain ⟨a, ha, hag⟩ := agrees_readPins φ _ (hob _ hkv) a₀ hsat ps h hp
    obtain ⟨sel, hsc, _⟩ := chain_of_agrees φ hbd _ hkv a ha ps h hp hag
    exact ⟨sel, hsc⟩
  obtain ⟨sel, hsc⟩ := hC _ ReadFirst.start
  have hv := PickInduction.isValid_of_ChainG _ sel hsc.chain
  exact List.any_eq_true.mpr ⟨_, hkv, readG_complete_first _ hv (progressFirst_of_chains _ hC)⟩

/-- info: 'AbsSatBin.GraphPath.Model.OtherBitSem.readerVerdictW_iff_of_otherBitSem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_otherBitSem

end AbsSatBin.GraphPath.Model.OtherBitSem
