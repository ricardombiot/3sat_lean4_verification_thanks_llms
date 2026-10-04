-- lean/improves_bin/AbsSatBin/GraphPath/Model/NoDeadEnd.lean
import AbsSatBin.GraphPath.Model.OtherBitSem
import AbsSatBin.GraphPath.Model.SymMachine
import AbsSatBin.SatMachine.PureProofs

/-!
# `NoDeadEnd`: one local statement for the reader and for the machine

**`NoDeadEnd`** (`ReaderPrefix.ProgressFirst` on the starting state): at every valid state the reader
visits, some node of the first step with a choice keeps the graph valid when pinned. On the bin map
the choice is between two bits, so it says: *the two pins never both die.* It is local: one state and
its two children, no solution, no chain.

* **Decoding is exact** (`selOfAssign_decode`). A chain of a full-length machine state that satisfies
  the requirements names, at every step, exactly the map node its decoded assignment names.
* **Pins are fixed in the state** (`PinNodes`). After a pin, every node of the pinned step carries the
  pinned map node, and the later pins keep it.
* **Descent** (`descend`). With `NoDeadEnd`, from a valid reader state the reader reaches a valid
  state with no choice left, keeping every pin.
* **`OtherBitSem ⇐ NoDeadEnd`** (`otherBitSem_of_noDeadEnd`). From the pinned state, descend; the final
  state denotes a path (`inhabited_of_noChoice_readable`); lifted to the machine's state, it decodes to
  a solution, and exact decoding makes it agree with every pin.
* **Machine soundness ⇐ `NoDeadEnd`** (`soundness_of_noDeadEnd`), with the zero-pin case
  `RootValid` (the review does not kill the final state). No `ClauseStepExact`, no `SkipExact`.
-/

namespace AbsSatBin.GraphPath.Model.NoDeadEnd

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.CnfChain
open AbsSatBin.GraphPath.Model.OtherBitSem
open AbsSatBin.GraphPath.Model.Reader (RCtx)
open AbsSatBin.GraphPath.Model.PickInduction (hasChoice)

variable (φ : Cnf)

-- ============================================================
-- Decoding is exact
-- ============================================================

theorem bit_beq (b : Int) (hb : b = 0 ∨ b = 1) : bit (b == 1) = b := by
  rcases hb with rfl | rfl <;> rfl

theorem onMap_two (k : Int) (d : NodeId) (h0 : 0 < k) (hm : k ≠ midFusion φ) (ht : k < fusionTop φ)
    (h : d ∈ mapNodes φ k) : ∃ b : Int, (b = 0 ∨ b = 1) ∧ d = ⟨k, b⟩ := by
  rw [mapNodes_two φ k h0 hm ht] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · exact ⟨0, Or.inl rfl, h⟩
  · exact ⟨1, Or.inr rfl, h⟩

/-- **The decoded assignment names the chain's own map node at every step.** -/
theorem selOfAssign_decode (g : GPathM) (sel : Int → PathNodeId) (hbd : Bounded φ)
    (hcs : g.current_step = stepCount φ) (hrs : MapChain.ReqSatisfying (reqOf φ) g sel)
    (hcm : ChainOnMap φ g sel) (k : Int) (h0 : 0 ≤ k) (hk : k < stepCount φ) :
    selOfAssign φ (decode sel) k = (sel k).id := by
  have hkc : k < g.current_step := by rw [hcs]; exact hk
  have hon := hcm k h0 hkc
  rcases step_cases φ k with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | h | ⟨j, p, c, hp, hjlt, hj, rfl⟩ | h
  · have hk0 : k = 0 := by omega
    subst hk0
    rw [mapNodes_fusion φ 0 (Or.inl rfl)] at hon
    rw [List.mem_singleton.mp hon]
    simp [selOfAssign]
  · obtain ⟨b, hb, hid⟩ := onMap_two φ _ _ (by simp only [varStep]; omega)
      (by simp only [varStep, midFusion]; omega) (by simp only [varStep, fusionTop]; omega) hon
    rw [selOfAssign_var φ _ v hv, hid]
    simp only [decode, hid]
    rw [bit_beq b hb]
  · obtain ⟨b, hb, hid⟩ := onMap_two φ _ _ (by simp only [negStep]; omega)
      (by simp only [negStep, midFusion]; omega) (by simp only [negStep, fusionTop]; omega) hon
    have hstep : (sel (negStep v)).id.step = negStep v := by rw [hid]
    have hreqs := reqOf_neg φ (sel (negStep v)).id v hv hstep
    have hidx : (sel (negStep v)).id.index = b := by rw [hid]
    rw [hidx] at hreqs
    have hvar := hrs (negStep v) h0 hkc { step := varStep v, index := 1 - b }
      (by rw [hreqs]; exact List.mem_cons_self) (by simp only [varStep]; omega)
      (by rw [hcs]; simp only [varStep, stepCount]; omega)
    rw [selOfAssign_neg φ _ v hv, hid]
    simp only [decode, hvar]
    rcases hb with rfl | rfl <;> rfl
  · rw [mapNodes_fusion φ k (Or.inr (Or.inl h))] at hon
    rw [List.mem_singleton.mp hon]
    subst h
    have e1 : ¬ midFusion φ ≤ 0 := by simp only [midFusion]; omega
    simp [selOfAssign, e1]
  · obtain ⟨b, hb, hid⟩ := onMap_two φ _ _ (by simp only [clauseStep]; omega)
      (by simp only [clauseStep, midFusion]; omega) (by simp only [clauseStep, fusionTop]; omega) hon
    have hstep : (sel (clauseStep φ j p)).id.step = clauseStep φ j p := by rw [hid]
    have hreqs := reqOf_clause φ (sel (clauseStep φ j p)).id j p c hp hjlt hj hstep
    have hidx : (sel (clauseStep φ j p)).id.index = b := by rw [hid]
    rw [hidx] at hreqs
    obtain ⟨h1, h2, h3⟩ := hbd c (List.mem_of_getElem? hj)
    have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
    have hlo : (0 : Int) ≤ (litAt c p).binStep := by have := (lit_step_bounds φ _ hv).1; omega
    have hhi : (litAt c p).binStep < g.current_step := by
      have := (lit_step_bounds φ _ hv).2
      rw [hcs]; simp only [midFusion, stepCount] at this ⊢; omega
    have hat := hrs _ h0 hkc { step := (litAt c p).binStep, index := b }
      (by rw [hreqs]; exact List.mem_cons_self) hlo hhi
    have hlit := litVal_of_node φ g sel hcs hrs (litAt c p) hv b hb hat
    rw [selOfAssign_clause φ _ j p c hp hjlt hj, hlit, bit_beq b hb, hid]
  · rw [mapNodes_fusion φ k (Or.inr (Or.inr ⟨h, hk⟩))] at hon
    rw [List.mem_singleton.mp hon]
    have h1 : ¬ k ≤ 0 := by simp only [fusionTop] at h; omega
    have h2 : ¬ k < midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
    have h3 : ¬ k = midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
    simp only [selOfAssign, h1, h2, h3, h, if_false, if_true]

-- ============================================================
-- Pins are fixed in the state
-- ============================================================

/-- **After a pin, every node of the pinned step carries the pinned map node.** A node of a valid
review fixpoint owns itself, and the cut is closed there, so it is a global owner; the pin left only
the pinned map node among the global owners of its step. -/
theorem pin_nodes (g : GPathM) (c : RCtx g) (q : NodeId) (hv : isValid (filterAll g [q]) = true)
    (n : PNodeM) (hn : n ∈ (filterAll g [q]).nodes) (hs : n.id.id.step = q.step) : n.id.id = q := by
  have cF := Reader.RCtx_filterAll g c [q]
  have hso := SelfOwn.SelfOwned_of_OOS (filterRequire g q) hv cF.oos cF.snn cF.below
  have hself : n.id ∈ n.owners := hso n.id n (node?_of_mem cF.nodup n hn)
  have hcc := SymMachine.cutClosed_review (filterRequire g q) hv
  have hcov := hasStepEntry_of_isValid _ hv n.id.id.step (cF.snn n hn) (cF.below n hn)
  have hgow : n.id ∈ (filterAll g [q]).gowners := hcc n hn n.id hself hcov
  have hgow' := (pruned_review (filterRequire g q)).gowners_sub _ hgow
  have hkeep := (List.mem_filter.mp hgow').2
  simp only [hs, bne_self_eq_false, Bool.false_or] at hkeep
  exact eq_of_beq hkeep

/-- The pins of a reader state are inside its steps and fixed in its nodes. -/
def PinNodes (ps : List NodeId) (g : GPathM) : Prop :=
  ∀ p ∈ ps, 0 ≤ p.step ∧ p.step < g.current_step ∧
    ∀ n ∈ g.nodes, n.id.id.step = p.step → n.id.id = p

theorem readFirst_of_readPins (g₀ : GPathM) (ps : List NodeId) (g : GPathM) (h : ReadPins g₀ ps g) :
    ReadFirst g₀ g := by
  induction h with
  | start => exact ReadFirst.start
  | pin g k q _ _ hv hf hq hv' ih => exact ReadFirst.pin g k q ih hv hf hq hv'

section
variable (g₀ : GPathM) (c₀ : RCtx g₀)
include c₀

theorem rctx_readPins (ps : List NodeId) (g : GPathM) (h : ReadPins g₀ ps g) : RCtx g := by
  induction h with
  | start => exact c₀
  | pin g _ q _ _ _ _ _ _ ih => exact Reader.RCtx_filterAll g ih [q.id]

omit c₀ in
theorem pruned_readPins (ps : List NodeId) (g : GPathM) (h : ReadPins g₀ ps g) : Pruned g₀ g := by
  induction h with
  | start => exact Pruned.refl _
  | pin g _ q _ _ _ _ _ _ ih => exact Pruned.trans ih (pruned_filterAll g [q.id])

theorem pinNodes_readPins (ps : List NodeId) (g : GPathM) (h : ReadPins g₀ ps g) : PinNodes ps g := by
  induction h with
  | start => intro p hp; cases hp
  | pin g k q ps hp _ hf hq hv' ih =>
    have hpr := pruned_filterAll g [q.id]
    have cg := rctx_readPins g₀ c₀ ps g hp
    intro p hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · have hmemk := List.mem_of_find?_eq_some hf
      have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
      refine ⟨by rw [hqs]; exact mem_intRange_lower hmemk, ?_, ?_⟩
      · rw [hpr.step_eq, hqs]; have := mem_intRange_upper hmemk; omega
      · exact fun n hn hs => pin_nodes g cg q.id hv' n hn hs
    · obtain ⟨h0, h1, hn⟩ := ih p hmem
      refine ⟨h0, by rw [hpr.step_eq]; exact h1, fun n hn' hs => ?_⟩
      obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived n hn'
      rw [hid] at hs ⊢
      exact hn m hm hs
end

theorem readable_readPins (m : GPathM) (cm : RCtx m) (ps : List NodeId) (g : GPathM)
    (h : ReadPins (filterAll m []) ps g) : Reader.Readable g := by
  induction h with
  | start => exact ⟨m, [], cm, rfl⟩
  | pin g _ q _ _ _ _ _ _ ih => exact Reader.Readable_filterAll g ih [q.id]

-- ============================================================
-- Descent
-- ============================================================

/-- **`NoDeadEnd`** from `g₀`: at every valid state the reader visits, some node of the first step
with a choice keeps the graph valid when pinned. -/
def NoDeadEnd (g₀ : GPathM) : Prop := ProgressFirst g₀

/-- **With `NoDeadEnd`, the reader goes down to a valid state with no choice, keeping its pins.** -/
theorem descend (g₀ : GPathM) (hnd : NoDeadEnd g₀) :
    ∀ (n : Nat) (ps : List NodeId) (g : GPathM), measure g ≤ n → ReadPins g₀ ps g →
      isValid g = true →
      ∃ ps' g', ReadPins g₀ ps' g' ∧ isValid g' = true ∧ hasChoice g' = false ∧ ∀ p ∈ ps, p ∈ ps' := by
  intro n
  induction n with
  | zero =>
    intro ps g hm hp hv
    cases hf : firstChoice g with
    | none => exact ⟨ps, g, hp, hv, noChoice_of_firstChoice_none g hf, fun _ h => h⟩
    | some k =>
      obtain ⟨q, hq, _⟩ := hnd g (readFirst_of_readPins g₀ ps g hp) hv k hf
      have := PickInduction.measure_lt_of_choiceAt g k (choiceAt_of_firstChoice g k hf) q hq
      exact absurd (Nat.lt_of_lt_of_le this hm) (Nat.not_lt_zero _)
  | succ n ih =>
    intro ps g hm hp hv
    cases hf : firstChoice g with
    | none => exact ⟨ps, g, hp, hv, noChoice_of_firstChoice_none g hf, fun _ h => h⟩
    | some k =>
      obtain ⟨q, hq, hvq⟩ := hnd g (readFirst_of_readPins g₀ ps g hp) hv k hf
      have hlt := PickInduction.measure_lt_of_choiceAt g k (choiceAt_of_firstChoice g k hf) q hq
      obtain ⟨ps', g', hp', hv', hnc, hsub⟩ :=
        ih (q.id :: ps) _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hm))
          (ReadPins.pin g k q ps hp hv hf hq hvq) hvq
      exact ⟨ps', g', hp', hv', hnc, fun p h => hsub p (List.mem_cons_of_mem _ h)⟩

-- ============================================================
-- `OtherBitSem ⇐ NoDeadEnd`
-- ============================================================

/-- **A valid reader state from which `NoDeadEnd` holds has a solution agreeing with its pins.** -/
theorem agrees_of_noDeadEnd (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (hnd : NoDeadEnd (filterAll kv.2 [])) (ps : List NodeId) (g : GPathM)
    (hp : ReadPins (filterAll kv.2 []) ps g) (hv : isValid g = true) :
    ∃ a, Sat a φ ∧ AgreesAll φ a ps := by
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hok := Decision.stateOk_pureRun φ hzero kv hkv
  have hreach := reachable_of_mapReachable φ hbd kv.2 hok.reach
  have hnd₀ := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have cm := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) kv.2 hnd₀ hreach
  have c₀ := Reader.RCtx_filterAll kv.2 cm []
  obtain ⟨ps', g', hp', hv', hnc, hsub⟩ := descend _ hnd _ ps g (Nat.le_refl _) hp hv
  -- the final state denotes a path
  have hR : Reader.Readable g' := readable_readPins kv.2 cm ps' g' hp'
  obtain ⟨_, sel, hchain', howned', _⟩ := Reader.inhabited_of_noChoice_readable g' hR hv' hnc
  -- lifted to the machine's state
  have hpr : Pruned kv.2 g' :=
    Pruned.trans (pruned_filterAll kv.2 []) (pruned_readPins _ ps' g' hp')
  have hchain := IsChain_of_pruned hpr hnd₀ sel hchain'
  have howned := PairwiseOwned_of_pruned hpr hnd₀ sel howned'
  have hcs : kv.2.current_step = stepCount φ := by rw [hok.step]; omega
  have hrs : MapChain.ReqSatisfying (reqOf φ) kv.2 sel := by
    intro k hk0 hk req hreq hr0 hr1
    exact L1_cor (reqOf φ) (isProhibited φ) hreach hchain howned k hk0 hk req hreq hr0 hr1
  have hcm : ChainOnMap φ kv.2 sel :=
    chainOnMap_of_nodesOnMap φ kv.2 (nodesOnMap_of_mapReachable φ kv.2 hok.reach) sel hchain
  refine ⟨decode sel, sat_of_reqSatisfying φ kv.2 sel hbd hcs hchain hrs hcm
    (noForb_of_mapReachable φ kv.2 hok.reach)
    (ParentId.PMP_reachable (reqOf φ) (isProhibited φ) kv.2 hreach)
    (ParentId.GPMP_reachable (reqOf φ) (isProhibited φ) kv.2 hreach), ?_⟩
  -- and agrees with every pin
  intro p hmem
  obtain ⟨h0, h1, hfix⟩ := pinNodes_readPins _ c₀ ps' g' hp' p (hsub p hmem)
  obtain ⟨hsome, hstep⟩ := hchain'.1 p.step h0 h1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hnm := List.mem_of_find?_eq_some hn
  have hnid : n.id = sel p.step := node?_id_eq g' _ n hn
  have hfixed := hfix n hnm (by rw [hnid, hstep])
  rw [hnid] at hfixed
  rw [selOfAssign_decode φ kv.2 sel hbd hcs hrs hcm p.step h0
    (by rw [← hcs, ← (hpr.step_eq)]; exact h1), hfixed]

/-- **`OtherBitSem ⇐ NoDeadEnd`.** -/
theorem otherBitSem_of_noDeadEnd (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (hnd : NoDeadEnd (filterAll kv.2 [])) : OtherBitSem φ (filterAll kv.2 []) := by
  intro ps g hp hv _ _ _ k hf q hq _ hvq
  exact agrees_of_noDeadEnd φ hbd kv hkv hnd (q.id :: ps) _ (ReadPins.pin g k q ps hp hv hf hq hvq) hvq

-- ============================================================
-- Machine soundness ⇐ NoDeadEnd
-- ============================================================

/-- The zero-pin case: the review does not kill a state of the final line. -/
def RootValid : Prop := ∀ kv ∈ pureRun φ, isValid (filterAll kv.2 []) = true

/-- **The machine is sound under `NoDeadEnd`**, with no `ClauseStepExact` and no `SkipExact`. -/
theorem soundness_of_noDeadEnd (hbd : Bounded φ) (hroot : RootValid φ)
    (hnd : ∀ kv ∈ pureRun φ, NoDeadEnd (filterAll kv.2 []))
    (h : AbsSatBin.SatMachine.PureSatMachine.is_satisfiable
      (AbsSatBin.SatMachine.PureSatMachine.run_pure φ) = true) : Satisfiable φ := by
  obtain ⟨kv, hkv⟩ := List.exists_mem_of_ne_nil _ ((AbsSatBin.SatMachine.PureProofs.is_satisfiable_run_pure_iff φ).mp h)
  obtain ⟨a, ha, _⟩ := agrees_of_noDeadEnd φ hbd kv hkv (hnd kv hkv) [] _ ReadPins.start
    (hroot kv hkv)
  exact ⟨a, ha⟩

/-- **The reader decides `φ` under `NoDeadEnd`.** -/
theorem readerVerdictW_iff_of_noDeadEnd (hbd : Bounded φ)
    (hnd : ∀ kv ∈ pureRun φ, NoDeadEnd (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_otherBitSem φ hbd
    (fun kv hkv => otherBitSem_of_noDeadEnd φ hbd kv hkv (hnd kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.NoDeadEnd.soundness_of_noDeadEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundness_of_noDeadEnd

/-- info: 'AbsSatBin.GraphPath.Model.NoDeadEnd.readerVerdictW_iff_of_noDeadEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_noDeadEnd

end AbsSatBin.GraphPath.Model.NoDeadEnd
