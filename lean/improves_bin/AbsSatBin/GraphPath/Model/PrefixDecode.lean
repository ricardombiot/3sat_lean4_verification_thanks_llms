-- lean/improves_bin/AbsSatBin/GraphPath/Model/PrefixDecode.lean
import AbsSatBin.GraphPath.Model.PrefixCarry

/-!
# Step 1: a chain of a machine state is a partial solution

`NoDeadEnd.selOfAssign_decode` reads a full chain of the final state as an assignment. The same reading
works for a chain of **any** state, up to its current step:

* `selOfAssign_decode_pre`: the decoded assignment names the chain's map node at every step below the
  state's current step;
* `pidOfAssign_decode_pre`: and the chain's path node itself (its window), by parent coherence;
* `preSat_decode`: the decoded assignment's windows below the current step are allowed — they are the
  chain's nodes, and no node of the machine is prohibited.

With `PrefixCarry.cert_of_prefix`, a chain of a state is carried by the machine into the state of
whatever map node its own values lead to (`decode_prefix`).
-/

namespace AbsSatBin.GraphPath.Model.PrefixDecode

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.CnfChain
open AbsSatBin.GraphPath.Model.NoDeadEnd
open AbsSatBin.GraphPath.Model.PrefixCarry

variable (φ : Cnf)

theorem litVal_of_node_pre (g : GPathM) (sel : Int → PathNodeId)
    (hrs : MapChain.ReqSatisfying (reqOf φ) g sel)
    (l : Lit) (hl : l.v < φ.nVars) (b : Int) (hb : b = 0 ∨ b = 1)
    (hat : (sel l.binStep).id = ⟨l.binStep, b⟩) (hlt : l.binStep < g.current_step) :
    litVal (decode sel) l = (b == 1) := by
  cases hp : l.pos with
  | true =>
    have hstep : l.binStep = varStep l.v := varStep_eq l hp
    have : (sel (varStep l.v)).id.index = b := by rw [← hstep, hat]
    simp only [litVal, hp, decode, this]
    rfl
  | false =>
    have hstep : l.binStep = negStep l.v := negStep_eq l hp
    -- the chain stands on "!v=b"; the negation node's own requirement moves it to "v=1-b"
    have hk0 : (0 : Int) ≤ negStep l.v := by simp only [negStep]; omega
    have hk1 : negStep l.v < g.current_step := by rw [← hstep]; exact hlt
    have hnegstep : (sel (negStep l.v)).id.step = negStep l.v := by rw [← hstep, hat]
    have hreqs := reqOf_neg φ (sel (negStep l.v)).id l.v hl hnegstep
    have hidx : (sel (negStep l.v)).id.index = b := by rw [← hstep, hat]
    rw [hidx] at hreqs
    have hsecond := hrs (negStep l.v) hk0 hk1 { step := varStep l.v, index := 1 - b }
      (by rw [hreqs]; exact List.mem_cons_self)
      (by simp only [varStep]; omega)
      (by simp only [varStep, negStep] at hk1 ⊢; omega)
    have hv : (sel (varStep l.v)).id.index = 1 - b := by rw [hsecond]
    simp only [litVal, hp, decode, hv]
    rcases hb with rfl | rfl <;> rfl

theorem selOfAssign_decode_pre (g : GPathM) (sel : Int → PathNodeId) (hbd : Bounded φ)
    (hcsle : g.current_step ≤ stepCount φ) (hrs : MapChain.ReqSatisfying (reqOf φ) g sel)
    (hcm : ChainOnMap φ g sel) (k : Int) (h0 : 0 ≤ k) (hkc : k < g.current_step) :
    selOfAssign φ (decode sel) k = (sel k).id := by
  have hk : k < stepCount φ := by omega
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
      (by simp only [varStep, negStep] at hkc ⊢; omega)
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
      simp only [midFusion, clauseStep] at this hkc ⊢; omega
    have hat := hrs _ h0 hkc { step := (litAt c p).binStep, index := b }
      (by rw [hreqs]; exact List.mem_cons_self) hlo hhi
    have hlit := litVal_of_node_pre φ g sel hrs (litAt c p) hv b hb hat hhi
    rw [selOfAssign_clause φ _ j p c hp hjlt hj, hlit, bit_beq b hb, hid]
  · rw [mapNodes_fusion φ k (Or.inr (Or.inr ⟨h, hk⟩))] at hon
    rw [List.mem_singleton.mp hon]
    have h1 : ¬ k ≤ 0 := by simp only [fusionTop] at h; omega
    have h2 : ¬ k < midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
    have h3 : ¬ k = midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
    simp only [selOfAssign, h1, h2, h3, h, if_false, if_true]

/-- **The decoded assignment's window is the chain's node.** -/
theorem pidOfAssign_decode_pre (g : GPathM) (sel : Int → PathNodeId) (hbd : Bounded φ)
    (hcsle : g.current_step ≤ stepCount φ) (hchain : IsChain g sel)
    (hrs : MapChain.ReqSatisfying (reqOf φ) g sel) (hcm : ChainOnMap φ g sel)
    (hpmp : ParentId.PMP g) (hgpmp : ParentId.GPMP g) (hroot : (sel 0).parent_id = none)
    (k : Int) (h0 : 0 ≤ k) (hkc : k < g.current_step) : pidOfAssign φ (decode sel) k = sel k := by
  have sd : ∀ i, 0 ≤ i → i < g.current_step → selOfAssign φ (decode sel) i = (sel i).id :=
    fun i hi0 hi1 => selOfAssign_decode_pre φ g sel hbd hcsle hrs hcm i hi0 hi1
  -- the gparent at step 0
  have hg0 : (sel 0).gparent_id = none := by
    obtain ⟨hs, _⟩ := hchain.1 0 (Int.le_refl 0) (by omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    have hid : n.id = sel 0 := node?_id_eq g _ n hn
    have := hgpmp.2 n (List.mem_of_find?_eq_some hn) (by rw [hid]; exact hroot)
    rw [hid] at this; exact this
  unfold pidOfAssign
  apply ParentId.pathNodeId_ext
  · exact sd k h0 hkc
  · by_cases hk : 0 < k
    · rw [if_pos hk, sd (k - 1) (by omega) (by omega)]
      have := ParentId.parentId_coherent g hpmp sel hchain (k - 1) (by omega) (by omega)
      rw [show k - 1 + 1 = k from by omega] at this
      exact this.symm
    · have hk0 : k = 0 := by omega
      rw [if_neg hk, hk0]; exact hroot.symm
  · by_cases hk : 1 < k
    · rw [if_pos hk, sd (k - 2) (by omega) (by omega)]
      have h1 := ParentId.gparentId_coherent g hgpmp sel hchain (k - 1) (by omega) (by omega)
      have h2 := ParentId.parentId_coherent g hpmp sel hchain (k - 2) (by omega) (by omega)
      rw [show k - 1 + 1 = k from by omega] at h1
      rw [show k - 2 + 1 = k - 1 from by omega] at h2
      rw [h1, h2]
    · rw [if_neg hk]
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact hg0.symm
      · have h1 := ParentId.gparentId_coherent g hgpmp sel hchain 0 (Int.le_refl 0) (by omega)
        rw [show (0 : Int) + 1 = 1 from rfl] at h1
        rw [h1, hroot]

/-- **The decoded assignment's windows below the current step are allowed.** -/
theorem preSat_decode (g : GPathM) (sel : Int → PathNodeId) (hbd : Bounded φ)
    (hcsle : g.current_step ≤ stepCount φ) (hchain : IsChain g sel)
    (hrs : MapChain.ReqSatisfying (reqOf φ) g sel) (hcm : ChainOnMap φ g sel)
    (hnf : NoForb (isProhibited φ) g)
    (hpmp : ParentId.PMP g) (hgpmp : ParentId.GPMP g) (hroot : (sel 0).parent_id = none) :
    PreSat φ (decode sel) g.current_step := by
  intro k hk
  by_cases h0 : 0 ≤ k
  · rw [pidOfAssign_decode_pre φ g sel hbd hcsle hchain hrs hcm hpmp hgpmp hroot k h0 hk]
    exact chain_not_forb _ g hnf sel hchain k h0 hk
  · -- below the root no window is a clause's third literal
    have hs : (pidOfAssign φ (decode sel) k).id.step = k := selOfAssign_step φ _ k
    unfold isProhibited isL3
    rw [hs]
    have : ¬ midFusion φ < k := by simp only [midFusion]; omega
    simp [this]

/-- **Step 1.** A certificate of a machine state reads as a partial solution: its windows below the
current step are allowed, and it passes exactly the chain's path nodes. -/
theorem decode_prefix (g : GPathM) (sel : Int → PathNodeId) (hbd : Bounded φ)
    (hcsle : g.current_step ≤ stepCount φ) (hreach : MapReachable φ g) (hs : ChainSound g sel) :
    PreSat φ (decode sel) g.current_step ∧
      ∀ k, 0 ≤ k → k < g.current_step → pidOfAssign φ (decode sel) k = sel k := by
  have hreach' := reachable_of_mapReachable φ hbd g hreach
  have hrs : MapChain.ReqSatisfying (reqOf φ) g sel := by
    intro k hk0 hk req hreq hr0 hr1
    exact L1_cor (reqOf φ) (isProhibited φ) hreach' hs.chain.1 hs.chain.2.1 k hk0 hk req hreq hr0 hr1
  have hcm : ChainOnMap φ g sel := chainOnMap_of_nodesOnMap φ g (nodesOnMap_of_mapReachable φ g hreach) sel
    hs.chain.1
  have hpmp := ParentId.PMP_reachable (reqOf φ) (isProhibited φ) g hreach'
  have hgpmp := ParentId.GPMP_reachable (reqOf φ) (isProhibited φ) g hreach'
  exact ⟨preSat_decode φ g sel hbd hcsle hs.chain.1 hrs hcm (noForb_of_mapReachable φ g hreach) hpmp hgpmp
      hs.root_shape.1,
    fun k h0 hk => pidOfAssign_decode_pre φ g sel hbd hcsle hs.chain.1 hrs hcm hpmp hgpmp hs.root_shape.1 k h0 hk⟩

/-- info: 'AbsSatBin.GraphPath.Model.PrefixDecode.decode_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decode_prefix

end AbsSatBin.GraphPath.Model.PrefixDecode
