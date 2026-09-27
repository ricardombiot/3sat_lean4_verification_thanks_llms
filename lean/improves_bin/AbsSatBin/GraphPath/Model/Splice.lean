-- lean/improves_bin/AbsSatBin/GraphPath/Model/Splice.lean
import AbsSatBin.GraphPath.Model.UnionLine

/-!
# Splicing certificates: the global structure of the network

Measured (`julia/improves_bin/test_3sat/probes/splice_probe.jl`, `docs/context/ambfar.md` §4.2μ): two certificates of a
state that share a node at step `s` splice (the prefix of one up to `s`, the suffix of the other after `s`) into a
certificate of the same state **exactly when the splice respects the requirements** — every failed splice violates a
requirement (266 824 of 266 824). A node is a window of three steps, so the splice respects every window, the prohibited
ones included: the prohibited window removes unsatisfiable certificates locally, and only the long-range requirements
(a literal of a clause that names a variable far back) couple the two sides.

* **`splice`**: the splice of two certificates of a state of the run, at a shared node, whose crossing requirements are
  met, is a certificate of the same state. Global and semantic: the splice is a linked path that meets the requirements,
  so it reads as a partial solution (`PrefixDecode.preSat_decode`), which the machine carries into the state of its key
  (`PrefixCarry.cert_of_prefix`) — the key of the second certificate's top, so the same state.
-/

namespace AbsSatBin.GraphPath.Model.Splice

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.CnfChain
open AbsSatBin.GraphPath.Model.PrefixCarry

variable (φ : Cnf) (hbd : Bounded φ)
include hbd

/-- **Splicing two certificates at a shared node**: if the requirements that cross the splice point are met by the first
certificate, the splice is a certificate of the same state. -/
theorem splice (n : Nat) (hn : (n : Int) < stepCount φ) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n)
    (σ τ : Int → PathNodeId) (hσ : ChainSound kv.2 σ) (hτ : ChainSound kv.2 τ) (s : Int) (hs0 : 0 ≤ s)
    (hsn : s ≤ n) (heq : σ s = τ s)
    (hreq : ∀ k, s < k → k ≤ n → ∀ r ∈ reqOf φ (τ k).id, 0 ≤ r.step → r.step ≤ s → (σ r.step).id = r) :
    ∃ ρ, ChainSound kv.2 ρ ∧ (∀ k, 0 ≤ k → k ≤ s → ρ k = σ k) ∧ (∀ k, s ≤ k → k ≤ n → ρ k = τ k) := by
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hcs : kv.2.current_step = (n : Int) + 1 := hok.step
  have hreach := reachable_of_mapReachable φ hbd kv.2 hok.reach
  -- the splice
  let ρ : Int → PathNodeId := fun k => if k ≤ s then σ k else τ k
  have hρlo : ∀ k, k ≤ s → ρ k = σ k := fun k hk => if_pos hk
  have hρhi : ∀ k, s ≤ k → ρ k = τ k := fun k hk => by
    by_cases h : k ≤ s
    · have e : k = s := by omega
      show (if k ≤ s then σ k else τ k) = τ k
      rw [if_pos h, e, heq]
    · exact if_neg h
  -- a linked path
  have hchain : IsChain kv.2 ρ := by
    refine ⟨fun k h0 h1 => ?_, fun k h0 h1 => ?_⟩
    · by_cases h : k ≤ s
      · rw [hρlo k h]; exact hσ.chain.1.1 k h0 h1
      · rw [hρhi k (by omega)]; exact hτ.chain.1.1 k h0 h1
    · by_cases h : k < s
      · rw [hρlo k (by omega), hρlo (k + 1) (by omega)]; exact hσ.chain.1.2 k h0 h1
      · rw [hρhi k (by omega), hρhi (k + 1) (by omega)]; exact hτ.chain.1.2 k h0 h1
  -- that meets the requirements
  have hrsσ : MapChain.ReqSatisfying (reqOf φ) kv.2 σ := fun k hk0 hk req hreq hr0 hr1 =>
    L1_cor (reqOf φ) (isProhibited φ) hreach hσ.chain.1 hσ.chain.2.1 k hk0 hk req hreq hr0 hr1
  have hrsτ : MapChain.ReqSatisfying (reqOf φ) kv.2 τ := fun k hk0 hk req hreq hr0 hr1 =>
    L1_cor (reqOf φ) (isProhibited φ) hreach hτ.chain.1 hτ.chain.2.1 k hk0 hk req hreq hr0 hr1
  have hrs : MapChain.ReqSatisfying (reqOf φ) kv.2 ρ := by
    intro k hk0 hk req hrq hr0 hr1
    by_cases hks : k ≤ s
    · rw [hρlo k hks] at hrq
      have hback := reqOf_backward φ hbd _ req hrq
      rw [(hσ.chain.1.1 k hk0 hk).2] at hback
      rw [hρlo req.step (by omega)]
      exact hrsσ k hk0 hk req hrq hr0 hr1
    · rw [hρhi k (by omega)] at hrq
      by_cases hrs' : req.step ≤ s
      · rw [hρlo req.step hrs']
        exact hreq k (by omega) (by rw [hcs] at hk; omega) req hrq hr0 hrs'
      · rw [hρhi req.step (by omega)]
        exact hrsτ k hk0 hk req hrq hr0 hr1
  have hcm := chainOnMap_of_nodesOnMap φ kv.2 (nodesOnMap_of_mapReachable φ kv.2 hok.reach) ρ hchain
  have hpmp := ParentId.PMP_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have hgpmp := ParentId.GPMP_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have hroot : (ρ 0).parent_id = none := by rw [hρlo 0 hs0]; exact hσ.root_shape.1
  have hcsle : kv.2.current_step ≤ stepCount φ := by rw [hcs]; omega
  -- a partial solution
  have hpre := PrefixDecode.preSat_decode φ kv.2 ρ hbd hcsle hchain hrs hcm (noForb_of_mapReachable φ kv.2 hok.reach)
    hpmp hgpmp hroot
  have hpid : ∀ k, 0 ≤ k → k < kv.2.current_step → pidOfAssign φ (decode ρ) k = ρ k := fun k h0 hk =>
    PrefixDecode.pidOfAssign_decode_pre φ kv.2 ρ hbd hcsle hchain hrs hcm hpmp hgpmp hroot k h0 hk
  rw [hcs] at hpre
  -- carried by the machine into the state of its key
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  obtain ⟨g, hmem, hgcs, sel', hs', hids⟩ := cert_of_prefix φ (decode ρ) hbd ((n : Int) + 1) hpre hzero n hn
    (Int.le_refl _)
  have htop : selOfAssign φ (decode ρ) n = kv.1 := by
    have e := hpid n (by omega) (by rw [hcs]; omega)
    obtain ⟨hsome, hstep⟩ := hτ.chain.1.1 n (by omega) (by rw [hcs]; omega)
    obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hsome
    have hself := hτ.self_owned n (by omega) (by rw [hcs]; omega)
    simp only [ownersOf, hnr] at hself
    have hk := top_entry_key φ hbd n kv hkv _ nr hnr _ hself hstep
    rw [← hk, ← hρhi n hsn, ← e]; rfl
  have he : (selOfAssign φ (decode ρ) n, g) = kv := key_inj _ (lineOk φ n).1 _ hmem kv hkv htop
  have hokg : StateOk φ n (selOfAssign φ (decode ρ) n, g) := (lineOk φ n).2 _ hmem
  have hreachg := reachable_of_mapReachable φ hbd g hokg.reach
  have heqρ : ∀ k, 0 ≤ k → k < (n : Int) + 1 → sel' k = ρ k := fun k h0 hk => by
    rw [chain_eq_pid φ g sel' (decode ρ) hs'.chain.1 (ParentId.PMP_reachable (reqOf φ) (isProhibited φ) g hreachg)
      (ParentId.GPMP_reachable (reqOf φ) (isProhibited φ) g hreachg) hs'.root_shape.1 hids k h0 (by rw [hgcs]; exact hk)]
    exact hpid k h0 (by rw [hcs]; exact hk)
  have hgk : g = kv.2 := by rw [← he]
  refine ⟨sel', hgk ▸ hs', fun k h0 hk => ?_, fun k hk hkn => ?_⟩
  · rw [heqρ k h0 (by omega)]; exact hρlo k hk
  · rw [heqρ k (by omega) (by omega)]; exact hρhi k hk

/-- info: 'AbsSatBin.GraphPath.Model.Splice.splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms splice

end AbsSatBin.GraphPath.Model.Splice
