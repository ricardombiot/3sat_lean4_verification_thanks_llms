-- lean/improves_bin/AbsSatBin/GraphPath/Model/Splice.lean
import AbsSatBin.GraphPath.Model.UnionLine

/-!
# Splicing certificates: the global structure of the network

Measured (`julia/improves_bin/test_3sat/probes/splice_probe.jl`, `docs/context/escalera_reader.md` §4.2μ): two certificates of a
state that share a node at step `s` splice (the prefix of one up to `s`, the suffix of the other after `s`) into a
certificate of the same state **exactly when the splice respects the requirements** — every failed splice violates a
requirement (266 824 of 266 824). A node is a window of three steps, so the splice respects every window, the prohibited
ones included: the prohibited window removes unsatisfiable certificates locally, and only the long-range requirements
(a literal of a clause that names a variable far back) couple the two sides.

* **`splice`**: the splice of two certificates of a state of the run, at a shared node, whose crossing requirements are
  met, is a certificate of the same state. Global and semantic: the splice is a linked path that meets the requirements,
  so it reads as a partial solution (`PrefixDecode.preSat_decode`), which the machine carries into the state of its key
  (`PrefixCarry.cert_of_prefix`) — the key of the second certificate's top, so the same state.
* **Certificates by induction on the top step** (`CertUpTo`, `SuffixSplit`, `certUpTo_succ`, `certClique_of_splits`): a
  clique with witnesses splits at a step `s` into a suffix certificate `τ` through its upper members and a lower clique
  with witnesses `P` (its lower members plus nodes naming the crossing requirements of `τ`); `P` has a certificate by
  induction, and it splices with `τ`. Measured (`goodsuffix_v3_probe.jl`): a suffix has a compatible prefix exactly when
  such a `P` exists (133 968 / 8 407, no exception). **`readerVerdictW_iff_of_splits`**: the reader decides when every
  clique with witnesses of the last line splices (and the cliques at step 0 have certificates).
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
open AbsSatBin.GraphPath.Model.CliqueTri (Clique)
open AbsSatBin.GraphPath.Model.CertDescent (Wit)
open AbsSatBin.GraphPath.Model.CertFix (CertThrough)
open AbsSatBin.GraphPath.Model.CertInvariant (CertClique)

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

-- ============================================================
-- Certificates by induction on the top step, through splices
-- ============================================================

omit hbd in
/-- Every clique with witnesses whose members lie at steps `≤ t` has a certificate. -/
def CertUpTo (g : GPathM) (t : Int) : Prop :=
  ∀ Q, (∀ q ∈ Q, q.id.step ≤ t) → Clique g Q → Wit g Q → CertThrough g Q

omit hbd in
/-- **A splice of `Q` at step `s`**: a member of `Q` at `s`, a certificate `τ` through the members of `Q` at steps
`≥ s`, and a clique with witnesses `P` at steps `≤ s` holding the members of `Q` below `s` and, for every requirement of
`τ` above `s` that looks at or below `s`, a node naming it. -/
def SuffixSplit (g : GPathM) (n : Nat) (Q : List PathNodeId) (s : Int) : Prop :=
  0 ≤ s ∧ (∃ q ∈ Q, q.id.step = s) ∧ ∃ τ, ChainSound g τ ∧ (∀ x ∈ Q, s ≤ x.id.step → τ x.id.step = x) ∧
    ∃ P : List PathNodeId, (∀ x ∈ Q, x.id.step ≤ s → x ∈ P) ∧ (∀ p ∈ P, p.id.step ≤ s) ∧
      (∀ k, s < k → k ≤ n → ∀ r ∈ reqOf φ (τ k).id, 0 ≤ r.step → r.step ≤ s → ∃ p ∈ P, p.id = r) ∧
      Clique g P ∧ Wit g P

/-- **One step of the induction**: if every clique with witnesses up to step `t` has a certificate, and every clique with
witnesses with a member at `t+1` splices at some `s ≤ t`, every clique with witnesses up to `t+1` has a certificate. The
lower clique `P` has a certificate `σ` (it lives at steps `≤ s ≤ t`); `σ` names the crossing requirements of `τ` and
meets `τ` at the member of step `s`, so the splice (`splice`) is a certificate through `Q`. -/
theorem certUpTo_succ (n : Nat) (hn : (n : Int) < stepCount φ) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (t : Int)
    (hlow : CertUpTo kv.2 t)
    (hS : ∀ Q, (∀ q ∈ Q, q.id.step ≤ t + 1) → Clique kv.2 Q → Wit kv.2 Q → (∃ q ∈ Q, q.id.step = t + 1) →
      ∃ s, s ≤ t ∧ SuffixSplit φ kv.2 n Q s) :
    CertUpTo kv.2 (t + 1) := by
  intro Q hQs hQ hW
  cases hany : Q.any (fun q => decide (q.id.step = t + 1)) with
  | true =>
    have htop : ∃ q ∈ Q, q.id.step = t + 1 := by
      obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hany; exact ⟨q, hq, of_decide_eq_true hqs⟩
    obtain ⟨s, hst, hs0, ⟨q, hqQ, hqs⟩, τ, hτ, hτQ, P, hPQ, hPs, hPreq, hPc, hPw⟩ := hS Q hQs hQ hW htop
    obtain ⟨σ, hσ, hσP⟩ := hlow P (fun p hp => Int.le_trans (hPs p hp) hst) hPc hPw
    have c := KernelUp.aCtx_line φ hbd n kv hkv
    have hcs : kv.2.current_step = (n : Int) + 1 := ((lineOk φ n).2 kv hkv).step
    have hrange : ∀ x ∈ Q, 0 ≤ x.id.step ∧ x.id.step ≤ n := fun x hx => by
      obtain ⟨nx, hnx, _⟩ := hQ x hx
      have h := CertFix.step_range c.pc x nx hnx
      rw [hcs] at h
      exact ⟨h.1, Int.lt_add_one_iff.mp h.2⟩
    have hsn : s ≤ n := by rw [← hqs]; exact (hrange q hqQ).2
    have hqP : q ∈ P := hPQ q hqQ (Int.le_of_eq hqs)
    have heq : σ s = τ s := by
      rw [← hqs, hσP q hqP, hτQ q hqQ (Int.le_of_eq hqs.symm)]
    have hreq : ∀ k, s < k → k ≤ n → ∀ r ∈ reqOf φ (τ k).id, 0 ≤ r.step → r.step ≤ s → (σ r.step).id = r := by
      intro k hk1 hk2 r hr h0 h1
      obtain ⟨p, hpP, hpr⟩ := hPreq k hk1 hk2 r hr h0 h1
      have hps : p.id.step = r.step := by rw [hpr]
      rw [← hps, hσP p hpP, hpr]
    obtain ⟨ρ, hρ, hlo, hhi⟩ := splice φ hbd n hn kv hkv σ τ hσ hτ s hs0 hsn heq hreq
    refine ⟨ρ, hρ, fun x hx => ?_⟩
    by_cases hxs : x.id.step ≤ s
    · rw [hlo _ (hrange x hx).1 hxs]; exact hσP x (hPQ x hx hxs)
    · have hsx : s ≤ x.id.step := Int.le_of_lt (Int.not_le.mp hxs)
      rw [hhi _ hsx (hrange x hx).2]; exact hτQ x hx hsx
  | false =>
    exact hlow Q (fun q hq => by
      have := hQs q hq
      have : q.id.step ≠ t + 1 := fun h => (List.any_eq_false.mp hany) q hq (decide_eq_true h)
      omega) hQ hW

/-- info: 'AbsSatBin.GraphPath.Model.Splice.certUpTo_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certUpTo_succ

omit hbd in
/-- **`SplitStep`** at a state of line `n`: every clique with witnesses whose top member is at `t+1` splices at some
`s ≤ t`. -/
def SplitStep (g : GPathM) (n : Nat) : Prop :=
  ∀ t : Int, 0 ≤ t → t < n → ∀ Q, (∀ q ∈ Q, q.id.step ≤ t + 1) → Clique g Q → Wit g Q →
    (∃ q ∈ Q, q.id.step = t + 1) → ∃ s, s ≤ t ∧ SuffixSplit φ g n Q s

/-- **`CertClique` of a state from splices**: by induction on the top step, the certificates of the cliques at step 0
and `SplitStep` give a certificate to every clique with witnesses. -/
theorem certClique_of_splits (n : Nat) (hn : (n : Int) < stepCount φ) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n)
    (h0 : CertUpTo kv.2 0) (hS : SplitStep φ kv.2 n) : CertClique kv.2 := by
  have up : ∀ m : Nat, m ≤ n → CertUpTo kv.2 m := by
    intro m
    induction m with
    | zero => intro _; exact h0
    | succ m ih =>
      intro hm
      have hm' : m < n := Nat.lt_of_succ_le hm
      have := certUpTo_succ φ hbd n hn kv hkv m (ih (Nat.le_of_lt hm')) (fun Q hQs hQ hW htop =>
        hS m (Int.natCast_nonneg m) (Int.ofNat_lt.mpr hm') Q hQs hQ hW htop)
      push_cast; exact this
  intro Q hQ hW
  have c := KernelUp.aCtx_line φ hbd n kv hkv
  have hcs : kv.2.current_step = (n : Int) + 1 := ((lineOk φ n).2 kv hkv).step
  exact up n (Nat.le_refl n) Q (fun q hq => by
    obtain ⟨nq, hnq, _⟩ := hQ q hq
    have h := CertFix.step_range c.pc q nq hnq
    rw [hcs] at h
    exact Int.lt_add_one_iff.mp h.2) hQ hW

/-- info: 'AbsSatBin.GraphPath.Model.Splice.certClique_of_splits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certClique_of_splits

/-- **The reader decides `φ` when, in every state of the last line, the cliques at step 0 have certificates and every
clique with witnesses splices** (the lower part, widened by the crossing requirements of a suffix, is a clique with
witnesses). -/
theorem readerVerdictW_iff_of_splits
    (h0 : ∀ kv ∈ pureRun φ, CertUpTo kv.2 0)
    (hS : ∀ kv ∈ pureRun φ, SplitStep φ kv.2 (stepCount φ - 1).toNat) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine CertInvariant.readerVerdictW_iff_of_certClique φ hbd (fun kv hkv => ?_)
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by simp only [stepCount]; omega
  have hkvl : kv ∈ line φ (stepCount φ - 1).toNat := hkv
  exact certClique_of_splits φ hbd _ hN kv hkvl (h0 kv hkv) (hS kv hkv)

/-- info: 'AbsSatBin.GraphPath.Model.Splice.readerVerdictW_iff_of_splits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_splits

end AbsSatBin.GraphPath.Model.Splice
