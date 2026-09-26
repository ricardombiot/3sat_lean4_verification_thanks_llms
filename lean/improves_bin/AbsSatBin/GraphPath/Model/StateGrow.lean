-- lean/improves_bin/AbsSatBin/GraphPath/Model/StateGrow.lean
import AbsSatBin.GraphPath.Model.ClauseWitness

/-!
# The correction: cliques inside one state, and the witness of the new step pins the source

The Julia probe (`julia/improves_bin/test_3sat/probes/extat_probe.jl`, `docs/context/ambfar.md` §4.2z)
showed that `LineSem.SemCert` is **false**: it lets every entry of a clique come from a different state of
the line, and in `rand3sat_v8_c10` (step 38) such a mixed clique has witnesses and no solution. Inside a
single state there was no failure (1.3 M cliques, 13 M extensions), and the mixed clique dies at the next
join because **the witness of the new step lives in one piece, which comes from one source state**.

This module states the reader's hypothesis inside one state and proves the join rule.

* **`GrowState g`**: in the state `g`, a clique with witnesses gains a node at any step, keeping its
  witnesses (the per-state `ExtAt`).
* **`certClique_of_grow`**: growing to a node at every step gives a certificate (`CertDescent.chain_of_cover`),
  so `GrowState ⇒ CertClique`; **`readerVerdictW_iff_of_grow`**: the reader decides `φ` when the starting
  states grow. This replaces the per-entry route (`LineSem`), whose hypothesis is false.
* **`row_parent_key`**: a node of a piece `upF X d` at the new step has, as parent, the key of `X`.
* **`top_one_source`** (the join rule): in a state of line `n+1`, **every entry** of a node at the new step
  comes from the same source state — the one whose key is the node's parent. The join cannot mix
  sources in the table of a new node.
* **`clique_in_source`**: so a clique owned by a node at the new step lies, whole, in the filtered source:
  every member is a node there and owns a parent of that node.
-/

namespace AbsSatBin.GraphPath.Model.StateGrow

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri (Clique OwnsAll)
open AbsSatBin.GraphPath.Model.CertDescent (Wit pick chain_of_cover)
open AbsSatBin.GraphPath.Model.CertFix (CertThrough)
open AbsSatBin.GraphPath.Model.CertInvariant (CertClique certLink_of_certClique)
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

-- ============================================================
-- The hypothesis inside one state
-- ============================================================

/-- **Growth inside one state**: a clique with witnesses gains a node at any step, keeping witnesses. -/
def GrowState (g : GPathM) : Prop :=
  ∀ Q, Clique g Q → Wit g Q → ∀ l, 0 ≤ l → l < g.current_step →
    ∃ r, r.id.step = l ∧ Clique g (r :: Q) ∧ Wit g (r :: Q)

theorem cover_of_grow {g : GPathM} (hG : GrowState g) (Q : List PathNodeId) (hQ : Clique g Q) (hW : Wit g Q) :
    ∀ m : Nat, ∃ Q', (∀ p ∈ Q, p ∈ Q') ∧ Clique g Q' ∧ Wit g Q' ∧
      ∀ l, 0 ≤ l → l < (m : Int) → l < g.current_step → ∃ p ∈ Q', p.id.step = l := by
  intro m
  induction m with
  | zero => exact ⟨Q, fun p hp => hp, hQ, hW, fun l h0 h1 _ => absurd h1 (by omega)⟩
  | succ m ih =>
    obtain ⟨Q', hsub, hQ', hW', hcov⟩ := ih
    by_cases hm : (m : Int) < g.current_step
    · obtain ⟨r, hrs, hQr, hWr⟩ := hG Q' hQ' hW' m (by omega) hm
      refine ⟨r :: Q', fun p hp => List.mem_cons_of_mem _ (hsub p hp), hQr, hWr, fun l h0 h1 h2 => ?_⟩
      rcases Int.lt_or_le l m with hl | hl
      · obtain ⟨p, hp, hps⟩ := hcov l h0 hl h2
        exact ⟨p, List.mem_cons_of_mem _ hp, hps⟩
      · exact ⟨r, List.mem_cons_self, by rw [hrs]; omega⟩
    · exact ⟨Q', hsub, hQ', hW', fun l h0 h1 h2 => hcov l h0 (by omega) h2⟩

/-- **`GrowState ⇒ CertClique`**: a clique grown to a node at every step is a certificate. -/
theorem certClique_of_grow {g : GPathM} (c : AmbTriCore.ACtx g) (hG : GrowState g) : CertClique g := by
  intro Q hQ hW
  obtain ⟨Q', hsub, hQ', _, hcov⟩ := cover_of_grow hG Q hQ hW g.current_step.toNat
  obtain ⟨hs, hon⟩ := chain_of_cover c Q' hQ' (fun l h0 h1 => hcov l h0 (by omega) h1)
  exact ⟨pick Q', hs, fun p hp => hon p (hsub p hp)⟩

variable (φ : Cnf)

/-- **The reader decides `φ` when its starting states grow.** -/
theorem readerVerdictW_iff_of_grow (hbd : Bounded φ)
    (h : ∀ kv ∈ pureRun φ, isValid (filterAll kv.2 []) = true → GrowState (filterAll kv.2 [])) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine CertFix.readerVerdictW_iff_of_certLink φ hbd (fun kv hkv hv => ?_)
  have c := AmbTriCore.aCtx_readPins φ hbd kv hkv [] _ ReadPins.start hv
  exact certLink_of_certClique c (certClique_of_grow c (h kv hkv hv))

-- ============================================================
-- The join rule: the witness of the new step pins the source
-- ============================================================

section join
variable (hbd : Bounded φ) (n : Nat)
include hbd

/-- **A node of a piece at the new step has, as parent, the key of the source.** -/
theorem row_parent_key (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId) (hd : d ∈ sonsOfMap φ kv.1)
    (hv : isValid (upF φ kv.2 d) = true) (w : PathNodeId) (nw : PNodeM) (hw : (upF φ kv.2 d).node? w = some nw)
    (hws : w.id.step = (n : Int) + 1) : w.parent_id = some kv.1 := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  obtain ⟨hwnew, _⟩ := upF_new φ kv.2 d hdst c hv w nw hw (by omega)
  obtain ⟨p, hp⟩ := exists_rowParent _ d _ (by omega) hwnew
  obtain ⟨hps1, hps⟩ := rowParent_node _ d (by omega) hp
  obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp hps1
  have hzp : shiftPid p d = w := eq_of_beq (List.mem_filter.mp hp).2
  have hself := TriPinCut.self_own_pc c.pc p np hnp
  obtain ⟨nJ, hnJ, hoJ, _, _⟩ := hb.node p np hnp
  have hkey := top_entry_key φ hbd n kv hkv p nJ hnJ p (hoJ p hself) (by rw [hps, hFcs]; omega)
  rw [← hzp, ← hkey]; rfl

/-- **The join rule.** Every entry of a node at the new step of a state of line `n+1` comes from the same
source state: the one whose key is the node's parent. -/
theorem top_one_source (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (w : PathNodeId) (nw : PNodeM)
    (hw : kv'.2.node? w = some nw) (hws : w.id.step = (n : Int) + 1) :
    ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 kv'.1) = true ∧
      w.parent_id = some kv.1 ∧ ∀ v ∈ nw.owners, ∃ n', (upF φ kv.2 kv'.1).node? w = some n' ∧ v ∈ n'.owners := by
  have hkv'' := hkv'
  rw [line_succ] at hkv''
  obtain ⟨kv, hkv, hd, hv, n0, hn0⟩ := (src_pureAdvance φ (line φ n) kv' hkv'').1 w nw hw
  have hpk := row_parent_key φ hbd n kv hkv kv'.1 hd hv w n0 hn0 hws
  refine ⟨kv, hkv, hd, hv, hpk, fun v hv' => ?_⟩
  obtain ⟨kv2, hkv2, hd2, hv2, n2, hn2, hvn2⟩ := (src_pureAdvance φ (line φ n) kv' hkv'').2 w nw hw v hv'
  have hpk2 := row_parent_key φ hbd n kv2 hkv2 kv'.1 hd2 hv2 w n2 hn2 hws
  have hsame : kv2 = kv := by
    refine key_inj (line φ n) (lineOk φ n).1 kv2 hkv2 kv hkv ?_
    rw [hpk] at hpk2; exact (Option.some.inj hpk2).symm
  subst hsame
  exact ⟨n2, hn2, hvn2⟩

/-- **A clique owned by a node at the new step lies in one filtered source**: each member is a node of it
and owns there a parent of that node. -/
theorem clique_in_source (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (w : PathNodeId) (nw : PNodeM)
    (hw : kv'.2.node? w = some nw) (hws : w.id.step = (n : Int) + 1) (Q : List PathNodeId)
    (hQw : ∀ q ∈ Q, q ∈ nw.owners) (hQs : ∀ q ∈ Q, q.id.step ≤ (n : Int)) :
    ∃ kv ∈ line φ n, w.parent_id = some kv.1 ∧ ∀ q ∈ Q, ∃ nq, (filterAll kv.2 (reqOf φ kv'.1)).node? q = some nq ∧
      ∃ p ∈ rowParents (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 w, p ∈ nq.owners := by
  obtain ⟨kv, hkv, hd, hv, hpk, hsrc⟩ := top_one_source φ hbd n kv' hkv' w nw hw hws
  refine ⟨kv, hkv, hpk, fun q hq => ?_⟩
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  obtain ⟨n', hn', hqn'⟩ := hsrc q (hQw q hq)
  obtain ⟨_, hrow⟩ := upF_new φ kv.2 kv'.1 hdst c hv w n' hn' (by omega)
  rcases (mem_rowOwners_iff _ _ w q).mp (hrow q hqn') with ⟨hu, _⟩ | he
  · obtain ⟨p, hp, np, hnp, hqp⟩ := KernelReader.mem_unionOwnersOf_inv _ _ q hu
    obtain ⟨nq, hnq⟩ := c.pc.ker.isNode_owner p np hnp q hqp
    exact ⟨nq, hnq, p, hp, c.pc.ker.sym p np q nq hnp hnq hqp⟩
  · exfalso; have := hQs q hq; rw [he] at this; omega

end join

/-- info: 'AbsSatBin.GraphPath.Model.StateGrow.readerVerdictW_iff_of_grow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_grow

/-- info: 'AbsSatBin.GraphPath.Model.StateGrow.clique_in_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms clique_in_source

end AbsSatBin.GraphPath.Model.StateGrow
