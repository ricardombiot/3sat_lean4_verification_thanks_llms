-- lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean
import AbsSatBin.GraphPath.Model.FExtInd
import AbsSatBin.GraphPath.Model.UnionLine
import AbsSatBin.GraphPath.Model.StateGrow

/-!
# M1 in parts (`docs/context/escalera_reader.md` §4.2ο.2)

In a joined state `J` of line `n+1` the rows of steps `n` and `n+1` are **pure**: a node there lives in one piece
only, the piece of its key (step `n`: its own map node; step `n+1`: its parent's). Below step `n` tables are unions.

* **`M1aAll`**: in `J` pinned by `ps`, pinning the key of any live node of step `n` keeps it valid.
* **`M1bBelow`**: with the key `k` of a source pinned, `J` pinned lies below the piece of `k`.
* **`m1_of_parts`**: `M1aAll ∧ M1bBelow ⇒ M1`. A live node of step `n` names a source (`PieceJoin.mid_one_source`);
  pin its key; the pinned `J` is a valid kernel below that piece that agrees with `ps`.
* **`pure_field`**: a node of a pure row of `J` has, field by field (owners, parents, sons), what it has in the piece
  of its key (`LineSem.src_pureAdvance`, `UnionLine.srcF_pureAdvance`, `PieceJoin.mid_key`,
  `StateGrow.row_parent_key`).
* **`m1bBelow_of_low`**: so `M1bBelow` reduces to its rows below step `n` (**`M1bLow`**). With the key pinned, the
  top row of the pinned `J` hangs from the key (its parents are pinned), so it is pure too.
* **`readerVerdictW_iff_of_parts`**: the reader decides under `M1aAll` and `M1bLow` at every join.

Measured without failure (`m1split_probe.jl`): M1a-todas (the form `M1aAll`) and M1b-entradas (the owners of
`M1bBelow`).
-/

namespace AbsSatBin.GraphPath.Model.M1Parts

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.ReaderExec

variable (φ : Cnf) (hbd : Bounded φ)

/-- **M1a (all keys)**: pinning the key of any live node of step `n` keeps a valid pinned joined state valid. -/
def M1aAll (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ ps : List NodeId, isValid (filterAll kv'.2 ps) = true →
    ∀ q ∈ (filterAll kv'.2 ps).gowners, q.id.step = (n : Int) → isValid (filterAll kv'.2 (q.id :: ps)) = true

/-- **M1b (below the piece)**: with the key of a source pinned, the pinned joined state lies below its piece. -/
def M1bBelow (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
    ∀ ps : List NodeId, isValid (filterAll kv'.2 (kv.1 :: ps)) = true →
      Below (upF φ kv.2 kv'.1) (filterAll kv'.2 (kv.1 :: ps))

/-- **M1b below step `n`**: the nodes of the lower rows of the pinned joined state are nodes of the piece, field by
field. -/
def M1bLow (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
    ∀ ps : List NodeId, isValid (filterAll kv'.2 (kv.1 :: ps)) = true →
      ∀ p np, (filterAll kv'.2 (kv.1 :: ps)).node? p = some np → p.id.step < (n : Int) →
        ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ (∀ v ∈ np.owners, v ∈ nP.owners) ∧
          (∀ v ∈ np.parents, v ∈ nP.parents) ∧ (∀ v ∈ np.sons, v ∈ nP.sons)

include hbd

-- ============================================================
-- M1 from its parts
-- ============================================================

/-- **`M1aAll ∧ M1bBelow ⇒ M1`.** -/
theorem m1_of_parts (n : Nat) (ha : M1aAll φ n) (hb : M1bBelow φ n) : FExtInd.M1 φ n := by
  intro kv' hkv' ps hv
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have cG := filt_ctx φ hbd _ kv' hok' ps hv
  have hbG := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') ps
  -- a live node at step `n`
  have hnmem : (n : Int) ∈ intRange 0 ((filterAll kv'.2 ps).current_step - 1) :=
    mem_intRange_zero _ _ (by omega) (by rw [← hbG.step, hcs']; omega)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv _ hnmem)
  have hqn : q.id.step = (n : Int) := eq_of_beq hqs
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cG.pc.ker.gn q hq)
  obtain ⟨nJ, hnJ, _, _, _⟩ := hbG.node q nq hnq
  obtain ⟨kv, hkv, hd, hvP, hk, _⟩ := PieceJoin.mid_one_source φ hbd n kv' hkv' q nJ hnJ hqn
  -- pin its key
  have hvk := ha kv' hkv' ps hv q hq hqn
  rw [hk] at hvk
  have hbel := hb kv' hkv' kv hkv hd hvP ps hvk
  have cK := filt_ctx φ hbd _ kv' hok' (kv.1 :: ps) hvk
  refine ⟨kv, hkv, hd, hvP, isValid_filterAll_of_kernel cK.pc.ker hvk hbel ps (fun r hr x hx hxs => ?_)⟩
  exact LineUnion.gowner_pinned kv'.2 _ x hx r (List.mem_cons_of_mem _ hr) hxs

-- ============================================================
-- The pure rows
-- ============================================================

omit hbd in
/-- A node of `J` whose every piece is the piece of `kv` has, field by field, what it has in that piece. -/
theorem pure_field (n : Nat) (sel : PNodeM → List PathNodeId) (hj : UnionLine.JoinsAsUnion sel)
    (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (kv : NodeId × GPathM)
    (p : PathNodeId) (np : PNodeM) (hnp : kv'.2.node? p = some np)
    (hpure : ∀ kv2 ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv2.1 → isValid (upF φ kv2.2 kv'.1) = true →
      ∀ n2, (upF φ kv2.2 kv'.1).node? p = some n2 → kv2 = kv) :
    ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ ∀ w ∈ sel np, w ∈ sel nP := by
  have hkv'' := hkv'
  rw [line_succ] at hkv''
  obtain ⟨kv1, hkv1, hd1, hv1, n1, hn1⟩ := (src_pureAdvance φ (line φ n) kv' hkv'').1 p np hnp
  have e1 := hpure kv1 hkv1 hd1 hv1 n1 hn1
  subst e1
  refine ⟨n1, hn1, fun w hw => ?_⟩
  obtain ⟨kv2, hkv2, hd2, hv2, n2, hn2, hw2⟩ := UnionLine.srcF_pureAdvance φ sel hj (line φ n) kv' hkv'' p np hnp w hw
  have e2 := hpure kv2 hkv2 hd2 hv2 n2 hn2
  subst e2
  rw [hn1] at hn2; cases hn2; exact hw2

/-- A node of `J` at step `n` lives only in the piece of its own map node. -/
theorem pure_mid (n : Nat) (kv' : NodeId × GPathM) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n)
    (p : PathNodeId) (hps : p.id.step = (n : Int)) (hpk : p.id = kv.1) :
    ∀ kv2 ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv2.1 → isValid (upF φ kv2.2 kv'.1) = true →
      ∀ n2, (upF φ kv2.2 kv'.1).node? p = some n2 → kv2 = kv := by
  intro kv2 hkv2 hd2 hv2 n2 hn2
  have hk2 := PieceJoin.mid_key φ hbd n kv2 hkv2 kv'.1 hd2 hv2 p n2 hn2 hps
  exact key_inj (line φ n) (lineOk φ n).1 kv2 hkv2 kv hkv (by rw [← hk2, hpk])

/-- A node of `J` at step `n+1` lives only in the piece of its parent's map node. -/
theorem pure_top (n : Nat) (kv' : NodeId × GPathM) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n)
    (p : PathNodeId) (hps : p.id.step = (n : Int) + 1) (hpk : p.parent_id = some kv.1) :
    ∀ kv2 ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv2.1 → isValid (upF φ kv2.2 kv'.1) = true →
      ∀ n2, (upF φ kv2.2 kv'.1).node? p = some n2 → kv2 = kv := by
  intro kv2 hkv2 hd2 hv2 n2 hn2
  have hk2 := StateGrow.row_parent_key φ hbd n kv2 hkv2 kv'.1 hd2 hv2 p n2 hn2 hps
  rw [hpk] at hk2
  exact key_inj (line φ n) (lineOk φ n).1 kv2 hkv2 kv hkv (Option.some.inj hk2).symm

omit hbd in
/-- A node of a pure row, whole: owners, parents and sons are those of the piece. -/
theorem pure_node (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (kv : NodeId × GPathM)
    (p : PathNodeId) (np : PNodeM) (hnp : kv'.2.node? p = some np)
    (hpure : ∀ kv2 ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv2.1 → isValid (upF φ kv2.2 kv'.1) = true →
      ∀ n2, (upF φ kv2.2 kv'.1).node? p = some n2 → kv2 = kv) :
    ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ (∀ v ∈ np.owners, v ∈ nP.owners) ∧
      (∀ v ∈ np.parents, v ∈ nP.parents) ∧ (∀ v ∈ np.sons, v ∈ nP.sons) := by
  obtain ⟨nP, hnP, ho⟩ := pure_field φ n PNodeM.owners UnionLine.owners_joins kv' hkv' kv p np hnp hpure
  obtain ⟨nP2, hnP2, hp⟩ := pure_field φ n PNodeM.parents UnionLine.parents_joins kv' hkv' kv p np hnp hpure
  obtain ⟨nP3, hnP3, hs⟩ := pure_field φ n PNodeM.sons UnionLine.sons_joins kv' hkv' kv p np hnp hpure
  rw [hnP] at hnP2 hnP3; cases hnP2; cases hnP3
  exact ⟨nP, hnP, ho, hp, hs⟩

-- ============================================================
-- M1b reduces to its lower rows
-- ============================================================

/-- **`M1bLow ⇒ M1bBelow`**: the two pure rows of the pinned joined state lie in the piece of the pinned key. -/
theorem m1bBelow_of_low (n : Nat) (hL : M1bLow φ n) : M1bBelow φ n := by
  intro kv' hkv' kv hkv hd hvP ps hvK
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hok := (lineOk φ n).2 kv hkv
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hkn : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 hok.onMap
  have cK := filt_ctx φ hbd _ kv' hok' (kv.1 :: ps) hvK
  have hbJK := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') (kv.1 :: ps)
  have hKcs : (filterAll kv'.2 (kv.1 :: ps)).current_step = (n : Int) + 2 := by rw [← hbJK.step, hcs']
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvP
  have hPcs : (upF φ kv.2 kv'.1).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hkP : Kernel (upF φ kv.2 kv'.1) :=
    KernelUp.kernel_reachable (reqOf φ) (isProhibited φ) _ (MapReachable.reachable_of_mapReachable φ hbd _ hP.reach) hvP
  -- every node of the pinned joined state is a node of the piece, field by field
  have toP : ∀ p np, (filterAll kv'.2 (kv.1 :: ps)).node? p = some np →
      ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ (∀ v ∈ np.owners, v ∈ nP.owners) ∧
        (∀ v ∈ np.parents, v ∈ nP.parents) ∧ (∀ v ∈ np.sons, v ∈ nP.sons) := by
    intro p np hnp
    have hr := CertFix.step_range cK.pc p np hnp
    rw [hKcs] at hr
    have hpg := cK.pc.ker.gow p np hnp
    obtain ⟨nJ, hnJ, hoJ, hpJ, hsJ⟩ := hbJK.node p np hnp
    have lift : (∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ (∀ v ∈ nJ.owners, v ∈ nP.owners) ∧
        (∀ v ∈ nJ.parents, v ∈ nP.parents) ∧ (∀ v ∈ nJ.sons, v ∈ nP.sons)) →
        ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ (∀ v ∈ np.owners, v ∈ nP.owners) ∧
          (∀ v ∈ np.parents, v ∈ nP.parents) ∧ (∀ v ∈ np.sons, v ∈ nP.sons) := by
      rintro ⟨nP, hnP, ho, hp, hs⟩
      exact ⟨nP, hnP, fun v h => ho v (hoJ v h), fun v h => hp v (hpJ v h), fun v h => hs v (hsJ v h)⟩
    by_cases hlow : p.id.step < (n : Int)
    · exact hL kv' hkv' kv hkv hd hvP ps hvK p np hnp hlow
    · by_cases hmid : p.id.step = (n : Int)
      · -- step `n`: the pinned key
        have hpk : p.id = kv.1 :=
          LineUnion.gowner_pinned kv'.2 _ p hpg kv.1 List.mem_cons_self (by rw [hmid, hkn])
        exact lift (pure_node φ n kv' hkv' kv p nJ hnJ (pure_mid φ hbd n kv' kv hkv p hmid hpk))
      · -- step `n+1`: its parent is a pinned node of step `n`
        have htop : p.id.step = (n : Int) + 1 := by omega
        have hkv'' := hkv'
        rw [line_succ] at hkv''
        obtain ⟨kv1, hkv1, hd1, hv1, n1, hn1⟩ := (src_pureAdvance φ (line φ n) kv' hkv'').1 p nJ hnJ
        have hpar1 := StateGrow.row_parent_key φ hbd n kv1 hkv1 kv'.1 hd1 hv1 p n1 hn1 htop
        have hpars : np.parents ≠ [] := by
          rcases ((isValidNode_iff _ np).mp (cK.pc.ker.valid p np hnp)).2.1 with h | h
          · rw [node?_id_eq _ p np hnp, hpar1] at h; exact absurd h (by simp)
          · exact h
        obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hpars
        have hcid : some c.id = p.parent_id := by
          rw [← node?_id_eq _ p np hnp]; exact cK.rc.pmp np (List.mem_of_find?_eq_some hnp) c hc
        rw [hpar1] at hcid
        have hc1 : c.id = kv1.1 := Option.some.inj hcid
        obtain ⟨_, nc, hnc, _⟩ := cK.pc.ker.linkP p np hnp c hc
        have hk1 : kv1.1.step = (n : Int) := mapNodes_step φ n kv1.1 ((lineOk φ n).2 kv1 hkv1).onMap
        have hck : c.id = kv.1 := LineUnion.gowner_pinned kv'.2 _ c (cK.pc.ker.gow c nc hnc) kv.1 List.mem_cons_self
          (by rw [hc1, hk1, hkn])
        have hpk : p.parent_id = some kv.1 := by rw [hpar1, ← hc1, hck]
        exact lift (pure_node φ n kv' hkv' kv p nJ hnJ (pure_top φ hbd n kv' kv hkv p htop hpk))
  refine ⟨by rw [hKcs, hPcs], fun q hq => ?_, fun p np hnp => toP p np hnp⟩
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cK.pc.ker.gn q hq)
  obtain ⟨nP, hnP, _⟩ := toP q nq hnq
  exact hkP.gow q nP hnP

/-- **The reader decides `φ` under `M1aAll` and `M1bLow` at every join.** -/
theorem readerVerdictW_iff_of_parts
    (hA : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1aAll φ n)
    (hL : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1bLow φ n) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  FExtInd.readerVerdictW_iff_of_m1 φ hbd (fun n h1 hn =>
    m1_of_parts φ hbd n (hA n h1 hn) (m1bBelow_of_low φ hbd n (hL n h1 hn)))

end AbsSatBin.GraphPath.Model.M1Parts

/-- info: 'AbsSatBin.GraphPath.Model.M1Parts.readerVerdictW_iff_of_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.M1Parts.readerVerdictW_iff_of_parts
