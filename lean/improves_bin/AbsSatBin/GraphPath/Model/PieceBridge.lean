-- lean/improves_bin/AbsSatBin/GraphPath/Model/PieceBridge.lean
import AbsSatBin.GraphPath.Model.FilterUnion
import AbsSatBin.GraphPath.Model.UpMono

/-!
# The two bridges between a source and its piece, for map pins (`docs/context/escalera_reader.md` §4.2ο)

A source `X` of line `n` and its piece `upF φ X d`. The pins of `X` for the key `d` are `pinsW`: the requirements of
`d`, and `L1 = 1` when the filter of `X` skips a window (the prohibited window of a clause is `(0, 0, 0)`, and a
skipped window leaves only `L1 = 1` alive, `StatePiece.skip_window`). With those pins the piece and its source agree
on validity, for every pin set below the top:

* **`src_of_piece`** (M2w, down): if the piece pinned by `ps` is valid, the source pinned by `pinsW` and by the pins
  of `ps` below the top is valid. The truncated pinned piece is a valid kernel below it
  (`FilterUnion.piece_pinned_below`).
* **`piece_of_src`** (M3w, up): if the source pinned by `pinsW` and by `ps` (pins below the top) is valid, the piece
  pinned by `ps` is valid. The pinned source `K` skips no window (without a skip in the filter of `X` it has fewer
  candidates; with one, `pinsW` pins `L1 = 1` and every prohibited candidate needs `L1 = 0`), so `up K` is the plain
  `addNode K`: a valid kernel (`KernelUp.kernel_up`), below the piece (`UpMono.below_addNode`, and the review of the
  piece never goes below a kernel), that agrees with `ps`.

Measured before (`fextind_probe.jl`): M3 without the window pin fails once in `clause_mix.cnf`; with the window pinned
(M3w) and M2w, no failure.
-/

namespace AbsSatBin.GraphPath.Model.PieceBridge

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel

variable (φ : Cnf) (hbd : Bounded φ) (n : Nat)

/-- The requirements are among the pins `pinsW`. -/
theorem reqs_sub_pinsW (d k : NodeId) : ∀ r ∈ reqOf φ d, r ∈ LineUnion.pinsW φ n d k := by
  intro r hr
  unfold LineUnion.pinsW
  split
  · exact List.mem_append_left _ hr
  · exact hr

/-- With a skipped window in the source's filter, `pinsW` pins `L1 = 1`. -/
theorem l1_mem_pinsW (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hsk : skipsWindow (filterAll kv.2 (reqOf φ d)) d (isProhibited φ) = true) :
    (⟨(n : Int) - 1, 1⟩ : NodeId) ∈ LineUnion.pinsW φ n d kv.1 := by
  unfold LineUnion.pinsW
  rw [if_pos (List.any_eq_true.mpr ⟨kv, hkv, by simp only [beq_self_eq_true, hsk, Bool.and_self]⟩)]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

include hbd

/-- **M2w**: a valid pinned piece gives a valid source pinned by `pinsW` and by the pins below the top. -/
theorem src_of_piece (hn1 : 1 ≤ n) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) (ps : List NodeId)
    (hvP : isValid (filterAll (upF φ kv.2 d) ps) = true) :
    isValid (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int))))) =
      true := by
  obtain ⟨hok, hdst, hcs, _, _, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have hb := FilterUnion.piece_pinned_below φ hbd n hn1 kv hkv d hd hv ps hvP
  have hP : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hreachP := MapReachable.reachable_of_mapReachable φ hbd _ hP.reach
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreachP
  have hPcs : (upF φ kv.2 d).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hQcs : (filterAll (upF φ kv.2 d) ps).current_step = (n : Int) + 2 := by
    rw [← (KernelIff.below_filterAll_self _ hndP ps).step, hPcs]
  have hXcs : (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int))))).current_step =
      (n : Int) + 1 := by rw [(pruned_filterAll _ _).step_eq, hcs]
  unfold isValid
  refine List.all_eq_true.mpr (fun k hk => ?_)
  have hk0 := mem_intRange_lower hk
  have hk1 := mem_intRange_upper hk
  rw [hXcs] at hk1
  have hkQ : k ∈ intRange 0 ((filterAll (upF φ kv.2 d) ps).current_step - 1) :=
    mem_intRange_zero k _ hk0 (by rw [hQcs]; omega)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvP k hkQ)
  have hqk : q.id.step = k := eq_of_beq hqs
  have hqT : q ∈ (Trunc.trunc (filterAll (upF φ kv.2 d) ps)).gowners := by
    refine List.mem_filter.mpr ⟨hq, ?_⟩
    rw [hQcs, hqk]
    exact bne_iff_ne.mpr (by omega)
  exact List.any_eq_true.mpr ⟨q, hb.gow q hqT, hqs⟩

/-- **M3w**: a valid source pinned by `pinsW` and by `ps` (pins below the top) gives a valid piece pinned by `ps`. -/
theorem piece_of_src (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) (ps : List NodeId)
    (hps : ∀ p ∈ ps, p.step ≤ (n : Int))
    (hvK : isValid (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) = true) :
    isValid (filterAll (upF φ kv.2 d) ps) = true := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  -- the pinned source `K` and the filtered source `F`
  have cK := filt_ctx φ hbd n kv hok (LineUnion.pinsW φ n d kv.1 ++ ps) hvK
  have cF := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hbK := KernelIff.below_filterAll_self kv.2 hnd (LineUnion.pinsW φ n d kv.1 ++ ps)
  have pinK : ∀ q ∈ (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).gowners,
      ∀ r ∈ LineUnion.pinsW φ n d kv.1 ++ ps, q.id.step = r.step → q.id = r :=
    fun q hq r hr hs => LineUnion.gowner_pinned kv.2 _ q hq r hr hs
  have hbFK : Below (filterAll kv.2 (reqOf φ d)) (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) :=
    below_filterAll cK.pc.ker hbK (reqOf φ d) (fun r hr q hq hs =>
      pinK q hq r (List.mem_append_left _ (reqs_sub_pinsW φ n d kv.1 r hr)) hs)
  have hKcs : (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).current_step = (n : Int) + 1 := by
    rw [(pruned_filterAll _ _).step_eq, hcs]
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by
    rw [(pruned_filterAll _ _).step_eq, hcs]
  have hdK : d.step = (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).current_step := by rw [hKcs, ← hcs, hdst]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  -- `K` skips no window
  have hskK : skipsWindow (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) d (isProhibited φ) = false := by
    cases hsk : skipsWindow (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) d (isProhibited φ) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨pid, hpid, hforb⟩ := List.any_eq_true.mp hsk
      cases hskF : skipsWindow (filterAll kv.2 (reqOf φ d)) d (isProhibited φ) with
      | false =>
        have : skipsWindow (filterAll kv.2 (reqOf φ d)) d (isProhibited φ) = true :=
          List.any_eq_true.mpr ⟨pid, UpMono.shiftRowIds_mono hbFK d pid hpid, hforb⟩
        rw [hskF] at this; exact absurd this (by decide)
      | true =>
        -- the candidate comes from a node `p` at step `n` whose parent is `L1 = 0`, but `L1 = 1` is pinned
        have hpos : 0 < (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).current_step := by omega
        obtain ⟨p, hp, hpp⟩ : ∃ p ∈ newParents (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)),
            shiftPid p d = pid := by
          unfold shiftRowIds at hpid; rw [if_pos hpos] at hpid
          exact List.mem_map.mp ((mem_dedupPids _ _).mp hpid)
        have hpl : p ∈ ((filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).line
            ((filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).current_step - 1)).map (·.id) := by
          unfold newParents at hp; rw [if_pos hpos] at hp; exact hp
        obtain ⟨np, hnpm, hnpid⟩ := Parents.mem_nodes_of_mem_line _ _ p hpl
        rw [← hpp] at hforb
        have hds : d.step = (n : Int) + 1 := by rw [hdK, hKcs]
        have hpar : p.parent_id = some ⟨(n : Int) - 1, 0⟩ := by
          unfold isProhibited shiftPid at hforb
          simp only [Bool.and_eq_true, beq_iff_eq] at hforb
          rw [hforb.2, hds, show (n : Int) + 1 - 2 = (n : Int) - 1 by omega]
        have hnp : (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).node? p = some np := by
          rw [← hnpid]; exact node?_of_mem cK.pc.nd np hnpm
        -- `p` has a parent (it is not a root: its parent id is set)
        have hpars : np.parents ≠ [] := by
          rcases ((isValidNode_iff _ np).mp (cK.pc.ker.valid p np hnp)).2.1 with hr | hr
          · rw [hnpid, hpar] at hr; exact absurd hr (by simp)
          · exact hr
        obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hpars
        have hcid : some c.id = p.parent_id := by rw [← hnpid]; exact cK.rc.pmp np hnpm c hc
        rw [hpar] at hcid
        obtain ⟨_, nc, hnc, _⟩ := cK.pc.ker.linkP p np hnp c hc
        have hcg := cK.pc.ker.gow c nc hnc
        have hL1 := pinK c hcg ⟨(n : Int) - 1, 1⟩
          (List.mem_append_left _ (l1_mem_pinsW φ n kv hkv d hskF))
          (by rw [Option.some.inj hcid])
        rw [Option.some.inj hcid] at hL1
        exact absurd (congrArg NodeId.index hL1) (by simp)
  -- `up K` is `addNode K`: a valid kernel
  have hsoK : Ownership.SelfOwned (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) :=
    SelfOwn.SelfOwned_of_OOS _ hvK cK.rc.oos cK.rc.snn cK.rc.below
  have hposK : 0 < (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).current_step := by omega
  have hkA : Kernel (addNode (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) d "" (isProhibited φ)) := by
    have := KernelUp.kernel_up d "" (isProhibited φ) cK.pc.ker hdK cK.rc.below hposK hsoK cK.rc.oos cK.rc.ownb
      hvK hskK
    unfold up at this; rw [if_pos hvK, hskK, if_neg (by decide)] at this; exact this
  have hvA : isValid (addNode (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) d "" (isProhibited φ)) = true := by
    unfold isValid
    refine List.all_eq_true.mpr (fun k hk => ?_)
    have hk0 := mem_intRange_lower hk
    have hk1 := mem_intRange_upper hk
    rw [addNode_current, hKcs] at hk1
    rw [addNode_gowners]
    by_cases hkn : k ≤ (n : Int)
    · have hkK : k ∈ intRange 0 ((filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).current_step - 1) :=
        mem_intRange_zero k _ hk0 (by rw [hKcs]; omega)
      obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvK k hkK)
      exact List.any_eq_true.mpr ⟨q, List.mem_append_left _ hq, hqs⟩
    · -- the new row: a node of `K` at step `n` shifts to an allowed identifier
      have hnK : (n : Int) ∈ intRange 0 ((filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)).current_step - 1) :=
        mem_intRange_zero _ _ (by omega) (by rw [hKcs]; omega)
      obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvK _ hnK)
      obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cK.pc.ker.gn q hq)
      have hqn : q ∈ newParents (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) := by
        unfold newParents; rw [if_pos hposK]
        have := Threaded.mem_line_of_node? _ q nq hnq
        rw [hKcs, show (n : Int) + 1 - 1 = (n : Int) by omega]
        rwa [eq_of_beq hqs] at this
      have hf : isProhibited φ (shiftPid q d) = false := by
        cases e : isProhibited φ (shiftPid q d) with
        | false => rfl
        | true =>
          have : skipsWindow (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) d (isProhibited φ) = true := by
            refine List.any_eq_true.mpr ⟨shiftPid q d, ?_, e⟩
            unfold shiftRowIds; rw [if_pos hposK]
            exact (mem_dedupPids _ _).mpr (List.mem_map_of_mem hqn)
          rw [hskK] at this; exact absurd this (by decide)
      have hrow := mem_newRowIds_of_mem_newParents _ d (isProhibited φ) q hposK hqn hf
      refine List.any_eq_true.mpr ⟨shiftPid q d, List.mem_append_right _ hrow, ?_⟩
      show ((shiftPid q d).id.step == k) = true
      have : (shiftPid q d).id = d := rfl
      rw [this, hdK, hKcs]
      exact beq_iff_eq.mpr (by omega)
  -- the piece sits above `addNode K`
  have hbA : Below (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ))
      (addNode (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) d "" (isProhibited φ)) :=
    UpMono.below_addNode hbFK d "" (isProhibited φ) hdF cF.rc.below cK.rc.below
  have hbP : Below (upF φ kv.2 d)
      (addNode (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps)) d "" (isProhibited φ)) := by
    rcases (upF_shape φ kv.2 d hv).2 with e | e
    · rw [e]; exact hbA
    · rw [e]; exact below_review hkA hbA
  refine isValid_filterAll_of_kernel hkA hvA hbP ps (fun r hr q hq hqs => ?_)
  rw [addNode_gowners] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact pinK q hq r (List.mem_append_right _ hr) hqs
  · exfalso
    have := KernelUp.row_step _ d (isProhibited φ) hdK q hq
    rw [hKcs] at this
    have := hps r hr
    omega

end AbsSatBin.GraphPath.Model.PieceBridge

/-- info: 'AbsSatBin.GraphPath.Model.PieceBridge.src_of_piece' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.PieceBridge.src_of_piece

/-- info: 'AbsSatBin.GraphPath.Model.PieceBridge.piece_of_src' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.PieceBridge.piece_of_src
