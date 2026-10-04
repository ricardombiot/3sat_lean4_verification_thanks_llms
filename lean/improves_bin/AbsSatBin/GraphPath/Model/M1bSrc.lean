-- lean/improves_bin/AbsSatBin/GraphPath/Model/M1bSrc.lean
import AbsSatBin.GraphPath.Model.M1Parts

/-!
# The truncated form of M1b: from the source to the piece (`docs/context/escalera_reader.md` §4.2ο.2)

Let `J` be a joined state of line `n+1`, `k = kv.1` one of its keys, `X = kv.2` the state of line `n` at `k` (the source
of the piece `P = upF X d`), and `K` the joined state pinned at `k` and at `ps`.

* **Step 1, `key_reqs`**: `K` respects the requirements of the key. A global owner of `K` owns a node of `k` at step `n`,
  which is pure, so it is a node of the piece, of the filtered source, and of `X`; and every node of a state of line
  `n` at a step of a requirement of its key names the requirement (`line_node_req`).
* **Step 2, `m1_of_src`**: `M1aAll ∧ M1bSrc ⇒ M1`. **`M1bSrc`** asks that the tables of the lower rows of `K` (entries up
  to step `n`) be tables of the source `X`. Then `K` without its top is a kernel below `X` that respects the pins of the
  piece (`pinsW`: the requirements of `d` and, if the filter skips a window, `L1 = 1`) and the pins of `ps` below the
  top. So `X` pinned there is valid, and M3w (`PieceBridge.piece_of_src`) lifts it to the piece.

`M1bSrc` is the part that the rest of the reduction (CoverSplit, one row lower) has to give.
-/

namespace AbsSatBin.GraphPath.Model.M1bSrc

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.M1Parts

variable (φ : Cnf) (hbd : Bounded φ)

/-- **M1b at the source**: the tables of the lower rows of the joined state pinned at a key are tables of the source
of that key (entries up to the key row). -/
def M1bSrc (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
    ∀ ps : List NodeId, isValid (filterAll kv'.2 (kv.1 :: ps)) = true →
      ∀ p np, (filterAll kv'.2 (kv.1 :: ps)).node? p = some np → p.id.step < (n : Int) →
        ∃ nX, kv.2.node? p = some nX ∧ ∀ v ∈ np.owners, v.id.step ≤ (n : Int) → v ∈ nX.owners

include hbd

/-- A node of a state of line `m+1`, below its top, at the step of a requirement of its key, names the requirement. -/
theorem line_node_req (m : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (m + 1)) (q : PathNodeId)
    (nq : PNodeM) (hnq : kv'.2.node? q = some nq) (hqs : q.id.step < (m : Int) + 1) (r : NodeId)
    (hr : r ∈ reqOf φ kv'.1) (hs : q.id.step = r.step) : q.id = r := by
  have hkv'' := hkv'
  rw [line_succ] at hkv''
  obtain ⟨kv, hkv, hd, hv, n1, hn1⟩ := (src_pureAdvance φ (line φ m) kv' hkv'').1 q nq hnq
  obtain ⟨hok, hdst, hcs, _, hvF, _⟩ := src_ctx φ hbd m kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd m kv hok (reqOf φ kv'.1) hvF
  obtain ⟨nF, hnF, _⟩ := upF_old φ kv.2 kv'.1 hdst c hv q n1 hn1 (by rw [hcs]; exact hqs)
  exact LineUnion.pinned_entry φ kv.2 kv'.1 q (c.pc.ker.gow q nF hnF) r hr hs

/-- A node of the joined state pinned at a key, up to the key row, is a node of the piece and of the filtered source.
It owns a node of the key at step `n`, which is pure. -/
theorem node_in_piece (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (kv : NodeId × GPathM)
    (hkv : kv ∈ line φ n) (hd : kv'.1 ∈ sonsOfMap φ kv.1) (hvP : isValid (upF φ kv.2 kv'.1) = true)
    (ps : List NodeId) (hvK : isValid (filterAll kv'.2 (kv.1 :: ps)) = true)
    (q : PathNodeId) (nq : PNodeM) (hnq : (filterAll kv'.2 (kv.1 :: ps)).node? q = some nq)
    (hqs : q.id.step ≤ (n : Int)) :
    (∃ nP, (upF φ kv.2 kv'.1).node? q = some nP) ∧ ∃ nF, (filterAll kv.2 (reqOf φ kv'.1)).node? q = some nF := by
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hkn : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 ((lineOk φ n).2 kv hkv).onMap
  have cK := filt_ctx φ hbd _ kv' hok' (kv.1 :: ps) hvK
  have hbJK := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') (kv.1 :: ps)
  have hKcs : (filterAll kv'.2 (kv.1 :: ps)).current_step = (n : Int) + 2 := by rw [← hbJK.step, hcs']
  obtain ⟨x, hx, hxs⟩ := AmbTriCore.entry_at cK q nq hnq (n : Int) (by omega) (by rw [hKcs]; omega)
  have hxk : x.id = kv.1 := LineUnion.gowner_pinned kv'.2 _ x (cK.pc.ker.own q nq hnq x hx) kv.1
    List.mem_cons_self (by rw [hxs, hkn])
  obtain ⟨nx, hnx⟩ := cK.pc.ker.isNode_owner q nq hnq x hx
  have hqx := cK.pc.ker.sym q nq x nx hnq hnx hx
  obtain ⟨nxJ, hnxJ, hoJ, _, _⟩ := hbJK.node x nx hnx
  obtain ⟨nPx, hnPx, hoP, _, _⟩ := pure_node φ n kv' hkv' kv x nxJ hnxJ (pure_mid φ hbd n kv' kv hkv x hxs hxk)
  have pcP := piece_pinCtx φ hbd n kv hkv kv'.1 hd hvP
  obtain ⟨nPq, hnPq⟩ := pcP.ker.isNode_owner x nPx hnPx q (hoP q (hoJ q hqx))
  obtain ⟨_, hdst, hcs, _, hvF, _⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvP
  have cF := filt_ctx φ hbd n kv ((lineOk φ n).2 kv hkv) (reqOf φ kv'.1) hvF
  obtain ⟨nF, hnF, _⟩ := upF_old φ kv.2 kv'.1 hdst cF hvP q nPq hnPq (by rw [hcs]; omega)
  exact ⟨⟨nPq, hnPq⟩, nF, hnF⟩

/-- **Step 1**: the joined state pinned at a key respects the requirements of the key. -/
theorem key_reqs (n : Nat) (hn1 : 1 ≤ n) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1))
    (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (hd : kv'.1 ∈ sonsOfMap φ kv.1)
    (hvP : isValid (upF φ kv.2 kv'.1) = true) (ps : List NodeId) (hvK : isValid (filterAll kv'.2 (kv.1 :: ps)) = true) :
    ∀ q ∈ (filterAll kv'.2 (kv.1 :: ps)).gowners, ∀ r ∈ reqOf φ kv.1, q.id.step = r.step → q.id = r := by
  intro q hq r hr hs
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have cK := filt_ctx φ hbd _ kv' hok' (kv.1 :: ps) hvK
  have hkn : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 ((lineOk φ n).2 kv hkv).onMap
  have hrb := reqOf_backward φ hbd kv.1 r hr
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cK.pc.ker.gn q hq)
  obtain ⟨_, nF, hnF⟩ := node_in_piece φ hbd n kv' hkv' kv hkv hd hvP ps hvK q nq hnq (by omega)
  obtain ⟨_, _, _, _, _, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvP
  obtain ⟨nX, hnX, _, _, _⟩ := (KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)).node q nF hnF
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact line_node_req φ hbd m kv hkv q nX hnX (by push_cast at hkn ⊢; omega) r hr hs

/-- A state of line `n` carries the context of a pin. -/
theorem line_pinCtx (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) : KernelSplit.PinCtx kv.2 := by
  have hok := (lineOk φ n).2 kv hkv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd _ hok.reach
  have cm := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) _
    (Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach) hreach
  exact ⟨KernelUp.kernel_reachable (reqOf φ) (isProhibited φ) _ hreach hok.valid, cm.nodup, cm.oos, cm.shape.pbelow,
    KernelSplit.SAbove_reachable (reqOf φ) (isProhibited φ) _ hreach, cm.snn, cm.below⟩

set_option maxHeartbeats 1000000 in
/-- **Step 2: `M1aAll ∧ M1bSrc ⇒ M1`.** -/
theorem m1_of_src (n : Nat) (hn1 : 1 ≤ n) (ha : M1aAll φ n) (hsrc : M1bSrc φ n) : FExtInd.M1 φ n := by
  intro kv' hkv' ps hv
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have cG := filt_ctx φ hbd _ kv' hok' ps hv
  have hbG := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') ps
  -- a live key, and its pin
  have hnmem : (n : Int) ∈ intRange 0 ((filterAll kv'.2 ps).current_step - 1) :=
    mem_intRange_zero _ _ (by omega) (by rw [← hbG.step, hcs']; omega)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv _ hnmem)
  have hqn : q.id.step = (n : Int) := eq_of_beq hqs
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cG.pc.ker.gn q hq)
  obtain ⟨nJ, hnJ, _, _, _⟩ := hbG.node q nq hnq
  obtain ⟨kv, hkv, hd, hvP, hk, _⟩ := PieceJoin.mid_one_source φ hbd n kv' hkv' q nJ hnJ hqn
  have hvK := ha kv' hkv' ps hv q hq hqn
  rw [hk] at hvK
  -- the contexts
  have hok := (lineOk φ n).2 kv hkv
  have hkn : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 hok.onMap
  have cK := filt_ctx φ hbd _ kv' hok' (kv.1 :: ps) hvK
  have hbJK := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') (kv.1 :: ps)
  have hKcs : (filterAll kv'.2 (kv.1 :: ps)).current_step = (n : Int) + 2 := by rw [← hbJK.step, hcs']
  obtain ⟨_, hdst, hXcs, _, hvF, hndX⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvP
  have cF := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hbXF := KernelIff.below_filterAll_self kv.2 hndX (reqOf φ kv'.1)
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by rw [← hbXF.step, hXcs]
  have pcX := line_pinCtx φ hbd n kv hkv
  have pcP := piece_pinCtx φ hbd n kv hkv kv'.1 hd hvP
  -- the pinned state without its top
  let K := filterAll kv'.2 (kv.1 :: ps)
  have hkT := Trunc.kernel_trunc cK.pc.ker cK.pc.pb cK.pc.sa cK.pc.below
  have hTcs : (Trunc.trunc K).current_step = (n : Int) + 1 := by
    show K.current_step - 1 = _; rw [hKcs]; omega
  -- every node of `K` up to the key row is a node of the source, with its entries up to the key row
  have toX : ∀ p np, K.node? p = some np → p.id.step ≤ (n : Int) →
      ∃ nX, kv.2.node? p = some nX ∧ ∀ v ∈ np.owners, v.id.step ≤ (n : Int) → v ∈ nX.owners := by
    intro p np hnp hps
    by_cases hlow : p.id.step < (n : Int)
    · exact hsrc kv' hkv' kv hkv hd hvP ps hvK p np hnp hlow
    · -- the key row: the node is pure, its table is its table in the piece
      have hpn : p.id.step = (n : Int) := by omega
      have hpk : p.id = kv.1 := LineUnion.gowner_pinned kv'.2 _ p (cK.pc.ker.gow p np hnp) kv.1
        List.mem_cons_self (by rw [hpn, hkn])
      obtain ⟨nJp, hnJp, hoJp, _, _⟩ := hbJK.node p np hnp
      obtain ⟨nPp, hnPp, hoPp, _, _⟩ := pure_node φ n kv' hkv' kv p nJp hnJp (pure_mid φ hbd n kv' kv hkv p hpn hpk)
      obtain ⟨nF, hnF, hoF⟩ := upF_old φ kv.2 kv'.1 hdst cF hvP p nPp hnPp (by rw [hXcs]; omega)
      obtain ⟨nX, hnX, hoX, _, _⟩ := hbXF.node p nF hnF
      exact ⟨nX, hnX, fun v hv hvs => hoX v (hoF v (hoPp v (hoJp v hv)) (by rw [hXcs]; omega))⟩
  -- (B) the truncation lies below the source
  have hbXT : Below kv.2 (Trunc.trunc K) := by
    refine ⟨by rw [hTcs, hXcs], fun z hz => ?_, fun p n' hn' => ?_⟩
    · obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (hkT.gn z hz)
      obtain ⟨nk, hnk, hzs, rfl⟩ := Trunc.trunc_node?_some K z nz hnz
      have hr := CertFix.step_range cK.pc z nk hnk
      rw [hKcs] at hr hzs
      obtain ⟨nX, hnX, _⟩ := toX z nk hnk (by omega)
      exact pcX.ker.gow z nX hnX
    · obtain ⟨np, hnp, hps, rfl⟩ := Trunc.trunc_node?_some K p n' hn'
      have hr := CertFix.step_range cK.pc p np hnp
      rw [hKcs] at hr hps
      obtain ⟨nX, hnX, hoX⟩ := toX p np hnp (by omega)
      have hnpid : np.id = p := node?_id_eq _ p np hnp
      have ownX : ∀ v ∈ np.owners, v.id.step ≠ (n : Int) + 1 → v ∈ nX.owners := by
        intro v hv hvs
        have hvb := cK.rc.ownb np (List.mem_of_find?_eq_some hnp) v hv
        rw [hKcs] at hvb
        exact hoX v hv (by omega)
      refine ⟨nX, hnX, fun v hv => ?_, fun c hc => ?_, fun c hc => ?_⟩
      · obtain ⟨hv, hvs⟩ := (Trunc.mem_cutTop_owners _ _ v).mp hv
        rw [hKcs] at hvs
        exact ownX v hv (by omega)
      · obtain ⟨hco, nc, hnc, _⟩ := cK.pc.ker.linkP p np hnp c hc
        have hcs : c.id.step = p.id.step - 1 := by
          have := cK.pc.pb np (List.mem_of_find?_eq_some hnp) c hc; rw [hnpid] at this; exact this
        have hc0 : 0 ≤ c.id.step := by
          have := cK.pc.snn nc (List.mem_of_find?_eq_some hnc); rw [node?_id_eq _ c nc hnc] at this; exact this
        exact (KernelSplit.parent_of_owner pcX p nX hnX (by omega) c (ownX c hco (by omega)) hcs).1
      · obtain ⟨hc, hcs⟩ := (Trunc.mem_cutTop_sons _ _ c).mp hc
        rw [hKcs] at hcs
        obtain ⟨hco, _⟩ := cK.pc.ker.linkS p np hnp c hc
        have hcs' : c.id.step = p.id.step + 1 := by
          have := cK.pc.sa np (List.mem_of_find?_eq_some hnp) c hc; rw [hnpid] at this; exact this
        exact (KernelSplit.son_of_owner pcX p nX hnX (by rw [hXcs]; omega) c (ownX c hco (by omega)) hcs').1
  -- (C) the truncation respects the pins of the piece and the pins of `ps` below the top
  let psl := ps.filter (fun m => decide (m.step ≤ (n : Int)))
  have hgowT : ∀ z ∈ (Trunc.trunc K).gowners, z ∈ K.gowners ∧ z.id.step ≠ (n : Int) + 1 := by
    intro z hz
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hz
    refine ⟨h1, ?_⟩
    have : (z.id.step != K.current_step - 1) = true := h2
    rw [hKcs] at this
    intro e
    rw [e] at this
    exact bne_iff_ne.mp this (by omega)
  have pins : ∀ r ∈ LineUnion.pinsW φ n kv'.1 kv.1 ++ psl, ∀ z ∈ (Trunc.trunc K).gowners,
      z.id.step = r.step → z.id = r := by
    intro r hr z hz hzs
    obtain ⟨hzK, hzt⟩ := hgowT z hz
    obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (cK.pc.ker.gn z hzK)
    have hzr := CertFix.step_range cK.pc z nz hnz
    rw [hKcs] at hzr
    obtain ⟨⟨nPz, hnPz⟩, nFz, hnFz⟩ := node_in_piece φ hbd n kv' hkv' kv hkv hd hvP ps hvK z nz hnz (by omega)
    rcases List.mem_append.mp hr with hr | hr
    · have hr' : r ∈ reqOf φ kv'.1 ∨ (r = ⟨(n : Int) - 1, 1⟩ ∧
          skipsWindow (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 (isProhibited φ) = true) := by
        unfold LineUnion.pinsW at hr
        cases hc : (line φ n).any (fun kv₂ => kv₂.1 == kv.1 && skipsWindow (filterAll kv₂.2 (reqOf φ kv'.1)) kv'.1
            (isProhibited φ)) <;> rw [hc] at hr
        · rw [if_neg (by decide)] at hr; exact Or.inl hr
        · rw [if_pos rfl] at hr
          rcases List.mem_append.mp hr with hr | hr
          · exact Or.inl hr
          · refine Or.inr ⟨List.mem_singleton.mp hr, ?_⟩
            obtain ⟨kv₂, hkv₂, h₂⟩ := List.any_eq_true.mp hc
            simp only [Bool.and_eq_true, beq_iff_eq] at h₂
            have he : kv₂ = kv := key_inj _ (lineOk φ n).1 kv₂ hkv₂ kv hkv h₂.1
            rw [he] at h₂; exact h₂.2
      rcases hr' with hr' | ⟨rfl, hsk⟩
      · exact LineUnion.pinned_entry φ kv.2 kv'.1 z (cF.pc.ker.gow z nFz hnFz) r hr' hzs
      · obtain ⟨_, _, _, hG, hE⟩ := StatePiece.skip_window φ hbd n hn1 kv hkv kv'.1 hd hvP hsk
        obtain ⟨e, he, hed⟩ := hE z nPz (by rw [hG] at hnPz; exact hnPz)
          (by rw [hFcs, hzs]; show (n : Int) - 1 < (n : Int) + 1; omega) nFz hnFz
        have hes : e.id.step = nFz.id.id.step := by rw [node?_id_eq _ z nFz hnFz, hed, hzs]
        have := cF.pc.oos nFz (List.mem_of_find?_eq_some hnFz) e he hes
        rw [node?_id_eq _ z nFz hnFz] at this
        rw [← this, hed]
    · exact LineUnion.gowner_pinned kv'.2 _ z hzK r (List.mem_cons_of_mem _ (List.mem_filter.mp hr).1) hzs
  -- (D) the source pinned there is valid
  have hvT : isValid (Trunc.trunc K) = true := by
    unfold isValid
    refine List.all_eq_true.mpr (fun k hk' => ?_)
    have hk0 := mem_intRange_lower hk'
    have hk1 := mem_intRange_upper hk'
    rw [hTcs] at hk1
    have hkK : k ∈ intRange 0 (K.current_step - 1) := mem_intRange_zero k _ hk0 (by rw [hKcs]; omega)
    obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvK k hkK)
    have hzk : z.id.step = k := eq_of_beq hzs
    refine List.any_eq_true.mpr ⟨z, List.mem_filter.mpr ⟨hz, ?_⟩, hzs⟩
    show (z.id.step != K.current_step - 1) = true
    rw [hKcs, hzk]
    exact bne_iff_ne.mpr (by omega)
  have hvX := isValid_filterAll_of_kernel hkT hvT hbXT _ pins
  -- (E) M3w: the piece pinned below the top
  have hvPm := PieceBridge.piece_of_src φ hbd n kv hkv kv'.1 hd hvP psl
    (fun p hp => of_decide_eq_true (List.mem_filter.mp hp).2) hvX
  -- (F) the pins above the key row name the top
  have topG := FExtInd.top_unique φ hbd (n + 1) kv' hkv' _ cG hbG
  obtain ⟨h, hh, hg⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hvP
  have heq : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hh kv' hkv' rfl
  have hbJP : Below kv'.2 (upF φ kv.2 kv'.1) := by
    rw [← heq]; exact PieceFilter.below_of_grown hg
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvP
  have cQ := filt_ctx φ hbd _ _ hP psl hvPm
  have hbQ := PieceFilter.below_trans hbJP (KernelIff.below_filterAll_self _ (FExtInd.nodup_ok φ hbd _ _ hP) psl)
  have hQcs : (filterAll (upF φ kv.2 kv'.1) psl).current_step = (n : Int) + 2 := by rw [← hbQ.step, hcs']
  have hbQP := KernelIff.below_filterAll_self _ (FExtInd.nodup_ok φ hbd _ _ hP) psl
  refine ⟨kv, hkv, hd, hvP, isValid_filterAll_of_kernel cQ.pc.ker hvPm hbQP ps (fun r hr z hz hzs => ?_)⟩
  by_cases hrn : r.step ≤ (n : Int)
  · exact LineUnion.gowner_pinned _ _ z hz r (List.mem_filter.mpr ⟨hr, decide_eq_true hrn⟩) hzs
  · obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (cQ.pc.ker.gn z hz)
    have hzr := CertFix.step_range cQ.pc z nz hnz
    rw [hQcs] at hzr
    have hzt : z.id.step = (n : Int) + 1 := by omega
    have hz1 : z.id = kv'.1 := FExtInd.top_unique φ hbd (n + 1) kv' hkv' _ cQ hbQ z hz (by rw [hzt]; push_cast; rfl)
    have hrmem : r.step ∈ intRange 0 ((filterAll kv'.2 ps).current_step - 1) :=
      mem_intRange_zero _ _ (by omega) (by rw [← hbG.step, hcs']; omega)
    obtain ⟨g0, hg0, hg0s⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv _ hrmem)
    have e1 := LineUnion.gowner_pinned kv'.2 ps g0 hg0 r hr (eq_of_beq hg0s)
    have e2 := topG g0 hg0 (by rw [eq_of_beq hg0s]; push_cast; omega)
    rw [hz1, ← e2, e1]

/-- **The reader decides `φ` under `M1aAll` and `M1bSrc` at every join.** -/
theorem readerVerdictW_iff_of_src
    (hA : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1aAll φ n)
    (hS : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1bSrc φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  FExtInd.readerVerdictW_iff_of_m1 φ hbd (fun n h1 hn => m1_of_src φ hbd n h1 (hA n h1 hn) (hS n h1 hn))

end AbsSatBin.GraphPath.Model.M1bSrc

/-- info: 'AbsSatBin.GraphPath.Model.M1bSrc.readerVerdictW_iff_of_src' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.M1bSrc.readerVerdictW_iff_of_src

/-- info: 'AbsSatBin.GraphPath.Model.M1bSrc.key_reqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.M1bSrc.key_reqs
