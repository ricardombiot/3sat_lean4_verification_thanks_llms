-- lean/improves_bin/AbsSatBin/GraphPath/Model/FiltCert.lean
import AbsSatBin.GraphPath.Model.FilterUnion
import AbsSatBin.GraphPath.Model.StateLine

/-!
# Certificates of the filtered states: the invariant that replaces `MapCert`

Measured (`julia/improves_bin/test_3sat/probes/certj_probe.jl`, `docs/context/ambfar.md` §4.2κ): **`MapCert` is false
on a joined state** — in `clause_mix.cnf` at step 26 a clique `Q` has witnesses owning `Q` and a node `25:0`, but no
chain goes through `Q` and `25:0`. So `PieceLocal` is false too. The constraint `R` of `MapCert` asks only the
witnesses to own `R`; the machine applies a constraint by filtering, and then every node owns it. With the
constraint applied as a filter no failure is known (`fcert_probe.jl`, `fcert_any_probe.jl`).

* **`FCert g`**: every valid filter of `g` by pins inside its steps has `CertClique`.
* **`fCert_of_mapCert`**: `MapCert` gives `FCert` (base, and the pieces of line 0).
* **`PieceLocalF n`**: a clique with witnesses of a joined state of line `n+1` filtered by `R` is one of a piece
  filtered by `R` — `PieceLocal` with the constraint applied as a filter.
* **`fCert_join`**: under `PieceLocalF`, the join keeps `FCert`. The certificate of the filtered piece climbs to the
  joined state, passes the pins, and survives the filter.
* **`readerVerdictW_iff_of_fCert`**: `FCert` on the machine's last line makes the reader decide.
* **`readerVerdictW_iff_of_pieceLocalF`**: the reader decides under `PieceLocalF` at every join and `PieceF` (a
  piece of a state with `FCert` has `FCert`) at every step.
* **The piece** (`cert_piece_low`): a clique with witnesses of a filtered piece below its top lies on a certificate —
  proved from `FCert` of the source: the truncated filtered piece sits below the source pinned by `pinsW` and the pins
  below the top (`FilterUnion.piece_pinned_below`), the source's certificate passes the requirements and `L1 = 1`,
  climbs through `up` and survives the pins.
* **`pieceF_of_topParent`**: with a member `w` at the top, `PieceF` follows from `TopParent` (some parent of `w` takes
  its place in the clique with witnesses; with a merge `w` has two). **`readerVerdictW_iff_of_topParent`**: the reader
  decides under `PieceLocalF` and `TopParent`.
-/

namespace AbsSatBin.GraphPath.Model.FiltCert

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri (Clique)
open AbsSatBin.GraphPath.Model.MapCert (MapCert)
open AbsSatBin.GraphPath.Model.CertDescent (Wit)
open AbsSatBin.GraphPath.Model.CertFix (CertThrough)
open AbsSatBin.GraphPath.Model.CertInvariant (CertClique)

/-- **Certificates of the filtered states**: every valid filter by pins inside the steps has `CertClique`. -/
def FCert (g : GPathM) : Prop :=
  ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < g.current_step) → isValid (filterAll g R) = true →
    CertClique (filterAll g R)

/-- A chain of a filtered state passes its pins. -/
theorem chain_pins (X : GPathM) (R : List NodeId) (sel : Int → PathNodeId) (hs : ChainSound (filterAll X R) sel) :
    ∀ r ∈ R, 0 ≤ r.step → r.step < X.current_step → (sel r.step).id = r := by
  intro r hr h0 h1
  have hcs : (filterAll X R).current_step = X.current_step := (pruned_filterAll X R).step_eq
  have h1' : r.step < (filterAll X R).current_step := by rw [hcs]; exact h1
  exact LineUnion.gowner_pinned X R _ (hs.chain.2.2 r.step h0 h1') r hr (hs.chain.1.1 r.step h0 h1').2

/-- **A certificate of a filtered state climbs to the same filter of a state it grows into.** -/
theorem certThrough_grown (X Y : GPathM) (hnd : NodupIds X) (hgr : Grown X Y) (R : List NodeId)
    (Q : List PathNodeId) (h : CertThrough (filterAll X R) Q) : CertThrough (filterAll Y R) Q := by
  obtain ⟨sel, hs, hon⟩ := h
  have hsX : ChainSound X sel :=
    ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self X hnd R)) sel hs
  refine ⟨sel, ChainSound_filterAll Y R sel (ChainSound_of_grown hgr sel hsX) (fun r hr h0 h1 => ?_), hon⟩
  exact chain_pins X R sel hs r hr h0 (by rw [← hgr.step_eq]; exact h1)

variable (φ : Cnf) (hbd : Bounded φ)
include hbd

/-- **`MapCert` gives `FCert`** on a state of the run. -/
theorem fCert_of_mapCert (k : Int) (kv : NodeId × GPathM) (hok : StateOk φ k kv) (hM : MapCert kv.2) :
    FCert kv.2 := by
  intro R hR hv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd _ hok.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach
  have c := filt_ctx φ hbd k kv hok R hv
  exact MapCert.certClique_of_mapCert (FilterUnion.mapCert_filter_pins kv.2 hnd R c.pc.ker hR hM)

omit hbd in
/-- **`PieceLocalF n`**: a clique with witnesses of a joined state of line `n+1` filtered by `R` is one of a piece
filtered by `R`. -/
def PieceLocalF (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < kv'.2.current_step) →
    isValid (filterAll kv'.2 R) = true → ∀ Q, Clique (filterAll kv'.2 R) Q → Wit (filterAll kv'.2 R) Q →
      ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 kv'.1) = true ∧
        isValid (filterAll (upF φ kv.2 kv'.1) R) = true ∧
        Clique (filterAll (upF φ kv.2 kv'.1) R) Q ∧ Wit (filterAll (upF φ kv.2 kv'.1) R) Q

/-- **The join keeps `FCert`** under `PieceLocalF`. -/
theorem fCert_join (n : Nat) (hPL : PieceLocalF φ n)
    (hP : ∀ kv ∈ line φ n, ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true → FCert (upF φ kv.2 d)) :
    ∀ kv' ∈ line φ (n + 1), FCert kv'.2 := by
  intro kv' hkv' R hR hv Q hQ hW
  obtain ⟨kv, hkv, hd, hvp, hvF, hQP, hWP⟩ := hPL kv' hkv' R hR hv Q hQ hW
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hvp
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  have hP' : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) :=
    StateOk_sent φ n kv ((lineOk φ n).2 kv hkv) kv'.1 hd hvp
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hP'.reach)
  have hRP : ∀ p ∈ R, 0 ≤ p.step ∧ p.step < (upF φ kv.2 kv'.1).current_step := by
    intro p hp
    have hcs : kv'.2.current_step = (upF φ kv.2 kv'.1).current_step := by rw [← he]; exact hgr.step_eq
    rw [← hcs]; exact hR p hp
  have hc := hP kv hkv kv'.1 hd hvp R hRP hvF Q hQP hWP
  rw [← he]
  exact certThrough_grown _ _ hndP hgr R Q hc

/-- **The reader decides `φ` when every state of the machine's last line has `FCert`.** -/
theorem readerVerdictW_iff_of_fCert (h0 : ∀ kv ∈ pureRun φ, FCert kv.2) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine CertFix.readerVerdictW_iff_of_certLink φ hbd (fun kv hkv hv => ?_)
  have c := AmbTriCore.aCtx_readPins φ hbd kv hkv [] _ OtherBitSem.ReadPins.start hv
  exact CertInvariant.certLink_of_certClique c (h0 kv hkv [] (fun _ h => absurd h List.not_mem_nil) hv)

omit hbd in
/-- **`PieceF n`**: every valid piece of a state of line `n` with `FCert` has `FCert`. -/
def PieceF (n : Nat) : Prop :=
  ∀ kv ∈ line φ n, FCert kv.2 → ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true → FCert (upF φ kv.2 d)

-- ============================================================
-- A piece: the clique below the top
-- ============================================================

section piece
variable (n : Nat)

omit hbd in
theorem reqOf_sub_pinsW (d k : NodeId) : ∀ r ∈ reqOf φ d, r ∈ LineUnion.pinsW φ n d k := by
  intro r hr
  unfold LineUnion.pinsW
  split
  · exact List.mem_append_left _ hr
  · exact hr

/-- **A clique with witnesses of a filtered piece, below its top, lies on a certificate** whose top node is the
extension of its node at step `n`. The truncated filtered piece sits below its source pinned by `pinsW` and the pins
below the top (`piece_pinned_below`); `FCert` of the source gives the certificate there, it passes the requirements
(and `L1 = 1` when the window is skipped, so its extension is allowed), climbs through `up`, and survives the pins. -/
theorem cert_piece_low (hn1 : 1 ≤ n) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) (hX : FCert kv.2)
    (ps : List NodeId) (hps : ∀ p ∈ ps, 0 ≤ p.step ∧ p.step < (upF φ kv.2 d).current_step)
    (hvP : isValid (filterAll (upF φ kv.2 d) ps) = true)
    (Q : List PathNodeId) (hQ : Clique (filterAll (upF φ kv.2 d) ps) Q)
    (hW : Wit (filterAll (upF φ kv.2 d) ps) Q) (hlow : ∀ q ∈ Q, q.id.step ≤ n) :
    ∃ sel, ChainSound (filterAll (upF φ kv.2 d) ps) sel ∧ (∀ q ∈ Q, sel q.id.step = q) ∧
      sel ((n : Int) + 1) = shiftPid (sel n) d := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hP : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hPcs : (upF φ kv.2 d).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hP.reach)
  have cQ := filt_ctx φ hbd _ (d, upF φ kv.2 d) hP ps hvP
  have hQcs : (filterAll (upF φ kv.2 d) ps).current_step = (n : Int) + 2 := by
    rw [(pruned_filterAll _ ps).step_eq, hPcs]
  have hkT := Trunc.kernel_trunc cQ.pc.ker cQ.pc.pb cQ.pc.sa cQ.pc.below
  have hBT := FilterUnion.piece_pinned_below φ hbd n hn1 kv hkv d hd hv ps hvP
  have hTcs : (Trunc.trunc (filterAll (upF φ kv.2 d) ps)).current_step = (n : Int) + 1 := by
    show (filterAll (upF φ kv.2 d) ps).current_step - 1 = _
    rw [hQcs]; omega
  have hGcs := hBT.step.trans hTcs
  -- a node of the filtered piece below the top, in the truncation and in the pinned source
  have toT : ∀ p np, (filterAll (upF φ kv.2 d) ps).node? p = some np → p.id.step ≤ n →
      (Trunc.trunc (filterAll (upF φ kv.2 d) ps)).node? p =
        some (Trunc.cutTop ((filterAll (upF φ kv.2 d) ps).current_step - 1) np) :=
    fun p np hnp hps' => Trunc.trunc_node?_of _ p np hnp (by rw [hQcs]; omega)
  have toG : ∀ p np, (filterAll (upF φ kv.2 d) ps).node? p = some np → p.id.step ≤ n →
      ∃ nG, (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int))))).node? p
        = some nG ∧ ∀ v ∈ np.owners, v.id.step ≤ n → v ∈ nG.owners := by
    intro p np hnp hps'
    obtain ⟨nG, hnG, ho, _, _⟩ := hBT.node p _ (toT p np hnp hps')
    exact ⟨nG, hnG, fun v hv hvs => ho v ((Trunc.mem_cutTop_owners _ _ v).mpr ⟨hv, by rw [hQcs]; omega⟩)⟩
  have hQG : Clique (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int))))) Q :=
    fun p hp => by
      obtain ⟨np, hnp, hpQ⟩ := hQ p hp
      obtain ⟨nG, hnG, ho⟩ := toG p np hnp (hlow p hp)
      exact ⟨nG, hnG, fun s hs => ho s (hpQ s hs) (hlow s hs)⟩
  have hWG : Wit (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int))))) Q := by
    intro l h0 h1
    rw [hGcs] at h1
    obtain ⟨r, nr, hnr, hrs, hrQ⟩ := hW l h0 (by rw [hQcs]; omega)
    obtain ⟨nG, hnG, ho⟩ := toG r nr hnr (by omega)
    exact ⟨r, nG, hnG, hrs, fun s hs => ho s (hrQ s hs) (hlow s hs)⟩
  -- the pinned source is valid: every step has a witness, a global owner of the truncation
  have hvG : isValid (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int)))))
      = true := by
    unfold isValid
    refine List.all_eq_true.mpr (fun l hl => ?_)
    have h0 := mem_intRange_lower hl
    have h1 := mem_intRange_upper hl
    rw [hGcs] at h1
    obtain ⟨r, nr, hnr, hrs, _⟩ := hW l h0 (by rw [hQcs]; omega)
    have hrT := hkT.gow r _ (toT r nr hnr (by omega))
    exact List.any_eq_true.mpr ⟨r, hBT.gow r hrT, beq_iff_eq.mpr hrs⟩
  -- the pins of the source are inside its steps
  have hSr : ∀ p ∈ LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int))),
      0 ≤ p.step ∧ p.step < kv.2.current_step := by
    intro p hp
    rw [hcs]
    have hreq : ∀ r ∈ reqOf φ d, 0 ≤ r.step ∧ r.step < (n : Int) + 1 := fun r hr =>
      ⟨reqOf_nonneg φ hbd d r hr, by have := reqOf_backward φ hbd d r hr; rw [hdst, hcs] at this; exact this⟩
    rcases List.mem_append.mp hp with hp | hp
    · unfold LineUnion.pinsW at hp
      split at hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact hreq p hp
        · rw [List.mem_singleton.mp hp]
          exact ⟨by show (0 : Int) ≤ (n : Int) - 1; omega, by show (n : Int) - 1 < (n : Int) + 1; omega⟩
      · exact hreq p hp
    · obtain ⟨hp, hle⟩ := List.mem_filter.mp hp
      exact ⟨(hps p hp).1, by have := of_decide_eq_true hle; omega⟩
  -- the certificate of the pinned source
  obtain ⟨sel, hsG, hon⟩ := hX _ hSr hvG Q hQG hWG
  have hsX : ChainSound kv.2 sel :=
    ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self kv.2 hnd _)) sel hsG
  have hpS := chain_pins kv.2 _ sel hsG
  have hreqs : ∀ req ∈ reqOf φ d, 0 ≤ req.step → req.step < kv.2.current_step → (sel req.step).id = req :=
    fun req hr h0 h1 => hpS req (List.mem_append_left _ (reqOf_sub_pinsW φ n d kv.1 req hr)) h0 h1
  have hsF := ChainSound_filterAll kv.2 (reqOf φ d) sel hsX hreqs
  have hmokX : MachineOk kv.2 := ⟨by rw [hok.step]; omega, fun h => by rw [hok.step] at h; omega,
    fun _ => by rw [hok.par]; simp⟩
  have hmok : MachineOk (filterAll kv.2 (reqOf φ d)) := MachineOk_of_pruned (pruned_filterAll _ _) hmokX
  -- its extension is allowed
  have hpos : 0 < (filterAll kv.2 (reqOf φ d)).current_step := by omega
  have hf : isProhibited φ (extendPid (filterAll kv.2 (reqOf φ d)) d sel) = false := by
    by_cases hsk : skipsWindow (filterAll kv.2 (reqOf φ d)) d (isProhibited φ) = true
    · obtain ⟨_, hdid, _, _, _⟩ := StatePiece.skip_window φ hbd n hn1 kv hkv d hd hv hsk
      have hin : (⟨(n : Int) - 1, 1⟩ : NodeId) ∈ LineUnion.pinsW φ n d kv.1 := by
        unfold LineUnion.pinsW
        rw [if_pos (List.any_eq_true.mpr ⟨kv, hkv, (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr rfl, hsk⟩⟩)]
        exact List.mem_append_right _ List.mem_cons_self
      have h1 := hpS _ (List.mem_append_left _ hin) (by show (0 : Int) ≤ (n : Int) - 1; omega)
        (by rw [hcs]; show (n : Int) - 1 < (n : Int) + 1; omega)
      simp only at h1
      have hlink := hsF.chain.1.2 ((n : Int) - 1) (by omega) (by rw [hFcs]; omega)
      rw [show (n : Int) - 1 + 1 = n by omega] at hlink
      obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp (hsF.chain.1.1 n (by omega) (by rw [hFcs]; omega)).1
      rw [hnl] at hlink
      have hpm := c.rc.pmp nl (List.mem_of_find?_eq_some hnl) _ hlink
      rw [node?_id_eq _ _ nl hnl, h1] at hpm
      unfold extendPid; rw [if_pos hpos, hFcs, show (n : Int) + 1 - 1 = n by omega]
      unfold isProhibited shiftPid
      rw [← hpm, hdid]
      simp only [Bool.and_eq_false_iff]
      right
      show (some (⟨(n : Int) - 1, 1⟩ : NodeId) == some ⟨(n : Int) + 1 - 2, 0⟩) = false
      rw [show (n : Int) + 1 - 2 = n - 1 by omega]
      exact beq_eq_false_iff_ne.mpr (by intro h; cases h)
    · cases hfb : isProhibited φ (extendPid (filterAll kv.2 (reqOf φ d)) d sel) with
      | false => rfl
      | true => exact absurd (List.any_eq_true.mpr ⟨_, extendPid_mem_shiftRowIds _ d sel hsF.chain.1, hfb⟩) hsk
  -- it climbs through `up`
  have hsP : ChainSound (upF φ kv.2 d) (extend (filterAll kv.2 (reqOf φ d)) d sel) :=
    ChainSound_upFiltering kv.2 (reqOf φ d) d "" (isProhibited φ) hvF hdF c.pc.below hmok sel hsX hreqs hf
  -- and survives the pins of the piece
  have hpsP : ∀ r ∈ ps, 0 ≤ r.step → r.step < (upF φ kv.2 d).current_step →
      (extend (filterAll kv.2 (reqOf φ d)) d sel r.step).id = r := by
    intro r hr h0 h1
    rw [hPcs] at h1
    by_cases hrt : r.step = (n : Int) + 1
    · obtain ⟨w, nw, hnw, hws, _⟩ := hW ((n : Int) + 1) (by omega) (by rw [hQcs]; omega)
      have hwr := LineUnion.gowner_pinned _ ps w (cQ.pc.ker.gow w nw hnw) r hr (by rw [hws, hrt])
      obtain ⟨nP, hnP, _, _, _⟩ := (KernelIff.below_filterAll_self _ hndP ps).node w nw hnw
      have hwd := mapId_of_mem_newRowIds _ _ _ w (upF_new φ kv.2 d hdst c hv w nP hnP (by rw [hws, hcs])).1
      rw [hrt, ← hFcs, extend_top, extendPid_mapId, ← hwd, hwr]
    · unfold extend
      rw [if_neg (by rw [hFcs]; exact hrt)]
      exact hpS r (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, decide_eq_true (by omega)⟩)) h0
        (by rw [hcs]; omega)
  refine ⟨extend (filterAll kv.2 (reqOf φ d)) d sel, ChainSound_filterAll _ ps _ hsP hpsP, fun q hq => ?_, ?_⟩
  · unfold extend
    rw [if_neg (by rw [hFcs]; have := hlow q hq; omega)]
    exact hon q hq
  · unfold extend
    rw [if_pos (by rw [hFcs]), if_neg (by rw [hFcs]; omega)]
    unfold extendPid
    rw [if_pos hpos, hFcs, show (n : Int) + 1 - 1 = n by omega]

/-- info: 'AbsSatBin.GraphPath.Model.FiltCert.cert_piece_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cert_piece_low

-- ============================================================
-- A piece: the clique with a member at the top
-- ============================================================

omit hbd in
/-- **A node with one parent hands its clique with witnesses to the parent** (in any kernel with the pin context).
`nbrP` puts every owner of `w` in the table of a parent; with one parent `cp`, `cp` owns all of `w`'s table, and
symmetry gives the rest: the members own `cp`, and a witness owns `w`, so `w` owns it, so `cp` owns it. -/
theorem single_parent {g : GPathM} (pc : KernelSplit.PinCtx g) (w : PathNodeId) (nw : PNodeM)
    (hnw : g.node? w = some nw) (hw1 : 1 ≤ w.id.step) (cp : PathNodeId) (hone : ∀ c' ∈ nw.parents, c' = cp)
    (Q0 : List PathNodeId) (hQ : Clique g (w :: Q0)) (hW : Wit g (w :: Q0)) :
    Clique g (cp :: Q0) ∧ Wit g (cp :: Q0) := by
  have hto : ∀ v ∈ nw.owners, ∃ nc, g.node? cp = some nc ∧ v ∈ nc.owners := by
    intro v hv
    obtain ⟨c', hc', nc, hnc, hvc⟩ := pc.ker.nbrP w nw hnw hw1 v hv
    rw [hone c' hc'] at hnc
    exact ⟨nc, hnc, hvc⟩
  obtain ⟨nw', hnw', hwall⟩ := hQ w List.mem_cons_self
  rw [hnw] at hnw'; cases hnw'
  obtain ⟨nc, hnc, _⟩ := hto w (TriPinCut.self_own_pc pc w nw hnw)
  have hcown : ∀ v ∈ nw.owners, v ∈ nc.owners := fun v hv => by
    obtain ⟨nc', hnc', h⟩ := hto v hv
    rw [hnc] at hnc'; cases hnc'; exact h
  refine ⟨fun p hp => ?_, fun l h0 h1 => ?_⟩
  · rcases List.mem_cons.mp hp with e | hp
    · rw [e]
      refine ⟨nc, hnc, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact TriPinCut.self_own_pc pc cp nc hnc
      · exact hcown s (hwall s (List.mem_cons_of_mem _ hs))
    · obtain ⟨np, hnp, hpall⟩ := hQ p (List.mem_cons_of_mem _ hp)
      refine ⟨np, hnp, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact pc.ker.sym cp nc p np hnc hnp (hcown p (hwall p (List.mem_cons_of_mem _ hp)))
      · exact hpall s (List.mem_cons_of_mem _ hs)
  · obtain ⟨r, nr, hnr, hrs, hrall⟩ := hW l h0 h1
    refine ⟨r, nr, hnr, hrs, fun s hs => ?_⟩
    rcases List.mem_cons.mp hs with e' | hs
    · rw [e']
      have hrw : r ∈ nw.owners := pc.ker.sym r nr w nw hnr hnw (hrall w List.mem_cons_self)
      exact pc.ker.sym cp nc r nr hnc hnr (hcown r hrw)
    · exact hrall s (List.mem_cons_of_mem _ hs)

/-- info: 'AbsSatBin.GraphPath.Model.FiltCert.single_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms single_parent

omit hbd in
/-- **`TopParent n`**: in a filtered piece of line `n+1`, a clique with witnesses with a member `w` at the top gives,
for some parent `c` of `w`, a clique with witnesses with `c` in place of `w`. With two parents (a merge) the members
below may split between them; the choice is the whole clique's. -/
def TopParent : Prop :=
  ∀ kv ∈ line φ n, ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true →
    ∀ ps : List NodeId, (∀ p ∈ ps, 0 ≤ p.step ∧ p.step < (upF φ kv.2 d).current_step) →
      isValid (filterAll (upF φ kv.2 d) ps) = true →
      ∀ w Q0, Clique (filterAll (upF φ kv.2 d) ps) (w :: Q0) → Wit (filterAll (upF φ kv.2 d) ps) (w :: Q0) →
        w.id.step = (n : Int) + 1 → (∀ q ∈ Q0, q.id.step ≤ n) →
        ∃ c nw, (filterAll (upF φ kv.2 d) ps).node? w = some nw ∧ c ∈ nw.parents ∧
          Clique (filterAll (upF φ kv.2 d) ps) (c :: Q0) ∧ Wit (filterAll (upF φ kv.2 d) ps) (c :: Q0)

omit hbd in
/-- **`TopMerge n`**: `TopParent` only where the top member comes from a merge (two different parents). -/
def TopMerge : Prop :=
  ∀ kv ∈ line φ n, ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true →
    ∀ ps : List NodeId, (∀ p ∈ ps, 0 ≤ p.step ∧ p.step < (upF φ kv.2 d).current_step) →
      isValid (filterAll (upF φ kv.2 d) ps) = true →
      ∀ w Q0, Clique (filterAll (upF φ kv.2 d) ps) (w :: Q0) → Wit (filterAll (upF φ kv.2 d) ps) (w :: Q0) →
        w.id.step = (n : Int) + 1 → (∀ q ∈ Q0, q.id.step ≤ n) →
        ∀ nw, (filterAll (upF φ kv.2 d) ps).node? w = some nw →
        (∃ c₁ ∈ nw.parents, ∃ c₂ ∈ nw.parents, c₁ ≠ c₂) →
        ∃ c ∈ nw.parents, Clique (filterAll (upF φ kv.2 d) ps) (c :: Q0) ∧ Wit (filterAll (upF φ kv.2 d) ps) (c :: Q0)

/-- **`TopParent` without a merge is proved**: it reduces to `TopMerge`. A top node has a parent (it is not the root
and it is valid); if all its parents are one node, `single_parent`. -/
theorem topParent_of_topMerge (hTM : TopMerge φ n) : TopParent φ n := by
  intro kv hkv d hd hv ps hps hvP w Q0 hQ hW hws hlow
  obtain ⟨hok, _, hcs, _, _, _⟩ := src_ctx φ hbd n kv hkv d hd hv
  have hP : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have cQ := filt_ctx φ hbd _ (d, upF φ kv.2 d) hP ps hvP
  obtain ⟨nw, hnw, _⟩ := hQ w List.mem_cons_self
  have hwmem := List.mem_of_find?_eq_some hnw
  have hwid : nw.id = w := node?_id_eq _ w nw hnw
  by_cases hm : ∃ c₁ ∈ nw.parents, ∃ c₂ ∈ nw.parents, c₁ ≠ c₂
  · obtain ⟨cp, hcp, hQc, hWc⟩ := hTM kv hkv d hd hv ps hps hvP w Q0 hQ hW hws hlow nw hnw hm
    exact ⟨cp, nw, hnw, hcp, hQc, hWc⟩
  · -- one parent
    have hnr : nw.id.parent_id ≠ none := cQ.rc.shape.notroot nw hwmem (by rw [hwid, hws]; omega)
    obtain ⟨cp, hcp⟩ : ∃ cp, cp ∈ nw.parents := by
      rcases ((Kernel.isValidNode_iff _ nw).mp (cQ.pc.ker.valid w nw hnw)).2.1 with h' | h'
      · exact absurd (Option.isNone_iff_eq_none.mp h') hnr
      · exact List.exists_mem_of_ne_nil _ h'
    have hone : ∀ c' ∈ nw.parents, c' = cp := by
      intro c' hc'
      by_cases e : c' = cp
      · exact e
      · exact absurd ⟨c', hc', cp, hcp, e⟩ hm
    obtain ⟨hQc, hWc⟩ := single_parent cQ.pc w nw hnw (by rw [hws]; omega) cp hone Q0 hQ hW
    exact ⟨cp, nw, hnw, hcp, hQc, hWc⟩

/-- info: 'AbsSatBin.GraphPath.Model.FiltCert.topParent_of_topMerge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topParent_of_topMerge

/-- **`PieceF` from `TopParent`.** Below the top, `cert_piece_low`. With a member `w` at the top (the only one: two
nodes of one step do not own each other), `TopParent` gives a parent `c`; the certificate through `c` and the members
below extends at the top by the shift of `c`, which is `w` (its id, parent and grandparent are those of `w`). -/
theorem pieceF_of_topParent (hn1 : 1 ≤ n) (hTP : TopParent φ n) : PieceF φ n := by
  intro kv hkv hX d hd hv ps hps hvP Q hQ hW
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hP : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hPcs : (upF φ kv.2 d).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hP.reach)
  have cQ := filt_ctx φ hbd _ (d, upF φ kv.2 d) hP ps hvP
  have hQcs : (filterAll (upF φ kv.2 d) ps).current_step = (n : Int) + 2 := by
    rw [(pruned_filterAll _ ps).step_eq, hPcs]
  by_cases htop : ∃ w ∈ Q, (n : Int) < w.id.step
  · obtain ⟨w, hwQ, hwn⟩ := htop
    obtain ⟨nw, hnw, hwown⟩ := hQ w hwQ
    have hwmem := List.mem_of_find?_eq_some hnw
    have hwid : nw.id = w := node?_id_eq _ w nw hnw
    have hws : w.id.step = (n : Int) + 1 := by
      have := (CertFix.step_range cQ.pc w nw hnw).2; rw [hQcs] at this; omega
    -- the members below the top
    have hsub : ∀ p ∈ w :: Q.filter (fun q => decide (q.id.step ≤ (n : Int))), p ∈ Q := by
      intro p hp
      rcases List.mem_cons.mp hp with e | hp
      · rw [e]; exact hwQ
      · exact (List.mem_filter.mp hp).1
    have hQw : Clique (filterAll (upF φ kv.2 d) ps) (w :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) :=
      fun p hp => by
        obtain ⟨np, hnp, ho⟩ := hQ p (hsub p hp)
        exact ⟨np, hnp, fun s hs => ho s (hsub s hs)⟩
    have hWw : Wit (filterAll (upF φ kv.2 d) ps) (w :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) := by
      intro l h0 h1
      obtain ⟨r, nr, hnr, hrs, ho⟩ := hW l h0 h1
      exact ⟨r, nr, hnr, hrs, fun s hs => ho s (hsub s hs)⟩
    obtain ⟨cp, nw', hnw', hcp, hQc, hWc⟩ := hTP kv hkv d hd hv ps hps hvP w _ hQw hWw hws
      (fun q hq => of_decide_eq_true (List.mem_filter.mp hq).2)
    rw [hnw] at hnw'; cases hnw'
    have hcps : cp.id.step = (n : Int) := by
      have := cQ.pc.pb nw hwmem cp hcp; rw [hwid, hws] at this; omega
    obtain ⟨sel, hs, hon, htopsel⟩ := cert_piece_low φ hbd n hn1 kv hkv d hd hv hX ps hps hvP _ hQc hWc
      (fun q hq => by
        rcases List.mem_cons.mp hq with e | hq
        · rw [e, hcps]; exact Int.le_refl _
        · exact of_decide_eq_true (List.mem_filter.mp hq).2)
    -- the shift of `cp` is `w`
    have hselc : sel n = cp := by rw [← hcps]; exact hon cp List.mem_cons_self
    obtain ⟨nP, hnP, _, _, _⟩ := (KernelIff.below_filterAll_self _ hndP ps).node w nw hnw
    have hwd := mapId_of_mem_newRowIds _ _ _ w (upF_new φ kv.2 d hdst c hv w nP hnP (by rw [hws, hcs])).1
    have hpar : some cp.id = w.parent_id := by
      have := cQ.rc.pmp nw hwmem cp hcp; rw [hwid] at this; exact this
    have hgpar : w.gparent_id = cp.parent_id := by
      have := cQ.rc.gpmp.1 nw hwmem cp hcp; rw [hwid] at this; exact this
    have hshift : shiftPid cp d = w := by
      unfold shiftPid
      revert hwd hpar hgpar
      cases w with
      | mk wi wp wg =>
        intro hwd hpar hgpar
        simp only at hwd hpar hgpar
        rw [hwd, ← hpar, hgpar]
    refine ⟨sel, hs, fun q hq => ?_⟩
    by_cases hqs : q.id.step ≤ (n : Int)
    · exact hon q (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hq, decide_eq_true hqs⟩))
    · -- a member at the top is `w`
      obtain ⟨nq, hnq, _⟩ := hQ q hq
      have hqs' : q.id.step = (n : Int) + 1 := by
        have := (CertFix.step_range cQ.pc q nq hnq).2; rw [hQcs] at this; omega
      have hqw : q = w := by
        have := cQ.pc.oos nw hwmem q (hwown q hq) (by rw [hwid, hqs', hws])
        rw [hwid] at this; exact this
      rw [hqw, hws, htopsel, hselc, hshift]
  · obtain ⟨sel, hs, hon, _⟩ := cert_piece_low φ hbd n hn1 kv hkv d hd hv hX ps hps hvP Q hQ hW
      (fun q hq => by
        have : ¬ (n : Int) < q.id.step := fun h => htop ⟨q, hq, h⟩
        omega)
    exact ⟨sel, hs, hon⟩

/-- info: 'AbsSatBin.GraphPath.Model.FiltCert.pieceF_of_topParent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pieceF_of_topParent
end piece

/-- **Every state of every line has `FCert`**, under `PieceLocalF` at every join and `PieceF` from line 1 on. -/
theorem fCert_line (hPL : ∀ n : Nat, (n : Int) + 1 < stepCount φ → PieceLocalF φ n)
    (hPF : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → PieceF φ n) :
    ∀ n : Nat, (n : Int) < stepCount φ → ∀ kv ∈ line φ n, FCert kv.2 := by
  intro n
  induction n with
  | zero =>
    intro _ kv hkv
    have hok : StateOk φ ((0 : Nat) : Int) kv := (lineOk φ 0).2 kv hkv
    refine fCert_of_mapCert φ hbd _ kv hok ?_
    rw [line_zero φ kv hkv]; exact StateLine.mapCert_seed
  | succ m ih =>
    intro hm
    push_cast at hm
    refine fCert_join φ hbd m (hPL m hm) (fun kv hkv d hd hv => ?_)
    by_cases hm0 : m = 0
    · subst hm0
      exact fCert_of_mapCert φ hbd _ _ (StateOk_sent φ 0 kv ((lineOk φ 0).2 kv hkv) d hd hv)
        (StateLine.mapCert_piece0 φ kv hkv d hd hv)
    · exact hPF m (by omega) hm kv hkv (ih (by omega) kv hkv) d hd hv

/-- **The reader decides `φ` under `PieceLocalF` and `PieceF`.** -/
theorem readerVerdictW_iff_of_pieceLocalF (hPL : ∀ n : Nat, (n : Int) + 1 < stepCount φ → PieceLocalF φ n)
    (hPF : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → PieceF φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_fCert φ hbd (fun kv hkv => ?_)
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by simp only [stepCount]; omega
  exact fCert_line φ hbd hPL hPF _ hN kv hkv

/-- info: 'AbsSatBin.GraphPath.Model.FiltCert.readerVerdictW_iff_of_pieceLocalF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pieceLocalF

/-- **The reader decides `φ` under `PieceLocalF` at every join and `TopParent` from line 1 on.** -/
theorem readerVerdictW_iff_of_topParent (hPL : ∀ n : Nat, (n : Int) + 1 < stepCount φ → PieceLocalF φ n)
    (hTP : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → TopParent φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_pieceLocalF φ hbd hPL
    (fun n hn1 hn => pieceF_of_topParent φ hbd n hn1 (hTP n hn1 hn))

/-- info: 'AbsSatBin.GraphPath.Model.FiltCert.readerVerdictW_iff_of_topParent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_topParent

/-- **The reader decides `φ` under `PieceLocalF` at every join and `TopMerge` (the top member of a merge) from line 1
on.** -/
theorem readerVerdictW_iff_of_topMerge (hPL : ∀ n : Nat, (n : Int) + 1 < stepCount φ → PieceLocalF φ n)
    (hTM : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → TopMerge φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_topParent φ hbd hPL (fun n hn1 hn => topParent_of_topMerge φ hbd n (hTM n hn1 hn))

/-- info: 'AbsSatBin.GraphPath.Model.FiltCert.readerVerdictW_iff_of_topMerge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_topMerge

end AbsSatBin.GraphPath.Model.FiltCert
