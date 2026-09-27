-- lean/improves_bin/AbsSatBin/GraphPath/Model/JoinTri.lean
import AbsSatBin.GraphPath.Model.Splice

/-!
# `CliqueTri` through the join

Measured (`julia/improves_bin/test_3sat/probes/cliquetri*_probe.jl`, `docs/context/escalera_reader.md` §4.2ν): `CliqueTri` (the
pair rule relative to a clique, with one round of cuts) holds at every stage of the machine — filtered sources, pieces
and joined states — for cliques of 1 to 4 nodes, with the corrected review. The joined state is the union of its pieces
with **no review after it**, so there `CliqueTri` must come from the pieces.

* **`cxP_grown`**: a `P`-compatible link climbs to a state the first one grows into.
* **`cliqueTri_of_joinChoice`**: if states that all grow into `J` have `CliqueTri`, and every `P`-compatible link of `J`
  (with `P` a clique of `J`) is already one of a single such state, with `P` a clique there (`JoinChoiceP`), then `J` has
  `CliqueTri`: the witness the state gives climbs to `J`.
* **`cliqueTri_line_of_pieces`**: the instance for a state of line `n+1` and its pieces.
* **`joinChoice_nil`**: `JoinChoiceP` for the empty clique holds: an entry of a joined state comes from one piece
  (`join_no_new`), where the pair rule gives its witnesses.
* **The route of `CliqueTri`** (`fCert_join_of_choice`, `fCert_line_choice`, **`readerVerdictW_iff_of_joinChoice`**): the
  reader decides under **two** hypotheses — `JoinChoicePF` (the join choice for every filter) and AF in the pieces. The
  pieces keep the certificates of the filters (`pieceF_of_topParent`); the join keeps `CliqueTri` of the filters
  (`cliqueTri_of_joinChoice`), which on states with the reader's context is `CertClique`.
-/

namespace AbsSatBin.GraphPath.Model.JoinTri

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.FiltCert
open AbsSatBin.GraphPath.Model.AnchorPiece

/-- A `P`-compatible link climbs to a state the first one grows into. -/
theorem cxP_grown {X J : GPathM} (hgr : Grown X J) {P : List PathNodeId} {ny nyJ : PNodeM} {w : PathNodeId}
    (hsub : ∀ q ∈ ny.owners, q ∈ nyJ.owners) (h : CxP X P ny w) : CxP J P nyJ w := by
  obtain ⟨nw, hnw, hwy, hl⟩ := h
  obtain ⟨nwJ, hnwJ, hownw, _, _⟩ := hgr.node?_grown w nw hnw
  refine ⟨nwJ, hnwJ, hsub w hwy, fun l h0 h1 => ?_⟩
  obtain ⟨r, hr, hrw, hrs, nr, hnr, hrP⟩ := hl l h0 (by rw [← hgr.step_eq]; exact h1)
  obtain ⟨nrJ, hnrJ, hownr, _, _⟩ := hgr.node?_grown r nr hnr
  exact ⟨r, hsub r hr, hownw r hrw, hrs, nrJ, hnrJ, fun p hp => hownr p (hrP p hp)⟩

/-- **`JoinChoiceP`**: every `P`-compatible link of `J`, with `P` a clique of `J` and both ends owning `P`, is already a
`P`-compatible link of one of the states `Side`, with `P` a clique there and both ends owning `P` there. -/
def JoinChoiceP (J : GPathM) (Side : GPathM → Prop) : Prop :=
  ∀ P, Clique J P → ∀ y ny w nw, J.node? y = some ny → J.node? w = some nw → OwnsAll P ny → OwnsAll P nw →
    CxP J P ny w → ∃ X, Side X ∧ Clique X P ∧ ∃ nyX nwX, X.node? y = some nyX ∧ X.node? w = some nwX ∧
      OwnsAll P nyX ∧ OwnsAll P nwX ∧ CxP X P nyX w

/-- **`CliqueTri` through the join**: states that grow into `J`, each with `CliqueTri`, and `JoinChoiceP`, give
`CliqueTri J`. The witness `r` the chosen state gives, with its compatible links, climbs to `J` (`cxP_grown`). -/
theorem cliqueTri_of_joinChoice (J : GPathM) (Side : GPathM → Prop) (hgr : ∀ X, Side X → Grown X J)
    (htri : ∀ X, Side X → CliqueTri X) (hch : JoinChoiceP J Side) : CliqueTri J := by
  intro P hP y ny w nw hy hw hyP hwP hC l h0 h1
  obtain ⟨X, hX, hPX, nyX, nwX, hyX, hwX, hyPX, hwPX, hCX⟩ := hch P hP y ny w nw hy hw hyP hwP hC
  have g := hgr X hX
  obtain ⟨ny', hny', hsuby, _, _⟩ := g.node?_grown y nyX hyX
  rw [hy] at hny'; cases hny'
  obtain ⟨nw', hnw', hsubw, _, _⟩ := g.node?_grown w nwX hwX
  rw [hw] at hnw'; cases hnw'
  obtain ⟨r, hr, hrw, hrs, ⟨nr, hnr, hrP⟩, hCyr, hCwr⟩ :=
    htri X hX P hPX y nyX w nwX hyX hwX hyPX hwPX hCX l h0 (by rw [← g.step_eq]; exact h1)
  obtain ⟨nrJ, hnrJ, hownr, _, _⟩ := g.node?_grown r nr hnr
  exact ⟨r, hsuby r hr, hsubw r hrw, hrs, ⟨nrJ, hnrJ, fun p hp => hownr p (hrP p hp)⟩,
    cxP_grown g hsuby hCyr, cxP_grown g hsubw hCwr⟩

/-- info: 'AbsSatBin.GraphPath.Model.JoinTri.cliqueTri_of_joinChoice' does not depend on any axioms -/
#guard_msgs in
#print axioms cliqueTri_of_joinChoice

variable (φ : Cnf)

/-- **A state of line `n+1` has `CliqueTri`** when its pieces have it and `JoinChoiceP` holds for them. -/
theorem cliqueTri_line_of_pieces (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1))
    (htri : ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
      CliqueTri (upF φ kv.2 kv'.1))
    (hch : JoinChoiceP kv'.2 (fun X => ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧
      isValid (upF φ kv.2 kv'.1) = true ∧ X = upF φ kv.2 kv'.1)) :
    CliqueTri kv'.2 := by
  refine cliqueTri_of_joinChoice kv'.2 _ (fun X ⟨kv, hkv, hd, hv, hX⟩ => ?_)
    (fun X ⟨kv, hkv, hd, hv, hX⟩ => hX ▸ htri kv hkv hd hv) hch
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hv
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  rw [hX, ← he]; exact hgr

/-- info: 'AbsSatBin.GraphPath.Model.JoinTri.cliqueTri_line_of_pieces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cliqueTri_line_of_pieces

variable (hbd : Bounded φ)
include hbd

/-- **`JoinChoiceP` for the empty clique**: an entry of a joined state comes from one piece (`join_no_new`), where the
kernel's pair rule gives its witnesses (`cxP_nil`). -/
theorem joinChoice_nil (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (y : PathNodeId) (ny : PNodeM)
    (w : PathNodeId) (nw : PNodeM) (hy : kv'.2.node? y = some ny) (_hw : kv'.2.node? w = some nw)
    (hC : CxP kv'.2 [] ny w) :
    ∃ X, (∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 kv'.1) = true ∧ X = upF φ kv.2 kv'.1) ∧
      Clique X [] ∧ ∃ nyX nwX, X.node? y = some nyX ∧ X.node? w = some nwX ∧
        OwnsAll [] nyX ∧ OwnsAll [] nwX ∧ CxP X [] nyX w := by
  obtain ⟨_, _, hwy, _⟩ := hC
  obtain ⟨kv, hkv, hd, hv, n', hn', hwn'⟩ := (PieceJoin.join_no_new φ n kv' hkv').2 y ny hy w hwy
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv ((lineOk φ n).2 kv hkv) kv'.1 hd hv
  have cP := KernelUp.aCtx_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hP.reach) hP.valid
  obtain ⟨nwX, hnwX⟩ := cP.pc.ker.isNode_owner y n' hn' w hwn'
  exact ⟨_, ⟨kv, hkv, hd, hv, rfl⟩, fun _ h => absurd h List.not_mem_nil, n', nwX, hn', hnwX,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, cxP_nil cP.pc y n' hn' w hwn'⟩

/-- info: 'AbsSatBin.GraphPath.Model.JoinTri.joinChoice_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms joinChoice_nil

-- ============================================================
-- The whole run through `CliqueTri` of the filters: two hypotheses
-- ============================================================

omit hbd in
/-- **`JoinChoicePF n`**: `JoinChoiceP` for every valid filter of a joined state of line `n+1`, against the same filter
of its pieces. -/
def JoinChoicePF (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < kv'.2.current_step) →
    isValid (filterAll kv'.2 R) = true →
    JoinChoiceP (filterAll kv'.2 R) (fun X => ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧
      isValid (upF φ kv.2 kv'.1) = true ∧ isValid (filterAll (upF φ kv.2 kv'.1) R) = true ∧
      X = filterAll (upF φ kv.2 kv'.1) R)

/-- **The join keeps `FCert` under `JoinChoicePF`.** For a filter `R`, the pieces filtered by `R` have `CliqueTri`
(`CliqueTri ⇔ CertClique` on states with the reader's context), they grow into the joined state filtered by `R` (a
filtered piece is a kernel below the joined state, pinned by `R`), so `cliqueTri_of_joinChoice` gives `CliqueTri` of the
filtered joined state, and with it `CertClique`. -/
theorem fCert_join_of_choice (n : Nat) (hJC : JoinChoicePF φ n)
    (hP : ∀ kv ∈ line φ n, ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true → FCert (upF φ kv.2 d)) :
    ∀ kv' ∈ line φ (n + 1), FCert kv'.2 := by
  intro kv' hkv' R hR hv
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have cF := filt_ctx φ hbd _ kv' hok' R hv
  refine CertInvariant.certClique_of_cliqueTri cF (cliqueTri_of_joinChoice _ _ (fun X hX => ?_) (fun X hX => ?_)
    (hJC kv' hkv' R hR hv))
  · obtain ⟨kv, hkv, hd, hvp, hvX, rfl⟩ := hX
    obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hvp
    have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
    have hP' : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) :=
      StateOk_sent φ n kv ((lineOk φ n).2 kv hkv) kv'.1 hd hvp
    have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
      (MapReachable.reachable_of_mapReachable φ hbd _ hP'.reach)
    have cP := filt_ctx φ hbd _ _ hP' R hvX
    have hB : Kernel.Below kv'.2 (filterAll (upF φ kv.2 kv'.1) R) := by
      rw [← he]
      exact PieceFilter.below_trans (PieceFilter.below_of_grown hgr) (KernelIff.below_filterAll_self _ hndP R)
    exact PieceFilter.grown_of_below (Kernel.below_filterAll cP.pc.ker hB R
      (fun r hr q hq hqs => LineUnion.gowner_pinned _ R q hq r hr hqs))
  · obtain ⟨kv, hkv, hd, hvp, hvX, rfl⟩ := hX
    have hP' : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) :=
      StateOk_sent φ n kv ((lineOk φ n).2 kv hkv) kv'.1 hd hvp
    have cP := filt_ctx φ hbd _ _ hP' R hvX
    obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hvp
    have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
    have hRP : ∀ p ∈ R, 0 ≤ p.step ∧ p.step < (upF φ kv.2 kv'.1).current_step := by
      intro p hp
      have hcs : kv'.2.current_step = (upF φ kv.2 kv'.1).current_step := by rw [← he]; exact hgr.step_eq
      rw [← hcs]; exact hR p hp
    exact CertFix.cliqueTri_of_certLink cP.pc
      (CertInvariant.certLink_of_certClique cP (hP kv hkv kv'.1 hd hvp R hRP hvX))

/-- info: 'AbsSatBin.GraphPath.Model.JoinTri.fCert_join_of_choice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fCert_join_of_choice

/-- **Every state of every line has `FCert`**, under `JoinChoicePF` at every join and AF in the pieces from line 1 on. -/
theorem fCert_line_choice (hJC : ∀ n : Nat, (n : Int) + 1 < stepCount φ → JoinChoicePF φ n)
    (hAF : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → AFP φ n) :
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
    refine fCert_join_of_choice φ hbd m (hJC m hm) (fun kv hkv d hd hv => ?_)
    by_cases hm0 : m = 0
    · subst hm0
      exact fCert_of_mapCert φ hbd _ _ (StateOk_sent φ 0 kv ((lineOk φ 0).2 kv hkv) d hd hv)
        (StateLine.mapCert_piece0 φ kv hkv d hd hv)
    · exact pieceF_of_topParent φ hbd m (by omega) (topParent_of_afp φ m hbd (by omega) (hAF m (by omega) hm))
        kv hkv (ih (by omega) kv hkv) d hd hv

/-- **The reader decides `φ` under two hypotheses: `JoinChoicePF` at every join and AF in the pieces.** The route of
`CliqueTri`: pieces keep the certificates of the filters (`pieceF_of_topParent`), and the join keeps `CliqueTri` of the
filters when every compatible link lies in one filtered piece. -/
theorem readerVerdictW_iff_of_joinChoice (hJC : ∀ n : Nat, (n : Int) + 1 < stepCount φ → JoinChoicePF φ n)
    (hAF : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → AFP φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_fCert φ hbd (fun kv hkv => ?_)
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by simp only [stepCount]; omega
  exact fCert_line_choice φ hbd hJC hAF _ hN kv hkv

/-- info: 'AbsSatBin.GraphPath.Model.JoinTri.readerVerdictW_iff_of_joinChoice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_joinChoice

end AbsSatBin.GraphPath.Model.JoinTri
