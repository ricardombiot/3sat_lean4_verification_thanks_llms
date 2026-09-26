-- lean/improves_bin/AbsSatBin/GraphPath/Model/AnchorPiece.lean
import AbsSatBin.GraphPath.Model.FiltCert

/-!
# `PieceLocalF` from an anchor at the top

Measured (`julia/improves_bin/test_3sat/probes/anchor_probe.jl`, `anchorf_probe.jl`, `docs/context/ambfar.md` §4.2λ):
in a joined state (filtered or not) a clique with witnesses always gains a node `w` of the new step keeping its
witnesses (A1, 1.78 M), and a clique with witnesses with a member `w` at the top is one of the piece of `w` — the only
piece where `w` lives — with no step missing, clause steps included (S2, 2.5 M).

* **`AnchorF n`** (A1): a clique with witnesses of a filtered joined state, below its top, gains a top node.
* **`TopPieceF n`** (S2): a clique with witnesses of a filtered joined state with a member `w` at the top is one of
  the piece of `w` (the source whose key is `w`'s parent id), filtered alike.
* **`pieceLocalF_of_anchor`**: both give `PieceLocalF`. With a member at the top, S2; without, A1 anchors the clique
  and S2 puts the anchored clique in one piece. The source of `w` is found by `top_one_source`.
* **`readerVerdictW_iff_of_anchor`**: the reader decides under A1, S2 and `MergeSplit`.
-/

namespace AbsSatBin.GraphPath.Model.AnchorPiece

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri (Clique)
open AbsSatBin.GraphPath.Model.CertDescent (Wit)
open AbsSatBin.GraphPath.Model.FiltCert

variable (φ : Cnf) (n : Nat)

/-- **A1**: a clique with witnesses of a filtered joined state, below its top, gains a node of the top step. -/
def AnchorF : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < kv'.2.current_step) →
    isValid (filterAll kv'.2 R) = true → ∀ Q, Clique (filterAll kv'.2 R) Q → Wit (filterAll kv'.2 R) Q →
      (∀ q ∈ Q, q.id.step ≤ n) →
      ∃ w, w.id.step = (n : Int) + 1 ∧ Clique (filterAll kv'.2 R) (w :: Q) ∧ Wit (filterAll kv'.2 R) (w :: Q)

/-- **S2**: a clique with witnesses of a filtered joined state with a member `w` at the top is one of the piece of
`w`, filtered alike. -/
def TopPieceF : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < kv'.2.current_step) →
    isValid (filterAll kv'.2 R) = true → ∀ w Q, Clique (filterAll kv'.2 R) (w :: Q) →
      Wit (filterAll kv'.2 R) (w :: Q) → w.id.step = (n : Int) + 1 →
      ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true → w.parent_id = some kv.1 →
        isValid (filterAll (upF φ kv.2 kv'.1) R) = true ∧
        Clique (filterAll (upF φ kv.2 kv'.1) R) (w :: Q) ∧ Wit (filterAll (upF φ kv.2 kv'.1) R) (w :: Q)

/-- A sub-list of a clique with witnesses is a clique with witnesses. -/
theorem good_sub {g : GPathM} {P Q : List PathNodeId} (hsub : ∀ q ∈ Q, q ∈ P) (hQ : Clique g P) (hW : Wit g P) :
    Clique g Q ∧ Wit g Q :=
  ⟨fun p hp => by
      obtain ⟨np, hnp, ho⟩ := hQ p (hsub p hp)
      exact ⟨np, hnp, fun s hs => ho s (hsub s hs)⟩,
    fun l h0 h1 => by
      obtain ⟨r, nr, hnr, hrs, ho⟩ := hW l h0 h1
      exact ⟨r, nr, hnr, hrs, fun s hs => ho s (hsub s hs)⟩⟩

variable (hbd : Bounded φ)
include hbd

/-- **A1 and S2 give `PieceLocalF`.** -/
theorem pieceLocalF_of_anchor (hA : AnchorF φ n) (hS : TopPieceF φ n) : PieceLocalF φ n := by
  intro kv' hkv' R hR hv Q hQ hW
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hreach := MapReachable.reachable_of_mapReachable φ hbd _ hok'.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach
  have c := filt_ctx φ hbd _ kv' hok' R hv
  have hb := KernelIff.below_filterAll_self kv'.2 hnd R
  have hcs : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hFcs : (filterAll kv'.2 R).current_step = (n : Int) + 2 := by rw [← hb.step, hcs]
  -- an anchor `w` at the top with `w :: Q` a clique with witnesses
  obtain ⟨w, hws, hQw, hWw⟩ : ∃ w, w.id.step = (n : Int) + 1 ∧ Clique (filterAll kv'.2 R) (w :: Q) ∧
      Wit (filterAll kv'.2 R) (w :: Q) := by
    by_cases htop : ∃ w ∈ Q, (n : Int) < w.id.step
    · obtain ⟨w, hwQ, hwn⟩ := htop
      obtain ⟨nw, hnw, _⟩ := hQ w hwQ
      have := (CertFix.step_range c.pc w nw hnw).2
      rw [hFcs] at this
      have hsub : ∀ q ∈ w :: Q, q ∈ Q := fun q hq => by
        rcases List.mem_cons.mp hq with e | hq
        · rw [e]; exact hwQ
        · exact hq
      obtain ⟨h1, h2⟩ := good_sub hsub hQ hW
      exact ⟨w, by omega, h1, h2⟩
    · exact hA kv' hkv' R hR hv Q hQ hW (fun q hq => by
        have : ¬ (n : Int) < q.id.step := fun h => htop ⟨q, hq, h⟩
        omega)
  -- the source of `w`
  obtain ⟨nw, hnw, _⟩ := hQw w List.mem_cons_self
  obtain ⟨nJ, hnJ, _, _, _⟩ := hb.node w nw hnw
  obtain ⟨kv, hkv, hd, hvp, hpar, _⟩ := StateGrow.top_one_source φ hbd n kv' hkv' w nJ hnJ hws
  obtain ⟨hvP, hQP, hWP⟩ := hS kv' hkv' R hR hv w Q hQw hWw hws kv hkv hd hvp hpar
  obtain ⟨h1, h2⟩ := good_sub (fun q hq => List.mem_cons_of_mem w hq) hQP hWP
  exact ⟨kv, hkv, hd, hvp, hvP, h1, h2⟩

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.pieceLocalF_of_anchor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pieceLocalF_of_anchor

omit n in
/-- **The reader decides `φ` under A1 and S2 at every join and `MergeSplit` from line 1 on.** -/
theorem readerVerdictW_iff_of_anchor (hA : ∀ n : Nat, (n : Int) + 1 < stepCount φ → AnchorF φ n)
    (hS : ∀ n : Nat, (n : Int) + 1 < stepCount φ → TopPieceF φ n)
    (hMS : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → MergeSplit φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_mergeSplit φ hbd (fun n hn => pieceLocalF_of_anchor φ n hbd (hA n hn) (hS n hn)) hMS

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.readerVerdictW_iff_of_anchor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_anchor

end AbsSatBin.GraphPath.Model.AnchorPiece
