-- lean/improves_bin/AbsSatBin/GraphPath/Model/ChainRoute.lean
import AbsSatBin.GraphPath.Model.StateLine

/-!
# The path route: every node on a chain, through the join

The machine carries every partial solution (`PrefixCarry`) and the union invents no chain
(`PieceJoin.chain_in_piece`). The path version of the invariant is `SupportedG`: every node of a state lies on a
chain of it.

* **`supported_join`**: if every piece has it, the joined state has it — every node of the union is a node of a
  piece (`PieceJoin.join_no_new`), and a chain of a piece is a chain of the union (`PieceJoin.piece_grown`).

So on the path route the join is free; what is left is the piece (the requirement filter with its review, and
the `UP` with a skipped window).
-/

namespace AbsSatBin.GraphPath.Model.ChainRoute

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem

variable (φ : Cnf)

/-- A chain of `g` is a chain of anything `g` grows into. -/
theorem chainG_of_grown {g g' : GPathM} (hgr : Grown g g') (sel : Int → PathNodeId) (h : ChainG g sel) :
    ChainG g' sel :=
  ⟨IsChain_of_grown hgr sel h.1, PairwiseOwned_of_grown hgr sel h.2.1,
    fun k h0 h1 => hgr.gowners_grown _ (h.2.2 k h0 (by rw [← hgr.step_eq]; exact h1))⟩

/-- **The join keeps `SupportedG`.** -/
theorem supported_join (n : Nat)
    (hP : ∀ kv ∈ line φ n, ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true → SupportedG (upF φ kv.2 d)) :
    ∀ kv' ∈ line φ (n + 1), SupportedG kv'.2 := by
  intro kv' hkv' pid n0 hn0
  obtain ⟨kv, hkv, hd, hv, n', hn'⟩ := (PieceJoin.join_no_new φ n kv' hkv').1 pid n0 hn0
  obtain ⟨sel, hsel, hpid⟩ := hP kv hkv kv'.1 hd hv pid n' hn'
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hv
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  rw [← he]
  exact ⟨sel, chainG_of_grown hgr sel hsel, hpid⟩

/-- info: 'AbsSatBin.GraphPath.Model.ChainRoute.supported_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supported_join

-- ============================================================
-- The reader on the path route
-- ============================================================

/-- **If every valid state the reader visits holds a chain, the reader never gets stuck**: at the first
choice it pins the chain's node, and the chain survives the pin. -/
theorem progressFirst_of_chains (g₀ : GPathM)
    (h : ∀ g, ReaderPrefix.ReadFirst g₀ g → isValid g = true → ∃ sel, ChainSound g sel) :
    ReaderPrefix.ProgressFirst g₀ := by
  intro g hg hv k hk
  have hkr : 0 ≤ k ∧ k < g.current_step := by
    clear h
    unfold ReaderExec.firstChoice at hk
    have hm := List.mem_of_find?_eq_some hk
    exact ⟨mem_intRange_lower hm, Int.lt_of_le_sub_one (mem_intRange_upper hm)⟩
  obtain ⟨sel, hs⟩ := h g hg hv
  refine ⟨sel k, ?_, ?_⟩
  · unfold ownersAt
    exact List.mem_filter.mpr ⟨hs.chain.2.2 k hkr.1 hkr.2,
      beq_iff_eq.mpr (hs.chain.1.1 k hkr.1 hkr.2).2⟩
  · have hs' := ChainSound_filterAll g [(sel k).id] sel hs (fun r hr _ _ => by
      rw [List.mem_singleton.mp hr, (hs.chain.1.1 k hkr.1 hkr.2).2])
    exact PickInduction.isValid_of_ChainG _ sel hs'.chain

/-- **The reader decides `φ` when every valid state it visits holds a chain** (the path route). -/
theorem readerVerdictW_iff_of_chains (hbd : Bounded φ)
    (h : ∀ kv ∈ pureRun φ, ∀ g, ReaderPrefix.ReadFirst (filterAll kv.2 []) g → isValid g = true →
      ∃ sel, ChainSound g sel) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  NoDeadEnd.readerVerdictW_iff_of_noDeadEnd φ hbd (fun kv hkv => progressFirst_of_chains _ (h kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.ChainRoute.readerVerdictW_iff_of_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_chains

-- ============================================================
-- The combined invariant
-- ============================================================

/-- **The combined invariant.** Cliques inside each piece (filter, `UP`, skipped window: `StatePiece`) and
chains across the join (`PieceJoin.chain_in_piece`): `MapCert` holds in every state of the machine **if and
only if** `PieceLocal` holds at every join. -/
theorem combined_invariant (hbd : Bounded φ) :
    (∀ n : Nat, (n : Int) + 1 < stepCount φ → PieceJoin.PieceLocal φ n) ↔
      (∀ n : Nat, (n : Int) < stepCount φ → ∀ kv ∈ line φ n, MapCert.MapCert kv.2) := by
  refine ⟨fun h => StateLine.mapCert_line φ hbd h, fun h n hn => ?_⟩
  exact PieceJoin.pieceLocal_of_mapCert φ hbd n hn (h (n + 1) (by push_cast; exact hn))

/-- info: 'AbsSatBin.GraphPath.Model.ChainRoute.combined_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms combined_invariant

end AbsSatBin.GraphPath.Model.ChainRoute
