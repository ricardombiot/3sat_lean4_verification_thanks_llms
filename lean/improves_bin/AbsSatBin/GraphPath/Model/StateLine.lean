-- lean/improves_bin/AbsSatBin/GraphPath/Model/StateLine.lean
import AbsSatBin.GraphPath.Model.StatePiece

/-!
# `MapCert` state by state along the run; the reader decides under `PieceLocal`

* **Base** (`mapCert_seed`, `mapCert_piece0`): the seed and the two states of line 1 are computed.
* **Step**: a piece keeps `MapCert` (`StatePiece.mapCert_piece`, skipped window included), and the join
  keeps it under `PieceLocal` (`PieceJoin.mapCert_join`).
* **`readerVerdictW_iff_of_pieceLocal`**: **the reader decides `φ` under the single hypothesis
  `PieceLocal`** at every join — every clique with witnesses of a joined state lives in one of its pieces.
  Measured: 3.5 M cliques of size 1–3, no exception (`julia/improves_bin/test_3sat/probes/piecelocal_probe.jl`).
-/

namespace AbsSatBin.GraphPath.Model.StateLine

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri (Clique)
open AbsSatBin.GraphPath.Model.MapCert (MapCert WitR CertR)

private def root : PathNodeId := { id := ⟨0, 0⟩, parent_id := none }
private def seed : GPathM := initSeed ⟨0, 0⟩ ""

-- ============================================================
-- Base
-- ============================================================

theorem mapCert_seed : MapCert seed := by
  intro Q R hQ hW
  have hnodes : ∀ q nq, seed.node? q = some nq → q = root ∧ nq.owners = [root] := by
    intro q nq h; exact seed_node q nq h
  refine ⟨fun _ => root, ChainSound_initSeed ⟨0, 0⟩ "" rfl, fun q hq => ?_, fun m hm h0 h1 => ?_⟩
  · obtain ⟨nq, hnq, _⟩ := hQ q hq
    exact (hnodes q nq hnq).1.symm
  · have hcs : seed.current_step = 1 := rfl
    rw [hcs] at h1
    obtain ⟨r, nr, hnr, _, _, hrR⟩ := hW m.step h0 (by rw [hcs]; exact h1)
    obtain ⟨p, hp, hpm⟩ := hrR m hm
    rw [(hnodes r nr hnr).2, List.mem_singleton] at hp
    rw [← hpm, hp]

/-- The addNode of the seed at a node of step 1, computed. -/
theorem mapCert_addNode_seed (i : Int) (hi : i = 0 ∨ i = 1) :
    MapCert (addNode seed ⟨1, i⟩ "" noForb) := by
  have hsel := ChainSound_addNode seed ⟨1, i⟩ "" noForb rfl (by rcases hi with rfl | rfl <;> decide)
    (Certifies.MachineOk_initSeed ⟨0, 0⟩ "") (fun _ => root) (ChainSound_initSeed ⟨0, 0⟩ "" rfl) rfl
  have hown : ∀ n ∈ (addNode seed ⟨1, i⟩ "" noForb).nodes, ∀ q ∈ n.owners,
      q = root ∨ q = shiftPid root ⟨1, i⟩ := by
    rcases hi with rfl | rfl <;> decide
  have hids : ∀ n ∈ (addNode seed ⟨1, i⟩ "" noForb).nodes, n.id = root ∨ n.id = shiftPid root ⟨1, i⟩ := by
    rcases hi with rfl | rfl <;> decide
  have hcs : (addNode seed ⟨1, i⟩ "" noForb).current_step = 2 := rfl
  have e0 : extend seed ⟨1, i⟩ (fun _ => root) 0 = root := rfl
  have e1 : extend seed ⟨1, i⟩ (fun _ => root) 1 = shiftPid root ⟨1, i⟩ := rfl
  intro Q R hQ hW
  refine ⟨extend seed ⟨1, i⟩ (fun _ => root), hsel, fun q hq => ?_, fun m hm h0 h1 => ?_⟩
  · obtain ⟨nq, hnq, _⟩ := hQ q hq
    have hid := node?_id_eq _ q nq hnq
    rcases hids nq (List.mem_of_find?_eq_some hnq) with e | e <;> rw [hid] at e <;> rw [e]
    · exact e0
    · exact e1
  · rw [hcs] at h1
    obtain ⟨r, nr, hnr, _, _, hrR⟩ := hW m.step h0 (by rw [hcs]; exact h1)
    obtain ⟨p, hp, hpm⟩ := hrR m hm
    rcases hown nr (List.mem_of_find?_eq_some hnr) p hp with e | e
    · rw [← hpm, e]; exact congrArg PathNodeId.id e0
    · rw [← hpm, e]; exact congrArg PathNodeId.id e1

variable (φ : Cnf) (hbd : Bounded φ)
include hbd

omit hbd in
theorem mapNodes_one (d : NodeId) (hd : d ∈ mapNodes φ 1) : d = ⟨1, 0⟩ ∨ d = ⟨1, 1⟩ := by
  unfold mapNodes at hd
  repeat' split at hd
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  all_goals
    first
      | exact Or.inl hd
      | (rcases hd with h | h
         · exact Or.inl h
         · exact Or.inr h)

omit hbd in
/-- **The pieces of the seed keep `MapCert`.** -/
theorem mapCert_piece0 (kv : NodeId × GPathM) (hkv : kv ∈ line φ 0) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) : MapCert (upF φ kv.2 d) := by
  rw [line_zero φ kv hkv] at hd ⊢
  have hm0 : (0 : Int) < midFusion φ := by simp only [midFusion]; omega
  have hd1 : d ∈ mapNodes φ 1 := by
    unfold sonsOfMap at hd
    rw [if_neg (by simp)] at hd; exact hd
  have hds : d.step = 1 := mapNodes_step φ 1 d hd1
  have hreq : reqOf φ d = [] := by
    unfold reqOf
    rw [if_neg (by omega)]
    split
    · split
      · rfl
      · omega
    · split
      · rfl
      · rw [if_neg (by simp only [fusionTop]; omega)]
        exfalso; omega
  have hfil : filterAll seed [] = seed := rfl
  have key : ∀ i : Int, (i = 0 ∨ i = 1) → d = ⟨1, i⟩ → MapCert (upF φ ((⟨0, 0⟩ : NodeId), seed).2 d) := by
    intro i hi hdi
    subst hdi
    have hsk : skipsWindow seed ⟨1, i⟩ (isProhibited φ) = false := by
      unfold skipsWindow
      rw [show shiftRowIds seed ⟨1, i⟩ = [shiftPid root ⟨1, i⟩] from rfl]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      unfold isProhibited isL3
      simp only [shiftPid]
      have : ¬ (midFusion φ < 1) := by omega
      simp [this]
    have hnr : newRowIds seed ⟨1, i⟩ (isProhibited φ) = newRowIds seed ⟨1, i⟩ noForb := by
      unfold newRowIds
      rw [show shiftRowIds seed ⟨1, i⟩ = [shiftPid root ⟨1, i⟩] from rfl]
      unfold isProhibited isL3
      simp only [shiftPid, noForb]
      have : ¬ (midFusion φ < 1) := by omega
      simp [this]
    have hup : upF φ ((⟨0, 0⟩ : NodeId), seed).2 ⟨1, i⟩ = addNode seed ⟨1, i⟩ "" noForb := by
      show up (filterAll seed (reqOf φ ⟨1, i⟩)) ⟨1, i⟩ "" (isProhibited φ) = _
      rw [hreq, hfil]
      unfold up
      rw [if_pos (show isValid seed = true from rfl), hsk, if_neg (by decide)]
      have hum : upMap seed ⟨1, i⟩ (isProhibited φ) = upMap seed ⟨1, i⟩ noForb := by
        funext x; unfold upMap upOwners upSons gainedOwners gainedSons; rw [hnr]
      unfold addNode newRow
      rw [hum, hnr]
    rw [hup]
    exact mapCert_addNode_seed i hi
  rcases mapNodes_one φ d hd1 with e | e
  · exact key 0 (Or.inl rfl) e
  · exact key 1 (Or.inr rfl) e

-- ============================================================
-- Along the run
-- ============================================================

/-- **Every state of every line has `MapCert`**, under `PieceLocal` at every join. -/
theorem mapCert_line (hPL : ∀ n : Nat, (n : Int) + 1 < stepCount φ → PieceJoin.PieceLocal φ n) :
    ∀ n : Nat, (n : Int) < stepCount φ → ∀ kv ∈ line φ n, MapCert kv.2 := by
  intro n
  induction n with
  | zero =>
    intro _ kv hkv
    rw [line_zero φ kv hkv]; exact mapCert_seed
  | succ m ih =>
    intro hm
    push_cast at hm
    refine PieceJoin.mapCert_join φ m (hPL m hm) (fun kv hkv d hd hv => ?_)
    by_cases hm0 : m = 0
    · subst hm0; exact mapCert_piece0 φ kv hkv d hd hv
    · exact StatePiece.mapCert_piece φ hbd m (by omega) kv hkv d hd hv (ih (by omega) kv hkv)

/-- **The reader decides `φ` under `PieceLocal`.** -/
theorem readerVerdictW_iff_of_pieceLocal
    (hPL : ∀ n : Nat, (n : Int) + 1 < stepCount φ → PieceJoin.PieceLocal φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine CertFix.readerVerdictW_iff_of_certLink φ hbd (fun kv hkv hv => ?_)
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by omega
  have hkvl : kv ∈ line φ (stepCount φ - 1).toNat := hkv
  have hmap := mapCert_line φ hbd hPL _ hN kv hkvl
  obtain ⟨cm, _⟩ := SymMachine.machine_ctx φ hbd kv hkv
  have c := AmbTriCore.aCtx_readPins φ hbd kv hkv [] _ OtherBitSem.ReadPins.start hv
  exact CertInvariant.certLink_of_certClique c
    (MapCert.certClique_of_mapCert (MapCert.mapCert_filterAll_nil kv.2 cm.nodup hmap))

/-- info: 'AbsSatBin.GraphPath.Model.StateLine.readerVerdictW_iff_of_pieceLocal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pieceLocal

end AbsSatBin.GraphPath.Model.StateLine
