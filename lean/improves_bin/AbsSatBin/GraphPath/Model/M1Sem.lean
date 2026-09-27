-- lean/improves_bin/AbsSatBin/GraphPath/Model/M1Sem.lean
import AbsSatBin.GraphPath.Model.FExtInd

/-!
# M1 from certificates (`docs/context/ambfar.md` §4.2ο.2)

* **`CertPin n`**: a valid pin set of a joined state of line `n+1` lies on a certificate of it (a chain through the
  pins). A chain of a machine state is a partial solution (`PrefixDecode`), so this is the semantic soundness of the
  validity test on the joined states.
* **`m1_of_certPin`**: `CertPin ⇒ M1`. Every chain of the joined state lies in one piece (`PieceJoin.chain_in_piece`),
  survives the piece's filter by the pins it passes (`ChainSound_filterAll`), and a chain makes a state valid
  (`isValid_of_chainSound`).
* **`readerVerdictW_iff_of_certPin`**: the reader decides under `CertPin` at every join.
-/

namespace AbsSatBin.GraphPath.Model.M1Sem

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.ReaderExec

/-- A state with a chain is valid. -/
theorem isValid_of_chainSound (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) : isValid g = true := by
  unfold isValid
  refine List.all_eq_true.mpr (fun k hk => ?_)
  have h0 := mem_intRange_lower hk
  have h1 := mem_intRange_upper hk
  exact List.any_eq_true.mpr ⟨sel k, h.chain.2.2 k h0 (by omega), beq_iff_eq.mpr (h.chain.1.1 k h0 (by omega)).2⟩

variable (φ : Cnf) (hbd : Bounded φ)

/-- **`CertPin`**: a valid pin set of a joined state lies on one of its certificates. -/
def CertPin (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ ps : List NodeId, isValid (filterAll kv'.2 ps) = true →
    ∃ sel, ChainSound kv'.2 sel ∧ ∀ r ∈ ps, 0 ≤ r.step → r.step < kv'.2.current_step → (sel r.step).id = r

include hbd

/-- **`CertPin ⇒ M1`.** -/
theorem m1_of_certPin (n : Nat) (hn : (n : Int) + 1 < stepCount φ) (h : CertPin φ n) : FExtInd.M1 φ n := by
  intro kv' hkv' ps hv
  obtain ⟨sel, hs, hps⟩ := h kv' hkv' ps hv
  obtain ⟨kv, hkv, hd, hvP, sel', hs', heq⟩ := PieceJoin.chain_in_piece φ hbd n hn kv' hkv' sel hs
  refine ⟨kv, hkv, hd, hvP, ?_⟩
  have hok := (lineOk φ n).2 kv hkv
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvP
  have hPcs : (upF φ kv.2 kv'.1).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  refine isValid_of_chainSound _ sel' (ChainSound_filterAll _ ps sel' hs' (fun r hr h0 h1 => ?_))
  rw [hPcs] at h1
  rw [heq r.step h0 h1]
  exact hps r hr h0 (by rw [hcs']; exact h1)

/-- **The reader decides `φ` under `CertPin` at every join.** -/
theorem readerVerdictW_iff_of_certPin (hC : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → CertPin φ n) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  FExtInd.readerVerdictW_iff_of_m1 φ hbd (fun n h1 hn => m1_of_certPin φ hbd n hn (hC n h1 hn))

end AbsSatBin.GraphPath.Model.M1Sem

/-- info: 'AbsSatBin.GraphPath.Model.M1Sem.readerVerdictW_iff_of_certPin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.M1Sem.readerVerdictW_iff_of_certPin
