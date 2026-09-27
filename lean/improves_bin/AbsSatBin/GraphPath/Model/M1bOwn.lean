-- lean/improves_bin/AbsSatBin/GraphPath/Model/M1bOwn.lean
import AbsSatBin.GraphPath.Model.M1Parts

/-!
# `M1bLowOwn` from the links witnessed through the key (`docs/context/escalera_reader.md` §4.2ο.2)

In the joined state `J` pinned by `k :: ps`, only the key `k` lives at step `n`, so every node owns, at step `n`, a node
of `k`. Let `p` (below `n`) own `v`: the pair rule gives them a common entry at every step, and that entry owns a node
of `k`.

* **`KTri`** (⚠ measured false): a common node `x` of step `n` is not enough. In `clause_mix.cnf` there are links `p–v`
  with a common `x` whose witnesses at some step are not owned by `x`; the key's piece does not have them.
* **`KTriK`**: if at every step `p` and `v` have a common entry that owns a node of the key `k`, then `v` is in the table
  of `p` in the piece of `k`. It speaks of any pins, not only of pinned keys.
* **`m1bLowOwn_of_kTriK`**: `KTriK ⇒ M1bLowOwn`. `p` is a node of the piece because it owns itself.
* **`readerVerdictW_iff_of_kTriK`**: the reader decides under `M1aAll` and `KTriK` at every join.
-/

namespace AbsSatBin.GraphPath.Model.M1bOwn

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.M1Parts

variable (φ : Cnf) (hbd : Bounded φ)

/-- **The triple at the key row** (⚠ measured FALSE, `ktri_probe.jl`: 716 failures with no pins in `clause_mix.cnf`):
two nodes of a valid pinned joined state that own each other and a common node `x` of step `n` own each other in the
piece of `x`'s key. The failures are links with no common witness that owns `x` (those of `KeyTri`). -/
def KTri (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ ps : List NodeId, isValid (filterAll kv'.2 ps) = true →
    ∀ p np v nv x, (filterAll kv'.2 ps).node? p = some np → (filterAll kv'.2 ps).node? v = some nv →
      p.id.step < (n : Int) → v ∈ np.owners → x ∈ np.owners → x ∈ nv.owners → x.id.step = (n : Int) →
      ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true → x.id = kv.1 →
        ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ v ∈ nP.owners

/-- **A link witnessed through the key lies in its piece**: in a valid pinned joined state, if `p` (below step `n`) owns
`v` and at every step they have a common entry that owns a node of the key `k`, then `v` is in the table of `p` in the
piece of `k`. With `k` pinned, every common entry owns a node of `k`. -/
def KTriK (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ ps : List NodeId, isValid (filterAll kv'.2 ps) = true →
    ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
      ∀ p np v nv, (filterAll kv'.2 ps).node? p = some np → (filterAll kv'.2 ps).node? v = some nv →
        p.id.step < (n : Int) → v ∈ np.owners →
        (∀ l : Int, 0 ≤ l → l < (n : Int) + 2 → ∃ r ∈ np.owners, r ∈ nv.owners ∧ r.id.step = l ∧
          ∃ nr, (filterAll kv'.2 ps).node? r = some nr ∧ ∃ x ∈ nr.owners, x.id = kv.1) →
        ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ v ∈ nP.owners

include hbd

/-- **`KTriK ⇒ M1bLowOwn`**: with the key pinned, the common entries the pair rule gives own, at step `n`, an entry
that is a node of the key. -/
theorem m1bLowOwn_of_kTriK (n : Nat) (hT : KTriK φ n) : M1bLowOwn φ n := by
  intro kv' hkv' kv hkv hd hvP ps hvK p np hnp hlow
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hkn : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 ((lineOk φ n).2 kv hkv).onMap
  have cK := filt_ctx φ hbd _ kv' hok' (kv.1 :: ps) hvK
  have hbJK := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') (kv.1 :: ps)
  have hKcs : (filterAll kv'.2 (kv.1 :: ps)).current_step = (n : Int) + 2 := by rw [← hbJK.step, hcs']
  have tri : ∀ v ∈ np.owners, ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ v ∈ nP.owners := by
    intro v hv
    obtain ⟨nv, hnv⟩ := cK.pc.ker.isNode_owner p np hnp v hv
    refine hT kv' hkv' (kv.1 :: ps) hvK kv hkv hd hvP p np v nv hnp hnv hlow hv (fun l h0 h1 => ?_)
    obtain ⟨r, hrp, hrv, hrs⟩ := cK.pc.ker.pair p np v nv hnp hnv hv l h0 (by rw [hKcs]; exact h1)
    obtain ⟨nr, hnr⟩ := cK.pc.ker.isNode_owner p np hnp r hrp
    obtain ⟨x, hx, hxs⟩ := AmbTriCore.entry_at cK r nr hnr (n : Int) (by omega) (by rw [hKcs]; omega)
    exact ⟨r, hrp, hrv, hrs, nr, hnr, x, hx, LineUnion.gowner_pinned kv'.2 _ x (cK.pc.ker.own r nr hnr x hx) kv.1
      List.mem_cons_self (by rw [hxs, hkn])⟩
  obtain ⟨nP, hnP, _⟩ := tri p (TriPinCut.self_own_pc cK.pc p np hnp)
  refine ⟨nP, hnP, fun v hv => ?_⟩
  obtain ⟨nP', hnP', hvP'⟩ := tri v hv
  rw [hnP] at hnP'; cases hnP'; exact hvP'

/-- **The reader decides `φ` under `M1aAll` and `KTriK` at every join.** -/
theorem readerVerdictW_iff_of_kTriK
    (hA : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1aAll φ n)
    (hT : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → KTriK φ n) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_own φ hbd hA (fun n h1 hn => m1bLowOwn_of_kTriK φ hbd n (hT n h1 hn))

end AbsSatBin.GraphPath.Model.M1bOwn

/-- info: 'AbsSatBin.GraphPath.Model.M1bOwn.readerVerdictW_iff_of_kTriK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.M1bOwn.readerVerdictW_iff_of_kTriK
