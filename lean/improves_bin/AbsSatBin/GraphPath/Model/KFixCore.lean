-- lean/improves_bin/AbsSatBin/GraphPath/Model/KFixCore.lean
import AbsSatBin.GraphPath.Model.M1bOwn

/-!
# `KFix`: what a set closed for the key already gives (`docs/context/escalera_reader.md` §4.2ο.2)

Let `G` be a valid pinned joined state of line `n+1` and `S` a set of links of `G` closed for the key `k` (`KClosed`:
every link has, at every step, a witness owning a node of `k`, linked to both ends inside `S`).

* **`witness_key`**: the witness at the key row is itself a node of `k`. A node of step `n` owns only itself at
  step `n` (OOS), so the node of `k` it owns is itself.
* **`pure_link`**: a link from any node to a pure node (a node of step `n` or `n+1` that lives only in the piece of `k`)
  is a link of the piece of `k`.
* **`kFix_of_low`**: so `KFix` only asks about links between two nodes below step `n` (**`KFixLow`**). A link to step
  `n` ends at a node of `k`; a link to the top ends at a node whose parent is a node of `k`; both are pure.
-/

namespace AbsSatBin.GraphPath.Model.KFixCore

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.M1Parts
open AbsSatBin.GraphPath.Model.M1bOwn

variable (φ : Cnf) (hbd : Bounded φ)

/-- **`KFix` between the lower rows**: the same statement, for links whose two ends are below step `n`. -/
def KFixLow (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ ps : List NodeId, isValid (filterAll kv'.2 ps) = true →
    ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
      ∀ S, KClosed (filterAll kv'.2 ps) kv.1 ((n : Int) + 2) S →
        ∀ p v, S p v → p.id.step < (n : Int) → v.id.step < (n : Int) →
          ∃ nP, (upF φ kv.2 kv'.1).node? p = some nP ∧ v ∈ nP.owners

include hbd

omit hbd in
/-- **The witness at the key row is a node of the key.** -/
theorem witness_key (n : Nat) (G : GPathM) (cG : AmbTriCore.ACtx G)
    (k : NodeId) (hk : k.step = (n : Int)) (S : PathNodeId → PathNodeId → Prop) (hS : KClosed G k ((n : Int) + 2) S)
    (a b : PathNodeId) (hab : S a b) : ∃ x, x.id = k ∧ S a x ∧ S b x := by
  obtain ⟨_, _, _, _, hw⟩ := hS a b hab
  obtain ⟨r, hrs, har, hbr, nr, hnr, x, hx, hxk⟩ := hw (n : Int) (by omega) (by omega)
  have hrid : nr.id = r := node?_id_eq G r nr hnr
  have e := cG.pc.oos nr (List.mem_of_find?_eq_some hnr) x hx (by rw [hrid, hxk, hk, hrs])
  rw [hrid] at e
  exact ⟨r, by rw [← e, hxk], har, hbr⟩

/-- **A link to a pure node is a link of the piece.** `y` lives in `J` only through the piece of `kv`, so its table
there is its table in the piece; the piece is symmetric. -/
theorem pure_link (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (kv : NodeId × GPathM)
    (hkv : kv ∈ line φ n) (hd : kv'.1 ∈ sonsOfMap φ kv.1) (hvP : isValid (upF φ kv.2 kv'.1) = true)
    (ps : List NodeId) (hv : isValid (filterAll kv'.2 ps) = true) (y : PathNodeId)
    (hpure : ∀ kv2 ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv2.1 → isValid (upF φ kv2.2 kv'.1) = true →
      ∀ n2, (upF φ kv2.2 kv'.1).node? y = some n2 → kv2 = kv)
    (a : PathNodeId) (na : PNodeM) (hna : (filterAll kv'.2 ps).node? a = some na) (hya : y ∈ na.owners) :
    ∃ nP, (upF φ kv.2 kv'.1).node? a = some nP ∧ y ∈ nP.owners := by
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have cG := filt_ctx φ hbd _ kv' hok' ps hv
  have hbG := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') ps
  have pcP := piece_pinCtx φ hbd n kv hkv kv'.1 hd hvP
  obtain ⟨ny, hny⟩ := cG.pc.ker.isNode_owner a na hna y hya
  have hay := cG.pc.ker.sym a na y ny hna hny hya
  obtain ⟨nJ, hnJ, hoJ, _, _⟩ := hbG.node y ny hny
  obtain ⟨nPy, hnPy, hoP, _, _⟩ := pure_node φ n kv' hkv' kv y nJ hnJ hpure
  have hayP : a ∈ nPy.owners := hoP a (hoJ a hay)
  obtain ⟨nPa, hnPa⟩ := pcP.ker.isNode_owner y nPy hnPy a hayP
  exact ⟨nPa, hnPa, pcP.ker.sym y nPy a nPa hnPy hnPa hayP⟩

/-- **`KFixLow ⇒ KFix`**: a link to step `n` ends at a node of the key, and a link to the top ends at a son of a node
of the key; both are pure. -/
theorem kFix_of_low (n : Nat) (hL : KFixLow φ n) : KFix φ n := by
  intro kv' hkv' ps hv kv hkv hd hvP S hS p v hpv hps
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have cG := filt_ctx φ hbd _ kv' hok' ps hv
  have hbG := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') ps
  have hGcs : (filterAll kv'.2 ps).current_step = (n : Int) + 2 := by rw [← hbG.step, hcs']
  have hkn : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 ((lineOk φ n).2 kv hkv).onMap
  obtain ⟨np, hnp, hvp, ⟨nv, hnv⟩, _⟩ := hS p v hpv
  have hvr := CertFix.step_range cG.pc v nv hnv
  rw [hGcs] at hvr
  by_cases hlow : v.id.step < (n : Int)
  · exact hL kv' hkv' ps hv kv hkv hd hvP S hS p v hpv hps hlow
  · -- the witness at the key row is a node `x` of the key, linked to `v`
    obtain ⟨x, hxk, _, hvx⟩ := witness_key n _ cG kv.1 hkn S hS p v hpv
    obtain ⟨nv', hnv', hxv, _, _⟩ := hS v x hvx
    rw [hnv] at hnv'; cases hnv'
    have hvid : nv.id = v := node?_id_eq _ v nv hnv
    by_cases hmid : v.id.step = (n : Int)
    · -- `v` is at the key row: it owns only itself there, so `v = x` is a node of the key
      have e := cG.pc.oos nv (List.mem_of_find?_eq_some hnv) x hxv (by rw [hvid, hxk, hkn, hmid])
      rw [hvid] at e
      subst e
      exact pure_link φ hbd n kv' hkv' kv hkv hd hvP ps hv x
        (pure_mid φ hbd n kv' kv hkv x hmid hxk) p np hnp hvp
    · -- `v` is at the top: its entry at the key row names its parent, a node of the key
      have htop : v.id.step = (n : Int) + 1 := by omega
      have hxs : x.id.step = v.id.step - 1 := by rw [hxk, hkn, htop]; omega
      have hpar := AmbTriCore.parentId_of_owner cG v nv hnv (by omega) x hxv hxs
      rw [hxk] at hpar
      exact pure_link φ hbd n kv' hkv' kv hkv hd hvP ps hv v
        (pure_top φ hbd n kv' kv hkv v htop hpar.symm) p np hnp hvp

/-- **The reader decides `φ` under `M1aAll` and `KFixLow` at every join.** -/
theorem readerVerdictW_iff_of_kFixLow
    (hA : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1aAll φ n)
    (hL : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → KFixLow φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_kFix φ hbd hA (fun n h1 hn => kFix_of_low φ hbd n (hL n h1 hn))

end AbsSatBin.GraphPath.Model.KFixCore

/-- info: 'AbsSatBin.GraphPath.Model.KFixCore.readerVerdictW_iff_of_kFixLow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.KFixCore.readerVerdictW_iff_of_kFixLow
