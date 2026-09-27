-- lean/improves_bin/AbsSatBin/GraphPath/Model/M1bDeep.lean
import AbsSatBin.GraphPath.Model.M1bSrc

/-!
# Step 3 of the truncated form: `M1bSrc` one row lower (`docs/context/escalera_reader.md` §4.2ο.2)

`J` is a joined state of line `n+1`, `k = kv.1` a key of its key row `n`, `X = kv.2` the state of line `n` at `k`, and
`K` the joined state pinned at `k` and `ps`. The source `X` is itself a joined state: the union of its pieces
`Q_i = upF W_i k`, one per key `i` of row `n-1` (`W_i` the state of line `n-1` at `i`).

* **`CoverSplit`** (measured without failure, `split_probe.jl`, 23,3 M links): `K` is the union of its pins at row `n-1`:
  every entry `(p, v)` of `K` with `p` below row `n-1` is an entry of `K` pinned also at some key `i` of row `n-1`.
* **`M1bDeep`**: the same statement as `M1bSrc` one row lower: the entries below row `n` of the lower nodes of the state
  pinned at `k` and `i` are entries of the piece `Q_i`.
* **`m1bSrc_of_cover`**: `CoverSplit ∧ M1bDeep ⇒ M1bSrc`. An entry `(p, v)` of `K`:
  * `v` at row `n` is a node of the key, pure: its table is the piece's, hence the source's; the source is symmetric;
  * `p` below row `n-1`: `CoverSplit` gives `i`, `M1bDeep` puts the entry in `Q_i`, and `Q_i` lies below `X`;
  * `p` at row `n-1`: `v = p`, or the symmetric entry `(v, p)` falls in the case before.
* **`readerVerdictW_iff_of_cover`**: the reader decides under `M1aAll`, `CoverSplit` and `M1bDeep` at every join.
-/

namespace AbsSatBin.GraphPath.Model.M1bDeep

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.M1Parts
open AbsSatBin.GraphPath.Model.M1bSrc

variable (φ : Cnf) (hbd : Bounded φ)

/-- **`K` is the union of its pins at row `n-1`.** -/
def CoverSplit (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
    ∀ ps : List NodeId, isValid (filterAll kv'.2 (kv.1 :: ps)) = true →
      ∀ p np, (filterAll kv'.2 (kv.1 :: ps)).node? p = some np → p.id.step < (n : Int) - 1 →
        ∀ v ∈ np.owners, v.id.step < (n : Int) →
          ∃ x ∈ (filterAll kv'.2 (kv.1 :: ps)).gowners, x.id.step = (n : Int) - 1 ∧
            isValid (filterAll kv'.2 (kv.1 :: x.id :: ps)) = true ∧
            ∃ n2, (filterAll kv'.2 (kv.1 :: x.id :: ps)).node? p = some n2 ∧ v ∈ n2.owners

/-- **`M1bSrc` one row lower**: pinned at the key `k` and at a key `i` of row `n-1`, the entries below row `n` of the nodes
below row `n-1` are entries of the piece of `i` in the source of `k`. -/
def M1bDeep (n : Nat) : Prop :=
  ∀ m : Nat, n = m + 1 →
  ∀ kv' ∈ line φ (n + 1), ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
    ∀ w ∈ line φ m, kv.1 ∈ sonsOfMap φ w.1 → isValid (upF φ w.2 kv.1) = true →
      ∀ ps : List NodeId, isValid (filterAll kv'.2 (kv.1 :: w.1 :: ps)) = true →
        ∀ p np, (filterAll kv'.2 (kv.1 :: w.1 :: ps)).node? p = some np → p.id.step < (n : Int) - 1 →
          ∀ v ∈ np.owners, v.id.step < (n : Int) → ∃ nQ, (upF φ w.2 kv.1).node? p = some nQ ∧ v ∈ nQ.owners

include hbd

/-- **`CoverSplit ∧ M1bDeep ⇒ M1bSrc`.** -/
theorem m1bSrc_of_cover (n : Nat) (hn1 : 1 ≤ n) (hC : CoverSplit φ n) (hD : M1bDeep φ n) : M1bSrc φ n := by
  intro kv' hkv' kv hkv hd hvP ps hvK p np hnp hpn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hok' := (lineOk φ (m + 1 + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = ((m + 1 : Nat) : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hok := (lineOk φ (m + 1)).2 kv hkv
  have hkn : kv.1.step = ((m + 1 : Nat) : Int) := mapNodes_step φ _ kv.1 hok.onMap
  have cK := filt_ctx φ hbd _ kv' hok' (kv.1 :: ps) hvK
  have hbJK := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') (kv.1 :: ps)
  have hKcs : (filterAll kv'.2 (kv.1 :: ps)).current_step = ((m + 1 : Nat) : Int) + 2 := by rw [← hbJK.step, hcs']
  obtain ⟨_, hdst, hXcs, _, hvF, hndX⟩ := src_ctx φ hbd (m + 1) kv hkv kv'.1 hd hvP
  have cF := filt_ctx φ hbd _ kv hok (reqOf φ kv'.1) hvF
  have hbXF := KernelIff.below_filterAll_self kv.2 hndX (reqOf φ kv'.1)
  have pcX := line_pinCtx φ hbd (m + 1) kv hkv
  -- every node of `K` up to the key row is a node of the source
  have nodeX : ∀ q nq, (filterAll kv'.2 (kv.1 :: ps)).node? q = some nq → q.id.step ≤ ((m + 1 : Nat) : Int) →
      ∃ nX, kv.2.node? q = some nX := by
    intro q nq hnq hqs
    obtain ⟨_, nF, hnF⟩ := node_in_piece φ hbd (m + 1) kv' hkv' kv hkv hd hvP ps hvK q nq hnq hqs
    obtain ⟨nX, hnX, _⟩ := hbXF.node q nF hnF
    exact ⟨nX, hnX⟩
  -- the lower entries through `CoverSplit` and `M1bDeep`, into a piece of the source
  have deep : ∀ q nq, (filterAll kv'.2 (kv.1 :: ps)).node? q = some nq → q.id.step < ((m + 1 : Nat) : Int) - 1 →
      ∀ u ∈ nq.owners, u.id.step < ((m + 1 : Nat) : Int) → ∀ nX, kv.2.node? q = some nX → u ∈ nX.owners := by
    intro q nq hnq hqs u hu hus nX hnX
    obtain ⟨x, hx, hxs, hvK2, n2, hn2, hun2⟩ := hC kv' hkv' kv hkv hd hvP ps hvK q nq hnq hqs u hu hus
    -- the key `x.id` names a source of `X`
    obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (cK.pc.ker.gn x hx)
    obtain ⟨nXx, hnXx⟩ := nodeX x nx hnx (by omega)
    obtain ⟨w, hw, hdw, hvQ, hxw, _⟩ := PieceJoin.mid_one_source φ hbd m kv hkv x nXx hnXx (by push_cast at hxs ⊢; omega)
    rw [hxw] at hn2 hvK2
    obtain ⟨nQ, hnQ, huQ⟩ := hD m rfl kv' hkv' kv hkv hd hvP w hw hdw hvQ ps hvK2 q n2 hn2 hqs u hun2 hus
    -- the piece lies below the source
    obtain ⟨h, hh, hg⟩ := PieceJoin.piece_grown φ m w hw kv.1 hdw hvQ
    have heq : (kv.1, h) = kv := key_inj _ (lineOk φ (m + 1)).1 _ hh kv hkv rfl
    have hbXQ : Below kv.2 (upF φ w.2 kv.1) := by rw [← heq]; exact PieceFilter.below_of_grown hg
    obtain ⟨nX', hnX', hoX, _, _⟩ := hbXQ.node q nQ hnQ
    rw [hnX] at hnX'; cases hnX'
    exact hoX u huQ
  obtain ⟨nX, hnX⟩ := nodeX p np hnp (by omega)
  refine ⟨nX, hnX, fun v hv hvs => ?_⟩
  have hnpid : np.id = p := node?_id_eq _ p np hnp
  obtain ⟨nv, hnv⟩ := cK.pc.ker.isNode_owner p np hnp v hv
  by_cases hvn : v.id.step = ((m + 1 : Nat) : Int)
  · -- `v` at the key row: a node of the key, pure; its table is the piece's, hence the source's
    have hvk : v.id = kv.1 := LineUnion.gowner_pinned kv'.2 _ v (cK.pc.ker.own p np hnp v hv) kv.1
      List.mem_cons_self (by rw [hvn, hkn])
    have hpv := cK.pc.ker.sym p np v nv hnp hnv hv
    obtain ⟨nvJ, hnvJ, hoJ, _, _⟩ := hbJK.node v nv hnv
    obtain ⟨nPv, hnPv, hoP, _, _⟩ :=
      pure_node φ (m + 1) kv' hkv' kv v nvJ hnvJ (pure_mid φ hbd (m + 1) kv' kv hkv v hvn hvk)
    obtain ⟨nFv, hnFv, hoF⟩ := upF_old φ kv.2 kv'.1 hdst cF hvP v nPv hnPv (by rw [hXcs]; omega)
    obtain ⟨nXv, hnXv, hoXv, _, _⟩ := hbXF.node v nFv hnFv
    have hpXv : p ∈ nXv.owners := hoXv p (hoF p (hoP p (hoJ p hpv)) (by rw [hXcs]; omega))
    exact pcX.ker.sym v nXv p nX hnXv hnX hpXv
  · have hvlt : v.id.step < ((m + 1 : Nat) : Int) := by omega
    by_cases hplow : p.id.step < ((m + 1 : Nat) : Int) - 1
    · exact deep p np hnp hplow v hv hvlt nX hnX
    · -- `p` at row `n-1`
      have hprow : p.id.step = ((m + 1 : Nat) : Int) - 1 := by omega
      by_cases hvrow : v.id.step = ((m + 1 : Nat) : Int) - 1
      · have e := cK.pc.oos np (List.mem_of_find?_eq_some hnp) v hv (by rw [hnpid, hvrow, hprow])
        rw [hnpid] at e
        rw [e]; exact TriPinCut.self_own_pc pcX p nX hnX
      · -- the symmetric entry `(v, p)`, with `v` below row `n-1`
        have hpv := cK.pc.ker.sym p np v nv hnp hnv hv
        obtain ⟨nXv, hnXv⟩ := nodeX v nv hnv (by omega)
        have hpXv := deep v nv hnv (by omega) p hpv (by omega) nXv hnXv
        exact pcX.ker.sym v nXv p nX hnXv hnX hpXv

/-- **The reader decides `φ` under `M1aAll`, `CoverSplit` and `M1bDeep` at every join.** -/
theorem readerVerdictW_iff_of_cover
    (hA : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1aAll φ n)
    (hC : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → CoverSplit φ n)
    (hD : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1bDeep φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_src φ hbd hA (fun n h1 hn => m1bSrc_of_cover φ hbd n h1 (hC n h1 hn) (hD n h1 hn))

end AbsSatBin.GraphPath.Model.M1bDeep

/-- info: 'AbsSatBin.GraphPath.Model.M1bDeep.readerVerdictW_iff_of_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.M1bDeep.readerVerdictW_iff_of_cover
