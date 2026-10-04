-- lean/improves_bin/AbsSatBin/GraphPath/Model/M1bChain.lean
import AbsSatBin.GraphPath.Model.TruncN
import AbsSatBin.GraphPath.Model.M1bDeep

/-!
# The chain form of M1b: every row reduces to CoverSplit (`docs/context/escalera_reader.md` §4.2ο.2)

`J` is a joined state of line `n+1`, pinned by a list `L`. For a row `m ≤ n`, let `S` be the state of line `m` whose key
is pinned in `L`.

* **`SrcAt n m`**: the entries up to row `m` of the nodes below row `m` of `J` pinned by `L` are entries of `S`.
  `SrcAt n n` is `M1bSrc` (`m1bSrc_of_srcAt`); `SrcAt n 0` holds trivially.
* **`CoverRow n m`**: the pinned state is the union of its pins at row `m-1` (CoverSplit, at any row): every entry of a
  node below row `m-1` (up to row `m-1`) is an entry of the state pinned, validly, also at some key of row `m-1`.
* **`srcAt_succ`**: `SrcAt n m ∧ CoverRow n (m+1) ⇒ SrcAt n (m+1)`. With `k` the pinned key of row `m+1` and `S` its
  state:
  * an entry towards a node of `k` is an entry of `S`, by the node's history (`NodeHistory.node_history`);
  * for the other entries, `CoverRow` adds a key `j` of row `m` with its state `W` (the piece `Q = upF W k` is part of
    `S`). The state pinned also at `j`, cut down to row `m+1` (`TruncN.truncN`), is a kernel `H`:
    * `H` cut once more lies below `W` (`SrcAt n m` and the history of the nodes of `j`), and it respects the
      requirements of `k` (they are pinned in `S`, `line_node_req`), so it lies below `W` filtered for `k`;
    * `H` lies below the UP of its own cut (`UpSelf.below_up_trunc`), hence below the UP of `W` filtered, hence below
      `Q` (the review never goes below a kernel), hence below `S`.
* **`readerVerdictW_iff_of_chain`**: **the reader decides `φ` under `M1aAll` and `CoverRow` at every row of every
  join.**
-/

namespace AbsSatBin.GraphPath.Model.M1bChain

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
open AbsSatBin.GraphPath.Model.TruncN

variable (φ : Cnf) (hbd : Bounded φ)

/-- **The pinned state at row `m` lies in the state of its pinned key.** -/
def SrcAt (n m : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ L : List NodeId, isValid (filterAll kv'.2 L) = true →
    ∀ S ∈ line φ m, S.1 ∈ L →
      ∀ p np, (filterAll kv'.2 L).node? p = some np → p.id.step < (m : Int) →
        ∀ v ∈ np.owners, v.id.step ≤ (m : Int) → ∃ nS, S.2.node? p = some nS ∧ v ∈ nS.owners

/-- **CoverSplit at row `m-1`**, for a state pinned at a key of row `m`. -/
def CoverRow (n m : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ L : List NodeId, isValid (filterAll kv'.2 L) = true →
    ∀ S ∈ line φ m, S.1 ∈ L →
      ∀ p np, (filterAll kv'.2 L).node? p = some np → p.id.step < (m : Int) - 1 →
        ∀ v ∈ np.owners, v.id.step < (m : Int) →
          ∃ x ∈ (filterAll kv'.2 L).gowners, x.id.step = (m : Int) - 1 ∧
            isValid (filterAll kv'.2 (x.id :: L)) = true ∧
            ∃ n2, (filterAll kv'.2 (x.id :: L)).node? p = some n2 ∧ v ∈ n2.owners

include hbd

/-- The pinned state carries the context. -/
theorem good_pinned (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (L : List NodeId)
    (hv : isValid (filterAll kv'.2 L) = true) : Good (isProhibited φ) (filterAll kv'.2 L) := by
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have c := filt_ctx φ hbd _ kv' hok' L hv
  exact ⟨c.pc, c.rc, MapReachable.NoForb_of_pruned _ (pruned_filterAll kv'.2 L)
    (MapReachable.noForb_of_mapReachable φ kv'.2 hok'.reach)⟩

/-- **History at a pinned key**: the table of a node of the pinned key, up to its row, is its table in the key's state. -/
theorem hist_key (n m : Nat) (hm : m ≤ n + 1) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1))
    (L : List NodeId) (S : NodeId × GPathM) (hS : S ∈ line φ m)
    (t : PathNodeId) (nt : PNodeM) (hnt : (filterAll kv'.2 L).node? t = some nt) (htk : t.id = S.1) :
    ∃ ns, S.2.node? t = some ns ∧ ∀ u ∈ nt.owners, u.id.step ≤ (m : Int) → u ∈ ns.owners := by
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hbJK := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') L
  obtain ⟨nJ, hnJ, hoJ, _, _⟩ := hbJK.node t nt hnt
  have htm : t.id.step = (m : Int) := by rw [htk]; exact mapNodes_step φ m S.1 ((lineOk φ m).2 S hS).onMap
  obtain ⟨kvm, hkvm, hkey, ns, hns, _, how⟩ := NodeHistory.node_history φ hbd (n + 1) kv' hkv' t nJ hnJ m htm hm
  have e : kvm = S := key_inj _ (lineOk φ m).1 kvm hkvm S hS (by rw [hkey, htk])
  subst e
  exact ⟨ns, hns, fun u hu hus => how u (hoJ u hu) hus⟩

/-- **One row up.** -/
theorem srcAt_succ (n m : Nat) (hmn : m + 1 ≤ n) (hS : SrcAt φ n m) (hC : CoverRow φ n (m + 1)) :
    SrcAt φ n (m + 1) := by
  intro kv' hkv' L hvK S hSl hSL p np hnp hp v hv hvs
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have gK := good_pinned φ hbd n kv' hkv' L hvK
  have cK := filt_ctx φ hbd _ kv' hok' L hvK
  have hbJK := KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') L
  have hKcs : (filterAll kv'.2 L).current_step = (n : Int) + 2 := by rw [← hbJK.step, hcs']
  have hkM : S.1.step = ((m + 1 : Nat) : Int) := mapNodes_step φ _ S.1 ((lineOk φ (m + 1)).2 S hSl).onMap
  have pcS := line_pinCtx φ hbd (m + 1) S hSl
  -- the node of the key at row `m+1` owned by a node of `K`, and that node's place in `S`
  have atKey : ∀ q nq, (filterAll kv'.2 L).node? q = some nq → q.id.step ≤ ((m + 1 : Nat) : Int) →
      ∃ nSq, S.2.node? q = some nSq := by
    intro q nq hnq hqs
    obtain ⟨x, hx, hxs⟩ := AmbTriCore.entry_at cK q nq hnq ((m + 1 : Nat) : Int) (by omega)
      (by rw [hKcs]; push_cast; omega)
    have hxk : x.id = S.1 := LineUnion.gowner_pinned kv'.2 L x (cK.pc.ker.own q nq hnq x hx) S.1 hSL (by rw [hxs, hkM])
    obtain ⟨nx, hnx⟩ := cK.pc.ker.isNode_owner q nq hnq x hx
    obtain ⟨nSx, hnSx, hoSx⟩ := hist_key φ hbd n (m + 1) (by omega) kv' hkv' L S hSl x nx hnx hxk
    exact pcS.ker.isNode_owner x nSx hnSx q (hoSx q (cK.pc.ker.sym q nq x nx hnq hnx hx) hqs)
  -- the lower entries, through a key of row `m`
  have deep : ∀ q nq, (filterAll kv'.2 L).node? q = some nq → q.id.step < (m : Int) →
      ∀ u ∈ nq.owners, u.id.step < ((m + 1 : Nat) : Int) → ∀ nSq, S.2.node? q = some nSq → u ∈ nSq.owners := by
    intro q nq hnq hq u hu hus nSq hnSq
    obtain ⟨x, hx, hxs, hvK', n2, hn2, hu2⟩ :=
      hC kv' hkv' L hvK S hSl hSL q nq hnq (by push_cast; omega) u hu (by exact hus)
    -- the state `W` of the key `x.id`, a source of `S`
    obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (cK.pc.ker.gn x hx)
    obtain ⟨nSx, hnSx⟩ := atKey x nx hnx (by rw [hxs]; push_cast; omega)
    obtain ⟨W, hW, hdW, hvQ, hxW, _⟩ :=
      PieceJoin.mid_one_source φ hbd m S hSl x nSx hnSx (by rw [hxs]; push_cast; omega)
    rw [hxW] at hn2 hvK'
    -- `K'`: pinned also at `W.1`; `H`: `K'` cut down to row `m+1`
    let K' := filterAll kv'.2 (W.1 :: L)
    have gK' := good_pinned φ hbd n kv' hkv' _ hvK'
    have hK'cs : K'.current_step = (n : Int) + 2 := by
      rw [← (KernelIff.below_filterAll_self kv'.2 (FExtInd.nodup_ok φ hbd _ kv' hok') (W.1 :: L)).step, hcs']
    obtain ⟨j, hj⟩ : ∃ j : Nat, j + m = n := ⟨n - m, by omega⟩
    let H := truncN j K'
    have gH := good_truncN j K' gK'
    have hHcs : H.current_step = ((m + 1 : Nat) : Int) + 1 := by
      have e1 : (truncN j K').current_step = K'.current_step - (j : Int) := truncN_cs j K'
      show (truncN j K').current_step = _
      push_cast
      omega
    -- `H`'s top row carries the key
    have htop : ∀ t nt, H.node? t = some nt → t.id.step = H.current_step - 1 → t.id = S.1 := by
      intro t nt hnt hts
      obtain ⟨n0, hn0, _, _, _⟩ := truncN_node_inv j K' t nt hnt
      exact LineUnion.gowner_pinned kv'.2 _ t (gK'.pc.ker.gow t n0 hn0) S.1 (List.mem_cons_of_mem _ hSL)
        (by rw [hts, hHcs, hkM]; omega)
    have ctx : UpSelf.Ctx H S.1 (isProhibited φ) :=
      ⟨gH.pc, gH.rc, htop, by rw [hHcs, hkM]; omega, by rw [hHcs]; omega, gH.nf⟩
    have hbUH := UpSelf.below_up_trunc ctx ""
    -- the cut of `H` lies below `W`
    have pcW := line_pinCtx φ hbd m W hW
    have gT := good_trunc gH
    have hTcs : (Trunc.trunc H).current_step = ((m + 1 : Nat) : Int) := by
      show H.current_step - 1 = _; rw [hHcs]; omega
    have hWcs : W.2.current_step = (m : Int) + 1 := ((lineOk φ m).2 W hW).step
    -- a node of the cut of `H` is a node of `K'` below row `m+1`
    have toK' : ∀ r nr, (Trunc.trunc H).node? r = some nr → ∃ n0, K'.node? r = some n0 ∧
        (∀ v ∈ nr.owners, v ∈ n0.owners) ∧ r.id.step ≤ (m : Int) := by
      intro r nr hnr
      obtain ⟨nH, hnH, hrs, rfl⟩ := Trunc.trunc_node?_some H r nr hnr
      obtain ⟨n0, hn0, ho0, _, _⟩ := truncN_node_inv j K' r nH hnH
      have hrb := gH.pc.below nH (List.mem_of_find?_eq_some hnH)
      rw [node?_id_eq H r nH hnH, hHcs] at hrb
      rw [hHcs] at hrs
      exact ⟨n0, hn0, fun v hv => ho0 v ((Trunc.mem_cutTop_owners _ _ v).mp hv).1, by push_cast at hrb hrs ⊢; omega⟩
    have hbWT : Below W.2 (Trunc.trunc H) := by
      refine below_of_owners pcW gT.pc (by rw [hWcs, hTcs]; push_cast; rfl) (fun r nr hnr => ?_)
      obtain ⟨n0, hn0, ho0, hrs⟩ := toK' r nr hnr
      have hob : ∀ v ∈ nr.owners, v.id.step ≤ (m : Int) := by
        intro v hv
        have := gT.rc.ownb nr (List.mem_of_find?_eq_some hnr) v hv
        rw [hTcs] at this; push_cast at this; omega
      by_cases hrm : r.id.step < (m : Int)
      · obtain ⟨nW, hnW, _⟩ := hS kv' hkv' _ hvK' W hW List.mem_cons_self r n0 hn0 hrm r
          (TriPinCut.self_own_pc gK'.pc r n0 hn0) (by omega)
        refine ⟨nW, hnW, fun v hv => ?_⟩
        obtain ⟨nW', hnW', hvW⟩ := hS kv' hkv' _ hvK' W hW List.mem_cons_self r n0 hn0 hrm v (ho0 v hv) (hob v hv)
        rw [hnW] at hnW'; cases hnW'; exact hvW
      · -- a node of the key `W.1` at row `m`: its history
        have hrk : r.id = W.1 := LineUnion.gowner_pinned kv'.2 _ r (gK'.pc.ker.gow r n0 hn0) W.1 List.mem_cons_self
          (by rw [mapNodes_step φ m W.1 ((lineOk φ m).2 W hW).onMap]; omega)
        obtain ⟨nW, hnW, hoW⟩ := hist_key φ hbd n m (by omega) kv' hkv' _ W hW r n0 hn0 hrk
        exact ⟨nW, hnW, fun v hv => hoW v (ho0 v hv) (hob v hv)⟩
    -- it respects the requirements of the key: they are pinned in `S`
    have hpinT : ∀ r ∈ reqOf φ S.1, ∀ g ∈ (Trunc.trunc H).gowners, g.id.step = r.step → g.id = r := by
      intro r hr g hg hgs
      obtain ⟨ng, hng⟩ := Option.isSome_iff_exists.mp (gT.pc.ker.gn g hg)
      obtain ⟨n0, hn0, _, hgs'⟩ := toK' g ng hng
      obtain ⟨nSg, hnSg⟩ : ∃ nSg, S.2.node? g = some nSg := by
        obtain ⟨y, hy, hys⟩ := AmbTriCore.entry_at ⟨gK'.pc, gK'.rc⟩ g n0 hn0 ((m + 1 : Nat) : Int) (by omega)
          (by rw [hK'cs]; push_cast; omega)
        have hyk : y.id = S.1 := LineUnion.gowner_pinned kv'.2 _ y (gK'.pc.ker.own g n0 hn0 y hy) S.1
          (List.mem_cons_of_mem _ hSL) (by rw [hys, hkM])
        obtain ⟨ny, hny⟩ := gK'.pc.ker.isNode_owner g n0 hn0 y hy
        obtain ⟨nSy, hnSy, hoSy⟩ := hist_key φ hbd n (m + 1) (by omega) kv' hkv' _ S hSl y ny hny hyk
        exact pcS.ker.isNode_owner y nSy hnSy g (hoSy g (gK'.pc.ker.sym g n0 y ny hn0 hny hy) (by push_cast; omega))
      exact line_node_req φ hbd m S hSl g nSg hnSg (by push_cast; omega) r hr hgs
    -- below `W` filtered, below its UP, below the piece `Q`, below `S`
    obtain ⟨_, hdst, hWcs', _, hvF, hndW⟩ := src_ctx φ hbd m W hW S.1 hdW hvQ
    have cF := filt_ctx φ hbd m W ((lineOk φ m).2 W hW) (reqOf φ S.1) hvF
    have hbFT : Below (filterAll W.2 (reqOf φ S.1)) (Trunc.trunc H) :=
      below_filterAll gT.pc.ker hbWT (reqOf φ S.1) hpinT
    have hFcs : (filterAll W.2 (reqOf φ S.1)).current_step = (m : Int) + 1 := by
      rw [← (KernelIff.below_filterAll_self W.2 hndW (reqOf φ S.1)).step, hWcs]
    have hbAA := UpMono.below_addNode hbFT S.1 "" (isProhibited φ) (by rw [hFcs, hkM]; push_cast; rfl)
      cF.pc.below gT.pc.below
    have hbAH := PieceFilter.below_trans hbAA hbUH
    have hbQH : Below (upF φ W.2 S.1) H := by
      rcases (upF_shape φ W.2 S.1 hvQ).2 with e | e
      · rw [e]; exact hbAH
      · rw [e]; exact below_review gH.pc.ker hbAH
    obtain ⟨h, hh, hg⟩ := PieceJoin.piece_grown φ m W hW S.1 hdW hvQ
    have heq : (S.1, h) = S := key_inj _ (lineOk φ (m + 1)).1 _ hh S hSl rfl
    have hbSQ : Below S.2 (upF φ W.2 S.1) := by rw [← heq]; exact PieceFilter.below_of_grown hg
    have hbSH := PieceFilter.below_trans hbSQ hbQH
    -- the entry, in `H`, in `S`
    obtain ⟨nH, hnH, hoH⟩ := truncN_node_of j K' q n2 hn2 (by rw [hK'cs]; push_cast; omega)
    obtain ⟨nS', hnS', hoS', _, _⟩ := hbSH.node q nH hnH
    rw [hnSq] at hnS'; cases hnS'
    exact hoS' u (hoH u hu2 (by rw [hK'cs]; push_cast at hus ⊢; omega))
  -- assemble
  obtain ⟨nSp, hnSp⟩ := atKey p np hnp (by push_cast at hp ⊢; omega)
  refine ⟨nSp, hnSp, ?_⟩
  obtain ⟨nv, hnv⟩ := cK.pc.ker.isNode_owner p np hnp v hv
  have hnpid : np.id = p := node?_id_eq _ p np hnp
  by_cases hvM : v.id.step = ((m + 1 : Nat) : Int)
  · -- `v` is a node of the key: its history
    have hvk : v.id = S.1 := LineUnion.gowner_pinned kv'.2 L v (cK.pc.ker.own p np hnp v hv) S.1 hSL (by rw [hvM, hkM])
    obtain ⟨nSv, hnSv, hoSv⟩ := hist_key φ hbd n (m + 1) (by omega) kv' hkv' L S hSl v nv hnv hvk
    have hpS := hoSv p (cK.pc.ker.sym p np v nv hnp hnv hv) (by omega)
    exact pcS.ker.sym v nSv p nSp hnSv hnSp hpS
  · have hvlt : v.id.step < ((m + 1 : Nat) : Int) := by omega
    by_cases hpm : p.id.step < (m : Int)
    · exact deep p np hnp hpm v hv hvlt nSp hnSp
    · have hprow : p.id.step = (m : Int) := by push_cast at hp; omega
      by_cases hvrow : v.id.step = (m : Int)
      · have e := cK.pc.oos np (List.mem_of_find?_eq_some hnp) v hv (by rw [hnpid, hvrow, hprow])
        rw [hnpid] at e
        rw [e]; exact TriPinCut.self_own_pc pcS p nSp hnSp
      · obtain ⟨nSv, hnSv⟩ := atKey v nv hnv (by omega)
        have hpv := cK.pc.ker.sym p np v nv hnp hnv hv
        have hpSv := deep v nv hnv (by omega) p hpv (by push_cast; omega) nSv hnSv
        exact pcS.ker.sym v nSv p nSp hnSv hnSp hpSv

/-- `SrcAt n 0` holds: nothing is below row `0`. -/
theorem srcAt_zero (n : Nat) : SrcAt φ n 0 := by
  intro kv' hkv' L hvK _ _ _ p np hnp hp
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have cK := filt_ctx φ hbd _ kv' hok' L hvK
  have := cK.pc.snn np (List.mem_of_find?_eq_some hnp)
  rw [node?_id_eq _ p np hnp] at this
  push_cast at hp
  omega

/-- **`SrcAt` at every row**, under `CoverRow` at every row. -/
theorem srcAt_all (n : Nat) (hC : ∀ m : Nat, 1 ≤ m → m ≤ n → CoverRow φ n m) : ∀ m : Nat, m ≤ n → SrcAt φ n m := by
  intro m
  induction m with
  | zero => intro _; exact srcAt_zero φ hbd n
  | succ m ih => intro hm; exact srcAt_succ φ hbd n m hm (ih (by omega)) (hC (m + 1) (by omega) hm)

/-- `SrcAt n n` is `M1bSrc n`. -/
theorem m1bSrc_of_srcAt (n : Nat) (h : SrcAt φ n n) : M1bSrc φ n := by
  intro kv' hkv' kv hkv _ _ ps hvK p np hnp hp
  obtain ⟨nX, hnX, _⟩ := h kv' hkv' _ hvK kv hkv List.mem_cons_self p np hnp hp p
    (TriPinCut.self_own_pc (filt_ctx φ hbd _ kv' ((lineOk φ (n + 1)).2 kv' hkv') _ hvK).pc p np hnp) (by omega)
  refine ⟨nX, hnX, fun v hv hvs => ?_⟩
  obtain ⟨nX', hnX', hvX⟩ := h kv' hkv' _ hvK kv hkv List.mem_cons_self p np hnp hp v hv hvs
  rw [hnX] at hnX'; cases hnX'; exact hvX

/-- **The reader decides `φ` under `M1aAll` and `CoverRow` at every row of every join.** -/
theorem readerVerdictW_iff_of_chain
    (hA : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → M1aAll φ n)
    (hC : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → ∀ m : Nat, 1 ≤ m → m ≤ n → CoverRow φ n m) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_src φ hbd hA (fun n h1 hn => m1bSrc_of_srcAt φ hbd n (srcAt_all φ hbd n (hC n h1 hn) n (Nat.le_refl n)))

end AbsSatBin.GraphPath.Model.M1bChain

/-- info: 'AbsSatBin.GraphPath.Model.M1bChain.readerVerdictW_iff_of_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.M1bChain.readerVerdictW_iff_of_chain
