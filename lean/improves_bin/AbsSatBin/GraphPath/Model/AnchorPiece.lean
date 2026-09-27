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
* **S2 from the line union** (`topPieceF_of_lua`, line `n ≥ 1`): the top member `w` gives its place to a parent `c`
  (`single_parent`, or `TopMergeJ` at a merge); the filtered joined state without its top row is a kernel inside the
  union of the sources, pinned by the destination's requirements and by `R` below the top; **LUA** (anchored locality of
  the line union: measured on the unfiltered union, 179 k, no failure) puts `c :: Q₀` in the source of `c`, filtered
  so; `FCert` of the source (the induction hypothesis) gives a certificate, which climbs through `up` with `w` and
  survives `R`. The filter `R` goes down through `below_filterAll` at the union: no FU, no anchored filter rule (AF).
* **Line 0** (`line_one`, `topPieceF_zero`): with one source, sending only appends (`sendTo_fold`), so every state of
  line 1 is its piece and S2 holds there.
* **`readerVerdictW_iff_of_lua`**: by induction on the line, the reader decides under A1, LUA, `TopMergeJ` and
  `MergeSplit`. `TopMergeJ` comes from `MergeSplitJ` (`merge_pin`, the pin of a grandparent, in any filtered state).
* **The merge in a piece from AF** (`topParent_of_afp`): a top node fixes the map node one step under its parents
  (`gparent_owner`); AF pins it; `cert_piece_low` then gives a certificate whose extension is `w` whichever parent it
  took. **`readerVerdictW_iff_of_afp`**: the reader decides under A1, LUA, `MergeSplitJ` and AF in the pieces.
* **A1 from ULUA** (`anchorF_of_ulua`, with `climb`): if a clique with witnesses of the truncated filtered joined state
  is one of some pinned source (ULUA, the unanchored line union), the source's certificate climbs to its piece and to
  the joined state, and its top node anchors the clique. At line 0, `anchorF_zero`. **`readerVerdictW_iff_of_ulua`**:
  the reader decides under ULUA, LUA, `MergeSplitJ` and AF in the pieces.
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


-- ============================================================
-- S2 from the line union (LUA) and a parent at the top
-- ============================================================

omit hbd in
/-- **A certificate through `Q` covering every step makes `Q` a clique with witnesses of a valid state.** -/
theorem good_of_chain {g : GPathM} (sel : Int → PathNodeId) (hs : ChainSound g sel) (Q : List PathNodeId)
    (hon : ∀ q ∈ Q, 0 ≤ q.id.step ∧ q.id.step < g.current_step ∧ sel q.id.step = q) :
    isValid g = true ∧ Clique g Q ∧ Wit g Q := by
  refine ⟨?_, fun p hp => ?_, fun l h0 h1 => ?_⟩
  · unfold isValid
    refine List.all_eq_true.mpr (fun l hl => ?_)
    have h0 := mem_intRange_lower hl
    have h1 := mem_intRange_upper hl
    exact List.any_eq_true.mpr ⟨sel l, hs.chain.2.2 l h0 (by omega), beq_iff_eq.mpr (hs.chain.1.1 l h0 (by omega)).2⟩
  · obtain ⟨hp0, hp1, hpe⟩ := hon p hp
    obtain ⟨np, hnp, _⟩ := GrowCert.chain_owns hs p.id.step p.id.step hp0 hp1 hp0 hp1
    rw [hpe] at hnp
    refine ⟨np, hnp, fun t ht => ?_⟩
    obtain ⟨ht0, ht1, hte⟩ := hon t ht
    obtain ⟨n', hn', ho⟩ := GrowCert.chain_owns hs p.id.step t.id.step hp0 hp1 ht0 ht1
    rw [hpe, hnp] at hn'; cases hn'
    rw [hte] at ho; exact ho
  · obtain ⟨nr, hnr, _⟩ := GrowCert.chain_owns hs l l h0 h1 h0 h1
    refine ⟨sel l, nr, hnr, (hs.chain.1.1 l h0 h1).2, fun t ht => ?_⟩
    obtain ⟨ht0, ht1, hte⟩ := hon t ht
    obtain ⟨n', hn', ho⟩ := GrowCert.chain_owns hs l t.id.step h0 h1 ht0 ht1
    rw [hnr] at hn'; cases hn'
    rw [hte] at ho; exact ho

omit hbd in
/-- **A node at step `≥ 1` of a kernel either merges (two parents) or hands its clique with witnesses to its parent.** -/
theorem parent_or_merge {g : GPathM} (c : AmbTriCore.ACtx g) (w : PathNodeId) (nw : PNodeM)
    (hnw : g.node? w = some nw) (hw1 : 1 ≤ w.id.step) (Q0 : List PathNodeId) (hQ : Clique g (w :: Q0))
    (hW : Wit g (w :: Q0)) :
    (∃ c₁ ∈ nw.parents, ∃ c₂ ∈ nw.parents, c₁ ≠ c₂) ∨
      ∃ cp ∈ nw.parents, Clique g (cp :: Q0) ∧ Wit g (cp :: Q0) := by
  have hwmem := List.mem_of_find?_eq_some hnw
  have hwid : nw.id = w := node?_id_eq _ w nw hnw
  by_cases hm : ∃ c₁ ∈ nw.parents, ∃ c₂ ∈ nw.parents, c₁ ≠ c₂
  · exact Or.inl hm
  · have hnr : nw.id.parent_id ≠ none := c.rc.shape.notroot nw hwmem (by rw [hwid]; omega)
    obtain ⟨cp, hcp⟩ : ∃ cp, cp ∈ nw.parents := by
      rcases ((Kernel.isValidNode_iff _ nw).mp (c.pc.ker.valid w nw hnw)).2.1 with h' | h'
      · exact absurd (Option.isNone_iff_eq_none.mp h') hnr
      · exact List.exists_mem_of_ne_nil _ h'
    have hone : ∀ c' ∈ nw.parents, c' = cp := by
      intro c' hc'
      by_cases e : c' = cp
      · exact e
      · exact absurd ⟨c', hc', cp, hcp, e⟩ hm
    obtain ⟨h1, h2⟩ := single_parent c.pc w nw hnw hw1 cp hone Q0 hQ hW
    exact Or.inr ⟨cp, hcp, h1, h2⟩

omit hbd in
/-- **`TopMergeJ n`**: in a filtered joined state of line `n+1`, a clique with witnesses whose top member `w` comes
from a merge hands itself to one of `w`'s parents. (Without a merge this is `single_parent`.) -/
def TopMergeJ : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < kv'.2.current_step) →
    isValid (filterAll kv'.2 R) = true → ∀ w Q0, Clique (filterAll kv'.2 R) (w :: Q0) →
      Wit (filterAll kv'.2 R) (w :: Q0) → w.id.step = (n : Int) + 1 → (∀ q ∈ Q0, q.id.step ≤ n) →
      ∀ nw, (filterAll kv'.2 R).node? w = some nw → (∃ c₁ ∈ nw.parents, ∃ c₂ ∈ nw.parents, c₁ ≠ c₂) →
      ∃ cp ∈ nw.parents, Clique (filterAll kv'.2 R) (cp :: Q0) ∧ Wit (filterAll kv'.2 R) (cp :: Q0)

omit hbd in
/-- **Pinning a grandparent leaves one parent** (any filtered state): if `w :: Q0` is a clique with witnesses of `X`
filtered by `ps ++ [u]`, with `u` three steps under `w`, then some parent of `w` in `X` filtered by `ps` takes `w`'s place.
Every parent of `w` there owns, two steps down, a node named `u`, so its grandparent is `u` (`gparent_owner`); the
parents share id and parent (`PMP`, `GPMP`), so there is one; `single_parent`; the pinned state sits below the
unpinned one. -/
theorem merge_pin {X : GPathM} (hnd : NodupIds X) (ps : List NodeId) (u : NodeId)
    (cU : AmbTriCore.ACtx (filterAll X (ps ++ [u]))) (hu0 : 0 ≤ u.step) (hult : u.step < X.current_step)
    (w : PathNodeId) (Q0 : List PathNodeId) (hus : u.step = w.id.step - 3)
    (hQU : Clique (filterAll X (ps ++ [u])) (w :: Q0)) (hWU : Wit (filterAll X (ps ++ [u])) (w :: Q0))
    (nw : PNodeM) (hnw : (filterAll X ps).node? w = some nw) :
    ∃ c ∈ nw.parents, Clique (filterAll X ps) (c :: Q0) ∧ Wit (filterAll X ps) (c :: Q0) := by
  have hUcs : (filterAll X (ps ++ [u])).current_step = X.current_step := (pruned_filterAll _ _).step_eq
  have hBF : Kernel.Below (filterAll X ps) (filterAll X (ps ++ [u])) :=
    Kernel.below_filterAll cU.pc.ker (KernelIff.below_filterAll_self _ hnd (ps ++ [u])) ps
      (fun r hr q hq hqs => LineUnion.gowner_pinned _ _ q hq r (List.mem_append_left _ hr) hqs)
  obtain ⟨nw1, hnw1, _⟩ := hQU w List.mem_cons_self
  have hw1m := List.mem_of_find?_eq_some hnw1
  have hw1id : nw1.id = w := node?_id_eq _ w nw1 hnw1
  have hpar : ∀ c' ∈ nw1.parents, c'.gparent_id = some u ∧ some c'.id = w.parent_id ∧ w.gparent_id = c'.parent_id := by
    intro c' hc'
    obtain ⟨_, nc', hnc', _⟩ := cU.pc.ker.linkP w nw1 hnw1 c' hc'
    have hc's : c'.id.step = w.id.step - 1 := by
      have := cU.pc.pb nw1 hw1m c' hc'; rw [hw1id] at this; exact this
    have hval := ((Kernel.isValidNode_iff _ nc').mp (cU.pc.ker.valid c' nc' hnc')).1
    obtain ⟨e, he, hes⟩ := List.any_eq_true.mp (List.all_eq_true.mp hval u.step
      (mem_intRange_zero u.step _ hu0 (by rw [hUcs]; exact hult)))
    have hes' : e.id.step = u.step := eq_of_beq hes
    have heu := LineUnion.gowner_pinned _ _ e (cU.pc.ker.own c' nc' hnc' e he) u (List.mem_append_right _
      List.mem_cons_self) hes'
    have hg := gparent_owner cU c' nc' hnc' (show 2 ≤ c'.id.step by rw [hc's]; omega) e he
      (show e.id.step = c'.id.step - 2 by rw [hes', hus, hc's]; omega)
    rw [heu] at hg
    refine ⟨hg, ?_, ?_⟩
    · have := cU.rc.pmp nw1 hw1m c' hc'; rw [hw1id] at this; exact this
    · have := cU.rc.gpmp.1 nw1 hw1m c' hc'; rw [hw1id] at this; exact this
  have hnr : nw1.id.parent_id ≠ none := cU.rc.shape.notroot nw1 hw1m (by rw [hw1id]; omega)
  obtain ⟨cp, hcp⟩ : ∃ cp, cp ∈ nw1.parents := by
    rcases ((Kernel.isValidNode_iff _ nw1).mp (cU.pc.ker.valid w nw1 hnw1)).2.1 with h' | h'
    · exact absurd (Option.isNone_iff_eq_none.mp h') hnr
    · exact List.exists_mem_of_ne_nil _ h'
  have hone : ∀ c' ∈ nw1.parents, c' = cp := by
    intro c' hc'
    obtain ⟨g1, i1, p1⟩ := hpar c' hc'
    obtain ⟨g2, i2, p2⟩ := hpar cp hcp
    have hid : c'.id = cp.id := Option.some.inj (i1.trans i2.symm)
    have hpi : c'.parent_id = cp.parent_id := p1.symm.trans p2
    have hgp : c'.gparent_id = cp.gparent_id := g1.trans g2.symm
    revert hid hpi hgp
    cases c' with
    | mk a b e => cases cp with
      | mk a' b' e' => intro hid hpi hgp; simp only at hid hpi hgp; rw [hid, hpi, hgp]
  obtain ⟨hQc, hWc⟩ := single_parent cU.pc w nw1 hnw1 (by omega) cp hone Q0 hQU hWU
  obtain ⟨nx, hnx, _, hpx, _⟩ := hBF.node w nw1 hnw1
  rw [hnw] at hnx; cases hnx
  refine ⟨cp, hpx cp hcp, fun p hp => ?_, fun l h0 h1 => ?_⟩
  · obtain ⟨np, hnp, ho⟩ := hQc p hp
    obtain ⟨nx, hnx, hox, _, _⟩ := hBF.node p np hnp
    exact ⟨nx, hnx, fun s hs => hox s (ho s hs)⟩
  · obtain ⟨r, nr, hnr', hrs, ho⟩ := hWc l h0 (by rw [← hBF.step]; exact h1)
    obtain ⟨nx, hnx, hox, _, _⟩ := hBF.node r nr hnr'
    exact ⟨r, nx, hnx, hrs, fun s hs => hox s (ho s hs)⟩

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.merge_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms merge_pin

omit hbd in
/-- **`MergeSplitJ n`**: `MergeSplit` in a filtered joined state of line `n+1`: a clique with witnesses whose top
member `w` comes from a merge survives the filter by the grandparent `u` of one of `w`'s parents (step `n-2`). -/
def MergeSplitJ : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < kv'.2.current_step) →
    isValid (filterAll kv'.2 R) = true → ∀ w Q0, Clique (filterAll kv'.2 R) (w :: Q0) →
      Wit (filterAll kv'.2 R) (w :: Q0) → w.id.step = (n : Int) + 1 → (∀ q ∈ Q0, q.id.step ≤ n) →
      ∀ nw, (filterAll kv'.2 R).node? w = some nw → (∃ c₁ ∈ nw.parents, ∃ c₂ ∈ nw.parents, c₁ ≠ c₂) →
      ∃ u : NodeId, (∃ c ∈ nw.parents, c.gparent_id = some u) ∧ 0 ≤ u.step ∧ u.step = (n : Int) - 2 ∧
        isValid (filterAll kv'.2 (R ++ [u])) = true ∧
        Clique (filterAll kv'.2 (R ++ [u])) (w :: Q0) ∧ Wit (filterAll kv'.2 (R ++ [u])) (w :: Q0)

/-- **`TopMergeJ` from `MergeSplitJ`** (`merge_pin` in the joined state). -/
theorem topMergeJ_of_mergeSplitJ (hMS : MergeSplitJ φ n) : TopMergeJ φ n := by
  intro kv' hkv' R hR hv w Q0 hQ hW hws hlow nw hnw hm
  obtain ⟨u, _, hu0, hus, hvU, hQU, hWU⟩ := hMS kv' hkv' R hR hv w Q0 hQ hW hws hlow nw hnw hm
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hnd' := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hok'.reach)
  have hcsJ : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  exact merge_pin hnd' R u (filt_ctx φ hbd _ kv' hok' _ hvU) hu0 (by rw [hcsJ]; omega) w Q0
    (by rw [hus, hws]; omega) hQU hWU nw hnw

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.topMergeJ_of_mergeSplitJ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topMergeJ_of_mergeSplitJ

omit hbd in
/-- **LUA n** (anchored locality of the union of line `n`, filtered): a kernel of the steps of line `n` whose entries
are all entries of states of line `n`, pinned by `S`, in which `c :: Q0` is a clique with witnesses with `c` at the top
step `n`, puts that clique in the state of `c`'s key filtered by `S`. -/
def LUA : Prop :=
  ∀ S : List NodeId, (∀ p ∈ S, 0 ≤ p.step ∧ p.step ≤ n) → ∀ K : GPathM, Kernel.Kernel K →
    K.current_step = (n : Int) + 1 →
    (∀ p nk, K.node? p = some nk → ∀ v ∈ nk.owners, ∃ kv ∈ line φ n, ∃ nx, kv.2.node? p = some nx ∧ v ∈ nx.owners) →
    (∀ r ∈ S, ∀ q ∈ K.gowners, q.id.step = r.step → q.id = r) →
    ∀ c Q0, Clique K (c :: Q0) → Wit K (c :: Q0) → c.id.step = n →
    ∀ kv ∈ line φ n, kv.1 = c.id →
      isValid (filterAll kv.2 S) = true ∧ Clique (filterAll kv.2 S) (c :: Q0) ∧ Wit (filterAll kv.2 S) (c :: Q0)

/-- **S2 from LUA** (line `n ≥ 1`). The top member `w` gives its place to a parent `c` (`single_parent`, or
`TopMergeJ` at a merge). The joined state filtered by `R`, without its top row, is a kernel whose entries are entries of
the sources and which is pinned by the requirements of the destination and by `R` below the top; LUA puts `c :: Q₀` in
the source of `c`'s key filtered so. There `FCert` gives a certificate; it climbs through `up` with `w` (the shift of
`c`, not prohibited since `w` exists) and survives `R`, and a certificate through `w :: Q` makes it a clique with
witnesses of the filtered piece. -/
theorem topPieceF_of_lua (hn1 : 1 ≤ n) (hL : LUA φ n) (hTM : TopMergeJ φ n)
    (hX : ∀ kv ∈ line φ n, FCert kv.2) : TopPieceF φ n := by
  intro kv' hkv' R hR hv w Q hQ hW hws kv hkv hd hvp hpar
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hreach' := MapReachable.reachable_of_mapReachable φ hbd _ hok'.reach
  have hnd' := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach'
  have cF := filt_ctx φ hbd _ kv' hok' R hv
  have hbJ := KernelIff.below_filterAll_self kv'.2 hnd' R
  have hcsJ : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hFcs : (filterAll kv'.2 R).current_step = (n : Int) + 2 := by rw [← hbJ.step, hcsJ]
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvp
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)
  have hSFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : kv'.1.step = (filterAll kv.2 (reqOf φ kv'.1)).current_step := by rw [hSFcs, ← hcs, hdst]
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvp
  have hPcs : (upF φ kv.2 kv'.1).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  -- the members below the top
  have hsub0 : ∀ q ∈ w :: Q.filter (fun q => decide (q.id.step ≤ (n : Int))), q ∈ w :: Q := by
    intro q hq
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mp hq).1
  obtain ⟨hQ0, hW0⟩ := good_sub hsub0 hQ hW
  have hlow0 : ∀ q ∈ Q.filter (fun q => decide (q.id.step ≤ (n : Int))), q.id.step ≤ n :=
    fun q hq => of_decide_eq_true (List.mem_filter.mp hq).2
  obtain ⟨nw, hnw, hwown⟩ := hQ w List.mem_cons_self
  have hwmem := List.mem_of_find?_eq_some hnw
  have hwid : nw.id = w := node?_id_eq _ w nw hnw
  -- a parent `cp` of `w` takes its place
  obtain ⟨cp, hcp, hQc, hWc⟩ : ∃ cp ∈ nw.parents, Clique (filterAll kv'.2 R)
      (cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) ∧
      Wit (filterAll kv'.2 R) (cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) := by
    rcases parent_or_merge cF w nw hnw (by rw [hws]; omega) _ hQ0 hW0 with hm | h
    · exact hTM kv' hkv' R hR hv w _ hQ0 hW0 hws hlow0 nw hnw hm
    · exact h
  have hcps : cp.id.step = (n : Int) := by
    have := cF.pc.pb nw hwmem cp hcp; rw [hwid, hws] at this; omega
  have hparc : some cp.id = w.parent_id := by
    have := cF.rc.pmp nw hwmem cp hcp; rw [hwid] at this; exact this
  have hgpar : w.gparent_id = cp.parent_id := by
    have := cF.rc.gpmp.1 nw hwmem cp hcp; rw [hwid] at this; exact this
  have hkey : kv.1 = cp.id := Option.some.inj (hpar.symm.trans hparc.symm)
  -- the truncated filtered joined state
  have hkT := Trunc.kernel_trunc cF.pc.ker cF.pc.pb cF.pc.sa cF.pc.below
  have hKcs : (Trunc.trunc (filterAll kv'.2 R)).current_step = (n : Int) + 1 := by
    show (filterAll kv'.2 R).current_step - 1 = _; rw [hFcs]; omega
  have toK : ∀ p np, (filterAll kv'.2 R).node? p = some np → p.id.step ≤ n →
      (Trunc.trunc (filterAll kv'.2 R)).node? p =
        some (Trunc.cutTop ((filterAll kv'.2 R).current_step - 1) np) :=
    fun p np hnp hps' => Trunc.trunc_node?_of _ p np hnp (by rw [hFcs]; omega)
  have hlowc : ∀ q ∈ cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int))), q.id.step ≤ n := by
    intro q hq
    rcases List.mem_cons.mp hq with e | hq
    · rw [e, hcps]; exact Int.le_refl _
    · exact hlow0 q hq
  have hQK : Clique (Trunc.trunc (filterAll kv'.2 R)) (cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) :=
    fun p hp => by
      obtain ⟨np, hnp, ho⟩ := hQc p hp
      exact ⟨_, toK p np hnp (hlowc p hp), fun s hs =>
        (Trunc.mem_cutTop_owners _ _ s).mpr ⟨ho s hs, by rw [hFcs]; have := hlowc s hs; omega⟩⟩
  have hWK : Wit (Trunc.trunc (filterAll kv'.2 R)) (cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) := by
    intro l h0 h1
    rw [hKcs] at h1
    obtain ⟨r, nr, hnr, hrs, ho⟩ := hWc l h0 (by rw [hFcs]; omega)
    exact ⟨r, _, toK r nr hnr (by omega), hrs, fun s hs =>
      (Trunc.mem_cutTop_owners _ _ s).mpr ⟨ho s hs, by rw [hFcs]; have := hlowc s hs; omega⟩⟩
  -- a node of the joined state below the top lives in a source, with its entries below the top
  have toSrc : ∀ p nJ, kv'.2.node? p = some nJ → p.id.step ≤ n → ∀ v ∈ nJ.owners, v.id.step ≤ n →
      ∃ kv0 ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv0.1 ∧ isValid (upF φ kv0.2 kv'.1) = true ∧
        ∃ nF0, (filterAll kv0.2 (reqOf φ kv'.1)).node? p = some nF0 ∧ v ∈ nF0.owners := by
    intro p nJ hnJ hps v hv hvs
    obtain ⟨kv0, hkv0, hd0, hv0, n', hn', hvn'⟩ := (PieceJoin.join_no_new φ n kv' hkv').2 p nJ hnJ v hv
    obtain ⟨hok0, hdst0, hcs0, _, hvF0, _⟩ := src_ctx φ hbd n kv0 hkv0 kv'.1 hd0 hv0
    have c0 := filt_ctx φ hbd n kv0 hok0 (reqOf φ kv'.1) hvF0
    obtain ⟨nF0, hnF0, ho0⟩ := upF_old φ kv0.2 kv'.1 hdst0 c0 hv0 p n' hn' (by rw [hcs0]; omega)
    exact ⟨kv0, hkv0, hd0, hv0, nF0, hnF0, ho0 v hvn' (by rw [hcs0]; omega)⟩
  have hunion : ∀ p nk, (Trunc.trunc (filterAll kv'.2 R)).node? p = some nk → ∀ v ∈ nk.owners,
      ∃ kv0 ∈ line φ n, ∃ nx, kv0.2.node? p = some nx ∧ v ∈ nx.owners := by
    intro p nk hnk v hv
    obtain ⟨nF, hnF, hps, rfl⟩ := Trunc.trunc_node?_some _ p nk hnk
    obtain ⟨hvF', hvs⟩ := (Trunc.mem_cutTop_owners _ _ v).mp hv
    have hpr := CertFix.step_range cF.pc p nF hnF
    rw [hFcs] at hpr hps hvs
    obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp (cF.pc.ker.gn v (cF.pc.ker.own p nF hnF v hvF'))
    have hvr := CertFix.step_range cF.pc v nv hnv
    rw [hFcs] at hvr
    obtain ⟨nJ, hnJ, hoJ, _, _⟩ := hbJ.node p nF hnF
    obtain ⟨kv0, hkv0, _, _, nF0, hnF0, hvo⟩ := toSrc p nJ hnJ (by omega) v (hoJ v hvF') (by omega)
    have hnd0 := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
      (MapReachable.reachable_of_mapReachable φ hbd _ ((lineOk φ n).2 kv0 hkv0).reach)
    obtain ⟨nx, hnx, hox, _, _⟩ := (KernelIff.below_filterAll_self kv0.2 hnd0 (reqOf φ kv'.1)).node p nF0 hnF0
    exact ⟨kv0, hkv0, nx, hnx, hox v hvo⟩
  -- the pins: the requirements of the destination and `R` below the top
  have hreqr : ∀ r ∈ reqOf φ kv'.1, 0 ≤ r.step ∧ r.step ≤ n := fun r hr =>
    ⟨reqOf_nonneg φ hbd kv'.1 r hr, by have := reqOf_backward φ hbd kv'.1 r hr; rw [hdst, hcs] at this; omega⟩
  have hSr : ∀ p ∈ reqOf φ kv'.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int))), 0 ≤ p.step ∧ p.step ≤ n := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hreqr p hp
    · obtain ⟨hp, hle⟩ := List.mem_filter.mp hp
      exact ⟨(hR p hp).1, of_decide_eq_true hle⟩
  have hpinK : ∀ r ∈ reqOf φ kv'.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int))),
      ∀ q ∈ (Trunc.trunc (filterAll kv'.2 R)).gowners, q.id.step = r.step → q.id = r := by
    intro r hr q hq hqs
    have hqF : q ∈ (filterAll kv'.2 R).gowners := (List.mem_filter.mp hq).1
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cF.pc.ker.gn q hqF)
      obtain ⟨nJ, hnJ, _, _, _⟩ := hbJ.node q nq hnq
      have hqs' : q.id.step ≤ n := by rw [hqs]; exact (hreqr r hr).2
      obtain ⟨kv0, hkv0, hd0, hv0, nF0, hnF0, _⟩ := toSrc q nJ hnJ hqs' q
        (by obtain ⟨nJ', hnJ', hoJ, _, _⟩ := hbJ.node q nq hnq
            rw [hnJ] at hnJ'; cases hnJ'
            exact hoJ q (TriPinCut.self_own_pc cF.pc q nq hnq)) hqs'
      obtain ⟨hok0, _, _, _, hvF0, _⟩ := src_ctx φ hbd n kv0 hkv0 kv'.1 hd0 hv0
      have c0 := filt_ctx φ hbd n kv0 hok0 (reqOf φ kv'.1) hvF0
      exact LineUnion.pinned_entry φ kv0.2 kv'.1 q (c0.pc.ker.gow q nF0 hnF0) r hr hqs
    · exact LineUnion.gowner_pinned kv'.2 R q hqF r (List.mem_filter.mp hr).1 hqs
  -- LUA puts the clique in the source of `cp`'s key, pinned
  obtain ⟨hvG, hQG, hWG⟩ := hL _ hSr _ hkT hKcs hunion hpinK cp _ hQK hWK hcps kv hkv hkey
  have hSr' : ∀ p ∈ reqOf φ kv'.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int))),
      0 ≤ p.step ∧ p.step < kv.2.current_step := fun p hp => ⟨(hSr p hp).1, by rw [hcs]; have := (hSr p hp).2; omega⟩
  obtain ⟨sel, hsG, hon⟩ := hX kv hkv _ hSr' hvG _ hQG hWG
  -- the certificate climbs
  have hsX : ChainSound kv.2 sel :=
    ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self kv.2 hnd _)) sel hsG
  have hpS := chain_pins kv.2 _ sel hsG
  have hreqs : ∀ req ∈ reqOf φ kv'.1, 0 ≤ req.step → req.step < kv.2.current_step → (sel req.step).id = req :=
    fun req hr h0 h1 => hpS req (List.mem_append_left _ hr) h0 h1
  have hmokX : MachineOk kv.2 := ⟨by rw [hok.step]; omega, fun h => by rw [hok.step] at h; omega,
    fun _ => by rw [hok.par]; simp⟩
  have hmok : MachineOk (filterAll kv.2 (reqOf φ kv'.1)) := MachineOk_of_pruned (pruned_filterAll _ _) hmokX
  have hpos : 0 < (filterAll kv.2 (reqOf φ kv'.1)).current_step := by omega
  have hselc : sel n = cp := by rw [← hcps]; exact hon cp List.mem_cons_self
  -- `w` is a node of the piece, so its window is allowed; it is the shift of `cp`
  obtain ⟨nJw, hnJw, _, _, _⟩ := hbJ.node w nw hnw
  obtain ⟨kv0, hkv0, hd0, hv0, nP0, hnP0⟩ := (PieceJoin.join_no_new φ n kv' hkv').1 w nJw hnJw
  have hk0 := StateGrow.row_parent_key φ hbd n kv0 hkv0 kv'.1 hd0 hv0 w nP0 hnP0 hws
  have he0 : kv0 = kv := key_inj _ (lineOk φ n).1 kv0 hkv0 kv hkv (Option.some.inj (hk0.symm.trans hpar))
  rw [he0] at hnP0
  have hwnew := (upF_new φ kv.2 kv'.1 hdst c hvp w nP0 hnP0 (by rw [hws, hcs])).1
  have hwd : w.id = kv'.1 := mapId_of_mem_newRowIds _ _ _ w hwnew
  have hshift : shiftPid cp kv'.1 = w := by
    unfold shiftPid
    revert hwd hparc hgpar
    cases w with
    | mk wi wp wg =>
      intro hwd hparc hgpar
      simp only at hwd hparc hgpar
      rw [hwd, hparc, hgpar]
  have hext : extendPid (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel = w := by
    unfold extendPid
    rw [if_pos hpos, hSFcs, show (n : Int) + 1 - 1 = n by omega, hselc, hshift]
  have hf : isProhibited φ (extendPid (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel) = false := by
    rw [hext]; exact not_forb_of_mem_newRowIds _ _ _ w hwnew
  have hsP : ChainSound (upF φ kv.2 kv'.1) (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel) :=
    ChainSound_upFiltering kv.2 (reqOf φ kv'.1) kv'.1 "" (isProhibited φ) hvF hdF c.pc.below hmok sel hsX hreqs hf
  have htop : extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel ((n : Int) + 1) = w := by
    rw [show (n : Int) + 1 = (filterAll kv.2 (reqOf φ kv'.1)).current_step by rw [hSFcs], extend_top, hext]
  have hlowsel : ∀ l, l ≤ (n : Int) → extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel l = sel l := by
    intro l hl
    unfold extend
    rw [if_neg (by rw [hSFcs]; omega)]
  -- it survives `R`
  have hpsP : ∀ r ∈ R, 0 ≤ r.step → r.step < (upF φ kv.2 kv'.1).current_step →
      (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel r.step).id = r := by
    intro r hr h0 h1
    rw [hPcs] at h1
    by_cases hrt : r.step = (n : Int) + 1
    · have hwr := LineUnion.gowner_pinned _ R w (cF.pc.ker.gow w nw hnw) r hr (by rw [hws, hrt])
      rw [hrt, htop]; exact hwr
    · rw [hlowsel r.step (by omega)]
      exact hpS r (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, decide_eq_true (by omega)⟩)) h0
        (by rw [hcs]; omega)
  have hsPR := ChainSound_filterAll _ R _ hsP hpsP
  have hPRcs : (filterAll (upF φ kv.2 kv'.1) R).current_step = (n : Int) + 2 := by
    rw [(pruned_filterAll _ R).step_eq, hPcs]
  -- the certificate goes through `w :: Q`
  refine good_of_chain _ hsPR (w :: Q) (fun q hq => ?_)
  rw [hPRcs]
  rcases List.mem_cons.mp hq with e | hq
  · rw [e, hws]; exact ⟨by omega, by omega, htop⟩
  · obtain ⟨nq, hnq, _⟩ := hQ q (List.mem_cons_of_mem _ hq)
    have hqr := CertFix.step_range cF.pc q nq hnq
    rw [hFcs] at hqr
    by_cases hqs : q.id.step ≤ (n : Int)
    · refine ⟨hqr.1, by omega, ?_⟩
      rw [hlowsel _ hqs]
      exact hon q (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hq, decide_eq_true hqs⟩))
    · have hqs' : q.id.step = (n : Int) + 1 := by omega
      have hqw : q = w := by
        have := cF.pc.oos nw hwmem q (hwown q (List.mem_cons_of_mem _ hq)) (by rw [hwid, hqs', hws])
        rw [hwid] at this; exact this
      rw [hqw, hws]; exact ⟨by omega, by omega, htop⟩

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.topPieceF_of_lua' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topPieceF_of_lua

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

-- ============================================================
-- Line 0: one source, so every state of line 1 is its piece
-- ============================================================

omit hbd n in
/-- **Sending one state to distinct new keys only appends**: every entry of the result is an old one or the state
filtered for its key. -/
theorem sendTo_fold (g : GPathM) : ∀ (ds : List NodeId) (acc : PureLine), ds.Nodup → (∀ kv ∈ acc, kv.1 ∉ ds) →
    ∀ kv ∈ ds.foldl (sendTo φ g) acc, kv ∈ acc ∨ kv = (kv.1, upFiltering g (reqOf φ kv.1) kv.1 "" (isProhibited φ)) := by
  intro ds
  induction ds with
  | nil => intro acc _ _ kv hkv; exact Or.inl hkv
  | cons d ds ih =>
    intro acc hnd hdis kv hkv
    simp only [List.foldl_cons] at hkv
    have hdn : d ∉ ds := (List.nodup_cons.mp hnd).1
    -- one step: `sendTo` appends `(d, …)` or does nothing
    have hstep : (∀ x ∈ sendTo φ g acc d, x ∈ acc ∨ x = (x.1, upFiltering g (reqOf φ x.1) x.1 "" (isProhibited φ))) ∧
        ∀ x ∈ sendTo φ g acc d, x.1 ∉ ds := by
      unfold sendTo
      split
      · have hnone : acc.find? (fun kv => kv.1 == d) = none := List.find?_eq_none.mpr (fun x hx h => by
          have := hdis x hx
          rw [eq_of_beq h] at this; exact this List.mem_cons_self)
        unfold insertPure; rw [hnone]
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl hx
          · rw [List.mem_singleton.mp hx]; exact Or.inr rfl
        · rcases List.mem_append.mp hx with hx | hx
          · exact fun h => hdis x hx (List.mem_cons_of_mem _ h)
          · rw [List.mem_singleton.mp hx]; exact hdn
      · exact ⟨fun x hx => Or.inl hx, fun x hx h => hdis x hx (List.mem_cons_of_mem _ h)⟩
    rcases ih _ (List.nodup_cons.mp hnd).2 hstep.2 kv hkv with h | h
    · rcases hstep.1 kv h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · exact Or.inr h

omit hbd n in
theorem sons_root_nodup : (sonsOfMap φ ⟨0, 0⟩).Nodup := by
  unfold sonsOfMap
  rw [if_neg (by simp)]
  show (mapNodes φ 1).Nodup
  unfold mapNodes
  repeat' split
  all_goals simp

omit hbd n in
/-- **Every state of line 1 is the piece of the seed for its key.** -/
theorem line_one (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ 1) :
    kv'.2 = upF φ (GPathM.initSeed ⟨0, 0⟩ "") kv'.1 := by
  have hm : mapNodes φ 0 = [⟨0, 0⟩] := mapNodes_fusion φ 0 (Or.inl rfl)
  have h0 : line φ 0 = [(⟨0, 0⟩, GPathM.initSeed ⟨0, 0⟩ "")] := by
    show pureInit φ = _
    unfold pureInit; rw [hm]; rfl
  have h1 : line φ 1 = sendAll φ (⟨0, 0⟩, GPathM.initSeed ⟨0, 0⟩ "") [] := by
    rw [show (1 : Nat) = 0 + 1 from rfl, line_succ, h0]; rfl
  rw [h1] at hkv'
  rcases sendTo_fold φ _ _ [] (sons_root_nodup φ) (fun _ h => absurd h List.not_mem_nil) kv' hkv' with h | h
  · exact absurd h List.not_mem_nil
  · exact congrArg Prod.snd h

omit hbd n in
/-- **S2 at line 0**: a state of line 1 is its only piece. -/
theorem topPieceF_zero : TopPieceF φ 0 := by
  intro kv' hkv' R _ hv w Q hQ hW _ kv hkv _ _ _
  have e := line_one φ kv' hkv'
  rw [line_zero φ kv hkv]
  rw [e] at hv hQ hW
  exact ⟨hv, hQ, hW⟩

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.topPieceF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topPieceF_zero

-- ============================================================
-- The merge in a piece, from the anchored filter
-- ============================================================

omit hbd in
/-- **AF in the pieces** (the anchored filter): in a filtered piece of line `n+1`, a clique with witnesses with a
member `w` at the top survives the filter by a map node `m` that `w` fixes (all of `w`'s entries at `m`'s step name
`m`). Measured in the states of the lines (`anchfilt_probe.jl`, 2.87 M, no failure). -/
def AFP : Prop :=
  ∀ kv ∈ line φ n, ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true →
    ∀ ps : List NodeId, (∀ p ∈ ps, 0 ≤ p.step ∧ p.step < (upF φ kv.2 d).current_step) →
      isValid (filterAll (upF φ kv.2 d) ps) = true →
      ∀ w Q0, Clique (filterAll (upF φ kv.2 d) ps) (w :: Q0) → Wit (filterAll (upF φ kv.2 d) ps) (w :: Q0) →
        w.id.step = (n : Int) + 1 → ∀ nw, (filterAll (upF φ kv.2 d) ps).node? w = some nw →
        ∀ m : NodeId, 0 ≤ m.step → m.step ≤ n → (∀ e ∈ nw.owners, e.id.step = m.step → e.id = m) →
          isValid (filterAll (upF φ kv.2 d) (ps ++ [m])) = true ∧
          Clique (filterAll (upF φ kv.2 d) (ps ++ [m])) (w :: Q0) ∧
          Wit (filterAll (upF φ kv.2 d) (ps ++ [m])) (w :: Q0)

/-- **`TopParent` from AF, merges included** (line `n ≥ 1`). A top node `w` fixes, one step under its parents, the map
node `g` named by its grandparent id (`gparent_owner`): the merge is only two steps under. AF pins `g`; there
`cert_piece_low` gives a certificate through the members below whose node at step `n` has parent `g` and key id, so its
extension is `w` whichever parent it took. The certificate survives back to the unpinned piece, and its node at step
`n` is the parent that takes `w`'s place. -/
theorem topParent_of_afp (hn1 : 1 ≤ n) (hAF : AFP φ n) : TopParent φ n := by
  intro kv hkv hX d hd hv ps hps hvP w Q0 hQ hW hws hlow
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hP : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hPcs : (upF φ kv.2 d).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hP.reach)
  have cQ := filt_ctx φ hbd _ (d, upF φ kv.2 d) hP ps hvP
  have hQcs : (filterAll (upF φ kv.2 d) ps).current_step = (n : Int) + 2 := by
    rw [(pruned_filterAll _ ps).step_eq, hPcs]
  obtain ⟨nw, hnw, _⟩ := hQ w List.mem_cons_self
  -- `w` fixes the map node `g` at step `n - 1`
  have hval := ((Kernel.isValidNode_iff _ nw).mp (cQ.pc.ker.valid w nw hnw)).1
  obtain ⟨e0, he0, he0s⟩ := List.any_eq_true.mp (List.all_eq_true.mp hval ((n : Int) - 1)
    (mem_intRange_zero _ _ (by omega) (by rw [hQcs]; omega)))
  have he0s' : e0.id.step = (n : Int) - 1 := eq_of_beq he0s
  have hg0 := gparent_owner cQ w nw hnw (by rw [hws]; omega) e0 he0 (by rw [he0s', hws]; omega)
  have hfix : ∀ e ∈ nw.owners, e.id.step = e0.id.step → e.id = e0.id := by
    intro e he hes
    have := gparent_owner cQ w nw hnw (by rw [hws]; omega) e he (by rw [hes, he0s', hws]; omega)
    exact Option.some.inj (this.symm.trans hg0)
  obtain ⟨hvG, hQG, hWG⟩ := hAF kv hkv d hd hv ps hps hvP w Q0 hQ hW hws nw hnw e0.id (by omega) (by omega) hfix
  have hps' : ∀ p ∈ ps ++ [e0.id], 0 ≤ p.step ∧ p.step < (upF φ kv.2 d).current_step := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hps p hp
    · rw [List.mem_singleton.mp hp, hPcs]; exact ⟨by omega, by omega⟩
  obtain ⟨hQ0, hW0⟩ := good_sub (fun q hq => List.mem_cons_of_mem w hq) hQG hWG
  obtain ⟨sel, hs, hon, htop⟩ := cert_piece_low φ hbd n hn1 kv hkv d hd hv hX (ps ++ [e0.id]) hps' hvG Q0 hQ0 hW0 hlow
  -- its node at step `n` has the key and parent `g`, so its extension is `w`
  have cG := filt_ctx φ hbd _ (d, upF φ kv.2 d) hP (ps ++ [e0.id]) hvG
  have hGcs : (filterAll (upF φ kv.2 d) (ps ++ [e0.id])).current_step = (n : Int) + 2 := by
    rw [(pruned_filterAll _ _).step_eq, hPcs]
  obtain ⟨nsn, hnsn⟩ := Option.isSome_iff_exists.mp (hs.chain.1.1 n (by omega) (by rw [hGcs]; omega)).1
  have hsns : (sel n).id.step = (n : Int) := (hs.chain.1.1 n (by omega) (by rw [hGcs]; omega)).2
  obtain ⟨nP, hnP, _, _, _⟩ := (KernelIff.below_filterAll_self _ hndP (ps ++ [e0.id])).node (sel n) nsn hnsn
  have hkey : (sel n).id = kv.1 := PieceJoin.mid_key φ hbd n kv hkv d hd hv (sel n) nP hnP hsns
  have hlink := hs.chain.1.2 ((n : Int) - 1) (by omega) (by rw [hGcs]; omega)
  rw [show (n : Int) - 1 + 1 = n by omega, hnsn] at hlink
  have hpm := cG.rc.pmp nsn (List.mem_of_find?_eq_some hnsn) _ hlink
  rw [node?_id_eq _ _ nsn hnsn] at hpm
  have hg1 : (sel ((n : Int) - 1)).id = e0.id := by
    have := chain_pins (upF φ kv.2 d) _ sel hs e0.id (List.mem_append_right _ List.mem_cons_self) (by omega)
      (by rw [hPcs]; omega)
    rw [he0s'] at this; exact this
  obtain ⟨nPw, hnPw, _, _, _⟩ := (KernelIff.below_filterAll_self _ hndP ps).node w nw hnw
  have hwd := mapId_of_mem_newRowIds _ _ _ w (upF_new φ kv.2 d hdst c hv w nPw hnPw (by rw [hws, hcs])).1
  have hwp := StateGrow.row_parent_key φ hbd n kv hkv d hd hv w nPw hnPw hws
  have hext : sel ((n : Int) + 1) = w := by
    rw [htop]
    unfold shiftPid
    rw [hkey, ← hpm, hg1]
    revert hwd hwp hg0
    cases w with
    | mk wi wp wg =>
      intro hwd hwp hg0
      simp only at hwd hwp hg0
      rw [hwd, hwp, hg0]
  -- back in the unpinned piece
  have hsP : ChainSound (upF φ kv.2 d) sel :=
    ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self _ hndP _)) sel hs
  have hsF := ChainSound_filterAll _ ps sel hsP (fun r hr h0 h1 =>
    chain_pins (upF φ kv.2 d) _ sel hs r (List.mem_append_left _ hr) h0 h1)
  have hcp : sel n ∈ nw.parents := by
    have := hsF.chain.1.2 n (by omega) (by rw [hQcs]; omega)
    rw [hext, hnw] at this; exact this
  refine ⟨sel n, nw, hnw, hcp, ?_⟩
  obtain ⟨_, h1, h2⟩ := good_of_chain sel hsF (sel n :: Q0) (fun q hq => by
    rw [hQcs]
    rcases List.mem_cons.mp hq with e | hq
    · rw [e, hsns]; exact ⟨by omega, by omega, rfl⟩
    · obtain ⟨nq, hnq, _⟩ := hQ q (List.mem_cons_of_mem _ hq)
      have := CertFix.step_range cQ.pc q nq hnq
      rw [hQcs] at this
      exact ⟨this.1, this.2, hon q hq⟩)
  exact ⟨h1, h2⟩

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.topParent_of_afp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topParent_of_afp

-- ============================================================
-- A1 from the unanchored line union (ULUA)
-- ============================================================

/-- **A certificate of the source pinned by `pinsW` and the pins below the top climbs to the filtered piece** (line
`n ≥ 1`), when every pin at the top is the destination. The tail of `cert_piece_low`, as a lemma. -/
theorem climb (hn1 : 1 ≤ n) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true)
    (ps : List NodeId) (htop : ∀ r ∈ ps, r.step = (n : Int) + 1 → r = d) (sel : Int → PathNodeId)
    (hsG : ChainSound (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int)))))
      sel) :
    ChainSound (filterAll (upF φ kv.2 d) ps) (extend (filterAll kv.2 (reqOf φ d)) d sel) ∧
      (∀ l, l ≤ (n : Int) → extend (filterAll kv.2 (reqOf φ d)) d sel l = sel l) := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hP : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hPcs : (upF φ kv.2 d).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hsX : ChainSound kv.2 sel :=
    ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self kv.2 hnd _)) sel hsG
  have hpS := chain_pins kv.2 _ sel hsG
  have hreqs : ∀ req ∈ reqOf φ d, 0 ≤ req.step → req.step < kv.2.current_step → (sel req.step).id = req :=
    fun req hr h0 h1 => hpS req (List.mem_append_left _ (reqOf_sub_pinsW φ n d kv.1 req hr)) h0 h1
  have hsF := ChainSound_filterAll kv.2 (reqOf φ d) sel hsX hreqs
  have hmokX : MachineOk kv.2 := ⟨by rw [hok.step]; omega, fun h => by rw [hok.step] at h; omega,
    fun _ => by rw [hok.par]; simp⟩
  have hmok : MachineOk (filterAll kv.2 (reqOf φ d)) := MachineOk_of_pruned (pruned_filterAll _ _) hmokX
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
  have hsP : ChainSound (upF φ kv.2 d) (extend (filterAll kv.2 (reqOf φ d)) d sel) :=
    ChainSound_upFiltering kv.2 (reqOf φ d) d "" (isProhibited φ) hvF hdF c.pc.below hmok sel hsX hreqs hf
  have hlow : ∀ l, l ≤ (n : Int) → extend (filterAll kv.2 (reqOf φ d)) d sel l = sel l := by
    intro l hl; unfold extend; rw [if_neg (by rw [hFcs]; omega)]
  refine ⟨ChainSound_filterAll _ ps _ hsP (fun r hr h0 h1 => ?_), hlow⟩
  rw [hPcs] at h1
  by_cases hrt : r.step = (n : Int) + 1
  · rw [hrt, ← hFcs, extend_top, extendPid_mapId]; exact (htop r hr hrt).symm
  · rw [hlow r.step (by omega)]
    exact hpS r (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, decide_eq_true (by omega)⟩)) h0
      (by rw [hcs]; omega)

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.climb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms climb

omit hbd in
/-- **ULUA n** (the unanchored line union): a clique with witnesses of a filtered joined state of line `n+1`, below
its top, is (in its truncation) one of some source sent to the destination, pinned by `pinsW` and `R` below the top. -/
def ULUA : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < kv'.2.current_step) →
    isValid (filterAll kv'.2 R) = true → ∀ Q, Clique (Trunc.trunc (filterAll kv'.2 R)) Q →
      Wit (Trunc.trunc (filterAll kv'.2 R)) Q → (∀ q ∈ Q, q.id.step ≤ n) →
      ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 kv'.1) = true ∧
        isValid (filterAll kv.2 (LineUnion.pinsW φ n kv'.1 kv.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int)))))
          = true ∧
        Clique (filterAll kv.2 (LineUnion.pinsW φ n kv'.1 kv.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int))))) Q ∧
        Wit (filterAll kv.2 (LineUnion.pinsW φ n kv'.1 kv.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int))))) Q

/-- **A1 from ULUA** (line `n ≥ 1`): the source's certificate through `Q` climbs to its piece filtered by `R`, then to the
joined state; its node at the top anchors the clique. -/
theorem anchorF_of_ulua (hn1 : 1 ≤ n) (hU : ULUA φ n) (hX : ∀ kv ∈ line φ n, FCert kv.2) : AnchorF φ n := by
  intro kv' hkv' R hR hv Q hQ hW hlow
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hreach' := MapReachable.reachable_of_mapReachable φ hbd _ hok'.reach
  have hnd' := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach'
  have cF := filt_ctx φ hbd _ kv' hok' R hv
  have hbJ := KernelIff.below_filterAll_self kv'.2 hnd' R
  have hcsJ : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hFcs : (filterAll kv'.2 R).current_step = (n : Int) + 2 := by rw [← hbJ.step, hcsJ]
  have hKcs : (Trunc.trunc (filterAll kv'.2 R)).current_step = (n : Int) + 1 := by
    show (filterAll kv'.2 R).current_step - 1 = _; rw [hFcs]; omega
  have toK : ∀ p np, (filterAll kv'.2 R).node? p = some np → p.id.step ≤ n →
      (Trunc.trunc (filterAll kv'.2 R)).node? p =
        some (Trunc.cutTop ((filterAll kv'.2 R).current_step - 1) np) :=
    fun p np hnp hps' => Trunc.trunc_node?_of _ p np hnp (by rw [hFcs]; omega)
  have hQK : Clique (Trunc.trunc (filterAll kv'.2 R)) Q := fun p hp => by
    obtain ⟨np, hnp, ho⟩ := hQ p hp
    exact ⟨_, toK p np hnp (hlow p hp), fun s hs =>
      (Trunc.mem_cutTop_owners _ _ s).mpr ⟨ho s hs, by rw [hFcs]; have := hlow s hs; omega⟩⟩
  have hWK : Wit (Trunc.trunc (filterAll kv'.2 R)) Q := by
    intro l h0 h1
    rw [hKcs] at h1
    obtain ⟨r, nr, hnr, hrs, ho⟩ := hW l h0 (by rw [hFcs]; omega)
    exact ⟨r, _, toK r nr hnr (by omega), hrs, fun s hs =>
      (Trunc.mem_cutTop_owners _ _ s).mpr ⟨ho s hs, by rw [hFcs]; have := hlow s hs; omega⟩⟩
  obtain ⟨kv, hkv, hd, hvp, hvG, hQG, hWG⟩ := hU kv' hkv' R hR hv Q hQK hWK hlow
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvp
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  -- the pins of the source are inside its steps
  have hSr : ∀ p ∈ LineUnion.pinsW φ n kv'.1 kv.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int))),
      0 ≤ p.step ∧ p.step < kv.2.current_step := by
    intro p hp
    rw [hcs]
    have hreq : ∀ r ∈ reqOf φ kv'.1, 0 ≤ r.step ∧ r.step < (n : Int) + 1 := fun r hr =>
      ⟨reqOf_nonneg φ hbd kv'.1 r hr, by have := reqOf_backward φ hbd kv'.1 r hr; rw [hdst, hcs] at this; exact this⟩
    rcases List.mem_append.mp hp with hp | hp
    · unfold LineUnion.pinsW at hp
      split at hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact hreq p hp
        · rw [List.mem_singleton.mp hp]
          exact ⟨by show (0 : Int) ≤ (n : Int) - 1; omega, by show (n : Int) - 1 < (n : Int) + 1; omega⟩
      · exact hreq p hp
    · obtain ⟨hp, hle⟩ := List.mem_filter.mp hp
      exact ⟨(hR p hp).1, by have := of_decide_eq_true hle; omega⟩
  obtain ⟨sel, hsG, hon⟩ := hX kv hkv _ hSr hvG Q hQG hWG
  -- every pin at the top is the destination: a top witness of the filtered joined state names it
  have htop : ∀ r ∈ R, r.step = (n : Int) + 1 → r = kv'.1 := by
    intro r hr hrs
    obtain ⟨w0, nw0, hnw0, hw0s, _⟩ := hW ((n : Int) + 1) (by omega) (by rw [hFcs]; omega)
    have hwr := LineUnion.gowner_pinned _ R w0 (cF.pc.ker.gow w0 nw0 hnw0) r hr (by rw [hw0s, hrs])
    obtain ⟨nJ, hnJ, _, _, _⟩ := hbJ.node w0 nw0 hnw0
    obtain ⟨kv0, hkv0, hd0, hv0, nP0, hnP0⟩ := (PieceJoin.join_no_new φ n kv' hkv').1 w0 nJ hnJ
    obtain ⟨hok0, hdst0, hcs0, _, hvF0, _⟩ := src_ctx φ hbd n kv0 hkv0 kv'.1 hd0 hv0
    have c0 := filt_ctx φ hbd n kv0 hok0 (reqOf φ kv'.1) hvF0
    have hwd := mapId_of_mem_newRowIds _ _ _ w0 (upF_new φ kv0.2 kv'.1 hdst0 c0 hv0 w0 nP0 hnP0 (by rw [hw0s, hcs0])).1
    rw [← hwr, hwd]
  obtain ⟨hsP, hlowsel⟩ := climb φ n hbd hn1 kv hkv kv'.1 hd hvp R htop sel hsG
  -- to the joined state
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hvp
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvp
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hP.reach)
  have hPcs : (upF φ kv.2 kv'.1).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hPRcs : (filterAll (upF φ kv.2 kv'.1) R).current_step = (n : Int) + 2 := by
    rw [(pruned_filterAll _ R).step_eq, hPcs]
  have hsJ' : ChainSound (filterAll h R) (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel) := by
    have hsU : ChainSound (upF φ kv.2 kv'.1) (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel) :=
      ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self _ hndP R)) _ hsP
    exact ChainSound_filterAll h R _ (ChainSound_of_grown hgr _ hsU) (fun r hr h0 h1 =>
      chain_pins (upF φ kv.2 kv'.1) R _ hsP r hr h0 (by rw [← hgr.step_eq]; exact h1))
  rw [← he] at hFcs ⊢
  have hws : (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel ((n : Int) + 1)).id.step = (n : Int) + 1 :=
    (hsJ'.chain.1.1 _ (by omega) (by rw [hFcs]; omega)).2
  obtain ⟨_, h1, h2⟩ := good_of_chain _ hsJ' (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel ((n : Int) + 1) :: Q)
    (fun q hq => by
      rw [hFcs]
      rcases List.mem_cons.mp hq with e | hq
      · rw [e, hws]; exact ⟨by omega, by omega, rfl⟩
      · obtain ⟨nq, hnq, _⟩ := hQ q hq
        have := CertFix.step_range cF.pc q nq hnq
        rw [← he] at this; rw [hFcs] at this
        exact ⟨this.1, by have := hlow q hq; omega, by rw [hlowsel _ (hlow q hq)]; exact hon q hq⟩)
  exact ⟨_, hws, h1, h2⟩

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.anchorF_of_ulua' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms anchorF_of_ulua

omit n in
/-- **A1 at line 0**: a state of line 1 is its piece, which has `FCert` (from `MapCert`); the certificate's top node
anchors the clique. -/
theorem anchorF_zero : AnchorF φ 0 := by
  intro kv' hkv' R hR hv Q hQ hW hlow
  have hok' : StateOk φ ((0 + 1 : Nat) : Int) kv' := (lineOk φ (0 + 1)).2 kv' hkv'
  have hcsJ : kv'.2.current_step = 2 := by have := hok'.step; push_cast at this; omega
  have hFcs : (filterAll kv'.2 R).current_step = 2 := by rw [(pruned_filterAll _ R).step_eq, hcsJ]
  obtain ⟨r0, nr0, hnr0, _, _⟩ := hW 0 (by omega) (by rw [hFcs]; omega)
  have hnd' := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hok'.reach)
  obtain ⟨nJ, hnJ, _, _, _⟩ := (KernelIff.below_filterAll_self kv'.2 hnd' R).node r0 nr0 hnr0
  obtain ⟨kv0, hkv0, hd0, hv0, _⟩ := (PieceJoin.join_no_new φ 0 kv' hkv').1 r0 nJ hnJ
  have hP := StateOk_sent φ 0 kv0 ((lineOk φ 0).2 kv0 hkv0) kv'.1 hd0 hv0
  have hFC := fCert_of_mapCert φ hbd _ _ hP (StateLine.mapCert_piece0 φ kv0 hkv0 kv'.1 hd0 hv0)
  have e : kv'.2 = upF φ kv0.2 kv'.1 := by rw [line_one φ kv' hkv', line_zero φ kv0 hkv0]
  rw [e] at hv hQ hW hR hFcs
  have cQ := filt_ctx φ hbd _ (kv'.1, upF φ kv0.2 kv'.1) hP R hv
  obtain ⟨sel, hs, hon⟩ := hFC R hR hv Q hQ hW
  have hws : (sel ((0 : Nat) + 1 : Int)).id.step = ((0 : Nat) : Int) + 1 :=
    (hs.chain.1.1 _ (by omega) (by rw [hFcs]; omega)).2
  obtain ⟨_, h1, h2⟩ := good_of_chain sel hs (sel ((0 : Nat) + 1 : Int) :: Q) (fun q hq => by
    rw [hFcs]
    rcases List.mem_cons.mp hq with e' | hq
    · rw [e', hws]; exact ⟨by omega, by omega, rfl⟩
    · obtain ⟨nq, hnq, _⟩ := hQ q hq
      have := CertFix.step_range cQ.pc q nq hnq
      exact ⟨this.1, by have := hlow q hq; omega, hon q hq⟩)
  rw [e]
  exact ⟨_, hws, h1, h2⟩

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.anchorF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms anchorF_zero

omit n in
/-- **Every state of every line has `FCert`**, by induction: S2 at line `n` comes from LUA and `FCert` of line `n` (the
induction hypothesis), then `PieceLocalF` from A1 and S2, and the pieces from `TopParent`. At line 0 S2 is
`topPieceF_zero`. -/
theorem fCert_line_lua
    (hA : ∀ n : Nat, (n : Int) + 1 < stepCount φ → (∀ kv ∈ line φ n, FCert kv.2) → AnchorF φ n)
    (hL : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → LUA φ n)
    (hTM : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → TopMergeJ φ n)
    (hTP : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → TopParent φ n) :
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
    have hS : TopPieceF φ m := by
      by_cases hm0 : m = 0
      · subst hm0; exact topPieceF_zero φ
      · exact topPieceF_of_lua φ m hbd (by omega) (hL m (by omega) hm) (hTM m (by omega) hm)
          (fun kv hkv => ih (by omega) kv hkv)
    refine fCert_join φ hbd m (pieceLocalF_of_anchor φ m hbd (hA m hm (fun kv hkv => ih (by omega) kv hkv)) hS)
      (fun kv hkv d hd hv => ?_)
    by_cases hm0 : m = 0
    · subst hm0
      exact fCert_of_mapCert φ hbd _ _ (StateOk_sent φ 0 kv ((lineOk φ 0).2 kv hkv) d hd hv)
        (StateLine.mapCert_piece0 φ kv hkv d hd hv)
    · exact pieceF_of_topParent φ hbd m (by omega) (hTP m (by omega) hm) kv hkv (ih (by omega) kv hkv) d hd hv

omit n in
/-- **The reader decides `φ` under A1, LUA, `TopMergeJ` and `MergeSplit`.** -/
theorem readerVerdictW_iff_of_lua (hA : ∀ n : Nat, (n : Int) + 1 < stepCount φ → AnchorF φ n)
    (hL : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → LUA φ n)
    (hTM : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → TopMergeJ φ n)
    (hMS : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → MergeSplit φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_fCert φ hbd (fun kv hkv => ?_)
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by simp only [stepCount]; omega
  exact fCert_line_lua φ hbd (fun n hn _ => hA n hn) hL hTM (fun n hn1 hn =>
    topParent_of_topMerge φ hbd n (topMerge_of_mergeSplit φ hbd n (hMS n hn1 hn))) _ hN kv hkv

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.readerVerdictW_iff_of_lua' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_lua

omit n in
/-- **The reader decides `φ` under A1, LUA and the two merge splits** (`MergeSplitJ` in the joined states,
`MergeSplit` in the pieces): a clique with witnesses with a merged top survives the pin of one of the two
grandparents. -/
theorem readerVerdictW_iff_of_lua_split (hA : ∀ n : Nat, (n : Int) + 1 < stepCount φ → AnchorF φ n)
    (hL : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → LUA φ n)
    (hMJ : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → MergeSplitJ φ n)
    (hMS : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → MergeSplit φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_lua φ hbd hA hL (fun n hn1 hn => topMergeJ_of_mergeSplitJ φ n hbd (hMJ n hn1 hn)) hMS

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.readerVerdictW_iff_of_lua_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_lua_split

omit n in
/-- **The reader decides `φ` under A1, LUA, `MergeSplitJ` and AF in the pieces** (`MergeSplit` is no longer needed:
the merge in a piece is resolved by the certificate of the source, once AF pins the map node `w` fixes one step under
its parents). -/
theorem readerVerdictW_iff_of_afp (hA : ∀ n : Nat, (n : Int) + 1 < stepCount φ → AnchorF φ n)
    (hL : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → LUA φ n)
    (hMJ : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → MergeSplitJ φ n)
    (hAF : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → AFP φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_fCert φ hbd (fun kv hkv => ?_)
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by simp only [stepCount]; omega
  exact fCert_line_lua φ hbd (fun n hn _ => hA n hn) hL (fun n hn1 hn => topMergeJ_of_mergeSplitJ φ n hbd (hMJ n hn1 hn))
    (fun n hn1 hn => topParent_of_afp φ n hbd hn1 (hAF n hn1 hn)) _ hN kv hkv

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.readerVerdictW_iff_of_afp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_afp

omit n in
/-- **The reader decides `φ` under ULUA, LUA, `MergeSplitJ` and AF in the pieces.** A1 is no longer a hypothesis: at
line 0 it is `anchorF_zero`, and from line 1 on it comes from ULUA and `FCert` of the line (`anchorF_of_ulua`). -/
theorem readerVerdictW_iff_of_ulua (hU : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → ULUA φ n)
    (hL : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → LUA φ n)
    (hMJ : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → MergeSplitJ φ n)
    (hAF : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → AFP φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_fCert φ hbd (fun kv hkv => ?_)
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by simp only [stepCount]; omega
  refine fCert_line_lua φ hbd (fun n hn hX => ?_) hL (fun n hn1 hn => topMergeJ_of_mergeSplitJ φ n hbd (hMJ n hn1 hn))
    (fun n hn1 hn => topParent_of_afp φ n hbd hn1 (hAF n hn1 hn)) _ hN kv hkv
  by_cases h0 : n = 0
  · subst h0; exact anchorF_zero φ hbd
  · exact anchorF_of_ulua φ n hbd (by omega) (hU n (by omega) hn) hX

/-- info: 'AbsSatBin.GraphPath.Model.AnchorPiece.readerVerdictW_iff_of_ulua' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_ulua

end AbsSatBin.GraphPath.Model.AnchorPiece
