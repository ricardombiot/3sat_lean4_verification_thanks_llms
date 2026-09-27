-- lean/improves_bin/AbsSatBin/GraphPath/Model/FExtInd.lean
import AbsSatBin.GraphPath.Model.PieceBridge
import AbsSatBin.GraphPath.Model.MapTri

/-!
# `FExt` by induction along the machine, under the join bridge M1 (`docs/context/ambfar.md` §4.2ο)

* **`LExt X`**: `FExt` with pin lists. If `X` pinned by `ps` is valid, then at every step `k` some map node `m` of
  step `k` keeps `X` pinned by `m :: ps` valid.
* **Successive pins fit the lists** (`readAny_track`, `fExt_of_lExt`). A state the reader reaches by successive
  pins `ps` is a kernel below the start that agrees with `ps`, and every kernel below the start that agrees with
  `ps` is below it (`filterAll` never goes below such a kernel). So `LExt ⇒ FExt`.
* **The low lines** (`lExt_low`): in lines 0 and 1 every step has one map node alive: the key at the top
  (`LineSem.top_entry_key`), the root at step 0 (`mapNodes`).
* **The step** (`lExt_succ`). A valid pin set of a joined state `J` of line `n+1`:
  1. **M1** (the hypothesis) puts it on a piece `upF X d`.
  2. **M2w** (`PieceBridge.src_of_piece`) takes it down to the source `X`, pinned by `pinsW`.
  3. `LExt X` gives a pin `m`.
  4. **M3w** (`PieceBridge.piece_of_src`) takes `m` back up to the piece.
  5. The piece sits below `J`.

  The top step of `J` has one map node, its key.
* **`readerVerdictW_iff_of_m1`**: **the reader decides `φ` under M1 at every join (`n ≥ 1`).**

M1 (a valid pin set of a joined state is valid on one of its pieces) is measured without failure
(`fextind_probe.jl`); it is the whole open core.
-/

namespace AbsSatBin.GraphPath.Model.FExtInd

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.PickInduction (choiceAt)

/-- **`LExt`**: a valid pin list grows by one pin at every step. -/
def LExt (X : GPathM) : Prop :=
  ∀ ps : List NodeId, isValid (filterAll X ps) = true → ∀ k, 0 ≤ k → k < X.current_step →
    ∃ m : NodeId, m.step = k ∧ isValid (filterAll X (m :: ps)) = true

variable (φ : Cnf) (hbd : Bounded φ)

/-- **M1, the join bridge**: a valid pin set of a joined state of line `n+1` is valid on one of its pieces. -/
def M1 (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ ps : List NodeId, isValid (filterAll kv'.2 ps) = true →
    ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 kv'.1) = true ∧
      isValid (filterAll (upF φ kv.2 kv'.1) ps) = true

include hbd

-- ============================================================
-- Pins on one state
-- ============================================================

section
variable (k : Int) (kv : NodeId × GPathM) (hkv : StateOk φ k kv)
include hkv

theorem nodup_ok : NodupIds kv.2 :=
  Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 (MapReachable.reachable_of_mapReachable φ hbd kv.2 hkv.reach)

/-- A valid filter stays valid with fewer pins. -/
theorem valid_sub (l₁ l₂ : List NodeId) (hsub : ∀ r ∈ l₂, r ∈ l₁) (hv : isValid (filterAll kv.2 l₁) = true) :
    isValid (filterAll kv.2 l₂) = true := by
  have c := filt_ctx φ hbd k kv hkv l₁ hv
  exact isValid_filterAll_of_kernel c.pc.ker hv (KernelIff.below_filterAll_self kv.2 (nodup_ok φ hbd k kv hkv) l₁) l₂
    (fun r hr q hq hs => LineUnion.gowner_pinned kv.2 l₁ q hq r (hsub r hr) hs)

/-- A pin that every global owner of its step already names keeps the filter valid. -/
theorem valid_unique (ps : List NodeId) (hv : isValid (filterAll kv.2 ps) = true) (m : NodeId)
    (hm : ∀ q ∈ (filterAll kv.2 ps).gowners, q.id.step = m.step → q.id = m) :
    isValid (filterAll kv.2 (m :: ps)) = true := by
  have c := filt_ctx φ hbd k kv hkv ps hv
  refine isValid_filterAll_of_kernel c.pc.ker hv (KernelIff.below_filterAll_self kv.2 (nodup_ok φ hbd k kv hkv) ps) _
    (fun r hr q hq hs => ?_)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hm q hq hs
  · exact LineUnion.gowner_pinned kv.2 ps q hq r hr hs

/-- At step 0 only the root is alive. -/
theorem zero_unique (ps : List NodeId) (hv : isValid (filterAll kv.2 ps) = true) :
    ∀ q ∈ (filterAll kv.2 ps).gowners, q.id.step = (⟨0, 0⟩ : NodeId).step → q.id = ⟨0, 0⟩ := by
  intro q hq hqs
  have c := filt_ctx φ hbd k kv hkv ps hv
  have hmap : MapReachable.NodesOnMap φ (filterAll kv.2 ps) :=
    MapReachable.NodesOnMap_of_pruned φ (pruned_filterAll kv.2 ps) (MapReachable.nodesOnMap_of_mapReachable φ kv.2 hkv.reach)
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn q hq)
  have hid : nq.id = q := node?_id_eq _ q nq hnq
  have := hmap nq (List.mem_of_find?_eq_some hnq)
  rw [hid, hqs, mapNodes_fusion φ 0 (Or.inl rfl)] at this
  exact List.mem_singleton.mp this

end

/-- In a state of line `n`, every node owned at step `n` names the key; so does every global owner of a filter. -/
theorem top_unique (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (G : GPathM) (cG : AmbTriCore.ACtx G)
    (hb : Below kv.2 G) : ∀ q ∈ G.gowners, q.id.step = (n : Int) → q.id = kv.1 := by
  intro q hq hqs
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cG.pc.ker.gn q hq)
  obtain ⟨nx, hnx, ho, _, _⟩ := hb.node q nq hnq
  exact top_entry_key φ hbd n kv hkv q nx hnx q (ho q (TriPinCut.self_own_pc cG.pc q nq hnq)) hqs

-- ============================================================
-- The low lines
-- ============================================================

theorem lExt_low (n : Nat) (hn : n ≤ 1) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) : LExt kv.2 := by
  intro ps hv k hk0 hk1
  have hok := (lineOk φ n).2 kv hkv
  have hcs : kv.2.current_step = (n : Int) + 1 := hok.step
  rw [hcs] at hk1
  by_cases hkn : k = (n : Int)
  · refine ⟨kv.1, by rw [mapNodes_step φ n kv.1 hok.onMap, hkn], ?_⟩
    have c := filt_ctx φ hbd n kv hok ps hv
    have hb := KernelIff.below_filterAll_self kv.2 (nodup_ok φ hbd n kv hok) ps
    refine valid_unique φ hbd n kv hok ps hv kv.1 (fun q hq hqs => ?_)
    rw [mapNodes_step φ n kv.1 hok.onMap] at hqs
    exact top_unique φ hbd n kv hkv _ c hb q hq hqs
  · have hk : k = 0 := by omega
    exact ⟨⟨0, 0⟩, hk.symm, valid_unique φ hbd n kv hok ps hv ⟨0, 0⟩ (zero_unique φ hbd n kv hok ps hv)⟩

-- ============================================================
-- The step
-- ============================================================

theorem lExt_succ (n : Nat) (hn1 : 1 ≤ n) (hM : M1 φ n) (hL : ∀ kv ∈ line φ n, LExt kv.2) :
    ∀ kv' ∈ line φ (n + 1), LExt kv'.2 := by
  intro kv' hkv' ps hv k hk0 hk1
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hkey' : kv'.1.step = (n : Int) + 1 := by rw [mapNodes_step φ _ kv'.1 hok'.onMap]; push_cast; rfl
  have cG := filt_ctx φ hbd _ kv' hok' ps hv
  have hbG := KernelIff.below_filterAll_self kv'.2 (nodup_ok φ hbd _ kv' hok') ps
  have topG := top_unique φ hbd (n + 1) kv' hkv' _ cG hbG
  by_cases hkt : k = (n : Int) + 1
  · -- the top: one map node, the key
    refine ⟨kv'.1, by rw [hkey', hkt], valid_unique φ hbd _ kv' hok' ps hv kv'.1 (fun q hq hqs => ?_)⟩
    exact topG q hq (by rw [hqs, hkey']; push_cast; rfl)
  · have hkn : k ≤ (n : Int) := by rw [hcs'] at hk1; omega
    -- M1: a piece
    obtain ⟨kv, hkv, hd, hvP0, hvP⟩ := hM kv' hkv' ps hv
    have hok := (lineOk φ n).2 kv hkv
    have hXcs : kv.2.current_step = (n : Int) + 1 := hok.step
    -- M2w: down to the source
    have hvX := PieceBridge.src_of_piece φ hbd n hn1 kv hkv kv'.1 hd hvP0 ps hvP
    -- `LExt` of the source
    obtain ⟨m, hms, hvm⟩ := hL kv hkv _ hvX k hk0 (by rw [hXcs]; omega)
    have hvm' : isValid (filterAll kv.2 (LineUnion.pinsW φ n kv'.1 kv.1 ++
        (m :: ps.filter (fun m => decide (m.step ≤ (n : Int)))))) = true := by
      refine valid_sub φ hbd n kv hok _ _ (fun r hr => ?_) hvm
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hr)
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ hr)
    -- M3w: back up to the piece
    have hvPm := PieceBridge.piece_of_src φ hbd n kv hkv kv'.1 hd hvP0
      (m :: ps.filter (fun m => decide (m.step ≤ (n : Int)))) (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp
        · rw [hms]; exact hkn
        · exact of_decide_eq_true (List.mem_filter.mp hp).2) hvm'
    -- the piece sits below the joined state
    obtain ⟨h, hh, hg⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hvP0
    have heq : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hh kv' hkv' rfl
    have hbJP : Below kv'.2 (upF φ kv.2 kv'.1) := by
      rw [← heq]; exact PieceFilter.below_of_grown hg
    have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvP0
    have cK := filt_ctx φ hbd _ _ hP (m :: ps.filter (fun m => decide (m.step ≤ (n : Int)))) hvPm
    have hbK := PieceFilter.below_trans hbJP
      (KernelIff.below_filterAll_self _ (nodup_ok φ hbd _ _ hP) (m :: ps.filter (fun m => decide (m.step ≤ (n : Int)))))
    have hKcs : (filterAll (upF φ kv.2 kv'.1) (m :: ps.filter (fun m => decide (m.step ≤ (n : Int))))).current_step =
        (n : Int) + 2 := by rw [← hbK.step, hcs']
    refine ⟨m, hms, isValid_filterAll_of_kernel cK.pc.ker hvPm hbK (m :: ps) (fun r hr q hq hqs => ?_)⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact LineUnion.gowner_pinned _ _ q hq r List.mem_cons_self hqs
    · by_cases hrn : r.step ≤ (n : Int)
      · exact LineUnion.gowner_pinned _ _ q hq r
          (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hr, decide_eq_true hrn⟩)) hqs
      · -- a pin above step `n`: `q` is at the top, where only the key lives, and so is the pin
        obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cK.pc.ker.gn q hq)
        have hqr := CertFix.step_range cK.pc q nq hnq
        rw [hKcs] at hqr
        have hqt : q.id.step = (n : Int) + 1 := by omega
        have hq1 : q.id = kv'.1 := top_unique φ hbd (n + 1) kv' hkv' _ cK hbK q hq (by rw [hqt]; push_cast; rfl)
        -- the pin names the key: the valid filter of `J` has a global owner at its step
        have hrmem : r.step ∈ intRange 0 ((filterAll kv'.2 ps).current_step - 1) :=
          mem_intRange_zero _ _ (by omega) (by rw [← hbG.step, hcs']; omega)
        obtain ⟨g0, hg0, hg0s⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv _ hrmem)
        have e1 := LineUnion.gowner_pinned kv'.2 ps g0 hg0 r hr (eq_of_beq hg0s)
        have e2 := topG g0 hg0 (by rw [eq_of_beq hg0s]; push_cast; omega)
        rw [hq1, ← e2, e1]

/-- **`LExt` in every state of every line, under M1 at every join.** -/
theorem lExt_line (hM : ∀ n, 1 ≤ n → M1 φ n) : ∀ n, ∀ kv ∈ line φ n, LExt kv.2 := by
  intro n
  induction n with
  | zero => exact lExt_low φ hbd 0 (by omega)
  | succ n ih =>
    by_cases h0 : n = 0
    · subst h0; exact lExt_low φ hbd 1 (by omega)
    · exact lExt_succ φ hbd n (by omega) (hM n (by omega)) ih

-- ============================================================
-- Successive pins fit the lists
-- ============================================================

section
variable (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
include hkv

/-- A state reached by successive pins `ps` lies below the start, agrees with `ps`, and every kernel below the start
that agrees with `ps` lies below it. -/
theorem readAny_track (g : GPathM) (hA : MapTri.ReadAny (filterAll kv.2 []) g) :
    ∃ ps : List NodeId, Below kv.2 g ∧ (∀ r ∈ ps, ∀ x ∈ g.gowners, x.id.step = r.step → x.id = r) ∧
      ∀ K, Kernel K → Below kv.2 K → (∀ r ∈ ps, ∀ x ∈ K.gowners, x.id.step = r.step → x.id = r) → Below g K := by
  have hkvl : kv ∈ line φ (stepCount φ - 1).toNat := hkv
  have hok := (lineOk φ _).2 kv hkvl
  have hnd := nodup_ok φ hbd _ kv hok
  have b₀ := PinChainBin.binCtx_start φ hbd kv hkv
  induction hA with
  | start =>
    refine ⟨[], KernelIff.below_filterAll_self kv.2 hnd [], fun r hr => absurd hr List.not_mem_nil,
      fun K hK hb _ => below_filterAll hK hb [] (fun r hr => absurd hr List.not_mem_nil)⟩
  | pin g _ q hA _ _ _ ih =>
    obtain ⟨ps, hbg, hpin, hup⟩ := ih
    have hndg := (MapTri.binCtx_readAny φ _ b₀ g hA).rctx.nodup
    refine ⟨q.id :: ps, PieceFilter.below_trans hbg (KernelIff.below_filterAll_self g hndg [q.id]),
      fun r hr x hx hxs => ?_, fun K hK hb hKp => ?_⟩
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact LineUnion.gowner_pinned g [q.id] x hx _ List.mem_cons_self hxs
      · exact hpin r hr x ((pruned_filterAll g [q.id]).gowners_sub x hx) hxs
    · have hbgK := hup K hK hb (fun r hr => hKp r (List.mem_cons_of_mem _ hr))
      exact below_filterAll hK hbgK [q.id] (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hKp _ List.mem_cons_self)

/-- **`LExt ⇒ FExt`** on the starting state. -/
theorem fExt_of_lExt (hL : LExt kv.2) : MapTri.FExt (filterAll kv.2 []) := by
  intro g hA hv k hc
  have hkvl : kv ∈ line φ (stepCount φ - 1).toNat := hkv
  have hok := (lineOk φ _).2 kv hkvl
  obtain ⟨ps, hbg, hpin, hup⟩ := readAny_track φ hbd kv hkv g hA
  have hkg := MapTri.kernel_readAny φ hbd kv hkv g hA hv
  have hvX : isValid (filterAll kv.2 ps) = true := isValid_filterAll_of_kernel hkg hv hbg ps hpin
  obtain ⟨q, hq, _⟩ := List.any_eq_true.mp hc
  obtain ⟨hqg, hqs⟩ := List.mem_filter.mp hq
  have hqk : q.id.step = k := eq_of_beq hqs
  -- the step of `q` is a step of the start
  have cS := KernelUp.aCtx_line φ hbd _ kv hkvl
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (hkg.gn q hqg)
  obtain ⟨nx, hnx, _, _, _⟩ := hbg.node q nq hnq
  have hr := CertFix.step_range cS.pc q nx hnx
  rw [hqk] at hr
  obtain ⟨m, hms, hvm⟩ := hL ps hvX k hr.1 hr.2
  have cK := filt_ctx φ hbd _ kv hok (m :: ps) hvm
  have hbK := KernelIff.below_filterAll_self kv.2 (nodup_ok φ hbd _ kv hok) (m :: ps)
  have pinK : ∀ r ∈ m :: ps, ∀ x ∈ (filterAll kv.2 (m :: ps)).gowners, x.id.step = r.step → x.id = r :=
    fun r hr x hx hxs => LineUnion.gowner_pinned kv.2 _ x hx r hr hxs
  have hbgK := hup _ cK.pc.ker hbK (fun r hr => pinK r (List.mem_cons_of_mem _ hr))
  -- a global owner of the pinned kernel at step `k`
  have hkmem : k ∈ intRange 0 ((filterAll kv.2 (m :: ps)).current_step - 1) :=
    mem_intRange_zero _ _ hr.1 (by rw [← hbK.step]; exact hr.2)
  obtain ⟨x, hx, hxs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvm _ hkmem)
  have hxk : x.id.step = k := eq_of_beq hxs
  have hxm : x.id = m := pinK m List.mem_cons_self x hx (by rw [hxk, hms])
  refine ⟨x, List.mem_filter.mpr ⟨hbgK.gow x hx, hxs⟩, ?_⟩
  refine isValid_filterAll_of_kernel cK.pc.ker hvm hbgK [x.id] (fun r hr y hy hys => ?_)
  rw [List.mem_singleton.mp hr] at hys ⊢
  rw [hxm]
  exact pinK m List.mem_cons_self y hy (by rw [hys, hxm])

end

/-- **The reader decides `φ` under M1 at every join.** -/
theorem readerVerdictW_iff_of_m1 (hM : ∀ n, 1 ≤ n → M1 φ n) : readerVerdictW φ = true ↔ Satisfiable φ :=
  MapTri.readerVerdictW_iff_of_fExt φ hbd (fun kv hkv =>
    fExt_of_lExt φ hbd kv hkv (lExt_line φ hbd hM _ kv hkv))

end AbsSatBin.GraphPath.Model.FExtInd

/-- info: 'AbsSatBin.GraphPath.Model.FExtInd.readerVerdictW_iff_of_m1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.FExtInd.readerVerdictW_iff_of_m1
