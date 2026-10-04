-- lean/improves_bin/AbsSatBin/GraphPath/Model/FilterUnion.lean
import AbsSatBin.GraphPath.Model.LineUnion

/-!
# Filtering the union stays inside the union of the filtered pieces (FU)

Measured (`julia/improves_bin/test_3sat/probes/glfstar_probe.jl`, FU): filtering a joined state by pins leaves,
entry by entry, only entries of its pieces filtered by the same pins (5 337 of 5 337). This module proves it from
`MapCert` of the joined state — step 2 of the induction of `GLF` (`docs/context/escalera_reader.md` §4.2κ).

* **`mapCert_filter_pins`**: pins keep `MapCert` when the pinned state is a kernel (the list form of
  `PieceFilter.mapCert_filter_pin`): the witnesses of the pinned kernel own, at each pinned step, only the pinned
  node, so the certificate goes through the pins and survives the filter.
* **`filter_union`** (FU): under `MapCert` of a state of line `n+1`, every entry of it filtered by `ps` is an entry of
  one of its pieces filtered by `ps`. The entry is a clique of two with witnesses (`entryOnChain_of_mapCert`); its
  certificate lies in one piece (`PieceJoin.chain_in_piece`), passes the pins, and survives the piece's filter.
-/

namespace AbsSatBin.GraphPath.Model.FilterUnion

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri (Clique)
open AbsSatBin.GraphPath.Model.MapCert (MapCert WitR CertR)

/-- **Pins keep `MapCert`** when the pinned state is a kernel and every pin is a step of the state. -/
theorem mapCert_filter_pins (X : GPathM) (hnd : NodupIds X) (ps : List NodeId)
    (hkF : Kernel.Kernel (filterAll X ps)) (hps : ∀ p ∈ ps, 0 ≤ p.step ∧ p.step < X.current_step)
    (hm : MapCert X) : MapCert (filterAll X ps) := by
  have hb := KernelIff.below_filterAll_self X hnd ps
  intro Q R hQ hW
  have hQX : Clique X Q := fun p hp => by
    obtain ⟨np, hnp, hpQ⟩ := hQ p hp
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node p np hnp
    exact ⟨nx, hnx, fun s hs => ho s (hpQ s hs)⟩
  have hWX : WitR X Q (R ++ ps) := by
    intro l hl0 hl1
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l hl0 (by rw [← hb.step]; exact hl1)
    obtain ⟨nx, hnx, hox, _, _⟩ := hb.node r nr hnr
    refine ⟨r, nx, hnx, hrs, fun p hp => hox p (hrQ p hp), fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm' | hm'
    · obtain ⟨p, hp, hpm⟩ := hrR m hm'
      exact ⟨p, hox p hp, hpm⟩
    · obtain ⟨hall, _, _⟩ := (Kernel.isValidNode_iff _ nr).mp (hkF.valid r nr hnr)
      obtain ⟨p, hp, hps'⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall m.step
        (mem_intRange_zero m.step _ (hps m hm').1 (by rw [← hb.step]; exact (hps m hm').2)))
      exact ⟨p, hox p hp, LineUnion.gowner_pinned X ps p (hkF.own r nr hnr p hp) m hm' (eq_of_beq hps')⟩
  obtain ⟨sel, hs, hon, hR⟩ := hm Q (R ++ ps) hQX hWX
  refine ⟨sel, ChainSound_filterAll X ps sel hs (fun r hr hr0 hr1 => hR r (List.mem_append_right _ hr) hr0 hr1),
    hon, fun m hm hm0 hm1 => hR m (List.mem_append_left _ hm) hm0 (by rw [hb.step]; exact hm1)⟩

/-- info: 'AbsSatBin.GraphPath.Model.FilterUnion.mapCert_filter_pins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapCert_filter_pins

variable (φ : Cnf) (hbd : Bounded φ) (n : Nat)
include hbd

/-- **FU**: under `MapCert` of a state of line `n+1`, every entry of it filtered by `ps` is an entry of one of its
pieces filtered by `ps`. -/
theorem filter_union (hn : (n : Int) + 1 < stepCount φ) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1))
    (ps : List NodeId) (hps : ∀ p ∈ ps, 0 ≤ p.step ∧ p.step < kv'.2.current_step)
    (hvF : isValid (filterAll kv'.2 ps) = true) (hM : MapCert kv'.2) :
    ∀ q nq, (filterAll kv'.2 ps).node? q = some nq → ∀ v ∈ nq.owners,
      ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 kv'.1) = true ∧
        ∃ np, (filterAll (upF φ kv.2 kv'.1) ps).node? q = some np ∧ v ∈ np.owners := by
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hreach := MapReachable.reachable_of_mapReachable φ hbd _ hok'.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach
  have c := filt_ctx φ hbd _ kv' hok' ps hvF
  have hb := KernelIff.below_filterAll_self kv'.2 hnd ps
  have hso : Ownership.SelfOwned (filterAll kv'.2 ps) :=
    SelfOwn.SelfOwned_of_OOS (ps.foldl filterRequire kv'.2) hvF c.rc.oos c.rc.snn c.rc.below
  have hab : KernelReader.OwnAbove (filterAll kv'.2 ps) :=
    KernelReader.ownAbove_of_pruned (pruned_filterAll _ _)
      (KernelReader.ownAbove_reachable (reqOf φ) (isProhibited φ) _ hreach)
  have hEC := PieceFilter.entryOnChain_of_mapCert c.pc.ker hso c.rc.below hab
    (mapCert_filter_pins kv'.2 hnd ps c.pc.ker hps hM)
  intro q nq hq v hv
  obtain ⟨sel, hs, hq0, hq1, hv0, hv1, hselq, hselv⟩ := hEC q nq hq v hv
  -- the certificate lies in one piece
  have hsJ : ChainSound kv'.2 sel := ChainSound_of_grown (PieceFilter.grown_of_below hb) sel hs
  obtain ⟨kv, hkv, hd, hvp, sel', hs', heq⟩ := PieceJoin.chain_in_piece φ hbd n hn kv' hkv' sel hsJ
  have hcsJ : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hFcs : (filterAll kv'.2 ps).current_step = (n : Int) + 2 := by rw [← hb.step, hcsJ]
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) :=
    StateOk_sent φ n kv ((lineOk φ n).2 kv hkv) kv'.1 hd hvp
  have hPcs : (upF φ kv.2 kv'.1).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  -- it passes the pins, and survives the piece's filter
  have hpins : ∀ r ∈ ps, 0 ≤ r.step → r.step < (upF φ kv.2 kv'.1).current_step → (sel' r.step).id = r := by
    intro r hr h0 h1
    rw [hPcs] at h1
    rw [heq r.step h0 h1]
    have hg := hs.chain.2.2 r.step h0 (by rw [hFcs]; exact h1)
    exact LineUnion.gowner_pinned kv'.2 ps _ hg r hr (hs.chain.1.1 r.step h0 (by rw [hFcs]; exact h1)).2
  have hsP := ChainSound_filterAll _ ps sel' hs' hpins
  have hPFcs : (filterAll (upF φ kv.2 kv'.1) ps).current_step = (n : Int) + 2 := by
    rw [(pruned_filterAll _ ps).step_eq, hPcs]
  rw [hFcs] at hq1 hv1
  obtain ⟨np, hnp, hown⟩ := GrowCert.chain_owns hsP q.id.step v.id.step hq0 (by rw [hPFcs]; exact hq1) hv0
    (by rw [hPFcs]; exact hv1)
  rw [heq _ hq0 hq1, hselq] at hnp
  rw [heq _ hv0 hv1, hselv] at hown
  exact ⟨kv, hkv, hd, hvp, np, hnp, hown⟩

/-- info: 'AbsSatBin.GraphPath.Model.FilterUnion.filter_union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filter_union

-- ============================================================
-- The descent: a pinned piece, without its top row, below its pinned source
-- ============================================================

/-- **A piece pinned by `ps`, without its top row, sits below its source pinned by `pinsW` and by the pins of `ps`
below the top.** The truncated pinned piece is a kernel; its tables below the top are tables of the source; at the
step of a pin of `ps` its global owners are pinned by the piece's own filter, at a requirement by the source's
filter, and at `L1` (when the filter skips a window) each owns `L1 = 1` at its own step. -/
theorem piece_pinned_below (hn1 : 1 ≤ n) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) (ps : List NodeId)
    (hvP : isValid (filterAll (upF φ kv.2 d) ps) = true) :
    Kernel.Below (filterAll kv.2 (LineUnion.pinsW φ n d kv.1 ++ ps.filter (fun m => decide (m.step ≤ (n : Int)))))
      (Trunc.trunc (filterAll (upF φ kv.2 d) ps)) := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  have hP : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hreachP := MapReachable.reachable_of_mapReachable φ hbd _ hP.reach
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreachP
  have cQ := filt_ctx φ hbd _ (d, upF φ kv.2 d) hP ps hvP
  have hkT := Trunc.kernel_trunc cQ.pc.ker cQ.pc.pb cQ.pc.sa cQ.pc.below
  have hPcs : (upF φ kv.2 d).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hbQ := KernelIff.below_filterAll_self _ hndP ps
  have hQcs : (filterAll (upF φ kv.2 d) ps).current_step = (n : Int) + 2 := by rw [← hbQ.step, hPcs]
  have hndG := Reader.nodup_addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ) c.pc.nd c.pc.below hdF
  -- the piece sits below `addNode` of the filtered source
  have hPA : Kernel.Below (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ)) (upF φ kv.2 d) := by
    rcases (upF_shape φ kv.2 d hv).2 with e | e
    · rw [e]; exact ⟨rfl, fun q h => h, fun p n' h => ⟨n', h, fun _ x => x, fun _ x => x, fun _ x => x⟩⟩
    · rw [e]; exact KernelIff.below_filterAll_self _ hndG []
  have hQA := PieceFilter.below_trans hPA hbQ
  -- a node of the truncated pinned piece, in the filtered source
  have toF : ∀ p n', (Trunc.trunc (filterAll (upF φ kv.2 d) ps)).node? p = some n' →
      ∃ nF, (filterAll kv.2 (reqOf φ d)).node? p = some nF ∧ (∀ v ∈ n'.owners, v ∈ nF.owners) ∧
        (∀ v ∈ n'.parents, v ∈ nF.parents) ∧ (∀ v ∈ n'.sons, v ∈ nF.sons) ∧
        ∃ ns, (upF φ kv.2 d).node? p = some ns := by
    intro p n' hn'
    obtain ⟨nq, hnq, hps, rfl⟩ := Trunc.trunc_node?_some _ p n' hn'
    rw [hQcs] at hps
    obtain ⟨nG, hnG, hoG, hpG, hsG⟩ := hQA.node p nq hnq
    have hps' : p.id.step < (filterAll kv.2 (reqOf φ d)).current_step := by
      have := CertFix.step_range cQ.pc p nq hnq; rw [hQcs] at this; rw [hFcs]; omega
    obtain ⟨nF, hnF, hEq⟩ := addNode_node?_below _ d "" (isProhibited φ) hdF p nG hnG hps'
    obtain ⟨ns, hns, _, _, _⟩ := hbQ.node p nq hnq
    refine ⟨nF, hnF, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, ns, hns⟩
    · obtain ⟨hv, hvs⟩ := (Trunc.mem_cutTop_owners _ _ v).mp hv
      have := hoG v hv; rw [hEq, upMap_owners] at this
      rcases List.mem_append.mp this with h | h
      · exact h
      · have := KernelUp.row_step _ d (isProhibited φ) hdF v (gainedOwners_subset _ _ _ _ v h)
        rw [hFcs] at this; omega
    · have := hpG v hv; rw [hEq, upMap_parents] at this; exact this
    · obtain ⟨hv, hvs⟩ := (Trunc.mem_cutTop_sons _ _ v).mp hv
      have := hsG v hv; rw [hEq, upMap_sons] at this
      rcases List.mem_append.mp this with h | h
      · exact h
      · have := KernelUp.row_step _ d (isProhibited φ) hdF v ((KernelUp.mem_gainedSons _ _ _ _ v).mp h).1
        rw [hFcs] at this; omega
  have gowF : ∀ q ∈ (Trunc.trunc (filterAll (upF φ kv.2 d) ps)).gowners,
      q ∈ (filterAll kv.2 (reqOf φ d)).gowners := by
    intro q hq
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp (hkT.gn q hq)
    obtain ⟨nF, hnF, _⟩ := toF q n' hn'
    exact c.pc.ker.gow q nF hnF
  refine Kernel.below_filterAll hkT ⟨?_, fun q hq => hb.gow q (gowF q hq), fun p n' hn' => ?_⟩ _ ?_
  · show kv.2.current_step = (filterAll (upF φ kv.2 d) ps).current_step - 1
    rw [hQcs, hcs]; omega
  · obtain ⟨nF, hnF, ho, hp, hs, _⟩ := toF p n' hn'
    obtain ⟨nX, hnX, hoX, hpX, hsX⟩ := hb.node p nF hnF
    exact ⟨nX, hnX, fun v h => hoX v (ho v h), fun v h => hpX v (hp v h), fun v h => hsX v (hs v h)⟩
  · intro r hr q hq hqs
    rcases List.mem_append.mp hr with hr | hr
    · -- a pin of `pinsW`
      have hr' : r ∈ reqOf φ d ∨ (r = ⟨(n : Int) - 1, 1⟩ ∧
          skipsWindow (filterAll kv.2 (reqOf φ d)) d (isProhibited φ) = true) := by
        unfold LineUnion.pinsW at hr
        cases hc : (line φ n).any (fun kv₂ => kv₂.1 == kv.1 && skipsWindow (filterAll kv₂.2 (reqOf φ d)) d
            (isProhibited φ)) <;> rw [hc] at hr
        · rw [if_neg (by decide)] at hr; exact Or.inl hr
        · rw [if_pos rfl] at hr
          rcases List.mem_append.mp hr with hr | hr
          · exact Or.inl hr
          · refine Or.inr ⟨List.mem_singleton.mp hr, ?_⟩
            obtain ⟨kv₂, hkv₂, h₂⟩ := List.any_eq_true.mp hc
            simp only [Bool.and_eq_true, beq_iff_eq] at h₂
            have he : kv₂ = kv := key_inj _ (lineOk φ n).1 kv₂ hkv₂ kv hkv h₂.1
            rw [he] at h₂; exact h₂.2
      rcases hr' with hr' | ⟨rfl, hsk⟩
      · exact LineUnion.pinned_entry φ kv.2 d q (gowF q hq) r hr' hqs
      · obtain ⟨_, _, _, hG, hE⟩ := StatePiece.skip_window φ hbd n hn1 kv hkv d hd hv hsk
        obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp (hkT.gn q hq)
        obtain ⟨nF, hnF, _, _, _, ns, hns⟩ := toF q n' hn'
        obtain ⟨e, he, hed⟩ := hE q ns (by rw [hG] at hns; exact hns)
          (by rw [hFcs, hqs]; show (n : Int) - 1 < (n : Int) + 1; omega) nF hnF
        have hes : e.id.step = nF.id.id.step := by rw [node?_id_eq _ q nF hnF, hed, hqs]
        have := c.pc.oos nF (List.mem_of_find?_eq_some hnF) e he hes
        rw [node?_id_eq _ q nF hnF] at this
        rw [← this, hed]
    · -- a pin of `ps` below the top: pinned by the piece's own filter
      have hq' : q ∈ (filterAll (upF φ kv.2 d) ps).gowners := (List.mem_filter.mp hq).1
      exact LineUnion.gowner_pinned _ ps q hq' r (List.mem_filter.mp hr).1 hqs

/-- info: 'AbsSatBin.GraphPath.Model.FilterUnion.piece_pinned_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms piece_pinned_below

end AbsSatBin.GraphPath.Model.FilterUnion
