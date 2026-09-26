-- lean/improves_bin/AbsSatBin/GraphPath/Model/FilterUnion.lean
import AbsSatBin.GraphPath.Model.LineUnion

/-!
# Filtering the union stays inside the union of the filtered pieces (FU)

Measured (`julia/improves_bin/test_3sat/probes/glfstar_probe.jl`, FU): filtering a joined state by pins leaves,
entry by entry, only entries of its pieces filtered by the same pins (5 337 of 5 337). This module proves it from
`MapCert` of the joined state — step 2 of the induction of `GLF` (`docs/context/ambfar.md` §4.2κ).

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

end AbsSatBin.GraphPath.Model.FilterUnion
