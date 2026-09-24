-- lean_project/AbsSat/GraphPath/Model/SegExactAdm.lean
import AbsSat.GraphPath.Model.SegExactFilter
import AbsSat.GraphPath.Model.AdjacentOwners

/-!
# `NodeAdmToChain` en dos piezas

`NodeAdmToChain` (si cada nodo de un tramo tiene una entrada admitida en el paso filtrado, hay una
cadena por el tramo y un nodo admitido) se parte en:

* **(a) `CommonAdm`, un Helly en un paso**: si cada nodo del tramo tiene su entrada admitida, hay UNA
  entrada admitida común a todas sus tablas. Es lo colectivo, reducido a un paso;
* **(b) `GapExact`, de la común a la cadena**: toda entrada `r` común a las tablas de un tramo, en un
  paso fuera de él, se extiende con el tramo a una cadena completa. Estructural: no mira el filtro.

`nodeAdmToChain_of`: (a) y (b) dan `NodeAdmToChain`.

**(b) cuando `r` es vecina del tramo** (justo debajo o justo encima) está demostrada
(`gapExact_below`, `gapExact_above`): en un estado del lector un owner un paso por debajo es padre (un
paso por encima, hijo) —`AdjacentOwners`—, la simetría mete el tramo en la tabla de `r`, y el tramo más
`r` es un tramo: `SegExact` da la cadena. Queda como hipótesis el caso con hueco (`GapExactFar`).

Medido (`row-degree nodeadm`, `dos_de_tres`): (a) 3.779 de 3.779; (b) 4.009 de 4.009.
-/

namespace AbsSat.GraphPath.Model.SegExactAdm

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview (filterAllAgg pruned_filterAllAgg)
open AbsSat.GraphPath.Model.FullExt (FullChainG)
open AbsSat.GraphPath.Model.TopGoodUp (Seg)
open AbsSat.GraphPath.Model.Extendable (upd upd_self upd_other)
open AbsSat.GraphPath.Model.SegExact (SegExact)
open AbsSat.GraphPath.Model.SegExactFilter (NodeAdmToChain)

/-- **(a) Helly en un paso**: si cada nodo del tramo tiene una entrada admitida en el paso filtrado,
hay una admitida común a todas sus tablas. -/
def CommonAdm (T : GPathM) (e : Int × List NodeId) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ T.current_step - 1 →
    Seg T sel lo hi → (e.1 < lo ∨ hi < e.1) →
    (∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj →
      ∃ r ∈ nj.owners, r ∈ T.gowners ∧ r.id.step = e.1 ∧ r.id ∈ e.2) →
    ∃ r ∈ T.gowners, r.id.step = e.1 ∧ r.id ∈ e.2 ∧
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj → r ∈ nj.owners

/-- The conclusion of (b) for a segment and a common entry `r` at step `k`. -/
def GapChain (T : GPathM) (sel : Int → PathNodeId) (lo hi k : Int) (r : PathNodeId) : Prop :=
  ∃ s, FullChainG T s ∧ (∀ j, lo ≤ j → j ≤ hi → s j = sel j) ∧ s k = r

/-- The hypotheses of (b): a segment, and an entry of the global at a step outside it, common to the
tables of all its nodes. -/
def GapCase (T : GPathM) (sel : Int → PathNodeId) (lo hi k : Int) (r : PathNodeId) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ T.current_step - 1 ∧ Seg T sel lo hi ∧
    0 ≤ k ∧ k ≤ T.current_step - 1 ∧ r ∈ T.gowners ∧ r.id.step = k ∧
    ∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj → r ∈ nj.owners

/-- **(b) `GapExact`**: toda entrada común de un tramo, fuera de él, se extiende con él a una cadena. -/
def GapExact (T : GPathM) : Prop :=
  ∀ sel lo hi k r, GapCase T sel lo hi k r → (k < lo ∨ hi < k) → GapChain T sel lo hi k r

/-- **(b) con hueco**: lo que queda como hipótesis, `r` a más de un paso del tramo. -/
def GapExactFar (T : GPathM) : Prop :=
  ∀ sel lo hi k r, GapCase T sel lo hi k r → (k < lo - 1 ∨ hi + 1 < k) → GapChain T sel lo hi k r

/-- **(a) y (b) dan `NodeAdmToChain`.** -/
theorem nodeAdmToChain_of (T : GPathM) (e : Int × List NodeId) (he0 : 0 ≤ e.1)
    (he1 : e.1 < T.current_step) (hA : CommonAdm T e) (hG : GapExact T) : NodeAdmToChain T e := by
  intro sel lo hi hlo hlh hhi hseg hout hadm
  obtain ⟨r, hrg, hrs, hrid, hrall⟩ := hA sel lo hi hlo hlh hhi hseg hout hadm
  obtain ⟨s, hs, hsel, hsr⟩ := hG sel lo hi e.1 r
    ⟨hlo, hlh, hhi, hseg, he0, by omega, hrg, hrs, hrall⟩ hout
  exact ⟨s, hs, hsel, by rw [hsr]; exact hrid⟩

-- ============================================================
-- (b) cuando `r` es vecina del tramo
-- ============================================================

/-- **`r` justo debajo del tramo**: es padre del nodo más bajo, y el tramo más `r` es un tramo. -/
theorem gapExact_below (T : GPathM) (a : AdjacentOwners.Adj T) (hsym : Threaded.OwnSymmetric T)
    (hS : SegExact T) (sel : Int → PathNodeId) (lo hi : Int) (r : PathNodeId)
    (hc : GapCase T sel lo hi (lo - 1) r) : GapChain T sel lo hi (lo - 1) r := by
  obtain ⟨hlo, hlh, hhi, ⟨hpc, hpo⟩, hk0, _, hrg, hrs, hrall⟩ := hc
  obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff T r).mp (a.ctx.gn r hrg))
  obtain ⟨hslo, hstlo⟩ := hpc.1 lo (Int.le_refl _) hlh
  obtain ⟨nlo, hnlo⟩ := Option.isSome_iff_exists.mp hslo
  have hrpar : r ∈ nlo.parents :=
    (AdjacentOwners.owners_below_iff_parents T a (sel lo) nlo hnlo (by rw [hstlo]; omega) r
      (by rw [hrs, hstlo])).mp (hrall lo (Int.le_refl _) hlh nlo hnlo)
  let sel' := upd sel (lo - 1) r
  have hlt : ∀ j, lo ≤ j → sel' j = sel j := fun j hj => upd_other sel _ r (by omega)
  have hpc' : Extendable.PartialChain T sel' (lo - 1) hi := by
    refine ⟨fun i hi0 hi1 => ?_, fun i hi0 hi1 => ?_⟩
    · rcases Int.lt_or_le i lo with h | h
      · have : i = lo - 1 := by omega
        subst this
        show (T.node? (upd sel (lo - 1) r (lo - 1))).isSome ∧ (upd sel (lo - 1) r (lo - 1)).id.step = lo - 1
        rw [upd_self, hnr]; exact ⟨rfl, hrs⟩
      · rw [hlt i h]; exact hpc.1 i h hi1
    · rcases Int.lt_or_le i lo with h | h
      · have : i = lo - 1 := by omega
        subst this
        show upd sel (lo - 1) r (lo - 1) ∈
          ((T.node? (upd sel (lo - 1) r (lo - 1 + 1))).map PNodeM.parents).getD []
        rw [upd_self, upd_other sel _ r (by omega), show lo - 1 + 1 = lo by omega, hnlo]
        exact hrpar
      · rw [hlt i h, hlt (i + 1) (by omega)]; exact hpc.2 i h hi1
  have hpo' : ∀ i j, lo - 1 ≤ i → lo - 1 ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, T.node? (sel' j) = some nj → sel' i ∈ nj.owners := by
    intro i j hi0 hj0 hi1 hj1 hij nj hnj
    rcases Int.lt_or_le i lo with hi2 | hi2
    · have : i = lo - 1 := by omega
      subst this
      have hj2 : lo ≤ j := by omega
      rw [hlt j hj2] at hnj
      show upd sel (lo - 1) r (lo - 1) ∈ nj.owners
      rw [upd_self]; exact hrall j hj2 hj1 nj hnj
    · rcases Int.lt_or_le j lo with hj2 | hj2
      · have : j = lo - 1 := by omega
        subst this
        rw [show sel' (lo - 1) = r from upd_self sel _ r, hnr] at hnj
        cases hnj
        rw [hlt i hi2]
        obtain ⟨hsi, _⟩ := hpc.1 i hi2 hi1
        obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsi
        exact hsym (sel i) ni r nr hni hnr (hrall i hi2 hi1 ni hni)
      · rw [hlt i hi2]; rw [hlt j hj2] at hnj
        exact hpo i j hi2 hj2 hi1 hj1 hij nj hnj
  obtain ⟨s, hs, hsel⟩ := hS sel' (lo - 1) hi hk0 (by omega) hhi hpc' hpo'
  refine ⟨s, hs, fun j hj0 hj1 => ?_, ?_⟩
  · rw [hsel j (by omega) hj1, hlt j hj0]
  · rw [hsel (lo - 1) (Int.le_refl _) (by omega)]; exact upd_self sel _ r

/-- **`r` justo encima del tramo**: es hijo del nodo más alto (y este, su padre), y el tramo más `r`
es un tramo. -/
theorem gapExact_above (T : GPathM) (a : AdjacentOwners.Adj T) (hsym : Threaded.OwnSymmetric T)
    (hS : SegExact T) (sel : Int → PathNodeId) (lo hi : Int) (r : PathNodeId)
    (hc : GapCase T sel lo hi (hi + 1) r) : GapChain T sel lo hi (hi + 1) r := by
  obtain ⟨hlo, hlh, hhi, ⟨hpc, hpo⟩, _, hk1, hrg, hrs, hrall⟩ := hc
  obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff T r).mp (a.ctx.gn r hrg))
  obtain ⟨hshi, hsthi⟩ := hpc.1 hi hlh (Int.le_refl _)
  obtain ⟨nhi, hnhi⟩ := Option.isSome_iff_exists.mp hshi
  have hrson : r ∈ nhi.sons :=
    (AdjacentOwners.owners_above_iff_sons T a (sel hi) nhi hnhi (by rw [hsthi]; omega) r
      (by rw [hrs, hsthi])).mp (hrall hi hlh (Int.le_refl _) nhi hnhi)
  have hhipar : sel hi ∈ nr.parents := by
    have := a.pms nhi (List.mem_of_find?_eq_some hnhi) r hrson nr (List.mem_of_find?_eq_some hnr)
      (node?_id_eq T r nr hnr)
    rwa [node?_id_eq T (sel hi) nhi hnhi] at this
  let sel' := upd sel (hi + 1) r
  have hlt : ∀ j, j ≤ hi → sel' j = sel j := fun j hj => upd_other sel _ r (by omega)
  have hpc' : Extendable.PartialChain T sel' lo (hi + 1) := by
    refine ⟨fun i hi0 hi1 => ?_, fun i hi0 hi1 => ?_⟩
    · rcases Int.lt_or_le hi i with h | h
      · have : i = hi + 1 := by omega
        subst this
        show (T.node? (upd sel (hi + 1) r (hi + 1))).isSome ∧ (upd sel (hi + 1) r (hi + 1)).id.step = hi + 1
        rw [upd_self, hnr]; exact ⟨rfl, hrs⟩
      · rw [hlt i h]; exact hpc.1 i hi0 h
    · rcases Int.lt_or_le i hi with h | h
      · rw [hlt i (by omega), hlt (i + 1) (by omega)]; exact hpc.2 i hi0 (by omega)
      · have : i = hi := by omega
        subst this
        show upd sel (i + 1) r i ∈ ((T.node? (upd sel (i + 1) r (i + 1))).map PNodeM.parents).getD []
        rw [upd_self, upd_other sel _ r (by omega), hnr]
        exact hhipar
  have hpo' : ∀ i j, lo ≤ i → lo ≤ j → i ≤ hi + 1 → j ≤ hi + 1 → i ≠ j →
      ∀ nj, T.node? (sel' j) = some nj → sel' i ∈ nj.owners := by
    intro i j hi0 hj0 hi1 hj1 hij nj hnj
    rcases Int.lt_or_le hi i with hi2 | hi2
    · have : i = hi + 1 := by omega
      subst this
      have hj2 : j ≤ hi := by omega
      rw [hlt j hj2] at hnj
      show upd sel (hi + 1) r (hi + 1) ∈ nj.owners
      rw [upd_self]; exact hrall j hj0 hj2 nj hnj
    · rcases Int.lt_or_le hi j with hj2 | hj2
      · have : j = hi + 1 := by omega
        subst this
        rw [show sel' (hi + 1) = r from upd_self sel _ r, hnr] at hnj
        cases hnj
        rw [hlt i hi2]
        obtain ⟨hsi, _⟩ := hpc.1 i hi0 hi2
        obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsi
        exact hsym (sel i) ni r nr hni hnr (hrall i hi0 hi2 ni hni)
      · rw [hlt i hi2]; rw [hlt j hj2] at hnj
        exact hpo i j hi0 hj0 hi2 hj2 hij nj hnj
  obtain ⟨s, hs, hsel⟩ := hS sel' lo (hi + 1) hlo (by omega) hk1 hpc' hpo'
  refine ⟨s, hs, fun j hj0 hj1 => ?_, ?_⟩
  · rw [hsel j hj0 (by omega), hlt j hj1]
  · rw [hsel (hi + 1) (by omega) (Int.le_refl _)]; exact upd_self sel _ r

/-- **(b) entera, desde el caso con hueco**: los vecinos están demostrados. -/
theorem gapExact_of_far (T : GPathM) (a : AdjacentOwners.Adj T) (hsym : Threaded.OwnSymmetric T)
    (hS : SegExact T) (hF : GapExactFar T) : GapExact T := by
  intro sel lo hi k r hc hout
  rcases hout with h | h
  · rcases Int.lt_or_le k (lo - 1) with h' | h'
    · exact hF sel lo hi k r hc (Or.inl h')
    · have : k = lo - 1 := by omega
      subst this
      exact gapExact_below T a hsym hS sel lo hi r hc
  · rcases Int.lt_or_le (hi + 1) k with h' | h'
    · exact hF sel lo hi k r hc (Or.inr h')
    · have : k = hi + 1 := by omega
      subst this
      exact gapExact_above T a hsym hS sel lo hi r hc

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.gapExact_of_far' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms gapExact_of_far

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.nodeAdmToChain_of' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms nodeAdmToChain_of

-- ============================================================
-- La escalera, con (a) y (b) con hueco en cada pin
-- ============================================================

open AbsSat.GraphPath.Model.SegExactFilter in
/-- **El lector sin retroceso decide 3-SAT**, con: `SegExact` en la línea final revisada, y en cada pin,
el Helly de un paso (`CommonAdm`) y la extensión con hueco (`GapExactFar`) del estado de antes. La
extensión desde una entrada vecina está demostrada. -/
theorem readerVerdictW_iff_of_commonAdm
    (hStart : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact (filterAllAgg kv.2 []))
    (hPin : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      CommonAdm g (q.id.step, [q.id]) ∧ GapExactFar g)
    (φ : AbsSat.Cnf.Cnf) (hwf : AbsSat.Cnf.WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ AbsSat.Cnf.Satisfiable φ := by
  refine SegExact.readerVerdictW_iff_of_readerSegExact ?_ φ hwf
  intro φ' hwf' kv hkv g hR hv
  obtain ⟨hm, hcs, _⟩ := ReaderAggRun.pureRunW_state φ' hwf' kv hkv
  have hpos : 0 < kv.2.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ'
  have ctx₀ : PinAliveChain.DCtx (filterAllAgg kv.2 []) :=
    { rd := ⟨kv.2, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms
      sn := AggInvariants.SN_filterAllAgg kv.2 [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot []
      pos := by rw [(pruned_filterAllAgg kv.2 []).step_eq]; exact hpos }
  revert hv
  induction hR with
  | start => exact hStart φ' hwf' kv hkv
  | pin g k q hR hv hk hq ih =>
    intro hv'
    have ctx := TopGoodLadder.dctx_of_readFromR _ ctx₀ g hR
    have rc := ReaderAgg.RCtx_of_readableAgg g ctx.rd
    have cG := Reader.Ctx_of_readable g (ReaderAgg.readable_of_readableAgg g ctx.rd) hv
    have c0 : StepFilter.SCtx g := ⟨rc, ctx.smp, cG.self, ctx.pos⟩
    have adj := AdjacentOwners.adj_of_readable g ctx.rd hv ctx.pms ctx.sn
    have hok : AggFixpoint.AggOk g := by
      obtain ⟨g₀, reqs, _, hg⟩ := ctx.rd
      rw [hg] at hv ⊢
      exact AggFixpoint.aggOk_reviewAgg _ hv
    have hsym := PinExactBoundary.ownSymmetric_of_aggOk g hok rc.snn rc.below adj.ctx.nodeval
    have hS := ih hv
    obtain ⟨hA, hF⟩ := hPin φ' hwf' kv hkv g k q hR hv hk hq
    have hqk : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
    have hkr : k ∈ intRange 0 (g.current_step - 1) := List.mem_of_find?_eq_some hk
    have hk0 := mem_intRange_lower hkr
    have hk1 := mem_intRange_upper hkr
    have he0 : 0 ≤ (q.id.step, [q.id]).1 := by show 0 ≤ q.id.step; rw [hqk]; exact hk0
    have he1 : (q.id.step, [q.id]).1 < g.current_step := by show q.id.step < _; rw [hqk]; omega
    rw [filterAllAgg_pin] at hv' ⊢
    have hG := gapExact_of_far g adj hsym hS hF
    have hN := nodeAdmToChain_of g _ he0 he1 hA hG
    have hAdm := admittedExt_of_nodeAdm g _ c0 he0 he1 hv' hN
    exact segExact_stepFilter_adm g _ c0 hS he0 he1 hAdm hv'

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.readerVerdictW_iff_of_commonAdm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_commonAdm

end AbsSat.GraphPath.Model.SegExactAdm
