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
`r` es un tramo: `SegExact` da la cadena. **Con hueco** (`gapExactFar_of_steps`), por inducción sobre la
distancia: cada paso alarga el tramo con un nodo `u` del paso vecino, común a sus tablas y en la tabla de
`r` (`GapStepBelow`, `GapStepAbove`), y `r` sigue siendo común por simetría.

Así, `readerVerdictW_iff_of_helly`: el lector decide 3-SAT con `SegExact` en la línea final revisada y,
en cada pin, **tres afirmaciones de un solo paso** sobre el estado de antes (`CommonAdm`,
`GapStepBelow`, `GapStepAbove`).

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
-- (a) desde `Nested`: la tabla del nodo más cercano es la más pequeña
-- ============================================================

/-- **La tabla del nodo más cercano es la más pequeña**: para un tramo y un paso `k` fuera de él, las
entradas (de la global) en `k` de la tabla del nodo del tramo más cercano a `k` están en las tablas de
todos los nodos del tramo.

Medido (`row-degree nested`, `dos_de_tres`): se cumple en todos los envíos (8.256) y en todos los
estados del lector **tras un pin** (5.138); falla solo en el primer estado del lector (84 de 1.164),
que es la unión final: la compresión de la unión lo rompe y el primer corte lo recupera. -/
def Nested (T : GPathM) : Prop :=
  (∀ (sel : Int → PathNodeId) (lo hi k : Int), 0 ≤ lo → lo ≤ hi → hi ≤ T.current_step - 1 →
    Seg T sel lo hi → k < lo →
    ∀ nn, T.node? (sel lo) = some nn → ∀ r ∈ nn.owners, r ∈ T.gowners → r.id.step = k →
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj → r ∈ nj.owners) ∧
  (∀ (sel : Int → PathNodeId) (lo hi k : Int), 0 ≤ lo → lo ≤ hi → hi ≤ T.current_step - 1 →
    Seg T sel lo hi → hi < k →
    ∀ nn, T.node? (sel hi) = some nn → ∀ r ∈ nn.owners, r ∈ T.gowners → r.id.step = k →
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj → r ∈ nj.owners)

/-- **`Nested` da `CommonAdm`**: la entrada admitida del nodo más cercano es común a todo el tramo. -/
theorem commonAdm_of_nested (T : GPathM) (e : Int × List NodeId) (hN : Nested T) : CommonAdm T e := by
  intro sel lo hi hlo hlh hhi hseg hout hadm
  rcases hout with h | h
  · obtain ⟨hs, _⟩ := hseg.1.1 lo (Int.le_refl _) hlh
    obtain ⟨nn, hnn⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨r, hr, hrg, hrs, hrid⟩ := hadm lo (Int.le_refl _) hlh nn hnn
    exact ⟨r, hrg, hrs, hrid, hN.1 sel lo hi e.1 hlo hlh hhi hseg h nn hnn r hr hrg hrs⟩
  · obtain ⟨hs, _⟩ := hseg.1.1 hi hlh (Int.le_refl _)
    obtain ⟨nn, hnn⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨r, hr, hrg, hrs, hrid⟩ := hadm hi hlh (Int.le_refl _) nn hnn
    exact ⟨r, hrg, hrs, hrid, hN.2 sel lo hi e.1 hlo hlh hhi hseg h nn hnn r hr hrg hrs⟩

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.commonAdm_of_nested' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms commonAdm_of_nested

-- ============================================================
-- (b) con hueco, por pasos: un Helly de un paso cada vez
-- ============================================================

/-- **Alargar un tramo un paso hacia abajo** con un nodo `u` común a sus tablas, en el paso de debajo:
`u` es padre del nodo más bajo (`AdjacentOwners`) y la simetría mete el tramo en la tabla de `u`. -/
theorem seg_extend_below (T : GPathM) (a : AdjacentOwners.Adj T) (hsym : Threaded.OwnSymmetric T)
    (sel : Int → PathNodeId) (lo hi : Int) (hlh : lo ≤ hi) (hlo1 : 1 ≤ lo) (hseg : Seg T sel lo hi)
    (u : PathNodeId) (hug : u ∈ T.gowners) (hus : u.id.step = lo - 1)
    (hu : ∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj → u ∈ nj.owners) :
    Seg T (upd sel (lo - 1) u) (lo - 1) hi := by
  obtain ⟨hpc, hpo⟩ := hseg
  obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff T u).mp (a.ctx.gn u hug))
  obtain ⟨hslo, hstlo⟩ := hpc.1 lo (Int.le_refl _) hlh
  obtain ⟨nlo, hnlo⟩ := Option.isSome_iff_exists.mp hslo
  have hupar : u ∈ nlo.parents :=
    (AdjacentOwners.owners_below_iff_parents T a (sel lo) nlo hnlo (by rw [hstlo]; omega) u
      (by rw [hus, hstlo])).mp (hu lo (Int.le_refl _) hlh nlo hnlo)
  have hlt : ∀ j, lo ≤ j → upd sel (lo - 1) u j = sel j := fun j hj => upd_other sel _ u (by omega)
  refine ⟨⟨fun i hi0 hi1 => ?_, fun i hi0 hi1 => ?_⟩, fun i j hi0 hj0 hi1 hj1 hij nj hnj => ?_⟩
  · rcases Int.lt_or_le i lo with h | h
    · have : i = lo - 1 := by omega
      subst this
      rw [upd_self, hnu]; exact ⟨rfl, hus⟩
    · rw [hlt i h]; exact hpc.1 i h hi1
  · rcases Int.lt_or_le i lo with h | h
    · have : i = lo - 1 := by omega
      subst this
      rw [upd_self, upd_other sel _ u (by omega), show lo - 1 + 1 = lo by omega, hnlo]
      exact hupar
    · rw [hlt i h, hlt (i + 1) (by omega)]; exact hpc.2 i h hi1
  · rcases Int.lt_or_le i lo with hi2 | hi2
    · have : i = lo - 1 := by omega
      subst this
      have hj2 : lo ≤ j := by omega
      rw [hlt j hj2] at hnj
      rw [upd_self]; exact hu j hj2 hj1 nj hnj
    · rcases Int.lt_or_le j lo with hj2 | hj2
      · have : j = lo - 1 := by omega
        subst this
        rw [upd_self, hnu] at hnj
        cases hnj
        rw [hlt i hi2]
        obtain ⟨hsi, _⟩ := hpc.1 i hi2 hi1
        obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsi
        exact hsym (sel i) ni u nu hni hnu (hu i hi2 hi1 ni hni)
      · rw [hlt i hi2]; rw [hlt j hj2] at hnj
        exact hpo i j hi2 hj2 hi1 hj1 hij nj hnj

/-- **Alargar un tramo un paso hacia arriba**, con un nodo `u` común en el paso de encima. -/
theorem seg_extend_above (T : GPathM) (a : AdjacentOwners.Adj T) (hsym : Threaded.OwnSymmetric T)
    (sel : Int → PathNodeId) (lo hi : Int) (hlh : lo ≤ hi) (hhi2 : hi ≤ T.current_step - 2)
    (hseg : Seg T sel lo hi)
    (u : PathNodeId) (hug : u ∈ T.gowners) (hus : u.id.step = hi + 1)
    (hu : ∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj → u ∈ nj.owners) :
    Seg T (upd sel (hi + 1) u) lo (hi + 1) := by
  obtain ⟨hpc, hpo⟩ := hseg
  obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff T u).mp (a.ctx.gn u hug))
  obtain ⟨hshi, hsthi⟩ := hpc.1 hi hlh (Int.le_refl _)
  obtain ⟨nhi, hnhi⟩ := Option.isSome_iff_exists.mp hshi
  have huson : u ∈ nhi.sons :=
    (AdjacentOwners.owners_above_iff_sons T a (sel hi) nhi hnhi (by rw [hsthi]; omega) u
      (by rw [hus, hsthi])).mp (hu hi hlh (Int.le_refl _) nhi hnhi)
  have hhipar : sel hi ∈ nu.parents := by
    have := a.pms nhi (List.mem_of_find?_eq_some hnhi) u huson nu (List.mem_of_find?_eq_some hnu)
      (node?_id_eq T u nu hnu)
    rwa [node?_id_eq T (sel hi) nhi hnhi] at this
  have hlt : ∀ j, j ≤ hi → upd sel (hi + 1) u j = sel j := fun j hj => upd_other sel _ u (by omega)
  refine ⟨⟨fun i hi0 hi1 => ?_, fun i hi0 hi1 => ?_⟩, fun i j hi0 hj0 hi1 hj1 hij nj hnj => ?_⟩
  · rcases Int.lt_or_le hi i with h | h
    · have : i = hi + 1 := by omega
      subst this
      rw [upd_self, hnu]; exact ⟨rfl, hus⟩
    · rw [hlt i h]; exact hpc.1 i hi0 h
  · rcases Int.lt_or_le i hi with h | h
    · rw [hlt i (by omega), hlt (i + 1) (by omega)]; exact hpc.2 i hi0 (by omega)
    · have : i = hi := by omega
      subst this
      rw [upd_self, upd_other sel _ u (by omega), hnu]
      exact hhipar
  · rcases Int.lt_or_le hi i with hi2 | hi2
    · have : i = hi + 1 := by omega
      subst this
      have hj2 : j ≤ hi := by omega
      rw [hlt j hj2] at hnj
      rw [upd_self]; exact hu j hj0 hj2 nj hnj
    · rcases Int.lt_or_le hi j with hj2 | hj2
      · have : j = hi + 1 := by omega
        subst this
        rw [upd_self, hnu] at hnj
        cases hnj
        rw [hlt i hi2]
        obtain ⟨hsi, _⟩ := hpc.1 i hi0 hi2
        obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsi
        exact hsym (sel i) ni u nu hni hnu (hu i hi0 hi2 ni hni)
      · rw [hlt i hi2]; rw [hlt j hj2] at hnj
        exact hpo i j hi0 hj0 hi2 hj2 hij nj hnj

/-- **Un paso hacia `r`, por debajo**: si `r` es común a un tramo y está a más de un paso por debajo,
hay en el paso de justo debajo del tramo un nodo común a sus tablas que está en la tabla de `r`.
Un Helly de un paso: el tramo y `r` juntos. -/
def GapStepBelow (T : GPathM) : Prop :=
  ∀ sel lo hi k r, GapCase T sel lo hi k r → k < lo - 1 →
    ∃ u ∈ T.gowners, u.id.step = lo - 1 ∧
      (∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj → u ∈ nj.owners) ∧
      ∀ nr, T.node? r = some nr → u ∈ nr.owners

/-- **Un paso hacia `r`, por encima.** -/
def GapStepAbove (T : GPathM) : Prop :=
  ∀ sel lo hi k r, GapCase T sel lo hi k r → hi + 1 < k →
    ∃ u ∈ T.gowners, u.id.step = hi + 1 ∧
      (∀ j, lo ≤ j → j ≤ hi → ∀ nj, T.node? (sel j) = some nj → u ∈ nj.owners) ∧
      ∀ nr, T.node? r = some nr → u ∈ nr.owners

/-- **(b) con hueco, desde los pasos**: por inducción sobre la distancia, cada paso alarga el tramo
con un nodo común hacia `r` (que sigue siendo común por simetría), hasta que `r` es vecina. -/
theorem gapExactFar_of_steps (T : GPathM) (a : AdjacentOwners.Adj T) (hsym : Threaded.OwnSymmetric T)
    (hS : SegExact T) (hB : GapStepBelow T) (hA : GapStepAbove T) : GapExactFar T := by
  have rnode : ∀ r, r ∈ T.gowners → ∃ nr, T.node? r = some nr := fun r hr =>
    Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff T r).mp (a.ctx.gn r hr))
  have below : ∀ n : Nat, ∀ sel lo hi k r, GapCase T sel lo hi k r → lo - k = (n : Int) + 1 →
      GapChain T sel lo hi k r := by
    intro n
    induction n with
    | zero =>
      intro sel lo hi k r hc hd
      have : k = lo - 1 := by omega
      subst this
      exact gapExact_below T a hsym hS sel lo hi r hc
    | succ n ih =>
      intro sel lo hi k r hc hd
      obtain ⟨hlo, hlh, hhi, hseg, hk0, hk1, hrg, hrs, hrall⟩ := hc
      obtain ⟨u, hug, hus, hu, hur⟩ :=
        hB sel lo hi k r ⟨hlo, hlh, hhi, hseg, hk0, hk1, hrg, hrs, hrall⟩ (by omega)
      have hseg' := seg_extend_below T a hsym sel lo hi hlh (by omega) hseg u hug hus hu
      obtain ⟨nr, hnr⟩ := rnode r hrg
      have hlt : ∀ j, lo ≤ j → upd sel (lo - 1) u j = sel j := fun j hj => upd_other sel _ u (by omega)
      have hc' : GapCase T (upd sel (lo - 1) u) (lo - 1) hi k r := by
        refine ⟨by omega, by omega, hhi, hseg', hk0, hk1, hrg, hrs, fun j hj0 hj1 nj hnj => ?_⟩
        rcases Int.lt_or_le j lo with h | h
        · have : j = lo - 1 := by omega
          subst this
          rw [upd_self] at hnj
          exact hsym r nr u nj hnr hnj (hur nr hnr)
        · rw [hlt j h] at hnj; exact hrall j h hj1 nj hnj
      obtain ⟨s, hs, hsel, hsk⟩ := ih (upd sel (lo - 1) u) (lo - 1) hi k r hc' (by omega)
      exact ⟨s, hs, fun j hj0 hj1 => by rw [hsel j (by omega) hj1, hlt j hj0], hsk⟩
  have above : ∀ n : Nat, ∀ sel lo hi k r, GapCase T sel lo hi k r → k - hi = (n : Int) + 1 →
      GapChain T sel lo hi k r := by
    intro n
    induction n with
    | zero =>
      intro sel lo hi k r hc hd
      have : k = hi + 1 := by omega
      subst this
      exact gapExact_above T a hsym hS sel lo hi r hc
    | succ n ih =>
      intro sel lo hi k r hc hd
      obtain ⟨hlo, hlh, hhi, hseg, hk0, hk1, hrg, hrs, hrall⟩ := hc
      obtain ⟨u, hug, hus, hu, hur⟩ :=
        hA sel lo hi k r ⟨hlo, hlh, hhi, hseg, hk0, hk1, hrg, hrs, hrall⟩ (by omega)
      have hseg' := seg_extend_above T a hsym sel lo hi hlh (by omega) hseg u hug hus hu
      obtain ⟨nr, hnr⟩ := rnode r hrg
      have hlt : ∀ j, j ≤ hi → upd sel (hi + 1) u j = sel j := fun j hj => upd_other sel _ u (by omega)
      have hc' : GapCase T (upd sel (hi + 1) u) lo (hi + 1) k r := by
        refine ⟨hlo, by omega, by omega, hseg', hk0, hk1, hrg, hrs, fun j hj0 hj1 nj hnj => ?_⟩
        rcases Int.lt_or_le hi j with h | h
        · have : j = hi + 1 := by omega
          subst this
          rw [upd_self] at hnj
          exact hsym r nr u nj hnr hnj (hur nr hnr)
        · rw [hlt j h] at hnj; exact hrall j hj0 h nj hnj
      obtain ⟨s, hs, hsel, hsk⟩ := ih (upd sel (hi + 1) u) lo (hi + 1) k r hc' (by omega)
      exact ⟨s, hs, fun j hj0 hj1 => by rw [hsel j hj0 (by omega), hlt j hj1], hsk⟩
  intro sel lo hi k r hc hout
  rcases hout with h | h
  · exact below (lo - k - 1).toNat sel lo hi k r hc (by omega)
  · exact above (k - hi - 1).toNat sel lo hi k r hc (by omega)

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.gapExactFar_of_steps' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms gapExactFar_of_steps

-- ============================================================
-- Los pasos hacia una entrada lejana, desde `Nested` y `AggOk`
-- ============================================================

/-- The pairwise test of the aggressive review, read at one step: two nodes that own each other
share an entry of that step. -/
private theorem shared_at (T : GPathM) (hok : AggFixpoint.AggOk T) (cT : Pinned.Ctx T)
    (x : PathNodeId) (nx : PNodeM) (hnx : T.node? x = some nx) (w : PathNodeId) (nw : PNodeM)
    (hnw : T.node? w = some nw) (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < T.current_step)
    (hw0 : 0 ≤ w.id.step) (hw1 : w.id.step < T.current_step) (hwx : w ∈ nx.owners)
    (m : Int) (hm0 : 0 ≤ m) (hm1 : m < T.current_step) :
    ∃ u ∈ nx.owners, u.id.step = m ∧ u ∈ nw.owners := by
  have hagg := hok x nx w nw hnx hnw hx0 hx1 hw0 hw1 hwx (cT.nodeval x nx hnx) (cT.nodeval w nw hnw)
  have hsh := List.all_eq_true.mp hagg.2 m (mem_intRange hm0 (by omega))
  have hent : hasStepEntry nw.owners m = true :=
    List.all_eq_true.mp (owners_ok_of_isValidNode T nw (cT.nodeval w nw hnw)) m
      (mem_intRange hm0 (by omega))
  rw [hent] at hsh
  simp only [Bool.not_true, Bool.false_or] at hsh
  obtain ⟨u, hu, huw⟩ := List.any_eq_true.mp hsh
  exact ⟨u, (List.mem_filter.mp hu).1, eq_of_beq (List.mem_filter.mp hu).2, List.elem_iff.mp huw⟩

/-- **`Nested` y `AggOk` dan el paso hacia abajo**: el nodo más bajo del tramo y `r` comparten una
entrada `u` en el paso de justo debajo (`AggOk`), y `Nested` la pone en la tabla de todo el tramo. -/
theorem gapStepBelow_of_nested (T : GPathM) (hN : Nested T) (hok : AggFixpoint.AggOk T)
    (cT : Pinned.Ctx T) : GapStepBelow T := by
  intro sel lo hi k r hc hk
  obtain ⟨hlo, hlh, hhi, hseg, hk0, _, hrg, hrs, hrall⟩ := hc
  obtain ⟨hs, hst⟩ := hseg.1.1 lo (Int.le_refl _) hlh
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff T r).mp (cT.gn r hrg))
  obtain ⟨u, hu, hus, hur⟩ := shared_at T hok cT (sel lo) nx hnx r nr hnr (by rw [hst]; omega)
    (by rw [hst]; omega) (by rw [hrs]; omega) (by rw [hrs]; omega)
    (hrall lo (Int.le_refl _) hlh nx hnx) (lo - 1) (by omega) (by omega)
  have hug : u ∈ T.gowners := cT.ownGow _ nx hnx u hu (by rw [hus]; omega) (by rw [hus]; omega)
  refine ⟨u, hug, hus, hN.1 sel lo hi (lo - 1) hlo hlh hhi hseg (by omega) nx hnx u hu hug hus, ?_⟩
  intro nr' hnr'
  rw [hnr] at hnr'
  cases hnr'
  exact hur

/-- **Y hacia arriba.** -/
theorem gapStepAbove_of_nested (T : GPathM) (hN : Nested T) (hok : AggFixpoint.AggOk T)
    (cT : Pinned.Ctx T) : GapStepAbove T := by
  intro sel lo hi k r hc hk
  obtain ⟨hlo, hlh, hhi, hseg, _, hk1, hrg, hrs, hrall⟩ := hc
  obtain ⟨hs, hst⟩ := hseg.1.1 hi hlh (Int.le_refl _)
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff T r).mp (cT.gn r hrg))
  obtain ⟨u, hu, hus, hur⟩ := shared_at T hok cT (sel hi) nx hnx r nr hnr (by rw [hst]; omega)
    (by rw [hst]; omega) (by rw [hrs]; omega) (by rw [hrs]; omega)
    (hrall hi hlh (Int.le_refl _) nx hnx) (hi + 1) (by omega) (by omega)
  have hug : u ∈ T.gowners := cT.ownGow _ nx hnx u hu (by rw [hus]; omega) (by rw [hus]; omega)
  refine ⟨u, hug, hus, hN.2 sel lo hi (hi + 1) hlo hlh hhi hseg (by omega) nx hnx u hu hug hus, ?_⟩
  intro nr' hnr'
  rw [hnr] at hnr'
  cases hnr'
  exact hur

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.gapStepBelow_of_nested' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms gapStepBelow_of_nested

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

open AbsSat.GraphPath.Model.SegExactFilter in
/-- **El lector sin retroceso decide 3-SAT, con Hellys de un paso**: `SegExact` en la línea final
revisada, y en cada pin, tres afirmaciones de un solo paso sobre el estado de antes: `CommonAdm` (una
entrada admitida común al tramo), `GapStepBelow` y `GapStepAbove` (un nodo común al tramo y a una
entrada común lejana, en el paso vecino del tramo). -/
theorem readerVerdictW_iff_of_helly
    (hStart : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact (filterAllAgg kv.2 []))
    (hPin : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      CommonAdm g (q.id.step, [q.id]) ∧ GapStepBelow g ∧ GapStepAbove g)
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
    obtain ⟨hA, hBl, hAb⟩ := hPin φ' hwf' kv hkv g k q hR hv hk hq
    have hF := gapExactFar_of_steps g adj hsym hS hBl hAb
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

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.readerVerdictW_iff_of_helly' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_helly

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.readerVerdictW_iff_of_commonAdm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_commonAdm

-- ============================================================
-- La escalera con `Nested`: la unión aparte
-- ============================================================

/-- **El lector sin retroceso decide 3-SAT**, con:
* en su primer estado (la línea final revisada, una unión): `SegExact`, y en sus pines, `CommonAdm` y los
  pasos hacia una entrada lejana —ahí `Nested` falla (84 de 1.164 en `dos_de_tres`) por la compresión—;
* tras cada pin: `Nested` (la tabla del nodo más cercano es la más pequeña). Medido sin fallos en todos
  los estados tras un pin y en los envíos. -/
theorem readerVerdictW_iff_of_nested
    (hStart : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact (filterAllAgg kv.2 []))
    (hStart0 : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ k q,
      isValid (filterAllAgg kv.2 []) = true →
      ReaderExec.firstChoice (filterAllAgg kv.2 []) = some k →
      q ∈ ownersAt (filterAllAgg kv.2 []).gowners k →
      CommonAdm (filterAllAgg kv.2 []) (q.id.step, [q.id]) ∧
        GapStepBelow (filterAllAgg kv.2 []) ∧ GapStepAbove (filterAllAgg kv.2 []))
    (hNested : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      isValid (filterAllAgg g [q.id]) = true → Nested (filterAllAgg g [q.id]))
    (φ : AbsSat.Cnf.Cnf) (hwf : AbsSat.Cnf.WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ AbsSat.Cnf.Satisfiable φ := by
  refine readerVerdictW_iff_of_helly hStart ?_ φ hwf
  intro φ' hwf' kv hkv g k q hR hv hk hq
  cases hR with
  | start => exact hStart0 φ' hwf' kv hkv k q hv hk hq
  | pin g₁ k₁ q₁ hR₁ hv₁ hk₁ hq₁ =>
    have hN := hNested φ' hwf' kv hkv g₁ k₁ q₁ hR₁ hv₁ hk₁ hq₁ hv
    obtain ⟨hm, hcs, _⟩ := ReaderAggRun.pureRunW_state φ' hwf' kv hkv
    have hpos : 0 < kv.2.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ'
    have ctx₀ : PinAliveChain.DCtx (filterAllAgg kv.2 []) :=
      { rd := ⟨kv.2, [], hm.rctx, rfl⟩
        pms := AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms
        sn := AggInvariants.SN_filterAllAgg kv.2 [] hm.sn
        smp := AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot []
        pos := by rw [(pruned_filterAllAgg kv.2 []).step_eq]; exact hpos }
    have ctx := TopGoodLadder.dctx_of_readFromR _ ctx₀ _
      (PinAliveChain.ReadFromR.pin g₁ k₁ q₁ hR₁ hv₁ hk₁ hq₁)
    have cG := Reader.Ctx_of_readable _ (ReaderAgg.readable_of_readableAgg _ ctx.rd) hv
    have hok : AggFixpoint.AggOk (filterAllAgg g₁ [q₁.id]) := by
      have hv2 := hv
      obtain ⟨g₀, reqs, _, hg⟩ := ctx.rd
      rw [hg] at hv2 ⊢
      exact AggFixpoint.aggOk_reviewAgg _ hv2
    exact ⟨commonAdm_of_nested _ _ hN, gapStepBelow_of_nested _ hN hok cG,
      gapStepAbove_of_nested _ hN hok cG⟩

/-- info: 'AbsSat.GraphPath.Model.SegExactAdm.readerVerdictW_iff_of_nested' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_nested

end AbsSat.GraphPath.Model.SegExactAdm
