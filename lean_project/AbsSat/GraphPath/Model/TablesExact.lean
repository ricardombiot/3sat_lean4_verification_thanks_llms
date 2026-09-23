-- lean_project/AbsSat/GraphPath/Model/TablesExact.lean
import AbsSat.GraphPath.Model.SendSeq
import AbsSat.GraphPath.Model.AggFixpoint

/-!
# Las tablas dicen la verdad

`q'` en la tabla de `r` (los dos en la tabla global) significa que hay una cadena completa dentro de
la global que pasa por los dos. Es lo que la tabla de owners **quiere decir**, y es lo que las parejas
de `PinPairs` y `SendPairs` piden en un solo paso.

Medido (`row-degree pairall`, `pairline`): 0 fallos en los estados del lector (293.377 parejas,
semilla 1), en la línea y en los estados intermedios del envío paso a paso.
-/

namespace AbsSat.GraphPath.Model.TablesExact

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.FullExt (FullChainG chainSound_of_fullChain fullChain_of_chainSound)
open AbsSat.GraphPath.Model.PinPairs (FrontierPairs)
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak)
open AbsSat.GraphPath.Model.StepFilter (SCtx mem_filterWeak fullChain_stepFilter)

/-- **Las tablas dicen la verdad**: cada pareja de la tabla de un nodo está en una cadena completa
dentro de la global. -/
def TablesExact (T : GPathM) : Prop :=
  ∀ r ∈ T.gowners, ∀ q' ∈ T.gowners, q'.id.step ≠ r.id.step →
    0 ≤ r.id.step → r.id.step < T.current_step →
    (∃ nr, T.node? r = some nr ∧ q' ∈ nr.owners) →
    ∃ s, FullChainG T s ∧ s r.id.step = r ∧ s q'.id.step = q'

/-- Las parejas de cualquier paso son un caso. -/
theorem frontierPairs_of_tablesExact (T : GPathM) (h : TablesExact T) (k : Int) :
    FrontierPairs T k := by
  intro r hr q' hq' hq's hne h0 h1 hown
  obtain ⟨s, hs, hsr, hsq⟩ := h r hr q' hq' (by rw [hq's]; exact fun e => hne e.symm) h0 h1 hown
  rw [hq's] at hsq
  exact ⟨s, hs, hsr, hsq⟩

/-- **El review sin filtro conserva la verdad de las tablas**: sus tablas son más pequeñas, y la
cadena del estado de antes es `ChainSound` y sobrevive. -/
theorem tablesExact_reviewAgg (g : GPathM) (hnd : NodupIds g)
    (hself : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (hsmp : Sons.SMP g) (hroot : Sons.RootAtZero g) (hnr : Parents.NotRoot g)
    (hpos : 0 < g.current_step) (h : TablesExact g) : TablesExact (reviewAgg g) := by
  have hpr := pruned_reviewAgg g
  rintro r hr q' hq' hne h0 h1 ⟨nr, hnrR, hown⟩
  obtain ⟨n0, hn0, hid, ho, _⟩ := hpr.nodes_derived nr (List.mem_of_find?_eq_some hnrR)
  have hn0g : g.node? r = some n0 := by
    have := node?_of_mem hnd n0 hn0
    rw [← hid, node?_id_eq _ r nr hnrR] at this
    exact this
  obtain ⟨s, hs, hsr, hsq⟩ := h r (hpr.gowners_sub r hr) q' (hpr.gowners_sub q' hq') hne h0
    (by rw [← hpr.step_eq]; exact h1) ⟨n0, hn0g, ho q' hown⟩
  exact ⟨s, fullChain_of_chainSound _ s (ChainSound_reviewAgg g s
    (chainSound_of_fullChain g hself hsmp hroot hnr hpos s hs)), hsr, hsq⟩

/-- info: 'AbsSat.GraphPath.Model.TablesExact.tablesExact_reviewAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesExact_reviewAgg

-- ============================================================
-- Un filtro de un paso
-- ============================================================

/-- **Las ternas que sobreviven al paso filtrado**: si tras el filtro `(k, A)` y su review `r` y `q'`
están en la tabla una de otra y `c` del paso `k` está en las dos tablas, las tres estaban ya en una
cadena completa común dentro de la global de antes. Es lo que `row-degree triplestep` mide. -/
def StepTriples (T : GPathM) (e : Int × List NodeId) : Prop :=
  ∀ r ∈ (reviewAgg (filterWeak T e)).gowners, ∀ q' ∈ (reviewAgg (filterWeak T e)).gowners,
    ∀ c ∈ (reviewAgg (filterWeak T e)).gowners, r.id.step ≠ e.1 → q'.id.step ≠ e.1 →
    q'.id.step ≠ r.id.step → c.id.step = e.1 →
    (∃ nr, (reviewAgg (filterWeak T e)).node? r = some nr ∧ q' ∈ nr.owners ∧ c ∈ nr.owners) →
    (∃ nq, (reviewAgg (filterWeak T e)).node? q' = some nq ∧ c ∈ nq.owners) →
    ∃ s, FullChainG T s ∧ s r.id.step = r ∧ s q'.id.step = q' ∧ s e.1 = c

/-- En el revisado, una tabla de un nodo del revisado viene de la del mismo nodo antes. -/
theorem node_before {T R : GPathM} (hpr : Pruned T R) (hnd : NodupIds T) (x : PathNodeId)
    (nx : PNodeM) (hnx : R.node? x = some nx) :
    ∃ n0, T.node? x = some n0 ∧ ∀ y ∈ nx.owners, y ∈ n0.owners := by
  obtain ⟨n0, hn0, hid, ho, _⟩ := hpr.nodes_derived nx (List.mem_of_find?_eq_some hnx)
  have := node?_of_mem hnd n0 hn0
  rw [← hid, node?_id_eq _ x nx hnx] at this
  exact ⟨n0, this, ho⟩

/-- **Un filtro de un paso y su review conservan la verdad de las tablas**, desde las parejas y las
ternas de ese paso que sobreviven. El review agresivo da la entrada común `c` del paso filtrado
(`AggFixpoint.aggOk_reviewAgg`); la cadena por `r`, `q'` y `c` pasa el filtro y sobrevive. -/
theorem tablesExact_stepFilter (T : GPathM) (e : Int × List NodeId) (c0 : SCtx T)
    (hE : TablesExact T) (he0 : 0 ≤ e.1) (he1 : e.1 < T.current_step)
    (hTri : StepTriples T e) (hv' : isValid (reviewAgg (filterWeak T e)) = true) :
    TablesExact (reviewAgg (filterWeak T e)) := by
  let R := reviewAgg (filterWeak T e)
  have hprX : Pruned (filterWeak T e) R := pruned_reviewAgg _
  have hprR : Pruned T R := Pruned.trans (ConservationCore.pruned_filterWeak T e) hprX
  have rcX : Reader.RCtx (filterWeak T e) :=
    RCtx_of_keeps (ReaderAggRun.keeps_filterWeak T e) c0.rc
  have hRd : ReadableAgg R := ⟨filterWeak T e, [], rcX, rfl⟩
  have cR := Reader.Ctx_of_readable R (readable_of_readableAgg R hRd) hv'
  have hcsR : R.current_step = T.current_step := hprR.step_eq
  have keep := fullChain_stepFilter T e c0.self c0.smp c0.rc.rootz c0.rc.shape.notroot c0.pos
  have clean : ∀ y ∈ R.gowners, y.id.step = e.1 → y.id ∈ e.2 :=
    fun y hy hys => ((mem_filterWeak T e y).mp (hprX.gowners_sub y hy)).2 hys
  have hnd := c0.rc.nodup
  rintro r hr q' hq' hne h0 h1 ⟨nr, hnrR, hown⟩
  rw [hcsR] at h1
  have hrT := hprR.gowners_sub r hr
  have hqT := hprR.gowners_sub q' hq'
  obtain ⟨n0, hn0, ho0⟩ := node_before hprR hnd r nr hnrR
  have rcR := RCtx_of_readableAgg R hRd
  have stepOf : ∀ y ∈ R.gowners, 0 ≤ y.id.step ∧ y.id.step < T.current_step := by
    intro y hy
    obtain ⟨m, hm, hmid⟩ := rcR.gn y hy
    rw [← hmid, ← hcsR]
    exact ⟨rcR.snn m hm, rcR.below m hm⟩
  obtain ⟨hq0, hq1⟩ := stepOf q' hq'
  -- uno de los dos está en el paso filtrado: basta su pareja
  rcases int_eq_or_ne q'.id.step e.1 with hqk | hqk
  · obtain ⟨s, hs, hsr, hsq⟩ := hE r hrT q' hqT hne h0 h1 ⟨n0, hn0, ho0 q' hown⟩
    exact ⟨s, keep s hs (by rw [← hqk, hsq]; exact clean q' hq' hqk), hsr, hsq⟩
  rcases int_eq_or_ne r.id.step e.1 with hrk | hrk
  · obtain ⟨s, hs, hsr, hsq⟩ := hE r hrT q' hqT hne h0 h1 ⟨n0, hn0, ho0 q' hown⟩
    exact ⟨s, keep s hs (by rw [← hrk, hsr]; exact clean r hr hrk), hsr, hsq⟩
  -- el caso general: la entrada común del paso filtrado, que da el review agresivo
  obtain ⟨nq, hnqR⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff R q').mp (cR.gn q' hq'))
  have hagg := AggFixpoint.aggOk_reviewAgg (filterWeak T e) hv' r nr q' nq hnrR hnqR h0
    (by rw [hcsR]; exact h1) hq0 (by rw [hcsR]; exact hq1) hown (cR.nodeval r nr hnrR)
    (cR.nodeval q' nq hnqR)
  have hsh := List.all_eq_true.mp hagg.2 e.1 (mem_intRange he0 (by rw [hcsR]; omega))
  have hqent : hasStepEntry nq.owners e.1 = true :=
    List.all_eq_true.mp (owners_ok_of_isValidNode R nq (cR.nodeval q' nq hnqR)) e.1
      (mem_intRange he0 (by rw [hcsR]; omega))
  rw [hqent] at hsh
  simp only [Bool.not_true, Bool.false_or] at hsh
  obtain ⟨c, hc, hcq⟩ := List.any_eq_true.mp hsh
  have hcr : c ∈ nr.owners := (List.mem_filter.mp hc).1
  have hcs : c.id.step = e.1 := eq_of_beq (List.mem_filter.mp hc).2
  have hcq' : c ∈ nq.owners := List.elem_iff.mp hcq
  have hcR : c ∈ R.gowners :=
    cR.ownGow r nr hnrR c hcr (by rw [hcs]; exact he0) (by rw [hcs, hcsR]; exact he1)
  obtain ⟨s, hs, hsr, hsq, hsc⟩ := hTri r hr q' hq' c hcR hrk hqk hne hcs
    ⟨nr, hnrR, hown, hcr⟩ ⟨nq, hnqR, hcq'⟩
  exact ⟨s, keep s hs (by rw [hsc]; exact clean c hcR hcs), hsr, hsq⟩

/-- info: 'AbsSat.GraphPath.Model.TablesExact.tablesExact_stepFilter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesExact_stepFilter

/-- **Un pin es un filtro de un paso** con un solo id admitido. -/
theorem filterRequire_eq_filterWeak (g : GPathM) (req : NodeId) :
    filterRequire g req = filterWeak g (req.step, [req]) := by
  simp only [filterRequire, filterWeak, List.contains_cons, List.contains_nil, Bool.or_false]

end AbsSat.GraphPath.Model.TablesExact
