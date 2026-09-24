-- lean_project/AbsSat/GraphPath/Model/SegExact.lean
import AbsSat.GraphPath.Model.TopGoodLadder
import AbsSat.GraphPath.Model.TablesExact

/-!
# Todo tramo está en una cadena completa

`TablesExact` dice que cada **pareja** de una tabla está en una cadena completa dentro de la global.
Aquí, la versión por **tramos**: todo tramo (enlazado por padres, poseído por pares) se extiende,
dentro de la global, a una cadena completa del paso 0 al último que coincide con él en sus pasos.

Medido (`row-degree segexact`): 0 tramos sin cadena en la línea, en los envíos revisados y en los
estados del lector.

Por qué es el invariante bueno para la parte colectiva:

* **implica `SegGood`** (`segGood_of_segExact`): el nodo de la cadena en un paso fuera del tramo está
  en la tabla de todos los nodos del tramo, porque los nodos de una cadena completa se poseen entre sí.
  Es una entrada común compatible con **todo** el tramo a la vez;
* **el review lo conserva sin más** (`segExact_reviewAgg`): un tramo de después era tramo antes (las
  tablas y los enlaces solo encogen), su cadena es sana, y el review no rompe cadenas sanas.

Con `ReaderSegExact` en lugar de `ReaderSegGood`, la escalera sigue en pie
(`readerVerdictW_iff_of_readerSegExact`), y la parte colectiva ya no está en las vueltas del review:
está en **UP** (los tramos nuevos) y en el **pin** del lector (los tramos que sobreviven al filtro).
-/

namespace AbsSat.GraphPath.Model.SegExact

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.FullExt (FullChainG chainSound_of_fullChain fullChain_of_chainSound)
open AbsSat.GraphPath.Model.TopGoodUp (SegGood)

/-- **Todo tramo está en una cadena completa dentro de la global.** -/
def SegExact (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ g.current_step - 1 →
    Extendable.PartialChain g sel lo hi →
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∃ s, FullChainG g s ∧ ∀ j, lo ≤ j → j ≤ hi → s j = sel j

/-- **Implica `SegGood`**: la cadena da la entrada común en cada paso fuera del tramo. -/
theorem segGood_of_segExact (g : GPathM) (h : SegExact g) : SegGood g := by
  intro sel lo hi hlo hlh hhi hpc hpo i hi0 hic hout
  obtain ⟨s, hs, hsel⟩ := h sel lo hi hlo hlh hhi hpc hpo
  refine ⟨s i, (hs.1.1.1 i hi0 hic).2, ?_⟩
  intro j hj0 hj1 nj hnj
  have hsj : g.node? (s j) = some nj := by rw [hsel j hj0 hj1]; exact hnj
  have hne : i ≠ j := by intro e; subst e; omega
  exact hs.1.2 i j hi0 (by omega) hic (by omega) hne nj hsj

-- ============================================================
-- El review lo conserva
-- ============================================================

/-- A node after a narrowing comes from a node before, with the same id, fewer owners and fewer
parents. -/
theorem node_before (g g' : GPathM) (hpr : Pruned g g') (hnd : NodupIds g) (p : PathNodeId)
    (n' : PNodeM) (hn' : g'.node? p = some n') :
    ∃ n, g.node? p = some n ∧ (∀ q ∈ n'.owners, q ∈ n.owners) ∧ (∀ c ∈ n'.parents, c ∈ n.parents) := by
  obtain ⟨n, hn, hid, hown, hpar⟩ := hpr.nodes_derived n' (List.mem_of_find?_eq_some hn')
  refine ⟨n, ?_, hown, hpar⟩
  rw [← node?_id_eq _ p n' hn', hid]
  exact node?_of_mem hnd n hn

/-- **Un tramo de después era tramo antes.** -/
theorem seg_before (g g' : GPathM) (hpr : Pruned g g') (hnd : NodupIds g) (sel : Int → PathNodeId)
    (lo hi : Int) (hpc : Extendable.PartialChain g' sel lo hi)
    (hpo : ∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, g'.node? (sel j) = some nj → sel i ∈ nj.owners) :
    Extendable.PartialChain g sel lo hi ∧
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) := by
  refine ⟨⟨fun i hlo hhi => ?_, fun i hlo hhi => ?_⟩, fun i j hi hj hi' hj' hne nj hnj => ?_⟩
  · obtain ⟨hs, hstep⟩ := hpc.1 i hlo hhi
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨n, hn, _, _⟩ := node_before g g' hpr hnd _ n' hn'
    exact ⟨by rw [hn]; rfl, hstep⟩
  · have hl := hpc.2 i hlo hhi
    obtain ⟨hs, _⟩ := hpc.1 (i + 1) (by omega) hhi
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hs
    rw [hn'] at hl
    obtain ⟨n, hn, _, hpar⟩ := node_before g g' hpr hnd _ n' hn'
    rw [hn]
    exact hpar _ hl
  · obtain ⟨hs, _⟩ := hpc.1 j hj hj'
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨n, hn, hown, _⟩ := node_before g g' hpr hnd _ n' hn'
    rw [hnj] at hn
    cases hn
    exact hown _ (hpo i j hi hj hi' hj' hne n' hn')

/-- **El review agresivo conserva `SegExact`**: la cadena del tramo en el estado de antes es sana y
sobrevive entera. -/
theorem segExact_reviewAgg (g : GPathM) (hnd : NodupIds g)
    (hself : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (hsmp : Sons.SMP g) (hroot : Sons.RootAtZero g) (hnr : Parents.NotRoot g)
    (hpos : 0 < g.current_step) (h : SegExact g) : SegExact (reviewAgg g) := by
  have hpr := pruned_reviewAgg g
  intro sel lo hi hlo hlh hhi hpc hpo
  obtain ⟨hpc0, hpo0⟩ := seg_before g _ hpr hnd sel lo hi hpc hpo
  obtain ⟨s, hs, hsel⟩ := h sel lo hi hlo hlh (by rw [← hpr.step_eq]; exact hhi) hpc0 hpo0
  exact ⟨s, fullChain_of_chainSound _ s (ChainSound_reviewAgg g s
    (chainSound_of_fullChain g hself hsmp hroot hnr hpos s hs)), hsel⟩

-- ============================================================
-- La escalera, con `SegExact` en los estados del lector
-- ============================================================

/-- **La hipótesis por tramos**: en todo estado válido que el lector visita, todo tramo está en una
cadena completa. -/
def ReaderSegExact : Prop :=
  ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g,
    PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true → SegExact g

theorem readerSegGood_of_readerSegExact (h : ReaderSegExact) : TopGoodLadder.ReaderSegGood :=
  fun φ hwf kv hkv g hr hv => segGood_of_segExact g (h φ hwf kv hkv g hr hv)

/-- **El lector sin retroceso decide 3-SAT, con «todo tramo está en una cadena completa» en sus
estados como única hipótesis.** -/
theorem readerVerdictW_iff_of_readerSegExact (h : ReaderSegExact) (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  TopGoodLadder.readerVerdictW_iff_of_readerSegGood (readerSegGood_of_readerSegExact h) φ hwf

/-- info: 'AbsSat.GraphPath.Model.SegExact.segGood_of_segExact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms segGood_of_segExact

/-- info: 'AbsSat.GraphPath.Model.SegExact.segExact_reviewAgg' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms segExact_reviewAgg

/-- info: 'AbsSat.GraphPath.Model.SegExact.readerVerdictW_iff_of_readerSegExact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_readerSegExact

-- ============================================================
-- El primer estado del lector no pide nada
-- ============================================================

/-! La escalera solo consume, de cada estado que el lector visita, **una** cadena sana
(`PinAliveChain.readerVerdictW_of_chainsR`). En el primer estado ya la hay: la de la asignación que
satisface (`hsel0`). Así que la hipótesis solo hace falta **tras un pin**, y un pin es un filtro de un
solo id: justo donde `SegExactFilter.segExact_stepFilter_cut` da `SegExact`. El primer estado —la línea
final revisada, que es una unión y puede tener tramos mezclados sin cadena— queda fuera. -/

/-- **La hipótesis, solo en los estados tras un pin.** -/
def ReaderPinnedSegExact : Prop :=
  ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
    PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
    ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
    isValid (filterAllAgg g [q.id]) = true → SegExact (filterAllAgg g [q.id])

/-- **El lector sin retroceso decide 3-SAT, con `SegExact` solo en los estados tras un pin.** -/
theorem readerVerdictW_iff_of_readerPinnedSegExact (h : ReaderPinnedSegExact) (φ : Cnf)
    (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine ⟨fun h' => ReaderExec.readerVerdictW_sound φ hwf h', fun hsat => ?_⟩
  obtain ⟨a, hsa⟩ := hsat
  obtain ⟨g, hmem, hcs, _, sel, hsel⟩ := ConservationImproves.pureRunW_full_chain φ a hwf hsa
  have hm := (ReaderAggRun.pureRunW_state φ hwf _ hmem).1
  have hsel0 : ChainSound (filterAllAgg g []) sel :=
    ChainSound_filterAllAgg g [] sel hsel (fun _ hreq => absurd hreq List.not_mem_nil)
  have hpos : 0 < g.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ
  have ctx₀ : PinAliveChain.DCtx (filterAllAgg g []) :=
    { rd := ⟨g, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg g [] hm.pms
      sn := AggInvariants.SN_filterAllAgg g [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg g hm.smp hm.rctx.shape.notroot []
      pos := by rw [(pruned_filterAllAgg g []).step_eq]; exact hpos }
  refine PinAliveChain.readerVerdictW_of_chainsR φ _ hmem
    (PickInduction.isValid_of_ChainG _ sel hsel0.chain) (fun g' hR hv' => ?_)
  cases hR with
  | start => exact ⟨sel, hsel0⟩
  | pin g₁ k q hR₁ hv₁ hk hq =>
    have hS := h φ hwf _ hmem g₁ k q hR₁ hv₁ hk hq hv'
    have ctx := TopGoodLadder.dctx_of_readFromR _ ctx₀ _ (PinAliveChain.ReadFromR.pin g₁ k q hR₁ hv₁ hk hq)
    have rc := ReaderAgg.RCtx_of_readableAgg _ ctx.rd
    have cR := Reader.Ctx_of_readable _ (ReaderAgg.readable_of_readableAgg _ ctx.rd) hv'
    -- an entry of the global at step 0, as a one-node segment
    have hent := hasStepEntry_of_isValid _ hv' 0 (Int.le_refl 0) ctx.pos
    simp only [hasStepEntry, List.any_eq_true] at hent
    obtain ⟨q0, hq0, hq0s⟩ := hent
    have hq0s' : q0.id.step = 0 := eq_of_beq hq0s
    obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp
      ((GownersNodes.hasNode_iff _ q0).mp (cR.gn q0 hq0))
    have hseg : Extendable.PartialChain (filterAllAgg g₁ [q.id]) (fun _ => q0) 0 0 :=
      ⟨fun i hi1 hi2 => by
          have : i = 0 := by omega
          subst this; exact ⟨by rw [hn0]; rfl, hq0s'⟩,
        fun i hi1 hi2 => by omega⟩
    obtain ⟨s, hs, _⟩ := hS (fun _ => q0) 0 0 (Int.le_refl 0) (Int.le_refl 0)
      (by have := ctx.pos; omega) hseg (fun i j hi hj hi' hj' hne => absurd (by omega) hne)
    exact ⟨s, chainSound_of_fullChain _ cR.self ctx.smp rc.rootz rc.shape.notroot ctx.pos s hs⟩

/-- info: 'AbsSat.GraphPath.Model.SegExact.readerVerdictW_iff_of_readerPinnedSegExact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_readerPinnedSegExact

end AbsSat.GraphPath.Model.SegExact
