-- lean_project/AbsSat/GraphPath/Model/SegExactFilter.lean
import AbsSat.GraphPath.Model.SegExactUp

/-!
# Un filtro de un paso y su review: la obligación, por tramos

La versión por tramos de `TablesExact.tablesExact_stepFilter`. Tras el filtro `e = (k, A)` (el envío
de una cláusula, o el pin del lector, que es el caso de un solo id) y su review agresivo `R`, cada
tramo de `R`:

* **si cubre el paso filtrado**, es gratis: su nodo en el paso `k` sobrevivió al filtro, así que está
  admitido; su cadena de antes pasa por él, pasa el filtro y sobrevive (`fullChain_stepFilter`);
* **si no lo cubre**, hacen falta dos cosas, las dos sobre el paso filtrado:
  * `CommonAtFilter`: una entrada admitida `c` del paso `k` **común a todo el tramo** en `R`. Es la
    parte colectiva, localizada en un solo paso. Para parejas la daba el review agresivo
    (`aggOk_reviewAgg`: dos tablas comparten algo en cada paso); para tramos es la pregunta de fondo;
  * `StepSegTriples`: el tramo y `c` están juntos en una cadena completa **del estado de antes**. Es la
    generalización por tramos de `StepTriples` (ternas), que se midió sin fallos.

`segExact_stepFilter`: con esas dos, `SegExact` pasa el filtro.
-/

namespace AbsSat.GraphPath.Model.SegExactFilter

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.FullExt (FullChainG)
open AbsSat.GraphPath.Model.TopGoodUp (Seg)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak)
open AbsSat.GraphPath.Model.StepFilter (SCtx mem_filterWeak fullChain_stepFilter)
open AbsSat.GraphPath.Model.SegExact (SegExact seg_before)

/-- **La parte colectiva, en el paso filtrado**: todo tramo de `R` que no cubre ese paso tiene en él
una entrada de la global común a las tablas de todos sus nodos. -/
def CommonAtFilter (T : GPathM) (e : Int × List NodeId) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi →
    hi ≤ (reviewAgg (filterWeak T e)).current_step - 1 →
    Seg (reviewAgg (filterWeak T e)) sel lo hi → (e.1 < lo ∨ hi < e.1) →
    ∃ c ∈ (reviewAgg (filterWeak T e)).gowners, c.id.step = e.1 ∧
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj, (reviewAgg (filterWeak T e)).node? (sel j) = some nj →
        c ∈ nj.owners

/-- **Las «ternas» por tramos**: un tramo de `R` y una entrada común `c` del paso filtrado están
juntos en una cadena completa del estado de antes. -/
def StepSegTriples (T : GPathM) (e : Int × List NodeId) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int) (c : PathNodeId), 0 ≤ lo → lo ≤ hi →
    hi ≤ (reviewAgg (filterWeak T e)).current_step - 1 →
    Seg (reviewAgg (filterWeak T e)) sel lo hi → (e.1 < lo ∨ hi < e.1) →
    c ∈ (reviewAgg (filterWeak T e)).gowners → c.id.step = e.1 →
    (∀ j, lo ≤ j → j ≤ hi → ∀ nj, (reviewAgg (filterWeak T e)).node? (sel j) = some nj →
      c ∈ nj.owners) →
    ∃ s, FullChainG T s ∧ (∀ j, lo ≤ j → j ≤ hi → s j = sel j) ∧ s e.1 = c

/-- **Un filtro de un paso y su review conservan `SegExact`**, dadas las dos obligaciones del paso
filtrado. Los tramos que cubren ese paso no piden nada. -/
theorem segExact_stepFilter (T : GPathM) (e : Int × List NodeId) (c0 : SCtx T)
    (hS : SegExact T) (he0 : 0 ≤ e.1) (he1 : e.1 < T.current_step)
    (hCommon : CommonAtFilter T e) (hTri : StepSegTriples T e)
    (hv' : isValid (reviewAgg (filterWeak T e)) = true) :
    SegExact (reviewAgg (filterWeak T e)) := by
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
  intro sel lo hi hlo hlh hhi hpc hpo
  obtain ⟨hpc0, hpo0⟩ := seg_before T R hprR c0.rc.nodup sel lo hi hpc hpo
  have hhiT : hi ≤ T.current_step - 1 := by rw [← hcsR]; exact hhi
  have outside : e.1 < lo ∨ hi < e.1 →
      ∃ s, FullChainG R s ∧ ∀ j, lo ≤ j → j ≤ hi → s j = sel j := by
    -- the common admitted entry of the filtered step, and the chain through both
    intro hout
    obtain ⟨c, hcR, hcs, hcall⟩ := hCommon sel lo hi hlo hlh hhi ⟨hpc, hpo⟩ hout
    obtain ⟨s, hs, hsel, hsc⟩ := hTri sel lo hi c hlo hlh hhi ⟨hpc, hpo⟩ hout hcR hcs hcall
    refine ⟨s, keep s hs ?_, hsel⟩
    rw [hsc]
    exact clean c hcR hcs
  rcases Int.lt_or_le e.1 lo with hlt | hle
  · exact outside (Or.inl hlt)
  rcases Int.lt_or_le hi e.1 with hgt | hle2
  · exact outside (Or.inr hgt)
  -- the segment covers the filtered step: its node there was admitted
  obtain ⟨s, hs, hsel⟩ := hS sel lo hi hlo hlh hhiT hpc0 hpo0
  obtain ⟨hsome, hstep⟩ := hpc.1 e.1 hle hle2
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hmem : sel e.1 ∈ R.gowners :=
    cR.ownGow _ n hn _ (cR.self _ n hn) (by rw [hstep]; exact he0)
      (by rw [hstep, hcsR]; exact he1)
  refine ⟨s, keep s hs ?_, hsel⟩
  rw [hsel e.1 hle hle2]
  exact clean _ hmem hstep

/-- info: 'AbsSat.GraphPath.Model.SegExactFilter.segExact_stepFilter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms segExact_stepFilter

end AbsSat.GraphPath.Model.SegExactFilter
