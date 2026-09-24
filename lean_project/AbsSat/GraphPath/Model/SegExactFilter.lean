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

**La unión.** Una unión comprime mezclando historias, y deja tramos mezclados sin cadena que el review
no toca (son estables). No hace falta ningún invariante sobre ella: `CutKillsMix` —un filtro que corta
algo deja solo tramos con cadena en el estado de antes— basta para que, tras el primer requisito que
corta, `SegExact` valga (`segExact_stepFilter_cut`), venga de donde venga el estado.
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

/-- **Los supervivientes que cubren el paso filtrado tienen cadena antes**: todo tramo de `R` que cubre
el paso filtrado está en una cadena completa del estado de antes del filtro. Es lo único que el caso
«cubre» pide del estado de antes; lo da `SegExact T` o, sin nada sobre `T`, `CutKillsMix`. -/
def CoverChained (T : GPathM) (e : Int × List NodeId) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi →
    hi ≤ (reviewAgg (filterWeak T e)).current_step - 1 →
    Seg (reviewAgg (filterWeak T e)) sel lo hi → lo ≤ e.1 → e.1 ≤ hi →
    ∃ s, FullChainG T s ∧ ∀ j, lo ≤ j → j ≤ hi → s j = sel j

/-- **Un filtro de un paso y su review dan `SegExact`**, desde lo que piden sus tres casos: los tramos
que cubren el paso filtrado tenían cadena antes (`CoverChained`), y los que no lo cubren, una entrada
común admitida (`CommonAtFilter`) y una cadena con ella (`StepSegTriples`). -/
theorem segExact_stepFilter_gen (T : GPathM) (e : Int × List NodeId) (c0 : SCtx T)
    (he0 : 0 ≤ e.1) (he1 : e.1 < T.current_step)
    (hCov : CoverChained T e) (hCommon : CommonAtFilter T e) (hTri : StepSegTriples T e)
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
  obtain ⟨s, hs, hsel⟩ := hCov sel lo hi hlo hlh hhi ⟨hpc, hpo⟩ hle hle2
  obtain ⟨hsome, hstep⟩ := hpc.1 e.1 hle hle2
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hmem : sel e.1 ∈ R.gowners :=
    cR.ownGow _ n hn _ (cR.self _ n hn) (by rw [hstep]; exact he0)
      (by rw [hstep, hcsR]; exact he1)
  refine ⟨s, keep s hs ?_, hsel⟩
  rw [hsel e.1 hle hle2]
  exact clean _ hmem hstep

/-- `SegExact` antes del filtro da `CoverChained`: el superviviente era tramo antes. -/
theorem coverChained_of_segExact (T : GPathM) (e : Int × List NodeId) (hnd : NodupIds T)
    (hS : SegExact T) : CoverChained T e := by
  have hprR : Pruned T (reviewAgg (filterWeak T e)) :=
    Pruned.trans (ConservationCore.pruned_filterWeak T e) (pruned_reviewAgg _)
  intro sel lo hi hlo hlh hhi hseg _ _
  obtain ⟨hpc0, hpo0⟩ := seg_before T _ hprR hnd sel lo hi hseg.1 hseg.2
  exact hS sel lo hi hlo hlh (by rw [← hprR.step_eq]; exact hhi) hpc0 hpo0

/-- **Un filtro de un paso y su review conservan `SegExact`**, dadas las dos obligaciones del paso
filtrado. Los tramos que cubren ese paso no piden nada. -/
theorem segExact_stepFilter (T : GPathM) (e : Int × List NodeId) (c0 : SCtx T)
    (hS : SegExact T) (he0 : 0 ≤ e.1) (he1 : e.1 < T.current_step)
    (hCommon : CommonAtFilter T e) (hTri : StepSegTriples T e)
    (hv' : isValid (reviewAgg (filterWeak T e)) = true) :
    SegExact (reviewAgg (filterWeak T e)) :=
  segExact_stepFilter_gen T e c0 he0 he1 (coverChained_of_segExact T e c0.rc.nodup hS) hCommon hTri hv'

-- ============================================================
-- La compresión de la unión: un corte la deshace
-- ============================================================

/-- **Un filtro que corta deshace la mezcla** (postulado del autor: «las cadenas solo se forman si han
pasado por los envíos correctos»). Si el filtro quita al menos una entrada de la global, todo tramo que
sobrevive a él y a su review estaba en una cadena completa del estado de antes — aunque ese estado,
recién salido de una unión, tuviera tramos mezclados sin cadena.

Medido (`row-degree baddie`, semilla 1): los 1.260 filtros que cortan algo matan los 24 tramos sin
cadena de la unión; los 252 que no cortan nada, no. La unión revisada es punto fijo de todas las
etapas del review con esos tramos dentro: la mezcla es estable mientras nadie exija nada. -/
def CutKillsMix (T : GPathM) (e : Int × List NodeId) : Prop :=
  (∃ q ∈ T.gowners, q ∉ (filterWeak T e).gowners) →
    ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi →
      hi ≤ (reviewAgg (filterWeak T e)).current_step - 1 →
      Seg (reviewAgg (filterWeak T e)) sel lo hi →
      ∃ s, FullChainG T s ∧ ∀ j, lo ≤ j → j ≤ hi → s j = sel j

/-- **Tras un filtro que corta, `SegExact` sin nada sobre el estado de antes**: ni `SegExact T` ni que
no venga de una unión. El primer requisito de cada envío corta siempre (`baddie`: 168 de 168). -/
theorem segExact_stepFilter_cut (T : GPathM) (e : Int × List NodeId) (c0 : SCtx T)
    (he0 : 0 ≤ e.1) (he1 : e.1 < T.current_step)
    (hcut : ∃ q ∈ T.gowners, q ∉ (filterWeak T e).gowners) (hK : CutKillsMix T e)
    (hCommon : CommonAtFilter T e) (hTri : StepSegTriples T e)
    (hv' : isValid (reviewAgg (filterWeak T e)) = true) :
    SegExact (reviewAgg (filterWeak T e)) :=
  segExact_stepFilter_gen T e c0 he0 he1
    (fun sel lo hi hlo hlh hhi hseg _ _ => hK hcut sel lo hi hlo hlh hhi hseg) hCommon hTri hv'

/-- info: 'AbsSat.GraphPath.Model.SegExactFilter.segExact_stepFilter_cut' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms segExact_stepFilter_cut

/-- info: 'AbsSat.GraphPath.Model.SegExactFilter.segExact_stepFilter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms segExact_stepFilter

-- ============================================================
-- El lector: sus pines cortan siempre
-- ============================================================

/-- **Un pin del lector corta**: `firstChoice` solo elige un paso con dos owners de ids de mapa
distintos, así que fijar uno quita de la global al otro. -/
theorem pin_cuts (g : GPathM) (k : Int) (q : PathNodeId) (hk : ReaderExec.firstChoice g = some k)
    (hq : q ∈ ownersAt g.gowners k) :
    ∃ w ∈ g.gowners, w ∉ (filterWeak g (q.id.step, [q.id])).gowners := by
  have hch : PickInduction.choiceAt g k = true := List.find?_some hk
  have hqk : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
  unfold PickInduction.choiceAt at hch
  obtain ⟨q1, hq1, hr⟩ := List.any_eq_true.mp hch
  obtain ⟨r1, hr1, hne⟩ := List.any_eq_true.mp hr
  have hne' : q1.id ≠ r1.id := bne_iff_ne.mp hne
  have notIn : ∀ w ∈ ownersAt g.gowners k, w.id ≠ q.id →
      w ∈ g.gowners ∧ w ∉ (filterWeak g (q.id.step, [q.id])).gowners := by
    intro w hw hwq
    refine ⟨(List.mem_filter.mp hw).1, fun hmem => ?_⟩
    have hws : w.id.step = k := eq_of_beq (List.mem_filter.mp hw).2
    have := ((mem_filterWeak g _ w).mp hmem).2 (by rw [hws, hqk])
    exact hwq (List.mem_singleton.mp this)
  rcases decEq q1.id q.id with h1 | h1
  · obtain ⟨hw, hn⟩ := notIn q1 hq1 h1
    exact ⟨q1, hw, hn⟩
  · have hr1q : r1.id ≠ q.id := by rw [← h1]; exact fun e => hne' e.symm
    obtain ⟨hw, hn⟩ := notIn r1 hr1 hr1q
    exact ⟨r1, hw, hn⟩

theorem filterAllAgg_pin (g : GPathM) (q : PathNodeId) :
    filterAllAgg g [q.id] = reviewAgg (filterWeak g (q.id.step, [q.id])) := by
  unfold filterAllAgg
  simp only [List.foldl_cons, List.foldl_nil]
  rw [TablesExact.filterRequire_eq_filterWeak]

/-- **La hipótesis del lector, desde las tres obligaciones del paso fijado.** En cada pin del lector:
`CutKillsMix`, `CommonAtFilter` y `StepSegTriples` del filtro `(paso de q, [q])`. El pin corta siempre
(`pin_cuts`), así que no hace falta nada sobre el estado de antes. -/
theorem readerPinnedSegExact_of_obligations
    (hObl : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      CutKillsMix g (q.id.step, [q.id]) ∧ CommonAtFilter g (q.id.step, [q.id]) ∧
        StepSegTriples g (q.id.step, [q.id])) :
    SegExact.ReaderPinnedSegExact := by
  intro φ hwf kv hkv g k q hR hv hk hq hv'
  obtain ⟨hK, hC, hT⟩ := hObl φ hwf kv hkv g k q hR hv hk hq
  obtain ⟨hm, hcs, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hpos : 0 < kv.2.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ
  have ctx₀ : PinAliveChain.DCtx (filterAllAgg kv.2 []) :=
    { rd := ⟨kv.2, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms
      sn := AggInvariants.SN_filterAllAgg kv.2 [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot []
      pos := by rw [(pruned_filterAllAgg kv.2 []).step_eq]; exact hpos }
  have ctx := TopGoodLadder.dctx_of_readFromR _ ctx₀ g hR
  have cG := Reader.Ctx_of_readable g (ReaderAgg.readable_of_readableAgg g ctx.rd) hv
  have c0 : SCtx g := ⟨ReaderAgg.RCtx_of_readableAgg g ctx.rd, ctx.smp, cG.self, ctx.pos⟩
  have hqk : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
  have hkr : k ∈ intRange 0 (g.current_step - 1) := List.mem_of_find?_eq_some hk
  have hk0 := mem_intRange_lower hkr
  have hk1 := mem_intRange_upper hkr
  rw [filterAllAgg_pin] at hv' ⊢
  exact segExact_stepFilter_cut g _ c0 (by rw [hqk]; exact hk0) (by rw [hqk]; omega)
    (pin_cuts g k q hk hq) hK hC hT hv'

/-- info: 'AbsSat.GraphPath.Model.SegExactFilter.readerPinnedSegExact_of_obligations' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerPinnedSegExact_of_obligations

/-- **El lector sin retroceso decide 3-SAT, con tres obligaciones locales en cada pin**: el pin deshace
la mezcla (`CutKillsMix`), deja una entrada común admitida para los tramos que no lo cubren
(`CommonAtFilter`), y tramo y entrada están en una cadena del estado de antes (`StepSegTriples`). -/
theorem readerVerdictW_iff_of_pinObligations
    (hObl : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      CutKillsMix g (q.id.step, [q.id]) ∧ CommonAtFilter g (q.id.step, [q.id]) ∧
        StepSegTriples g (q.id.step, [q.id]))
    (φ : AbsSat.Cnf.Cnf) (hwf : AbsSat.Cnf.WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ AbsSat.Cnf.Satisfiable φ :=
  SegExact.readerVerdictW_iff_of_readerPinnedSegExact (readerPinnedSegExact_of_obligations hObl) φ hwf

/-- info: 'AbsSat.GraphPath.Model.SegExactFilter.readerVerdictW_iff_of_pinObligations' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pinObligations

-- ============================================================
-- La escalera sin `CutKillsMix`: `SegExact` en el primer estado, y los pines lo conservan
-- ============================================================

/-! `CutKillsMix` («cualquier filtro que corte deshace la mezcla») es probablemente demasiado fuerte:
la medición (`row-degree mixtrace`) muestra que los tramos mezclados caen por un **colapso masivo** —
un filtro real de envío lleva la medida de 4.692 a 2.303 en el primer `cleanInvalid₂`—, no por un
argumento local; un corte mínimo podría dejarlos vivos. La escalera no lo necesita: si el primer
estado del lector —la línea final revisada— no tiene tramos sin cadena (medido: 0 en las semillas 1 y
7), cada pin conserva `SegExact` con `segExact_stepFilter`. -/

/-- **Todo estado del lector cumple `SegExact`**, si el primero lo cumple y cada pin tiene sus dos
obligaciones del paso fijado. Por inducción sobre la lectura. -/
theorem segExact_readFromR (g₀ : GPathM) (ctx₀ : PinAliveChain.DCtx g₀)
    (h0 : isValid g₀ = true → SegExact g₀)
    (hPin : ∀ g k q, PinAliveChain.ReadFromR g₀ g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      CommonAtFilter g (q.id.step, [q.id]) ∧ StepSegTriples g (q.id.step, [q.id])) :
    ∀ g, PinAliveChain.ReadFromR g₀ g → isValid g = true → SegExact g := by
  intro g hR
  induction hR with
  | start => exact h0
  | pin g k q hR hv hk hq ih =>
    intro hv'
    have ctx := TopGoodLadder.dctx_of_readFromR _ ctx₀ g hR
    have cG := Reader.Ctx_of_readable g (ReaderAgg.readable_of_readableAgg g ctx.rd) hv
    have c0 : SCtx g := ⟨ReaderAgg.RCtx_of_readableAgg g ctx.rd, ctx.smp, cG.self, ctx.pos⟩
    obtain ⟨hC, hT⟩ := hPin g k q hR hv hk hq
    have hqk : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
    have hkr : k ∈ intRange 0 (g.current_step - 1) := List.mem_of_find?_eq_some hk
    have hk0 := mem_intRange_lower hkr
    have hk1 := mem_intRange_upper hkr
    rw [filterAllAgg_pin] at hv' ⊢
    exact segExact_stepFilter g _ c0 (ih hv) (by rw [hqk]; exact hk0) (by rw [hqk]; omega)
      hC hT hv'

/-- **El lector sin retroceso decide 3-SAT**, con: `SegExact` en la línea final revisada (su primer
estado), y en cada pin, `CommonAtFilter` y `StepSegTriples` del paso fijado. -/
theorem readerVerdictW_iff_of_startSegExact
    (hStart : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact (filterAllAgg kv.2 []))
    (hPin : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      CommonAtFilter g (q.id.step, [q.id]) ∧ StepSegTriples g (q.id.step, [q.id]))
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
  exact segExact_readFromR _ ctx₀ (hStart φ' hwf' kv hkv) (hPin φ' hwf' kv hkv) g hR hv

/-- info: 'AbsSat.GraphPath.Model.SegExactFilter.readerVerdictW_iff_of_startSegExact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_startSegExact

-- ============================================================
-- Una sola obligación por pin: `AdmittedExt`
-- ============================================================

/-- **La completitud tras un filtro, por tramos**: todo tramo del revisado que no cubre el paso
filtrado se extiende, en el estado de antes, a una cadena completa cuyo nodo en ese paso está
admitido. Es lo único que el caso «no cubre» usa: esa cadena pasa el filtro y sobrevive. -/
def AdmittedExt (T : GPathM) (e : Int × List NodeId) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi →
    hi ≤ (reviewAgg (filterWeak T e)).current_step - 1 →
    Seg (reviewAgg (filterWeak T e)) sel lo hi → (e.1 < lo ∨ hi < e.1) →
    ∃ s, FullChainG T s ∧ (∀ j, lo ≤ j → j ≤ hi → s j = sel j) ∧ (s e.1).id ∈ e.2

/-- **Las dos obligaciones de antes dan `AdmittedExt`**: la entrada común `c` es de la global del
revisado, luego admitida. `AdmittedExt` es la más débil de las dos juntas. -/
theorem admittedExt_of_common_triples (T : GPathM) (e : Int × List NodeId)
    (hCommon : CommonAtFilter T e) (hTri : StepSegTriples T e) : AdmittedExt T e := by
  have hprX : Pruned (filterWeak T e) (reviewAgg (filterWeak T e)) := pruned_reviewAgg _
  intro sel lo hi hlo hlh hhi hseg hout
  obtain ⟨c, hcR, hcs, hcall⟩ := hCommon sel lo hi hlo hlh hhi hseg hout
  obtain ⟨s, hs, hsel, hsc⟩ := hTri sel lo hi c hlo hlh hhi hseg hout hcR hcs hcall
  refine ⟨s, hs, hsel, ?_⟩
  rw [hsc]
  exact ((mem_filterWeak T e c).mp (hprX.gowners_sub c hcR)).2 hcs

/-- **Un filtro de un paso y su review conservan `SegExact`, con una sola obligación**
(`AdmittedExt`) además de `SegExact` del estado de antes. -/
theorem segExact_stepFilter_adm (T : GPathM) (e : Int × List NodeId) (c0 : SCtx T)
    (hS : SegExact T) (he0 : 0 ≤ e.1) (he1 : e.1 < T.current_step) (hA : AdmittedExt T e)
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
  have hcov := coverChained_of_segExact T e c0.rc.nodup hS
  intro sel lo hi hlo hlh hhi hpc hpo
  rcases Int.lt_or_le e.1 lo with hlt | hle
  · obtain ⟨s, hs, hsel, hadm⟩ := hA sel lo hi hlo hlh hhi ⟨hpc, hpo⟩ (Or.inl hlt)
    exact ⟨s, keep s hs hadm, hsel⟩
  rcases Int.lt_or_le hi e.1 with hgt | hle2
  · obtain ⟨s, hs, hsel, hadm⟩ := hA sel lo hi hlo hlh hhi ⟨hpc, hpo⟩ (Or.inr hgt)
    exact ⟨s, keep s hs hadm, hsel⟩
  obtain ⟨s, hs, hsel⟩ := hcov sel lo hi hlo hlh hhi ⟨hpc, hpo⟩ hle hle2
  obtain ⟨hsome, hstep⟩ := hpc.1 e.1 hle hle2
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hmem : sel e.1 ∈ R.gowners :=
    cR.ownGow _ n hn _ (cR.self _ n hn) (by rw [hstep]; exact he0)
      (by rw [hstep, hcsR]; exact he1)
  refine ⟨s, keep s hs ?_, hsel⟩
  rw [hsel e.1 hle hle2]
  exact clean _ hmem hstep

/-- **El lector sin retroceso decide 3-SAT, con una sola obligación por pin**: `SegExact` en la línea
final revisada, y en cada pin, `AdmittedExt` —todo tramo que sobrevive al pin tenía, antes, una cadena
completa por un nodo admitido en el paso fijado—. -/
theorem readerVerdictW_iff_of_admittedExt
    (hStart : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact (filterAllAgg kv.2 []))
    (hPin : ∀ φ : AbsSat.Cnf.Cnf, AbsSat.Cnf.WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      AdmittedExt g (q.id.step, [q.id]))
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
    have cG := Reader.Ctx_of_readable g (ReaderAgg.readable_of_readableAgg g ctx.rd) hv
    have c0 : SCtx g := ⟨ReaderAgg.RCtx_of_readableAgg g ctx.rd, ctx.smp, cG.self, ctx.pos⟩
    have hqk : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
    have hkr : k ∈ intRange 0 (g.current_step - 1) := List.mem_of_find?_eq_some hk
    have hk0 := mem_intRange_lower hkr
    have hk1 := mem_intRange_upper hkr
    have hA := hPin φ' hwf' kv hkv g k q hR hv hk hq
    rw [filterAllAgg_pin] at hv' ⊢
    exact segExact_stepFilter_adm g _ c0 (ih hv) (by rw [hqk]; exact hk0) (by rw [hqk]; omega)
      hA hv'

/-- info: 'AbsSat.GraphPath.Model.SegExactFilter.readerVerdictW_iff_of_admittedExt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms readerVerdictW_iff_of_admittedExt

end AbsSat.GraphPath.Model.SegExactFilter
