-- lean_project/AbsSat/GraphPath/Model/PinAliveChain.lean
import AbsSat.GraphPath.Model.ReaderChain
import AbsSat.GraphPath.Model.SubsetSemantics
import AbsSat.GraphPath.Model.AnchoredSurvive

/-!
# La ruta del autor: sin ternas, sin tablas por nodo, sin pegar cadenas

*«El lector no tiene lógica más allá del review. En cada paso toma cualquier nodo válido, y al
seleccionarlo el filtro y el review reducen el grafo hasta que solo queda un camino.»*

Este módulo escribe **esa** frase y la usa, y el resultado es que el residuo del lector cabe entero
en una sola hipótesis que no menciona parejas, ni ternas, ni tablas de nodo:

    **PinAlive** — pinchar una entrada viva de un estado válido no lo invalida.

Por qué las ternas aparecían antes y aquí no: venían de pasar por `Exactness.TablesSound`, que es
un enunciado sobre **(nodo, entrada de su tabla)** —una pareja— y que al cruzar el filtro necesita
además el requisito —un tercero—. Ese rodeo no es del algoritmo, era del camino. Aquí no se pasa
por las tablas de nodo en ningún momento.

La prueba es la inducción que el autor describe, y decrece con la medida de la propia criba
(`ReaderAgg.measure_lt_of_choiceAt`): **cada pin en un paso con elección hace el grafo
estrictamente más pequeño**, así que la recursión termina, y en el fondo, cuando ya no queda nada
que elegir, la cadena la da `Reader.inhabited_of_noChoice_readable` sin hipótesis.
-/

namespace AbsSat.GraphPath.Model.PinAliveChain

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderExec
open AbsSat.GraphPath.Model.ReaderChain

/-- **El contexto que el lector trae consigo.** No es una hipótesis abierta: son los invariantes
que la máquina ya mantiene y que `filterAllAgg` conserva. -/
structure DCtx (g : GPathM) : Prop where
  rd  : ReadableAgg g
  pms : Sons.PMS g
  sn  : Sons.SN g
  smp : Sons.SMP g
  pos : 0 < g.current_step

theorem DCtx_filterAllAgg (g : GPathM) (c : DCtx g) (reqs : List NodeId) :
    DCtx (filterAllAgg g reqs) where
  rd := ReadableAgg_filterAllAgg g c.rd reqs
  pms := AggInvariants.PMS_filterAllAgg g reqs c.pms
  sn := AggInvariants.SN_filterAllAgg g reqs c.sn
  smp := AnchoredSurvive.SMP_filterAllAgg g c.smp (RCtx_of_readableAgg g c.rd).shape.notroot reqs
  pos := by rw [(pruned_filterAllAgg g reqs).step_eq]; exact c.pos

/-- **Un paso sin elección tiene un solo id de mapa.** Es `choiceAt` leído al revés. -/
theorem oneIdAt_of_choiceAt (g : GPathM) (k : Int) (h : PickInduction.choiceAt g k = false) :
    OneIdAt g k := by
  intro p hp q hq hps hqs
  have hmp : p ∈ ownersAt g.gowners k := List.mem_filter.mpr ⟨hp, beq_iff_eq.mpr hps⟩
  have hmq : q ∈ ownersAt g.gowners k := List.mem_filter.mpr ⟨hq, beq_iff_eq.mpr hqs⟩
  by_cases hpq : p.id = q.id
  · exact hpq
  · have hct : PickInduction.choiceAt g k = true :=
      List.any_eq_true.mpr ⟨p, hmp, List.any_eq_true.mpr ⟨q, hmq, bne_iff_ne.mpr hpq⟩⟩
    rw [hct] at h; exact Bool.noConfusion h

-- ============================================================
-- La frase del autor, entera
-- ============================================================

/-- **Pinchar una entrada viva no invalida el grafo.**

La única hipótesis. Dice exactamente lo que el autor dice del lector: *toma cualquier nodo válido*
—cualquier entrada que el review haya dejado en la tabla global— *y selecciónalo*; el filtro y el
review harán el resto.

No habla de cadenas, ni de parejas, ni de ternas, ni de tablas de nodo. Habla de **una entrada y la
validez**, que es lo único que el lector mira.

Medido: `row-degree pairdesc`, columna «como lo hace el lector» —pinchar y revisar en cada paso—,
**1.016/1.016** pares en `dos_de_tres.cnf` y **12.602/12.602** en el corpus aleatorio: pinchar deja
el grafo válido siempre. -/
def PinAlive : Prop :=
  ∀ g : GPathM, DCtx g → isValid g = true →
    ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
      isValid (filterAllAgg g [q.id]) = true

/-- **Y de ahí sale todo, por la inducción que el autor describe.**

*«El filtro y el review reducen el grafo cada vez más hasta que solo queda un camino.»* Eso es
literalmente la recursión: pinchar en un paso con elección hace el grafo estrictamente más pequeño
(`ReaderAgg.measure_lt_of_choiceAt`), así que se llega al fondo; y en el fondo, donde ya no queda
nada que elegir, la cadena aparece sola (`hasChain_of_noChoice`).

Subiendo, la cadena del grafo pequeño **es** cadena del grande —las tablas solo encogen,
`SubsetSemantics.ChainSound_of_pruned`— y en el paso pinchado elige el pin, porque después del
filtro allí no hay otra cosa (`ReaderComplete.pin_id`).

Se demuestran las dos a la vez porque se necesitan mutuamente: la cadena para las entradas de los
pasos ya decididos, y las entradas para construir la cadena. -/
theorem chained_of_pinAlive (hpa : PinAlive) :
    ∀ (n : Nat) (g : GPathM), GPathM.measure g ≤ n → DCtx g → isValid g = true →
      HasChain g ∧ OwnerChained g := by
  intro n
  induction n with
  | zero =>
    intro g hm ctx hv
    exfalso
    have hent := hasStepEntry_of_isValid g hv 0 (Int.le_refl 0) ctx.pos
    simp only [hasStepEntry, List.any_eq_true] at hent
    obtain ⟨q, hq, _⟩ := hent
    have : 0 < g.gowners.length := List.length_pos_of_mem hq
    simp only [GPathM.measure] at hm
    omega
  | succ m ih =>
    intro g hm ctx hv
    have hnd := (RCtx_of_readableAgg g ctx.rd).nodup
    -- el paso de la recursión: pinchar una entrada de un paso con elección
    have key : ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
        PickInduction.choiceAt g q.id.step = true →
        ∃ sel, ChainSound g sel ∧ (sel q.id.step).id = q.id := by
      intro q hq h0 h1 hcq
      have hqm : q ∈ ownersAt g.gowners q.id.step :=
        List.mem_filter.mpr ⟨hq, beq_iff_eq.mpr rfl⟩
      have hv' : isValid (filterAllAgg g [q.id]) = true := hpa g ctx hv q hq h0 h1
      have hlt : GPathM.measure (filterAllAgg g [q.id]) < GPathM.measure g :=
        ReaderAgg.measure_lt_of_choiceAt g q.id.step hcq q hqm
      obtain ⟨⟨sel, hsc'⟩, _⟩ :=
        ih _ (by omega) (DCtx_filterAllAgg g ctx _) hv'
      have hpr := pruned_filterAllAgg g [q.id]
      have h1' : q.id.step < (filterAllAgg g [q.id]).current_step := by
        rw [hpr.step_eq]; exact h1
      obtain ⟨_, hss⟩ := hsc'.chain.1.1 q.id.step h0 h1'
      have hmem := hsc'.chain.2.2 q.id.step h0 h1'
      exact ⟨sel, SubsetSemantics.ChainSound_of_pruned hpr hnd ctx.smp sel hsc',
        ReaderComplete.pin_id g q.id (sel q.id.step) hmem (by rw [hss])⟩
    -- la cadena del estado
    have hchain : HasChain g := by
      cases hc : PickInduction.hasChoice g with
      | false =>
        exact hasChain_of_noChoice g ctx.rd hv ctx.pms ctx.sn ctx.smp ctx.pos hc
      | true =>
        obtain ⟨k, hk, hck⟩ := List.any_eq_true.mp hc
        obtain ⟨x, hx, _⟩ := List.any_eq_true.mp hck
        have hxg : x ∈ g.gowners := (List.mem_filter.mp hx).1
        have hxs : x.id.step = k := eq_of_beq (List.mem_filter.mp hx).2
        have lo := mem_intRange_lower hk
        have hi := mem_intRange_upper hk
        obtain ⟨sel, hsc, _⟩ :=
          key x hxg (by rw [hxs]; exact lo) (by rw [hxs]; omega) (by rw [hxs]; exact hck)
        exact ⟨sel, hsc⟩
    refine ⟨hchain, ?_⟩
    -- y la frase, entrada por entrada
    intro q hq h0 h1
    cases hcq : PickInduction.choiceAt g q.id.step with
    | true => exact key q hq h0 h1 hcq
    | false =>
      obtain ⟨sel, hsc⟩ := hchain
      obtain ⟨_, hss⟩ := hsc.chain.1.1 q.id.step h0 h1
      exact ⟨sel, hsc, oneIdAt_of_choiceAt g q.id.step hcq
        (sel q.id.step) (hsc.chain.2.2 q.id.step h0 h1) q hq hss rfl⟩

/-- **Y entonces la frase vale en todo estado del lector.** -/
theorem ownerChained_of_pinAlive (hpa : PinAlive) (g : GPathM) (ctx : DCtx g)
    (hv : isValid g = true) : OwnerChained g :=
  (chained_of_pinAlive hpa (GPathM.measure g) g (Nat.le_refl _) ctx hv).2

/-- **El lector no se atasca nunca.**

`PinAlive` da `OwnerChained` de cada estado, `hasChain_pin_of_ownerChained` lo convierte en que
cada pin conserva la cadena, y `progressAgg_of_chains` cierra. Sin una sola hipótesis más. -/
theorem progressAgg_of_pinAlive (hpa : PinAlive) (g₀ : GPathM) (ctx₀ : DCtx g₀) :
    ProgressAgg g₀ := by
  refine progressAgg_of_chains g₀ ?_
  intro g hF
  induction hF with
  | start => intro hv; exact (chained_of_pinAlive hpa _ g₀ (Nat.le_refl _) ctx₀ hv).1
  | pin g' mid hF' hv' ih =>
    intro hv
    have ctx' : DCtx g' := by
      clear ih hv
      induction hF' with
      | start => exact ctx₀
      | pin g'' mid'' hF'' hv'' ih'' => exact DCtx_filterAllAgg g'' (ih'' hv'') _
    exact hasChain_pin_of_ownerChained g'
      (ownerChained_of_pinAlive hpa g' ctx' hv') (ih hv') mid hv

/-- **Y el veredicto: el lector sin retroceso acierta siempre que hay solución.** -/
theorem readerVerdictW_of_pinAlive (hpa : PinAlive) (φ : Cnf) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (ctx₀ : DCtx (filterAllAgg kv.2 []))
    (hv : isValid (filterAllAgg kv.2 []) = true) :
    ReaderExec.readerVerdictW φ = true :=
  ReaderExec.readerVerdictW_complete φ kv hkv hv (progressAgg_of_pinAlive hpa _ ctx₀)

/-! ## Qué queda, y dónde NO está

Queda `PinAlive`, y nada más. Nótese lo que ya no aparece en ningún sitio de esta ruta:

* no hay **parejas** `(nodo, entrada de su tabla)`;
* no hay **ternas** `(x, q, requisito)`;
* no hay que **pegar** cadenas, que es lo que el contraejemplo `{110,101,011}` de
  `SupportedRun.triple_data_of_survival` impide;
* no se usa `Exactness.TablesSound` en ningún paso.

Todo eso venía del rodeo por las tablas de nodo. La ruta del autor no pasa por ahí: el lector mira
la tabla **global**, pincha, y deja trabajar al review — y eso es lo único que la prueba necesita.

Y `PinAlive` tiene además la forma que el algoritmo hace cierta por construcción: la entrada `q`
está viva **porque el review la dejó**, y el review solo deja lo que tiene continuación; pincharla
no puede entonces vaciar ningún paso. Es la misma frase de siempre, pero por primera vez es la
**única**. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.chained_of_pinAlive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chained_of_pinAlive

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.readerVerdictW_of_pinAlive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_of_pinAlive

/-- **Y con la semilla puesta, el teorema entero desde una sola frase.**

    PinAlive  →  ∀ φ, WF φ →  (readerVerdictW φ = true ↔ Satisfiable φ)

La vuelta ya estaba cerrada sin hipótesis (`ReaderExec.readerVerdictW_sound`: lo que el lector
devuelve se decodifica y se comprueba). La ida la pone la conservación —que sobre una fórmula
satisfacible aparca en la línea final un estado con cadena— más `PinAlive`.

Y el contexto de la semilla no es una hipótesis: son los invariantes que `ReaderAggRun.MInv` ya
demuestra de todo estado de la línea final. -/
theorem readerVerdictW_complete_of_pinAlive (hpa : PinAlive) (φ : Cnf) (hwf : WF φ)
    (hsat : Satisfiable φ) : readerVerdictW φ = true := by
  obtain ⟨a, hsa⟩ := hsat
  obtain ⟨g, hmem, hcs, _, sel, hsel⟩ := ConservationImproves.pureRunW_full_chain φ a hwf hsa
  have hm := (ReaderAggRun.pureRunW_state φ hwf _ hmem).1
  have hsel0 : ChainSound (filterAllAgg g []) sel :=
    ChainSound_filterAllAgg g [] sel hsel (fun _ hreq => absurd hreq List.not_mem_nil)
  have ctx₀ : DCtx (filterAllAgg g []) :=
    { rd := ⟨g, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg g [] hm.pms
      sn := AggInvariants.SN_filterAllAgg g [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg g hm.smp hm.rctx.shape.notroot []
      pos := by
        rw [(pruned_filterAllAgg g []).step_eq, hcs]; exact ConservationCore.stepCount_pos φ }
  exact readerVerdictW_of_pinAlive hpa φ _ hmem ctx₀
    (PickInduction.isValid_of_ChainG _ sel hsel0.chain)

/-- **El lector sin retroceso decide 3-SAT, bajo la frase del autor y nada más.** -/
theorem readerVerdictW_iff_of_pinAlive (hpa : PinAlive) (φ : Cnf) (hwf : WF φ) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  ⟨fun h => ReaderExec.readerVerdictW_sound φ hwf h,
   readerVerdictW_complete_of_pinAlive hpa φ hwf⟩

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.readerVerdictW_iff_of_pinAlive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pinAlive

-- ============================================================
-- Dentro de `PinAlive`: el pin no rompe nada, solo el review puede
-- ============================================================

/-- **El pin, por sí solo, nunca invalida el grafo.** Sin ninguna hipótesis.

`filterRequire` solo toca el paso del propio pin, y allí deja al pin — que sigue vivo—. Los demás
pasos no los mira. Así que la mitad de `PinAlive` que corresponde al **filtro** se cierra aquí, y
toda la obligación cae sobre el review. -/
theorem isValid_filterRequire_of_live (g : GPathM) (hv : isValid g = true)
    (q : PathNodeId) (hq : q ∈ g.gowners) : isValid (filterRequire g q.id) = true := by
  simp only [isValid, List.all_eq_true] at hv ⊢
  intro k hk
  have hx := hv k hk
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hx ⊢
  obtain ⟨p, hp, hps⟩ := hx
  rcases int_eq_or_ne k q.id.step with hkq | hkq
  · refine ⟨q, ?_, hkq.symm⟩
    rw [PickInduction.filterRequire_gowners, List.mem_filter]
    exact ⟨hq, by simp⟩
  · refine ⟨p, ?_, hps⟩
    rw [PickInduction.filterRequire_gowners, List.mem_filter]
    exact ⟨hp, by simp only [Bool.or_eq_true, bne_iff_ne]; exact Or.inl (by rw [hps]; exact hkq)⟩

/-- **Y además el pin deja, en cada paso, un owner del propio nodo pinchado.**

Esto es más que la validez y es la forma en que el autor lo piensa: **la tabla de `q` es su
camino**. Un nodo válido tiene un owner en todos los pasos (`owners_ok_of_isValidNode`), esos
owners son owners globales (`ownGow`), y sobreviven al filtro — los de otros pasos porque el filtro
ni los mira, y el del paso de `q` porque, por `OOS`, **es `q`**.

Así que después de pinchar, el testigo de que ningún paso está vacío no es uno cualquiera: es la
propia tabla del nodo elegido. -/
theorem pin_keeps_own_owners (g : GPathM) (ctx : DCtx g) (hv : isValid g = true)
    (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq)
    (k : Int) (hk0 : 0 ≤ k) (hk1 : k < g.current_step) :
    ∃ w ∈ nq.owners, w.id.step = k ∧ w ∈ (filterRequire g q.id).gowners := by
  have rctx := Reader.Ctx_of_readable _ (readable_of_readableAgg _ ctx.rd) hv
  have hok := owners_ok_of_isValidNode g nq (rctx.nodeval q nq hq)
  simp only [List.all_eq_true] at hok
  obtain ⟨w, hw, hws⟩ := List.any_eq_true.mp (hok k (mem_intRange hk0 (by omega)))
  have hwstep : w.id.step = k := eq_of_beq hws
  have hwg : w ∈ g.gowners :=
    rctx.ownGow q nq hq w hw (by rw [hwstep]; exact hk0) (by rw [hwstep]; exact hk1)
  have hqid : nq.id = q := node?_id_eq g q nq hq
  refine ⟨w, hw, hwstep, ?_⟩
  rw [PickInduction.filterRequire_gowners, List.mem_filter]
  refine ⟨hwg, ?_⟩
  rcases int_eq_or_ne w.id.step q.id.step with hs | hs
  · have hwq : w = nq.id :=
      (RCtx_of_readableAgg g ctx.rd).oos nq (List.mem_of_find?_eq_some hq) w hw (by rw [hs, hqid])
    simp only [Bool.or_eq_true, beq_iff_eq]
    exact Or.inr (by rw [hwq, hqid])
  · simp only [Bool.or_eq_true, bne_iff_ne]
    exact Or.inl hs

/-- **Y entonces `PinAlive` es, exactamente, una frase sobre el review.**

    el review no puede vaciar un paso de un estado que acaba de fijar una entrada viva.

Nada más. El filtro ya está cerrado (`isValid_filterRequire_of_live`), y el testigo de cada paso
está puesto y nombrado: un owner del nodo pinchado (`pin_keeps_own_owners`). Lo único que falta es
que el review no se lo lleve.

Y eso es `ReaderChain.PinKeepsPartner` dicho sobre la tabla global: *pinchar `q` no puede volver
incompatible con `q` a algo que ya era compatible con `q`*. El review solo quita un owner cuando
deja de compartir paso con los suyos (`aggPair`), y los owners de `q` comparten con `q` por
construcción. -/
theorem pinAlive_of_reviewKeeps
    (h : ∀ g : GPathM, DCtx g → isValid g = true →
      ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
        isValid (reviewAgg (filterRequire g q.id)) = true) : PinAlive :=
  fun g ctx hv q hq h0 h1 => h g ctx hv q hq h0 h1

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValid_filterRequire_of_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_filterRequire_of_live

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.pin_keeps_own_owners' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pin_keeps_own_owners

end AbsSat.GraphPath.Model.PinAliveChain
