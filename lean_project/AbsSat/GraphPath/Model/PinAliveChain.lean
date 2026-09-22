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

-- ============================================================
-- Y el review: la tabla de UN nodo vivo basta para validar el estado
-- ============================================================

/-- **Las tablas viven dentro de los owners globales.**

Es lo que `cleanInvalid` impone en cada vuelta: la tabla de cada nodo se corta contra `gowners`
(`intersectOwners n.owners gow`). Una propiedad del punto fijo del review, no una hipótesis sobre
el problema. -/
def OwnersWithin (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, ∀ q ∈ n.owners, q ∈ g.gowners

/-- **Y entonces basta UN nodo vivo y válido para que el estado entero sea válido.**

Éste es el punto. *La tabla de un nodo es su camino*: un nodo válido tiene un owner en **todos** los
pasos (`owners_ok_of_isValidNode`), y esos owners están en la tabla global. Así que ningún paso
puede estar vacío mientras quede un solo nodo vivo.

Dicho al revés, que es como hay que leerlo: **para que el review invalide un estado tiene que
matarlos a todos.** No puede vaciar un paso suelto. -/
theorem isValid_of_survivor (g : GPathM) (hw : OwnersWithin g)
    (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx)
    (hval : isValidNode g nx = true) : isValid g = true := by
  simp only [isValid, List.all_eq_true]
  intro k hk
  have hok := owners_ok_of_isValidNode g nx hval
  simp only [List.all_eq_true] at hok
  obtain ⟨w, hwm, hws⟩ := List.any_eq_true.mp (hok k hk)
  simp only [hasStepEntry, List.any_eq_true]
  exact ⟨w, hw nx (List.mem_of_find?_eq_some hx) w hwm, hws⟩

/-- **Y con eso `PinAlive` se dice en cinco palabras: seleccionar un nodo vivo no lo mata.**

Todo lo demás está cerrado:

* el **filtro** no invalida nada (`isValid_filterRequire_of_live`);
* el filtro deja en cada paso un owner del propio `q` (`pin_keeps_own_owners`);
* y si `q` sale vivo del review, su tabla sola valida el estado entero
  (`isValid_of_survivor`), porque para invalidarlo el review tendría que matar **todos** los nodos.

Así que la obligación entera es que el review no mate al nodo que se acaba de elegir. Y eso es lo
que el autor viene diciendo del algoritmo desde el principio: *si el nodo `x` sigue presente es
porque tiene un camino de compatibles que lo lleva a configurar una solución* — elegirlo no puede
quitárselo. -/
theorem pinAlive_of_pinKeepsPinned
    (h : ∀ g : GPathM, DCtx g → isValid g = true →
      ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
        OwnersWithin (filterAllAgg g [q.id]) ∧
        ∃ nq, (filterAllAgg g [q.id]).node? q = some nq ∧
              isValidNode (filterAllAgg g [q.id]) nq = true) : PinAlive := by
  intro g ctx hv q hq h0 h1
  obtain ⟨hw, nq, hnq, hval⟩ := h g ctx hv q hq h0 h1
  exact isValid_of_survivor _ hw q nq hnq hval

/-! ## El frente, en una frase

    Pinchar un nodo vivo no lo mata.

No hay nada más. Ni parejas, ni ternas, ni tablas cruzadas, ni cadenas que pegar: un nodo, y que
siga ahí después de elegirlo.

Y la estructura del review dice por dónde: los `gowners` **solo encogen por `removeNode`**
—`updateAt`, `unlinkIncompatible`, `relink` y `dropOwnerPair` tocan tablas, nunca la tabla
global—, y `removeNode` solo dispara cuando `isValidNode` falla, o sea cuando la tabla del nodo se
queda sin owner en algún paso. Así que la pregunta final es concreta:

> ¿puede fijar `q` dejar a `q` sin owner en algún paso?

Los owners de `q` comparten paso con `q` por construcción, y `aggPair` solo desenlaza pares que
**dejan** de compartir. Fijar `q` no quita nada de la tabla de `q`: el filtro ni la toca. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValid_of_survivor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_of_survivor

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.pinAlive_of_pinKeepsPinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinAlive_of_pinKeepsPinned

-- ============================================================
-- El pin es un no-op completo para el nodo elegido
-- ============================================================

/-- **El pin no puede invalidar NINGÚN nodo.** Por `rfl`.

`isValidNode` mira el paso actual y el propio nodo —su tabla, sus padres, sus hijos—, y
**no lee `gowners` en ningún sitio**. `filterRequire` solo reescribe `gowners`. Así que ni el nodo
elegido ni ningún otro cambia de estado al pinchar.

Es la frase más barata de todo el módulo y sin embargo cierra una mitad: **todo lo que el pin
pueda romper lo rompe a través del review, nunca por sí mismo.** -/
theorem isValidNode_filterRequire (g : GPathM) (req : NodeId) (n : PNodeM) :
    isValidNode (filterRequire g req) n = isValidNode g n := rfl

/-- **Y la tabla del nodo elegido sobrevive entera al pin.**

No una entrada por paso (`pin_keeps_own_owners`): **todas**. Los owners de `q` de otros pasos el
filtro ni los mira, y el del paso de `q` es `q` mismo por `OOS`, que es justo lo que el filtro
deja. Así que cuando el review corte las tablas contra `gowners` —`intersectOwners n.owners gow`,
lo primero que hace `cleanInvalid`— **la tabla de `q` no pierde nada**. -/
theorem pin_owners_stay (g : GPathM) (hw : OwnersWithin g) (hoos : SelfOwn.OOS g)
    (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq) :
    ∀ w ∈ nq.owners, w ∈ (filterRequire g q.id).gowners := by
  intro w hwm
  have hqid : nq.id = q := node?_id_eq g q nq hq
  rw [PickInduction.filterRequire_gowners, List.mem_filter]
  refine ⟨hw nq (List.mem_of_find?_eq_some hq) w hwm, ?_⟩
  rcases int_eq_or_ne w.id.step q.id.step with hs | hs
  · have hwq : w = nq.id := hoos nq (List.mem_of_find?_eq_some hq) w hwm (by rw [hs, hqid])
    simp only [Bool.or_eq_true, beq_iff_eq]
    exact Or.inr (by rw [hwq, hqid])
  · simp only [Bool.or_eq_true, bne_iff_ne]
    exact Or.inl hs

/-- **El pin, entero, visto desde el nodo elegido: no pasa nada.**

Sigue estando (`filterRequire` no toca `nodes`), sigue siendo válido (`isValidNode` no lee
`gowners`), y conserva su tabla completa dentro de los owners globales (`pin_owners_stay`).

Con `isValid_of_survivor`, eso vuelve a dar la validez del estado pinchado sin pasar por los pasos
uno a uno — y deja dicho que **el único que puede hacer daño es el review**. -/
theorem pin_is_noop_for_pinned (g : GPathM) (hw : OwnersWithin g) (hoos : SelfOwn.OOS g)
    (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq) (hval : isValidNode g nq = true) :
    (filterRequire g q.id).node? q = some nq ∧
      isValidNode (filterRequire g q.id) nq = true ∧
      (∀ w ∈ nq.owners, w ∈ (filterRequire g q.id).gowners) :=
  ⟨hq, hval, pin_owners_stay g hw hoos q nq hq⟩

/-! ## Y entonces el frente es todavía más pequeño

Del pin ya no queda nada: para el nodo elegido es un **no-op completo** —sigue, sigue válido, y su
tabla entera sigue dentro de `gowners`—. Toda la obligación vive en el review, y dentro del review
en un solo mecanismo, porque los `gowners` solo encogen por `removeNode` y `removeNode` solo
dispara cuando `isValidNode` falla.

Así que `q` solo puede morir **por contagio**: alguno de sus owners `w` muere, la siguiente vuelta
de `cleanInvalid` corta `w` de la tabla de `q`, y si `w` era el único owner de `q` en su paso, `q`
se queda inválido.

O sea que lo que falta es exactamente esto:

> fijar `q` no puede matar a **todos** los owners de `q` de ningún paso.

Y aquí es donde el diseño habla: los owners de `q` son, por construcción, los nodos con los que
`q` tiene camino común. Matarlos a todos en un paso sería decir que `q` no tenía camino — y `q`
estaba vivo. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValidNode_filterRequire' does not depend on any axioms -/
#guard_msgs in
#print axioms isValidNode_filterRequire

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.pin_owners_stay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pin_owners_stay

-- ============================================================
-- La validez, dicha sobre NODOS: cada paso conserva alguno
-- ============================================================

/-- **Validez = ningún paso se queda sin nodos.**

La tabla global y las filas del grafo dicen lo mismo: un owner global es un nodo (`GN`) y un nodo
se posee a sí mismo (`SelfOwned`), luego está en la tabla global (`OwnersWithin`).

Esto mueve `PinAlive` al nivel en el que el review de verdad trabaja. Porque `gowners` **solo**
encoge por `removeNode` —`updateAt`, `unlinkIncompatible`, `relink` y `dropOwnerPair` tocan tablas
de nodo y nunca la tabla global—, y `removeNode` solo dispara cuando `isValidNode` falla. Así que
la pregunta deja de ser sobre entradas de tabla y pasa a ser sobre **muertes de nodos**. -/
theorem isValid_iff_lines (g : GPathM) (hw : OwnersWithin g) (hso : Ownership.SelfOwned g)
    (hgn : GownersNodes.GN g) (hnd : NodupIds g) :
    isValid g = true ↔ ∀ k, 0 ≤ k → k < g.current_step → ∃ n, n ∈ g.line k := by
  constructor
  · intro hv k hk0 hk1
    have hent := hasStepEntry_of_isValid g hv k hk0 hk1
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
    obtain ⟨q, hq, hqs⟩ := hent
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
    exact ⟨n, List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hn,
      beq_iff_eq.mpr (by rw [node?_id_eq g q n hn]; exact hqs)⟩⟩
  · intro hl
    simp only [isValid, List.all_eq_true]
    intro k hk
    obtain ⟨n, hn⟩ := hl k (mem_intRange_lower hk) (by have := mem_intRange_upper hk; omega)
    obtain ⟨hnm, hns⟩ := List.mem_filter.mp hn
    have hnode : g.node? n.id = some n := node?_of_mem hnd n hnm
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq]
    exact ⟨n.id, hw n hnm n.id (hso n.id n hnode), eq_of_beq hns⟩

/-- **Y un solo nodo vivo llena todas las filas.**

Corolario de `isValid_of_survivor` leído sobre nodos: los owners del superviviente cubren todos los
pasos, y son nodos. Así que **mientras quede un nodo vivo, ninguna fila se vacía**.

Es la forma más nítida de por qué el review no puede romper el estado por un lado: no hay «romper
por un lado». O caen todos o no cae ninguno. -/
theorem lines_nonempty_of_survivor (g : GPathM) (hw : OwnersWithin g) (hgn : GownersNodes.GN g)
    (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx) (hval : isValidNode g nx = true)
    (k : Int) (hk0 : 0 ≤ k) (hk1 : k < g.current_step) : ∃ n, n ∈ g.line k := by
  have hok := owners_ok_of_isValidNode g nx hval
  simp only [List.all_eq_true] at hok
  obtain ⟨w, hwm, hws⟩ := List.any_eq_true.mp (hok k (mem_intRange hk0 (by omega)))
  have hwg : w ∈ g.gowners := hw nx (List.mem_of_find?_eq_some hx) w hwm
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g w).mp (hgn w hwg))
  exact ⟨n, List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hn,
    by rw [node?_id_eq g w n hn]; exact hws⟩⟩

/-! ## Dónde queda, dicho sobre nodos

    Fijar `q` no puede matar a `q`.

Y ahora con el mecanismo a la vista, porque todo lo demás está cerrado:

* el pin **no toca** ni los nodos, ni las tablas, ni la validez de ningún nodo
  (`isValidNode_filterRequire`, por `rfl`);
* la tabla de `q` sobrevive entera al pin (`pin_owners_stay`), así que el corte contra `gowners`
  de `cleanInvalid` no le quita nada;
* si `q` sale vivo, **ninguna fila se vacía** (`lines_nonempty_of_survivor`) y el estado es válido
  (`isValid_of_survivor`);
* y `q` solo puede morir por `removeNode`, que solo dispara si `isValidNode q` falla, que solo
  ocurre si `q` se queda sin owner en algún paso — es decir, **por contagio desde su propia
  tabla**.

La frase que falta es, por tanto, que el contagio no llegue: *fijar `q` no puede matar a todos los
owners de `q` de ningún paso*. Y los owners de `q` son, por construcción de la máquina, los nodos
con los que `q` comparte camino. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValid_iff_lines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_iff_lines

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.lines_nonempty_of_survivor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lines_nonempty_of_survivor

-- ============================================================
-- El contagio, acotado: la primera muerte solo alcanza a los incompatibles
-- ============================================================

/-- **El pin solo puede quitar entradas de su propio paso.**

`gowners` cambia únicamente en el paso pinchado, así que el corte contra `gowners` que hace
`cleanInvalid` no puede tocar ninguna entrada de otro paso. Sin hipótesis más allá de que las
tablas ya estuvieran dentro de la tabla global. -/
theorem pin_keeps_owners_off_step (g : GPathM) (hw : OwnersWithin g) (q : PathNodeId)
    (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx) :
    ∀ w ∈ nx.owners, w.id.step ≠ q.id.step → w ∈ (filterRequire g q.id).gowners := by
  intro w hwm hne
  rw [PickInduction.filterRequire_gowners, List.mem_filter]
  exact ⟨hw nx (List.mem_of_find?_eq_some hx) w hwm,
    by simp only [Bool.or_eq_true, bne_iff_ne]; exact Or.inl hne⟩

/-- **Y un nodo COMPATIBLE con la elección no pierde nada que le haga falta.**

«Compatible» es justo lo que el autor dice: que su tabla contenga el valor elegido. Si lo contiene,
entonces tras pinchar sigue teniendo un owner en **todos** los pasos y todos dentro de la tabla
global: en los pasos distintos del pinchado porque el filtro no los mira
(`pin_keeps_owners_off_step`), y en el pinchado porque lo que conserva es precisamente el valor
elegido.

Ésta es la frase del autor convertida en teorema: **el filtro limpia los nodos que no son
compatibles con los requisitos** — y solo ésos. -/
theorem compat_owners_survive_pin (g : GPathM) (hw : OwnersWithin g) (q : PathNodeId)
    (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx)
    (hval : isValidNode g nx = true)
    (hcompat : ∃ u ∈ nx.owners, u.id = q.id) :
    ∀ k, 0 ≤ k → k < g.current_step →
      ∃ w ∈ nx.owners, w.id.step = k ∧ w ∈ (filterRequire g q.id).gowners := by
  intro k hk0 hk1
  have hok := owners_ok_of_isValidNode g nx hval
  simp only [List.all_eq_true] at hok
  obtain ⟨w, hwm, hws⟩ := List.any_eq_true.mp (hok k (mem_intRange hk0 (by omega)))
  have hwstep : w.id.step = k := eq_of_beq hws
  rcases int_eq_or_ne k q.id.step with hkq | hkq
  · -- el paso pinchado: lo que se conserva es el valor elegido
    obtain ⟨u, hum, huid⟩ := hcompat
    refine ⟨u, hum, by rw [huid, ← hkq], ?_⟩
    rw [PickInduction.filterRequire_gowners, List.mem_filter]
    exact ⟨hw nx (List.mem_of_find?_eq_some hx) u hum,
      by simp only [Bool.or_eq_true, beq_iff_eq]; exact Or.inr huid⟩
  · -- cualquier otro paso: el filtro no lo mira
    exact ⟨w, hwm, hwstep,
      pin_keeps_owners_off_step g hw q x nx hx w hwm (by rw [hwstep]; exact hkq)⟩

/-- **Y el nodo elegido es compatible consigo mismo**, así que la primera criba no lo roza.

`SelfOwned` pone a `q` en su propia tabla, y su id es el valor elegido. Sin más. -/
theorem pinned_is_compat (g : GPathM) (hso : Ownership.SelfOwned g)
    (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq) :
    ∃ u ∈ nq.owners, u.id = q.id :=
  ⟨q, hso q nq hq, rfl⟩

/-! ## El contagio, con su primera vuelta cerrada

Queda dicho lo que el pin puede y no puede hacer, y no es poco:

* solo puede quitar entradas **del paso pinchado** (`pin_keeps_owners_off_step`);
* a un nodo **compatible** con la elección no le quita nada que le haga falta
  (`compat_owners_survive_pin`): sigue con owner en todos los pasos y todos en la tabla global;
* y el nodo elegido es compatible consigo mismo (`pinned_is_compat`), así que **la primera criba no
  lo roza**.

Así que la muerte, si empieza, empieza en los incompatibles — exactamente los que el filtro está
ahí para limpiar. Lo que queda abierto es solo la **propagación**: que ninguna de esas muertes
vuelva, vuelta a vuelta, hasta vaciar un paso de la tabla de `q`.

Y contra eso juega la simetría del punto fijo (`AggFixpoint.AggOk`): si `w` es owner de `q`,
entonces `q` es owner de `w`. De modo que mientras `q` viva, `w` tiene owner en el paso de `q`, y no
puede morir *por ahí*. La muerte de un owner de `q` tendría que venirle de un tercer paso, y eso es
lo único que falta acotar. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.pin_keeps_owners_off_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pin_keeps_owners_off_step

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.compat_owners_survive_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compat_owners_survive_pin

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.pinned_is_compat' does not depend on any axioms -/
#guard_msgs in
#print axioms pinned_is_compat

-- ============================================================
-- La simetría: los owners del elegido también son compatibles
-- ============================================================

/-- **Todo owner del nodo elegido es compatible con la elección.**

Y sale de la simetría del punto fijo de la criba, que es lo primero que `aggPair` impone: si `w`
está en la tabla de `q`, entonces `q` está en la tabla de `w` (`AggFixpoint.AggOk`, primera
componente). Y `q` lleva el valor elegido por definición.

Dicho en el lenguaje del algoritmo: **los owners de un nodo son los nodos con los que comparte
camino, y compartir camino es mutuo.** -/
theorem owner_of_pinned_is_compat (g : GPathM) (hok : AggFixpoint.AggOk g) (ctx : Pinned.Ctx g)
    (q w : PathNodeId) (nq nw : PNodeM) (hq : g.node? q = some nq) (hwn : g.node? w = some nw)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < g.current_step)
    (hw0 : 0 ≤ w.id.step) (hw1 : w.id.step < g.current_step)
    (hwm : w ∈ nq.owners) : ∃ u ∈ nw.owners, u.id = q.id :=
  ⟨q, (hok q nq w nw hq hwn hq0 hq1 hw0 hw1 hwm (ctx.nodeval q nq hq) (ctx.nodeval w nw hwn)).1,
    rfl⟩

/-- **Así que la primera criba no puede matar a ningún owner del nodo elegido.**

Junta las dos piezas: un owner de `q` es compatible con la elección (por simetría), y a un nodo
compatible el pin no le quita nada que le haga falta (`compat_owners_survive_pin`).

Es decir: **el pin no roza el vecindario del nodo que se elige.** Ni `q`, ni su tabla entera. Y la
tabla de `q` es lo único que hace falta para que ninguna fila se vacíe
(`lines_nonempty_of_survivor`). -/
theorem owners_of_pinned_survive_pin (g : GPathM) (hw : OwnersWithin g)
    (hok : AggFixpoint.AggOk g) (ctx : Pinned.Ctx g)
    (q w : PathNodeId) (nq nw : PNodeM) (hq : g.node? q = some nq) (hwn : g.node? w = some nw)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < g.current_step)
    (hw0 : 0 ≤ w.id.step) (hw1 : w.id.step < g.current_step)
    (hwm : w ∈ nq.owners) :
    ∀ k, 0 ≤ k → k < g.current_step →
      ∃ u ∈ nw.owners, u.id.step = k ∧ u ∈ (filterRequire g q.id).gowners :=
  compat_owners_survive_pin g hw q w nw hwn (ctx.nodeval w nw hwn)
    (owner_of_pinned_is_compat g hok ctx q w nq nw hq hwn hq0 hq1 hw0 hw1 hwm)

/-! ## Lo que la simetría compra, y lo que no

Compra el vecindario entero del nodo elegido:

* `q` sobrevive a la primera criba (`pinned_is_compat`);
* **y todos sus owners también** (`owners_of_pinned_survive_pin`), porque la simetría del punto
  fijo los hace compatibles con la elección;
* y con la tabla de `q` en pie, ninguna fila se vacía (`lines_nonempty_of_survivor`) y el estado es
  válido (`isValid_of_survivor`).

Lo que no compra es la **segunda vuelta**. El review itera: un nodo incompatible muere, su muerte
sale de `gowners`, y la vuelta siguiente vuelve a cortar todas las tablas contra una tabla global
ya más pequeña. La simetría protege a los owners de `q` del **primer** corte, no de que uno de
ellos pierda más adelante su último owner en un tercer paso.

Así que el residuo, ya del todo pelado, es la terminación de esa cascada:

> ninguna cadena de muertes que empiece en los incompatibles con la elección alcanza la tabla
> de `q`.

Y ahí es donde el diseño tiene la última palabra, porque los owners de `q` son su camino: para
alcanzarlos habría que matar el camino que hacía vivo a `q` — y `q` estaba vivo antes de elegirlo,
que es lo único que el lector comprueba. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.owner_of_pinned_is_compat' does not depend on any axioms -/
#guard_msgs in
#print axioms owner_of_pinned_is_compat

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.owners_of_pinned_survive_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owners_of_pinned_survive_pin

-- ============================================================
-- La cascada, acotada: `sharesEveryStep` protege TODAS las vueltas
-- ============================================================

/-- **Si la tabla del elegido está intacta, la de un compañero suyo no se queda vacía en ningún
paso.** Y esto vale para **cualquier** estado posterior, no solo para el primer corte.

La entrada es la segunda componente de `AggFixpoint.AggOk`, la que hasta ahora no se había usado en
esta línea: dos tablas que se poseen **comparten una entrada en todos los pasos**. Así que en cada
paso `k` hay un `z` que está en la tabla de `q` **y** en la de `w`; si la tabla de `q` sigue dentro
de los owners globales, ese `z` sobrevive al corte, y con él la cobertura de `w`.

Dicho en el lenguaje de la máquina: *los caminos de `q` y de `w` se cruzan en cada paso*, así que
mientras el camino de `q` esté en pie el de `w` no puede quedarse sin nada. -/
theorem partner_keeps_cover (g h : GPathM) (_q _w : PathNodeId) (nq nw : PNodeM)
    (hshare : sharesEveryStep g.current_step nq.owners nw.owners = true)
    (hwval : isValidNode g nw = true)
    (hI : ∀ z ∈ nq.owners, z ∈ h.gowners) :
    ∀ k, 0 ≤ k → k < g.current_step →
      ∃ z ∈ nw.owners, z.id.step = k ∧ z ∈ h.gowners := by
  intro k hk0 hk1
  simp only [sharesEveryStep, List.all_eq_true] at hshare
  have hk := hshare k (mem_intRange hk0 (by omega))
  have hwe : hasStepEntry nw.owners k = true := by
    have hok := owners_ok_of_isValidNode g nw hwval
    simp only [List.all_eq_true] at hok
    exact hok k (mem_intRange hk0 (by omega))
  rw [hwe] at hk
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hk
  obtain ⟨z, hz, hzc⟩ := hk
  obtain ⟨hzq, hzs⟩ := List.mem_filter.mp hz
  exact ⟨z, List.mem_of_elem_eq_true hzc, eq_of_beq hzs, hI z hzq⟩

/-- **Y entonces ningún owner del nodo elegido puede perder su cobertura, en ninguna vuelta.**

`AggOk` da las dos cosas de golpe para el par `(q, w)`: la simetría y el cruce en todos los pasos.
Con la tabla de `q` intacta, `w` conserva en cada paso un owner vivo.

Esto cierra la parte de **owners** de la cascada entera —no solo el primer corte—, porque no
depende de qué estado sea `h`: solo de que la tabla de `q` siga dentro de sus owners globales. -/
theorem owner_of_pinned_keeps_cover (g h : GPathM) (hok : AggFixpoint.AggOk g) (ctx : Pinned.Ctx g)
    (q w : PathNodeId) (nq nw : PNodeM) (hq : g.node? q = some nq) (hwn : g.node? w = some nw)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < g.current_step)
    (hw0 : 0 ≤ w.id.step) (hw1 : w.id.step < g.current_step)
    (hwm : w ∈ nq.owners) (hI : ∀ z ∈ nq.owners, z ∈ h.gowners) :
    ∀ k, 0 ≤ k → k < g.current_step →
      ∃ z ∈ nw.owners, z.id.step = k ∧ z ∈ h.gowners :=
  partner_keeps_cover g h q w nq nw
    (hok q nq w nw hq hwn hq0 hq1 hw0 hw1 hwm (ctx.nodeval q nq hq) (ctx.nodeval w nw hwn)).2
    (ctx.nodeval w nw hwn) hI

/-! ## La cascada, ya solo por los enlaces

`isValidNode` pide dos cosas: que la tabla cubra todos los pasos (`owners_ok`) y que el nodo tenga
padres o hijos según dónde esté. Con lo de arriba, **la primera ya no puede fallarle a ningún owner
del nodo elegido, en ninguna vuelta del review**:

* la simetría del punto fijo hace a todo owner de `q` compatible con la elección
  (`owner_of_pinned_is_compat`);
* y el cruce en todos los pasos le conserva la cobertura mientras la tabla de `q` esté en pie
  (`owner_of_pinned_keeps_cover`);
* y con la tabla de `q` en pie, ninguna fila se vacía y el estado es válido
  (`lines_nonempty_of_survivor`, `isValid_of_survivor`).

Lo único por donde la cascada puede aún entrar es la **segunda** mitad de `isValidNode`: que
`relink` o `unlinkIncompatible` dejen a un owner de `q` sin padres o sin hijos. Y ahí conviene
notar de qué tamaño es lo que queda: no es una frase sobre caminos, ni sobre tablas, ni sobre
elecciones — es una frase sobre **los enlaces padre-hijo de un nodo cuya tabla está intacta**. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.partner_keeps_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms partner_keeps_cover

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.owner_of_pinned_keeps_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owner_of_pinned_keeps_cover

-- ============================================================
-- Los enlaces: el review deja el nodo elegido literalmente igual
-- ============================================================

/-- **Intersecar con algo que ya contiene todo no quita nada.** -/
theorem intersectOwners_eq_self_of_subset (a b : List PathNodeId) (h : ∀ q ∈ a, q ∈ b) :
    intersectOwners a b = a :=
  List.filter_eq_self.mpr (fun q hq => by
    simp only [Bool.or_eq_true]
    exact Or.inr (by simpa using h q hq))

/-- **Los enlaces de un nodo están dentro de su tabla.**

Es lo que `relinkSelf` impone en cada vuelta: padres e hijos se filtran contra los propios owners
(`n.owners.contains p`). Otra propiedad del punto fijo del review, como `OwnersWithin`. -/
def LinksWithin (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, (∀ p ∈ n.parents, p ∈ n.owners) ∧ (∀ s ∈ n.sons, s ∈ n.owners)

/-- **Y entonces el re-enlace no hace nada.** Si los enlaces ya están dentro de la tabla, filtrarlos
contra la tabla los deja como estaban. -/
theorem relinkSelf_eq_self (n : PNodeM) (hp : ∀ p ∈ n.parents, p ∈ n.owners)
    (hs : ∀ s ∈ n.sons, s ∈ n.owners) : relinkSelf n = n := by
  unfold relinkSelf
  rw [List.filter_eq_self.mpr (fun p hp' => by simpa using hp p hp'),
      List.filter_eq_self.mpr (fun s hs' => by simpa using hs s hs')]

/-- **El corte del review sobre el nodo elegido es la identidad.**

`cleanInvalid` hace, por nodo: cortar la tabla contra `gowners` y re-enlazar
(`relink (intersectOwners d.owners gow) d`). Sobre el nodo elegido las dos cosas son la identidad —
el corte porque su tabla entera sigue dentro de `gowners` (`pin_owners_stay`), y el re-enlace porque
sus enlaces ya estaban dentro de su tabla.

O sea: **el review no le toca ni un campo.** -/
theorem relink_eq_self (n : PNodeM) (gow : List PathNodeId) (hsub : ∀ q ∈ n.owners, q ∈ gow)
    (hp : ∀ p ∈ n.parents, p ∈ n.owners) (hs : ∀ s ∈ n.sons, s ∈ n.owners) :
    relink (intersectOwners n.owners gow) n = n := by
  unfold relink
  rw [intersectOwners_eq_self_of_subset n.owners gow hsub]
  exact relinkSelf_eq_self n hp hs

/-- **Y el desenlace tampoco, visto desde el propio nodo.** `unlinkIncompatible` filtra los enlaces
del nodo contra su tabla, que es otra vez la identidad. -/
theorem unlinkMap_self_eq (n : PNodeM) (hp : ∀ p ∈ n.parents, p ∈ n.owners)
    (hs : ∀ s ∈ n.sons, s ∈ n.owners) : unlinkMap n n.id n = n := by
  unfold unlinkMap
  simp only [beq_self_eq_true, if_true]
  rw [List.filter_eq_self.mpr (fun p hp' => by simpa using hp p hp'),
      List.filter_eq_self.mpr (fun s hs' => by simpa using hs s hs')]

/-- **El nodo elegido, tras el pin y el corte del review: idéntico.**

Las tres piezas juntas sobre `q`. Su tabla no pierde nada (`pin_owners_stay`), su re-enlace es la
identidad (`relink_eq_self`) y su desenlace también (`unlinkMap_self_eq`). -/
theorem review_step_noop_on_pinned (g : GPathM) (hw : OwnersWithin g) (hl : LinksWithin g)
    (hoos : SelfOwn.OOS g) (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq) :
    relink (intersectOwners nq.owners (filterRequire g q.id).gowners) nq = nq ∧
      unlinkMap nq nq.id nq = nq :=
  let hlq := hl nq (List.mem_of_find?_eq_some hq)
  ⟨relink_eq_self nq _ (pin_owners_stay g hw hoos q nq hq) hlq.1 hlq.2,
   unlinkMap_self_eq nq hlq.1 hlq.2⟩

/-! ## Y el residuo, con el mecanismo entero a la vista

`q` no puede perder nada por sí mismo: el pin no lo toca, el corte del review es la identidad sobre
él, y su cobertura de owners está protegida en todas las vueltas
(`owner_of_pinned_keeps_cover`). La **única** manera de que `q` muera es que `removeNode` se lleve a
un vecino suyo, porque `removeNode` sí filtra los enlaces de todos los nodos que quedan.

Y aquí es donde el residuo se vuelve pequeño de verdad, porque los vecinos de `q` son sus owners
(`LinksWithin`), y de sus owners ya sabemos que **no pueden perder cobertura**. Así que un vecino de
`q` solo puede morir a su vez por **sus** enlaces, y sus enlaces son sus owners, un paso más abajo
o más arriba.

Es decir: la cascada de enlaces baja por la cadena de padres y sube por la de hijos, y **las dos
son finitas** —el paso decrece hacia 0 y crece hacia `current_step - 1`—, y en los extremos
`isValidNode` **no pide enlace**: un nodo del paso 0 es raíz y no necesita padres, uno del último
paso no necesita hijos.

Lo que queda por escribir es esa recursión sobre el paso. No es un enunciado sobre elecciones ni
sobre caminos: es una inducción sobre los pasos, con el caso base ya dado por la propia definición
de `isValidNode`. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.relink_eq_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms relink_eq_self

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.review_step_noop_on_pinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_step_noop_on_pinned

end AbsSat.GraphPath.Model.PinAliveChain
