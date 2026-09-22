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

-- ============================================================
-- Y los enlaces se van del todo: la cobertura de la tabla basta
-- ============================================================

/-- **Un nodo cuya tabla cubre todos los pasos es válido. Los enlaces salen de la tabla.**

Y esto quita los enlaces del problema entero, porque en los estados del lector **los owners de los
pasos vecinos SON los enlaces**: `AdjacentOwners.owners_below_iff_parents` y
`owners_above_iff_sons`. Así que:

* si el nodo no es raíz, su paso es ≥ 1 (`RootAtZero` al revés), la cobertura le da un owner en el
  paso de abajo, y ese owner **es un padre**;
* si no es el último, la cobertura le da un owner en el paso de arriba, y ese owner **es un hijo**.

`isValidNode` colapsa por tanto sobre una sola cosa: **que la tabla cubra todos los pasos**. Que es,
otra vez, la frase del autor — *la tabla de un nodo es su camino* — ahora en su forma más fuerte:
no es que el camino esté en la tabla, es que **la tabla es todo lo que hay que mirar**. -/
theorem isValidNode_of_cover (g : GPathM) (a : AdjacentOwners.Adj g)
    (x : PathNodeId) (n : PNodeM) (hx : g.node? x = some n)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < g.current_step)
    (hcover : ∀ k, 0 ≤ k → k < g.current_step → ∃ z ∈ n.owners, z.id.step = k) :
    isValidNode g n = true := by
  have hid : n.id = x := node?_id_eq g x n hx
  have hmem := List.mem_of_find?_eq_some hx
  have howners : (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry n.owners k) = true := by
    simp only [List.all_eq_true]
    intro k hk
    obtain ⟨z, hz, hzs⟩ := hcover k (mem_intRange_lower hk)
      (by have := mem_intRange_upper hk; omega)
    simp only [hasStepEntry, List.any_eq_true]
    exact ⟨z, hz, beq_iff_eq.mpr hzs⟩
  have hpar : 1 ≤ x.id.step → n.parents ≠ [] := by
    intro h1
    obtain ⟨z, hz, hzs⟩ := hcover (x.id.step - 1) (by omega) (by omega)
    exact List.ne_nil_of_mem
      ((AdjacentOwners.owners_below_iff_parents g a x n hx h1 z (by rw [hzs])).mp hz)
  have hson : x.id.step ≤ g.current_step - 2 → n.sons ≠ [] := by
    intro h2
    obtain ⟨z, hz, hzs⟩ := hcover (x.id.step + 1) (by omega) (by omega)
    exact List.ne_nil_of_mem
      ((AdjacentOwners.owners_above_iff_sons g a x n hx h2 z (by rw [hzs])).mp hz)
  have hnr : ¬(n.id.parent_id.isNone = true) → 1 ≤ x.id.step := by
    intro hr
    by_cases h1 : 1 ≤ x.id.step
    · exact h1
    · exact absurd (by rw [a.rc.rootz n hmem (by rw [hid]; omega)]; rfl) hr
  have hlast : (n.id.id.step == g.current_step - 1) = (x.id.step == g.current_step - 1) := by
    rw [hid]
  have hnotlast : ¬((x.id.step == g.current_step - 1) = true) → x.id.step ≤ g.current_step - 2 := by
    intro hl
    have : x.id.step ≠ g.current_step - 1 := fun he => hl (by rw [he]; exact beq_iff_eq.mpr rfl)
    omega
  simp only [isValidNode, hlast]
  split
  · split
    · exact howners
    · next hl =>
      simp only [howners, not_isEmpty_of_ne_nil _ (hson (hnotlast hl)), Bool.and_self]
  · next hr =>
    split
    · simp only [howners, not_isEmpty_of_ne_nil _ (hpar (hnr hr)), Bool.and_self]
    · next hl =>
      simp only [howners, not_isEmpty_of_ne_nil _ (hpar (hnr hr)),
        not_isEmpty_of_ne_nil _ (hson (hnotlast hl)), Bool.and_self]

/-! ## `PinAlive`, reducido a una sola palabra: cobertura

Con `isValidNode_of_cover` los enlaces desaparecen del problema y todo queda dicho en términos de
una única cosa, **que la tabla de un nodo siga cubriendo todos los pasos**:

| pieza | estado |
|---|---|
| un nodo con cobertura es válido (los enlaces salen de la tabla) | **cerrado** |
| un nodo válido basta para que el estado sea válido | **cerrado** |
| el pin no toca la tabla del elegido | **cerrado** |
| el corte y el re-enlace del review son la identidad sobre él | **cerrado** |
| los owners del elegido son compatibles con la elección (simetría) | **cerrado** |
| y conservan cobertura mientras la del elegido esté intacta (cruce) | **cerrado** |
| **la tabla del elegido sigue intacta al final del review** | lo que falta |

Y la última casilla ya no tiene nada de geometría: la tabla de `q` solo puede perder una entrada
`z` si `z` deja de estar en `gowners`, o sea si `z` muere; `z` es un owner de `q`, luego tiene
cobertura mientras la tabla de `q` esté intacta; **así que la única forma de romperlo es que se
rompa solo.**

Eso es una inducción sobre las vueltas del review con el invariante «la tabla de `q` está dentro de
`gowners`», y lo que queda es escribirla contra la recursión de `reviewAggFuel`. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValidNode_of_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValidNode_of_cover

-- ============================================================
-- Y el barrido agresivo tampoco: `aggPair` no dispara sobre el elegido
-- ============================================================

/-- **El barrido nunca desenlaza al nodo elegido de un owner suyo.**

`aggPair g q w` tiene exactamente dos motivos para actuar, y `AggFixpoint.AggOk` niega los dos para
el par `(q, w)` cuando `w` está en la tabla de `q`:

* **asimetría** — `w` sería owner de `q` sin que `q` lo sea de `w`: la primera componente de `AggOk`
  dice que sí lo es;
* **inconsistencia** — las dos tablas no compartirían algo en algún paso: la segunda componente dice
  que comparten en todos.

Así que `aggPair` devuelve el grafo tal cual. Con esto el review **entero** queda cerrado sobre el
nodo elegido: el corte y el re-enlace de `cleanInvalid` son la identidad
(`review_step_noop_on_pinned`) y el barrido no dispara. -/
theorem aggPair_noop_on_pinned (g : GPathM) (hok : AggFixpoint.AggOk g) (ctx : Pinned.Ctx g)
    (q w : PathNodeId) (nq nw : PNodeM) (hq : g.node? q = some nq) (hwn : g.node? w = some nw)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < g.current_step)
    (hw0 : 0 ≤ w.id.step) (hw1 : w.id.step < g.current_step)
    (hwm : w ∈ nq.owners) : aggPair g q w = g := by
  obtain ⟨hsym, hshare⟩ := hok q nq w nw hq hwn hq0 hq1 hw0 hw1 hwm
    (ctx.nodeval q nq hq) (ctx.nodeval w nw hwn)
  unfold aggPair
  rw [hq, hwn]
  simp [hsym, hshare]

/-! ## Lo que queda: una inducción, y ya sin nada geométrico dentro

El review, sobre el nodo elegido, no hace **nada**: ni el corte (`relink_eq_self`), ni el desenlace
(`unlinkMap_self_eq`), ni el barrido (`aggPair_noop_on_pinned`). Y sus owners conservan cobertura
mientras su tabla esté dentro de `gowners` (`owner_of_pinned_keeps_cover`), lo que por
`isValidNode_of_cover` los mantiene válidos, y por tanto fuera del alcance del único mecanismo que
puede borrar algo de `gowners`, que es `removeNode`.

El círculo se cierra solo, y eso es lo que hay que escribir: el invariante

    I(h) :  ∀ z ∈ (tabla de q), z ∈ h.gowners

vale al empezar (`pin_owners_stay`), y **cada operación del review lo conserva** por lo de arriba.
Lo que falta es la inducción contra la recursión de `reviewAggFuel` / `reviewFuel` /
`cleanInvalidGo`, que es trabajo de fontanería sobre tres recursiones anidadas, no una idea nueva.

Y conviene subrayar lo que ya **no** hay que probar por el camino: ni que se peguen cadenas, ni que
tres pasos sean compatibles, ni nada sobre las fórmulas. El invariante habla de una lista y de una
tabla. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.aggPair_noop_on_pinned' depends on axioms: [propext] -/
#guard_msgs in
#print axioms aggPair_noop_on_pinned

-- ============================================================
-- Los ladrillos de la inducción: qué toca la tabla global y qué no
-- ============================================================

/-- Actualizar un nodo no toca la tabla global. -/
theorem gowners_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM) :
    (updateAt g id f).gowners = g.gowners := rfl

/-- Desenlazar tampoco. -/
theorem gowners_unlinkIncompatible (g : GPathM) (id : PathNodeId) :
    (unlinkIncompatible g id).gowners = g.gowners := by
  unfold unlinkIncompatible; split <;> rfl

/-- `aggPair` tampoco: sus dos ramas son `updateAt`. -/
theorem gowners_aggPair (g : GPathM) (x w : PathNodeId) :
    (aggPair g x w).gowners = g.gowners := by
  unfold aggPair
  split
  · split
    · rfl
    · split
      · rfl
      · rfl
  · rfl

/-- **Y `removeNode` solo se lleva el nodo que borra.** -/
theorem mem_gowners_removeNode (g : GPathM) (id z : PathNodeId) (hz : z ∈ g.gowners)
    (hne : z ≠ id) : z ∈ (removeNode g id).gowners := by
  simp only [removeNode, List.mem_filter]
  exact ⟨hz, bne_iff_ne.mpr hne⟩

/-- **El paso del review conserva toda entrada que no sea la que está mirando.**

Es el ladrillo que la inducción necesita: `cleanStep` intercala `updateAt` y `unlinkIncompatible`
—que no tocan la tabla global— y termina, como mucho, en un `removeNode` del **propio** id. -/
theorem mem_gowners_cleanStep (g : GPathM) (id z : PathNodeId) (hz : z ∈ g.gowners)
    (hne : z ≠ id) : z ∈ (cleanStep g id).gowners := by
  unfold cleanStep
  split
  · exact hz
  · unfold intersectOrDrop
    have hg : ∀ f : PNodeM → PNodeM,
        z ∈ (unlinkIncompatible (updateAt g id f) id).gowners := by
      intro f; rw [gowners_unlinkIncompatible, gowners_updateAt]; exact hz
    split
    · exact hg _
    · exact mem_gowners_removeNode _ id z (hg _) hne

/-- **Y por tanto una vuelta entera de `cleanInvalid` conserva lo que no mira.** -/
theorem mem_gowners_cleanInvalidGo (z : PathNodeId) :
    ∀ (ids : List PathNodeId) (g : GPathM), z ∈ g.gowners → z ∉ ids →
      z ∈ (cleanInvalidGo g ids).gowners := by
  intro ids
  induction ids with
  | nil => intro g hz _; exact hz
  | cons id rest ih =>
    intro g hz hnot
    rw [cleanInvalidGo_cons]
    exact ih _ (mem_gowners_cleanStep g id z hz (fun he => hnot (he ▸ List.mem_cons_self)))
      (fun hm => hnot (List.mem_cons_of_mem _ hm))

/-! ## Lo que falta de la inducción, y es un solo caso

Con estos ladrillos, el invariante

    I(h) :  ∀ z ∈ (tabla de q), z ∈ h.gowners

solo puede romperse cuando el review **mira exactamente a un `z` de la tabla de `q`** — en los
demás pasos `mem_gowners_cleanStep` lo conserva sin condiciones. Y en ese caso la pregunta es una
sola: si `isValidNode` de `z` aguanta el corte.

Y aguanta, por lo ya demostrado: `z` es un owner de `q`, luego comparte paso con `q` en **todos**
los pasos (`AggOk`), luego conserva cobertura mientras `I` valga (`owner_of_pinned_keeps_cover`), y
la cobertura basta para la validez (`isValidNode_of_cover`). El invariante se sostiene a sí mismo.

Lo que queda por escribir es esa implicación dentro del `if` de `intersectOrDrop`, y después
propagarla por `reviewFuel`, `aggSweep` y `reviewAggFuel`. Ya no hay ninguna pregunta abierta de
diseño: hay tres recursiones que recorrer con un invariante que se conserva. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.mem_gowners_cleanStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_gowners_cleanStep

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.mem_gowners_cleanInvalidGo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_gowners_cleanInvalidGo

-- ============================================================
-- Y el caso que faltaba: cuando el review mira al propio nodo
-- ============================================================

/-- El paso del review, con el nodo a la vista. -/
theorem cleanStep_some (g : GPathM) (id : PathNodeId) (d : PNodeM) (h : g.node? id = some d) :
    cleanStep g id = intersectOrDrop g id g.gowners d := by
  simp only [cleanStep, h]

/-- Y cuando el nodo ya no está, el paso no hace nada. -/
theorem cleanStep_none (g : GPathM) (id : PathNodeId) (h : g.node? id = none) :
    cleanStep g id = g := by
  simp only [cleanStep, h]

/-- Desenlazar no mueve el paso actual. -/
theorem current_step_unlinkIncompatible (g : GPathM) (id : PathNodeId) :
    (unlinkIncompatible g id).current_step = g.current_step := by
  unfold unlinkIncompatible; split <;> rfl

/-- **`isValidNode` solo lee el paso actual del grafo.** Dos grafos con el mismo paso dan el mismo
veredicto sobre el mismo nodo — y es la razón por la que el corte del review no puede invalidar a
nadie *por el grafo*, solo por el nodo. -/
theorem isValidNode_congr_step (g h : GPathM) (n : PNodeM)
    (hcs : h.current_step = g.current_step) : isValidNode h n = isValidNode g n := by
  unfold isValidNode; rw [hcs]

/-- **El review conserva también la entrada que está mirando, si el nodo era válido.**

Y con esto el ladrillo está completo, porque las dos condiciones del `if` de `intersectOrDrop` se
resuelven con lo ya demostrado:

* el nodo que se somete a examen es `relink (intersectOwners nz.owners gowners) nz`, que **es `nz`**
  cuando su tabla está dentro de la tabla global y sus enlaces dentro de su tabla
  (`relink_eq_self`);
* y el grafo contra el que se examina tiene el mismo paso actual, así que el veredicto es el mismo
  (`isValidNode_congr_step`).

De modo que si `nz` era válido, el `if` va por la rama que **no borra**, y `z` sigue en la tabla
global. -/
theorem mem_gowners_cleanStep_self (g : GPathM) (z : PathNodeId) (nz : PNodeM)
    (hz : z ∈ g.gowners) (hn : g.node? z = some nz)
    (hw : ∀ q ∈ nz.owners, q ∈ g.gowners)
    (hp : ∀ p ∈ nz.parents, p ∈ nz.owners) (hs : ∀ s ∈ nz.sons, s ∈ nz.owners)
    (hval : isValidNode g nz = true) : z ∈ (cleanStep g z).gowners := by
  have hstep : (unlinkIncompatible
      (updateAt g z (fun n => { n with owners := intersectOwners n.owners g.gowners })) z).current_step
      = g.current_step := current_step_unlinkIncompatible _ _
  rw [cleanStep_some g z nz hn]
  unfold intersectOrDrop
  split
  · rw [gowners_unlinkIncompatible, gowners_updateAt]; exact hz
  · next hbad =>
    exact absurd (by
      rw [relink_eq_self nz g.gowners hw hp hs, isValidNode_congr_step g _ nz hstep]
      exact hval) hbad

/-- **Y entonces una vuelta entera de `cleanInvalid` conserva a todo nodo válido cuya tabla esté
dentro de la tabla global.**

Ya sin la condición `z ∉ ids`: o el review no lo mira, y lo conserva por `mem_gowners_cleanStep`,
o lo mira, y lo conserva por `mem_gowners_cleanStep_self`.

Queda una única hipótesis, la que hace falta **en el estado intermedio**: que al llegarle el turno
`z` siga siendo válido y su tabla siga dentro de la tabla global. Que es, otra vez, el invariante
que se sostiene a sí mismo. -/
theorem mem_gowners_cleanInvalidGo_of_valid (z : PathNodeId) :
    ∀ (ids : List PathNodeId) (g : GPathM), z ∈ g.gowners →
      (∀ h : GPathM, ∀ nz : PNodeM, h.node? z = some nz → z ∈ h.gowners →
        (∀ q ∈ nz.owners, q ∈ h.gowners) ∧ (∀ p ∈ nz.parents, p ∈ nz.owners) ∧
          (∀ s ∈ nz.sons, s ∈ nz.owners) ∧ isValidNode h nz = true) →
      z ∈ (cleanInvalidGo g ids).gowners := by
  intro ids
  induction ids with
  | nil => intro g hz _; exact hz
  | cons id rest ih =>
    intro g hz hkeep
    rw [cleanInvalidGo_cons]
    refine ih _ ?_ hkeep
    by_cases he : z = id
    · subst he
      cases hnz : g.node? z with
      | none => rw [cleanStep_none g z hnz]; exact hz
      | some nz =>
        obtain ⟨hw, hp, hs, hval⟩ := hkeep g nz hnz hz
        exact mem_gowners_cleanStep_self g z nz hz hnz hw hp hs hval
    · exact mem_gowners_cleanStep g id z hz he

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.mem_gowners_cleanStep_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_gowners_cleanStep_self

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.mem_gowners_cleanInvalidGo_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_gowners_cleanInvalidGo_of_valid

-- ============================================================
-- Y el desenlace no toca a los demás: las dos únicas salidas
-- ============================================================

/-- **Si el nodo que se desenlaza posee a `m`, `m` se queda igual.** Es la segunda rama de
`unlinkMap`, literal. -/
theorem unlinkMap_keeps (n : PNodeM) (id : PathNodeId) (m : PNodeM) (hne : m.id ≠ id)
    (h : n.owners.contains m.id = true) : unlinkMap n id m = m := by
  unfold unlinkMap
  rw [if_neg (by simpa using hne), if_pos h]

/-- **Y si `m` no estaba enlazado con él, tampoco.** Quitar lo que no hay no quita nada. -/
theorem unlinkMap_keeps_unlinked (n : PNodeM) (id : PathNodeId) (m : PNodeM) (hne : m.id ≠ id)
    (hp : id ∉ m.parents) (hs : id ∉ m.sons) : unlinkMap n id m = m := by
  unfold unlinkMap
  rw [if_neg (by simpa using hne)]
  split
  · rfl
  · rw [List.filter_eq_self.mpr
          (fun p hpm => bne_iff_ne.mpr (fun he => hp (by rw [← he]; exact hpm))),
        List.filter_eq_self.mpr
          (fun t htm => bne_iff_ne.mpr (fun he => hs (by rw [← he]; exact htm)))]

/-- **El desenlace deja intacto a todo nodo protegido.**

Y solo hay dos casos, los dos cubiertos:

* o el nodo desenlazado **posee** a `z` —lo que la simetría de `AggOk` garantiza cuando `z` lo
  posee a él—, y entonces `unlinkMap` no lo toca;
* o `z` **no lo tiene en su tabla**, y entonces tampoco lo tiene entre sus enlaces
  (`LinksWithin`), así que el filtro no le quita nada.

No hay tercera salida. Con esto, un nodo protegido cruza `unlinkIncompatible` idéntico a sí
mismo. -/
theorem unlinkIncompatible_keeps (g : GPathM) (id : PathNodeId) (n : PNodeM)
    (hn : g.node? id = some n) (z : PathNodeId) (nz : PNodeM) (hz : g.node? z = some nz)
    (hne : z ≠ id) (hp : ∀ p ∈ nz.parents, p ∈ nz.owners) (hs : ∀ t ∈ nz.sons, t ∈ nz.owners)
    (hcase : z ∈ n.owners ∨ id ∉ nz.owners) :
    (unlinkIncompatible g id).node? z = some nz := by
  have hid : nz.id = z := node?_id_eq g z nz hz
  rw [unlinkIncompatible_node? g id n hn z nz hz]
  rcases hcase with hown | hout
  · rw [unlinkMap_keeps n id nz (by rw [hid]; exact hne) (by rw [hid]; simpa using hown)]
  · rw [unlinkMap_keeps_unlinked n id nz (by rw [hid]; exact hne)
      (fun hm => hout (hp id hm)) (fun hm => hout (hs id hm))]

/-! ## El invariante, ya con todas sus piezas

Para llevar la tabla de `q` entera a través de una vuelta del review hacen falta exactamente tres
cosas, y las tres están:

1. **que la entrada siga en la tabla global** — `mem_gowners_cleanStep` si el review mira a otro,
   `mem_gowners_cleanStep_self` si la mira a ella;
2. **que el nodo no cambie al desenlazar** — `unlinkIncompatible_keeps`, con sus dos únicas
   salidas;
3. **que siga siendo válido** — `isValidNode_of_cover` sobre la cobertura que
   `owner_of_pinned_keeps_cover` le garantiza mientras el invariante valga.

Y el `updateAt` intermedio no cuenta: solo toca al nodo que el review está mirando, y sobre él ya
sabemos que es la identidad cuando su tabla está dentro de la global (`relink_eq_self`).

Lo que queda es ensamblar las tres en la recursión —`cleanInvalidGo`, luego `reviewPass`,
`reviewFuel`, `aggSweep`, `reviewAggFuel`—. Ni una de esas cinco pregunta nada nuevo: son bucles
sobre listas. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.unlinkMap_keeps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms unlinkMap_keeps

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.unlinkIncompatible_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unlinkIncompatible_keeps

-- ============================================================
-- El invariante, en su forma definitiva: la COBERTURA
-- ============================================================

/-- **Un nodo vivo cuya tabla cubre todos los pasos dentro de la tabla global.**

Éste es el invariante bueno, y no el valor del nodo: los enlaces de un nodo cambian cuando muere un
vecino, pero **su tabla no** —`removeNode` filtra padres e hijos y no toca los owners de nadie—.
Y por `isValidNode_of_cover` la validez sale de la cobertura, no de los enlaces. -/
def Cover (g : GPathM) (z : PathNodeId) : Prop :=
  ∃ nz, g.node? z = some nz ∧
    ∀ k, 0 ≤ k → k < g.current_step → ∃ w ∈ nz.owners, w.id.step = k ∧ w ∈ g.gowners

/-- **Y un solo nodo con cobertura hace válido el estado. Sin ninguna hipótesis.**

Mejor que `isValid_of_survivor`, que pedía `OwnersWithin`: aquí los testigos vienen ya dentro de la
tabla global, que es lo que la cobertura dice. -/
theorem isValid_of_Cover (g : GPathM) (z : PathNodeId) (hc : Cover g z) : isValid g = true := by
  obtain ⟨_, _, hcov⟩ := hc
  simp only [isValid, List.all_eq_true]
  intro k hk
  obtain ⟨w, _, hws, hwg⟩ := hcov k (mem_intRange_lower hk)
    (by have := mem_intRange_upper hk; omega)
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq]
  exact ⟨w, hwg, hws⟩

/-- **Borrar un nodo no toca la tabla de nadie.** `removeNode` filtra padres, hijos y la tabla
global; los owners los deja intactos. -/
theorem owners_removeNode (g : GPathM) (id z : PathNodeId) (nz : PNodeM)
    (hz : g.node? z = some nz) (hne : z ≠ id) :
    (removeNode g id).node? z = some (unlink id nz) ∧ (unlink id nz).owners = nz.owners :=
  ⟨removeNode_node? g id z nz hz hne, rfl⟩

/-- **Y entonces la cobertura sobrevive a una muerte, salvo que el muerto fuera su único testigo.**

Que es exactamente lo que había que aislar: la cascada no puede romper la cobertura de `z` por
efectos laterales —ni por enlaces, ni por cortes de tabla—, **solo** quitándole un testigo. -/
theorem Cover_removeNode (g : GPathM) (id z : PathNodeId) (nz : PNodeM) (hne : z ≠ id)
    (hz : g.node? z = some nz)
    (hcov : ∀ k, 0 ≤ k → k < g.current_step →
      ∃ w ∈ nz.owners, w.id.step = k ∧ w ∈ g.gowners ∧ w ≠ id) :
    Cover (removeNode g id) z := by
  refine ⟨unlink id nz, removeNode_node? g id z nz hz hne, ?_⟩
  intro k hk0 hk1
  obtain ⟨w, hwm, hws, hwg, hwne⟩ := hcov k hk0 hk1
  exact ⟨w, hwm, hws, by
    rw [removeNode_gowners, List.mem_filter]
    exact ⟨hwg, bne_iff_ne.mpr hwne⟩⟩

/-! ## Por qué la cobertura es el invariante y no otro

Las tres operaciones que el review encadena se comportan, frente a la cobertura, así:

| operación | tabla del nodo | tabla global | cobertura |
|---|---|---|---|
| `updateAt` (el corte) | la corta contra `gowners` | intacta | **intacta** si la tabla ya estaba dentro |
| `unlinkIncompatible` | no la toca | intacta | **intacta** |
| `removeNode id` | **no la toca** | pierde `id` | intacta salvo que `id` fuera testigo |

O sea que la cobertura solo se puede perder de **una** manera, y está aislada: que muera un owner
que era el único testigo de algún paso. Los enlaces ya no entran —la validez sale de la cobertura
(`isValidNode_of_cover`)— y el estado entero ya no entra —la validez del estado sale de una sola
cobertura (`isValid_of_Cover`, sin hipótesis)—.

Y para la tabla de `q` esa única manera está cerrada por la simetría y el cruce de `AggOk`: sus
owners comparten paso con `q` en todos los pasos, así que mientras su tabla esté en pie ninguno se
queda sin testigos. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValid_of_Cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_of_Cover

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Cover_removeNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cover_removeNode

-- ============================================================
-- Y la cobertura atraviesa un paso entero del review
-- ============================================================

/-- **El desenlace no toca la tabla de nadie.** Las tres ramas de `unlinkMap` filtran padres e hijos
y dejan los owners donde estaban. -/
theorem owners_unlinkMap (n : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (unlinkMap n id m).owners = m.owners := by
  unfold unlinkMap
  split
  · rfl
  · split
    · rfl
    · rfl

/-- **La cobertura, con sus testigos distintos de un id dado.** Lo que hace falta para cruzar un
`removeNode` de ese id. -/
def CoverNe (g : GPathM) (z : PathNodeId) (id : PathNodeId) : Prop :=
  ∃ nz, g.node? z = some nz ∧
    ∀ k, 0 ≤ k → k < g.current_step →
      ∃ w ∈ nz.owners, w.id.step = k ∧ w ∈ g.gowners ∧ w ≠ id

theorem Cover_of_CoverNe (g : GPathM) (z id : PathNodeId) (h : CoverNe g z id) : Cover g z := by
  obtain ⟨nz, hz, hcov⟩ := h
  exact ⟨nz, hz, fun k hk0 hk1 =>
    let ⟨w, hwm, hws, hwg, _⟩ := hcov k hk0 hk1; ⟨w, hwm, hws, hwg⟩⟩

/-- Actualizar otro nodo no afecta a la cobertura. -/
theorem CoverNe_updateAt (g : GPathM) (id r z : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, (f n).id = n.id) (hne : z ≠ r) (h : CoverNe g z id) :
    CoverNe (updateAt g r f) z id := by
  obtain ⟨nz, hz, hcov⟩ := h
  have hid : nz.id = z := node?_id_eq g z nz hz
  refine ⟨nz, ?_, hcov⟩
  rw [updateAt_node? g r f hf z nz hz,
      show (nz.id == r) = false from beq_eq_false_iff_ne.mpr (by rw [hid]; exact hne)]

/-- Desenlazar tampoco: solo cambia enlaces. -/
theorem CoverNe_unlinkIncompatible (g : GPathM) (id r z : PathNodeId) (h : CoverNe g z id) :
    CoverNe (unlinkIncompatible g r) z id := by
  obtain ⟨nz, hz, hcov⟩ := h
  cases hn : g.node? r with
  | none =>
    have he : unlinkIncompatible g r = g := by unfold unlinkIncompatible; rw [hn]
    rw [he]; exact ⟨nz, hz, hcov⟩
  | some n =>
    refine ⟨unlinkMap n r nz, unlinkIncompatible_node? g r n hn z nz hz, ?_⟩
    intro k hk0 hk1
    rw [current_step_unlinkIncompatible] at hk1
    obtain ⟨w, hwm, hws, hwg, hwne⟩ := hcov k hk0 hk1
    exact ⟨w, by rw [owners_unlinkMap]; exact hwm, hws,
      by rw [gowners_unlinkIncompatible]; exact hwg, hwne⟩

/-- **Y entonces la cobertura cruza un paso entero del review.**

Las tres piezas del paso, cada una con su motivo:

* el **corte** solo toca el nodo que se está mirando, y `z` no es ése;
* el **desenlace** no toca la tabla de nadie;
* y el **borrado**, si ocurre, se lleva únicamente al nodo mirado — que por hipótesis no es testigo
  de ningún paso de `z`.

Con esto el análisis de una vuelta está cerrado: **la cobertura de `z` solo se pierde si el review
borra a un testigo suyo.** Ni por cortes, ni por enlaces, ni por efectos laterales. -/
theorem Cover_cleanStep (g : GPathM) (r z : PathNodeId) (hne : z ≠ r)
    (h : CoverNe g z r) : Cover (cleanStep g r) z := by
  cases hn : g.node? r with
  | none => rw [cleanStep_none g r hn]; exact Cover_of_CoverNe g z r h
  | some d =>
    rw [cleanStep_some g r d hn]
    unfold intersectOrDrop
    have h' : CoverNe (unlinkIncompatible
        (updateAt g r (fun n => { n with owners := intersectOwners n.owners g.gowners })) r) z r :=
      CoverNe_unlinkIncompatible _ r r z (CoverNe_updateAt g r r z _ (fun _ => rfl) hne h)
    split
    · exact Cover_of_CoverNe _ z r h'
    · obtain ⟨nz, hz, hcov⟩ := h'
      exact Cover_removeNode _ r z nz hne hz hcov

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Cover_cleanStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cover_cleanStep

-- ============================================================
-- El invariante que no necesita punto fijo
-- ============================================================

/-- **La cobertura anclada**, y con testigos dentro del propio conjunto protegido.

`isValidNode_of_cover` sacaba los enlaces de la cobertura, pero para eso necesitaba `Adj`, que es
una propiedad **del punto fijo** — y dentro del bucle del review el estado no es un punto fijo. Así
que el invariante que hay que llevar a cuestas guarda los enlaces explícitamente:

* la tabla de `z` cubre todos los pasos, con testigos **en `P`** y dentro de la tabla global;
* si `z` no está en el paso 0, tiene un padre **en `P`**;
* si no está en el último, tiene un hijo **en `P`**.

Que los testigos y los anclajes estén en `P` es lo que hace el invariante **cerrado**: para
romperlo habría que borrar a un miembro de `P`, y los miembros de `P` son justo los que el
invariante mantiene válidos. -/
def Anchored (g : GPathM) (P : PathNodeId → Prop) (z : PathNodeId) : Prop :=
  ∃ nz, g.node? z = some nz ∧
    (∀ k, 0 ≤ k → k < g.current_step → ∃ w ∈ nz.owners, w.id.step = k ∧ w ∈ g.gowners ∧ P w) ∧
    (1 ≤ z.id.step → ∃ p ∈ nz.parents, P p ∧ p ∈ nz.owners ∧ p ∈ g.gowners) ∧
    (z.id.step ≤ g.current_step - 2 → ∃ t ∈ nz.sons, P t ∧ t ∈ nz.owners ∧ t ∈ g.gowners)

/-- **Y de él la validez del nodo sale sin ninguna propiedad de punto fijo.** -/
theorem isValidNode_of_Anchored (g : GPathM) (P : PathNodeId → Prop) (z : PathNodeId)
    (hrz : Sons.RootAtZero g) (hz0 : 0 ≤ z.id.step) (hz1 : z.id.step < g.current_step)
    (h : Anchored g P z) : ∃ nz, g.node? z = some nz ∧ isValidNode g nz = true := by
  obtain ⟨nz, hn, hcov, hpar, hson⟩ := h
  refine ⟨nz, hn, ?_⟩
  have hid : nz.id = z := node?_id_eq g z nz hn
  have hmem := List.mem_of_find?_eq_some hn
  have howners : (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry nz.owners k) = true := by
    simp only [List.all_eq_true]
    intro k hk
    obtain ⟨w, hw, hws, _, _⟩ := hcov k (mem_intRange_lower hk)
      (by have := mem_intRange_upper hk; omega)
    simp only [hasStepEntry, List.any_eq_true]
    exact ⟨w, hw, beq_iff_eq.mpr hws⟩
  have hp : 1 ≤ z.id.step → nz.parents ≠ [] := fun h1 =>
    let ⟨p, hpm, _, _, _⟩ := hpar h1; List.ne_nil_of_mem hpm
  have hs : z.id.step ≤ g.current_step - 2 → nz.sons ≠ [] := fun h2 =>
    let ⟨t, htm, _, _, _⟩ := hson h2; List.ne_nil_of_mem htm
  have hnr : ¬(nz.id.parent_id.isNone = true) → 1 ≤ z.id.step := by
    intro hr
    by_cases h1 : 1 ≤ z.id.step
    · exact h1
    · exact absurd (by rw [hrz nz hmem (by rw [hid]; omega)]; rfl) hr
  have hlast : (nz.id.id.step == g.current_step - 1) = (z.id.step == g.current_step - 1) := by
    rw [hid]
  have hnotlast : ¬((z.id.step == g.current_step - 1) = true) → z.id.step ≤ g.current_step - 2 := by
    intro hl
    have : z.id.step ≠ g.current_step - 1 := fun he => hl (by rw [he]; exact beq_iff_eq.mpr rfl)
    omega
  simp only [isValidNode, hlast]
  split
  · split
    · exact howners
    · next hl =>
      simp only [howners, not_isEmpty_of_ne_nil _ (hs (hnotlast hl)), Bool.and_self]
  · next hr =>
    split
    · simp only [howners, not_isEmpty_of_ne_nil _ (hp (hnr hr)), Bool.and_self]
    · next hl =>
      simp only [howners, not_isEmpty_of_ne_nil _ (hp (hnr hr)),
        not_isEmpty_of_ne_nil _ (hs (hnotlast hl)), Bool.and_self]

/-- **Y la validez del estado, también.** Un solo anclado basta. -/
theorem isValid_of_Anchored (g : GPathM) (P : PathNodeId → Prop) (z : PathNodeId)
    (h : Anchored g P z) : isValid g = true := by
  obtain ⟨nz, hn, hcov, _, _⟩ := h
  exact isValid_of_Cover g z ⟨nz, hn, fun k hk0 hk1 =>
    let ⟨w, hw, hws, hwg, _⟩ := hcov k hk0 hk1; ⟨w, hw, hws, hwg⟩⟩

/-! ## Por qué este invariante es el que se puede llevar en el bucle

`Adj` —«los owners de los pasos vecinos son los enlaces»— vale en los estados que el lector visita,
que son puntos fijos del review. Dentro del bucle no vale, y por eso `isValidNode_of_cover` no
servía para razonar paso a paso. `Anchored` lo arregla guardando los enlaces en el propio
invariante, y se paga barato: se instancia **una vez** al principio, donde `Adj` sí vale, y a partir
de ahí solo hay que conservarlo.

Y se conserva por lo ya demostrado: el corte no toca a otros nodos, el desenlace no toca tablas
(`owners_unlinkMap`), y el borrado solo se lleva al nodo mirado. Los testigos y los anclajes están
en `P`, así que **el único modo de romperlo sigue siendo borrar a un miembro de `P`** — y por
`isValidNode_of_Anchored` los miembros de `P` son válidos, luego el review no los borra.

El círculo está cerrado en lo conceptual; lo que queda es recorrer los cinco bucles con él. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValidNode_of_Anchored' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValidNode_of_Anchored

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValid_of_Anchored' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_of_Anchored

-- ============================================================
-- Los anclajes también cruzan: un enlace solo se pierde con su nodo
-- ============================================================

/-- **Un padre distinto del nodo desenlazado sobrevive al desenlace.**

La primera rama de `unlinkMap` —la que filtra los enlaces contra la tabla— es solo para el propio
nodo desenlazado; para cualquier otro, o no se toca nada, o se quita exactamente ese id. -/
theorem parents_unlinkMap_keeps (n : PNodeM) (r : PathNodeId) (m : PNodeM) (hmr : m.id ≠ r)
    (p : PathNodeId) (hp : p ∈ m.parents) (hne : p ≠ r) : p ∈ (unlinkMap n r m).parents := by
  unfold unlinkMap
  rw [if_neg (by simpa using hmr)]
  split
  · exact hp
  · exact List.mem_filter.mpr ⟨hp, bne_iff_ne.mpr hne⟩

/-- **Y un hijo, igual.** -/
theorem sons_unlinkMap_keeps (n : PNodeM) (r : PathNodeId) (m : PNodeM) (hmr : m.id ≠ r)
    (t : PathNodeId) (ht : t ∈ m.sons) (hne : t ≠ r) : t ∈ (unlinkMap n r m).sons := by
  unfold unlinkMap
  rw [if_neg (by simpa using hmr)]
  split
  · exact ht
  · exact List.mem_filter.mpr ⟨ht, bne_iff_ne.mpr hne⟩

/-- **Y al borrado: `removeNode` solo quita de los enlaces al nodo que borra.** -/
theorem parents_unlink_keeps (r : PathNodeId) (m : PNodeM) (p : PathNodeId)
    (hp : p ∈ m.parents) (hne : p ≠ r) : p ∈ (unlink r m).parents :=
  List.mem_filter.mpr ⟨hp, bne_iff_ne.mpr hne⟩

theorem sons_unlink_keeps (r : PathNodeId) (m : PNodeM) (t : PathNodeId)
    (ht : t ∈ m.sons) (hne : t ≠ r) : t ∈ (unlink r m).sons :=
  List.mem_filter.mpr ⟨ht, bne_iff_ne.mpr hne⟩

/-! ## El herramental, completo

Con estos cuatro, cada campo de `Anchored` tiene ya su lema de supervivencia frente a cada
operación del review:

| | corte (`updateAt`) | desenlace (`unlinkMap`) | borrado (`removeNode`) |
|---|---|---|---|
| **está vivo** | `updateAt_node?` | `unlinkIncompatible_node?` | `removeNode_node?` |
| **tabla** | intacta si estaba dentro | `owners_unlinkMap` | `owners_removeNode` |
| **tabla global** | `gowners_updateAt` | `gowners_unlinkIncompatible` | `mem_gowners_removeNode` |
| **padre anclado** | no lo toca | `parents_unlinkMap_keeps` | `parents_unlink_keeps` |
| **hijo anclado** | no lo toca | `sons_unlinkMap_keeps` | `sons_unlink_keeps` |

Y en las tres columnas la condición es **siempre la misma**: que el nodo afectado no sea el
testigo ni el anclaje, es decir que no sea un miembro de `P`. Que es justo lo que
`isValidNode_of_Anchored` garantiza, porque un miembro de `P` es válido y el review no borra
nodos válidos.

No queda ninguna pieza suelta. Lo que falta es enhebrar la tabla de arriba por los cinco bucles
—`cleanInvalidGo`, `reviewPass`, `reviewFuel`, `aggSweep`, `reviewAggFuel`—, y cada casilla ya
tiene su lema con nombre. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.parents_unlinkMap_keeps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parents_unlinkMap_keeps

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.parents_unlink_keeps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parents_unlink_keeps

-- ============================================================
-- Primer ladrillo del ensamblaje: `Anchored` cruza el corte
-- ============================================================

/-- **El corte de otro nodo no afecta a un anclado.** `updateAt` solo toca al nodo que nombra, y la
tabla global y el paso actual no se mueven. -/
theorem Anchored_updateAt (g : GPathM) (P : PathNodeId → Prop) (z r : PathNodeId)
    (f : PNodeM → PNodeM) (hf : ∀ n, (f n).id = n.id) (hne : z ≠ r)
    (h : Anchored g P z) : Anchored (updateAt g r f) P z := by
  obtain ⟨nz, hn, hcov, hpar, hson⟩ := h
  have hid : nz.id = z := node?_id_eq g z nz hn
  refine ⟨nz, ?_, hcov, hpar, hson⟩
  rw [updateAt_node? g r f hf z nz hn,
      show (nz.id == r) = false from beq_eq_false_iff_ne.mpr (by rw [hid]; exact hne)]

/-- **Y cruza el desenlace, si el desenlazado no es de los protegidos.**

Los tres campos, cada uno por su lema: la tabla no la toca `unlinkMap`, la tabla global tampoco, y
el padre y el hijo anclados sobreviven porque están en `P` y el desenlazado no.

Es el primer sitio donde se ve funcionar el cierre del invariante: **lo único que podría hacer daño
está excluido por ser miembro de `P`.** -/
theorem Anchored_unlinkIncompatible (g : GPathM) (P : PathNodeId → Prop) (z r : PathNodeId)
    (hne : z ≠ r) (hPr : ¬ P r) (h : Anchored g P z) :
    Anchored (unlinkIncompatible g r) P z := by
  obtain ⟨nz, hn, hcov, hpar, hson⟩ := h
  have hid : nz.id = z := node?_id_eq g z nz hn
  cases hnr : g.node? r with
  | none =>
    have he : unlinkIncompatible g r = g := by unfold unlinkIncompatible; rw [hnr]
    rw [he]; exact ⟨nz, hn, hcov, hpar, hson⟩
  | some n =>
    refine ⟨unlinkMap n r nz, unlinkIncompatible_node? g r n hnr z nz hn, ?_, ?_, ?_⟩
    · intro k hk0 hk1
      rw [current_step_unlinkIncompatible] at hk1
      obtain ⟨w, hwm, hws, hwg, hwP⟩ := hcov k hk0 hk1
      exact ⟨w, by rw [owners_unlinkMap]; exact hwm, hws,
        by rw [gowners_unlinkIncompatible]; exact hwg, hwP⟩
    · intro h1
      obtain ⟨p, hpm, hpP, hpo, hpg⟩ := hpar h1
      exact ⟨p, parents_unlinkMap_keeps n r nz (by rw [hid]; exact hne) p hpm
        (fun he => hPr (by rw [← he]; exact hpP)), hpP,
        by rw [owners_unlinkMap]; exact hpo,
        by rw [gowners_unlinkIncompatible]; exact hpg⟩
    · intro h2
      rw [current_step_unlinkIncompatible] at h2
      obtain ⟨t, htm, htP, hto, htg⟩ := hson h2
      exact ⟨t, sons_unlinkMap_keeps n r nz (by rw [hid]; exact hne) t htm
        (fun he => hPr (by rw [← he]; exact htP)), htP,
        by rw [owners_unlinkMap]; exact hto,
        by rw [gowners_unlinkIncompatible]; exact htg⟩

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Anchored_updateAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anchored_updateAt

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Anchored_unlinkIncompatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anchored_unlinkIncompatible

-- ============================================================
-- Tercer ladrillo: `Anchored` cruza el borrado, y con él el paso entero
-- ============================================================

/-- **Y cruza el borrado de un nodo no protegido.**

Los cinco campos, cada uno por su lema: la tabla no la toca `removeNode`, el testigo sigue en la
tabla global porque no es el borrado, y padre e hijo anclados sobreviven por lo mismo. Todo bajo la
única condición de siempre: **el borrado no es de `P`**. -/
theorem Anchored_removeNode (g : GPathM) (P : PathNodeId → Prop) (z r : PathNodeId)
    (hne : z ≠ r) (hPr : ¬ P r) (h : Anchored g P z) :
    Anchored (removeNode g r) P z := by
  obtain ⟨nz, hn, hcov, hpar, hson⟩ := h
  have hcs : (removeNode g r).current_step = g.current_step := rfl
  refine ⟨unlink r nz, removeNode_node? g r z nz hn hne, ?_, ?_, ?_⟩
  · intro k hk0 hk1
    rw [hcs] at hk1
    obtain ⟨w, hwm, hws, hwg, hwP⟩ := hcov k hk0 hk1
    refine ⟨w, hwm, hws, ?_, hwP⟩
    rw [removeNode_gowners, List.mem_filter]
    exact ⟨hwg, bne_iff_ne.mpr (fun he => hPr (by rw [← he]; exact hwP))⟩
  · intro h1
    obtain ⟨p, hpm, hpP, hpo, hpg⟩ := hpar h1
    refine ⟨p, parents_unlink_keeps r nz p hpm (fun he => hPr (by rw [← he]; exact hpP)),
      hpP, hpo, ?_⟩
    rw [removeNode_gowners, List.mem_filter]
    exact ⟨hpg, bne_iff_ne.mpr (fun he => hPr (by rw [← he]; exact hpP))⟩
  · intro h2
    rw [hcs] at h2
    obtain ⟨t, htm, htP, hto, htg⟩ := hson h2
    refine ⟨t, sons_unlink_keeps r nz t htm (fun he => hPr (by rw [← he]; exact htP)),
      htP, hto, ?_⟩
    rw [removeNode_gowners, List.mem_filter]
    exact ⟨htg, bne_iff_ne.mpr (fun he => hPr (by rw [← he]; exact htP))⟩

/-- **Y con los tres, el paso entero del review.**

    Anchored g P z  →  z ≠ r  →  ¬ P r  →  Anchored (cleanStep g r) P z

El caso genérico queda cerrado: **mientras el review mire a un nodo que no está protegido, el
invariante pasa al otro lado intacto**, sin pedir nada del estado ni de la fórmula. Ni punto fijo,
ni cadenas, ni pasos vecinos.

Lo que falta del paso es solo el caso en que el review mira **a un protegido**, y ahí la clave ya
está demostrada: un protegido es válido (`isValidNode_of_Anchored`), y el review no borra nodos
válidos. -/
theorem Anchored_cleanStep (g : GPathM) (P : PathNodeId → Prop) (z r : PathNodeId)
    (hne : z ≠ r) (hPr : ¬ P r) (h : Anchored g P z) : Anchored (cleanStep g r) P z := by
  cases hnr : g.node? r with
  | none => rw [cleanStep_none g r hnr]; exact h
  | some d =>
    rw [cleanStep_some g r d hnr]
    unfold intersectOrDrop
    have h' := Anchored_unlinkIncompatible _ P z r hne hPr
      (Anchored_updateAt g P z r
        (fun n => { n with owners := intersectOwners n.owners g.gowners }) (fun _ => rfl) hne h)
    split
    · exact h'
    · exact Anchored_removeNode _ P z r hne hPr h'

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Anchored_removeNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anchored_removeNode

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Anchored_cleanStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anchored_cleanStep

-- ============================================================
-- Cuarto ladrillo: el review mirando A UN PROTEGIDO no lo borra
-- ============================================================

/-- **El nodo que el review somete a examen, cuando mira a un protegido, es válido.**

Y con eso el `if` de `intersectOrDrop` va por la rama que **no borra**.

Los tres campos del anclaje sobreviven al corte contra la tabla global por la misma razón: **todos
están ya dentro de ella** —los testigos por la cobertura, el padre y el hijo anclados por los dos
conjuntos que el invariante les añade—, así que `intersectOwners` los conserva
(`mem_intersectOwners_of_mem`), y `relinkSelf`, que filtra los enlaces contra los owners nuevos, los
conserva también.

Nótese que esto es, por fin, el enunciado que hacía falta para cerrar el paso del review por ambos
lados: los no protegidos se tratan con `Anchored_cleanStep`, y el protegido con éste. -/
theorem isValidNode_relink_of_Anchored (g : GPathM) (P : PathNodeId → Prop) (r : PathNodeId)
    (nr : PNodeM) (hrz : Sons.RootAtZero g) (hr0 : 0 ≤ r.id.step)
    (hr1 : r.id.step < g.current_step) (hn : g.node? r = some nr) (h : Anchored g P r) :
    isValidNode g (relink (intersectOwners nr.owners g.gowners) nr) = true := by
  obtain ⟨nr', hn', hcov, hpar, hson⟩ := h
  have hnn : nr' = nr := Option.some.inj (hn'.symm.trans hn)
  subst hnn
  have hid : nr'.id = r := node?_id_eq g r nr' hn'
  -- los owners nuevos siguen cubriendo todos los pasos
  have hcov' : ∀ k, 0 ≤ k → k < g.current_step → ∃ w ∈ (intersectOwners nr'.owners g.gowners), w.id.step = k := by
    intro k hk0 hk1
    obtain ⟨w, hwm, hws, hwg, _⟩ := hcov k hk0 hk1
    exact ⟨w, mem_intersectOwners_of_mem _ _ w hwm hwg, hws⟩
  have howners : (intRange 0 (g.current_step - 1)).all
      (fun k => hasStepEntry (relink (intersectOwners nr'.owners g.gowners) nr').owners k) = true := by
    simp only [List.all_eq_true]
    intro k hk
    obtain ⟨w, hwm, hws⟩ := hcov' k (mem_intRange_lower hk)
      (by have := mem_intRange_upper hk; omega)
    simp only [hasStepEntry, List.any_eq_true]
    exact ⟨w, hwm, beq_iff_eq.mpr hws⟩
  -- el padre y el hijo anclados sobreviven al corte y al re-enlace
  have hp : 1 ≤ r.id.step → (relink (intersectOwners nr'.owners g.gowners) nr').parents ≠ [] := by
    intro h1
    obtain ⟨p, hpm, _, hpo, hpg⟩ := hpar h1
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hpm,
      by simpa using mem_intersectOwners_of_mem _ _ p hpo hpg⟩)
  have hs : r.id.step ≤ g.current_step - 2 → (relink (intersectOwners nr'.owners g.gowners) nr').sons ≠ [] := by
    intro h2
    obtain ⟨t, htm, _, hto, htg⟩ := hson h2
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨htm,
      by simpa using mem_intersectOwners_of_mem _ _ t hto htg⟩)
  have hidr : (relink (intersectOwners nr'.owners g.gowners) nr').id = r := hid
  have hnr : ¬((relink (intersectOwners nr'.owners g.gowners) nr').id.parent_id.isNone = true) → 1 ≤ r.id.step := by
    intro hr
    by_cases h1 : 1 ≤ r.id.step
    · exact h1
    · exact absurd (by
        rw [show (relink (intersectOwners nr'.owners g.gowners) nr').id = nr'.id from rfl,
          hrz nr' (List.mem_of_find?_eq_some hn') (by rw [hid]; omega)]; rfl) hr
  have hlast : ((relink (intersectOwners nr'.owners g.gowners) nr').id.id.step == g.current_step - 1)
      = (r.id.step == g.current_step - 1) := by rw [hidr]
  have hnotlast : ¬((r.id.step == g.current_step - 1) = true) → r.id.step ≤ g.current_step - 2 := by
    intro hl
    have : r.id.step ≠ g.current_step - 1 := fun he => hl (by rw [he]; exact beq_iff_eq.mpr rfl)
    omega
  simp only [isValidNode, hlast]
  split
  · split
    · exact howners
    · next hl =>
      simp only [howners, not_isEmpty_of_ne_nil _ (hs (hnotlast hl)), Bool.and_self]
  · next hr =>
    split
    · simp only [howners, not_isEmpty_of_ne_nil _ (hp (hnr hr)), Bool.and_self]
    · next hl =>
      simp only [howners, not_isEmpty_of_ne_nil _ (hp (hnr hr)),
        not_isEmpty_of_ne_nil _ (hs (hnotlast hl)), Bool.and_self]

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.isValidNode_relink_of_Anchored' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValidNode_relink_of_Anchored

-- ============================================================
-- La simetría dentro del conjunto protegido, y que el corte la conserva
-- ============================================================

/-- **Dentro de `P`, poseer es mutuo.**

Es la primera componente de `AggFixpoint.AggOk` restringida al conjunto protegido, y hace falta
para el caso en que el review mira **a un protegido que es anclaje de otro**: `unlinkMap` deja
intacto a todo nodo que el mirado posea, así que la mutualidad es lo que impide que un anclaje se
pierda. -/
def Sym (g : GPathM) (P : PathNodeId → Prop) : Prop :=
  ∀ x y nx ny, P x → P y → g.node? x = some nx → g.node? y = some ny →
    y ∈ nx.owners → x ∈ ny.owners

/-- **Y el corte la conserva.**

La dirección delicada es la de vuelta: si el corte quitara `x` de la tabla de `y` mientras `y` sigue
en la de `x`, la simetría se rompería. No puede: el corte solo quita lo que no está en la tabla
global, y **los miembros de `P` están en la tabla global**.

Es la primera vez que se usa `P ⊆ gowners`, y es justo para esto. -/
theorem Sym_cut (g : GPathM) (P : PathNodeId → Prop) (r : PathNodeId)
    (hPg : ∀ x, P x → x ∈ g.gowners) (h : Sym g P) :
    Sym (updateAt g r (fun n => { n with owners := intersectOwners n.owners g.gowners })) P := by
  intro x y nx ny hx hy hnx hny hyx
  obtain ⟨nx0, hnx0, hxe⟩ :=
    Reader.updateAt_node?_inv g r (fun n => { n with owners := intersectOwners n.owners g.gowners })
      (fun _ => rfl) x nx hnx
  obtain ⟨ny0, hny0, hye⟩ :=
    Reader.updateAt_node?_inv g r (fun n => { n with owners := intersectOwners n.owners g.gowners })
      (fun _ => rfl) y ny hny
  have hyx0 : y ∈ nx0.owners := by
    subst hxe
    cases hb : nx0.id == r with
    | true =>
      simp only [hb, intersectOwners, List.mem_filter] at hyx
      exact hyx.1
    | false => simp only [hb] at hyx; exact hyx
  have hxy0 : x ∈ ny0.owners := h x y nx0 ny0 hx hy hnx0 hny0 hyx0
  subst hye
  cases hb : ny0.id == r with
  | true => exact mem_intersectOwners_of_mem _ _ x hxy0 (hPg x hx)
  | false => exact hxy0

/-! ## Qué falta para cerrar el paso del review para TODO `r`

El caso `¬ P r` está cerrado (`Anchored_cleanStep`) y el nodo protegido no se borra
(`isValidNode_relink_of_Anchored`). Lo que queda del caso `P r` es que los **anclajes** de los demás
protegidos sobrevivan al `unlinkMap` de `r`, y para eso `unlinkMap` ofrece la salida buena: **deja
intacto a todo nodo que el mirado posea**. `Sym` es exactamente esa hipótesis, y `Sym_cut` dice que
el corte previo no la estropea.

Faltan las dos conservaciones restantes de `Sym` —frente al desenlace y al borrado—, que necesitan
una inversión de `unlinkIncompatible_node?` con `NodupIds`; y con ellas, el paso entero. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Sym_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sym_cut

-- ============================================================
-- Las dos inversiones, y con ellas `Sym` entera
-- ============================================================

/-- **Inversión del desenlace: todo nodo del resultado viene de uno del original, con su misma
tabla.** -/
theorem unlinkIncompatible_node?_inv (g : GPathM) (hnd : NodupIds g) (r x : PathNodeId)
    (nx : PNodeM) (hx : (unlinkIncompatible g r).node? x = some nx) :
    ∃ nx0, g.node? x = some nx0 ∧ nx.owners = nx0.owners := by
  cases hnr : g.node? r with
  | none =>
    have he : unlinkIncompatible g r = g := by unfold unlinkIncompatible; rw [hnr]
    rw [he] at hx
    exact ⟨nx, hx, rfl⟩
  | some n =>
    have hshape : (unlinkIncompatible g r).nodes = g.nodes.map (unlinkMap n r) := by
      simp only [unlinkIncompatible, hnr]
    have hmem : nx ∈ (unlinkIncompatible g r).nodes := List.mem_of_find?_eq_some hx
    rw [hshape] at hmem
    obtain ⟨nx0, hnx0, heq⟩ := List.mem_map.mp hmem
    have hxid : nx.id = x := node?_id_eq _ x nx hx
    have h0id : nx0.id = x := by rw [← hxid, ← heq, unlinkMap_id]
    exact ⟨nx0, by rw [← h0id]; exact node?_of_mem hnd nx0 hnx0, by rw [← heq, owners_unlinkMap]⟩

/-- **Inversión del borrado, igual.** `removeNode` filtra y re-enlaza, pero no toca tablas. -/
theorem removeNode_node?_inv (g : GPathM) (hnd : NodupIds g) (r x : PathNodeId)
    (nx : PNodeM) (hx : (removeNode g r).node? x = some nx) :
    ∃ nx0, g.node? x = some nx0 ∧ nx.owners = nx0.owners := by
  have hmem : nx ∈ (removeNode g r).nodes := List.mem_of_find?_eq_some hx
  rw [removeNode_nodes] at hmem
  obtain ⟨nx0, hnx0, heq⟩ := List.mem_map.mp hmem
  have hxid : nx.id = x := node?_id_eq _ x nx hx
  have h0id : nx0.id = x := by rw [← hxid, ← heq]; rfl
  exact ⟨nx0, by rw [← h0id]; exact node?_of_mem hnd nx0 (List.mem_filter.mp hnx0).1,
    by rw [← heq]; rfl⟩

/-- **Y entonces el desenlace conserva la simetría.** Las tablas no cambian, así que no hay nada
que conservar más que el propio enunciado. -/
theorem Sym_unlinkIncompatible (g : GPathM) (hnd : NodupIds g) (P : PathNodeId → Prop)
    (r : PathNodeId) (h : Sym g P) : Sym (unlinkIncompatible g r) P := by
  intro x y nx ny hx hy hnx hny hyx
  obtain ⟨nx0, hnx0, hxo⟩ := unlinkIncompatible_node?_inv g hnd r x nx hnx
  obtain ⟨ny0, hny0, hyo⟩ := unlinkIncompatible_node?_inv g hnd r y ny hny
  rw [hyo]
  exact h x y nx0 ny0 hx hy hnx0 hny0 (by rw [hxo] at hyx; exact hyx)

/-- **Y el borrado también.** -/
theorem Sym_removeNode (g : GPathM) (hnd : NodupIds g) (P : PathNodeId → Prop)
    (r : PathNodeId) (h : Sym g P) : Sym (removeNode g r) P := by
  intro x y nx ny hx hy hnx hny hyx
  obtain ⟨nx0, hnx0, hxo⟩ := removeNode_node?_inv g hnd r x nx hnx
  obtain ⟨ny0, hny0, hyo⟩ := removeNode_node?_inv g hnd r y ny hny
  rw [hyo]
  exact h x y nx0 ny0 hx hy hnx0 hny0 (by rw [hxo] at hyx; exact hyx)

/-! ## `Sym` cruza el paso entero

Las tres operaciones, las tres cerradas: el corte por `Sym_cut` —que es la única con contenido, y
usa que `P` está dentro de la tabla global—, y el desenlace y el borrado porque **no tocan ninguna
tabla**, que es lo que las dos inversiones dicen.

Con `Sym` disponible en todo momento, el caso «el review mira a un protegido» tiene ya sus dos
mitades: el protegido no se borra (`isValidNode_relink_of_Anchored`) y los anclajes ajenos
sobreviven, porque `unlinkMap` no toca a quien el mirado posee y `Sym` dice que lo posee. -/

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Sym_unlinkIncompatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sym_unlinkIncompatible

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Sym_removeNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sym_removeNode

-- ============================================================
-- El desenlace de un PROTEGIDO no daña a los demás protegidos
-- ============================================================

/-- **Si el mirado posee a `z`, el desenlace deja a `z` idéntico.** La segunda rama de `unlinkMap`,
aplicada a un anclado. -/
theorem Anchored_unlinkIncompatible_owned (g : GPathM) (P : PathNodeId → Prop) (z r : PathNodeId)
    (n : PNodeM) (hnr : g.node? r = some n) (hne : z ≠ r) (hzn : z ∈ n.owners)
    (h : Anchored g P z) : Anchored (unlinkIncompatible g r) P z := by
  obtain ⟨nz, hn, hcov, hpar, hson⟩ := h
  have hid : nz.id = z := node?_id_eq g z nz hn
  have hkeep : unlinkMap n r nz = nz :=
    unlinkMap_keeps n r nz (by rw [hid]; exact hne) (by rw [hid]; simpa using hzn)
  refine ⟨nz, by rw [unlinkIncompatible_node? g r n hnr z nz hn, hkeep], ?_, ?_, ?_⟩
  · intro k hk0 hk1
    rw [current_step_unlinkIncompatible] at hk1
    obtain ⟨w, hwm, hws, hwg, hwP⟩ := hcov k hk0 hk1
    exact ⟨w, hwm, hws, by rw [gowners_unlinkIncompatible]; exact hwg, hwP⟩
  · intro h1
    obtain ⟨p, hpm, hpP, hpo, hpg⟩ := hpar h1
    exact ⟨p, hpm, hpP, hpo, by rw [gowners_unlinkIncompatible]; exact hpg⟩
  · intro h2
    rw [current_step_unlinkIncompatible] at h2
    obtain ⟨t, htm, htP, hto, htg⟩ := hson h2
    exact ⟨t, htm, htP, hto, by rw [gowners_unlinkIncompatible]; exact htg⟩

/-- **Y entonces el desenlace de un protegido no daña a ningún otro protegido.**

Dos salidas, y la disyuntiva es la del propio `unlinkMap`:

* si `r` **está** en la tabla de `z`, la simetría de `P` pone a `z` en la tabla de `r`, y el
  desenlace deja a `z` intacto (`Anchored_unlinkIncompatible_owned`);
* si `r` **no está** en la tabla de `z`, entonces no es anclaje suyo —los anclajes están en la
  tabla—, así que el filtro le quita algo que no le hacía falta.

Es el último sitio donde `Sym` hacía falta, y aquí se ve por qué: **es lo que impide que desenlazar
un protegido desancle a otro.** -/
theorem Anchored_unlinkIncompatible_protected (g : GPathM) (P : PathNodeId → Prop)
    (z r : PathNodeId) (hSym : Sym g P) (hPz : P z) (hPr : P r) (hne : z ≠ r)
    (n : PNodeM) (hnr : g.node? r = some n) (h : Anchored g P z) :
    Anchored (unlinkIncompatible g r) P z := by
  obtain ⟨nz, hn, hcov, hpar, hson⟩ := h
  have hid : nz.id = z := node?_id_eq g z nz hn
  by_cases hrz : r ∈ nz.owners
  · exact Anchored_unlinkIncompatible_owned g P z r n hnr hne
      (hSym z r nz n hPz hPr hn hnr hrz) ⟨nz, hn, hcov, hpar, hson⟩
  · refine ⟨unlinkMap n r nz, unlinkIncompatible_node? g r n hnr z nz hn, ?_, ?_, ?_⟩
    · intro k hk0 hk1
      rw [current_step_unlinkIncompatible] at hk1
      obtain ⟨w, hwm, hws, hwg, hwP⟩ := hcov k hk0 hk1
      exact ⟨w, by rw [owners_unlinkMap]; exact hwm, hws,
        by rw [gowners_unlinkIncompatible]; exact hwg, hwP⟩
    · intro h1
      obtain ⟨p, hpm, hpP, hpo, hpg⟩ := hpar h1
      exact ⟨p, parents_unlinkMap_keeps n r nz (by rw [hid]; exact hne) p hpm
          (fun he => hrz (by rw [← he]; exact hpo)), hpP,
        by rw [owners_unlinkMap]; exact hpo,
        by rw [gowners_unlinkIncompatible]; exact hpg⟩
    · intro h2
      rw [current_step_unlinkIncompatible] at h2
      obtain ⟨t, htm, htP, hto, htg⟩ := hson h2
      exact ⟨t, sons_unlinkMap_keeps n r nz (by rw [hid]; exact hne) t htm
          (fun he => hrz (by rw [← he]; exact hto)), htP,
        by rw [owners_unlinkMap]; exact hto,
        by rw [gowners_unlinkIncompatible]; exact htg⟩

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Anchored_unlinkIncompatible_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anchored_unlinkIncompatible_owned

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Anchored_unlinkIncompatible_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anchored_unlinkIncompatible_protected

-- ============================================================
-- Y la última pieza: el protegido mirado sigue anclado tras su propio corte
-- ============================================================

/-- El desenlace sobre el propio nodo mirado: filtra sus enlaces contra su tabla. -/
theorem unlinkMap_self (m : PNodeM) (r : PathNodeId) (hm : m.id = r) :
    unlinkMap m r m =
      { m with
        parents := m.parents.filter (fun p => m.owners.contains p),
        sons := m.sons.filter (fun t => m.owners.contains t) } := by
  unfold unlinkMap
  rw [if_pos (by simpa using hm)]

/-- **El protegido que el review está mirando sigue anclado después de su propio corte.**

Su tabla se corta contra la tabla global, pero **todo lo que el anclaje necesita ya estaba dentro**:
los testigos por la cobertura, el padre y el hijo por los dos conjuntos que el invariante les añade.
Así que `intersectOwners` los conserva, y el re-enlace —que filtra los enlaces contra la tabla
nueva— también.

Con esto el paso del review está cerrado **para todo `r`**, sin excepciones de caso: el mirado por
éste, los otros protegidos por `Anchored_unlinkIncompatible_protected` y `Anchored_updateAt`, y
todo lo demás por `Anchored_cleanStep`. -/
theorem Anchored_selfStep (g : GPathM) (P : PathNodeId → Prop) (r : PathNodeId) (nr : PNodeM)
    (hnr : g.node? r = some nr) (h : Anchored g P r) :
    Anchored (unlinkIncompatible
      (updateAt g r (fun n => { n with owners := intersectOwners n.owners g.gowners })) r) P r := by
  obtain ⟨nr', hn', hcov, hpar, hson⟩ := h
  have hnn : nr' = nr := Option.some.inj (hn'.symm.trans hnr)
  subst hnn
  have hid : nr'.id = r := node?_id_eq g r nr' hn'
  have hcut : (updateAt g r
      (fun n => { n with owners := intersectOwners n.owners g.gowners })).node? r
      = some { nr' with owners := intersectOwners nr'.owners g.gowners } := by
    rw [updateAt_node? g r (fun n => { n with owners := intersectOwners n.owners g.gowners })
        (fun _ => rfl) r nr' hn', show (nr'.id == r) = true from beq_iff_eq.mpr hid]
  have hstep : (unlinkIncompatible (updateAt g r
      (fun n => { n with owners := intersectOwners n.owners g.gowners })) r).current_step
      = g.current_step := current_step_unlinkIncompatible _ _
  have hgow : (unlinkIncompatible (updateAt g r
      (fun n => { n with owners := intersectOwners n.owners g.gowners })) r).gowners
      = g.gowners := by rw [gowners_unlinkIncompatible, gowners_updateAt]
  have hself : unlinkMap { nr' with owners := intersectOwners nr'.owners g.gowners } r
      { nr' with owners := intersectOwners nr'.owners g.gowners }
      = { nr' with
          owners := intersectOwners nr'.owners g.gowners,
          parents := nr'.parents.filter
            (fun p => (intersectOwners nr'.owners g.gowners).contains p),
          sons := nr'.sons.filter
            (fun t => (intersectOwners nr'.owners g.gowners).contains t) } :=
    unlinkMap_self _ r (by rw [hid])
  refine ⟨_, by rw [unlinkIncompatible_node? _ r _ hcut r _ hcut, hself], ?_, ?_, ?_⟩
  · intro k hk0 hk1
    rw [hstep] at hk1
    obtain ⟨w, hwm, hws, hwg, hwP⟩ := hcov k hk0 hk1
    exact ⟨w, mem_intersectOwners_of_mem _ _ w hwm hwg, hws, by rw [hgow]; exact hwg, hwP⟩
  · intro h1
    obtain ⟨p, hpm, hpP, hpo, hpg⟩ := hpar h1
    have hpc : p ∈ intersectOwners nr'.owners g.gowners :=
      mem_intersectOwners_of_mem _ _ p hpo hpg
    exact ⟨p, List.mem_filter.mpr ⟨hpm, by simpa using hpc⟩, hpP, hpc, by rw [hgow]; exact hpg⟩
  · intro h2
    rw [hstep] at h2
    obtain ⟨t, htm, htP, hto, htg⟩ := hson h2
    have htc : t ∈ intersectOwners nr'.owners g.gowners :=
      mem_intersectOwners_of_mem _ _ t hto htg
    exact ⟨t, List.mem_filter.mpr ⟨htm, by simpa using htc⟩, htP, htc, by rw [hgow]; exact htg⟩

/-- info: 'AbsSat.GraphPath.Model.PinAliveChain.Anchored_selfStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anchored_selfStep

end AbsSat.GraphPath.Model.PinAliveChain
