-- lean_project/AbsSat/GraphPath/Model/SupportedRun.lean
import AbsSat.GraphPath.Model.RunSteps
import AbsSat.GraphPath.Model.Descent

/-!
# Del invariante de entradas al de nodos, y qué queda exactamente

La sonda `row-degree sup-all` mide que **todo nodo de todo estado está en una cadena**
(`Descent.SupportedS`): 42.652 nodos, cero fantasmas. Y `row-degree soundat` mide que **toda
entrada de toda tabla es realizable** (`TablesSound`, y en particular `SoundAt (LitStep φ)`):
825.612 entradas, cero fantasmas.

Este módulo conecta las dos y deja escrito el enunciado exacto que falta.

* **`supportedS_of_soundAt`** — el invariante de *entradas* implica el de *nodos*, y la prueba es de
  dos líneas: todo nodo válido tiene una entrada en el paso 0, el paso 0 es un `LitStep`, y
  `SoundAt` entrega la cadena. Así que la medida de nodos es consecuencia de la de entradas, no un
  hecho aparte.
* **`supportedS_pin_of_soundAt`** — y con un pin en un paso literal, `RunSteps.realizes_pin` da
  `SupportedS` del estado pinchado **sin hipótesis nueva**: el filtro rompe `SupportedS` (medido:
  una cuarta parte de los nodos) y la revisión la restablece entera (medido: 0 de 10.572 envíos
  falla), y esto es la mitad de esa frase que ya está demostrada.

Lo que queda, y es lo único: **`RunSteps.PinPairSoundAt`**. Dice que tras un pin `r` en un paso
literal, para todo nodo `x` que sobrevive y toda entrada `q` suya hacia un paso literal **distinto
del pinchado**, hay una cadena del estado pinchado por `x` y por `q`. El paso pinchado ya está
(`pinStep_of_pairs`), y los requisitos débiles no hacen nada (v144), así que de ahí sale
`FilterSoundAt` y con él el invariante de toda la corrida.

Es una frase sobre **tres** cosas —el nodo, el pin y la segunda entrada—, que es el lado de la
frontera donde esta sesión vio caerse cinco hipótesis. Pero a diferencia de aquellas, esta no
cuantifica sobre tablas arbitrarias: `r` es un pin y `q` apunta a un paso literal, donde el mapa
solo tiene dos nodos por paso y los enlaza cruzados. Medirla es el siguiente paso, y el enunciado
de arriba es exactamente lo que hay que medir.
-/

namespace AbsSat.GraphPath.Model.SupportedRun

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep)
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.Descent (SupportedS)

variable (φ : Cnf)

/-- **El invariante de entradas implica el de nodos.** Todo nodo válido tiene una entrada en el
paso 0, el paso 0 es un `LitStep`, y `SoundAt` entrega la cadena que pasa por los dos. -/
theorem supportedS_of_soundAt (g : GPathM) (a : AdjacentOwners.Adj g) (hpos : 0 < g.current_step)
    (ht : SoundAt (LitStep φ) g) : SupportedS g := by
  intro x n hx
  have hmem := List.mem_of_find?_eq_some hx
  have hid : n.id = x := node?_id_eq g x n hx
  have hx0 : 0 ≤ x.id.step := by have := a.rc.snn n hmem; rwa [hid] at this
  have hxs : x.id.step < g.current_step := by have := a.rc.below n hmem; rwa [hid] at this
  -- una entrada en el paso 0
  have hent := List.all_eq_true.mp
    (owners_ok_of_isValidNode g n (a.ctx.nodeval x n hx)) 0
    (mem_intRange (Int.le_refl 0) (by omega))
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨q, hq, hqs⟩ := hent
  obtain ⟨sel, hsc, hsx, _⟩ :=
    ht x n hx hx0 hxs q (by omega) (by omega) (Or.inr hqs) hq
  exact ⟨sel, hsc, hsx⟩

/-- **Y con un pin en un paso literal, el estado pinchado también.**

Esta es la mitad demostrada del paso del filtro: el filtro deja nodos sin cadena —medido, una
cuarta parte— y la revisión los quita todos. `RunSteps.realizes_pin` lo dice para el pin, sin
hipótesis mas alla del invariante de entradas. -/
theorem supportedS_pin_of_soundAt (g : GPathM) (hR : ReadableAgg g) (ht : SoundAt (LitStep φ) g)
    (r : NodeId) (hr : LitStep φ r.step) (hr0 : 0 ≤ r.step)
    (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs : r.step < (filterAllAgg g [r]).current_step)
    (hb : ∀ x n, (filterAllAgg g [r]).node? x = some n →
      0 ≤ x.id.step ∧ x.id.step < (filterAllAgg g [r]).current_step) :
    SupportedS (filterAllAgg g [r]) := by
  intro x n hx
  obtain ⟨hx0, hx1⟩ := hb x n hx
  obtain ⟨w, _, _, sel, hsc, hsx, _⟩ :=
    RunSteps.realizes_pin φ g hR ht r hr hr0 hvr hrs x n hx hx0 hx1
  exact ⟨sel, hsc, hsx⟩


-- ============================================================
-- `PinPairSoundAt`, reducido a una frase sobre UN estado sin pinchar
-- ============================================================

/-- **La terna, dicha antes del pin: una cadena se puede reencaminar.**

Si hay cadena por `x` y por `q`, y el pin `r` deja el estado válido, entonces hay una cadena por
`x`, por `q` **y por `r`**.

Es lo único que `PinPairSoundAt` pide de más, y esta forma tiene tres ventajas sobre aquella: habla
de **un solo estado**, el de antes de pinchar —no del pinchado, que es el resultado de un punto
fijo—; no menciona el filtro más que como condición; y **solo lo pide de nodos que sobreviven al
pin**.

Lo último no es cosmético. `ChainMerge` es falso (v145): de «hay cadena por `x` y `q`» y «hay cadena
por `x` y `r`» **no** se sigue «hay cadena por los tres», y el contraejemplo es de una línea —una
fórmula donde `v1` puede ser cierta, `v2` puede ser cierta, y no a la vez—. Así que toda versión de
esta frase que no use la supervivencia al review es falsa. La hipótesis de supervivencia es la
única información que queda por explotar, y por eso está aquí. -/
def TriplePin : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → SoundAt (LitStep φ) g →
    ∀ r : NodeId, LitStep φ r.step → isValid (filterAllAgg g [r]) = true →
      ∀ x q : PathNodeId, Realizes g x q → q.id.step ≠ r.step →
        ((filterAllAgg g [r]).node? x).isSome = true →
        ((filterAllAgg g [r]).node? q).isSome = true →
        ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel q.id.step = q ∧ (sel r.step).id = r

/-- **Y basta.** `SoundAt` da la cadena por `x` y `q` antes del pin, la terna la reencamina por `r`,
y `ChainSound_filterAllAgg` la deja intacta a través del pin y de la revisión.

Así que **toda la obligación abierta de esta ruta cabe en `TriplePin`**: con ella salen
`PinPairSoundAt`, `PinStepSoundAt` (`pinStep_of_pairs`), `SendPinSoundAt`, `FilterSoundAt`, el
invariante de la corrida, `SupportedS`, `Inhabited`, que el lector no se atasca, y el veredicto. -/
theorem pinPair_of_triplePin (h : TriplePin φ) : RunSteps.PinPairSoundAt φ := by
  intro g hR hv ht r hr hvr x n hx hx0 hx1 q hq0 hq1 hL hqr hqn
  have hpr := pruned_filterAllAgg g [r]
  have hcs := hpr.step_eq
  have rcg := RCtx_of_readableAgg g hR
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  have hxq : Realizes g x q :=
    ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) q hq0 (by rw [← hcs]; exact hq1) hL (hown q hqn)
  -- `x` y `q` sobreviven al pin: `x` por hipótesis, `q` por ser owner suyo en el estado pinchado
  have hRr := ReadableAgg_filterAllAgg g hR [r]
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
  have hqg : q ∈ (filterAllAgg g [r]).gowners := ctxR.ownGow x n hx q hqn hq0 hq1
  have hqnode : ((filterAllAgg g [r]).node? q).isSome = true :=
    (GownersNodes.hasNode_iff _ q).mp ((RCtx_of_readableAgg _ hRr).gn q hqg)
  obtain ⟨sel, hsc, hsx, hsq, hsr⟩ :=
    h g hR hv ht r hr hvr x q hxq hqr (by rw [hx]; rfl) hqnode
  exact ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => by
    rw [List.mem_singleton.mp hreq]; exact hsr), hsx, hsq⟩


-- ============================================================
-- Una cadena respeta los requisitos duros del mapa
-- ============================================================

/-- **Cuando el pin es lo que el nodo ya requiere, la cadena pasa por él sin reencaminar.**

`ReqFiltered` dice que todo owner de un nodo en el paso de uno de sus requisitos **es** ese
requisito. Y los picks de una cadena son owners unos de otros. Así que si `q` está en la cadena y el
pin `r` es un requisito de `q`, el pick de la cadena en el paso de `r` **es** `r`.

Es el primer trozo de `TriplePin` que sale sin hipótesis: el caso en que el mapa ya forzaba la
respuesta. En el bloque de literales eso cubre la pareja `2v ↔ 2v+1`, que es donde `reqOfCnf` enlaza
cruzado — un nodo del paso impar requiere el del par con el índice contrario. -/
theorem chain_through_req (g : GPathM)
    (hrf : ReqFiltered (reqOfCnf φ) g)
    (sel : Int → PathNodeId) (hsc : ChainSound g sel)
    (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq) (hqsel : sel q.id.step = q)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < g.current_step)
    (r : NodeId) (hreq : r ∈ reqOfCnf φ q.id) (hr0 : 0 ≤ r.step) (hr1 : r.step < g.current_step)
    (hne : r.step ≠ q.id.step) :
    (sel r.step).id = r := by
  -- el pick del paso de `r` es owner de `q`
  have hmem := hsc.chain.2.1 r.step q.id.step hr0 hq0 hr1 hq1 hne
  rw [hqsel] at hmem
  have hmem' := List.mem_filter.mp hmem
  have hown : sel r.step ∈ nq.owners := by
    simpa only [ownersOf, hq] using hmem'.1
  have hstep : (sel r.step).id.step = r.step := eq_of_beq hmem'.2
  -- y `ReqFiltered` lo identifica con el requisito
  exact hrf nq (List.mem_of_find?_eq_some hq) r (by
    rw [node?_id_eq g q nq hq]; exact hreq) (sel r.step) hown hstep


/-- **`TriplePin` cerrado cuando el pin es requisito de alguno de los dos.**

Aplicando `chain_through_req` a `x` o a `q`, según cuál de los dos lo requiera. No hace falta
reencaminar nada: el mapa ya había forzado el pick.

Cubre, en la corrida: todo nodo del paso `2v+1` cuyo requisito sea exactamente el pin —la pareja
cruzada del bloque de literales— y todo nodo de cláusula que tenga al pin entre sus tres literales.

Lo que queda fuera es el caso en que **ni `x` ni `q` requieren `r`**: dos variables que el mapa no
enlaza directamente. Ahí la cadena puede estar usando el otro valor y hay que reencaminarla — y
empalmar dos cadenas no vale, porque `ChainMerge` es falso (v145). -/
theorem triplePin_of_req (g : GPathM) (hrf : ReqFiltered (reqOfCnf φ) g)
    (r : NodeId) (hr0 : 0 ≤ r.step) (hr1 : r.step < g.current_step)
    (x q : PathNodeId) (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < g.current_step)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < g.current_step)
    (hxq : Realizes g x q)
    (hreq : (r ∈ reqOfCnf φ x.id ∧ r.step ≠ x.id.step) ∨
            (r ∈ reqOfCnf φ q.id ∧ r.step ≠ q.id.step)) :
    ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel q.id.step = q ∧ (sel r.step).id = r := by
  obtain ⟨sel, hsc, hsx, hsq⟩ := hxq
  refine ⟨sel, hsc, hsx, hsq, ?_⟩
  rcases hreq with ⟨hreq, hne⟩ | ⟨hreq, hne⟩
  · obtain ⟨hsome, _⟩ := hsc.chain.1.1 x.id.step hx0 hx1
    rw [hsx] at hsome
    obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp hsome
    exact chain_through_req φ g hrf sel hsc x nx hnx hsx hx0 hx1 r hreq hr0 hr1 hne
  · obtain ⟨hsome, _⟩ := hsc.chain.1.1 q.id.step hq0 hq1
    rw [hsq] at hsome
    obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp hsome
    exact chain_through_req φ g hrf sel hsc q nq hnq hsq hq0 hq1 r hreq hr0 hr1 hne


/-- **La supervivencia da un testigo COMPARTIDO en el paso del pin.**

Y esto es lo que `ChainMerge` no tenía. Si `x` y `q` sobreviven al pin y `q` sigue en la tabla de
`x`, la criba del estado pinchado obliga a que compartan un owner en **todos** los pasos
(`AggOk`), y en el paso del pin ese owner común lleva el pin (`pin_id`).

Así que la frase abierta ya no es «tres nodos compatibles dos a dos»: es «`x`, `q` y **un mismo
tercero** `z` que los dos poseen y que es el valor pinchado». Un testigo, no dos. Es la forma más
débil a la que ha bajado, y la que de verdad usa que el review dejó vivos a los dos. -/
theorem shared_pin_witness (g : GPathM) (hR : ReadableAgg g)
    (r : NodeId) (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs0 : 0 ≤ r.step) (hrs : r.step < (filterAllAgg g [r]).current_step)
    (hpms : Sons.PMS (filterAllAgg g [r])) (hsn : Sons.SN (filterAllAgg g [r]))
    (x q : PathNodeId) (n mq : PNodeM)
    (hx : (filterAllAgg g [r]).node? x = some n) (hq : (filterAllAgg g [r]).node? q = some mq)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < (filterAllAgg g [r]).current_step)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < (filterAllAgg g [r]).current_step)
    (hqn : q ∈ n.owners) :
    ∃ z, z.id = r ∧ z ∈ n.owners ∧ z ∈ mq.owners := by
  have a := AdjacentOwners.adj_of_readable _ (ReadableAgg_filterAllAgg g hR [r]) hvr hpms hsn
  have hok := AggFixpoint.aggOk_reviewAgg _ hvr
  obtain ⟨z, hzx, hzq, hzs⟩ :=
    ParentWitness.shared_owner a hok hx hq hx0 hx1 hq0 hq1 hqn r.step hrs0 hrs
  have hzg : z ∈ (filterAllAgg g [r]).gowners :=
    a.ctx.ownGow x n hx z hzx (by rw [hzs]; exact hrs0) (by rw [hzs]; exact hrs)
  exact ⟨z, ReaderComplete.pin_id g r z hzg hzs, hzx, hzq⟩

/-- info: 'AbsSat.GraphPath.Model.SupportedRun.shared_pin_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shared_pin_witness

/-- info: 'AbsSat.GraphPath.Model.SupportedRun.triplePin_of_req' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms triplePin_of_req

/-- info: 'AbsSat.GraphPath.Model.SupportedRun.chain_through_req' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_through_req

/-- info: 'AbsSat.GraphPath.Model.SupportedRun.pinPair_of_triplePin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinPair_of_triplePin

/-- info: 'AbsSat.GraphPath.Model.SupportedRun.supportedS_of_soundAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supportedS_of_soundAt

/-- info: 'AbsSat.GraphPath.Model.SupportedRun.supportedS_pin_of_soundAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supportedS_pin_of_soundAt

end AbsSat.GraphPath.Model.SupportedRun
