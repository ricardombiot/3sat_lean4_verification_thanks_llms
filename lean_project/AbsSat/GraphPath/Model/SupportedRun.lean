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

Es lo único que `PinPairSoundAt` pide de más, y esta forma tiene dos ventajas sobre aquella: habla
de **un solo estado**, el de antes de pinchar —no del pinchado, que es el resultado de un punto
fijo— y no menciona el filtro más que como condición. Medirla es mirar tres nodos de un grafo. -/
def TriplePin : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → SoundAt (LitStep φ) g →
    ∀ r : NodeId, LitStep φ r.step → isValid (filterAllAgg g [r]) = true →
      ∀ x q : PathNodeId, Realizes g x q → q.id.step ≠ r.step →
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
  obtain ⟨sel, hsc, hsx, hsq, hsr⟩ := h g hR hv ht r hr hvr x q hxq hqr
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
