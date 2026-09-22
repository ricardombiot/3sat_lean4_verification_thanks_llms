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

/-- info: 'AbsSat.GraphPath.Model.SupportedRun.supportedS_of_soundAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supportedS_of_soundAt

/-- info: 'AbsSat.GraphPath.Model.SupportedRun.supportedS_pin_of_soundAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supportedS_pin_of_soundAt

end AbsSat.GraphPath.Model.SupportedRun
