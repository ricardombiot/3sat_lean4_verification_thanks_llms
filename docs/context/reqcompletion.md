# `ReqCompletion`, explorado

> Resultado principal, y es negativo: **`ReqCompletion` no es una reducción, es el objetivo
> reescrito.** Lo he demostrado, no conjeturado. Lo que sale de ahí, y sí es nuevo, está en §3.

---

## 1. El enunciado

```lean
def ReqCompletion (g : GPathM) (reqs : List NodeId) : Prop :=
  ∀ sel lo, 0 < lo → lo ≤ (filterAllAgg g reqs).current_step - 1 →
    SoundFrom (filterAllAgg g reqs) sel lo →
    ∃ sel', ChainSound g sel' ∧
      (∀ k, lo ≤ k → k < g.current_step → sel' k = sel k) ∧
      (∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel' req.step).id = req)
```

*Toda cadena parcial del estado filtrado se completa, **dentro del estado sin filtrar**, a una
cadena entera que cumple los pines.*

Tras la fase 1 (`DescentRun`) es **la única hipótesis del veredicto** de la ruta del descenso:
`sat_of_reqCompletion` no necesita ni `JoinCoveredF` ni nada más.

## 2. Y es el objetivo, reescrito

`DescentFilter.noDeadEnd_filterAllAgg_of_completion` es la ida:

> `ReqCompletion g reqs` ⟹ `NoDeadEnd (filterAllAgg g reqs)`

He demostrado la vuelta — `DescentRun.reqCompletion_of_noDeadEnd`, sin axiomas:

> `NoDeadEnd (filterAllAgg g reqs)` ⟹ `ReqCompletion g reqs`

y sale en veinte líneas, porque **descender dentro del estado filtrado lo da todo gratis**:

* la cadena que sale es cadena de `g` por `SubsetSemantics.ChainSound_of_pruned`;
* y **cumple todos los pines sin pedir nada**, porque en el estado filtrado *todo* nodo de un
  paso pinchado ya lleva el nodo de mapa pinchado (`PairChain.node_id_of_pin`).

**Así que las dos son la misma frase.** El caso del filtro de la inducción no reduce nada: mueve
el cuantificador de *«el estado filtrado no tiene callejones»* a *«las cadenas del filtrado se
completan en el no filtrado»*. Útil como reformulación, nulo como reducción.

> Esto corrige mi plan de la fase 2 en [descenso_por_induccion.md](descenso_por_induccion.md):
> «reducir `ReqCompletion` usando `NoDeadEnd g` como hipótesis inductiva» estaba atacando una
> tautología por un lado. El lado que sí tiene contenido es el otro, y es el §3.

## 3. Donde está el contenido de verdad

El paso que la inducción necesita **no** es `ReqCompletion`; es

> **(★)** `NoDeadEnd g` ⟹ `NoDeadEnd (filterAllAgg g reqs)`
>
> *la revisión no crea callejones sin salida.*

Con `ReqCompletion` ⟺ `NoDeadEnd (filtered)`, (★) es exactamente lo que falta. Y su forma
concreta es esta: `NoDeadEnd g` da una completación `sel'` **dentro de `g`**; lo único que puede
fallar es que `sel'` no pase por los pines por debajo de `lo`. Es decir:

> **(★) ⟸ `NoDeadEnd g` + «el descenso puede dirigirse por los pines por debajo de `lo`».**

## 4. Lo que la ventana regala aquí — demostrado

**`DescentRun.pins_below_free`**, sin axiomas, bajo `#guard_msgs`. Con sus dos lemas:

```lean
parent_id_of_pin   -- (sel lo).parent_id  es el pin de lo-1
gparent_id_of_pin  -- (sel lo).gparent_id es el pin de lo-2
pins_below_free    -- y el descenso no puede fallarlos
```

La cadena del argumento, ya en Lean:

* `sel lo` es nodo del estado **filtrado** y no es raíz (`Parents.NotRoot`), así que tiene padres
  ahí (`SelfOwn.have_parents_of_isValidNode` sobre `isValidNode`);
* ese padre está al paso `lo-1`, luego `PairChain.node_id_of_pin` fuerza su id de mapa al pin, y
  **`PMP`** lo copia en `(sel lo).parent_id`;
* el padre tampoco es raíz, así que el mismo paso una vez más da el pin de `lo-2`, y **`GPMP`** lo
  copia en `(sel lo).gparent_id`;
* y en `g`, `PMP` y `GPMP` fuerzan los picks del descenso a esos ids de mapa.

> Con ventana 2 solo saldría gratis `lo-1`. **El tercer componente compra el segundo paso.**

## 4bis. Y cuánto vale eso, medido

`lake exe row-degree random 20 4 11` — 138.100 pares (pin, posición del pick más bajo):

| distancia del pin al pick más bajo | | |
|---|---|---|
| por encima o igual — gratis por `node_id_of_pin` | 30.994 | 22,4 % |
| a **1** paso — gratis ya con ventana 2 | 6.502 | 4,7 % |
| a **2** pasos — gratis **solo** con ventana 3 | 6.300 | 4,5 % |
| a **≥3** pasos — **el residuo** | 94.304 | **68,2 %** (máx. 48) |

Y la métrica que de verdad decide, porque la completación necesita **todos** los pines a la vez:

| de 46.736 posiciones posibles del pick más bajo | | |
|---|---|---|
| todos sus pines gratis (arriba, a 1 o a 2) | 8.754 | **18,7 %** |
| queda algún pin a ≥3 pasos | 37.982 | **81,2 %** |

**Así que no: el §4 no casi cierra (★).** Es un teorema real y corta una rebanada real, pero la
rebanada es el 18,7 % de las posiciones. Yo esperaba más; los pines caen lejos.

**Y esto zanja otra cosa.** Cada componente extra del identificador compra **un** paso más, y el
histograma decae despacio (4,7 % → 4,5 % → …) con cola hasta 48. Para cubrir la cola haría falta
ventana 49. **Ensanchar la ventana no es el camino aquí** — es la segunda vez en esta sesión que
los datos dicen lo mismo (la primera fue `parents_differ_below`, §5.7 del contexto).

## 5. Cómo seguiría, revisado tras medir

Lo que escribí antes de medir era: *«demostrar el §4 y luego medir; si la mayoría de los pines
cae a ≤2 pasos, casi cierra»*. Medido: **cae lejos**, y el §4 cubre el 18,7 %. Así que:

1. **No insistir en la dirección «acercar los pines».** Ni ensanchando la ventana (cola 48) ni
   afinando `pins_below_free` (ya es óptimo: `w-1` pasos es todo lo que el identificador sabe).
2. **Cambiar lo que se dirige.** El residuo es *«el descenso debe pasar por un pin que está muy
   por debajo»*. Dos formas de atacarlo que no pasan por el identificador:
   * **descender en el estado filtrado en vez de en `g`** — ahí los pines son gratis a cualquier
     distancia (`node_id_of_pin`), y es justo lo que hace `reqCompletion_of_noDeadEnd`. El
     problema se convierte entonces en `NoDeadEnd (filtrado)` sin pasar por `g`, o sea el
     objetivo otra vez; pero **sin** la obligación de los pines, que es lo que este documento
     pensaba atacar. El muro vuelve a ser el descenso puro.
   * **`ChainSound_filterAllAgg` al revés**: para cadenas **completas** el filtro no pierde nada.
     Lo que falta es la versión parcial. Es el mismo enunciado que (★) y hay que decidir si se
     ataca ahí o en el descenso puro.
3. **El corolario útil de todo esto**, y es el que yo me llevaría: la obligación de los pines **no
   es el muro**. Se puede quitar de encima descendiendo en el filtrado. El muro es, otra vez, el
   descenso: `NoDeadEnd`. Todo lo que este documento explora acaba devolviéndonos ahí.

## 6. Lo que aprendí, y que habría sido mejor saber antes

`DescentFilter` dice en su propio docstring que *«el filtro es el caso que carga con todo el
peso»*. Era literal, y la equivalencia del §2 lo demuestra. Los otros tres casos de la inducción
(semilla, `up`, `join`) están probados porque son los fáciles; el cuarto no está reducido, está
**renombrado**. Conviene leer los docstrings de este repo como lo que son: precisos.
