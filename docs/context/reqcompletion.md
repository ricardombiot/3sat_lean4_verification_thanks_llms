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

## 4. Lo que la ventana regala aquí — y es nuevo

*(Verificado a mano paso por paso, **no** demostrado en Lean. Lo digo porque en esta sesión ya
me he pasado de listo dos veces.)*

Los pines por encima de `lo` son gratis (`node_id_of_pin`). La pregunta es cuántos pasos **por
debajo** de `lo` siguen siendo gratis. Y la respuesta es: **`w - 1 = 2`**.

* `sel lo` es un nodo del estado **filtrado**, y no es raíz (`root_shape`, `lo > 0`), así que
  tiene padres ahí (un punto fijo de la revisión exige padres a un nodo no raíz).
* Ese padre está al paso `lo-1` en el filtrado, luego por `node_id_of_pin` su id de mapa **es**
  el pin de `lo-1`. Y por **`PMP`**, `(sel lo).parent_id = some (ese id de mapa)`.
  → **`(sel lo).parent_id` es el pin de `lo-1`.**
* Ese padre tampoco es raíz, así que tiene padre en el filtrado al paso `lo-2`, con id de mapa =
  el pin de `lo-2`. Y por **`GPMP`**, `(sel lo).gparent_id = (ese padre).parent_id`.
  → **`(sel lo).gparent_id` es el pin de `lo-2`.**
* Y ahora, en `g`: por `PMP`, el pick del descenso al paso `lo-1` es un padre de `sel lo`, luego
  su id de mapa **está forzado** a `(sel lo).parent_id`. Por `GPMP`, el pick al paso `lo-2` está
  forzado a `(sel lo).gparent_id`.

> **Los pines de `lo-1` y `lo-2` se cumplen solos.** El identificador de `sel lo` los lleva
> escritos, y `PMP`/`GPMP` obligan al descenso a respetarlos.

Con ventana 2 solo saldría gratis `lo-1`. **El residuo empieza en `lo-3`, y ensanchar la ventana
lo empuja un paso más abajo cada vez.** Es la primera vez en todo el proyecto que la ventana
compra algo *cuantificable* en esta ruta: `w-1` pasos de dirección.

### Y lo que eso no resuelve

Los pines son `reqOfCnf φ d`: los requisitos del destino, que viven en **pasos de literal**.
Pueden estar arbitrariamente por debajo de `lo`. Así que «gratis en `lo-1` y `lo-2`» ayuda cuando
los pines caen cerca y no ayuda cuando caen lejos. **No cierra (★).** Lo que hace es dar la forma
exacta del residuo:

> el descenso tiene que dirigirse por los pines que estén **tres o más pasos** por debajo del
> pick más bajo de la cadena.

## 5. Cómo seguiría

1. **Demostrar el §4** (los dos pasos gratis). Es acotado, usa solo `PMP`, `GPMP`,
   `node_id_of_pin` y `have_parents_of_isValidNode`, y deja (★) con el residuo recortado y
   dicho con precisión. Es lo que yo haría: pequeño, cerrado, y convierte una observación en
   teorema.
2. **Medir el residuo.** ¿A qué distancia de `lo` caen los pines que la máquina pone de verdad?
   Si la mayoría cae a ≤2 pasos, el §4 casi cierra (★) y merece la pena buscar el resto. Si
   cae lejos, hay que cambiar de ángulo. Es una línea en la sonda `row-degree`.
3. **No seguir por `ReqCompletion` como si fuera una reducción.** Por el §2, no lo es.

## 6. Lo que aprendí, y que habría sido mejor saber antes

`DescentFilter` dice en su propio docstring que *«el filtro es el caso que carga con todo el
peso»*. Era literal, y la equivalencia del §2 lo demuestra. Los otros tres casos de la inducción
(semilla, `up`, `join`) están probados porque son los fáciles; el cuarto no está reducido, está
**renombrado**. Conviene leer los docstrings de este repo como lo que son: precisos.
