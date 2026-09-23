# Verificación para el Autor v179: la escalera cerrada con una sola hipótesis — la completitud del review

Ricardo, soy Claude (Opus 5.5). Este informe recoge toda la sesión del 23 de septiembre, que empezó
donde lo dejó el v178 —cerrar `DescentStepOwned` por la ruta A— y terminó en un sitio distinto y
mejor: **la escalera del lector está demostrada en Lean con una única hipótesis**, y esa hipótesis
habla de un estado filtrado y su review, nada más.

Rama `spaik-window3`. `lake build AbsSat` verde (245 jobs), sin `sorry`. Todos los cierres
`[propext, Quot.sound]`. 33 commits desde `2e18a63` (el del v178).

Módulos nuevos: `TopGoodUp.lean`, `SegReview.lean`, `FullExt.lean`, `ReaderLadder.lean`.
`OwnerChainedBuild.lean` ampliado. Sondas nuevas en `Probes/RowDegree.lean` (quince modos, §6).

---

## 0. Dónde estamos, en una línea

```lean
theorem readerVerdictW_iff_of_filterReviewComplete (h : FilterReviewComplete) (φ : Cnf)
    (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ
```

`FilterReviewComplete` dice: **tras un filtro del lector, un tramo cuyos miembros están en la tabla
global y sobrevive al review agresivo ya se extendía, antes del review, a una cadena completa que
sobrevive al review (`ChainSound`).** Todo lo demás está demostrado.

---

## 1. Lo primero: `DescentStepOwned` era falso tal como estaba escrito

El enunciado del v178 no pedía que `sel` fuera cadena por encima de `k`. Con `sel := fun _ => a`
cumple las hipótesis y la conclusión pide un padre de `a` en el paso 0: **imposible en cuanto hay un
nodo en el paso 2** (`not_descentStepAny`). La escalera del v178 colgaba de algo falso. Lo corregí
añadiendo la cadena (que la recursión ya aportaba), y después, a petición tuya, lo reescribí **solo
con owners**: el lector no mira padres, y el enlace de padre lo pone `owners_below_iff_parents`.

## 2. Lo que la sesión fue descubriendo

Lo cuento en orden porque cada paso cambió el siguiente.

1. **El paso `k` no elige id de mapa: lo fija el hijo** (`below_same_window`). La entrada de `k` tiene
   que estar en la tabla de `sel (k+1)`, y ahí todas llevan el mismo id y el mismo `parent_id`. El
   caso «dos ids de mapa» que la ruta A atacaba **no existe**; lo que varía es la ventana (el id de
   `k-2`). Cerrados: `k ≤ 1` (`descentStep_of_low`) y `k-2` ya pinchado (`descentStep_of_pinned`).
2. **Tu frase, escrita**: «el lector no elige, cualquier opción tiene un camino» →
   `AnyOptionStep` sobre la tabla colectiva de lo elegido. Medida al 100 % (`anyoption`: 69.197
   pasos, 225.471 opciones, ninguna falla).
3. **La coherencia del review (`cohP`/`cohS`) es cota superior**: leída al revés da un recubrimiento
   (`mem_parent_table`, `mem_son_table`), que cierra el caso de un solo padre pero no el general.
4. **Invariantes no locales, medidos antes de apostar**:
   * «toda familia que se posee por pares comparte entrada» — **falso** (56/88.986 ternas);
   * «toda cadena **desde la cima** comparte entrada por debajo» — 0 fallos en 133.623 (`TopGood`);
   * el `up` la conserva **por construcción** (`rowOwners` es la unión de las tablas de los padres) —
     demostrado (`topGood_addNode`), sin hipótesis del review.
5. **El anfitrión estorbaba**: con él, `cleanInvalid` nodo a nodo rompía estados intermedios. Sin
   él, y con tramos en los dos sentidos (`SegGood`), el descenso **desde `a`** (bajando y subiendo)
   da `OwnerChained` (`ownerChained_of_segGood`).
6. **Las pasadas de padres, de hijos y el barrido**, demostradas nodo a nodo / par a par para
   `SegGood` —pero con una hipótesis de simetría local que **falla justo donde el barrido dispara**
   (19 de 24 pares, `extfire`). Tuve que retirarla.
7. **El invariante único, `FullExtG`**: *todo tramo dentro de la tabla global se extiende a una
   cadena completa dentro de ella*. Da la escalera directamente (el tramo `[q]`), el `up` lo conserva
   sin simetría, y —lo decisivo— **no hace falta llevarlo operación por operación por el review**.

## 3. La dicotomía que lo cambió todo

Medida tras cada filtro, en la construcción y en los pines del lector (`filterkill`):

| corpus | tramos dentro de la global tras el filtro | se extienden → sobreviven | no se extienden → sobreviven |
|---|---|---|---|
| `dos_de_tres.cnf` (184 estados) | 3.800 | 1.904 → **1.904** | 1.896 → **0** |
| 12 aleatorias, semilla 1 (6.124 estados) | 423.160 | 200.133 → **200.133** | 223.027 → **0** |

**El review mata exactamente los tramos que el filtro deja sin extensión, y conserva todos los
demás.** Sin una sola excepción, y sin agotar nunca el presupuesto de búsqueda.

Una dirección está demostrada: **si se extiende, sobrevive** (`seg_survives_of_extends`) — una
cadena completa dentro de la global es `ChainSound` (`chainSound_of_fullChain`) y
`ChainSound_reviewAgg`, que ya estaba en el repositorio, la lleva entera al otro lado.

La otra es la hipótesis: **si sobrevive, se extendía.**

## 4. La escalera

```
FilterReviewComplete                              ← abierto (medido sin excepción)
   → FullExtG del estado revisado                  fullExtG_reviewAgg_cs
   → OwnerChained en todo estado que el lector lee ownerChained_of_filterReviewComplete
   → PinAlive                                      pinAlive_of_filterReviewComplete
   → readerVerdictW φ = true ↔ Satisfiable φ        readerVerdictW_iff_of_filterReviewComplete
```

Nótese lo que **no** pide: ni la inducción sobre la máquina, ni el `up`, ni el `doJoin`, ni ninguna
propiedad de forma de los estados intermedios del review. Todo lo que el lector lee sale de un
estado revisado, y `FullExtG` de un revisado sale solo de la completitud de su review.

## 5. Lo que se midió falso (y ahorra tiempo)

| hipótesis | medida | lección |
|---|---|---|
| `DescentStepOwned` (redacción v178) | **demostrado falso** | pedía de más: faltaba la cadena |
| familia poseída por pares ⇒ entrada común | 56/88.986 ternas | la estructura de cadena es imprescindible |
| cadena con extremo alto cualquiera, con anfitrión | 232/467.024 | el anfitrión por debajo estorba |
| `TopGoodNH` nodo a nodo en `cleanInvalid` | 204/73.757 estados (semilla 1) | `cleanInvalid` solo al final de la pasada |
| simetría local «para toda» en barridos que disparan | 19/24 | vale la versión «existe» |
| `cleanInvalid` pasada a pasada con `FullExtG` | 80/453.158 | la completitud es del review entero |

En los seis el patrón es el mismo del v178: **yo pedía de más**, no fallaba la máquina.

Dos datos sobre la máquina que no esperaba: **el barrido agresivo no dispara en la construcción**
sobre estos corpus (0 de 6.082 envíos; 2 de 42 pines del lector), y los tramos que `cleanInvalid`
rompe a medias **mueren siempre** antes de acabar la pasada (13.592 de 13.592).

## 6. Sondas de esta sesión

`anyoption`, `cliqueshare`, `chainshare`, `upextend`, `topgoodops`, `joinmix`, `reviewops`,
`reviewnodes`, `nohostops`/`nohostnodes`, `segments`, `segops`/`segnodes`, `cleandiag`, `midinv`,
`localsym`, `sweeppairs`, `sweepcheck`, `extfire`, `fullext`, `cleanobl`, `filterkill`,
`filterkillcs`. Todas en `lean_project/Probes/RowDegree.lean` (`lake exe row-degree <modo>
file|random`).

## 7. Lo que falta

1. **Confirmar la forma exacta de la hipótesis.** `filterkill` buscó extensiones enlazadas, poseídas
   por pares y dentro de la global; `ChainSound` pide además que cada miembro se posea, que el
   enlace se vea desde los dos lados y que la raíz esté solo en el paso 0. `filterkillcs` lo mide:
   en `dos_de_tres.cnf` es idéntico (1.904 / 1.904, 0 tramos que sobrevivan sin extensión
   `ChainSound`); la semilla 1 está corriendo al escribir esto.
2. **Demostrar `FilterReviewComplete`.** Es la única pieza abierta. Es una frase de *completitud*
   del review —el review solo quita, así que lo que sobrevive tiene que haber sobrevivido *por*
   algo—, no de conservación. Lo que sabemos de ella:
   * no se puede probar pasada a pasada (80 fallos intermedios en `cleanInvalid`);
   * es una propiedad del **punto fijo** del review completo tras el filtro;
   * tiene la misma forma que el paso de cláusula que `ownerChained_filterAllAgg_of_reqSatisfying`
     cerró con el argumento de la cima: allí los requisitos de un nodo de cláusula los cumple
     cualquier camino que llegue a él. Mi primera apuesta es mirar si el mismo argumento sirve.
3. **Lo que quedó escrito pero la escalera ya no usa**: `TopGood`, `SegGood`, las pasadas y el
   barrido para `SegGood` (`SegReview.lean`), el `up` y el `doJoin` (con `NoMix`, sin medir para
   tramos). Siguen compilando y pueden servir si hace falta la inducción sobre la máquina.

## 8. Una frase sobre el tamaño de lo que queda

El v178 dejaba un enunciado local que resultó falso. El v179 deja uno que **no es local sino del
review completo**, está medido sin excepción en 225.000 casos, y tiene demostrada su dirección
fácil. Lo que ha cambiado no es el porcentaje: es que la pregunta abierta ya no es sobre el lector
ni sobre la construcción, sino sobre **una sola operación de la máquina, el review, y su punto
fijo**: *¿mata el review todo lo que el filtro deja sin salida?*
