# Verificación para el Autor v186: la regla de parejas, en la máquina y en la prueba

Ricardo, soy Claude (Opus 5.5). Este informe sigue al v185. Allí propuse adelantar la rama
«inconsistente» del filtro agresivo a justo después de la limpieza, con la idea de convertir la última
hipótesis del lector —dinámica, sobre una vuelta entera— en una afirmación sobre un solo estado. Aquí
se cuenta qué ha pasado con esa regla: en Julia, en el modelo Lean y en las mediciones.

En pocas palabras: **la regla no cambia nada de lo que la máquina decide, es correcta (demostrado), se
lleva todo el trabajo que hacía la rama inconsistente del agresivo, convierte `AggInactive` en un
teorema, y deja el lector a una afirmación de tipo Helly sobre un único estado, medida sin fallos.**

Rama `pair-mode` (sale de `spaik`, que ya incluye `review-symmetric`). Plan:
`docs/plans/pair_mode.md`. `lake build AbsSat` verde (271 jobs), sin `sorry` nuevos, los teoremas con
los axiomas de siempre (`propext`, `Quot.sound`).

---

## 0. Dónde estamos, en una línea

```lean
theorem readerVerdictW_iff_of_pairHelly (hStart : …)
    (hPin : … → PairHelly (cleanPair X) ∧ CleanRest X ∧ LaterValid X)
    (φ : Cnf) (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ

def PairHelly (C : GPathM) : Prop := isValid C = true → PairFixed C → SegGood C
```

con `X` el estado pinchado de cada pin del lector. **`PairHelly`**: en un estado donde la regla ya no
quita nada, todo tramo tiene entrada común en cada paso. Las otras dos son de forma (§4), y las tres
están medidas sin fallos (§5).

## 1. La regla

> Tras la limpieza, si dos nodos vivos se poseen y en algún paso en el que los dos tienen entradas no
> comparten ninguna, la posesión se deshace en las dos direcciones. Con las tablas tal como están se
> marcan todas las parejas malas, se quitan a la vez, se purga, y se repite hasta que no cambie nada.

Es la rama «inconsistente» del filtro agresivo, adelantada al momento en que el pin deja los tramos sin
entrada común. En dos fases (marcar contra una instantánea, luego quitar) para que no dependa del
orden de los nodos —en Julia el de un `Set` es el del hash— y para que el modelo Lean sea un solo `map`.

## 2. Julia (`julia/improves`, fase A)

`src/graph_path/graph_path_filter_pair.jl`, incluido en `graph_path.jl`; interruptor
`PAIR_MODE` (`:off` por defecto hasta decidir). El test de pareja, `shares_every_step`, en
`PathDocumentOwners`: simétrico, y igual a `intersect!` + `is_valid` en las 2.809 parejas de una
instancia real (A1).

* **A3** (`runtests`, testset `PairMode`, 17 tests): en 126 estados pinchados la regla actúa en 77;
  tras ella 0 parejas malas y 0 asimétricas; con el review completo, **mismos veredictos y mismos
  estados finales** que sin la regla.
* **A0 + A4** (`test_3sat/compare_pair.jl`, 80 instancias):

| | sin regla | con regla |
|---|---|---|
| veredictos / aciertos contra el exhaustivo | 80 / 80 | 80 / 80 |
| estados finales, lector sin retroceso, soluciones del lector exponencial | — | **80 iguales**, checker sin fallos |
| vueltas del review | 23.904 | 23.904 |
| rama «inconsistente» del agresivo, máquina / lectores | 19.238 / 180 | **0 / 0** |
| tiempo | 524 s | 554 s (+6 %) |

La regla hace, antes, exactamente lo que el agresivo hacía después.

## 3. El modelo Lean (fase B)

`reviewPass = reviewSons ∘ reviewParents ∘ cleanPair`, con `cleanPair` = la limpieza en dos fases y
después la regla hasta su punto fijo (`pairSweep`, `pairFuel`).

* **La regla no pierde soluciones** (`ChainSound_pairSweep`, `ChainSound_cleanPair`): dos nodos de
  una cadena sana comparten entrada en cada paso —el nodo de la cadena en ese paso está en las dos
  tablas—, así que la regla nunca los separa.
* **Todo lo demostrado siguió en pie.** `cleanPair` termina siempre en una limpieza normal
  (`cleanPair_eq_clean`), así que lo que la limpieza *establece* sale gratis; lo que solo *conserva*
  hubo que llevarlo a la regla: forma, enlaces, `GN`, `PN`, `SMP`, `PMS`, `SN`, `SAbove`, `OOS`,
  `Woven`, `Sup`, `Fabric`, medida y punto fijo, y la **simetría** (`OwnSymmetric_cleanPair`: el test
  es simétrico, `pairShares_comm`, así que la regla quita las dos direcciones a la vez).
* **Una sorpresa: `Fabric` necesitaba una cláusula nueva.** Un `Fabric` no decía que dos entradas de
  una tabla compartan otra en cada paso, y sin eso la regla podía romperlo. Se añadió (`agg`, la misma
  que `Sup` ya tenía) y se demostró en todas las construcciones: la semilla, `addNode` (por casos:
  nodo antiguo o de la fila nueva), la unión, el núcleo, las cadenas, las soluciones y el estado entero
  (por el triángulo del v69). Solo `PinNonEmpty_of_star`, que ya era una reducción a hipótesis, recibe
  `agg` como hipótesis más: para la estrella es una afirmación de tipo Helly.
* **`AggInactive` pasa a ser un teorema** (`aggInactive_of_revOk`). En el punto fijo del review la
  regla ya no quita nada, así que toda pareja comparte cada paso; con los nodos válidos eso es el
  test del agresivo, y la simetría cierra su rama asimétrica: **el barrido agresivo es la identidad**
  (`aggSweep_eq_self`).
* **Tras la limpieza con parejas, la regla no quita nada** (`pairFixed_cleanPair`), y de ahí `PairOk`:
  toda pareja viva que se posee comparte entrada en cada paso.

## 4. La escalera nueva

`readerVerdictW_iff_of_pairHelly` usa la de `PinDoomed`, con:

* `PinFirstRound` **demostrada** a partir de `PairHelly` y `CleanRest`
  (`pinFirstRound_of_pairHelly`): tras `cleanPair` vale `PairFixed`, `PairHelly` da `SegGood`,
  `CleanRest` el resto de `PStateG`, y las pasadas lo conservan (ya demostrado, v184);
* `AggInactive` **demostrada**;
* `LaterValid` como estaba, con una mitad más: que la regla no quite nada al empezar una vuelta
  siguiente que progresa.

`CleanRest X` dice: si tras `cleanPair X` vale `SegGood`, vale todo `PStateG`. Casi todo está
demostrado por otras vías (ids sin repetir, forma, `OwnLive`, la simetría local es un caso de la
global); lo que queda con contenido son cinco piezas de forma: I1, I1-hijos, padres e hijos vivos y
autoposesión.

## 5. Mediciones (86 pines del lector, semillas 1 y 7)

| qué | medido |
|---|---|
| tras la limpieza **sin** regla: tramos sin entrada común | 526 + 90 (en 6 + 4 pines) |
| tras `cleanPair`: tramos sin entrada común (`PairHelly`) | **0** (de 126.023 + 157.016) |
| tras `cleanPair`: tramos sin cadena completa (forma fuerte) | **0** (8.888 + 9.112, los mismos que tras la primera vuelta) |
| tras `cleanPair`: I1, I1-hijos, padres/hijos vivos, autoposesión (`CleanRest`) | **0 fallos** |
| vueltas siguientes que progresan (`LaterValid`) | **0**; la regla nunca actúa al empezarlas |
| limpiezas siguientes que cambian algo | 0 |
| barrido agresivo | no actúa (ahora es un teorema) |

La regla actúa en la primera limpieza de solo 10 pines, justo los que tenían tramos condenados, y deja
**en un paso local lo mismo que antes dejaba la vuelta entera**: los tramos tras `cleanPair` son
exactamente los de la salida de la primera vuelta.

**`diffTest` se queda atascado, y no por un error.** Con 30 casos, lleva una hora en un solo caso
UNSAT de 7 variables y 42 cláusulas. Aislado y ejecutado paso a paso (`Probes/ModelSlow.lean`), el
modelo con y sin regla da **las mismas vueltas en cada paso**, pero con la regla va unas 25 veces más
lento en el paso 28 (342 s frente a 14 s). El tiempo crece muy deprisa con el tamaño, y la instancia
tiene 58 pasos. No es el ejecutable IO: las dos primeras bandas de `diffTest` lo usan a él, que aún no
tiene la regla y no ha cambiado. Es la tercera banda, la del **modelo puro**. Por piezas: una
`pairSweep` cuesta 40 veces una limpieza (120 s frente a 3 s acumulados en el paso 23). Para cada nodo
y cada entrada de su tabla busca el nodo en una lista y compara dos tablas: orden N³ con listas.
Pasar el test de pareja a conjuntos hash (`pairSharesFast`, con su igualdad demostrada,
`@[csimp] pairShares_eq_fast`, sin tocar ninguna prueba) solo gana un 13 %. El resto está en las
búsquedas de nodos y en rehacer los conjuntos en cada pareja.

## 6. Cómo demostrar `PairHelly`

Lo que el v185 dejó claro: no saldrá de la forma de cada tabla (ni árbol, ni intervalos, ni mayoría),
porque las tablas son exactas y la fórmula liga más de dos variables. Tampoco puede valer para
*cualquier* estado con parejas compatibles: la consistencia de parejas no implica la global en 3-SAT.
Tiene que usar **de dónde viene** el estado: un estado del lector con `SegExact` y un pin.

Una reducción que ya está a mano:

1. En el estado pinchado, la global del paso `k` es solo `q`; tras la limpieza, toda tabla viva tiene
   en `k` solo a `q`. Así que **todo miembro de un tramo de `C = cleanPair X` posee a `q`**.
2. Si alguna cadena completa del estado del lector `g` pasa por el tramo **y** por `q`, esa cadena es
   sana en el estado pinchado (el pin no le quita nada) y **sigue sana en `C`**
   (`ChainSound_cleanPair`, ya demostrado). Da la entrada común en todos los pasos —de hecho da
   `SegExact`, que es lo que se mide—.

Queda entonces **`SegThrough`**: *en un estado del lector, si tras pinchar `q` y aplicar `cleanPair`
un tramo sobrevive, alguna cadena completa pasa por el tramo y por `q`.* Es una afirmación sobre `g`
(que ya cumple `SegExact`) y la regla, no sobre la geometría de las tablas. Leída al revés: si ninguna
cadena de `g` junta el tramo con `q`, la limpieza o la regla lo rompen —y la medición del v185 dice
que siempre lo rompe la regla, con una pareja de miembros—.

El paso que falta es el de siempre, en su forma más concreta: juntar «el tramo se extiende» y «cada
miembro es compatible con `q`» en una sola cadena. La herramienta natural sería un **lema de
empalme**: dos cadenas completas de `g` que coinciden en un nodo (o en una ventana) se pueden cortar
y pegar en una cadena completa. Con él, una cadena por el tramo y una cadena por `q` que se cruzan
darían la cadena buscada. Si vale, es de estructura de cadena y encaja con lo que el v185 dijo que
había que buscar; si no vale, dirá qué información guarda la tabla que el empalme pierde.
