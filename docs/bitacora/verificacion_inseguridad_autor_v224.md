# Verificación para el Autor v224: cuatro bloques cerrados, y en cinco el lector deja de ser exacto sin atascarse

3 de octubre de 2026, rama `reader-stuck`. Continúa el v223. En una frase: **`chain4_cross` (cuatro bloques,
numeración cruzada) queda demostrada sin ninguna hipótesis: la máquina es exacta y el lector no se atasca con cualquier
orden de lectura**; en cinco bloques (`chain5_cross`) la máquina sigue siendo exacta en sus líneas, pero el lector
**no** es exacto en triángulos, y aun así no se atasca, así que el invariante que hay que demostrar es más débil que
la exactitud. Ese invariante está formulado y la reducción del lector a él, demostrada.

## 0. Dónde estamos

| | v223 | v224 |
|---|---|---|
| cómo se demuestra una clase | niveles escritos a mano | **descenso por un rango** (`tri_descent`) |
| clases sin hipótesis | `Blocks3`, `Sep2`, `Chain3` | además cuatro bloques: `Chain4L2` (líneas) y `Chain4R` (lector), con cualquier numeración |
| fórmula medida y demostrada | `chain4_cross` medida exacta | **`chain4_cross` demostrada**: `machineExact_chain4Cross`, `reader_chain4Cross_any` |
| el «testigo de cuatro nodos» | lo daba por necesario para cuatro bloques | lo da la regla: **el testigo de la ventana de una cláusula** |
| las líneas | una prueba por clase | **solo ven el prefijo** (`phantomAt_of_prefix`) |
| cinco bloques | — | `chain5_cross` exacta en líneas; **el lector no es exacto** (36 triángulos fantasma) y **no se atasca** (40 lecturas completas) |
| invariante del lector | exactitud (`HRead`) | aristas exactas: reducción a **`PinPairs`** demostrada (`reader_on_pinPairs`) |

Lean: nueve módulos nuevos (`ForbidOnDescent`, `ForbidOnChain4`, `ForbidOnChain4L`, `ForbidOnChain4R`,
`ForbidOnChain4W`, `ForbidOnChain4X`, `ForbidOnPrefix`, `ForbidOnEdge`, `ForbidOnPinPairs`), 3 208 líneas, `lake build`
completo en verde (158 trabajos), sin `sorry`, axiomas estándar `[propext, Classical.choice, Quot.sound]`.

## 1. Cómo se llegó aquí

* Ricardo pidió vías lógicas nuevas. Propuse un descenso por contraejemplo mínimo y, al formalizarlo, rehízo dos y
  tres bloques con un solo argumento (§2).
* Con cuatro bloques encontré que las ventanas leen los pasos `k`, `k-1`, `k-2`: con numeración cruzada una ventana
  mezcla bloques. Mi primera reacción fue restringir la numeración (`WinLocal`). Ricardo: **«confía en el
  algoritmo»**. La máquina es exacta en `chain4_cross`; la restricción sobraba. Buscando sin ella salieron dos
  testigos a la vez (§3) y, después, el testigo de una ventana (§5).
* Una sonda mostró que los triángulos difíciles de las líneas solo aparecen donde la cláusula de `v` aún no se exige;
  de ahí que las líneas solo ven el prefijo (§4, §6).
* En cinco bloques medí antes de demostrar: líneas exactas, lector no exacto, lector sin atasco (§7). Con eso cambió
  el objetivo: no la exactitud del lector, sino un invariante de aristas (§8).

## 2. El descenso (`ForbidOnDescent`)

`tri_descent`: si cada triángulo es de una rama de `P` en cuanto lo son todos los de rango menor, todos lo son (si
hubiera un fantasma, el de rango mínimo lo contradiría). El rango cuenta qué pasos de variables compartidas toca el
triángulo: el testigo en un paso que no toca da tres caras que sí lo tocan, de rango menor. Sep y `Chain3` se rehacen
con él (`phantomFree_sep_desc`, `phantomFree_chainData_desc`, `machineExact_threeChain_desc`), con los mismos pegados.

## 3. Cuatro bloques con `v` en un separador (`ForbidOnChain4`)

Bloques `A ∪ {s1}`, `{s1, m, s2}`, `{s2, n, s3}`, `{s3} ∪ C`, una fuente por bloque (`glue4`). El rango pasa a ser
por **lectura**: qué separadores lee alguna ventana del triángulo. Las fuentes salen de las caras de un testigo, o de
la propia rama `a0` del triángulo en los bloques que no contienen a `v`.

* `v = s3` (`phantomFree_chain4_s3`): tres rangos, solo cuentas de cardinal.
* `v = s2` (`phantomFree_chain4_s2`): cuando el triángulo no lee `s1` ni `s3`, **dos testigos a la vez**: el lado
  izquierdo sale de las caras del testigo de `s1`, el derecho de las del de `s3`, y se pegan en `v`, que todas las
  ramas de `P` leen igual (`c4s2_none`).

## 4. Las líneas solo exigen el prefijo (`ForbidOnChain4L`)

`probe_hard4.jl` en `chain4_cross`: los triángulos del caso abierto (`v` dentro de un bloque) aparecen, pero en las
líneas solo donde la cláusula de `v` aún no se exige (líneas 21/22, zona trivial; 30/31, la cláusula `(8, 4, 9)` con
ventana en el paso 31). Ahí basta parchear `v` sola (`phantomFree_free_filter`, `phantomFree_free_up`, con
`helly4_of_patch` de un bloque de una variable). Clase `Chain4L` (interiores en una sola cláusula y no su tercer
literal): `machineExact_of_chain4L`, `machineExact_fourChainL`.

## 5. El testigo de una ventana (`ForbidOnChain4R`, `ForbidOnChain4W`, `ForbidOnChain4X`)

Primero, un lector que fija antes los separadores: con los separadores fijados los bloques no se ven y basta parchear
el interior del bloque de `v` (`phantomFree_pinnedSeps`, `reader_on_chain4L_good`).

Después, la pieza que faltaba. **En el tercer paso de una cláusula la ventana lee sus tres variables; el testigo de la
regla en ese paso da tres caras que las leen igual.** Con la cláusula `{s1, m, s2}`, quedan libres los cortes en `s1`
y en `s2` a la vez. El v223 decía que cuatro bloques pedían «un testigo vecino de cuatro nodos»: lo da la regla, en el
paso de la ventana.

* `phantomFree_chain4_C` (`v ∈ C`) y `phantomFree_chain4_N` (`v ∈ N`); `A` y `M`, leyendo la cadena al revés.
* `Chain4R` y `hRead_of_chain4R`; `reader_on_chain4LR`: el lector no se atasca con cualquier orden.
* `Chain4L2` (`InnerWL`): el testigo de ventana también cubre en las líneas el tercer literal de una cláusula si la
  ventana va antes; cubre la variable 9 del `.cnf`.
* **`machineExact_chain4Cross`** y **`reader_chain4Cross_any`**: la fórmula medida, tal cual, sin hipótesis.

## 6. Las líneas solo ven el prefijo, en general (`ForbidOnPrefix`)

Por debajo del primer paso de la cláusula `j`, `φ` y su prefijo (`prefixCnf φ j`) eligen los mismos nodos, tienen las
mismas ventanas y prohíben lo mismo (`sel_prefix`, `pid_prefix`, `isProhibited_prefix`, `solE_prefix`,
`reqOf_prefix`). Entonces `phantomAt_of_prefix`: la condición de la línea `T` para el prefijo da la de `φ`. Las líneas
de una cadena larga se reducen a las de sus prefijos, que son cadenas más cortas, salvo las de la última cláusula.

## 7. Cinco bloques: lo que mide la máquina

`chain5_cross` (cinco cláusulas en cadena, 11 variables, numeración cruzada; `scripts/cnf/chain5_cross.cnf`):

| sonda | qué mide | resultado |
|---|---|---|
| `probe_exact3.jl` | exactitud fuerte en filtro, llegadas, uniones, final | **0 fuera en todo** |
| `probe_exactw.jl` | exactitud débil de las llegadas | **0** |
| `probe_hard5_read.jl` | estados de lectura (470): triángulos de la configuración doble para `v ∈ C` | 6 360, **36 fuera de toda camarilla** |
| `probe_read_full.jl` | lecturas completas (20 al azar, 20 en orden) | **0 atascos, 40 soluciones** |
| `probe_hard5_ne.jl` | nodos y aristas en estados leídos (262) | **0 nodos y 0 aristas fuera**, 24 triángulos fuera |
| `probe_triid5.jl` | `TriId` en estados leídos (260) | 32 triángulos fuera, **0 fallos de `TriId`** |

La configuración doble la había predicho el análisis a mano: la ventana del primer paso de la primera cláusula lee
`x1` y `x11` (los pasos `k-1`, `k-2` caen en la zona de variables), y con eso ninguna elección de testigo de ventana
cubre los dos lados. La máquina confirma que ahí el estado leído **no** es exacto. Por `readerExactW_iff`, `HRead` es
falsa para `chain5_cross`: la vía de la exactitud no puede cerrar el lector en cinco bloques.

## 8. El invariante de aristas exactas (`ForbidOnEdge`, `ForbidOnPinPairs`)

El lector fija **colores** (`NodeId`), no ventanas. Tras fijar el color `r`, una arista que sobrevive tiene en el paso
de `r` un testigo de ese color, y basta una rama que pase por la arista y **elija** `r`, por la ventana que sea. Un
triángulo fantasma no estropea las aristas siguientes.

* `TriId φ P g`: todo triángulo tiene una rama de `P` por dos de sus nodos que elige el color del tercero.
  `snd_pin_of_triId`: aristas exactas y `TriId` antes de fijar dan aristas exactas después. `reader_on_edge`: el
  lector no se atasca si fijar conserva `TriId` (`HReadE`).
* `HReadE` resultó circular: `TriId` en un estado es «aristas exactas tras un color más». La formulación sin círculo
  mira todos los colores a la vez: **`PinPairs φ P0 N`**: una estructura cerrada cuyas parejas y triángulos son de
  `P0`, con los nodos de los pasos fijados de su color, tiene sus parejas en ramas que eligen **todos** los colores.
  Sus hipótesis solo piden objetos exactos de `P0`, que da la exactitud del estado final.
* **`reader_on_pinPairs`**: con las líneas (`PhantomAtW`) y `PinPairs`, el lector no se atasca y acaba en una
  solución que coincide con todas las elecciones. Demostrado.

## 9. Lo que es falso (para no volver)

* **«El lector es exacto en toda cadena»**: falso en `chain5_cross` (36 triángulos fantasma en estados leídos,
  medido); por tanto `HRead` falla ahí.
* **«Cuatro bloques piden un testigo de cuatro nodos que la regla no da»** (v223): erróneo; lo da el testigo de una
  ventana.
* **«Hace falta restringir la numeración en cuatro bloques»**: erróneo; `chain4_cross` está demostrada con su
  numeración cruzada.
* **`HReadE` como paso de inducción**: circular (§8).

## 10. Lo que no se sabe

* `PinPairs` para cadenas: es lo único que falta para el lector de cinco bloques (las líneas se reducen por el prefijo
  y, en la última cláusula, a los casos del bloque final).
* Si el testigo de ventana basta para las líneas de cinco bloques en la última cláusula (casos `v ∈ C` y `v = s4`);
  el análisis a mano dice que sí salvo la configuración doble, que en las líneas no apareció.
* Seis bloques: `chain6_cross` ya incumplía la exactitud fuerte en llegadas (v223); falta ver si `PinPairs` y la
  versión débil bastan allí.

## 11. Plan

1. Demostrar `PinPairs` en cadenas. Idea: una cadena de bloques que comparten una sola variable es un problema de
   satisfacción con forma de árbol, donde la consistencia local basta para la global; construir la rama bloque a
   bloque, y que la regla de la máquina dé la consistencia local necesaria.
2. Las líneas de `chain5_cross`: prefijos de uno a cuatro bloques con las clases ya demostradas, y la última cláusula
   con el testigo de ventana.
3. Con 1 y 2, `reader_chain5Cross` sin hipótesis.

## Ficheros y teoremas

| fichero | líneas | lo principal |
|---|---|---|
| `Model/ForbidOnDescent.lean` | 308 | `tri_descent`, `phantomFree_of_descent`, `hitRank`, `phantomFree_chainData_desc` |
| `Model/ForbidOnChain4.lean` | 762 | `Chain4Data`, `glue4`, `Faces.pick3`, `phantomFree_chain4_s3`, `phantomFree_chain4_s2` |
| `Model/ForbidOnChain4L.lean` | 360 | `FreeBelow`, `phantomFree_free_filter` / `_up`, `OnceNotLast`, `Chain4L`, `machineExact_fourChainL` |
| `Model/ForbidOnChain4R.lean` | 385 | `phantomFree_pinnedSeps`, `GoodAlong`, `reading_inv_on`, `reader_on_chain4L_good` |
| `Model/ForbidOnChain4W.lean` | 450 | `faces_Pw`, `phantomFree_chain4_C`, `phantomFree_chain4_N`, `Chain4R`, `reader_fourChainL_any` |
| `Model/ForbidOnChain4X.lean` | 301 | `InnerWL`, `Chain4L2`, `machineExact_chain4Cross`, `reader_chain4Cross_any` |
| `Model/ForbidOnPrefix.lean` | 195 | `prefixCnf`, `phantomFree_transfer`, `phantomAt_of_prefix` |
| `Model/ForbidOnEdge.lean` | 235 | `TriId`, `snd_pin_of_triId`, `RInvE`, `reader_on_edge` |
| `Model/ForbidOnPinPairs.lean` | 212 | `PinPairs`, `RInvP`, `read_stepP`, `reader_on_pinPairs` |
| `test_3sat/probe_hard4.jl`, `probe_hard4_read.jl` | — | el caso abierto de cuatro bloques en líneas y lector |
| `test_3sat/probe_hard5_read.jl`, `probe_hard5_ne.jl`, `probe_triid5.jl`, `probe_read_full.jl` | — | cinco bloques: fantasmas, aristas, `TriId`, lecturas completas |
| `scripts/cnf/chain4_l.cnf`, `chain5_cross.cnf` | — | `fourChainL`, la cadena de cinco |

Commits: `5ad5d31` (descenso), `517fc03` (separadores), `7d23cd0` (sonda), `32651ac` (prefijo en cuatro bloques),
`4a416f6` (separadores primero), `0ccec38` (testigo de ventana, `chain4_cross`), `f22204f` (prefijo general),
`b9accaa` (fantasmas en cinco bloques), `1bc45c0` (aristas exactas), `2f8c0dc` (`TriId` medido), `5da9c69`
(`PinPairs`). La tabla de sincronía Julia/Lean está en `docs/plans/lean_bingo.md`.
