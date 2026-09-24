# Verificación para el Autor v184: el review simétrico, la simetría como invariante y el lector por las pasadas

Ricardo, soy Claude (Opus 5.5). Este informe sigue al v183. Allí la escalera del lector había quedado en
`hStart` más una obligación por pin (`AdmittedExt`), y el review simétrico del v182 se había aparcado
porque «ya no estaba en el camino principal». Las mediciones de `nactrace` lo devolvieron al camino: los
tramos que quedaban sin cadena morían en las pasadas **perdiendo la posesión entre sus miembros**, y
esa pérdida era de un solo lado. Aquí se cuenta cómo el espejo entró en la máquina (Julia, el modelo y
el ejecutable), qué se demostró con él, y a qué ha quedado reducido el lector.

Ramas `clean-two-phase` → `review-symmetric`. `lake build AbsSat` verde (268 jobs), sin `sorry`, sin
`Classical.choice` (los axiomas de siempre: `propext`, `Quot.sound`). 18 commits desde el v183
(`d52a5f9`). Módulos nuevos: `SymInvariant.lean`, `PinDoomed.lean`, `ReadyInv.lean`.

---

## 0. Dónde estamos, en una línea

```lean
theorem readerVerdictW_iff_of_pinDoomed (hStart : …) (hPin : …) (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ
```

El lector sin retroceso decide 3-SAT con: la línea final revisada sin tramos sin cadena (`hStart`,
medida desde el v183) y, en cada pin, **tres afirmaciones sobre el review del pin**, todas medidas sin
fallos: los tramos que el pin deja sin entrada común mueren en la primera vuelta (`PinFirstRound`), las
vueltas siguientes que aún progresan empiezan con todos sus nodos válidos (`LaterValid`), y el barrido
agresivo no actúa (`AggInactive`). Todo lo demás —las pasadas, la limpieza, la simetría— está
demostrado.

## 1. El review simétrico: tu idea, ahora en la máquina

La frase del v182: cuando el review quita `w` de la tabla de `x` afirma *ninguna solución pasa a la vez
por `x` y por `w`*; la frase es simétrica, así que **`w` pierde también a `x`** (el espejo).

**Julia** (`julia/improves`, plan `docs/plans/review_simetrico.md`, fase A):

* **A0, la situación de partida** (`measure_symmetry.jl`, `test_window`): hay poca asimetría, y la
  crean las pasadas de padres e hijos (150 parejas tras la de hijos); UP no la crea nunca; el barrido
  agresivo la reduce pero no la elimina.
* **A1–A4**: `intersect_removed!` (el corte devolviendo lo que quita) y `mirror_remove!` en las dos
  pasadas, detrás de `SYM_MODE`. Test en `runtests`: con `:on`, 0 parejas asimétricas tras cada etapa,
  0 disparos de la rama «asimétrica» del filtro agresivo, 0 nodos eliminados en las pasadas.
* **A5, comparación diferencial** (`compare_sym.jl`, 80 instancias): **mismos veredictos, mismos
  estados finales y mismas vueltas** que sin espejo, +0,2 % de tiempo. La rama «asimétrica» del filtro
  agresivo pasa de 44.029 disparos a **0**: el espejo hace en el momento lo que ese filtro hacía
  después.
* **A6**: `SYM_MODE = :on` por defecto.

**El modelo Lean** (fase B): `reviewNode` corta la tabla de `x`, borra `x` de las tablas de los owners
que perdió (`mirrorDrop`), desenlaza y valida, en el mismo orden que Julia. La sonda `sym2` confirma que
el modelo con espejo deja **los mismos estados** que sin él (semillas 1 y 7: 12.944 envíos y 86 pines,
0 distintos). **El ejecutable IO** (`GraphPath.lean`) pasa a la limpieza en dos fases y al espejo, y
coincide con el oráculo exhaustivo en veredicto y conjunto de soluciones: 500 de 500 (`exec-diff`);
`diffTest` con las tres bandas, 30 de 30.

Un tropiezo de rendimiento, ya resuelto: `cutRemoved` recalculaba el corte entero para cada owner, y
el modelo se volvió 40 veces más lento en algunos casos (un UNSAT de 7 variables: más de una hora).
Reescrito con el test de `intersectOwners` directamente, el espejo cuesta 1,3 veces el review sin él.

## 2. Todo lo demostrado siguió siendo cierto

Con el espejo, la tabla de un nodo distinto de `x` ya no es constante en `reviewNode x`: puede perder la
entrada `x`. Todo lo que usaba «las demás tablas no cambian» hubo que repararlo (B2): forma, medida,
cadenas sanas (`ChainSound`), `Closed`/`Woven`, `Sup`, `Fabric`, `Anchored`, y las pasadas nodo a nodo
(`PassCtx`, `PassSons`, `PassPlain`, `CompatLoss`).

El único sitio con contenido nuevo fue **`SegGood` nodo a nodo**. Si `x` era la entrada común de un
tramo y su corte deja fuera a un miembro, el espejo le quita `x` a ese miembro. La prueba nueva: el
tramo se extiende a una cadena completa `Q` (`seg_full`), y la entrada común de después es `Q i`; si
`Q i` es justo `x`, el vecino de `x` en `Q` posee al miembro, así que el corte de `x` no lo deja fuera.
Medido antes de demostrarlo (`nodeseg`): el espejo actúa 44 veces en la semilla 1 y nunca rompe
`SegGood`.

## 3. La simetría es ahora un invariante (B3)

`SymInvariant.lean`:

* **`OwnSymmetric_reviewNode`**: un paso de una pasada conserva la simetría entre nodos vivos, sin más
  hipótesis que ids sin repetir.
* **`OwnSymmetric_cleanInvalid₂`**: la purga no toca tablas, y en su punto fijo cada nodo vivo está en
  su propio corte (`self_in_cut`, por `OOS`), así que el corte global no lo quita de ninguna tabla.
* **`aggPair_asym_never`**: con simetría, la rama «asimétrica» del barrido no se dispara; la
  «inconsistente» quita las dos direcciones. De ahí `OwnSymmetric_aggSweep`, `…_reviewAgg` y
  `…_filterAllAgg`.
* **`LocSym_of_ownSymmetric`**: la simetría local que las pasadas pedían es un caso de la global. Con
  eso **las pasadas conservan `PStateG` sin hipótesis** (`pstateG_reviewPass'`): desaparecen
  `LocSymStable` y `LocSymStableS`.

## 4. S1′, demostrado; S2, medido

**S1′** —tu postulado flexible del v182— está demostrado para las dos pasadas de una vuelta
(`commonLoss_round`): si una entrada viva `r` sale de la tabla de `y`, o `y` es el procesado y `r`
queda separado de él en el paso de sus vecinos, o `r` es el procesado (el espejo) y es `y` quien queda
separado; y la separación dura el resto de la vuelta.

**S2** —que alguna entrada común de antes siga viva— no está demostrado. Medido en los estados del
lector (`roundseg`, semillas 1 y 7, 566.078 casos): **0 fallos**; y S1′ se cumple en los 683 casos en
que una entrada sale de una tabla. `SegGood` tampoco se rompe nunca entre vueltas del lector.

## 5. La escalera, por el invariante de las pasadas

Con las pasadas cerradas, la pregunta pasó a ser dónde se rompe `PStateG` en el review de un pin
(`cleanpin`, 86 pines):

| momento | I1 / I1-hijos / vivos / autoposesión | `SegGood` |
|---|---|---|
| entrada de la 1ª limpieza (el pin) | 0 fallos | 0 fallos |
| **salida de la 1ª limpieza** | 0 fallos | **616 tramos sin entrada común** |
| limpiezas siguientes | 0 fallos | 0 fallos |
| barrido agresivo | no actúa en ningún pin | — |

Así que `SegGood` no es invariante de la limpieza: el pin deja tramos sin entrada común, y **las pasadas
de esa misma vuelta los rompen todos**. `PinDoomed.lean` lo formaliza:

* `pstateG_of_reader`: un estado del lector con `SegGood` cumple todo `PStateG` y la simetría (el
  punto fijo del review agresivo da el resto: posesión vecina = enlaces, tablas vivas);
* `segGood_pinReview`: con las tres hipótesis del pin, `SegGood` llega al punto fijo;
* y la escalera, por inducción sobre la lectura: `SegGood` en cada estado del lector da el veredicto.

Y dos de las hipótesis se afinaron con pruebas:

* **las limpiezas siguientes no hacen nada**: sobre un estado con todo nodo válido, en la global y con
  los enlaces en su tabla, `cleanInvalid₂` es la identidad (`cleanInvalid₂_eq_self_of_ready`); estar en
  la global y tener los enlaces en la tabla lo deja la vuelta anterior (`ReadyInv`); y la vuelta final
  es la identidad por el punto fijo. Queda solo `LaterValid`: los nodos son válidos al empezar una
  vuelta siguiente que aún progresa —y en la medición ninguna progresa: todos los pines terminan en
  dos vueltas—.

## 6. Cómo mueren los tramos condenados (`doomtrace`)

`PinFirstRound` es la hipótesis de fondo. Medido, en las semillas 1 y 7 (86 tramos condenados):

* **mueren todos en la primera vuelta, y siempre igual**: cuando la pasada procesa a **su extremo** (el
  miembro más bajo en la pasada de padres, el más alto en la de hijos), el corte de ese extremo deja
  fuera a otro miembro, el espejo lo hace mutuo y la pareja deja de poseerse; nunca por eliminar un
  miembro ni por perder un enlace;
* **la unión de las tablas de los vecinos del extremo nunca cubre al resto del tramo** (0 de 86), y
  casi siempre faltan varios miembros;
* **antes de la limpieza sí lo cubría** (86 de 86);
* el pin actúa **a distancia**: fija un paso entre 4 y 13 pasos por debajo del extremo, que nunca es
  uno de los pasos sin entrada común del tramo;
* la cobertura se pierde por dos vías: vecinos que la purga eliminó **en cascada** (ninguno en el paso
  fijado) y vecinos vivos cuyo propio corte, **antes en la misma pasada**, ya había quitado al miembro.

Es una **propagación en dos tiempos**: la purga elimina una franja a partir del pin y la pasada de
padres, que sube paso a paso, va vaciando las tablas hasta llegar al tramo.

## 7. Lo que queda

| hipótesis | qué dice | medido |
|---|---|---|
| `hStart` | la línea final revisada no tiene tramos sin cadena | 0 fallos (v183) |
| `PinFirstRound` (cada pin) | los tramos que la limpieza del pin deja sin entrada común mueren en la primera vuelta | 0 supervivientes (86 condenados) |
| `LaterValid` (cada pin) | las vueltas siguientes que progresan empiezan con todos sus nodos válidos | 0 fallos; ninguna progresa |
| `AggInactive` (cada pin) | el barrido agresivo no quita nada tras el review base | no actúa en ningún pin |

## 8. Cómo seguir

`PinFirstRound` como **lema de propagación por la pasada**: tras procesar el paso `j`, una entrada
sobrevive en una tabla solo si hay un camino hacia abajo, por padres ya procesados, que la contiene.
La parte «cada miembro del tramo por algún camino» es demostrable; el salto a «todos por el mismo
camino» es, otra vez, la dificultad de tipo Helly —pero ya en su forma más local: una sola vuelta, un
solo nodo (el extremo) y sus vecinos—. `LaterValid` y `AggInactive` son más mecánicas, y las dos
quedarían vacías si se demuestra que tras la primera vuelta del pin el estado ya es punto fijo, que es
lo que la medición enseña.

## 9. Una frase

El espejo no cambió lo que la máquina decide —mismos estados en Julia, en el modelo y en el
ejecutable—, pero cambió lo que se puede demostrar sobre ella: la simetría dejó de ser una propiedad de
los estados finales para ser un invariante, las pasadas quedaron cerradas sin hipótesis, y lo que
separa al lector de un teorema sin hipótesis es ahora una afirmación sobre la primera vuelta de cada
pin.
