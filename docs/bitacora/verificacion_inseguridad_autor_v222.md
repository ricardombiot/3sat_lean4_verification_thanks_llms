# Verificación para el Autor v222: la corrección de la máquina, equivalente a un enunciado sobre la fórmula

2 de octubre de 2026, rama `reader-stuck`. Continúa el v221. En una frase: **la máquina con tríos es exacta en todos
sus estados si y solo si la fórmula no tiene «familias fantasma»**, y esa condición no menciona la máquina. Con ella
la máquina decide y el lector no se atasca; para las fórmulas con forma 2-CNF todo eso queda demostrado **sin ninguna
hipótesis**. Lo que sigue abierto ya no es un lema de la máquina: es una pregunta de combinatoria sobre fórmulas.

## 0. Dónde estamos

| | v221 | v222 |
|---|---|---|
| veredicto | bajo `HypsNodeKeep` (una hipótesis sobre estados de la máquina) | bajo `PhantomAt` (una propiedad de la **fórmula**) |
| ¿la hipótesis es la justa? | no se sabía | **sí**: `machineExact_iff`, una equivalencia |
| clase sin hipótesis | ninguna | las fórmulas con forma 2-CNF: la máquina decide y el lector no retrocede |
| el lector | no estaba formalizado | `reader_on`: cualquier lectura deja un estado válido con una solución |
| las copias de literales | consumían un nivel de la prueba cada una | demostrado que no consumen nada sin ventanas prohibidas |
| hipótesis del v221 (`HypsNodeKeep`, `HypsTriKeep`) | las vigentes | consecuencias de `PhantomAt` |

Lean: seis módulos, 3 761 líneas, `lake build` completo en verde, sin `sorry`, axiomas estándar. Cinco de ellos son
nuevos desde el v221 (`ForbidOnMaj`, `ForbidOnHelly`, `ForbidOnRead`, `ForbidOnTight`, `ForbidOnReadIff`) y
`ForbidOnExact` creció.

## 1. Cómo se llegó aquí

El v221 dejó todo el contenido en un paso del filtro (`PinTetra`, cuatro nodos). Las preguntas de Ricardo desde
entonces marcaron el camino:

* *«Sin la ventana prohibida tendríamos todas las combinaciones… y al podarlas estaríamos en la misma»* (§2). Es
  exacto: toda la dificultad la crea la ventana prohibida; las copias de literales son igualdades y no cuestan nada.
* *«Me niego a pensar que no hay forma de demostrar un sistema de lectura que funciona.»* Lo descartado hasta
  entonces eran atajos, no la posibilidad. El atajo que sí funcionó fue cambiar de sitio: en vez de seguir a la
  máquina operación a operación con niveles, describir **qué representa cada estado** (las soluciones de lo leído) y
  demostrar que cada operación conserva esa descripción.

## 2. La lectura semántica del mapa bin

* Un paso de variable elige su valor; el paso siguiente es su negación; **un paso de cláusula copia el valor de un
  literal** (su requisito es el nodo de esa variable con ese valor); la disyunción es la **ventana prohibida**
  `(0, 0, 0)` en el tercer paso de cada cláusula.
* **Cada paso lee una sola variable** (`stepVar`, `sel_eq_of_var`, `var_eq_of_sel`). Una camarilla es la rama de una
  asignación; las copias van determinadas.
* El filtro de una llegada es **partir por el valor de una variable más**.

Dos consecuencias formalizadas en `ForbidOnExact`:

* Un filtro cuyo requisito cae en el paso de la cima no consume nivel (`ct_filter_of_topReq`); en la parte de
  variables todos son así (`reqOf_step_pre`), y los tres niveles valen sin hipótesis hasta la fusión central
  (`lInvX_pre`). Las hipótesis solo hacen falta en las líneas de cláusula (`spineVerdictOn_iff_of_nodeKeepC`).
* Con la escalera del v221, cada copia lejana consumía un nivel de la prueba: se llegaba solo hasta justo antes de la
  primera ventana prohibida y solo para las cimas (`topCT_before_first_window`). Con la semántica (§3) se llega al
  mismo sitio con **los tres niveles** (`levels_before_first_window`): las copias no consumen nada.

## 3. La mayoría: las fórmulas con forma 2-CNF, sin hipótesis (`ForbidOnMaj`)

**El invariante.** `Snd φ P g`: toda pareja de nodos vecinos de `g` está en la rama de una asignación de `P`, donde
`P` son las soluciones del prefijo leído (`ValidUpTo`: la rama no pisa ventanas prohibidas por debajo del paso) con la
clave de la entrada. Con la completitud (`comp_line`, que generaliza `run_carriesOn` a los prefijos), el grafo de cada
entrada es exactamente el de sus soluciones.

**La pieza.** La mayoría de tres asignaciones (`maj3`) pasa por todo nodo por el que pasan dos de ellas
(`pid_maj_ab`, `_ac`, `_bc`), porque cada paso lee una variable. Bajo `MajClosed` (las soluciones del prefijo son
cerradas por mayoría), `Snd` pasa las tres operaciones:

| operación | lema | idea |
|---|---|---|
| join | `snd_joinOn` | una arista de la unión es de un lado |
| filtro | `snd_filter` | la pareja tiene un testigo común en el paso del requisito; la mayoría de las tres ramas pasa por los dos nodos y cumple el requisito |
| UP | `snd_upOn` | un nodo de la fila baja a un padre (`adjust`, `lift_row`); dos nodos viejos tienen una cima testigo si la fila saltó una ventana |

Con `Snd` y la completitud los tres niveles del v221 salen **a la vez** (`levels_of_snd`): no hay escalera.

**Resultados.**

* `spineVerdictOn_iff_of_majClosed`: la espina decide toda fórmula cuyas soluciones de prefijo son cerradas por
  mayoría.
* **`spineVerdictOn_iff_of_twoLike`**: en particular las fórmulas con forma 2-CNF (`TwoLike`: en cada cláusula el
  segundo y el tercer literal son el mismo), por `majClosed_twoLike`. Es el **primer veredicto sin hipótesis** de la
  máquina con tríos. La máquina de Lean, ejecutada sobre tres fórmulas pequeñas de esa forma, da UNSAT, SAT, UNSAT.

**Por qué no llega a 3-CNF.** La mayoría de las ventanas `100`, `010` y `001` es `000`, la prohibida. Es el mismo
fenómeno que el trío muerto de `clause_mix`.

## 4. El nivel de triángulos: una condición sobre la fórmula (`ForbidOnHelly`)

El mismo esqueleto, un nivel más arriba. `Snd3 φ P g`: toda pareja de vecinos **y todo triángulo sin prohibir** de
`g` está en la rama de una asignación de `P`. La mayoría se sustituye por lo mínimo que la prueba usa.

**`PhantomFree φ P0 P N σ`** (sin familias fantasma). Toda estructura de nodos, parejas y tríos prohibidos que sea

* simétrica y **cerrada por la regla** en los pasos `0 … N − 1` (cada pareja tiene en cada paso un testigo bueno, y
  cada triángulo sin prohibir también),
* **hecha de ramas de `P0`** (sus parejas y sus triángulos sin prohibir),
* y anclada (una rama de `P0` por un nodo suyo del paso `σ` es de `P`),

es de ramas de `P`. Es una propiedad de conjuntos de asignaciones: **no menciona la máquina**.

La prueba la pide en dos situaciones, y en las dos la estructura es el propio estado revisado (`ClosedState`,
`trioGood_low`):

| operación | cuándo | de qué ramas a qué ramas | `σ` |
|---|---|---|---|
| filtro (`snd3_filter`) | el filtro mata algo | las de la entrada → las que cumplen el requisito | el paso del requisito |
| UP (`snd3_upOn`) | la fila salta una ventana | las del remitente filtrado → las de la llegada | el paso nuevo |

El join no pide nada (`snd3_joinOn`). `PhantomAt φ T` reúne las dos condiciones de la línea `T`, y

> **`spineVerdictOn_iff_of_phantomFree`**: `Bounded φ → (∀ T ≥ 1, PhantomAt φ T) → (SpineVerdictOn φ ↔ Satisfiable φ)`.

Hay una versión de un solo paso, más fuerte y más fácil de comprobar: **`Helly4`** (una rama por tres nodos y tres
ramas por cada dos de ellos y por un mismo nodo del paso `σ` dan una rama por los tres). La cadena, toda demostrada:

```
MajClosed  ⟹  HellyAt (un paso)  ⟹  PhantomAt (todos los pasos)  ⟹  la máquina decide y el lector no se atasca
```

La de un paso **no** vale siempre (§8): usa el testigo de un solo paso, y la regla de la máquina busca en todos.

## 5. La equivalencia (`ForbidOnTight`)

> **`machineExact_iff`**: `MachineExact φ ↔ ∀ T ≥ 1, PhantomAt φ T`, sin hipótesis.

`MachineExact φ`: en cada línea, cada entrada, cada remitente filtrado válido y cada llegada válida cumplen `Snd3`.
Son los estados que mide `probe_exact3.jl`.

**El recíproco, por el punto fijo.** Una estructura cerrada por la regla y hecha de ramas de antes vive dentro del
estado como estructura cerrada completa: sus enlaces padre–hijo salen de la rama que realiza cada pareja
(`Carried.node`), así que no hace falta pedirlos. Cumple lo que se fija, y **sobrevive** al filtro y a su review
(`struct_survives_filter`) y a la fila nueva, a los tríos que escribe el UP —que llevan siempre un nodo de la fila— y
a su review (`struct_survives_up`). Lo que sobrevive en un estado exacto es de ramas que cumplen lo fijado. Si el
estado queda inválido no hay estructura que sobreviva (`valid_of_sec`), y si ninguna solución elige una clave no hay
estructura (`phantomFree_of_empty`).

**Lo que significa.** La pregunta «¿es exacta la máquina con tríos?» queda traducida, exactamente y verificada en
Lean, a: **¿puede una 3-CNF tener una familia fantasma?** Un fallo de la sonda en una instancia es una familia
fantasma de esa fórmula, y al revés.

## 6. El lector (`ForbidOnRead`, `ForbidOnReadIff`)

Una lectura (`Reading g R g'`) fija en orden los colores de nodos vivos, revisando tras cada uno.

* **`read_step`**: fijar el color de **cualquier** nodo vivo deja el estado válido sin pedir nada (la rama que pasa
  por el nodo sobrevive entera); que el estado siga exacto pide `PhantomFree` para ese color.
* **`reader_on`**: bajo `PhantomAt` en las líneas y `HRead` en la lectura, cualquier lectura de un estado final deja
  un estado válido que lleva la rama de una asignación que **satisface la fórmula y coincide con todas las
  elecciones**. El lector no retrocede.
* **`reader_on_twoLike`**: lo mismo sin hipótesis en las fórmulas con forma 2-CNF.
* **`readerExact_iff`**: el lector es exacto en todos los estados que visita si y solo si la lectura no tiene
  familias fantasma (`HRead`).

Y el enlace con el v221: `hypsTriKeep_of_phantomAt`, `hypsNodeKeep_of_phantomAt`. Las hipótesis de niveles son
consecuencias de la condición sobre la fórmula.

## 7. Comprobaciones

### 7.1 La condición, por fuerza bruta sobre la fórmula (`scripts/helly_formula.py`, sin máquina)

Enumera las `2^n` asignaciones y comprueba `HellyAt` en cada línea; donde falla (o siempre, con `--phantom-all`)
calcula la mayor estructura cerrada y cuenta los fantasmas; con `--reader`, la hipótesis de la lectura con las
variables fijadas en orden.

| fórmula | variables | cláusulas | fallos de un paso (filtro / UP / lector) | fantasmas |
|---|---|---|---|---|
| `clause_mix` | 6 | 4 | 0 / 0 / 0 | 0 (todos los casos) |
| `clause_mix_sep` | 9 | 4 | 0 / 0 / 160 | 0 (todos los casos) |
| `v5_c20_i1` | 5 | 20 | 0 / 0 / 0 | 0 (todos los casos) |
| `v5_c20_i2` (UNSAT) | 5 | 20 | 0 / 0 / — | 0 (todos los casos) |
| `parity4` (paridad sola) | 5 | 8 | 0 / 0 / 0 | 0 (todos los casos) |
| `parity_use` (paridad + una cláusula que lee una variable) | 9 | 9 | 0 / 768 / 7 296 | 0 |
| `parity_use2` (la anterior + otra cláusula) | 9 | 10 | 8 192 / 1 536 / 8 704 | 0 |
| `parity_use_unsat` | 9 | 14 | 0 / 768 / — | 0 |

Control del script: sin el ancla toda la estructura sobrevive (296 393 fantasmas en `clause_mix`), así que el cero no
es un artefacto. Las fórmulas de paridad se construyeron para romper la condición de un paso; la rompen, y la de
todos los pasos se cumple.

### 7.2 La máquina sobre las fórmulas de paridad (`probe_exact3.jl`, `FORBID=:on`)

| fórmula | estados | fuera de camarilla | estado final | tetraedros muertos en el paso del requisito |
|---|---|---|---|---|
| `parity_use` (SAT) | 377 | 0 | 112 camarillas = soluciones | 768 de 493 279 |
| `parity_use2` (SAT) | 407 | 0 | 96 camarillas | 1 344 de 623 873 |
| `parity_unsat_units` (UNSAT) | 391 | 0 | no hay | 0 |
| `parity_use_unsat` (UNSAT) | 426 | 0 | no hay | 1 408 de 685 435 |

Primera vez que aparecen tetraedros muertos en el paso del requisito. Sus triángulos de cima se salvan por otro nodo
de ese paso: la forma fuerte de `PinTetra` (el tetraedro mismo está en una camarilla) es **falsa**; la débil, la del
v221, vale.

### 7.3 Cuánto ve un trío (`probe_regen.jl`)

| instancia | variables | triángulos en una sola solución | mayoría por parejas: las dos ventanas viven y no son vecinas |
|---|---|---|---|
| `v5_c20_i1` | 5 | 84 % | 14,7 % |
| `v6_c26_i5` | 6 | 78 % | 10,8 % |
| `clause_mix` | 6 | 40 % | 3,4 % |
| `clause_mix_sep` | 9 | 0,4 % | 1,0 % |

**Aviso sobre toda la evidencia medida hasta el v221.** Las instancias tenían entre 5 y 9 variables, y un trío de
ventanas ve hasta 9 valores de literales: en las aleatorias un triángulo ya fija casi siempre la solución entera, y
ahí «el nivel 3 es exacto» dice casi lo mismo que «las camarillas son las soluciones», que es un teorema. Los ceros
son ciertos pero dicen poco de fórmulas con muchas más variables.

### 7.4 Instancias mayores (otra sesión, parciales)

De la sesión paralela de Ricardo, leído de `output_probes/exact3_n12/` al cerrar este informe. Solo una tanda terminó;
las demás las cortó el tope de memoria (2 500 MB) y lo que hay es el volcado parcial:

| instancia | estado de la tanda | estados juzgados | fuera de camarilla |
|---|---|---|---|
| `tseitin_k33_H` (UNSAT) | completa | 318 (55 428 935 triángulos) | 0 |
| `tseitin_k33_even` | cortada | 338 | 0 |
| `tseitin_cube_H`, `tseitin_cube_even` | cortadas | 323 cada una | 0 |
| `tseitin_petersen_H` | cortada | 327 | 0 |
| `rand_v12_c36_s1`, `rand_v12_c44_s2` | cortadas | 341 y 253 | 0 |

No las he lanzado yo ni he comprobado su configuración; las cito para que el informe no las ignore. Por
`machineExact_iff`, un cero completo en una instancia equivale a que esa fórmula no tiene familias fantasma en los
estados medidos.

## 8. Lo que es falso (para no volver)

| afirmación | por qué |
|---|---|
| la condición de un paso (`HellyAt`) vale en toda fórmula | falla en `parity_use` (768, en el UP), `parity_use2` (9 728, de ellos 8 192 en el filtro) y en la lectura de `clause_mix_sep` (160) |
| un tetraedro con sus cuatro caras legítimas y un nodo en el paso del requisito está en una camarilla | 768, 1 344 y 1 408 muertos en las fórmulas de paridad |
| la prueba de 2-CNF se adapta a 3-CNF «salvo ventanas prohibidas» | a nivel de parejas la mayoría falla con las dos ventanas vivas en el 1–15 % |
| hace falta añadir el cierre padre–hijo a la condición para que sea la justa | no: los enlaces salen de la rama que realiza cada pareja |
| un nivel fijo de la escalera del v221 basta para la inducción | cada cláusula añade una variable por la que partir; lo que hay que probar es que el review recupera lo que el filtro consume, y eso es `PhantomFree` |

Tres errores míos de esta etapa, corregidos: recomendé un «lector certificado» que ya existía
(`verdictOn_certified`); dije que la condición de familias fantasma era algo más fuerte de lo necesario, y es la
justa; y estimé en días una formalización que salió en horas porque las piezas del repositorio ya encajaban.

## 9. Lo que no se sabe

* **Si toda 3-CNF está libre de familias fantasma.** Es la pregunta abierta, en su forma final. La teoría conocida de
  consistencia local dice que las condiciones de nivel fijo fallan en familias de tipo paridad sobre grafos grandes;
  aquí las ventanas de tres copias dan a la regla más de lo que da un nivel fijo sobre las variables, y no sé si
  basta.
* **Si la exactitud es necesaria para acertar.** La equivalencia es para la exactitud de todos los estados, que basta
  para decidir y leer. Una máquina podría no ser exacta en un estado intermedio y acertar al final.
* **Instancias grandes.** Las comprobaciones por fuerza bruta de la condición son de 5–9 variables (el script en
  Python no escala), y las tandas de 12–15 variables de la otra sesión están incompletas.
* **El espejo Julia–Lean de la condición.** `helly_formula.py` reproduce a mano `selOfAssign`, `pidOfAssign`,
  `isProhibited`, `mapNodes`, `sonsOfMap` y `reqOf`. No está verificado contra Lean más que por coincidencia de
  resultados con la máquina.

## 10. Plan

1. Completar las tandas de 12–15 variables con más memoria o con la enumeración acotada, y leerlas con la
   equivalencia: un fallo es una familia fantasma concreta, con su fórmula, su línea y su paso.
2. Pasar la comprobación de `PhantomAt` a Julia para llegar a más variables, o a Lean para que la comprobación de una
   fórmula concreta sea una demostración.
3. Buscar clases mayores que 2-CNF donde `PhantomAt` se demuestre: lo natural es acotar la estructura de la fórmula
   (por ejemplo por la anchura del grafo de sus restricciones entre ventanas).
4. Si aparece una familia fantasma: es el punto exacto donde la máquina necesita más memoria que parejas y tríos, y
   dice qué habría que guardar.

## Ficheros y teoremas

| fichero | líneas | qué tiene |
|---|---|---|
| `ForbidOnExact` | 1 010 | (v221) `TopEdge`, `TopTri`, la escalera, `LInvP`; (nuevo) `ct_filter_of_topReq`, `reqOf_step_pre`, `lInvX_pre`, `spineVerdictOn_iff_of_nodeKeepC`, `topCT_before_first_window` |
| `ForbidOnMaj` | 1 021 | `maj3`, `stepVar`, `pid_maj_ab/ac/bc`; `ValidUpTo`, `comp_line`; `adjust`, `lift_row`; `Snd`, `snd_joinOn`, `snd_filter`, `snd_upOn`; `levels_of_snd`; `LInvS`; `levels_before_first_window`; `prohibited_clause`, `prohibited_of_false`; `TwoLike`, `majClosed_twoLike`; `spineVerdictOn_iff_of_majClosed`, `spineVerdictOn_iff_of_twoLike` |
| `ForbidOnHelly` | 762 | `Helly4`, `PhantomFree`, `phantomFree_of_helly4`, `helly4_extend`; `Snd3`, `snd3_joinOn`, `snd3_filter`, `snd3_upOn`; `levels_of_snd3`; `PhantomAt`, `HellyAt`, `phantomAt_of_hellyAt`, `hellyAt_of_majClosed`; `LInvS3`; `spineVerdictOn_iff_of_phantomFree`, `spineVerdictOn_iff_of_helly` |
| `ForbidOnRead` | 191 | `sat_of_validUpTo`; `RInv`, `read_step`, `Reading`, `Pinned`, `HRead`, `reading_inv`, `hRead_of_maj`; `reader_on`, `reader_on_twoLike` |
| `ForbidOnTight` | 593 | `PhStruct`, `phantomFree_of_empty`, `valid_of_sec`; `struct_survives_filter`, `struct_survives_up`; `phantomFree_of_exact_filter`, `phantomFree_of_exact_up`, `snd3_filter_iff`; `lInvBase_steps`, `compLine_base`; `MachineExact`, `machineExact_iff` |
| `ForbidOnReadIff` | 184 | `hypsTriKeep_of_phantomAt`, `hypsNodeKeep_of_phantomAt`; `reading_snoc`, `ReaderExact`, `rInv_step`, `reach`, `readerExact_iff` |

| teorema | hipótesis | dice |
|---|---|---|
| `spineVerdictOn_iff_of_twoLike` | forma 2-CNF | la espina decide |
| `reader_on_twoLike` | forma 2-CNF | el lector no retrocede |
| `spineVerdictOn_iff_of_phantomFree` | `PhantomAt` (la fórmula) | la espina decide |
| `reader_on` | `PhantomAt` y `HRead` (la fórmula) | el lector no retrocede |
| `machineExact_iff` | ninguna | la máquina es exacta ⟺ `PhantomAt` |
| `readerExact_iff` | `PhantomAt` | el lector es exacto ⟺ `HRead` |

Sondas y scripts nuevos: `probe_regen.jl`, `lean/improves_bingo/scripts/helly_formula.py` y las fórmulas de
`scripts/cnf/`. Commits desde el v221: de `f590548` al de este informe. Tabla de sincronía: `docs/plans/lean_bingo.md`.
