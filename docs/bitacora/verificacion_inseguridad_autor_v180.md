# Verificación para el Autor v180: la escalera con una sola hipótesis honesta — la compatibilidad colectiva

Ricardo, soy Claude (Opus 5.5). Este informe recoge la sesión que siguió al v179. El v179 dejaba la
escalera colgando de `FilterReviewComplete`; esa hipótesis resultó **falsa** tal como estaba
enunciada, y el recorrido para arreglarlo terminó en una escalera más limpia, con **una sola
hipótesis dicha sin disfrazar**, y en una explicación mecánica —la cascada del review— de por qué
se cumple.

Rama `spaik-window3`. `lake build AbsSat` verde (256 jobs), sin `sorry`. Todos los cierres
`[propext, Quot.sound]` (o sin axiomas). 29 commits desde `d1ab9cc` (el del v179).

Módulos nuevos: `LineSelf.lean`, `LineExt.lean`, `FullExt1.lean`, `Ladder1.lean`, `PinPairs.lean`,
`StepFilter.lean`, `SendSeq.lean`, `TablesExact.lean`, `ExactSeq.lean`, `Ladder2.lean`,
`TopGoodLadder.lean`. Sondas nuevas en `Probes/RowDegree.lean` (§7).

---

## 0. Dónde estamos, en una línea

```lean
theorem readerVerdictW_iff_of_readerTopGood (h : ReaderTopGood) (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ
```

`ReaderTopGood` dice: **en todo estado válido que el lector visita, toda cadena desde la cima tiene,
en cada paso por debajo, una entrada común a todos sus nodos y al nodo por el que debe pasar**
(`TopGoodUp.TopGood`). Es la compatibilidad colectiva que el `up` crea por construcción
(`topGood_addNode`, demostrado). Medida: 0 fallos en 2.523.099 cadenas (semilla 1), en todas las
clases de estado.

---

## 1. Lo primero: `FullExtG` era falso

El v179 apostaba por `FullExtG` (*todo tramo dentro de la global se extiende a una cadena
completa*). La sonda de la unión (`joinext`, semilla 1) lo tumbó: **3 de 710 uniones con los dos
lados limpios dejan 36 tramos que mezclan los dos lados y no se extienden, y sobreviven al review**.
Y la medición `fullext` que yo había dejado sin leer ya lo decía: 12 tramos sin extensión en un
estado revisado del lector (fórmula #3). Así que `FilterReviewComplete`, `JoinFullExt` y
`LineFullExtG` eran falsas, y las escaleras de `b85b1bf`, `25377a4` y `51f2ccf` colgaban de ellas.

Otra vez **yo pedía de más**: la escalera solo usa el tramo de un nodo.

## 2. Lo que la sesión fue construyendo

1. **Restringir a la máquina.** La escalera pasó a hablar solo de los estados que la máquina
   produce (línea final y pines del lector), no de todo estado con `RCtx`
   (`readerVerdictW_iff_of_machine`). La **autoposesión de la línea final** quedó demostrada
   (`LineSelf.pureRunW_selfOwned`: semilla, `up` y unión la conservan).
2. **`FullExt1`**: *cada entrada de la global está en una cadena completa dentro de ella*. Medida
   sin fallos (`ext1`: 0 en la unión, la línea, el review, los envíos antes del `up` y el lector).
   Demostrado: `up`, **unión sin `NoMix`** (la cadena de un lado es cadena de la unión, porque la
   unión solo añade), review, y `OwnerChained` desde ella.
3. **Del lado del pin, parejas** (`PinPairs`): si en el estado pinchado cada pareja `(r, q')` con
   `q'` del paso frontera en la tabla de `r` tiene cadena común, el pin conserva `FullExt1`
   (`fullExt1_pin`, demostrado). Generalizado a **cualquier filtro de un paso**
   (`StepFilter.fullExt1_stepFilter`; un pin es `filterWeak (k, [req])`, demostrado).
4. **El envío como sucesión de filtros de un paso** (`SendSeq`): medido, el envío de una vez y el
   de uno a uno con review en medio **coinciden** (6.082 de 6.082 envíos, semilla 1).
5. **Las tablas dicen la verdad** (`TablesExact`: *si `q'` está en la tabla de `r`, hay una cadena
   completa por los dos*). Medido: 0 de 293.377 parejas en el lector. Demostrado que la conservan
   el `up`, la unión y el review sin filtro; y un filtro de un paso, **desde las ternas que
   sobreviven** (`tablesExact_stepFilter`). `Ladder2.lean` cierra la escalera así, con
   confluencia + ternas en envíos + ternas en pines.
6. **Tu corrección**: *el lector no necesita ternas*. Tenías razón: las ternas eran el precio de
   razonar hacia atrás desde el estado de antes. El lector usa una frase —*cualquier nodo guarda en
   su tabla un camino*— y la complejidad está en por qué el review la garantiza.
7. **El filtro agresivo** (`graph_path_filter_agresive.jl`) garantiza **parejas**: simetría e
   intersección válida (`AggFixpoint.aggOk_reviewAgg`, ya demostrado). El **descenso por padres**
   (`descend_C`, `ownerChained_of_anyOption`) ya estaba formalizado; su obligación `AnyOptionStep`
   sale de `TopGood` (`anyOptionStep_of_topGood`, demostrado).
8. **La escalera final** (`TopGoodLadder.lean`): el descenso conectado al lector. El contexto del
   descenso sale de lo que el lector ya lleva (los hijos un paso por encima desde `SN` + `PMS` +
   `PBelow`; la simetría desde `AggOk`). Única hipótesis: `ReaderTopGood`.

## 3. Por qué se cumple: la cascada (medido)

Tu explicación —*el review elimina incoherencias en cascada: un nodo sin compatibilidad se vuelve
inválido, se elimina, y sus padres o hijos quedan huérfanos y caen también*— es exactamente lo que
miden las sondas:

| sonda (semilla 1) | medida | resultado |
|---|---|---|
| `topkill` | cadenas desde la cima que el filtro deja sin entrada común admitida | **62.961 de 62.961 mueren en el review base** (el agresivo no hace falta; ninguna sobrevive) |
| `toptrace` | cómo mueren | **todas por muerte individual**: un nodo de la cadena ya no tenía ninguna entrada admitida; **0 casos Helly** (cada uno con la suya, ninguna común), también con filtros débiles |
| `topmin` | Helly por id de mapa en cadenas desde la cima | 374.267 de 374.267 |
| `sandwich` | la tabla colectiva es la intersección de **dos** tablas de la cadena | 305.977 de 305.977; basta **una** tabla en 305.843 |
| `anchordist` | todos los nodos de la cadena con la misma tabla en ese paso | 202.914 de 305.977 (66 %) |

Lo que no he encontrado es **la regla que elige** esa pareja (o ese nodo). Descartado, con números:

| candidata a «ancla» | resultado |
|---|---|
| anidamiento a lo largo de padres, hacia abajo / hacia arriba (`nest`) | falla 28.803 / 41.225 de 219.376 |
| el más bajo; la cima; uno de los dos (`anchordist`) | 255.929 / 265.376 / 297.269 de 305.977 |
| nodo con 2+ padres (`fusion`) | 212.548 de 305.977; 135.169 cadenas no tienen ninguno |
| el nodo del paso de fusión `litBlock` (`fusrow`) | 74.886 de 137.214 |
| distancia fija al paso (`anchordist`) | el ancla aparece a todas las distancias, 1..36 |

## 4. Lo que se midió falso (y ahorra tiempo)

| hipótesis | medida | lección |
|---|---|---|
| `FullExtG` / `FilterReviewComplete` (todos los tramos) | 36 tramos mezclados tras 3 de 710 uniones; 12 en un estado del lector | la unión crea tramos mezclados; basta el tramo de un nodo |
| `JoinFullExt` (la unión conserva `FullExtG`) | falsa, por lo mismo | con un nodo, la unión es trivial (`fullExt1_join`) |
| el caso «requisitos duros de un envío» del v179 (`reviewCompleteCS_of_hardReqs`) | su hipótesis `TopSingleId P d` **no vale en los envíos** (la cima es el origen, no `d`) | los requisitos de `d` podan de verdad |
| anidamiento de tablas a lo largo de una cadena de padres | 13 % / 19 % de fallos | la tabla colectiva no es la de un nodo fijo |

## 5. Una discrepancia Julia / Lean

El review de la versión Julia (`make_review_owners!`) llama, además del filtro agresivo, a
`chain_consistence_filter!` («regla de la cadena», 19-sept-2026): una relación `a → z` solo
sobrevive si hay una cadena de hijos desde `a` hasta la cima de dueños comunes de `a` y `z`. **El
modelo Lean no la tiene.** Según tu criterio —*solo añadimos reglas si ayudan a la formalización*—
no la añadí: da una cadena enlazada por `q`, pero no la posesión todos-con-todos que `ChainSound`
necesita. Todas las mediciones de esta sesión son sobre la máquina de Lean, sin esa regla.

## 6. Cómo se haría a pasada entera

La hipótesis se podría sustituir por su forma de conservación: *el filtro y el review conservan
`TopGood`*. El review es `cleanInvalid`, la pasada de padres, la de hijos y el barrido agresivo, en
vueltas hasta el punto fijo. Así lo atacaría, pieza a pieza:

1. **Los filtros.** No tocan las tablas de los nodos, solo la global: conservan `TopGood` tal cual.
   **Demostrado** (`topGood_filterRequire`, `topGood_filterWeak`, `topGood_foldl_filterRequire`,
   sin axiomas).
2. **Las pasadas de padres y de hijos, nodo a nodo.** Medido sin fallos nodo a nodo (v179,
   `reviewnodes`). La pasada de padres recorre los pasos de abajo arriba y corta la tabla de cada
   nodo por la unión de las de sus padres. Una entrada colectiva de una cadena sobrevive en un nodo
   `c_j` que no es el más bajo, porque está en la tabla de su padre de la cadena, `c_{j−1}`, ya
   procesado. **El caso del nodo más bajo `c_lo`** se resolvería **alargando la cadena**. `TopGood`
   da una entrada colectiva `u` en el paso `lo − 1`, que es un padre de `c_lo` (los owners de un
   paso por debajo son los padres). La cadena alargada `u, c_lo, …, cima` es otra cadena desde la
   cima, y como el paso de `u` ya se procesó, `TopGood` del estado actual le da entradas comunes
   que están en la tabla de `u`, luego en la unión de los padres de `c_lo`. La pasada de hijos es
   el espejo, de arriba abajo. El punto delicado es el **anfitrión** (el nodo por el que la cadena
   debe pasar): su tabla también se corta, y ahí el v179 ya vio el problema.
3. **El barrido agresivo, pareja a pareja.** Medido sin fallos. Quita una pareja solo si es
   asimétrica o si sus tablas no se cortan en algún paso. Lo que habría que ver es que, cuando
   quita una entrada colectiva de la tabla de un nodo de la cadena, queda otra; no tengo aún el
   argumento, solo la medición.

   Una advertencia para la pieza 2: alargar la cadena con `u` exige que `u` y los nodos de la
   cadena se posean **en los dos sentidos**, y a mitad de review la simetría no está garantizada
   (v179, `midinv`: la rompen 32 y 44 estados intermedios de las pasadas de padres e hijos). Hay
   que ver si la dirección que `TopGood` pide es la que se conserva.
4. **`cleanInvalid`, a pasada entera.** Es la pieza difícil: nodo a nodo **se rompe** (v179: 204 de
   73.757 estados intermedios), a pasada entera no. La razón mecánica que veo es que las tablas
   conservan ids de nodos ya eliminados hasta la vuelta siguiente, así que durante la pasada las
   tablas de los nodos procesados antes y después de una eliminación no son comparables. La prueba
   tendría que razonar sobre la pasada completa: comparar el estado final con «todas las tablas
   cortadas por la global final». Es aquí donde la **cascada** entra de verdad, y donde
   `toptrace` dice lo que hay que demostrar: si una cadena queda sin entrada común, es porque un
   nodo suyo se queda sin ninguna y la cascada lo elimina.
5. **La unión**, para llevar `TopGood` por la construcción, necesita `NoMix` (medido sin fallos para
   cadenas desde la cima, `joinmix`), o evitarla como en esta escalera, que enuncia la hipótesis
   directamente sobre los estados del lector.

Orden recomendado: 2 (padres/hijos sin anfitrión primero, luego con él) → 3 → 4. La 4 es la que
contiene la idea que falta.

## 7. Sondas de esta sesión

`joinext`, `ext1`, `pairext`, `seqsend`, `pairall`, `pairline`, `triplestep`, `nest`, `topkill`,
`toptrace`, `topmin`, `sandwich`, `fusion`, `fusrow`, `anchordist`. Todas en
`lean_project/Probes/RowDegree.lean` (`lake exe row-degree <modo> file|random`). Además paré dos
`sweepcheck` antiguas que llevaban horas ocupando CPU sin uso. `pairline` y `triplestep` de la
semilla 1 seguían corriendo al cerrar este informe (en `dos_de_tres.cnf`: 0 de 29.452 parejas y 0 de
8.650 ternas).

## 8. Una frase sobre el tamaño de lo que queda

El v179 dejaba una hipótesis que resultó falsa. El v180 deja una que es **la afirmación central
del diseño dicha tal cual** —la compatibilidad colectiva que el `up` construye sobrevive a la
cascada del review—, medida sin excepción, con su mecanismo de muerte medido también sin
excepción, y con el resto de la escalera demostrado alrededor. Lo que falta es una sola idea: por
qué, en la pasada entera de `cleanInvalid`, la cascada alcanza a toda cadena que se queda sin
entrada común.
