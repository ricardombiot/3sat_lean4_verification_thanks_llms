# Resumen de las demostraciones (informes v126–v225)

4 de octubre de 2026. Este documento resume los cien últimos informes de la bitácora
(`docs/bitacora/verificacion_inseguridad_autor_v126.md` … `v225.md`) y los commits posteriores al v225 en la rama
`reader-stuck`. Recorre los tres proyectos Lean, explica qué cambió en cada etapa, qué quedó demostrado, qué vías se
atacaron y por qué se abandonaron.

**Cómo leerlo.**

* Cada afirmación lleva su estado: **demostrado** (teorema en Lean, sin `sorry`), **medido** (sonda en Julia o Lean,
  sin teorema), **falso** (contraejemplo medido o demostrado), **abierto** o **propuesto**.
* Las citas a Lean enlazan con el fichero y la línea del árbol actual (rama `reader-stuck`, commit `80dbd58`). Se
  comprobó que todos los nombres citados existen; ninguno de los tres proyectos contiene `sorry`.
* Los axiomas son los estándar: `[propext, Quot.sound]` en casi todo `AbsSat` y `AbsSatBin`, y
  `[propext, Classical.choice, Quot.sound]` en buena parte de `AbsSatBingo`.
* «vNNN» remite al informe de la bitácora con ese número.

---

## 0. Resumen ejecutivo

### 0.1 Los tres proyectos

| proyecto | carpeta | namespace | máquina que modela | informes | tamaño hoy |
|---|---|---|---|---|---|
| **AbsSat** | `lean_project/` | `AbsSat` | la máquina pura y *Improves* sobre el **mapa clásico** (cláusula = un paso con 7 filas), owners en **tablas por nodo** | v126–v191 | 277 ficheros, ~103 000 líneas |
| **AbsSatBin** | `lean/improves_bin/` | `AbsSatBin` | la misma máquina sobre el **mapa binario** (cláusula = 3 pasos de 2 nodos y una ventana prohibida) | v192–v198 | 124 ficheros, ~43 000 líneas |
| **AbsSatBingo** | `lean/improves_bingo/` | `AbsSatBingo` | la máquina bin con los owners como **grafo de aristas** por gpath; desde v217, también con **tríos prohibidos** (`FORBID = :on`) | v199–v225 | 156 ficheros, ~52 000 líneas |

`AbsSatBingo` importa de `AbsSatBin` la capa de base (CNF, mapa bin, identificadores) como dependencia de Lake
(`lean/improves_bingo/lakefile.toml`).

### 0.2 Lo demostrado sin ninguna hipótesis

| afirmación | proyecto | teorema |
|---|---|---|
| Si la máquina *Improves* termina sin estados, la fórmula es insatisfacible (la máquina no pierde soluciones) | AbsSat | [`pureRunW_ne_nil`](../lean_project/AbsSat/GraphPath/Model/ConservationImproves.lean#L207) |
| Toda respuesta UNSAT es correcta y toda respuesta SAT lleva un modelo comprobado | AbsSat | [`answer_unsat_sound`](../lean_project/AbsSat/GraphPath/Model/Answer.lean#L93), [`answer_sat_sound`](../lean_project/AbsSat/GraphPath/Model/Answer.lean#L101) |
| Un camino leído decodifica a un modelo | AbsSat | [`sat_of_denotS`](../lean_project/AbsSat/GraphPath/Model/NoDeadEndVerdict.lean#L51) |
| El conjunto de caminos de la máquina es **exactamente** el de certificados de φ | AbsSat | [`machineSet_complete`](../lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L74), [`machineSet_sound`](../lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L112), [`machineSet_nonempty_iff`](../lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L124) |
| La máquina no pierde ninguna solución parcial | AbsSat | [`pureStepsW_chain_below`](../lean_project/AbsSat/GraphPath/Model/ConservationPrefix.lean#L400) |
| No hay préstamo de caminos entre ramas en las uniones | AbsSat | [`noBorrow_at_insert`](../lean_project/AbsSat/GraphPath/Model/RunNoBorrow.lean#L531) |
| **La máquina decide 3-SAT con un lector con retroceso** | AbsSat | [`readerVerdictBT_iff`](../lean_project/AbsSat/GraphPath/Model/ReaderBT.lean#L267) |
| El lector sin retroceso, cuando termina, da un modelo | AbsSat, AbsSatBin | [`readerVerdictW_sound`](../lean_project/AbsSat/GraphPath/Model/ReaderExec.lean#L149), [`readerVerdictW_sound`](../lean/improves_bin/AbsSatBin/GraphPath/Model/ReaderExec.lean#L152) |
| Completitud de la máquina del mapa bin | AbsSatBin | [`completeness_pure`](../lean/improves_bin/AbsSatBin/SatMachine/PureProofs.lean#L126) |
| Simetría de todas las tablas de la máquina bin; el review agresivo coincide con el normal a lo largo del lector | AbsSatBin | [`symInv_reachable`](../lean/improves_bin/AbsSatBin/GraphPath/Model/SymMachine.lean#L214), [`reviewAgg_eq_review`](../lean/improves_bin/AbsSatBin/GraphPath/Model/PairInactive.lean#L742) |
| Todo estado de la máquina bin es un *kernel* | AbsSatBin | [`kernel_reachable`](../lean/improves_bin/AbsSatBin/GraphPath/Model/KernelUp.lean#L636) |
| Completitud de la máquina con grafo de owners | AbsSatBingo | [`machineVerdict_of_sat`](../lean/improves_bingo/AbsSatBingo/Model/Machine.lean#L502) |
| Completitud de la máquina con tríos prohibidos | AbsSatBingo | [`machineVerdictOn_of_sat`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnMachine.lean#L529) |
| Las dos respuestas definidas de la máquina con tríos son correctas | AbsSatBingo | [`verdictOn_certified`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnTop.lean#L336) |
| En todo join de la máquina con tríos, toda cima viva de la unión revisada está viva en un lado | AbsSatBingo | [`topSideAt_nil_line`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnNoPin.lean#L290) |
| **La máquina con tríos es exacta en todos sus estados si y solo si la fórmula no tiene familias fantasma** | AbsSatBingo | [`machineExact_iff`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnTight.lean#L509), y la forma débil [`machineExactW_iff`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L158) |
| **Clases sin hipótesis**: fórmulas con forma 2-CNF; bloques de ≤ 3 variables; dos bloques con una variable compartida; cadenas de tres bloques; `chain4_cross`; `chain5_cross`; la clase de cinco bloques `Chain5C` | AbsSatBingo | [`spineVerdictOn_iff_of_twoLike`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnMaj.lean#L1016), [`machineExact_of_blocks`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnBlock.lean#L285), [`machineExact_of_sep2`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnSep.lean#L671), [`machineExact_threeChain`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain.lean#L959), [`machineExact_chain4Cross`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4X.lean#L289), [`machineExact_chain5Cross`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L395), [`machineExact_of_chain5C`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5C.lean#L655) |
| En esas clases el lector no retrocede (cualquier lectura acaba en una solución) | AbsSatBingo | [`reader_on_twoLike`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnRead.lean#L181), [`reader_chain4Cross_any`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4X.lean#L293), [`reader_sep_chain5Cross_full`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L404) |

### 0.3 Lo que sigue abierto

La pregunta de fondo no ha cambiado en cien informes: **¿basta lo que la máquina guarda (compatibilidades por
parejas, y desde v217 tríos prohibidos) para que el lector sin retroceso nunca se atasque?** Ha cambiado su forma:

* en AbsSat quedó en enunciados sobre la máquina (`CommonOwner`, `GhostsLine`, `PairHelly`, `KeptOwn`…), y en la
  semilla 11 se vio que el invariante por tramos (`SegGood`) es falso aunque el lector acierte (v190);
* en AbsSatBin quedó en `M1aAll` y `M1bLowOwn` (`KFix`) en cada join (v196–v198);
* en AbsSatBingo quedó, por primera vez, en un **enunciado sobre la fórmula** (`PhantomAtW`, sin familias fantasma),
  equivalente a la exactitud de la máquina (v222–v223), y se demuestra **clase a clase** (cadenas de bloques, hasta
  seis bloques dadas las líneas tras el último commit).

### 0.4 Línea de tiempo

| fechas (2026) | informes | rama | proyecto | hipótesis vigente al cierre |
|---|---|---|---|---|
| 17–20 sep | v126–v173 | `spaik` | AbsSat | de `NoBorrow` a `CommonOwner`, `GhostsLine`, `LivePinUp`, `SideKeepFar`… y en *ImprovesCima*, `PinnedUnionInhabited` |
| 22–23 sep | v174–v181 | `spaik-window3` | AbsSat | decide con retroceso sin hipótesis; sin retroceso bajo `ReaderSegGood` |
| 24 sep | v182–v183 | `clean-two-phase` | AbsSat | `hStart` + Hellys de un paso |
| 24 sep | v184–v185 | `review-symmetric` | AbsSat | `RoundExact` |
| 24–25 sep | v186–v191 | `pair-mode` | AbsSat | `PairExact` + `KeptOwn`; `SegGood` falso en la semilla 11 |
| 25–27 sep | v192–v198 | `improves_bin`, `lean_improves_bin` | AbsSatBin | `M1aAll` + `KFix` |
| 27–28 sep | v199–v202 | `graph_owners` | AbsSatBingo | `union` (+ `skip`) |
| 28 sep | v203–v204 | `star-rule` | AbsSatBingo | `JoinStarCore` |
| 28 sep | v205–v206 | `row-tags` | AbsSatBingo | (máquina etiquetada: completitud) |
| 29 sep–3 oct | v207–v225 | `reader-stuck` | AbsSatBingo | `PhantomAtW` (fórmula); clases demostradas |

---

## 1. Vocabulario común

* **Mapa.** Grafo por pasos que codifica φ. En el **mapa clásico** (2n + m + 2 pasos): paso `2v` = «v = 0 / v = 1»,
  paso `2v+1` = la negación (requiere el valor opuesto en `2v`), una fusión, un paso por cláusula con sus **siete
  filas** (las asignaciones que la satisfacen) y una fusión final. En el **mapa bin** (2n + 3m + 3 pasos): una fusión
  raíz, las variables, una fusión media, **tres pasos de dos nodos por cláusula** (cada uno copia un literal) y una
  **ventana prohibida** `(0,0,0)` que codifica la disyunción.
* **Nodo de camino** (`PathNodeId`). Un nodo del mapa más su historia: primero `(id, padre)`, y desde
  `spaik-window3` una **ventana de tres** `(id, parent_id, gparent_id)`.
* **Estado** (`GPathM` en AbsSat y AbsSatBin, `GPathB` en AbsSatBingo). Los nodos vivos con, en AbsSat/AbsSatBin, una
  **tabla de owners** por nodo (con qué es compatible en cada paso), y en AbsSatBingo un **grafo de aristas**.
* **Operaciones.** El **UP** (`addNode`/`upOn`) añade una fila; el **join** une los estados que llegan a la misma
  clave; el **filtro** o **pin** fija nodos de mapa (requisitos o elecciones del lector); el **review** poda hasta el
  punto fijo (limpieza, coherencia con padres e hijos, barrido agresivo o regla de parejas, y desde v217 la regla de
  tríos).
* **Lector.** Fija un paso con elección, revisa y sigue. **Con retroceso** puede deshacer un pin; **sin retroceso**
  no.
* **Cadena / camarilla.** Un nodo por paso, compatibles dos a dos y enlazados; es la rama de una asignación.
* **Familia fantasma** (v222). Una estructura cerrada por las reglas de la máquina, hecha de ramas de un conjunto de
  asignaciones `P0`, que no es de ramas del subconjunto que exige una fijación. Es una propiedad de la fórmula, no de
  la máquina.

---

## 2. Proyecto AbsSat (`lean_project/`)

### 2.0 Antes del v126 (fuera de los cien informes)

Por el historial de git: la máquina pura (`SatMachinePure`) con `run_pure_eq_driver`, completitud y solidez
condicional (13 sep); la semántica por subconjuntos de caminos parciales y la reducción de la prueba de vacío
(v96); `NoDeadEnd` y la clausura de borrado (v97–v101); la máquina *Improves* con **requisitos débiles** que no pierde
soluciones (v105–v110, una sola prueba de conservación para tres filtros); el **review agresivo** y su regla de parada
(simetría y consistencia de pares, v116–v121); `PinExact` y la conmutación exacta «fijar = construir la rama»
(v119–v124). El v126 parte de ahí.

### 2.1 Rama `spaik`: la máquina *Improves* (v126–v173)

#### a) Ramas, préstamos y validez hereditaria (v126–v128)

| resultado | estado | teorema |
|---|---|---|
| La rama de las fijaciones `P` vive, línea a línea, dentro de la máquina completa | demostrado | [`branchRun_embedded`](../lean_project/AbsSat/GraphPath/Model/BranchLines.lean#L392) |
| La rama es compatible con sus fijaciones | demostrado | [`branchRun_compat`](../lean_project/AbsSat/GraphPath/Model/BranchCompat.lean#L203) |
| Veredicto bajo **`NoBorrow`** (toda elección viva tiene una rama válida por sí misma) | demostrado | [`sat_of_noBorrow`](../lean_project/AbsSat/GraphPath/Model/BranchReader.lean#L90) |
| Validez hereditaria de fijaciones (`HPV`): semilla, filtro, UP y línea la conservan | demostrado | [`sat_of_hpv`](../lean_project/AbsSat/GraphPath/Model/Hereditary.lean#L226) |
| Veredicto bajo **`JoinsSplit`** (la unión reparte sus elecciones entre sus lados) | demostrado | [`sat_of_joinSplit`](../lean_project/AbsSat/GraphPath/Model/HereditaryRun.lean#L180) |

Medido (v128): las uniones no prestan elecciones (2,5 M owners, 0 prestados). El único caso que no cierra la inducción
es el `join`.

#### b) Un solo obstáculo: de pares a tríos (v129–v131)

* **v129**: `SpcStable` (v122), la conservación de `PairChain` (v123) y `JoinSplit` piden lo mismo: un testigo común a
  **tres** objetos. Demostrada la mitad de nodos: [`slice_of_exclusive_top`](../lean_project/AbsSat/GraphPath/Model/JoinProvenance.lean#L148) (la rebanada de un nodo que un lado no
  tiene vive en el otro).
* **v130**: el identificador fija el testigo: [`parents_id_eq`](../lean_project/AbsSat/GraphPath/Model/ParentWitness.lean#L38), [`par_witness_triple`](../lean_project/AbsSat/GraphPath/Model/ParentWitness.lean#L86) (con un solo padre, la
  consistencia de pares da el trío) y [`owners_below_unique`](../lean_project/AbsSat/GraphPath/Model/ParentWitness.lean#L143). **Falso**: la rebanada del ancla como soporte (72 de
  15 180 en K4). Conclusión: el salto de pares a tríos es «el precio de la abstracción»: con un solo padre por nodo el
  identificador sería un camino.
* **v131**: invariante de ejecución incondicional [`runWithin_of_wf`](../lean_project/AbsSat/GraphPath/Model/RunEnv.lean#L562) y [`shared_tables_common_bound`](../lean_project/AbsSat/GraphPath/Model/RunEnv.lean#L512). La
  «puerta A» (`JoinSplit` por entradas) cae por medida (1 328 pares ajenos). Aparece la forma mínima: [`sat_of_noDeadEnd`](../lean_project/AbsSat/GraphPath/Model/NoDeadEndVerdict.lean#L61).

#### c) El descenso y `CommonOwner` (v132–v134)

* [`extend_of_common_owner`](../lean_project/AbsSat/GraphPath/Model/Descent.lean#L44): extender una cadena parcial **es** encontrar un owner común; las otras seis
  condiciones salen de los invariantes. El UP mantiene el descenso ([`noDeadEnd_addNode`](../lean_project/AbsSat/GraphPath/Model/DescentUp.lean#L267)); en el join, los picks
  viven en el lado de su ancla ([`picks_left_of_exclusive_anchor`](../lean_project/AbsSat/GraphPath/Model/DescentJoin.lean#L151), [`soundFrom_left_of_entries`](../lean_project/AbsSat/GraphPath/Model/DescentJoin.lean#L229)).
* **`CommonOwner`** ([`CommonOwner`](../lean_project/AbsSat/GraphPath/Model/Descent.lean#L261)) y el veredicto [`sat_of_commonOwner`](../lean_project/AbsSat/GraphPath/Model/NoDeadEndVerdict.lean#L85). La máquina mantiene
  2-consistencia; el descenso pide k-consistencia.
* **Falsas** (cinco reglas locales): transitividad de la posesión (52 720 de 380 746), su forma adyacente, «el vecino
  decide», rebanada = camarilla, candidatos anidados.
* v134 separa dos afirmaciones: **SAT con camino** (certificado, sin hipótesis) y **SAT desde la validez** (bajo
  `CommonOwner`).

#### d) Exactitud de las tablas y conjunto de certificados (v135–v137)

* v135: [`tablesComplete`](../lean_project/AbsSat/GraphPath/Model/Exactness.lean#L67) (la máquina nunca olvida) sin hipótesis; `TablesSound` en semilla, UP y join
  ([`tablesSound_addNode`](../lean_project/AbsSat/GraphPath/Model/Exactness.lean#L119), [`tablesSound_join`](../lean_project/AbsSat/GraphPath/Model/Exactness.lean#L240)). Corrección: la exactitud por entradas **no** implica
  `CommonOwner`.
* v136: el conjunto de la máquina es el de certificados ([`machineSet_nonempty_iff`](../lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L124)); el veredicto se reduce a
  `ValidDecidesEmpty` ([`ValidDecidesEmpty`](../lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L138), [`verdict_iff`](../lean_project/AbsSat/GraphPath/Model/CertificateSet.lean#L156)), más débil que `CommonOwner`. Lectura en
  compilación de conocimiento (DNNF).
* v137 (solo medida): el join une **futuros distintos** (68–92 %), así que no es una fusión de OBDD; aun así no fabrica
  pasados. Ruta OBDD descartada.

#### e) Distributividad, oráculo, rebanadas y `GhostsLine` (v138–v141)

* v138: el envío distribuye sobre la unión (0 diferencias en ~90 000 comprobaciones). [`split_branch`](../lean_project/AbsSat/GraphPath/Model/SendDistrib.lean#L454),
  [`sat_of_reviewJoin`](../lean_project/AbsSat/GraphPath/Model/ReviewJoin.lean#L570).
* v139: [`reviewJoin_of_split`](../lean_project/AbsSat/GraphPath/Model/SupportSplit.lean#L312) (`SupportCover`); **cada estado = unión de los caminos del oráculo** (medido);
  [`sat_of_oracle_path`](../lean_project/AbsSat/GraphPath/Model/OraclePath.lean#L120) sin hipótesis; [`entry_on_linked_chain`](../lean_project/AbsSat/GraphPath/Model/LinkedChain.lean#L122). **Falsas**: cadena enlazada = camino,
  Helly-3, rebanada cerrada por enlaces. Hipótesis de **anchura** (Yannakakis).
* v140: invariante de rebanadas ([`run_slices`](../lean_project/AbsSat/GraphPath/Model/SliceInvariant.lean#L171)); medido que el review mata todas las «fantasmas» (3,02 M) y
  cómo; [`tablesSound_of_ghosts`](../lean_project/AbsSat/GraphPath/Model/RoundInvariant.lean#L104).
* v141: veredicto con **`GhostsLine`** declarada ([`GhostsLine`](../lean_project/AbsSat/GraphPath/Model/RoundInvariant.lean#L280), [`sat_of_ghosts`](../lean_project/AbsSat/GraphPath/Model/RoundInvariant.lean#L336)).

#### f) La respuesta certificada y el lector (v142–v145)

* v142: la máquina responde UNSAT, SAT con certificado o «no sé»; las dos primeras son correctas **sin hipótesis**
  ([`answer_unsat_sound`](../lean_project/AbsSat/GraphPath/Model/Answer.lean#L93), [`answer_sat_sound`](../lean_project/AbsSat/GraphPath/Model/Answer.lean#L101)); nunca «no sé» bajo `GhostsLine` + `ReaderPinExact`
  ([`answer_ne_unknown`](../lean_project/AbsSat/GraphPath/Model/ReaderComplete.lean#L295)).
* v143: fijar a la vez = fijar en secuencia ([`seq_eq_all`](../lean_project/AbsSat/GraphPath/Model/SeqPin.lean#L187), [`multiPinExact`](../lean_project/AbsSat/GraphPath/Model/SeqPin.lean#L263)).
* v144: los requisitos débiles no cambian las tablas (medido); [`chain_of_ids`](../lean_project/AbsSat/GraphPath/Model/PinExtends.lean#L125) (un estado válido con un mapa
  por paso es un camino); veredicto bajo `PinExtends` ([`verdict_iff_pinExtends`](../lean_project/AbsSat/GraphPath/Model/PinExtends.lean#L256)).
* v145: de abajo arriba la única elección es el valor de una variable ([`decided_off_var`](../lean_project/AbsSat/GraphPath/Model/PinUp.lean#L118)); veredicto bajo
  **`LivePinUp`** ([`LivePinUp`](../lean_project/AbsSat/GraphPath/Model/PinUp.lean#L221), [`verdict_iff_up`](../lean_project/AbsSat/GraphPath/Model/PinUp.lean#L329)).

#### g) Uniones y construcción (v146–v148)

* `TripleA` (regla de ternas a través del valor vivo): **falsa**. `SideCover` ([`entry_side`](../lean_project/AbsSat/GraphPath/Model/JoinSide.lean#L32),
  [`cover_of_sideCover`](../lean_project/AbsSat/GraphPath/Model/JoinSide.lean#L76)), medido en 33,2 M entradas.
* v147: «estar en un camino de una rama» es un soporte ([`sup_through`](../lean_project/AbsSat/GraphPath/Model/PartSplitReal.lean#L217)); la partición sale de los caminos
  ([`splitOk_of_paths`](../lean_project/AbsSat/GraphPath/Model/PartSplitReal.lean#L285)); veredicto bajo `RunPaths` ([`sat_of_paths`](../lean_project/AbsSat/GraphPath/Model/PartSplitReal.lean#L419)).
* v148: **no se pierde ninguna solución parcial** ([`pureStepsW_chain_below`](../lean_project/AbsSat/GraphPath/Model/ConservationPrefix.lean#L400)) y **no hay préstamo en las
  uniones** ([`noBorrow_at_insert`](../lean_project/AbsSat/GraphPath/Model/RunNoBorrow.lean#L531)), los dos sin hipótesis. Balance: cuatro rutas (lectura, exactitud,
  construcción, pares) que desembocan en «fijar y revisar conserva lo que hay».

#### h) Historia, cláusulas y conmutación de pins (v149–v160)

* v149: todo camino es una solución ([`path_is_solution`](../lean_project/AbsSat/GraphPath/Model/LiveSolution.lean#L51)); cláusulas decididas ([`decided_clause_holds`](../lean_project/AbsSat/GraphPath/Model/LiveSolution.lean#L165)),
  propagación unitaria ([`unit_forced`](../lean_project/AbsSat/GraphPath/Model/LiveSolution.lean#L209)), filas testigo ([`row_bit_prefix`](../lean_project/AbsSat/GraphPath/Model/LiveSolution.lean#L286), [`entry_witness`](../lean_project/AbsSat/GraphPath/Model/LiveSolution.lean#L340)). Falta la
  «elección común».
* v150: invariante `SoundAt` conservado por semilla, unión, UP y review; los débiles no cambian nada (`WeakNoop`);
  veredicto bajo `PinPairSoundAt` ([`sat_of_pinPairs`](../lean_project/AbsSat/GraphPath/Model/WeakNoop.lean#L319)).
* v151–v152: las tablas hacia los literales **son** la compatibilidad entre soluciones parciales
  ([`owns_iff_witness`](../lean_project/AbsSat/GraphPath/Model/RunHistory.lean#L173)); veredicto bajo `ClauseWitness` ([`sat_of_clauseWitness`](../lean_project/AbsSat/GraphPath/Model/RunHistory.lean#L279)); lo que aporta el review en
  la fila ([`clause_review`](../lean_project/AbsSat/GraphPath/Model/ClauseReview.lean#L326)).
* v153–v156: fijar es un requisito que la historia ya aplicó ([`pinIds_branch`](../lean_project/AbsSat/GraphPath/Model/PinHistory.lean#L202), [`pinCommutes_of_one`](../lean_project/AbsSat/GraphPath/Model/PinHistory.lean#L402));
  fijar atraviesa un envío ([`pin_send`](../lean_project/AbsSat/GraphPath/Model/PinSend.lean#L205)); **la etapa de variables queda demostrada** ([`pinJoinVar`](../lean_project/AbsSat/GraphPath/Model/PinVar.lean#L476),
  [`var_glue`](../lean_project/AbsSat/GraphPath/Model/PinVar.lean#L327)).
* v157–v160: la etapa de cláusulas se reduce a un cambio de valor (`FlipSat`, [`sat_of_flipSat`](../lean_project/AbsSat/GraphPath/Model/PinClause.lean#L384)), luego a
  `SideKeep` y a las incoherencias **anchas** (`SideKeepFar`, [`sat_of_sideKeepFar`](../lean_project/AbsSat/GraphPath/Model/PinClause.lean#L613)).

#### i) Muerte directa, testigos y validez (v161–v165)

* v161–v163: los triángulos repartidos mueren siempre en una fila de cláusula (medido); muerte directa demostrada
  ([`direct_death`](../lean_project/AbsSat/GraphPath/Model/PinDeath.lean#L83)); veredicto bajo `RowWitnessAt` ([`sat_of_rowWitness`](../lean_project/AbsSat/GraphPath/Model/PinDeath.lean#L156)).
* v164: **`SemWitnessAt` es falsa** (caso construido de 23 variables, comprobado por fuerza bruta); el testigo con cierre
  `ClosedWitnessAt` resiste ([`sat_of_closedWitness`](../lean_project/AbsSat/GraphPath/Model/PinDeath.lean#L557)); el lector sin retroceso como programa
  ([`readerVerdictW_sound`](../lean_project/AbsSat/GraphPath/Model/ReaderExec.lean#L149)).
* v165: ruta C, validez en lugar de exactitud; `SendPinAt` sin hipótesis ([`sendPin`](../lean_project/AbsSat/GraphPath/Model/HereditaryValid.lean#L472)); veredicto bajo
  `ValidSideAt` ([`sat_of_validSideOnly`](../lean_project/AbsSat/GraphPath/Model/HereditaryValid.lean#L481)).

#### j) La máquina `ImprovesCima` (v166–v173)

Una pasada más en el review de la unión: **la regla de la cima** (recortar la unión a lo que lleva el lado de cada cima
y revisar). Medido: no cambia ningún resultado.

* No pierde soluciones ([`ChainSound_cimaSweep`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L733)); la familia de una cima buena es soporte del envío de su lado
  ([`valid_pinned_of_famSide`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L1898)); `TopValidAt` sin hipótesis ([`topValid_cima`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L1973)).
* v169: el **filtro del triángulo** del autor como test computable: si pasa, la fórmula es satisfacible, sin hipótesis
  ([`sat_of_filterCheck`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L3306)); 3 071 de 3 071 uniones reales dan `true`.
* v170–v172: una cadena sana **es** un soporte ([`sup_of_chainSound`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L846)); **conservación de `ImprovesCima`**
  ([`cima_chain_below`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L1516)); lo que queda equivale al veredicto: `RulePreservesValidity`
  ([`sat_of_rulePreserves`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L2442), [`rulePreserves_of_genuine`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L2325)).
* v173: todo queda en `PinnedUnionInhabited` ([`sat_of_pinnedUnionInhabited`](../lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean#L2451)): «una unión fijada viva contiene una
  cadena». Propuesta: subir la ventana del identificador a tres.

### 2.2 Rama `spaik-window3`: ventanas de tres (v174–v181)

* **v174, el resultado grande**: [`readerVerdictBT_iff`](../lean_project/AbsSat/GraphPath/Model/ReaderBT.lean#L267), la máquina decide con un lector **con retroceso**, sin
  hipótesis. Salió de no tirar la cadena que la conservación ya construía ([`pureRunW_full_chain`](../lean_project/AbsSat/GraphPath/Model/ConservationImproves.lean#L196)). El retroceso
  no se paga cuando no hace falta ([`readerVerdictBT_of_readerVerdictW`](../lean_project/AbsSat/GraphPath/Model/ReaderBT.lean#L253)), y medido no hace falta nunca. La
  obligación pasa de la corrección al **coste** (que el lector sin retroceso baste).
* La máquina es **exacta en 2-consistencia e inexacta desde 3** (`SupportedG`, `TablesSound` al 100 %;
  [`path_consistent_witness`](../lean_project/AbsSat/GraphPath/Model/Descent.lean#L1103)). Cinco hipótesis de tres objetos cayeron. El pin se propaga dos niveles
  ([`pid_of_three_pins`](../lean_project/AbsSat/GraphPath/Model/Descent.lean#L745)); el lector de arriba abajo usa la mitad de pines ([`readerVerdictWTop_sound`](../lean_project/AbsSat/GraphPath/Model/ReaderTop.lean#L124)).
  Hueco aislado: `TriplePin` ([`TriplePin`](../lean_project/AbsSat/GraphPath/Model/SupportedRun.lean#L109), [`shared_pin_witness`](../lean_project/AbsSat/GraphPath/Model/SupportedRun.lean#L219)).
* v175: el lector no añade nada al problema: singles ← pares ← tríos ([`readerVerdictW_of_tablesSound`](../lean_project/AbsSat/GraphPath/Model/ReaderChain.lean#L278),
  [`rootChained_pin_of_tablesSound`](../lean_project/AbsSat/GraphPath/Model/ReaderChain.lean#L616)). `AncOwned` vale en el UP ([`ancOwned_addNode`](../lean_project/AbsSat/GraphPath/Model/AncestorOwned.lean#L181)) y es falsa tras el join
  (22,8 %).
* v176: `TablesSound` por la construcción: join y UP ([`tablesSound_join`](../lean_project/AbsSat/GraphPath/Model/TablesSoundBuild.lean#L59)), pasos sin requisitos e impares; el
  residuo, un nodo y una elección binaria ([`realizes_pin_of_singleId`](../lean_project/AbsSat/GraphPath/Model/TablesSoundBuild.lean#L486), [`pinCompatChain_of_singleId`](../lean_project/AbsSat/GraphPath/Model/ReaderChain.lean#L934)).
* v177–v178: la ruta sin ternas `PinAlive` ([`PinAlive`](../lean_project/AbsSat/GraphPath/Model/PinAliveChain.lean#L84), [`readerVerdictW_iff_of_pinAlive`](../lean_project/AbsSat/GraphPath/Model/PinAliveChain.lean#L251),
  [`pinAlive_iff_ownerChained`](../lean_project/AbsSat/GraphPath/Model/PinAliveChain.lean#L2397)); **los pasos de cláusula caen** ([`ownerChained_filterAllAgg_of_reqSatisfying`](../lean_project/AbsSat/GraphPath/Model/OwnerChainedBuild.lean#L352):
  el filtro de un envío propaga lo que la cima fijó); el pin no invalida ningún nodo, por `rfl`
  ([`isValidNode_filterRequire`](../lean_project/AbsSat/GraphPath/Model/PinAliveChain.lean#L433)); escalera hasta `DescentStepOwned` ([`tableHasOwnedChain_of_descentStep`](../lean_project/AbsSat/GraphPath/Model/OwnerChainedBuild.lean#L1350)).
* v179: `DescentStepOwned` **era falso** tal como estaba escrito ([`not_descentStepAny`](../lean_project/AbsSat/GraphPath/Model/OwnerChainedBuild.lean#L1198)); escalera bajo
  `FilterReviewComplete` ([`readerVerdictW_iff_of_filterReviewComplete`](../lean_project/AbsSat/GraphPath/Model/ReaderLadder.lean#L79)); el UP crea la compatibilidad colectiva
  ([`topGood_addNode`](../lean_project/AbsSat/GraphPath/Model/TopGoodUp.lean#L131)).
* v180: `FullExtG` **falso** (36 tramos mezclados tras la unión); escalera bajo `ReaderTopGood`
  ([`readerVerdictW_iff_of_readerTopGood`](../lean_project/AbsSat/GraphPath/Model/TopGoodLadder.lean#L86)); autoposesión de la línea final ([`pureRunW_selfOwned`](../lean_project/AbsSat/GraphPath/Model/LineSelf.lean#L196)); la cascada
  del review, medida.
* v181: las dos pasadas de coherencia, enteras ([`pstate_reviewParents`](../lean_project/AbsSat/GraphPath/Model/PassCtx.lean#L907), [`pstate_reviewSons`](../lean_project/AbsSat/GraphPath/Model/PassSons.lean#L428)); escalera sin
  anfitrión bajo `ReaderSegGood` ([`readerVerdictW_iff_of_readerSegGood`](../lean_project/AbsSat/GraphPath/Model/TopGoodLadder.lean#L166)). Propuesta: `cleanInvalid` en dos fases.

### 2.3 Rama `clean-two-phase` (v182–v183)

* **Adoptado en Julia y en Lean**: `cleanInvalid₂` (purga hasta el punto fijo, después un solo corte)
  ([`cleanInvalid₂`](../lean_project/AbsSat/GraphPath/Model/GPathM.lean#L326)). Sin ids muertos ([`owners_live_cleanInvalid₂`](../lean_project/AbsSat/GraphPath/Model/CleanTwoPhase.lean#L118)), todo nodo válido
  ([`isValidNode_cleanInvalid₂`](../lean_project/AbsSat/GraphPath/Model/CleanTwoPhase.lean#L256)), no pierde soluciones ([`ChainSound_cleanInvalid₂`](../lean_project/AbsSat/GraphPath/Model/CleanInvalid.lean#L627)); 0 estados distintos de
  la versión secuencial. Las pasadas quedan sin versiones «vivas» ([`pstateG_reviewPass`](../lean_project/AbsSat/GraphPath/Model/PassPlain.lean#L280)); el mecanismo local de
  pérdida de compatibilidad ([`lost_parents`](../lean_project/AbsSat/GraphPath/Model/CompatLoss.lean#L89)).
* v183: `SegExact` (todo tramo se extiende a una cadena) implica `SegGood` y el review lo conserva
  ([`segGood_of_segExact`](../lean_project/AbsSat/GraphPath/Model/SegExact.lean#L47), [`segExact_reviewAgg`](../lean_project/AbsSat/GraphPath/Model/SegExact.lean#L99), [`segExact_addNode`](../lean_project/AbsSat/GraphPath/Model/SegExactUp.lean#L97)); la unión **mezcla** y los tramos
  mezclados mueren en el primer filtro; escalera bajo `hStart` y tres Hellys de un paso
  ([`readerVerdictW_iff_of_helly`](../lean_project/AbsSat/GraphPath/Model/SegExactAdm.lean#L583), [`gapExactFar_of_steps`](../lean_project/AbsSat/GraphPath/Model/SegExactAdm.lean#L390)).

### 2.4 Rama `review-symmetric` (v184–v185)

* **Adoptado**: el review simétrico (espejo: si `x` pierde a `r`, `r` pierde a `x`). Mismos estados en Julia, en el
  modelo y en el ejecutable (500/500). La simetría pasa a ser invariante ([`OwnSymmetric_reviewNode`](../lean_project/AbsSat/GraphPath/Model/SymInvariant.lean#L37),
  [`aggPair_asym_never`](../lean_project/AbsSat/GraphPath/Model/SymInvariant.lean#L315)) y las pasadas quedan sin hipótesis ([`pstateG_reviewPass'`](../lean_project/AbsSat/GraphPath/Model/SymInvariant.lean#L666)); S1′ demostrado
  ([`commonLoss_round`](../lean_project/AbsSat/GraphPath/Model/SymInvariant.lean#L927)). Escalera bajo `PinFirstRound`, `LaterValid`, `AggInactive`
  ([`readerVerdictW_iff_of_pinDoomed`](../lean_project/AbsSat/GraphPath/Model/PinDoomed.lean#L365)).
* v185: escalera bajo `RoundExact` ([`readerVerdictW_iff_of_roundExact`](../lean_project/AbsSat/GraphPath/Model/RoundExact.lean#L87)). Medido: los tramos condenados tienen
  **siempre** un conflicto de pareja. **Falso**: que las tablas sean subárboles, intervalos o laminares; la vía de la
  **mayoría** (Baker–Pixley) cae con dos casos vivos exactos. Propuesta: la regla de parejas tras la limpieza.

### 2.5 Rama `pair-mode` (v186–v191)

* **Adoptado**: la regla de parejas tras la limpieza (`cleanPair`). En Julia: 80/80 iguales, la rama inconsistente del
  agresivo pasa de 19 238 disparos a 0. En Lean: no pierde soluciones ([`ChainSound_cleanPair`](../lean_project/AbsSat/GraphPath/Model/CleanInvalid.lean#L821)), simetría
  ([`OwnSymmetric_cleanPair`](../lean_project/AbsSat/GraphPath/Model/SymInvariant.lean#L231)), punto fijo ([`pairFixed_cleanPair`](../lean_project/AbsSat/GraphPath/Model/PairHelly.lean#L98)) y **`AggInactive` pasa a teorema**: en el
  punto fijo el barrido agresivo es la identidad ([`aggInactive_of_revOk`](../lean_project/AbsSat/GraphPath/Model/PairHelly.lean#L205), [`aggSweep_eq_self`](../lean_project/AbsSat/GraphPath/Model/PairHelly.lean#L195)). Escalera bajo
  `PairHelly` ([`readerVerdictW_iff_of_pairHelly`](../lean_project/AbsSat/GraphPath/Model/PairHelly.lean#L249), [`pairHelly_of_segThroughPin`](../lean_project/AbsSat/GraphPath/Model/PairHelly.lean#L358)).
* v187–v189: alargar un tramo un paso cada vez ([`segGood_of_oneStep`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L167)); Helly de dos elementos
  ([`helly_two`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L222)) y por cajas ([`helly_box`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L361), [`req_shared`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L426)); triángulo con el extremo reducido a `Tri3`
  ([`triTop_of_tri3`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L678)); el testigo viene de la historia ([`witUp_of_segGood`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L781)); escaleras bajo `Survives` y
  `KeptOwn` ([`readerVerdictW_iff_of_survives`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L808), [`survives_of_pinned_owner`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L868), [`link_cleanPair`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L1062),
  [`readerVerdictW_iff_of_keptOwn`](../lean_project/AbsSat/GraphPath/Model/OneStep.lean#L1175)).
* **v190, hallazgo**: en la semilla 11, fórmula #1 (`Probes/cnf/seed11_1_segexact_start.cnf`), **`hStart` y `SegGood`
  son falsos** aunque el lector acierta; `TriExact` falla (87 de 26 413 sin muestreo) y `PairExact` no (0 de 6 742).
  Los prefijos (tramos desde el paso 0) nunca fallan.
* v191: anatomía: un **trío muerto hecho de tres parejas vivas** (la cláusula `x2 ∨ x4 ∨ x6`, tres caras del cubo que
  solo se cortan en la `000`). Ninguna regla correcta sobre parejas puede quitarlo; la «regla del hueco» propuesta en
  el chat era incorrecta. Propuesta B: llevar `PairExact` por la inducción.

---

## 3. Proyecto AbsSatBin (`lean/improves_bin/`): el mapa binario

### 3.1 Motivo y migración (v192–v194)

* v192 (teórico): con dos nodos por paso, el Helly de un paso es el lema de dos elementos; desaparecen las cajas y el
  hueco `000`; queda solo el triángulo con el extremo. No elimina el trío muerto de la semilla 11 (el hueco se muda a
  las ventanas).
* v193 (Julia, `julia/improves_bin`): `GraphMapBin`, 73/73 veredictos y soluciones iguales al clásico y al exhaustivo;
  cuatro errores documentados en `docs/bitacora/bin-map_informe_errores.md`; quitar el filtro agresivo (identidad en
  el punto fijo) acelera ~3,5×.
* v194 (Lean, rama `lean_improves_bin`, 26 commits): proyecto independiente; `Lit.binStep` para que ningún índice
  heredado compile; `scripts/index_lint.py`; diferencial del mapa contra Julia 74/74.

| resultado | estado | teorema |
|---|---|---|
| Completitud de la máquina bin (solo `Bounded`; `Sat` entra en un lema) | demostrado | [`completeness_pure`](../lean/improves_bin/AbsSatBin/SatMachine/PureProofs.lean#L126), [`pidOfAssign_not_prohibited`](../lean/improves_bin/AbsSatBin/GraphMap/CnfSelBin.lean#L251) |
| Solidez bajo `ClauseStepExact` (`HardStepExact` + `SkipExact`) | demostrado bajo hipótesis | [`soundness_pure`](../lean/improves_bin/AbsSatBin/SatMachine/PureProofs.lean#L132) |
| Toda la máquina es simétrica (invariante `CutClosed`) | demostrado | [`symInv_reachable`](../lean/improves_bin/AbsSatBin/GraphPath/Model/SymMachine.lean#L214), [`CutClosed`](../lean/improves_bin/AbsSatBin/GraphPath/Model/SymMachine.lean#L40) |
| Con la regla de parejas, review agresivo = normal | demostrado | [`reviewAgg_eq_review`](../lean/improves_bin/AbsSatBin/GraphPath/Model/PairInactive.lean#L742) |
| Escalera del lector: `PinChain` ⇐ `OtherBit` ⇐ `OtherBitSem` ⇐ `NoDeadEnd` ⇔ `KernelSplit` ⇐ `TriPin` | demostrado | [`readerVerdictW_iff_of_pinChain`](../lean/improves_bin/AbsSatBin/GraphPath/Model/ReaderPrefix.lean#L250), [`readerVerdictW_iff_of_otherBit`](../lean/improves_bin/AbsSatBin/GraphPath/Model/PinChainBin.lean#L154), [`readerVerdictW_iff_of_otherBitSem`](../lean/improves_bin/AbsSatBin/GraphPath/Model/OtherBitSem.lean#L153), [`readerVerdictW_iff_of_noDeadEnd`](../lean/improves_bin/AbsSatBin/GraphPath/Model/NoDeadEnd.lean#L296), [`readerVerdictW_iff_of_kernelSplit`](../lean/improves_bin/AbsSatBin/GraphPath/Model/KernelReader.lean#L309), [`readerVerdictW_iff_of_triPin`](../lean/improves_bin/AbsSatBin/GraphPath/Model/KernelSplit.lean#L397) |
| Solidez de la máquina desde `NoDeadEnd` + `RootValid`, sin `ClauseStepExact` | demostrado | [`soundness_of_noDeadEnd`](../lean/improves_bin/AbsSatBin/GraphPath/Model/NoDeadEnd.lean#L286), [`selOfAssign_decode`](../lean/improves_bin/AbsSatBin/GraphPath/Model/NoDeadEnd.lean#L62) |
| El review nunca baja de un kernel; todo estado del lector es un kernel | demostrado | [`below_review`](../lean/improves_bin/AbsSatBin/GraphPath/Model/Kernel.lean#L579), [`kernel_readPins`](../lean/improves_bin/AbsSatBin/GraphPath/Model/KernelReader.lean#L268) |
| Solo importan las parejas ambiguas | demostrado | [`tri_of_exclusive`](../lean/improves_bin/AbsSatBin/GraphPath/Model/TriPinCore.lean#L34) |

### 3.2 Del trío al certificado y a la unión (v195)

80 commits (25–27 sep). Detalle en `docs/context/escalera_reader.md` §3–§4.2λ.

* Recortes del trío (`AmbTri ⇐ AmbFar ⇐ AmbHigh`), `TriPin₁`, `CliqueTri` ([`pin_eq_cut`](../lean/improves_bin/AbsSatBin/GraphPath/Model/CliqueTri.lean#L314)), certificados
  (`CertLink ⇔ CliqueTri`, `CertClique`).
* **Todo estado de la máquina es un kernel** ([`kernel_reachable`](../lean/improves_bin/AbsSatBin/GraphPath/Model/KernelUp.lean#L636)); crecer con restricciones es exactamente
  `MapCert` ([`growR_iff_mapCert_line`](../lean/improves_bin/AbsSatBin/GraphPath/Model/KernelUp.lean#L725)); la unión no inventa cadenas ([`chain_in_piece`](../lean/improves_bin/AbsSatBin/GraphPath/Model/PieceJoin.lean#L238));
  `MapCert` en toda la máquina ⇔ `PieceLocal` en todo join ([`combined_invariant`](../lean/improves_bin/AbsSatBin/GraphPath/Model/ChainRoute.lean#L94)); veredicto bajo `PieceLocal`
  ([`readerVerdictW_iff_of_pieceLocal`](../lean/improves_bin/AbsSatBin/GraphPath/Model/StateLine.lean#L166)).
* **Falsos**: `TriPin` para los dos bits (`simple3sat_v3_c2`); la ruta por entradas de la línea (`SemCert`, 16 cliques
  en `rand3sat_v8_c10`); `GL`/`GLF` (unión de línea, 20 casos en `clause_mix.cnf`); **`MapCert` del estado unido**, y
  con él `PieceLocal`.
* El sustituto `FCert` (la restricción aplicada como filtro): base, join ([`fCert_join`](../lean/improves_bin/AbsSatBin/GraphPath/Model/FiltCert.lean#L97)), pieza sin cima
  ([`cert_piece_low`](../lean/improves_bin/AbsSatBin/GraphPath/Model/FiltCert.lean#L147)), cima con un padre ([`single_parent`](../lean/improves_bin/AbsSatBin/GraphPath/Model/FiltCert.lean#L302)), fusión ([`topMerge_of_mergeSplit`](../lean/improves_bin/AbsSatBin/GraphPath/Model/FiltCert.lean#L445)). Veredicto
  bajo `PieceLocalF` + `MergeSplit` ([`readerVerdictW_iff_of_mergeSplit`](../lean/improves_bin/AbsSatBin/GraphPath/Model/FiltCert.lean#L655)); `PieceLocalF` medida en 66,9 M casos.
* Tres correcciones de la review de Julia para que coincida con Lean (enlaces caducados, review contra hijos hasta el
  paso 0, regla de la cadena desactivada): 55/55.

### 3.3 M1 y la fila de claves (v196–v198)

* El lector decide bajo **M1** en cada join ([`readerVerdictW_iff_of_m1`](../lean/improves_bin/AbsSatBin/GraphPath/Model/FExtInd.lean#L282)), que se parte en **`M1aAll`** (fijar
  una clave viva no invalida, [`M1aAll`](../lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean#L43)) y **`M1bLowOwn`** (con la clave fijada, las tablas de abajo son de la
  pieza, [`M1bLowOwn`](../lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean#L64)): [`readerVerdictW_iff_of_own`](../lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean#L331), [`m1bLow_of_own`](../lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean#L238), [`m1aAll_of_keyTri₁`](../lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean#L308).
* `KTri` y `KTriK` **falsos**; la forma que no falla es **`KFix`** (punto fijo de la regla de parejas relativa a la
  clave, 24,7 M enlaces): [`KFix`](../lean/improves_bin/AbsSatBin/GraphPath/Model/M1bOwn.lean#L66), [`m1bLowOwn_of_kFix`](../lean/improves_bin/AbsSatBin/GraphPath/Model/M1bOwn.lean#L99), [`readerVerdictW_iff_of_kFix`](../lean/improves_bin/AbsSatBin/GraphPath/Model/M1bOwn.lean#L128).
* **Propuestas retiradas** (v196–v198): la etiqueta de clave de un nivel y la comprobación de claves (formalizadas en
  `KeyRules.lean`: M1 donde actúan y `below_reviewKC`; **no cierran la inducción** porque esta baja a las fuentes) y
  las etiquetas de todos los niveles (exactas, pero 88,7 GB y ×12,8). Revertidas (`92b4b61`); recuperables en
  `82c121f` (Lean) y `cfc92c9` (Julia).
* **Después del v198 (sin informe propio)**: `KFix ⇐ KFixLow` (`KFixCore`), `M1bSrc`, `M1bDeep`, `NodeHistory`,
  `UpSelf`, `TruncN` y `M1bChain` (último commit `8424484`): el lector decide bajo `M1aAll` y `CoverRow` en cada fila.

---

## 4. Proyecto AbsSatBingo (`lean/improves_bingo/`): el grafo de owners

### 4.1 Rama `graph_owners` (v199–v202)

* v199 (Julia, `julia/improves_bingo`): los owners pasan a un `OwnersGraph` (`alive`, `edges`, `inc`) con simetría por
  construcción. **Misma máquina** que `improves_bin` en 81/81 instancias (veredicto, soluciones, estado final, vueltas);
  99,0 s → 40,1 s; +35 % de memoria. Hallazgo: las pasadas de padres e hijos nunca cortan aristas.
* v200 (Lean, L0–L7): `GPathB` sin owners por nodo; la camarilla llevada `Carried` y el marco `Rule`. Completitud sin
  hipótesis ([`machineVerdict_of_sat`](../lean/improves_bingo/AbsSatBingo/Model/Machine.lean#L502), [`run_carries`](../lean/improves_bingo/AbsSatBingo/Model/Machine.lean#L485)); ninguna regla pierde una camarilla
  ([`carried_review`](../lean/improves_bingo/AbsSatBingo/Model/Keeps.lean#L363)); una camarilla es una solución ([`sat_of_carried`](../lean/improves_bingo/AbsSatBingo/Model/Decode.lean#L169)); veredicto bajo `NoZombie`
  ([`readerVerdict_iff_of_noZombie`](../lean/improves_bingo/AbsSatBingo/Model/Decode.lean#L250)), corregido luego: `NoZombie` es más fuerte que `NoDeadEnd`.
* v201: el review como **núcleo**; confluencia de los pins ([`pin_confluent`](../lean/improves_bingo/AbsSatBingo/Model/Kernel.lean#L181)); **`KernelExact`** conservado por
  la selección, el UP y el join ([`kernelExact_filterAll`](../lean/improves_bingo/AbsSatBingo/Model/Kernel.lean#L214), [`kernelExact_addNode`](../lean/improves_bingo/AbsSatBingo/Model/KernelUp.lean#L249),
  [`kernelExact_doJoin`](../lean/improves_bingo/AbsSatBingo/Model/KernelJoin.lean#L28)); veredicto bajo `closed`, `union`, `skip` ([`readerVerdict_iff_of_hyps`](../lean/improves_bingo/AbsSatBingo/Model/ReaderFinal.lean#L408)).
  **Adoptado**: la comprobación final del review (`FINAL_CHECK`, `finalPass`); con ella **`closed` es teorema**
  ([`closedState_review`](../lean/improves_bingo/AbsSatBingo/Model/ClosedReview.lean#L403)). `skip` pasa a `AvoidExact` ([`kernelExact_addNode_gen`](../lean/improves_bingo/AbsSatBingo/Model/KernelSkip.lean#L73)).
* v202: `union` ⇔ `SplitAt` + `SidePinned` ([`kernelUnion_iff_split`](../lean/improves_bingo/AbsSatBingo/Model/UnionEquiv.lean#L151)); veredicto por partes
  ([`readerVerdict_iff_of_parts`](../lean/improves_bingo/AbsSatBingo/Model/ReaderFinal.lean#L444)). **Falsos**: `SharedAgree`, paso de hijos, triángulo en la cima y en el
  origen, `ConeClosed` (la inducción por conos [`sideEdges_of_cone`](../lean/improves_bingo/AbsSatBingo/Model/SideCone.lean#L54) es correcta pero su paso es falso).

### 4.2 Rama `star-rule` (v203–v204)

* **Pedir menos**: `TopExact` (exactitud solo para las cimas); el UP la conserva sin hipótesis y **`skip`
  desaparece** ([`topExact_addNode`](../lean/improves_bingo/AbsSatBingo/Model/TopExact.lean#L59), [`noZombie_of_topExact`](../lean/improves_bingo/AbsSatBingo/Model/TopExact.lean#L122)); veredicto bajo `TopUnion`
  ([`readerVerdict_iff_of_topUnion`](../lean/improves_bingo/AbsSatBingo/Model/ReaderTop.lean#L320)), bajo la estrella de una cima ([`readerVerdict_iff_of_star`](../lean/improves_bingo/AbsSatBingo/Model/ReaderTop.lean#L355),
  [`readerVerdict_iff_of_local`](../lean/improves_bingo/AbsSatBingo/Model/ReaderTop.lean#L378)) y con un descenso bien fundado en la estrella ([`noBad_of_descent`](../lean/improves_bingo/AbsSatBingo/Model/StarLocal.lean#L94),
  [`topUnion_of_order`](../lean/improves_bingo/AbsSatBingo/Model/StarLocal.lean#L134)).
* v204: inducción por **linajes** (lo que en bin era M1b) demostrada; veredicto bajo `PinFree`
  ([`readerVerdict_iff_of_pinFree`](../lean/improves_bingo/AbsSatBingo/Model/LineInduction.lean#L244)), bajo `StarCore` ([`readerVerdict_iff_of_starCore`](../lean/improves_bingo/AbsSatBingo/Model/RowAgree.lean#L175)) y bajo
  **`JoinStarCore`** ([`readerVerdict_iff_of_joinStarCore`](../lean/improves_bingo/AbsSatBingo/Model/JoinStar.lean#L117)). Ocho restricciones locales medidas falsas
  (`StarRestrict`, `OwnRestrict`…). Propuesta: etiquetas por fila con review por etiqueta.

### 4.3 Rama `row-tags` (v205–v206)

* Julia (`ROW_TAGS`, `TAG_RULE`): correcta, la unión sale «por la razón buscada» (0 fallos con la regla, cientos
  sin ella), pero ×25 de tiempo.
* Lean (`AbsSatBingo/Tagged/`): la máquina etiquetada no pierde soluciones ([`machineVerdictT_of_sat`](../lean/improves_bingo/AbsSatBingo/Tagged/Machine.lean#L444)). El
  veredicto **no** sale: las intersecciones de piezas de filas distintas no son cerradas (40 %). Línea detenida.

### 4.4 Rama `reader-stuck`, máquina sin tríos (v207–v215)

* v207: contrapositivo (Solow): si el lector se atasca hay un zombi ([`zombie_of_sat_of_readerFalse`](../lean/improves_bingo/AbsSatBingo/Model/ReaderStuck.lean#L268));
  `SeqExact` ([`seqExact_iff_noZombie_visited`](../lean/improves_bingo/AbsSatBingo/Model/SeqExact.lean#L123)); `SecIn` (y `AvoidSat` desaparece, [`secIn_addNode`](../lean/improves_bingo/AbsSatBingo/Model/SecIn.lean#L81));
  `SepAt` demostrado; **un color por lado** en el mapa bin. Veredicto bajo `SecSplitIn`
  ([`readerVerdict_iff_of_secIn`](../lean/improves_bingo/AbsSatBingo/Model/SecIn.lean#L288)). Los tríos muertos existen también en el mapa bin.
* v208: `NodeIn` ([`readerVerdict_iff_of_nodeIn`](../lean/improves_bingo/AbsSatBingo/Model/NodeIn.lean#L344)); **`CliqueSplit`**, primer hecho del join demostrado sin
  hipótesis ([`cliqueSplit`](../lean/improves_bingo/AbsSatBingo/Model/CliqueSplit.lean#L372), con la completitud para toda selección válida [`steps_has_sel`](../lean/improves_bingo/AbsSatBingo/Model/CliqueSplit.lean#L145)).
* v209: la estrella por inducción a lo largo de la línea ([`starInv_up`](../lean/improves_bingo/AbsSatBingo/Model/StarLine.lean#L107)); veredicto bajo `StarJoinDown`
  ([`readerVerdict_iff_of_down`](../lean/improves_bingo/AbsSatBingo/Model/StarClique.lean#L123)), `StarCliqueSide` ([`readerVerdict_iff_of_starCliqueOnly`](../lean/improves_bingo/AbsSatBingo/Model/StarClique.lean#L132)) y
  `UnionTopClique` ([`readerVerdict_iff_of_unionClique`](../lean/improves_bingo/AbsSatBingo/Model/StarUnion.lean#L119)); `CliqueSplit` para árboles de llegadas
  ([`cliqueSplitTree`](../lean/improves_bingo/AbsSatBingo/Model/ArrTree.lean#L102)).
* v210–v213: `ChainInv` (fijar y revisar nunca vacía, [`chainInv_up`](../lean/improves_bingo/AbsSatBingo/Model/ChainPin.lean#L92), [`starJoinDown_iff_unionClique`](../lean/improves_bingo/AbsSatBingo/Model/ChainPin.lean#L334));
  `StarOneSide` por la historia ([`starOneSide_split`](../lean/improves_bingo/AbsSatBingo/Model/OneSideHist.lean#L129)); veredicto bajo B1 + `ArrHole` + `AbsHole`
  ([`readerVerdict_iff_of_holes`](../lean/improves_bingo/AbsSatBingo/Model/StarHole.lean#L200)); el hueco se explica en el 99,4 % por los requisitos del destino;
  [`pinOneSide2`](../lean/improves_bingo/AbsSatBingo/Model/PinSide.lean#L51) y [`readerVerdict_iff_of_pin`](../lean/improves_bingo/AbsSatBingo/Model/PinJoin.lean#L117) (con la corrección: `PinKeeps2` ≡ B1); la espina
  ([`forced_parent`](../lean/improves_bingo/AbsSatBingo/Model/Spine.lean#L32), [`two_helly`](../lean/improves_bingo/AbsSatBingo/Model/Spine.lean#L41), [`carried_of_spine`](../lean/improves_bingo/AbsSatBingo/Model/SpineZombie.lean#L124)) y `ChainInv` sin B1
  ([`chainInv_run`](../lean/improves_bingo/AbsSatBingo/Model/ChainLine.lean#L116)). `SpineTrio` **falsa**: siempre hay que revisar.
* v214: **FORBID** (tríos prohibidos en las aristas, Julia). **Límite de la revisión**: un estado cerrado por parejas
  sin camarilla ([`closed_not_chainInv`](../lean/improves_bingo/AbsSatBingo/Model/ClosedLimit.lean#L201), K5 con 4 colores). Solidez de los tríos ([`forbidSound_join`](../lean/improves_bingo/AbsSatBingo/Model/ForbidSound.lean#L146));
  el invariante **`LiveExt`** da el veredicto de la espina ([`liveChain_full`](../lean/improves_bingo/AbsSatBingo/Model/LiveExt.lean#L51),
  [`spineVerdict_iff_of_liveExt`](../lean/improves_bingo/AbsSatBingo/Model/LiveExt.lean#L130)); el UP no necesita heredar tríos ([`liveExt_addNode_same`](../lean/improves_bingo/AbsSatBingo/Model/LiveUp.lean#L441)); teorema
  sobre la máquina real bajo `PinJoinSplitAll` + `NoNewClose` ([`spineVerdict_iff_of_liveLine`](../lean/improves_bingo/AbsSatBingo/Model/LiveDriver.lean#L609)).
* v215: antes de las cláusulas todo es exacto (parcheo, [`triSplit`](../lean/improves_bingo/AbsSatBingo/Model/PreClause.lean#L660)); solidez de las familias con pins
  ([`AvoidV`](../lean/improves_bingo/AbsSatBingo/Model/CliqueSound.lean#L75)); veredicto bajo `PinJoinSplitAll` + `HClq` ([`spineVerdict_iff_of_clq`](../lean/improves_bingo/AbsSatBingo/Model/CliqueSound.lean#L297)).

### 4.5 Auditoría y espejo de la máquina con tríos (v216–v220)

* **v216, auditoría**: Lean modelaba `FORBID = :off` con tríos **fantasma**, mientras las sondas del día corrían con
  `:on`; las hipótesis vigentes no tenían medida en el modo de Lean. `TriClq` se revirtió (`c693d31`). Regla desde
  entonces: **cada medida en el modo del enunciado Lean que respalda**.
* v217, **el espejo `:on`** (`docs/plans/lean_forbid_on.md`): `ForbidOn.lean` con la máquina parametrizada por modo
  ([`runM`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOn.lean#L330); con `.off` es la de siempre por `rfl`); diferencial Lean ↔ Julia con tríos: 0 diferencias en 5
  instancias. Completitud ([`machineVerdictOn_of_sat`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnMachine.lean#L529)); veredicto bajo `LiveExt` con los tríos reales
  ([`spineVerdictOn_iff_of_liveExt`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnLine.lean#L316)); el join bajo (★) ([`liveExt_joinOn`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnLive.lean#L562)); la regla llega a su punto
  fijo ([`forbidRule_closed`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnFix.lean#L353)) y la dirección 2 de la llegada fijada sale sin hipótesis ([`liveChain_down`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnPin.lean#L219)).
* v218: dirección 1 ([`ct_arrival_up`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnArr.lean#L91)) y **las llegadas ya no piden nada** ([`good_arrivalOn`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnArr.lean#L250));
  inducción de línea `:on` ([`spineVerdictOn_iff_of_joinOn`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnDriver.lean#L347)); de cadenas a cimas
  ([`spineVerdictOn_iff_of_topOn`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnTop.lean#L309)); **respuestas certificadas** ([`verdictOn_certified`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnTop.lean#L336)); y la hipótesis
  estrechada a `CrossCut` + `Star4At` ([`spineVerdictOn_iff_of_cross4`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnStar.lean#L1069)).
* v219: revisión de niveles e índices; veredicto bajo `PrevCut` + `Star4At` ([`spineVerdictOn_iff_of_prev4`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnStar.lean#L1085),
  [`HPrevCut`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnStar.lean#L923), [`Star4At`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnStar.lean#L508)).
* **v220**: `PrevCut`, `CrossCut`, `Star4At` y `StarTriAt` **falsas en `v7`** (bases que revivan en el join:
  [`revive_sender_open`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnStarD.lean#L941)). La prueba se rehízo sin ellas ([`star_coreD`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnStarD.lean#L43)), y **`TopSideAt` sin pins quedó
  demostrada** ([`topSideAt_nil_line`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnNoPin.lean#L290)); veredicto bajo `TopSideAt` con pins
  ([`spineVerdictOn_iff_of_topPins`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnNoPin.lean#L438)). Por el camino: la forma normal del nacimiento ([`birth_pattern`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnBirth.lean#L249)) y
  la partición en el paso de los padres ([`tetra_parent_or_split`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnSplit.lean#L206)). Propuesta: cuartetos anclados en la cima.

### 4.6 La escalera de niveles y la fórmula (v221–v222)

* v221: en vez de cuartetos, **otro invariante**: niveles sobre el estado tal cual (1 nodos, 2 aristas, 3 triángulos
  de cima). Join y UP los conservan en los tres niveles sin hipótesis; el filtro baja un nivel. Veredicto bajo
  `HypsNodeKeep` ([`spineVerdictOn_iff_of_nodeKeep`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnExact.lean#L956)), y todo bajo el nivel 3 ([`exact_of_triKeep`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnExact.lean#L675));
  lo abierto, `PinTetra` ([`PinTetra`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnExact.lean#L260), [`spineVerdictOn_iff_of_pinTetra`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnExact.lean#L1004)). Medido en 4 198 estados de 8
  instancias (318 M triángulos): 0 objetos fuera de camarillas. Descartado: los criterios de Freuder y van
  Beek–Dechter (anchura 16–41, estrechez 6–7).
* **v222**: la lectura semántica del mapa bin (cada paso lee una variable).
  * **Primer veredicto sin hipótesis de la máquina con tríos**: fórmulas con forma 2-CNF, por la mayoría
    ([`majClosed_twoLike`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnMaj.lean#L954), [`spineVerdictOn_iff_of_twoLike`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnMaj.lean#L1016), [`reader_on_twoLike`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnRead.lean#L181)).
  * **Sin familias fantasma** ([`PhantomFree`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnHelly.lean#L73), [`PhantomAt`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnHelly.lean#L596)): la máquina decide y el lector no retrocede
    ([`spineVerdictOn_iff_of_phantomFree`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnHelly.lean#L762), [`reader_on`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnRead.lean#L155)).
  * **La equivalencia**: `MachineExact φ ↔ ∀ T ≥ 1, PhantomAt φ T`, sin hipótesis ([`machineExact_iff`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnTight.lean#L509)); y la
    del lector ([`readerExact_iff`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnReadIff.lean#L129)).
  * La condición de un paso (`HellyAt`) falla en fórmulas de paridad construidas; la de todos los pasos se cumple.

### 4.7 Las clases (v223–v225 y después)

* v223: `PhantomAt` **es falsa en general** (`chain6_cross`: 8 triángulos de más en llegadas); la inducción solo
  necesitaba la forma débil **`PhantomAtW`** ([`PhantomAtW`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L57), [`machineExactW_iff`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L158),
  [`readerExactW_iff`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L295)), que ahí se cumple. Clases nuevas por **parche** ([`helly4_of_patch`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnBlock.lean#L99),
  [`machineExact_of_blocks`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnBlock.lean#L285)), **pegado en la variable compartida** ([`phantomFree_sep`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnSep.lean#L299),
  [`machineExact_of_sep2`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnSep.lean#L671)) y **cadenas de tres bloques** ([`phantomAt_of_chain3`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain.lean#L858),
  [`machineExact_threeChain`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain.lean#L959)), sobre familias locales ([`LocPair`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnLocal.lean#L83)).
* v224: el **descenso por rango** ([`tri_descent`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnDescent.lean#L54)); cuatro bloques y **`chain4_cross` sin hipótesis**
  ([`machineExact_chain4Cross`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4X.lean#L289), [`reader_chain4Cross_any`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4X.lean#L293)); el testigo de una ventana sustituye al
  «testigo de cuatro nodos»; las líneas solo ven el prefijo ([`phantomAt_of_prefix`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnPrefix.lean#L165)). En cinco bloques el lector
  **no es exacto pero no se atasca**; invariante de aristas `TriId` ([`TriId`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnEdge.lean#L42)) y reducción a `PinPairs`
  ([`PinPairs`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnPinPairs.lean#L39), [`reader_on_pinPairs`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnPinPairs.lean#L235)).
* v225, **lector por separadores**: fijar primero las variables compartidas. T1 ([`phantomFree_pinnedSepCover`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnSepRead.lean#L47))
  y T3 ([`reader_sep_on`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnSepRead.lean#L217)) demostrados; **`chain5_cross` sin hipótesis**: la máquina es exacta, su veredicto es
  correcto y el lector por separadores no se atasca ([`machineExact_chain5Cross`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L395),
  [`spineVerdictOn_iff_chain5Cross`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L399), [`reader_sep_chain5Cross_full`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L404)). El orden del lector no cambia lo
  que la máquina calcula. Borrador Julia en `julia/improves_bingo/drafts/path_sep_reader.jl`.
* **Después del v225** (commits `9cd3d6f` … `80dbd58`, sin informe):
  * las líneas de `chain5_cross` ([`phantomAt_chain5Cross`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5L.lean#L294));
  * la **clase de cinco bloques** `Chain5C`, con cualquier numeración: [`Chain5C`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5C.lean#L41), [`machineExact_of_chain5C`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5C.lean#L655);
  * la infraestructura de **n bloques**: [`ChainN`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainN.lean#L45), [`glueN`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainN.lean#L55); un lado de la bisección ([`SideCap`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainSide.lean#L48));
  * fijar un separador con los dos lados abiertos ([`phantomFree_bisect`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisect.lean#L326)); T2 en orden de bisección y lector
    para `ChainN` **hasta seis bloques, dadas las líneas** ([`sepPinFree_of_bisect`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisect.lean#L404), [`bisectOrder_6`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisect.lean#L456),
    [`reader_bisect`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisect.lean#L489)).
  * Sondas: el lector por separadores no se atasca en `chain6_cross` (0 fantasmas en 26 estados) ni en `chain7_cross`
    (11 lecturas).

---

## 5. Vías atacadas y descartadas

| vía / enunciado | informe | por qué cae |
|---|---|---|
| relación de soporte estática; cierre de triángulos `SPC`; doble rebanada | v119–v123 (resumidas en v131) | medidas: 32 nodos perdidos; K4 3-colores; 2 026 nodos |
| rebanada del ancla como soporte | v130 | 72/15 180 (K4), 5 712 (cubo), 592 (K3,3) sin trío |
| `JoinSplit` por entradas (puerta A) | v131 | 1 328 pares ajenos dentro de la rebanada |
| transitividad de la posesión, adyacente, «el vecino decide», rebanada = camarilla, candidatos anidados | v132 | fallos medidos en K4/K3,3 |
| fusión de tipo OBDD (mismo futuro) | v137 | casi cada pasado tiene un futuro propio |
| cadena enlazada = camino; Helly-3; rebanada cerrada por enlaces; dominancia del ancla | v139 | fallos medidos |
| bases direccionales de `GhostsLine` | v140 | las fantasmas persisten hasta el barrido |
| empalme de caminos; construcción voraz sin review | v144 | 23 506 entradas sin empalme; atascos |
| regla de ternas a través del valor vivo (`TripleA`) | v146 | falla ya en la primera variable |
| `SideCover` fuerte; que cada rama explique todas sus entradas | v147 | 476 anclas cruzadas; 41 708 casos |
| `TopKeep` universal | v163 | 2 040 en 16,6 M |
| `SemWitnessAt` | v164 | caso construido de 23 variables, fuerza bruta |
| triángulo como regla de borrado de pares | v164, v168 | perdería soluciones |
| `ParentMeet`, `PairMeet`, `DecidedAbove`, `TableDownClosed`, `AllParentsOwn`; `ChainMerge` | v174 | todas hablan de tres objetos; contraejemplo `{110,101,011}` |
| `AncOwned`, `PairChained`, `HopDown`, «la tabla es una clique» | v175–v178 | 22,8 % tras el join; contradictoria; 16/484; 7,9 % |
| `DescentStepOwned` (redacción v178) | v179 | demostrado falso ([`not_descentStepAny`](../lean_project/AbsSat/GraphPath/Model/OwnerChainedBuild.lean#L1198)) |
| `FullExtG`, `FilterReviewComplete`, `JoinFullExt` | v180 | 36 tramos mezclados tras 3 de 710 uniones |
| `SegNoMix`, `MixDies`, `CutKillsMix` | v183 | la unión mezcla; caen por colapso masivo, no localmente |
| forma de las tablas (subárbol, intervalo, laminar) y mayoría (Baker–Pixley) | v185 | 2–8 % fuera de cada forma; 2 casos vivos exactos |
| cajas literales | v188 | 30 de 463 |
| `hStart`, `SegGood`, `TriExact`, `RoundExact`, `PairHelly` fuerte | v190 | semilla 11, fórmula #1 |
| regla del hueco | v191 | quitaría parejas que están en soluciones |
| binarizar como arreglo del trío muerto | v191 | el hueco se muda a las ventanas |
| `TriPin` para los dos bits; `SemCert` por entradas; `GL`/`GLF`; `MapCert` del estado unido | v195 | contraejemplos en `simple3sat_v3_c2`, `rand3sat_v8_c10`, `clause_mix.cnf` |
| `KTri`, `KTriK`, `KeyTri` | v196 | 716/10 530; 8/56; 360 |
| `SecMeet` (inducción local por el lector) | v201 | 21 044 casos |
| `SharedAgree`, `SonClosed`, triángulos en cima y origen, `ConeClosed` | v202 | fallos medidos |
| desdoblar nodos; `AncKernel`; testigos `OwnSideGood`/`PairIn`/`TriIn`; `StarClosed` | v203 | sin cota; las tablas llevan historia; 61 casos; ~7 % |
| `TopsSep` entre copias; `StarRestrict`; `OwnRestrict`; pin del linaje | v204 | 47 %; 4,9–13 %; 9,4 %; mal definido |
| etiquetas por fila para el veredicto | v206 | intersecciones no cerradas (40 %) |
| `WitnessAgree`; `OneSideSupport` en un sentido | v208 | ~25 %; falla con tríos muertos |
| `CrossAt1` inductivo | v211 | el paso libre no se hereda entre subgrupos |
| `SpineTrio` (espina sin revisión) | v213 | se atasca en `clause_mix` |
| `TopDom`, `ChainOpen`, acuerdo de tríos, `PinEdgeMono`, `NoNewClose` por llegada | v214 | fallos medidos (`:on`) |
| `TriClq` | v216 | la definición no pedía cadena viva; revertido |
| `TopFace` | v218 | 300 de 2 775 en `clause_mix` |
| `PrevCut`, `CrossCut`, `Star4At`, `StarTriAt`, `HNoRule` sin restricción, `LineCut` | v219–v220 | instancias `v7` |
| propiedades estáticas del grafo final (anchura de Freuder, estrechez de van Beek–Dechter, memoria corta) | v221 | anchura 16–41; estrechez 6–7; la cuenta local sobrecuenta |
| `HellyAt` (condición de un paso); `PinTetra` fuerte | v222 | paridades construidas |
| `PhantomAt` en toda 3-CNF | v223 | `chain6_cross` |
| exactitud del lector en cualquier orden (`HRead`); `HReadE` | v224 | 36 fantasmas en `chain5_cross`; circular |

---

## 6. Cambios en la máquina: propuestos, adoptados y retirados

| cambio | informe | resultado |
|---|---|---|
| marcar la procedencia de las entradas | v129, v133 | no adoptado (coste en espacio) |
| ventana del identificador de tres | v173 | **adoptado** (rama `spaik-window3`) |
| `cleanInvalid` en dos fases | v181–v182 | **adoptado** (Julia y Lean) |
| review simétrico (espejo) | v182, v184 | **adoptado** (`SYM_MODE = :on`) |
| regla de parejas tras la limpieza | v185–v186 | **adoptado** (`PAIR_MODE`); `AggInactive` pasa a teorema |
| quitar el filtro agresivo | v193 | **adoptado** en bin (identidad en el punto fijo; ~3,5×) |
| mapa binario | v187, v192–v193 | **adoptado** (`improves_bin`, y base de bingo) |
| acarreo del estado de las cláusulas | v191 | no (exponencial en el ancho de corte) |
| etiqueta de clave de un nivel; comprobación de claves; etiquetas de todos los niveles | v196–v197 | **retirados** (v198) |
| grafo de owners | v199 | **adoptado** (`improves_bingo`) |
| comprobación final del review (`FINAL_CHECK`) | v201 | **adoptado**; `closed` pasa a teorema |
| regla de la estrella | v204 | sólida pero vacía (no corta nada) |
| etiquetas por fila con review por etiqueta | v204–v206 | implementado (`ROW_TAGS`, apagado); no da el veredicto |
| regla de tríos (`TRIO_RULE`) | v207 | no corta nada |
| tríos prohibidos (`FORBID`) | v214, v217 | modo `:on`, reflejado en Lean (`ForbidOn*`) |
| cuartetos anclados en la cima | v220 | no hizo falta: se cambió el invariante (v221) |
| lector por separadores | v225 | propuesto (borrador); demostrado en `chain5_cross`, `Chain5C` y `ChainN` ≤ 6 |

---

## 7. Hipótesis vigentes y preguntas abiertas

| pregunta | dónde | estado |
|---|---|---|
| ¿Toda 3-CNF cumple `PhantomAtW` (sin familias fantasma en la forma débil)? | AbsSatBingo | **abierto**; equivale a la exactitud de la máquina con tríos ([`machineExactW_iff`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean#L158)) |
| Las líneas de `ChainN` para n ≥ 6 | AbsSatBingo | el lector está demostrado hasta seis bloques **dadas las líneas** ([`reader_bisect`](../lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisect.lean#L489)) |
| `PinPairs` en general (lector en cualquier orden) | AbsSatBingo | abierto; demostrado en las clases |
| `M1aAll` y `KFix` / `CoverRow` en cada join | AbsSatBin | abiertos, medidos sin fallos |
| `KeptOwn`, `PairExact` en el pin, `PrefixSegGood` | AbsSat | abiertos; `SegGood` y `hStart` son falsos (v190) |
| `PinnedUnionInhabited` / `RulePreservesValidity` | AbsSat (`ImprovesCima`) | abierto; equivalente al veredicto |
| El coste del lector sin retroceso | todos | el lector **con** retroceso decide sin hipótesis ([`readerVerdictBT_iff`](../lean_project/AbsSat/GraphPath/Model/ReaderBT.lean#L267)); medido, el retroceso no hace falta nunca |

---

## 8. Lecciones de método que dejaron los informes

* **Medir antes de demostrar, y medir en grande.** Dos semillas ocultaron el fallo de la semilla 11 (v190); seis
  instancias dieron por buenas `PrevCut` y `HNoRule`, que cayeron en `v7` (v220). Las instancias pequeñas dicen poco:
  con 5–9 variables un trío ya fija casi la solución (v222, §7.3).
* **Medir en el modo que modela Lean** (v216).
* **«Confía en el algoritmo»** (v224): restringir la numeración sobraba; la máquina era exacta.
* **Un teorema pide la ejecución cuando solo necesita los invariantes** (v172): pagar esa deuda desbloqueó varios
  pasos.
* **Revisar tras cada elección** es lo que hace funcionar al lector (v176, v213); la espina sin revisión se atasca.
* **Pedir menos**: casi cada salto vino de debilitar el enunciado (de `∀` a `∃`, de parejas a cimas, de exactitud
  fuerte a débil, de `SegGood` a prefijos).
* **El contenido de una medida**: contar solo lo que el enunciado pide (sondas que contaban estados inválidos dieron
  cifras espurias, v174) y volcar resultados parciales (v220).
* **Técnicas del libro de Solow** citadas en los informes: contrapositivo (v207), construcción y contraejemplo
  (v212, v214), inducción con hipótesis reforzada (v204, v212); fuera del libro, buen orden y palomar (v212, v214).

---

## Apéndice: índice de los informes v126–v225

| v | rama | tema |
|---|---|---|
| 126 | spaik | la rama vive dentro de la máquina completa |
| 127 | spaik | compatibilidad de la rama; veredicto bajo `NoBorrow` |
| 128 | spaik | inducción sobre la construcción salvo el join (`HPV`, `JoinSplit`) |
| 129 | spaik | un solo obstáculo en tres disfraces; procedencia del join |
| 130 | spaik | el ID fija el testigo; rebanada del ancla refutada |
| 131 | spaik | invariante de ejecución; mapa de la demostración; `NoDeadEnd` |
| 132 | spaik | descenso; cinco reglas locales refutadas; `CommonOwner` |
| 133 | spaik | veredicto con `CommonOwner` declarada |
| 134 | spaik | qué es `CommonOwner`; SAT con camino frente a SAT desde la validez |
| 135 | spaik | exactitud de tablas por construcción |
| 136 | spaik | el conjunto de certificados, exacto; `ValidDecidesEmpty` |
| 137 | spaik | el join no es una fusión de OBDD (medida) |
| 138 | spaik | distributividad; `ReviewJoin` |
| 139 | spaik | la máquina como oráculo comprimido; `FilterSound` |
| 140 | spaik | invariante de rebanadas; fantasmas |
| 141 | spaik | veredicto con `GhostsLine` declarada |
| 142 | spaik | respuestas correctas sin hipótesis; lector sin atasco |
| 143 | spaik | fijar a la vez = en secuencia |
| 144 | spaik | `PinExtends`; débiles sin efecto |
| 145 | spaik | `LivePinUp` |
| 146 | spaik | `TripleA` refutada; `SideCover` |
| 147 | spaik | la unión partida por caminos (`RunPaths`) |
| 148 | spaik | no se pierden soluciones parciales; sin préstamo; balance |
| 149 | spaik | lo local demostrado; la elección común |
| 150 | spaik | ruta de construcción; `PinPairSoundAt` |
| 151 | spaik | el núcleo en el idioma de la historia |
| 152 | spaik | lo que aporta el review en la fila |
| 153 | spaik | fijar es un requisito que la historia ya aplicó |
| 154 | spaik | fijar atraviesa un envío; `PinJoin` |
| 155 | spaik | las cimas distintas separan la unión |
| 156 | spaik | la etapa de variables demostrada |
| 157 | spaik | la etapa de cláusulas, un cambio de valor |
| 158 | spaik | `FlipSat` |
| 159 | spaik | `SideKeep` |
| 160 | spaik | solo quedan las incoherencias anchas |
| 161 | spaik | los triángulos repartidos los mata una fila |
| 162 | spaik | muerte directa; `RowWitnessAt` |
| 163 | spaik | el lado lo elige su cima |
| 164 | spaik | `SemWitnessAt` falsa; testigo con cierre; lector programa |
| 165 | spaik | ruta C, validez; `OwnSupportAt` |
| 166 | spaik | `ImprovesCima` |
| 167 | spaik | la regla de la cima por recorte al lado |
| 168 | spaik | el filtro del triángulo del autor |
| 169 | spaik | el filtro como test computable |
| 170 | spaik | la cadena se arrastra; las dos rutas son una |
| 171 | spaik | conservación de `ImprovesCima`, el suelo |
| 172 | spaik | `ImprovesCima` conserva; `RulePreservesValidity` |
| 173 | spaik | `PinnedUnionInhabited`; la ventana del identificador |
| 174 | spaik-window3 | decide con retroceso sin hipótesis; `TriplePin` |
| 175 | spaik-window3 | el lector no añade nada; niveles de consistencia |
| 176 | spaik-window3 | tres de cuatro operaciones; elección binaria |
| 177 | spaik-window3 | `PinAlive`; `TableChainOwned` |
| 178 | spaik-window3 | todo en un paso de descenso |
| 179 | spaik-window3 | `FilterReviewComplete` |
| 180 | spaik-window3 | `ReaderTopGood`; la cascada |
| 181 | spaik-window3 | las pasadas de coherencia; propuesta de dos fases |
| 182 | clean-two-phase | `cleanInvalid₂` adoptado; propuesta de review simétrico |
| 183 | clean-two-phase | `SegExact`; Hellys de un paso |
| 184 | review-symmetric | review simétrico; la simetría como invariante |
| 185 | review-symmetric | condenados por parejas; Helly no viene de la forma; regla de parejas |
| 186 | pair-mode | la regla de parejas en la máquina y en la prueba |
| 187 | pair-mode | Helly de un paso; propuesta de binarizar |
| 188 | pair-mode | `PairHelly` paso a paso; el testigo de la historia |
| 189 | pair-mode | mapa de la escalera |
| 190 | pair-mode | semilla 11: `SegGood` falso; prefijos |
| 191 | pair-mode | anatomía del trío muerto; propuestas por capas |
| 192 | improves_bin | qué gana la prueba con el mapa binario (teórico) |
| 193 | improves_bin | el mapa bin en el diferencial (Julia) |
| 194 | lean_improves_bin | el proyecto Lean bin; hasta `TriPin` |
| 195 | lean_improves_bin | de `TriPin` a certificados; `MapCert` falso; `FCert` |
| 196 | lean_improves_bin | M1; etiqueta de clave y comprobación de claves |
| 197 | lean_improves_bin | etiquetas de todos los niveles |
| 198 | lean_improves_bin | se retiran las reglas de la fila de claves |
| 199 | graph_owners | el grafo de owners (Julia) y cinco reglas sobre aristas |
| 200 | graph_owners | el proyecto Lean bingo; `NoZombie`/`NoDeadEnd` |
| 201 | graph_owners | `KernelExact`; tres hipótesis; comprobación final |
| 202 | graph_owners | `closed` teorema; `union` descompuesta |
| 203 | star-rule | `TopExact`; `skip` desaparece; la estrella |
| 204 | star-rule | `JoinStarCore`; propuesta de etiquetas por fila |
| 205 | row-tags | etiquetas por fila en Julia |
| 206 | row-tags | etiquetas en Lean; dónde se paran |
| 207 | reader-stuck | `SecSplitIn`; un color por lado |
| 208 | reader-stuck | `NodeIn`; `CliqueSplit`; vías A–E |
| 209 | reader-stuck | la estrella por inducción; `UnionTopClique` |
| 210 | reader-stuck | bajada del lector; B1, `CrossAt`, `ArrivalGap` |
| 211 | reader-stuck | cono de antepasados; `ArrHole`, `AbsHole` |
| 212 | reader-stuck | requisitos del hueco; `pinOneSide2`; la espina |
| 213 | reader-stuck | lector por caminos; `ChainInv` sin B1 |
| 214 | reader-stuck | tríos prohibidos; `LiveExt`; inducción sobre la máquina real |
| 215 | reader-stuck | antes de las cláusulas; `AvoidV`; `HClq` |
| 216 | reader-stuck | auditoría Lean ↔ Julia |
| 217 | reader-stuck | el espejo `:on` en Lean |
| 218 | reader-stuck | veredicto `:on` bajo dos hipótesis de tríos |
| 219 | reader-stuck | revisión de `PrevCut` y `Star4At` |
| 220 | reader-stuck | caen `PrevCut` y `CrossCut`; `TopSideAt` sin pins |
| 221 | reader-stuck | la escalera de niveles |
| 222 | reader-stuck | la corrección equivale a un enunciado sobre la fórmula |
| 223 | reader-stuck | primeras clases con cláusulas de tres literales; `PhantomAtW` |
| 224 | reader-stuck | cuatro bloques; cinco bloques sin atasco |
| 225 | reader-stuck | el lector por separadores; `chain5_cross` sin hipótesis |
