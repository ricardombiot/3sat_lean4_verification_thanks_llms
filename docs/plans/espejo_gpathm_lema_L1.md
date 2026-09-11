# Plan de formalización: espejo puro `GPathM` + Lema L1

**Objetivo:** construir el espejo puro (sin `IO.Ref`) del grafo con Owners y demostrar el
primer lema del puente — **L1, soundness local de requisitos** — tal como se define en
[`lean_project/formal_bridge_owners_runpure.md`](../../lean_project/formal_bridge_owners_runpure.md)
(§5-L1 y §6.1). Este plan cubre las etapas 0 y 1 del puente y deja enunciada (sin
demostrar) la denotación que usarán L2–L8.

---

## Registro de ejecución

**2026-09-11 (bl) — P3 reducida a una existencia: `PinReaches`.**

`FabricAdd.lean`: `Compat`, `CoreS`, `CoreT`, `CoreS_of_mem`, `CoreS_sat`, **`Fabric_core`**
(el mayor tejido que cumple una restricción es un tejido; **sin axiomas**), `PinReaches`,
**`FabricAt_filterAll_of_PinReaches`**. Hallazgo de base: `filterRequire` toca **solo `gowners`**
(las tablas por nodo las estrecha el review), luego de las nueve cláusulas el pinchazo amenaza solo
`gow` — que es exactamente la hipótesis de `FOk_filterAll` (v65) y por eso falla en el paso de
cláusula, ya que el tejido de `addNode` contiene todos los gowners. Solución: el movimiento de v44
(las cláusulas se conservan bajo unión porque cada una se atestigua dentro de un solo tejido), de
donde sale `Fabric_core` por construcción. Queda **una sola existencia**: `PinReaches g reqs r rn` =
`CoreS g (Compat reqs ∧ ∈ owners(r)) r` — el `CoreCovers` de v44, y lo medido en v77 (124.246 nodos,
0 fallos). Ruta: P1 ✅ (v78), P2 ✅ (v65 + join v79), P3 reducida, P4 abierta (desajuste
`readStepSym` vs `filterAll g [q.id]`), P5 libre. Límite: `PinReaches` general = 3SAT en P; ahí entra
la clase, ya sobre `owners` y no sobre un modelo paralelo.

Informe: `verificacion_inseguridad_autor_v80.md`.

**2026-09-11 (bk) — `join` cerrado; y P3 resulta ser `CoreCovers`.**

`FabricAdd.lean`: **`Fabric_of_grown`** (un tejido sobrevive a cualquier crecimiento — todas sus
cláusulas son pertenencias o existencias), y de ahí `Fabric_join_left` y `Fabric_join_right` usando
`Grown`/`grown_join_left`/`grown_join_right` de `Join.lean`. Cierres `[propext, Quot.sound]`. Libro
mayor de la inducción sobre `Reachable` completo en lo estructural: semilla ✅, `addNode` ✅ (v78),
`join` ✅ (hoy), review y filtros de literal ✅ (v65). **Hallazgo**: `FOk_filterAll` (v65) exige
`∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r`; en un paso de cláusula eso falla de entrada
porque el tejido de `addNode` contiene todos los gowners y por tanto ambos valores del paso pinzado.
Luego **P3 no es preservación sino estrechamiento**: estrechar el tejido a los miembros que concuerdan
con los tres requisitos y probar que sigue teniendo entrada en cada paso — que es el `CoreCovers` de
v44 reencontrado por otra vía, y lo que v77 midió (124.246 nodos, 0 fallos). Siguiente: P3, con la
expectativa declarada de que ahí entre la hipótesis de clase (P3 general = 3SAT en P).

Informe: `verificacion_inseguridad_autor_v79.md`.

**2026-09-11 (bj) — P1: el tejido nace en la semilla y en `addNode`.**

`FabricAdd.lean` (módulo nuevo, registrado en `AbsSat.lean`): `addS`, `addT`, y los teoremas
`not_S_newPid`, `step_lt_of_S`, `mem_newParents_of_S`, `exists_S_at`, `carrier_for`,
**`Fabric_initSeed`**, **`Fabric_addNode`**, **`FabricAt_addNode_new`**,
**`isValid_readStepSym_addNode_new`**; todos `[propext, Quot.sound]`. La cláusula difícil es `up`
del nodo nuevo: su tabla contiene a todos los miembros y `up` pide un padre suyo en la tabla que
respalde cada entrada; como sus padres son toda la línea anterior, el portador es el testigo de
`support` de la entrada, girado con `symm` y hecho miembro por `inS` — la simetría es portante
(de ahí el valor de `OwnSymmetric_read`, v64). Hipótesis: `d.step = g.current_step`, nodos por
debajo, `S` no vacío, `0 < current_step`. **Corrección a v77**: `Fabric.lean` no menciona `join`
(0 ocurrencias), luego «sobrevive a las cuatro operaciones» era inexacto. Libro mayor de la
inducción sobre `Reachable`: semilla ✅, `addNode` ✅, review y filtros ✅ (v65), **`join` abierto**.
Ruta de v77: P1 cerrada, P2 cerrada salvo `join`, P3 abierta (medida en v77), P4 abierta (desajuste
`readStepSym` vs `filterAll g [q.id]`), P5 libre. Siguiente: `join`, y después P4.

Informe: `verificacion_inseguridad_autor_v78.md`.

**2026-09-11 (bi) — El tejido en los pasos de cláusula; y el veredicto no necesita `PairwiseOwned`.**

`cnfmap --fabclause` (`fabricCover`, `scoreFabricClause`, `runFabricClause`): para cada nodo de cada
estado válido **en los pasos de cláusula**, el mayor tejido dentro de `owners(n)`. **124.246 nodos**
(84.538 aleatorios 3–6 vars en 4 semillas; 39.708 en controles Tseitin K4/K3,3/prisma, ambas
paridades): miembros conservados, **cobertura de todos los pasos** y auto-pertenencia en **todos**,
0 fallos; original y simétrica idénticas. Recorte solo de **entradas** (permitido por `Fabric`, que
guarda subtablas): 0 % en aleatorias 3–5 y en K4, 0,003 % en 4–6, 0,9–2,0 % en K3,3/prisma —
fenómeno de ciclicidad. **Hallazgo**: verificadas las firmas, el veredicto solo consume `Inhabited`
(`L7.satisfiable_of_inhabited`), que v58 reduce a `PickSome` y v65 a `FabricAt` — así que hay ruta
sin `PairwiseOwned` ni `ClauseStepExact`. Plan en cinco piezas: P1 `FabricAt` en `addNode` (v62 da la
simetría de creación), P2 review (**hecho**, v65), P3 filtro de cláusula (**nueva**, medida hoy),
P4 puente `FabricAt ⟹ PickSome` con desajuste declarado (`filterAll g [q.id]` vs
`readStepSym = reviewSym ∘ pinOwners`), P5 cierre con `L7`. Esquiva v43 (caminos), v40
(transitividad) y v28 (clique), y la simetría es teorema desde v64. Límite: las cinco cerrando para
toda φ sería P=NP, luego se espera que **P3 pida la hipótesis de clase** (anchura acotada de v76,
sobre las estructuras propias). Siguiente: P1, y empujar la medición de P3 a tamaños mayores
buscando el primer tejido que pierda un paso.

Informe: `verificacion_inseguridad_autor_v77.md`.

**2026-09-11 (bh) — El mapa: qué falta para demostrar que el algoritmo decide 3SAT.**

Análisis sin código, a petición del autor. El diseño (construir el conjunto de **todos** los
certificados) son dos inclusiones: ⊇ demostrada entera (v50–v53), ⊆ abierta (`ClauseStepExact`), y
`decides_of_ClauseStepExact` ya hecho. Traducción del diseño: variables = pasos, dominios = nodos
(valores de variable / filas de cláusula), `owners` = soportes por **pares** = 2-consistencia
(`ZeroOneAll.lean`, v20), `review` = su punto fijo, triángulo (v69) = un nivel más. Por Freuder
(consistencia fuerte de nivel k + anchura inducida < k ⟹ sin retroceso): ningún k fijo vale para
toda φ (⊆ general = P=NP, v14/v67); sí vale en anchura acotada; **subir el nivel del filtro ensancha
la clase, no cierra el general** — respuesta a la pregunta sobre correcciones del filtrado. Huecos
medidos por nivel: pares 0 tras el triángulo (v69), tríos 38/905.506 con 7 genuinos (v70), nodos
zombie 0 y veredictos malos 0 (v66/v70/v75): la exactitud de tabla ya falla en tríos y aun así la
propagación por filas cierra a tiempo — margen medido, no teorema. Rutas: R1 clase por anchura sobre
las estructuras propias (objetivo `decides_on_class`), R2 pasada de nivel 4 (ensancha la clase), R3
caso general = P=NP (aplazado). Siguiente concreto: enunciar y demostrar el puente (A) de v75 sobre
`owners`, vía `L1`/`ReqFiltered` + coherencia de padres e hijos en los pasos de literal; alcance
advertido: (A) da exactitud a nivel de **clave**, y de clave a **nodo** falta un escalón (v67).

Informe: `verificacion_inseguridad_autor_v76.md`.

**2026-09-11 (bg) — La banda máquina↔reductor: la máquina es más fuerte, y el puente cambia de sentido.**

`cnfmap --band` (`scoreBand`, `runBand` en `SymCampaign.lean`): en cada paso de cláusula de una
ejecución real compara tres conjuntos de filas — las vivas en la máquina (claves válidas en la línea
a ese paso), las vivas en `CnfReducer.reduce (initRels (take (j+1)))`, y la verdad por fuerza bruta.
Dos campañas (5 semillas 3–6 vars; 4 semillas 5–8 vars, estas para intentar romperlo), **5.203 pasos
de cláusula**: filas solo de la máquina = **0** sin excepción; espurias de la máquina = **0**;
espurias del reductor = **2.166**; perdidas = 0 en ambos. Dentro de la clase (426 pasos) los
conjuntos coinciden exactamente. Controles Tseitin: mismo patrón. Con `pureAdvanceTri`, idéntico.
Consecuencia: el reductor es **cota superior más débil** que la máquina, no su modelo; el puente va
al revés — (A) `máquina ⊆ reductor` + (B) reductor exacto en la clase ⟹ máquina exacta en la clase.
Ninguna demostrada. Alcance (v74): (A)+(B) darían exactitud a nivel de clave (sabor `OwnersExactAt`),
**no** `ClauseStepExact` (que es sobre nodos). Siguiente: enunciar y demostrar (A) sobre estados
alcanzables, vía `L1`/`ReqFiltered` + las dos pasadas de coherencia en los pasos de literal — el
primer trabajo de esta rama que toca `owners` de verdad.

Informe: `verificacion_inseguridad_autor_v75.md`.

**2026-09-11 (bf) — CORRECCIÓN: v71–v73 no toca la máquina.**

A pregunta del autor («¿por qué han desaparecido los owners?, ¿el modelo se ajusta a mi algoritmo?»),
comprobado sobre el repositorio: `CnfHypergraph.lean`, `CnfReducer.lean` y `CnfSelection.lean` tienen
**0 apariciones en código** de `owners`/`gowners`/`GPathM`/`PathNodeId`/`isValid`/`filterAll`/`review`/
`ChainSound` (4 en comentarios), y **ningún teorema** conecta `reduce`/`NoBacktrack` con
`FlipCore`/`ClauseStepExact`. Las campañas `--flipscope`, `--reducer` y `--pickstep` **no ejecutan la
máquina** (0 llamadas a `pureAdvance`; las de v66–v70, 20). Retiradas: la «correspondencia término a
término» (v71), «la fila que el reductor conserva *es* el índice del nodo superviviente» (v72), «ya no
es una analogía» (v72) y «`NoBacktrack` es lo único que queda para `FlipCore`» (v73 y docstring de
`CnfSelection`). Docstrings de los módulos corregidos. Diagnóstico: que los supervivientes del
semi-join coincidan con los de la poda de `owners` **es** `owners ⊆ support`, abierta desde v11 — la
ruta no rodea el muro, lo reencuentra en el puente; y `NoBacktrack` a solas daría BFMY 1983, mudo
sobre el algoritmo. Los teoremas de v71–v73 siguen válidos, sobre el reductor de fórmulas. Decisión
pendiente del autor: (1) medir la banda máquina↔reductor sobre estados reales, o (2) rehacer el
reductor sobre `owners`/`filterAll`/`review`.

Informe: `verificacion_inseguridad_autor_v74.md`.

**2026-09-11 (be) — La pieza 2, partida: el caso base demostrado, la diana medida, el teorema abierto.**

`CnfSelection.lean`: `allPairs`, `PairsCoherent`, `Agreeing`, `assignOfSel`, `selOfAssign`,
`forcedSel`, `RowsInAll`, `NoBacktrack`. Demostrados `Agreeing_of_pairwise`, `assignOfSel_eq`,
`sat_of_agreeing` (Helly en moneda de fórmulas, sin aciclicidad), `RowsInAll_*`, `clauses_reduceGo`,
`map_fst_initRels`/`_selOfAssign`/`_forcedSel`, `Agreeing_selOfAssign`,
**`satisfiable_iff_agreeing_in_reduce`** (el reductor no pierde nada),
`satisfiable_iff_nonempty_of_NoBacktrack`, y el caso base **`Agreeing_forcedSel`** →
**`NoBacktrack_of_singletons`** → `satisfiable_iff_nonempty_of_singletons`. Cierres
`[propext, Quot.sound]`; `beq_self_eq_true` vuelve a arrastrar `Classical` (se usa
`beq_iff_eq.mpr rfl`). Medido (`cnfmap --pickstep`, cinco semillas, 600 fórmulas): el reductor pinza
solo el 20 % de los prefijos de la clase (275/1.368); el paso de UNA elección es la obligación
equivocada — dentro de la clase 5.690/5.690 con toda fila válida, pero **Tseitin impar también da
736/736 y es UNSAT**; la diana correcta es el descenso completo: **dentro de la clase 1.368/1.368
llegan a una selección**, fuera 603 fallos sobre prefijos satisfacibles, y 0 éxitos sobre UNSAT en
todas partes (banda del caso base). Abierto: `NoBacktrack` bajo `BoundedScope`, por inducción sobre
las `K` rondas de `gyoIter_eq_nil_of_BoundedScope` — BFMY sin Mathlib, la parte cara.

Informe: `verificacion_inseguridad_autor_v73.md`.

**2026-09-11 (bd) — El reductor de semi-joins, formalizado en el modelo puro.**

`CnfReducer.lean`, sobre la codificación de filas de `CnfMap` (índices `1..7`, `b1`/`b2`/`b3`), no sobre
una representación nueva: `bitOf`, `varOfLit`, `rowPairs`, `pairsAgree`, `rowOk` (descarta filas que
fijan una variable dos veces de forma contradictoria — `WF` pide pasos distintos, no variables
distintas), `allRows`, `initRows`, `rowOfAssign`, `Rels`, `initRels`, `supported`, `sweep`,
`sweepWith`, `totalRows`, `reduceGo`/`reduce`. Demostrados sin hipótesis ni aciclicidad:
`b1_bits`/`b2_bits`/`b3_bits`, `varOfLit_bitOf`, `mem_rowPairs_rowOfAssign`, `pairsAgree_rowOfAssign`,
`mem_allRows_of_bits`; **conservación** `Carries_sweep` → `Carries_reduce` → `rowOfAssign_mem_reduce`
y `reduce_ne_nil_of_sat`; **terminación** `length_filter_lt`, `totalRows_sweepWith_le/_lt`,
`sweep_reduceGo`, `sweep_reduce`; **arco-consistencia** `eq_of_map_eq_self`,
`arcConsistent_of_sweep_eq`, `arcConsistent_reduce`, y `reduce_sound` juntando las dos mitades.
Cierres `[propext, Quot.sound]`: `reduceGo` usa igualdad decidible porque `beq_self_eq_true` arrastra
`Classical.choice` en este tipo compuesto. Medido (`cnfmap --reducer`, corre el reductor *del modelo*,
cinco semillas, 1.000 fórmulas, 16.349 prefijos): 0 prefijos SAT con relación vaciada (banda del
teorema); dentro de la clase 39/39 prefijos UNSAT detectados, fuera 9 de 688 sin detectar; control
Tseitin de paridad impar, exactamente 1 prefijo sin detectar cada una (la fórmula entera — la
consistencia de arcos no ve la paridad). Siguiente: pieza 2, el no-retroceso bajo `BoundedScope`
(inducción sobre `gyoIter_eq_nil_of_BoundedScope`), y pieza 3, el puente de vuelta a la cadena.

Informe: `verificacion_inseguridad_autor_v72.md`.

**2026-09-11 (bc) — La clase de alcance acotado: definida y estable; la reparación, corregida dos veces por la medición.**

`CnfHypergraph.lean`: `clauseEdge`, `cnfEdges`, `gyoIter`, `gyoRounds`, `prefixEdges`, `PrefixAcyclic`,
`BoundedScope φ K` (α-acíclico y ≤ `K` rondas GYO **en todos los prefijos** — la α-aciclicidad no es
hereditaria; testigo `{0,1},{1,2},{0,2},{0,1,2}` acíclico y su subfórmula no). Demostrados
`gyoIter_gyoRoundsGo`/`gyoIter_gyoRounds` (sin axiomas), `boundedScopeB_iff` + `Decidable`,
`gyoIter_eq_nil_of_BoundedScope`, `alphaAcyclic_of_BoundedScope`, `prefixEdges_take`,
`BoundedScope_prefix` (cerrada bajo prefijos). Cuatro ejemplos `decide`: 12 variables con la misma
`K = 2` que 3 (la clase no es «fórmulas pequeñas»), triángulo fuera a toda `K`. Tseitin (K4, K3,3,
prisma, cubo, Petersen, ambas paridades): fuera, núcleo cíclico de una arista por vértice. Medido
(`cnfmap --flipscope`, 5 semillas, 400 fórmulas, 3–6 vars, todos los prefijos, solo instancias con
solución reparada existente): reparación por **variable** 484 atascos de 47.663 dentro de la clase
(la Pieza 1 planeada era falsa); los casos son fórmulas con todas las cláusulas sobre un mismo
ámbito — una arista, varias relaciones — y la unidad correcta es la **fila**, que es lo que la
máquina mueve; por fila 25; los restantes son filas localmente válidas y globalmente muertas, que
elimina el **semi-join**; por fila tras el reductor **0 de 47.663** dentro, 1.192 de 415.984 fuera,
607 de 111.547 en los controles. Correspondencia término a término con la máquina (filas = nodos de
cláusula, semi-joins = pasadas de `review`, arco-consistencia ya demostrada en `ArcConsistency.lean`).
`FlipCore` para la clase **no** demostrado. Siguiente: relaciones y semi-join en el modelo puro, el
teorema de no-retroceso por inducción sobre las `K` rondas, y el puente de asignación reparada a
cadena de *ese* estado.

Informe: `verificacion_inseguridad_autor_v71.md`.

**2026-09-11 (bb) — El caso general: tríos, inserciones apuntadas, y la decodificación por prefijo.**

`cnfmap --triples` (máquina con triángulo, tres semillas): 905.506 tríos co-poseídos; 0 con un par sin
solución común; 38 sin solución común para los tres; 7 genuinos entre valores del mapa, todos ausentes de
toda solución vista (no es cosa de una clave). `cnfmap --insertgen` apuntado a los 7 (800 fórmulas) y al
hueco final de 777/3 (240 × 2 máquinas): 0 nodos zombie, 0 veredictos equivocados — fijar dos valores
propaga por las filas de cláusula hasta el tercero. `PrefixDecode.lean`: `litVal_of_reqSat_prefix`,
`satClause_of_reqSat_prefix`, `satUpTo_of_chain` (toda cadena de un estado intermedio satisface lo visto).
Caso general no demostrado; siguiente: teorema para una clase de alcance acotado, o búsqueda con paridad
sobre expansores (requiere implementación más rápida).

Informe: `verificacion_inseguridad_autor_v70.md`.

**2026-09-11 (ba) — El caso 17, el triángulo, y la conservación por prefijo.**

Caso 17 (`cnfmap --case17`): clave (17,4) fija x1=x4=x5=0; tres soluciones dentro; las 18 entradas son
x0=0 × x2=1, prohibido por la cláusula 1 una vez x5=0; sin owner común en los pasos 13–15. El review
solo mira un nodo cada vez. `TriReview.lean`: `triClean` (quita `q` de `owners(p)` si algún paso no
tiene owner común), `reviewTri`, `filterAllTri`; `ChainSound_triClean`, `ChainSound_reviewTri`.
`cnfmap --tri` (cinco semillas): entradas espurias 216 → 0 de 5.575.860, veredictos idénticos, 0
perdidas. `PrefixConservation.lean`: `SatUpTo`, `selOfAssign_onMap_of`, `chainSound_along_prefix`,
`selOfAssign_son_of`, `advance_target_prefix`, `Carries_pureAdvance_prefix`, `pureSteps_succ`,
`pureSteps_carries_prefix` — la conservación por prefijo en el driver. Siguiente: la dirección
contraria por prefijo (descodificar cadenas intermedias), para enunciar `FlipCore` sin grafo.

Informe: `verificacion_inseguridad_autor_v69.md`.

**2026-09-11 (az) — El filtro de cláusula, en piezas pequeñas.**

`ClauseFilter.lean`: `ClauseStepExact ⇐ OneReqStep` (un requisito cada vez; `SupportedS_filterAll_of_
OneReqStep`) `⇐` casos (a) `step_case_self`, (b) trivial, (c) `step_case_pinned`, todos demostrados, más
(d) `FlipCore` (cambiar un literal), el núcleo. `decides_of_FlipCore`. Medido (`cnfmap --flipcases`,
cinco semillas, 9.703 filtros, 593.472 instancias): (c) 58,0 %, (b) 12,8 %, (a) 5,2 %, (d) 24,0 %
resuelto, 0 fallos. Refutado: partir el núcleo en «dos supervivientes co-poseídos están en una cadena
común» — es la exactitud por pares, falsa por las 18 entradas del caso 17. Siguiente pieza demostrable:
conservación por prefijo, para enunciar `FlipCore` sin grafo.

Informe: `verificacion_inseguridad_autor_v68.md`.

**2026-09-11 (ay) — El invariante de nodo, demostrado salvo el filtro de cláusulas.**

`NodeInvariant.lean`: `NodeInv g := isValid g → SupportedS g`. `NodeInv_reachable` por inducción sobre
`Reachable`, con una sola hipótesis (`HardStepExact`): seed, join (`SupportedS_join`), addNode
(`SupportedS_addNode`), review (`SupportedS_review`), y los filtros fáciles (`SupportedS_filterAll_easy`:
sin requisitos, o uno sobre la cima; `TopKey_reachable` prueba que la cima lleva el id de la clave).
`easy_of_not_clause`: en un mapa 3SAT los pasos difíciles son exactamente los de cláusula
(`ClauseStepExact`, `NodeInv_of_ClauseStepExact`). `owns_required`: un superviviente del filtro de
cláusula es compatible con cada literal requerido por separado — el hueco con `ClauseStepExact` es
conjunto frente a pares (Helly). `Decision.lean`: `decides_of_ClauseStepExact` — satisfacible ⟺
`pureRun` acaba con un estado válido. Con la máquina polinómica, `ClauseStepExact ∀φ` ⇒ 3SAT ∈ P.

Medido: `cnfmap --insert` (640 fórmulas, cláusula insertada tras el estado del caso 17): 0 violaciones,
0 veredictos zombie. `cnfmap --tseitin`: K4, K3,3, prisma, cubo, 13 versiones UNSAT refutadas, 0
zombies (Petersen no terminó con la implementación en listas).

Informe: `verificacion_inseguridad_autor_v67.md`.

**2026-09-11 (ax) — El muro, releído con la definición de owners del autor; corrección a v60.**

El autor: los owners globales contienen todos los nodos mientras el grafo es válido, y los owners de un
nodo son los nodos compatibles con él, por paso. Formalizado como `OwnersExactAt` («todo owner de `r`
está en una solución común con `r`»). **Demostrado**: `Fabric_sol` (las soluciones por `r` forman un
tejido), `FabricAt_of_chain`, `alive_readStepSym_of_OwnersExactAt` (la definición implica que elegir `r`
no mata a ninguno de sus owners).

**Medido** (`cnfmap --tableexact`, cinco semillas): a longitud completa, 0 de 395.149 entradas espurias,
0 nodos sin solución, 0 nodos fuera de gowners, en finales y en lecturas. **Corrección a v60**: contra
las cláusulas vistas hasta cada paso (no la fórmula completa), los 7.790 estados intermedios dan 0 nodos
zombie de 188.435 y 18 entradas espurias de 4.362.215, todas en un estado (semilla 90210, caso 17, paso
18/40): nueve pares simétricos compatibles uno a uno sin solución conjunta. `--exactdiag` los lista;
`--hunt` añade cláusulas a esa fórmula: 0 veredictos zombie.

**El muro**: el invariante de *nodo* («todo nodo está en una solución de las cláusulas vistas») se
cumple en todo lo medido y es el candidato para inducir sobre la construcción; el de *tabla* (la
definición del autor) solo a longitud completa. Paso difícil: añadir una cláusula (información por
pares frente a compatibilidad conjunta).

Informe: `verificacion_inseguridad_autor_v66.md`.

**2026-09-11 (aw) — `Survive.Woven` generalizado: el tejido.**

`Fabric.lean` (nuevo). `Fabric g S T`: cada miembro conserva una subtabla `T p` de sus owners — simétrica,
dentro de `S`, con `p` en ella, con entrada en cada paso, y cada entrada respaldada por un padre y un
hijo del tejido (`up` / `down`). `Woven` es el caso `T p v := S v` (`Fabric_of_Woven`).

**Demostrado** (`[propext, Quot.sound]`): `Fabric_updateAt` / `_symmetrize` / `_unlink` / `_removeNode`;
`isValidNode_of_Fabric(_self)`; el bucle original entero (`FOk_review`, `isValid_filterAll_of_Fabric`,
generaliza `isValid_filterAll_of_Woven` y la cobertura sale de `support`); el simétrico con el pinchazo
por owners (`FOk_reviewSym`, `FOk_readStepSym`, `isValid_readStepSym_of_Fabric`); y
`isValid_readStepSym_of_FabricAt`.

**Medido** (`cnfmap --fabric`, cinco semillas): el mayor tejido dentro de `owners(r)` es **todo**
`owners(r)` en 4.888/4.888 elecciones (159.621 nodos), recortando 15.792 de 4.548.107 entradas (0,35 %).

**El muro, ahora estático:** *`owners(r)` contiene un tejido que pasa por `r`*. Candidato:
`owners(p) ∩ owners(r)` menos un 0,35 %; hay que demostrar que el recorte nunca vacía un paso (tipo Helly).

Informe: `verificacion_inseguridad_autor_v65.md`.

**2026-09-11 (av) — El review simétrico; y la lectura del autor, medida al pie de la letra.**

`SymReview.lean` (nuevo): `symmetrize` —cuando la tabla de `id` encoge, todo nodo fuera de ella pierde
`id` de la suya— detrás de cada intersección, en coherencia y barrida; `reviewSym`, `filterAllSym`,
y la lectura del autor, `pinOwners` (gowners ∩ owners(r), todos los pasos a la vez) + `reviewSym`.

**Demostrado** (`[propext, Quot.sound]`): `OwnSymmetric_symmetrize_updateAt` sin hipótesis más que la
simetría; de ahí `OwnSymmetric_reviewSym`, `_filterAllSym`, `_readStepSym`, `_read`. Conservación:
`ChainSound_symmetrize` (si una solución pasa por `id` y `m`, `m ∈ owners(id)`, así que el espejo no
toca entradas de soluciones), `ChainSound_reviewSym`, `ChainSound_pinOwners`, `ChainSound_readStepSym`.

**Medido** (`lake exe cnfmap`, `SymCampaign.lean`): `--symreview` 100 fórmulas, veredictos idénticos,
0 soluciones perdidas, asimetrías 132 (original) / 0 (simétrica, join y addNode incluidos), 0 fallos de
`PickValid` en 5.260 elecciones, 86/86 lecturas certificadas. `--pinexact`: **elegir `r` conserva
exactamente `owners(r)`** — 0 muertos de 195.167, 0 supervivientes fuera, 6.244 elecciones.
`--triangle`: 0 huecos en ~197.000 pares a longitud completa; 9 en >1M a longitud parcial (ambas
máquinas). `--selfsupport`: (b) padre/hijo dentro de `owners(r)` 0 fallos; (c) coherencia con tabla
intacta falla 1–2 % — las tablas encogen tras elegir aunque nadie muera.

**El muro, con forma:** *en un estado de longitud completa del review simétrico, elegir un nodo no mata
a ninguno de sus owners*. Ruta: generalizar `Survive.Woven` de cadenas co-poseídas a `owners(r)`, con
subtablas que encogen. Salvedad: el triángulo es 3-consistencia; cada paso de lectura pide un nivel más.

No se ha tocado la máquina original, el ejecutable ni Julia. Informe: `verificacion_inseguridad_autor_v64.md`.

**2026-09-11 (au) — La barrida, demostrada; y la simetría resulta ser cosa de los extremos.**

Cierra el cuarto punto que (at) dejó como argumento, y al medir su alcance encuentra el resultado
que de verdad importa.

**Demostrado** (`Reader.lean`, `[propext, Quot.sound]`): `OwnSymmetric_cleanInvalid` — la barrida no
puede romper la simetría, bajo `Ownership.NodesAreGowners`. El argumento en una línea: `cleanInvalid`
solo quita de una tabla ids que **no son owners globales**, y mientras todo nodo lo sea, un nodo no
se quita nunca de ninguna tabla. Con él: `NG_cleanInvalid` (la barrida conserva `NodesAreGowners`),
`OwnSymmetric_of_ownersEq` (todo estrechamiento que no toque las tablas transporta la simetría), las
inversiones de `node?` para `updateAt` / `unlinkIncompatible` / `removeNode`, y `not_gowner_invalid`
(un nodo degradado pierde la auto-posesión al intersecar, se queda sin owner en su propio paso y
falla `owners_ok`) — la mitad provable de la recuperación.

**Medido** (`lake exe extend --gowscope`, modo nuevo; cinco semillas, 76 estados finales, 5.864
nodos, 64 pinchazos):

| etapa | no-owners-globales | violaciones de simetría |
|---|---|---|
| estado final | 0 | 0 |
| tras `filterRequire` | 64 | — |
| tras `cleanInvalid` | **0** | **0** |
| tras `+ reviewParents` | — | **236** |
| punto fijo del review | 0 | **51** |
| final de la lectura | — | **0** |

Tres lecturas. (i) La **recuperación ocurre**: el pinchazo degrada 64 nodos y la barrida se lleva los
64, simetría 0 — el hueco entre el teorema y la barrida real es contabilidad que los números
confirman. (ii) La **coherencia la rompe**, pillada en el acto: 236 violaciones en una sola pasada.
(iii) **La simetría está en los dos extremos y no en el medio** — vale en el estado que la máquina
entrega y en el final de la lectura, no entre ellos. Misma forma que la exactitud de (v60): propiedad
de los estados sin elección pendiente, no invariante arrastrable.

**Consecuencia para la ruta de (as)/v61:** `chain_through_of_symmetric` sigue disponible sobre el
estado que la máquina entrega, pero **no se puede arrastrar a lo largo de una lectura**. Cualquier
plan que induzca sobre los pasos de lectura usando simetría en cada uno no funciona tal cual.

Informe: `verificacion_inseguridad_autor_v63.md`. Build verde, 87 módulos, 0 `sorry`, 0 axiomas.

**2026-09-11 (at) — Simetría: localizada en una sola operación, no demostrada.**

Intento de demostrar la simetría en longitud completa. **No sale.** Lo obtenido:

Evidencia reforzada: dos campañas más (`--finalowners`, semillas 90210 y 777, hasta 7 variables),
**0 violaciones en 11.009 nodos** en total sobre cinco semillas.

Localización, en `Reader.lean`: **`OwnSymmetric_addNode`** (el nodo nuevo se lleva todos los gowners
y todo nodo se lleva el nuevo — `all_previous_nodes_are_owners_of_me!`; con `NodesAreGowners` las dos
mitades encajan) y **`OwnSymmetric_filterRequire`** (solo toca los gowners). Ambas
`[propext, Quot.sound]`. `cleanInvalid` no puede romperla —interseca todas las tablas con la misma
lista y el id que sale de gowners pierde la auto-posesión y su nodo cae por `isValidNode`— pero la
barrida cambia los gowners al eliminar nodos, así que queda **argumentado, no demostrado**.
**`reviewNode` es la única operación sin contrapartida simétrica**: interseca con la unión de los
owners de los vecinos, que es una cantidad por nodo.

Razón de que la demostración directa no salga: una vez `reviewNode` quita `q` de `owners(p)`,
ninguna operación posterior quita `p` de `owners(q)` por sí sola; que al final coincidan es un hecho
semántico, no una consecuencia de las cláusulas de coherencia. Es decir, **la simetría es —como la
exactitud de (ar)— una propiedad del punto fijo, no un invariante arrastrable**.

Informe: `verificacion_inseguridad_autor_v62.md`.

---

**2026-09-11 (as) — La simetría vale en el estado final; `threaded` se da la vuelta.**

Aplicando la lección de (ar) —mirar el estado terminado, no el recorrido— dos modos nuevos:
`--finalowners` y `--finalthread`, ambos sobre `mirrorRun`.

**Simetría**: las 185 violaciones de v54 están **todas** en estados parciales. En la línea final:
**0 de 3.849 nodos**, 64 estados, semillas 2026/31337/4242. Explicación estructural: `addNode` da al
nodo nuevo todos los gowners y a nadie le añade el nodo nuevo; al completar el mapa `isValidNode`
obliga a un owner en el paso más alto y la asimetría se resuelve.

En `Threaded.lean`: `OwnSymmetric`, **`owners_contain_chain`** (la tabla de owners de un nodo
contiene una cadena completa enlazada padre→hijo, no solo una entrada por paso) y
**`chain_through_of_symmetric`** (con `SelfOwn.OOS`, esa cadena pasa por el nodo). Ambos
`[propext, Quot.sound]`, con la simetría como hipótesis explícita.

**Clique de owners**: falsa incluso al final (159.608/624.854, 208.820/1.145.170, 768.088/2.513.802)
— y es lo correcto: por (ar), los owners de un nodo son las proyecciones de *todas* las soluciones
que pasan por él, así que dos owners pertenecen a soluciones distintas. El enunciado local tiene que
ser por solución, no por nodo.

**Residuo al final** (`--finalthread`): cadena golosa co-poseída en 854/857 y 1.558/1.683; los 128
fallos los recupera la búsqueda; **0 zombis en 2.540 anclas**.

El muro pasa a ser: **el camino que un nodo posee es co-poseído**, con dos sub-objetivos nombrados —
la simetría en longitud completa (hipótesis medida) y la regla de elección (la golosa falla al 5 %).

Informe: `verificacion_inseguridad_autor_v61.md`.

---

**2026-09-11 (ar) — La conjetura medida semánticamente: exacta al final, no inductiva antes.**

Modo nuevo `lake exe cnfmap --exact`: enumera las 2ⁿ asignaciones, se queda con las que satisfacen φ,
y comprueba cuáles siguen «dentro» de cada estado (su nodo de mapa sigue entre los owners globales en
cada paso). Sin cadenas ni `Closed`.

Estados **finales**: 115 válidos en tres campañas (2026/31337/4242, 3..6 vars), **0 sin solución
dentro**, y 5.681 nodos de mapa supervivientes con **0 espurios** — los supervivientes son
*exactamente* los usados por soluciones supervivientes. Es la exactitud, no solo la no vacuidad.

Estados **intermedios que aún contienen solución**: 912 espurios de 10.239 (8,9 %) y 1.852 de 17.932
(10,3 %). **La exactitud no es un invariante arrastrable**: es falsa durante el recorrido y solo se
vuelve cierta al completarlo.

Consecuencia estratégica: la propiedad que uno querría inducir sobre la construcción **es falsa hasta
el último paso**, lo que explica el fracaso de v12, de `Inhabited_of_descent`, de la ruta A y de la
línea v54–v57. El objetivo pasa a ser un argumento de **punto fijo** sobre el estado terminado:
«todo owner global superviviente es usado por alguna solución superviviente», cuyo ⊇ es la ley de
conservación (demostrada) y cuyo ⊆ es el muro.

Informe: `verificacion_inseguridad_autor_v60.md`.

---

**2026-09-11 (aq) — `Woven`: las pasadas de coherencia cubiertas, y el pinchazo sobre la cadena.**

Cierra el hueco de v44. Aquel informe ya había desenrollado `share` hasta su punto fijo
(«una selección poseída por todos los miembros … eso es `PairwiseOwned`») pero la perseguía cadena
abajo. `Woven g S := Closed g S ∧ (∀ p n, S p → node? p = some n → ∀ v, S v → v ∈ n.owners)` la pide
directamente, y así **se mantiene sola**: las pasadas solo intersecan con listas que ya contienen a
todos los miembros.

Generalizadas: `Closed_updateAt_of` y `isValidNode_of_Closed_of` (contra cualquier lista `b` con
`S id → ∀ v, S v → v ∈ b`), más `isValidNode_of_Closed_self` (un miembro pasa el test tal cual).
Nuevas: `Woven.share_parents` / `share_sons`, `own_updateAt` / `own_unlink` / `own_removeNode` /
`own_cleanInvalidGo`, `Closed_reviewNode`, `Woven_reviewNode`, el bundle `WOk` (woven + SMP +
NotRoot) y toda la cadena calcada de `Sons.SMP_*`: `WOk_reviewNode_{parents,sons}`,
`WOk_reviewLine_{parents,sons}`, `WOk_reviewSteps_*`, `WOk_reviewParents`, `WOk_reviewSons`,
`WOk_cleanInvalid`, `WOk_reviewPass`, `WOk_reviewFuel`, `WOk_review`, `WOk_filterRequire`,
`WOk_filterAll`, y **`isValid_filterAll_of_Woven`**.

En `Reader.lean`: `ChainSet`, **`WOk_chainSet`** (cada cláusula de `Closed` es una de `IsChain` o
`PairwiseOwned`; la de posesión mutua **es** `PairwiseOwned`), **`isValid_pin_of_chain`** (pinchar
en el nodo que la cadena elige deja el grafo válido, pasadas incluidas) y **`PickSome_of_Inhabited`**.

Con `Inhabited_of_pickSome_readable` de (ap): **`PickSome` ⟺ `Inhabited`**. El muro queda solo:
existe una cadena co-poseída en todo estado válido. Todo `[propext, Quot.sound]`.

`diffTest` 200/200, `validate` 40/40. Informe: `verificacion_inseguridad_autor_v59.md`.

---

**2026-09-11 (ap) — El lector del diseño original, ensamblado.**

Corrección del autor: el lector no comprueba posesión dos a dos, **pina y propaga**. Leído
`src/graph_path/reader/path_reader.jl` y `graph_path_filter.jl`: `select_id!` toma `first(ids)` y
se queda con su **id de mapa**; `filter_require!` elimina en ese paso todo owner global que nombre
otro nodo de mapa; `make_review_owners!` es **recursivo** hasta que la bandera deja de levantarse;
el lector lanza `throw("GRAVE ERROR READER")` si el grafo deja de ser válido; termina con un nodo
de mapa por paso.

Eso ya era `PickInduction.Inhabited_of_pickSome` + `Pinned.inhabited_of_noChoice`. Lo que faltaba:
la inducción pide una clase cerrada bajo `filterAll`, y **todos** los invariantes estaban
enunciados para *un* `filterAll` sobre un `Reachable`.

`Model/NodeIds.lean` (nuevo): `Ids`, `ids_map`/`ids_filter` y la cadena completa
(`updateAt`, `unlinkIncompatible`, `removeNode`, `cleanInvalidGo`, `reviewNode`, `reviewLine`,
`reviewSteps`, `reviewPass`, `reviewFuel`, `review`, `filterRequire`, `filterAll`) hasta
**`NodupIds_filterAll`** — la hipótesis que `Filter.lean` y `PickInduction.lean` piden y nadie
descargaba.

`Model/Reader.lean` (nuevo): `RCtx` (OOS, SNN, GN, Shape, RootAtZero, PMP, NodupIds) con
`RCtx_reachable` y **`RCtx_filterAll`**; `Readable g := ∃ g₀ reqs, RCtx g₀ ∧ g = filterAll g₀ reqs`,
cerrada bajo pinado; `Ctx_of_readable`, `exists_isChain_of_readable` (sin hipótesis de
positividad), `inhabited_of_noChoice_readable`; **`Inhabited_of_pickSome_readable`**. Y
`nodup_addNode` / `nodup_up` / `nodup_join` / **`NodupIds_reachable`**, que descargan la última
hipótesis y dan **`Inhabited_of_pickSome_machine`**: el bucle del lector sobre los estados de la
máquina, con `PickSome` como única hipótesis. Todo `[propext, Quot.sound]`.

Mediciones: `--randomread` 40/40 (3.808 estados, 116.330 nodos, 0 inconclusos); `--pickvalid`
semilla 31337: 0 de 2.759 estados sin selección buena, 0 de 64.144 selecciones invalidan.

87 módulos. Informe: `verificacion_inseguridad_autor_v58.md`.

---

**2026-09-11 (ao) — Ataque a `GoodParentOnCliques`: tres atajos caídos, dos teoremas.**

Intento de demostración. **No cayó.** Lo obtenido:

Atajo 1 (padres hermanos anidados por inclusión ⟹ hay un padre máximo ⟹ la mitad *abajo* sale
gratis): **refutado** — de los pares de hermanos con owners distintos, **todos** son incomparables
(4.274/4.274 y 4.980/4.980, `--randomgoodparent`).

Atajo 2 (la mitad *arriba* se sigue de la de *abajo* en la configuración concreta): **refutado** —
0 fallos con semilla 2026 (175.294 configuraciones) pero **38 de 594.332** con semilla 31337
(`--randomupdown`), 37 de ellos a distancia ≥2. Recordatorio de correr dos semillas antes de
escribir Lean. Pero los 38 están **todos en nodos que ramifican**: en nodos con un solo padre,
**0 de 473.730**.

Atajo 3 (todo nodo tiene ≤2 padres ⟹ Helly trivial ⟹ el caso general se reduce a pares):
**refutado en general** — máximo 4 padres — pero ≥3 es **19 de 19.931** y **27 de ~20.000**, el
0,1 %.

Teoremas nuevos: `Threaded.owners_subset_of_unique_parent` (con `parents = [c]`, `hop_down` no deja
elección y `owners p ⊆ owners c` entero — la mitad *abajo* en el 80 % de las configuraciones) y
`Extendable.good_of_pairwise_two` (Helly sobre dos padres: bueno para cada par ⟹ bueno para toda
la exigencia), más `exists_false_of_all_false`. Todo `[propext, Quot.sound]`.

Residuo partido: mitad *abajo* con padre único **demostrada**; mitad *arriba* con padre único
0/473.730 sin demostrar; nodos de dos padres **reducidos a pares**; nodos de 3-4 padres (0,1 %)
necesitan Helly de verdad.

Informe: `verificacion_inseguridad_autor_v57.md`.

---

**2026-09-11 (an) — `GoodParentOnCliques`: el residuo deja de hablar de caminos.**

Dos modos nuevos. `--randomgoodparent`: los padres de un nodo **nunca** abarcan dos ids de mapa
(0 de 26.878 nodos, dos semillas) — `parent_id` decide el nodo de mapa del padre; pero hermanos con
ese mismo id tienen owners distintos en 5.182 pares, así que la decoración importa y el atajo se
cae. Pedirle a un padre que cubra *todos* los owners de arriba es falso: 948 de 26.878. Restringido
a los nodos cuyos owners-de-arriba forman una **transversal clique** (≤1 por paso, mutuamente
poseídos): 18.760 nodos, **0 fallos**.

`--randomclique`: enumeración exhaustiva de **todas** las sub-cliques por nodo (basta con las
maximales, pero se recorren todas). Semilla 2026, 3..5 vars: **154.635.941 exigencias coherentes,
0 sin padre bueno**, 315 de 6.947 enumeraciones cortadas por presupuesto.

En `Extendable.lean`: `Coherent`, **`GoodParentOnCliques`**, `mem_ownersAt`,
`node?_isSome_of_mem_ownersOf` y **`ExtendDownTop_of_GoodParentOnCliques`** — la historia de una
cadena parcial *es* una exigencia coherente hecha de los owners de `sel lo`, así que el padre que
el enunciado local produce es la extensión. En `DownVerdict.lean`:
**`Inhabited_of_GoodParentOnCliques`**. Todo `[propext, Quot.sound]`.

El residuo queda **local, de un paso, universal y sin cadenas**: falta intercambiar ∀∃ → ∃∀
*usando la coherencia de la exigencia*, que es justo la hipótesis que las mediciones señalan.

Informe: `verificacion_inseguridad_autor_v56.md`.

---

**2026-09-11 (am) — `ExtendDownTop`: el veredicto sin la mitad refutada.**

Reparo primero: `Extendable.ExtendDown` en general **también** está refutado (57 de los 1.574
callejones son bajando), así que el descenso goloso de (al) no era evidencia suficiente. Pero
`SupportedAt_of_Extend` solo aplica `hdown` a cadenas que **ya llegan al paso alto**, porque
`extendUpTo` corrió antes — subconjunto estricto.

`ExtendDownTop` (nuevo en `Extendable.lean`) es ese subconjunto. Modo `--randomdowntop`: desde cada
nodo del paso alto, DFS sobre **todas** las cadenas parciales hacia abajo. **0 callejones en 15.755
cadenas**, 5.393 anclas, 3.342 estados válidos, semillas 2026/31337/4242/90210, ninguna búsqueda
cortada por presupuesto.

Demostrado: `extendDownTopTo` (la inducción con `hi` fijo al techo),
`SupportedAt_top_of_ExtendDownTop`, y en el módulo nuevo `Model/DownVerdict.lean`
—aparte porque `PickInduction` importa `Extendable`— **`Inhabited_of_ExtendDownTop`**:
`isValid` + `GN` dan un nodo en el paso alto, el descenso lo enhebra, y
`Verdict.Inhabited_of_SupportedAt` cierra. `ExtendUp` no aparece. Ambos `[propext, Quot.sound]`.

El residuo queda desnudo: `Threaded.hop_down` da, para **cada** owner, **algún** padre que lo posee;
`ExtendDownTop` pide **algún** padre que posea **todos** los de la historia — un intercambio
∀∃ → ∃∀. Pista estructural de la medición: menos de tres cadenas por ancla, porque los padres de un
nodo comparten el id de mapa que `parent_id` codifica y solo se ramifica la decoración.

85 módulos. Informe: `verificacion_inseguridad_autor_v55.md`.

---

**2026-09-11 (al) — Ruta C atacada por medición: el residuo se reduce al descenso.**

Cuatro modos nuevos en `ExtendSearch.lean` / `ExtendMain.lean`, todos `IO` y sin teoremas:

`--randomsym` — simetría de la propiedad, partida por enlace / distancia / paso 0 / tras otro
`review`. **185 violaciones en 116.330 nodos, todas a distancia ≥ 2, ninguna en par enlazado, y
`review` no elimina ninguna.** La simetría es falsa y no es propiedad de punto fijo: la vía de
voltear `Threaded.threaded` (que da una cadena cuyos nodos poseen el ancla, cuando el residuo pide
lo contrario) queda cerrada.

`--randomthread` — construye ejecutablemente la cadena de `threaded` (goloso: primer hijo/padre que
posee el ancla) y comprueba `PairwiseOwned`. Nunca se atasca; co-poseída en 54.947 de 55.838.

`--randomsup` — para cada ancla que falla, DFS sobre todas las cadenas por ella (enlace padre→hijo
+ posesión mutua con el ancla y con lo elegido). **891 recuperadas, 0 presupuestos agotados,
0 zombis en 55.838 anclas** (2.375 estados válidos, semillas 2026/31337/4242). Primera medición
directa de `SupportedAt` sobre mapas de CNF reales; `l6search` solo cubría sintéticos.

`--randomhist` — goloso **con historia** (compatibilidad con todo lo ya elegido, sin backtracking).
Fallos: de 891 a **7**. **Bajando: 0 atascos en 55.838.** Los siete son todos subiendo — coherente
con que la máquina construya hacia arriba. Y separando las anclas del paso alto: **3.719/3.719**.

Consecuencia, usando que `Verdict.lean` solo necesita `SupportedAt` en **un** nodo: el objetivo
abierto pasa de `Supported` a **`DownH`** — «en un punto fijo de `review`, un nodo con paso > 0
tiene un padre mutuamente poseído con toda la historia» — local, de un paso, universal, una sola
dirección, y con la forma que `Threaded.hop_down` ya tiene demostrada para el ancla sola.

Informe: `verificacion_inseguridad_autor_v54.md`.

---

**2026-09-11 (ak) — El bucle del driver conserva la rama: teorema.**

La contabilidad que (aj) dejó nombrada, cerrada. En `Model/PureDriver.lean`: `StateOk` (clave en
el mapa, `MapReachable`, `current_step`, `map_parent`, validez — los tres últimos campos son
literalmente lo que pide `okJoin`), `LineOk` (claves `Nodup` + `StateOk` de cada entrada) y
`Carries` (la entrada de la rama). El lema bisagra es **`Carries_insertPure`**: insertar en otra
clave deja la entrada intacta, insertar sobre ella la fusiona con `join`, y `AlongAssign.joinL`
cubre ese caso — ninguna de las dos operaciones del driver puede perderla.

`pureAdvance` se partió en `sendTo` / `sendAll` (preserva la semántica; la banda `--driver` lo
confirma) para poder razonar fold a fold: `StateOk_sent` → `LineOk_sendTo` → `LineOk_sendAll` →
`LineOk_pureAdvance`; `sons_fold_establish` (el fold interno **crea** la entrada al llegar al hijo
que `advance_target` señala) → `outer_fold_mono` → **`Carries_pureAdvance`**. Con `init_ok`
(`AlongAssign.seed` en la primera línea) y `run_ok` (inducción sobre los pasos), sale
**`pureRun_full_state`**: para *toda* asignación satisfactoria, la última línea tiene una entrada
en su nodo final, con `current_step = stepCount φ`, válida e `Inhabited`. Y `pureRun_ne_nil`.

Piezas nuevas fuera del fichero: `mapNodes_step` y `mapSons_subset` en `GraphMap/CnfSel.lean` (un
hijo de un nodo del mapa es un nodo del mapa un paso arriba; el único caso no trivial es el enlace
cruzado de variable).

Trampa: `isValid_initSeed` con `simp` ancho arrastraba `Classical.choice`; reescrito vía
`PickInduction.isValid_of_gowner` vuelve a `[propext, Quot.sound]`.

Bandas: `cnfmap --driver` 30/30 (2026) y 100/100 (31337), `cnfmap` 200/200 (7), `diffTest` 300/300
(2026). `lake build AbsSat` verde, 84 módulos, 0 `sorry`. Informe: `verificacion_inseguridad_autor_v53.md`.

---

**2026-09-10 (aj) — El driver, puro y validado.**

`mirrorRun` vive sobre `GMap` (`Std.HashMap`) y razonar ahí arrastraría `Classical.choice`, así
que se aplica una tercera vez el patrón del proyecto (`GPathM` frente a `GPath`, el modelo
aritmético frente a `ImportCnf`): **`Model/PureDriver.lean`** define `insertPure`, `pureAdvance`,
`pureInit`, `pureRun` — el mismo bucle con `mapSons` / `reqOfCnf` / `mapNodes` en lugar de
`map_node.sons` / `destine_node.requires` / `get_ids_step`.

**Banda `lake exe cnfmap --driver`**: compara `pureRun φ` con `mirrorRun gmap` en claves de la
línea final, recuento de nodos por clave y validez. 30/30 (2026), 100/100 (90210), 60/60 (4242)
— **190 instancias, 0 desacuerdos**. Los títulos no se comparan a propósito.

**El teorema — `advance_target`** (cierre `[propext, Quot.sound]`): desde el estado aparcado en el
nodo de la asignación en el paso `k`, (i) el hijo al que el driver va a moverse **es** el nodo de
la asignación en `k+1`, (ii) el estado que construye allí es `AlongAssign`, y (iii) **pasa el
filtro de validez**. Los tres conjuntos son justo lo que `pureAdvance` necesita en ese punto.

**Lo que queda no es matemático:** que los dos `foldl` anidados conserven la entrada una vez
insertada. Tres invariantes, nombrados en el módulo — claves nodup; `current_step`/`map_parent`/
validez uniformes (para que `okJoin` valga); y `MapReachable` de todo estado (para `joinL`). Con
ellos, `mem_insertPure` y `mem_insertPure_of_ne` (ya demostrados) llevan la entrada por ambos
folds y `pureRun` acaba no vacío siempre que φ sea satisfacible.

84 módulos. Documento: `verificacion_inseguridad_autor_v52.md`.

**2026-09-10 (ai) — La rama es un camino del mapa, y llega hasta el final.**

La salvedad que (ah) dejó abierta. Leyendo `add_var!`: los positivos se enlazan al bloque de
negación **cruzados** (`"v=0"`→`"!v=1"`), y el resto del mapa es completo entre pasos
consecutivos. Eso son dos líneas de aritmética (`CnfSel.mapSons`), y con ellas:

    selOfAssign_son : selOfAssign φ a (k+1) ∈ mapSons φ k (selOfAssign φ a k).index

**La rama que nombra una asignación es un camino a lo largo de las aristas del propio mapa.**
El caso de variable es el bonito: el único hijo de `⟨2v, bit(a v)⟩` es `⟨2v+1, 1 − bit(a v)⟩`,
que es `⟨2v+1, bit(¬a v)⟩` — **el cruce del mapa y la negación de la asignación son la misma
operación**, y eso estaba ya en `add_var!`.

Y la rama se recorre entera (`Model/Conservation.lean`):

    alongAssign_exists      : ∀ n < stepCount φ, ∃ g, AlongAssign φ a g ∧ current_step = n+1
    exists_full_valid_state : ∃ g, AlongAssign φ a g ∧ current_step = stepCount φ
                                   ∧ isValid g ∧ Inhabited g

La recursión necesita en cada paso que el grafo filtrado siga válido para que `up` tome la rama
de `addNode`, y esa validez **la da la propia ley de conservación** (`isValid_filterAll_along`):
la inducción se alimenta a sí misma, sin hipótesis metidas a mano.

**Verificado, no supuesto:** la banda `cnfmap` compara ahora pasos, nodos, requisitos **e hijos**:
40/40 (semilla 2026) y 120/120 (90210), 0 desacuerdos; malformadas 30 saltadas / 10 de acuerdo /
0 desacuerdos; `diffTest` 150/150.

**Queda:** el driver como teorema — `mirrorRun` vive sobre `GMap`/`HashMap` y razonar ahí
arrastraría `Classical.choice`; cerrarlo pide un driver puro sobre el modelo aritmético validado
diferencialmente, que es el patrón de siempre y es acotado. Y «sin zombis», y la complejidad.

83 módulos. Documento: `verificacion_inseguridad_autor_v51.md`.

**2026-09-10 (ah) — La ley de conservación: el veredicto cerrado por los dos lados.**

**Corrección de estrategia, a partir de una observación del autor** («el conjunto válido contiene
de forma abstracta no una solución sino todas las soluciones»): el enunciado no es una existencia
sino una **conservación**, y por eso los cinco intentos anteriores chocaban con el mismo muro —
producir un testigo a partir de un conjunto construido por podas es justo la parte dura.

**El teorema** (`Model/Conservation.lean`, cierres `[propext, Quot.sound]`):

    AlongAssign φ a g   -- la rama de la máquina que sigue a la asignación `a`
    chainSound_along : WF φ → Sat a φ → AlongAssign φ a g →
      ∃ sel, ChainSound g sel ∧ ∀ k en rango, (sel k).id = selOfAssign φ a k

El testigo **viene de fuera**: lo entrega la asignación. La máquina solo tiene que no destruirlo.

**Los cuatro pasos ya estaban demostrados** y nadie los había encadenado así:
`ChainSound_initSeed` y `ChainSound_upFiltering` (`AddNode.lean`), `ChainSound_join_left/right`
(`JoinSound.lean`). La hipótesis que pide el paso del filtro es `CnfSel.reqSat_selOfAssign`,
demostrada hoy en M3 — sin ella la inducción no cerraba.

**Gratis:** `isValid_of_ChainG` convierte la supervivencia de la cadena en la validez, luego
`isValid_along`: **la máquina no puede invalidar un estado que todavía contiene una solución.**
La validez pasa de obligación a consecuencia.

**`sound_and_complete`** junta las dos direcciones con `L7.sat_of_inhabited`: que el conjunto de
la máquina sea no vacío **es** la satisfacibilidad.

**No cierra:** `AlongAssign` es una rama — el paso de ahí a `mirrorRun` es la siguiente pieza,
contable; «sin zombis» sigue abierto (lo necesita el lector sin retroceso); y la complejidad
sigue sin un solo teorema.

83 módulos, `diffTest` 150/150, `cnfmap` 60/60, `validate` 40/40.
Documento: `verificacion_inseguridad_autor_v50.md`.

**2026-09-10 (ag) — Recap de estado (v49).**

Informe auditado contra el árbol, no contra la memoria. Higiene comprobada: 74 módulos, **0**
`sorry` (las tres apariciones del texto son comentarios), **0** axiomas de proyecto, **0**
`native_decide`, **106** pines `#print axioms`; todos los cierres `[propext, Quot.sound]` o más
finos **salvo tres** en `MapReqs` que arrastran `Classical.choice` y están pinados como tales.

**Encuadre corregido: la cadena de validación tiene cinco eslabones**, y solo uno es el problema
abierto. (1) CNF→GMap **sin verificar** — `ImportCnf` es `IO` y no hay semántica booleana
formalizada; (2) GMap→estados **demostrado**; (3) estado válido→cadena **abierto**; (4)
cadena→asignación satisfactoria **sin verificar**; (5) ejecutable↔espejo **empírico**.
Los eslabones 1 y 4 son los que convierten «hay una cadena» en «la fórmula es satisfacible»:
sin ellos el resto habla de un grafo, no de 3SAT.

**Siguientes pasos, por rentabilidad:** (1) cerrar 1 y 4 —definir `CNF`/`Assignment`/`satisfies`,
`buildMap` puro, L7 y la vuelta para UNSAT; criterio de hecho:
`Inhabited (machine (buildMap φ)) → ∃ a, satisfies a φ` sin axiomas—, que **no depende del
problema abierto**; (2) el residuo, con tres frentes concretos (la regla de elección medida sobre
los 6.371 descensos que fallan, buscar contraejemplo sin `Reachable`, y mirar el conjunto
candidato con la lupa 0/1/all); (3) el refinamiento F6 como teorema, después del eslabón 3;
(4) higiene de `Classical.choice`. **No** empezar por la complejidad.

Documento: `verificacion_inseguridad_autor_v49.md`. Versión navegable publicada como artifact.

**2026-09-10 (af) — Estudio: el paso 0 y la barrida de hijos (pregunta del autor).**

**Origen de los rangos.** El espejo copia al ejecutable y este a Julia:
`review_owners_parents_sons!` barre `1:S-1`, `review_owners_sons_parents!` barre `S-2:-1:1`.
Tres cotas están forzadas (el paso 0 no tiene padres; la cima no tiene hijos; la cima sí tiene
padres). **La cuarta —la inferior de la pasada de hijos— no**: un nodo del paso 0 sí tiene hijos.
Forma de cota copiada del otro bucle.

**No es fallo de corrección.** La omisión solo agranda `owners`, luego nunca invalida de más y no
puede dar un UNSAT falso. Medido (`extend --zerosons`): de 3.292 nodos del paso 0, **3** perderían
owners (15 entradas) y **0** quedarían inválidos; segunda semilla, 7.333 → **51** (317 entradas),
**0** inválidos. Poda perdida, no error de veredicto.

**Impacto en la demostración, probado aplicándolo.** Con `reviewSons` sobre
`intRange 0 (current_step - 2)` la reconstrucción de los 74 módulos rompe **exactamente tres
anotaciones de rango** (`GPathM.reviewSons`, `Fuel.review_owners_coherent_sons` ×2,
`ArcConsistent.coherent_sons`) y **ninguna demostración**. La razón: el lado de la preservación
**ya estaba demostrado para el paso 0** — `ChainSound_reviewLine_sons` pide `0 ≤ k` y
`ChainSound_reviewSteps_sons` pide `∀ k ∈ ks, 0 ≤ k ∧ k+1 < cs`.

Se gana: `Threaded.hop_up`, `Survive.support_above` y **`Survive.son_of_hop_up`** pierden
`1 ≤ p.id.step` — y lo último **cierra el hueco de (ae)**, dejando `Closed_PinSet` con una sola
hipótesis. Además las dos cláusulas de arco-consistencia quedan simétricas.
No se gana: el residuo `support` a distancia ≥ 2 no se mueve (mismas 3.473.942 comprobaciones).

**Comportamiento:** `diffTest` (ejecutable + espejo + fuerza bruta) 150/150 y 400/400 con el
espejo extendido.

**Aplicado** (decisión del autor, mismo día) a **ejecutable y espejo** en un commit propio.
La copia de Julia queda intacta como registro histórico y los docstrings de procedencia dicen
ahora que divergen deliberadamente. Pago cobrado: `Survive.Closed_PinSet` e
`isValid_cleanInvalid_pin` pasan de **dos hipótesis a una** — solo `support`.
Verificado: `lake build AbsSat` verde (74 módulos, 0 `sorry`), `diffTest` **400/400** (semilla
2026) y **300/300** (90210), `validate --random 50` **50/50** con 4.835 estados e `Inhabited`
certificado en todos, y `extend --zerosons` pasa de 3 nodos con soporte rancio a **0** con el
mismo recuento de nodos raíz y de estados válidos — se podó basura, no se perdió nada.

Documento: `verificacion_inseguridad_autor_v48.md`.

**2026-09-10 (ae) — El espejo inverso (`SN`, `PMS`), y los dos huecos que cerraba.**

    SN  h := ∀ n ∈ h.nodes, ∀ s ∈ n.sons, HasNode h s
    PMS h := ∀ n ∈ h.nodes, ∀ s ∈ n.sons, ∀ m ∈ h.nodes, m.id = s → n.id ∈ m.parents
    SN_reachable, PMS_reachable  (cierres [propext, Quot.sound])

**Nota de método.** Toda la mitad de poda de `PMS` —`updateAt`, `removeNode`,
`unlinkIncompatible`, `cleanInvalidGo`, `reviewNode`, las barridas, el fuel, `filterAll`— es el
calco literal de las demostraciones de `SMP` con `parents`/`sons` intercambiados, y compiló
entera sin retoques. Eso **es** el arreglo del autor: `unlinkIncompatible` desenlaza por los dos
lados con los mismos owners decidiendo, luego la demostración es simétrica bajo el intercambio.
Solo `addNode` —la única operación que crea enlaces— hubo que escribirla a mano.

**Hueco 1 cerrado.** `Threaded.hop_up_zero`: un hijo del nodo del ancla tiene al ancla entre sus
padres (`PMS`), el puente lo hace owner y `SAbove` pone el paso. Luego **`threaded` pierde
`1 ≤ a.id.step`**: todo nodo está en un camino completo 0→cima cuyos nodos lo poseen todos. Y
`Survive.pinSet_covers` deja de tener salvedad (cubría el 95,1 % de las elecciones; ahora todas).

**Hueco 2 cerrado.** `Survive.son_of_hop_up`: `hop_up` da un hijo candidato y `PMS` gira el
enlace, produciendo el enlace de padre que `Closed.son` pide — **para pasos ≥ 1**. Queda fuera
un candidato en el paso 0 con el pinchazo en otro paso.

**Sigue abierto:** `support` a distancia ≥ 2 (0 de 3.473.942), y con él `CoreCovers`/`PickValid`.

`lake exe diffTest 200`: 200/200. Documento: `verificacion_inseguridad_autor_v47.md`.

**2026-09-10 (ad) — `support` a distancia ≥ 2: dos refutaciones y una caracterización.**

**Refutado 1 — `Survive.PinSetDownClosed`** (todo owner de un candidato es candidato). Habría
hecho `support` gratis vía `owners_ok`. `extend --downclosed`: 722.851 de 3.723.185 (semilla
2026) y 1.418.285 de 6.271.084 (semilla 90210). Luego **el ∃ de `support` es esencial**.

**Refutado 2 — `Survive.AnchoredDescentStaysInSupport`** (el descenso anclado al pinchazo se
queda dentro de los owners del nodo de partida). Era el testigo obvio: `hop_down` garantiza que
todo el descenso son candidatos, y el puente regala el primer salto. `extend --descentin`: se
sale en 6.371 de 125.528 descensos (28.665 de 1.315.726 saltos) y 17.499 de 208.331 en la otra
semilla. Luego `support` es cierto pero **no por la construcción natural**.

**Demostrado — `Threaded.owner_below_on_descent`** (cierre `[propext, Quot.sound]`): todo owner
por debajo de un nodo está en un descenso desde él —cadena de padres cuya cima es `p`, cuyos
nodos poseen todos a `v`— y el nodo en el paso de `v` **es `v`**, por `OOS`. Con el puente esto
encierra la tabla de owners:

    parents(p) ⊆ owners(p) en el paso de abajo   (v39)
    owners(p) en l ⊆ ancestros de p en l          (aquí)

y la transitividad refutada de (v40) dice que ninguna es igualdad.

De paso, `descend_T` y `threaded_below` se fortalecen para conservar el nodo de partida.

**El residuo queda**: cierto (0 de 3.473.942), estrictamente existencial, y sin construcción.
Lo que falta no es un lema más sino una **regla de elección**: entre los descensos que arrastran
el pinchazo, uno que se quede dentro del soporte del candidato.

Documento: `verificacion_inseguridad_autor_v46.md`.

**2026-09-10 (ac) — `CoreCovers` partido: la cobertura del candidato es teorema.**

El núcleo se obtiene estrechando `PinSet g k mid = {p : p posee, en el paso k, algo con id de
mapa mid}`. Dos preguntas separadas, y la primera está cerrada:

    pinSet_covers : ∀ l en rango, ∃ p, PinSet g q.id.step q.id p ∧ p.id.step = l

directo de `Threaded.threaded` (v42). La dificultad no es si hay candidatos —los hay en todos los
pasos, demostrado— sino si la compatibilidad sobrevive a su propia clausura.

**Cadena completa** (`Model/Survive.lean`, cierres `[propext, Quot.sound]`):

    Closed_PinSet          : gow (vía OOS), node, parent (hop_down), coown (bridge) — demostradas
    isValid_cleanInvalid_pin : del pinchazo a isValid (cleanInvalid (filterRequire g q.id))

con **solo** `hsupport` y `hson` como hipótesis.

**`support` gratis en cuatro pasos** — `support_at_pin`, `support_at_self`, `support_below`,
`support_above`. Los dos últimos existen **solo gracias al arreglo del bug** (v37–v39): el puente
hace owner a todo padre y a todo hijo, y `SAbove` pone el paso del hijo. Luego el residuo es
`support` **a distancia ≥ 2**, que es donde la transitividad refutada de (v40) lo habría llevado.

**Medido** (`extend --closed`, contando solo el residuo): 3.473.942 comprobaciones lejanas,
**0** fallos; `son` 237.503 / **0**. De las 4.357.895 de v43, un 20 % pasó a ser teorema.

Documento: `verificacion_inseguridad_autor_v45.md`.

**2026-09-10 (ab) — `support` retirado de la cuenta: queda un solo enunciado.**

Las seis cláusulas de `Closed` son de la forma «un miembro tiene un miembro entre sus …», luego
son cerradas bajo unión — y `coown` **no depende del conjunto** (`coown_of_bridge`, v43), que es
lo que hace que la unión cierre. Por tanto el mayor conjunto auto-sostenido las cumple por
construcción (`Model/Survive.lean`, cierres `[propext, Quot.sound]`):

    Core g p       := ∃ S, Closed g S ∧ S p
    Core_greatest  : Closed g S → ∀ p, S p → Core g p
    Closed_Core    : SMP g → LinksInOwners g → Closed g (Core g)
    CoreCovers g   := ∀ l en rango, ∃ p, Core g p ∧ p.id.step = l
    isValid_cleanInvalid_of_CoreCovers : SMP → LinksInOwners → CoreCovers g →
                                          isValid (cleanInvalid g) = true

**Todo lo que `cleanInvalid` debe tras un pinchazo es `CoreCovers`.** Un enunciado, sin cadenas,
sin `isValidNode`, sin el bucle de fuel. No está demostrado: es `PickValid`.

**Medido sin circularidad** (`extend --core`: el núcleo se calcula estrechando los gowners bajo
las cláusulas de `Closed`, nunca llamando a `isValidNode`): 7.664 pinchazos / **0** pasos vacíos
(semilla 2026) y 17.213 / **0** (semilla 90210). Núcleos de ~25–30 entradas por pinchazo.

**El muro desde tres lados** (todos el mismo): `PairwiseOwned` en la cadena (v28–v42), `support`
en el camino testigo (v43), y `share` en las pasadas de coherencia — esta última porque
`reviewNode` intersecta con la unión de los **vecinos**, lo que pide un testigo común entre
miembro y padre-miembro; propagada por la cadena de miembros da una selección poseída por todos,
cuyos elementos se poseen entre sí, que es `PairwiseOwned`.

Documento: `verificacion_inseguridad_autor_v44.md`.

**2026-09-10 (aa) — Supervivencia a `cleanInvalid`: el testigo es un conjunto, no un camino.**

**El hallazgo estructural.** `cleanInvalid` reintersecta los owners con los gowners *actuales*,
que encogen según elimina. Luego un nodo solo sigue pasando `isValidNode` si en cada paso tiene
un owner **que también sobrevive**; iterando, el testigo debe estar cerrado bajo su propio
soporte. Y **un camino cerrado bajo su propio soporte es `PairwiseOwned`** — de ahí que v27 y
v41 no puedan cerrar esto: no les falta un ingrediente, les sobra la forma. Pero `isValid` pide
un owner global por paso, no una cadena.

**El teorema** (`Model/Survive.lean`, 74 módulos, cierres `[propext, Quot.sound]`):

    Closed g S : gow, node, support, parent, son, coown  (ver el módulo)
    Closed_cleanInvalidGo      : SMP g → Closed g S → Closed (cleanInvalidGo g ids) S
    isValid_cleanInvalid_of_Closed : + cobertura de todos los pasos → isValid (cleanInvalid g)

Corazón: `isValidNode_of_Closed` — cada cláusula de `isValidNode` la contesta una de `Closed`.
La inducción reestablece las seis cláusulas en las tres suboperaciones (intersección de owners,
`unlinkIncompatible`, `removeNode`). Diseño clave: `Closed.son` se escribe por la tabla de
**padres**, así `SMP` la gira y el espejo inverso nunca se usa dentro del teorema.

**Gratis:** `coown_of_bridge` (SMP gira el enlace de padre, el puente de v39 hace owner a los dos
extremos) — cierre `[propext]`, sin `Quot.sound`.

**El residuo:** `support` — *en cada paso, un miembro posee a un miembro*. Es `PickValid` sin
cadenas: dice que el núcleo arco-consistente del pinchazo no se vacía.

**Medido** (`extend --closed`, dos semillas): support 667.682 / **0** y 4.357.895 / **0**;
la cláusula `son` 45.312 / **0** y 237.503 / **0** — el hueco del espejo es de formalización,
no de matemáticas.

Documento: `verificacion_inseguridad_autor_v43.md`.

**2026-09-10 (z) — `SAbove` demostrado; el enhebrado completo.**

**El invariante que (y) dejó nombrado** (`Model/Sons.lean`, cierre `[propext, Quot.sound]`):

    SAbove h := ∀ n ∈ h.nodes, ∀ s ∈ n.sons, s.id.step = n.id.id.step + 1
    SAbove_reachable : Reachable reqOf g → SAbove g

Más barato que `SMP` porque `SAbove` es **local**. Un solo lema cubre toda la poda:

    SonsSub g g' := ∀ n' ∈ g'.nodes, ∃ n ∈ g.nodes, n'.id = n.id ∧ ∀ s ∈ n'.sons, s ∈ n.sons
    SAbove_of_SonsSub : SonsSub g g' → SAbove g → SAbove g'

`updateAt`, `removeNode`, `unlinkIncompatible`, `filterRequire` son `SonsSub`; el resto de la
review se compone. La única operación con contenido es `addNode`: la guarda de `upSons` reparte
el nodo nuevo justo a la línea de un paso por debajo.

**El enhebrado completo** (`Model/Threaded.lean`):

    threaded : 1 ≤ a.id.step → ∃ sel, IsChain g sel ∧ ∀ i en rango, a ∈ ownersOf g (sel i)
    threaded_filterAll : lo mismo sobre los estados de la máquina

Dos mitades con ingredientes distintos: **subir** con `coherent_sons` + `SAbove` (solo
existencia, sin enlaces — así se esquiva el espejo hijos→padres, que no tenemos), y **bajar**
con `coherent_parents`, que sí da el enlace que `IsChain` pide.

**Fuera: el paso 0.** `reviewSons` barre `1 .. current_step-2`, nunca el 0, así que
`coherent_sons` calla ahí y `climb` no puede arrancar. Medido (`extend --pickvalid`):
**3.090 de 63.314** elecciones permitidas están en el paso 0 — 4,9 %. Cerrarlo pide extender la
barrida (toca el ejecutable) o el otro espejo de la tabla de hijos (invariante distinto de
`SAbove`, con la inducción que necesitó `SMP`).

**Y aun con eso**, tener el camino no es `PickValid`: falta la inducción sobre `cleanInvalidGo`
que demuestre que el camino **sobrevive** a la poda tras el pinchazo. No está escrita.

Documento: `verificacion_inseguridad_autor_v42.md`.

**2026-09-10 (y) — `PickValid`: obligación debilitada, riesgo localizado, y el enhebrado por debajo.**

**No cerrado.** Tres avances:

1. **`PickInduction.PickSome`** — la inducción de v19 consume *una* elección buena por etapa,
   no todas. `Inhabited_of_pickSome` corre sobre la forma ∃; `measure_lt_of_choiceAt` mantiene
   gratis el decrecimiento. `PickSome_of_PickValid` cierra la comparación.
   Medido (`extend --pickvalid`, 40 instancias): 2.794 estados con elección, **63.314** elecciones,
   **0** invalidan — la forma ∀ también aguanta, así que la debilitación compra tamaño, no un hueco.

2. **Riesgo localizado** (`extend --sweep`, 25 instancias, 39.984 elecciones): `cleanInvalid` sola
   deja el grafo inválido **0** veces; la review completa, **0**; las pasadas de coherencia quitan
   nodos extra en **67** elecciones (185 nodos). `PickValid` es en la práctica un teorema sobre
   `cleanInvalid`, la pasada que hace el trabajo del pinzado.

3. **`Model/Threaded.lean`** — el ingrediente. `coherent_parents` da que si `d` posee `a`, algún
   padre de `d` posee `a`; bajando con eso:

       TPart g a sel lo hi  := PartialChain g sel lo hi  ∧  ∀ i en rango, a ∈ ownersOf g (sel i)
       threaded_below       : ∃ sel, TPart g a sel 0 a.id.step

   **Todo nodo tiene un pasado enhebrado**: un camino desde el paso 0 cuyos nodos poseen todos el
   ancla. Un ancla común, no co-posesión por pares — estrictamente entre v27 y `PairwiseOwned`, y
   demostrado. Ensamblado en `threaded_below_filterAll`. Módulos: 73.

**El hueco, nombrado.** El ascenso por `coherent_sons` funciona pero entrega un nodo **sin paso**.
Falta el espejo de `Parents.PBelow` para la tabla de hijos — **`SAbove`: todo hijo está un paso
por encima** — que no sale de `Pruned` (lleva `owners ⊆` y `parents ⊆`, **no** hijos) y necesita la
inducción operación por operación que necesitó `Sons.SMP`. Anotado en `Threaded.lean` donde iría
`hop_up`.

**Y aun con el camino completo** faltarían las dos pasadas de coherencia: para que un nodo del
camino conserve soporte en un paso `l` cualquiera hace falta que comparta owner con su vecino *en
ese* paso, y el ancla común solo lo da en el paso del ancla.

Documento: `verificacion_inseguridad_autor_v41.md`.

**2026-09-10 (x) — `PairwiseOwned` en el régimen pinzado, y el caso base de A′ descargado.**

**Refutado primero:** `Pinned.OwnersTransitive` — la posesión no se propaga por los enlaces.
`extend --randomtrans`, 20 instancias: global 2.950.784 / 22.521.728; bajando (q padre de n,
r owner de q por debajo) **15.240 / 420.078**; subiendo (q hijo de n) **18.919 / 416.403**.
Era la vía natural que abría `Bridge.linksInOwners_review`; queda cerrada.

**La ruta que sí cierra** (`Model/Pinned.lean`, 72 módulos, cierres `[propext, Quot.sound]`):

    PinnedAt h k    := ∀ q r ∈ ownersAt h.gowners k, q.id = r.id
    FullyPinned h   := ∀ k en rango, PinnedAt h k

    pid_unique                  : FullyPinned → un solo PathNodeId por paso
    pairwiseOwned_of_fullyPinned: FullyPinned → IsChain → PairwiseOwned

Dos clavos fijan un `PathNodeId`: el **id de mapa** (el filtro pinza `gowners`, la review
intersecta, `SelfOwned` mete el id propio del nodo en la intersección) y el **`parent_id`**
(`PMP`: nombra el id de mapa de los padres, que viven en el paso de abajo, también pinzado).
Con un solo candidato por paso, la co-posesión no se demuestra: no hay otra cosa que el owner
pueda ser.

**Y eso es el caso base de la ruta A′.** `PickInduction.NoChoice` desplegado *es* `FullyPinned`
escrito con `Bool`; ambos sentidos demostrados (`fullyPinned_of_noChoice`,
`noChoice_of_fullyPinned`). De ahí `inhabited_of_noChoice_filterAll`, con el camino puesto por
`PathExists.exists_isChain`. El `hbase` que v19 dejó pendiente queda **descargado**; a
`Inhabited_of_pickValid` le queda solo `PickValid`.

**No vacío** (`extend --nochoice`, dos semillas): 1.284 de 4.835 y 2.685 de 15.362 estados
válidos son `NoChoice`; en **los 3.969** el paso más ancho tiene exactamente **1** id distinto,
que es lo que `pid_unique` predice.

**Sigue abierto:** `PairwiseOwned` fuera del régimen pinzado, y `PickValid`.

Documento: `verificacion_inseguridad_autor_v40.md`.

**2026-09-10 (w) — El puente, demostrado; el espejo migrado.**

**El teorema** (`Model/Bridge.lean`, cierre `[propext, Quot.sound]`):

    LinksInOwners h := ∀ pid d, h.node? pid = some d →
      (∀ p ∈ d.parents, p ∈ d.owners) ∧ (∀ s ∈ d.sons, s ∈ d.owners)

    linksInOwners_review   : isValid (review g) = true → LinksInOwners (review g)
    linksInOwners_filterAll: isValid (filterAll g reqs) = true → LinksInOwners (filterAll g reqs)

Enunciado sobre `node?`, no sobre `n ∈ h.nodes`: así no hace falta unicidad de ids, y
encaja con la moneda en la que el resto de los módulos consulta el grafo.

**Ruta** (tres pasos, todos ya disponibles tras la migración): en un punto fijo válido cada
`cleanStep` es la identidad (`Fuel.review_cleanStep_fixed`) → el desenlace de dentro es la
identidad (`Fuel.intersectOrDrop_valid_branch`, ahora terna) → los enlaces ya estaban dentro
de los owners (`Fuel.relinkSelf_eq_self_of_fixed` + `links_of_relinkSelf_eq`).

**Migración del arreglo del autor al espejo, completa.** `GPathM.relinkSelf`/`relink`/
`unlinkMap`/`unlinkIncompatible`, cableados en `cleanInvalidGo` y `reviewNode` en el mismo
orden que el ejecutable. Reparados: `Pruned` (`pruned_unlinkIncompatible`), `Fuel`
(`measure_unlinkIncompatible_le`, `unlinkIncompatible_eq_self`, `relinkSelf_eq_self_of_fixed`,
toda F2.c), `CleanInvalid` (`ChainSound_unlinkIncompatible`), `Coherence`, `GownersNodes`
(`GN_unlinkIncompatible`), `Parents` (`PN_unlinkIncompatible`), `Sons` (`SMP_unlinkIncompatible`,
el delicado), `SelfOwn` (`OOS_unlinkIncompatible`). `lake build AbsSat` verde, 71 módulos, 0 `sorry`.

**Error de diseño corregido:** la primera `unlinkMap` filtraba los enlaces del vecino contra
*sus propios* owners; eso rompía `Pruned` con ids repetidos y rompía `SMP`. La correcta filtra
los enlaces del objetivo contra `n.owners` dejando `m.owners` intacto — los owners del nodo
podado deciden en los dos lados, como en el desenlace simétrico del ejecutable.

**Medición antes/después con las mismas banderas y semilla** (el *antes* se obtuvo guardando la
migración y volviendo a medir):

- `extend --randombridge 60` (161.839 nodos, 174,7 k enlaces): 5 padres y 2 hijos fuera de
  owners → **0 y 0**.
- `extend --stale 100 90210 3 8` (la campaña de (u)): **277** nodos con padre rancio → **0**,
  con los mismos 2.563.751 pares consecutivos de cadenas req-satisfactorias y 0 excepciones.
- `validate --random 60 2026 3 5`: 60/60 limpias, 5.466 estados válidos, 161.839 nodos,
  5.466 `Inhabited` certificados — mismo recuento de nodos que antes, así que no se poda de más.

**Consecuencia:** se retira el aviso de (u) sobre `PathExists.exists_isChain` — el padre
arbitrario que elige el descenso es ahora necesariamente owner. `ParentId.ParentIsOwner` y
`SonIsOwner`, refutados en (u), pasan a ser consecuencias del teorema sobre los estados que
importan. Sin cambio en lo abierto: **`PairwiseOwned`**.

Documento: `verificacion_inseguridad_autor_v39.md`.

**2026-09-09 (v) — Bug real corregido en el ejecutable, y el puente formalizado.**

**El bug, reportado por el autor** a partir de la medición de (u): la poda de owners debe
**desenlazar a los padres incompatibles**, y un nodo que se queda sin padres se invalida y se
elimina, porque nunca podría formar parte de una cadena solución.

**Corregido en `GraphPath.lean`:** `unlink_incompatible!`, llamada tras las dos
intersecciones de owners (`clean_invalid_nodes!`, `review_owners_line!`). Desenlace
**simétrico** —si `n` pierde a `p` como padre, `p` pierde a `n` como hijo— para no romper
`Sons.SMP` (n). `remove_if_invalid_node!` hace el resto.

**Validado:** `diffTest` **800/800** contra el oráculo (701 SAT, 99 UNSAT), veredictos y
conjuntos completos de soluciones **sin cambio** — que es el único resultado aceptable para
un arreglo que solo poda lo ya inservible.

**`Model/Bridge.lean` — el puente como teorema.**

    LinksInOwners h : ∀ n ∈ h.nodes, (∀ p ∈ n.parents, p ∈ n.owners) ∧ (∀ s ∈ n.sons, s ∈ n.owners)

- `linksInOwners_relinkSelf` / `linksInOwners_at` — **el arreglo lo establece por
  construcción** en el nodo sobre el que actúa.
- `pruned_unlinkIncompatible` — solo quita enlaces, luego todo lo que da `Pruned` atraviesa
  la operación. Es lo que hace segura la migración.
- `chain_link_survives` — **por qué la migración saldrá**: el enlace padre de una cadena
  sonora sobrevive al desenlace *precisamente porque la cadena está co-poseída*, y
  `PairwiseOwned` ya es un campo de `ChainSound`.

**Estado de la migración del espejo** (intentada y revertida para no romper el build):
`GPathM` (definiciones + pasos cableados), `Pruned`, las cotas de medida de `Fuel` y **F2.c
entero** funcionan; faltan `CleanInvalid`, `Coherence`, `Review`, `AddNode`, cada una
necesitando `ChainSound_unlinkIncompatible`, cuyo argumento es `chain_link_survives`.
Mientras tanto el espejo poda menos que el ejecutable; la diferencia es conservadora y
`diffTest` valida ambas bandas.

**Nota de método:** el puente pasó de **refutado** (u, 37 testigos que escalaban) a **cierto
por construcción** (v) por un cambio en el algoritmo, no por una demostración mejor. Solo
pasa cuando lo que falla es un defecto y no una conjetura — a diferencia de `Extendable`, el
clique del soporte, la simetría, la aciclicidad y `ArcImpliesChain`, que siguen refutados.

Documentado en `lean_project/verificacion_inseguridad_autor_v37.md` y `..._v38.md`.

**2026-09-09 (u) — El puente `owners`/`parents`: refutado en general, cierto en cadenas.**

**El candidato mínimo.** `OwnerMatchesPredecessor` pide que un `PathNodeId` concreto esté en
una lista de owners. Los dos libros se construyen aparte (`addNode` + `intersectOwners` vs
`newParents`), y el puente mínimo sería que coincidan en los enlaces directos.

**Refutado.** `lake exe extend --randombridge`, 60 instancias, 282.077 nodos: **37** enlaces
padre y **71** enlaces hijo de 328.086 faltan de los owners (0,011 %). Registrados en
`ParentId.lean` como `ParentIsOwner` / `SonIsOwner`, refutados.

**La razón, en el código:** la poda de owners **nunca desenlaza un padre** — `removeNode` sí,
pero `intersectOwners` solo encoge `owners`. Un nodo puede conservar un predecesor
estructural que la propagación ya descartó. **De los dos libros, el obsoleto es `parents`.**
Observación sobre la implementación, no recomendación: el lector filtra por requisitos, no
camina `parents` a ciegas.

**Cierto donde hace falta.** `lake exe extend --stale`, dos semillas: **3.556.470** pares
consecutivos de caminos req-satisfactorios, **0** con el padre fuera de los owners. Los
**313** nodos con enlace rancio están fuera de todo camino req-satisfactorio. Asimetría
significativa: los enlaces rancios **escalan** con el tamaño de la campaña (36 → 277); las
excepciones en cadenas no aparecen nunca. Enunciado como
`ChainParentIsOwner` — que es `OwnerMatchesPredecessor` para `req.step = j-1`.

**Aviso sobre (l)/v27.** `PathExists.exists_isChain` desciende eligiendo un padre
*cualquiera*, y ahora se sabe que hay enlaces padre rancios de verdad: el camino que ese
teorema construye puede usar uno. La distancia entre `IsChain` y `ChainSound` no es una
precaución teórica.

**Resultado negativo sobre la estrategia:** el puente **no es estructural**. La pieza que
falta sigue necesitando el lado del mapa; no se saca de cómo están construidas las listas.

Documentado en `lean_project/verificacion_inseguridad_autor_v36.md`.

**2026-09-09 (t) — Revisión externa: el lema propuesto es falso; la mitad pinzada se reduce a
una existencia.**

**Contexto.** Otro agente revisó el estado con el código delante. Verificado y correcto:
`ReqSatImpliesOwned` es un `def`, no un teorema; `ChainSound_of_parts` está listo para
consumirlo; y —lo más valioso— **`PMP` es sobre el grafo estructural (`n.parents`) mientras
`owners` es otro libro de contabilidad**, así que `parentId_coherent` **no** se aplica a un
owner cualquiera. Eso corrige una frase de (s)/v34 §4.

**Lo que hay que corregir de su propuesta.** Propuso
`owner_at_req_eq_chain_pick : ∀ q ∈ ownersAt n.owners req.step, q = sel req.step`. **Es
falso.** Medido sobre nodos *de cadena* (`lake exe extend --randompinnedchain`, 60
instancias) y semilla 90210 (100 instancias): **4.429.212** pares (nodo de cadena,
requisito) en total, de los cuales **1.035.280 (23,4 %) tienen conjunto de owners de ancho
≥ 2**. Lo que `PairwiseOwned` necesita es **pertenencia**,
estrictamente más débil.

**Su pregunta empírica, respondida:** la elección de la cadena falta del conjunto de owners
**0** veces; owners que casan con el predecesor de la cadena: ninguno **0**, exactamente uno
**4.429.212**, dos o más **0**. **Siempre exactamente uno**, en dos semillas.

**Lo demostrado (`Model/ParentId.lean`):**

- `owner_eq_chain_pick` — un owner del paso pinzado que lleve el `parent_id` de la cadena
  **es** la elección de la cadena (un `PathNodeId` son dos campos; el id de mapa lo daba
  `owner_at_req_shares_mapid` de (r)).
- `OwnerMatchesPredecessor` — la obligación restante: **existe** un owner con ese
  `parent_id`.
- `chain_pick_mem_owners` — y con esa existencia sale la pertenencia.

**Dónde atacar ahora**, coincidiendo con la revisión: un **puente entre el libro de `owners`
y el de `parents`** — que las pasadas de coherencia (`intersectOwners` contra
`unionOwnersOf`) no expulsen justamente al owner que la rama estructural conserva.

**Anotado, porque nadie lo había dicho:** `PairwiseOwned` pide **todos** los pares `(i,j)`;
esto solo cubre aquellos donde `i` es un paso que un requisito de `sel j` nombra. Los pares
**no pinzados** no tienen requisito en el que apoyarse y no tienen reducción — solo la
medición global de (p).

Documentado en `lean_project/verificacion_inseguridad_autor_v35.md`.

**2026-09-09 (s) — La condición local sobre `parent_id`: una cadena está determinada por sus
ids de mapa.**

**`parent_id` no es decoración.** `addNode` construye `⟨d, g.map_parent⟩` y da al nodo nuevo
como `parents` la línea anterior de la misma rama. De ahí dos invariantes, en
`Model/ParentId.lean`:

- **`TL`** — la línea de arriba de un estado lleva el nodo de mapa que nombra `map_parent`.
- **`PMP`** — todo padre de un nodo lleva el id de mapa que nombra el `parent_id` del nodo.

Demostrados para toda la máquina (`TL_reachable`, `PMP_reachable`, `PMP_filterAll`); `TL` es
lo que hace pasar el caso `addNode` de `PMP`.

**La condición local — `parentId_coherent`:** `(sel (k+1)).parent_id = some (sel k).id`. El
enlace padre de `IsChain` leído sobre los ids.

**Lo que fuerza — `chain_eq_of_mapIds_eq`:** dos cadenas que coinciden en todos los ids de
mapa **son la misma cadena**. Paso 0 por `root_shape` (n); cada paso siguiente por
`parentId_coherent`.

**Efecto sobre (r).** Aquel decía "en un paso pinzado hay a lo sumo dos `PathNodeId` y falta
que la cadena elija el que está ahí". **Ya no hay elección:** el path-node está determinado
por el id de mapa del requisito (`ReqSatisfying`) más el id de mapa del paso de abajo
(`parentId_coherent`). Lo que queda es una **pertenencia** de un elemento concreto, no una
búsqueda. Y explica el factor dos medido: los dos owners corresponden a dos ids de mapa
distintos en el paso inferior, y la cadena ya ha elegido uno.

**Quinta vez que la pieza que falta es una decisión de diseño del autor:** ligar `parent_id`
a `map_parent` hace que el `PathNodeId` codifique un paso de historia — lo que v14 había
observado sin ver para qué servía.

Documentado en `lean_project/verificacion_inseguridad_autor_v34.md`.

**2026-09-09 (r) — El hueco de `ReqSatImpliesOwned`, acotado a factor dos.**

**Dónde está el hueco.** `ReqSatisfying` habla de **ids de mapa**
(`(sel req.step).id = req`); `PairwiseOwned` habla de **`PathNodeId`s**. Varios path-nodes
comparten id de mapa y difieren solo en `parent_id`, así que acertar el id de mapa no mete el
nodo concreto en la lista de owners. Ese es todo el hueco de la mitad pinzada.

**Demostrado — `MapChain.owner_at_req_shares_mapid`:** en un paso que algún requisito de
`sel j` nombra, **todos** los owners de `sel j` ahí coinciden con la elección de la cadena en
el id de mapa (L1 los pinza a `req`; la cadena req-satisfactoria elige `req`). Solo puede
diferir el padre.

**Medido — `lake exe extend --randompinned`, dos semillas (160 instancias):** semilla 2026 →
466.889 pares, 45.086 (9,7 %) con dos; semilla 90210 → 1.188.019 pares, 121.983 (10,3 %) con
dos. **Total 1.654.908 pares; el conjunto más ancho visto es 2, nunca tres.** El conjunto de owners en un paso pinzado es
a lo sumo un par `{⟨req, p₁⟩, ⟨req, p₂⟩}` — el mismo nodo de mapa desde dos padres.
Registrado como `MapChain.PinnedWidthTwo` (medido, no demostrado).

**La segunda obligación no se disfraza:** "existe un camino req-satisfactorio en cada estado
válido" **es** la afirmación central en la dirección de (q). Ocho reducciones acabaron ahí.
Lo que hay es la medición: 19.327 estados válidos, 0 sin camino.

**Contexto de credibilidad del arnés:** ha refutado cinco cosas — `Extendable` (l),
aciclicidad (i), `ArcImpliesChain` (i), clique del soporte (m) y simetría de posesión (m,
corrigiendo al propio autor de la entrada).

Documentado en `lean_project/verificacion_inseguridad_autor_v33.md`.

**2026-09-09 (q) — Corrección del autor: el mapa dibuja, la máquina garantiza.**

**El error de (p).** Glosé la obligación restante como "existe un camino que satisface los
requisitos — que en un mapa 3SAT es, palabra por palabra, que la fórmula sea satisfacible".
Eso mezcla el mapa con la máquina. El autor:

> El mapa con los requisitos **dibuja** la expresión 3SAT en términos que la máquina
> entiende, pero el dibujo **no garantiza** que deba existir un camino que satisfaga la
> expresión que representa. Es la máquina la que, después de procesar el mapa, si obtiene un
> conjunto válido, entonces **sí** garantiza que la fórmula es satisfacible. Y la máquina
> podría también no poder construir paso a paso un conjunto solución, y ahí tendríamos la
> detección de UNSAT.

Si el dibujo certificara la satisfacibilidad, el mapa **sería** el solver. La implicación va
**de la validez a la solución**, y la produce la máquina.

**Enunciado correcto de la obligación:** *existe un camino que satisface los requisitos en el
estado válido que la máquina sostiene.* No es una propiedad del mapa. Y el lado UNSAT no es
una omisión sino el diseño: si la máquina no puede construir el conjunto, el grafo se
invalida, toda obligación sobre grafos válidos es vacía, y esa incapacidad *es* el veredicto
(ya colocado bien en (f), tapado por la frase de (p)).

Corregido el docstring de `MapChain.lean` y la §5 de v31.

**Y la corrección permite medir la obligación de frente.** Planteada sobre los estados de la
máquina es comprobable, cosa que sobre el mapa no lo era. Añadido el contador
"estados válidos sin ningún camino req-satisfactorio" a `lake exe extend --randomreqpaths`:
semilla 2026 (3–9 vars, 60 instancias) → 6.548 estados; semilla 90210 (3–10 vars, 100
instancias) → 12.779 estados. **Total 19.327 estados válidos, 0 sin camino**, con dos
semillas independientes.

**Estado:** las dos obligaciones restantes (`ReqSatImpliesOwned` y la existencia del camino)
están **medidas y en pie**, y **ninguna es sobre el mapa**: las dos son sobre lo que la
máquina sostiene después de procesarlo.

Documentado en `lean_project/verificacion_inseguridad_autor_v32.md`.

**2026-09-09 (p) — `PairwiseOwned` por la estructura del mapa: entra por los requisitos.**

**Dónde entra el mapa.** Un requisito pinza un nodo en un paso (`MapReqs.Functional`, 0/1/all);
los `owners` son tablas que la máquina estrecha y que (h) demostró que **no** heredan esa
forma. Luego la condición natural a nivel de mapa sobre una cadena es **satisfacer los
requisitos**, no la co-posesión — y no menciona `owners`.

**`Model/MapChain.lean`.**

- `ReqSatisfying` — la condición a nivel de mapa.
- **`reqSatisfying_of_pairwiseOwned`** — demostrado: la co-posesión implica satisfacer los
  requisitos. Es L1 (`ReqFiltered`) leído a lo largo de la cadena: la co-posesión mete
  `sel req.step` en los owners de `sel k` en ese paso, y L1 dice que ese conjunto entero
  proyecta a `req`. Es la dirección que consume `ChainSound_filterAll`.
- `ReqSatImpliesOwned` — la recíproca, abierta. Había razón para desconfiar: (h) mostró que
  los `owners` son más estrechos que las restricciones crudas.

**Medición (`lake exe extend --randomreqpaths`), dos semillas independientes:** semilla 2026
(3–9 vars, 60 instancias) → 6.548 estados, 89.104 caminos; semilla 90210 (3–10 vars, 100
instancias) → 12.779 estados, 261.139 caminos. **Total: 160/160 instancias, 19.327 estados,
350.243 caminos que satisfacen los requisitos, 0 no co-poseídos.** Los owners son más estrechos que las restricciones crudas, pero no tanto como
para excluir un camino que respeta los requisitos.

**La ensambladura — `ChainSound_of_parts`.** Reúne `IsChain` (l), `son_link` y `root_shape`
(n), `self_owned` (o), y deja `ChainSound` saliendo de **exactamente dos** enunciados
abiertos:

1. **existe un camino que satisface los requisitos** — en un mapa 3SAT, *que la fórmula sea
   satisfacible*;
2. `ReqSatImpliesOwned` — medido, sin violaciones.

El punto 1 no es un lema que se escape: **es la afirmación central del autor**. Lo que cambia
en esta entrada es *dónde* está: ya no repartido entre owners, cadenas, invariantes y pasadas
de coherencia, sino en un solo sitio y en el vocabulario del mapa.

Documentado en `lean_project/verificacion_inseguridad_autor_v31.md`.

**2026-09-09 (o) — `self_owned` cerrado. `ParentOwns` no hacía falta.**

**Lo que (n) tenía incompleto.** La recursión mutua `SelfOwned` ↔ `ParentOwns` es real para la
ruta *directa*. Lo que faltaba ver es que la auto-posesión **no hay que llevarla como
invariante**.

**`Model/SelfOwn.lean` — el invariante que solo encoge.**

    OOS h : ∀ n ∈ h.nodes, ∀ q ∈ n.owners, q.id.step = n.id.id.step → q = n.id

En su propio paso, los owners de un nodo no contienen nada más que a él. Cierto **desde el
nacimiento**: `addNode` da al nodo nuevo `gowners ++ [pid]`, y todos los gowners están en
pasos estrictamente inferiores. Y estable, porque todas las demás operaciones **solo quitan**
owners — un invariante que solo encoge no pelea con la pasada de coherencia. Demostrado para
toda la máquina (`OOS_reachable`), más `SNN` (los pasos son ≥ 0) que hacía falta para
instanciar el rango.

**Y la auto-posesión es consecuencia, no invariante:** `SelfOwned_of_OOS` — en un punto fijo
válido todo nodo pasa `isValidNode`, que exige un owner en cada paso incluido el suyo; por
`OOS` ese owner solo puede ser el nodo mismo. De ahí `SelfOwned_filterAll`.

`ParentOwns` se conserva en `Sons.lean` marcado como la ruta que no hace falta.

**Estado de `ChainSound`: cinco de seis.** `IsChain` ✔ (l), cláusula `gowners` ✔ (k),
`son_link` ✔ (n), `root_shape` ✔ (n), `self_owned` ✔ (o). Queda **`PairwiseOwned`** — la
Helly (m), y es el único de los seis que no es una propiedad local preservada operación a
operación.

**Anotado:** cuarta vez que una decisión de diseño del autor resulta ser justo la pieza que
falta — `okJoin` exigiendo validez de ambas ramas (k), `up` devolviendo el grafo invalidado
sin añadir nodo (k), `MachineOk` ligando `map_parent` a `current_step` (l, n), y ahora
`addNode` dando `gowners ++ [pid]` con los gowners por debajo (o).

Documentado en `lean_project/verificacion_inseguridad_autor_v30.md`.

**2026-09-09 (n) — `son_link` y `root_shape` cerrados; `self_owned` es de otra clase.**

**`Model/Sons.lean`.**

- **`SMP`** — si `p` es padre de `n`, `n` es hijo de `p`. Demostrado para toda la máquina:
  `filterRequire`, `updateAt`, `removeNode` (filtra padres **e** hijos por el mismo id, así
  que el reflejo sobrevive), la cadena de `review`, `addNode` (necesitó `PBelow` y
  `steps_below_current` para descartar que un padre fuese el nodo nuevo), `join` (necesitó
  `PN` de ambas ramas) e `initSeed`. De ahí `SMP_reachable` y `SMP_reachable_filterAll`.
- **`RootAtZero`** — un nodo del paso 0 es raíz; espejo de `NotRoot` (l). En `addNode` sale
  de `MachineOk` (tercera vez que esa pieza resulta ser justo la que falta).
- **Los puentes:** `son_link_of_SMP` (el enlace padre de `IsChain` se da la vuelta) y
  `root_shape_of` (`RootAtZero` abajo, `NotRoot` arriba).

**`self_owned`, y por qué no salió.** `SMP` y `RootAtZero` hablan de `parents`/`sons`/`id`,
que las pasadas de review nunca tocan salvo al eliminar un nodo con sus enlaces:
incondicionales. `Ownership.SelfOwned` habla de `owners`, que es lo que las pasadas podan:

- bajo `cleanInvalid`, `n.id` sobrevive la intersección con `gowners` solo si
  `n.id ∈ gowners` — o sea dado `NodesAreGowners` (medido, no demostrado);
- bajo `reviewNode`, sobrevive solo si **algún vecino posee a `n`** — que es `ParentOwns`.

Y `ParentOwns` se preserva solo dado `SelfOwned`. **Mutuamente recursivas**: hace falta
inducción simultánea sobre la máquina arrastrando también `NodesAreGowners`. Enunciado
(`ParentOwns` en el código con el mecanismo al lado), no intentado.

**Estado de `ChainSound` (seis requisitos):** `IsChain` ✔ (l), cláusula `gowners` ✔ gratis
(k), `son_link` ✔ (n), `root_shape` ✔ (n), `self_owned` abierto pero acotado, `PairwiseOwned`
abierto — la Helly (m). **Cuatro de seis.**

Documentado en `lean_project/verificacion_inseguridad_autor_v29.md`.

**2026-09-09 (m) — `PairwiseOwned`: la vía barata, refutada con coste demostrado.**

**Por qué esta es distinta.** Todas las obligaciones cerradas hasta ahora eran **locales**
(propiedad de un nodo o de una operación, preservada paso a paso: `GownersAreNodes`,
`MachineOk`, `PN`, `PBelow`, `NotRoot`). `PairwiseOwned` es una propiedad de una **selección
global**; no hay inducción sobre operaciones que la dé. Así que primero se midió.

**`lake exe extend --owners`,** sobre cada estado válido que la máquina sostiene:

Campaña de 80 instancias: 7.800 estados válidos, 259.187 nodos.

| propiedad | violaciones |
|---|---|
| `nodes ⊆ gowners` | **0** |
| auto-posesión | **0** |
| **simetría de la posesión** | **1.364**, en 19/80 instancias — **refutada** |
| **clique del soporte** | **63.917.242**, en 80/80 — **refutado** |

**Corrección propia anotada:** la primera redacción daba la simetría por buena con 0
violaciones, a partir de **cuatro instancias elegidas a mano**. La campaña la refuta. Cuatro
instancias no son una medición, y el arnés de campañas estaba disponible. Mecanismo:
`reviewNode` intersecta contra la **unión sobre los vecinos**, que no es simétrica — el mismo
mecanismo que identificó (h).

**El coste de la refutación, demostrado.** `Model/Ownership.lean`:
`SupportClique_gives_PairwiseOwned` — si el soporte de un nodo fuera un clique, cualquier
cadena sacada de ese soporte estaría co-poseída **gratis**; y (l) ya construye caminos. Las
dos juntas habrían cerrado `ChainSound`. El clique falla por cuatro órdenes de magnitud.

**Y eso es la Helly en el vocabulario de la máquina:** dos nodos pueden ser ambos compatibles
con `t` e incompatibles entre sí. Explica por qué (h) anchura, (i) hipergrafo y (l)
`Extendable` se quedaban cortas: todas intentaban sacar información global de información
por pares, y la medición dice que la información por pares no la contiene.

**Dianas demostrables que quedan:** `SelfOwned` (con `self_owned_of_SelfOwned` ya demostrado,
cierra directamente una de las tres condiciones que faltan de `ChainSound`) y
`NodesAreGowners` — las dos con 0 violaciones sobre 259.187 nodos y del tipo que sí se sabe
demostrar (idioma de (j) y (l)). No hechas en este turno. `OwnersSymmetric` queda refutada y
anotada en el código como invariante plausible pero falso.

**Lo que no se afirma:** `PairwiseOwned` no está demostrado y no parece salir de más
invariantes estructurales. Lo que queda ahí es matemática sobre la red de restricciones que
genera el mapa, no fontanería sobre el grafo.

Documentado en `lean_project/verificacion_inseguridad_autor_v28.md`.

**2026-09-09 (l) — `IsChain` demostrado. `PairwiseOwned` queda aislado.**

**`Model/Parents.lean` — tres invariantes de forma.**

| | |
|---|---|
| `PN` | todo padre de un nodo superviviente es un nodo superviviente |
| `PBelow` | un padre está exactamente un paso por debajo |
| `NotRoot` | un nodo por encima del paso 0 no es raíz |

`PBelow` y `NotRoot` salen **gratis de `Pruned`** (`nodes_derived` da que los padres encogen y
los ids no cambian), luego solo hay que demostrarlos en `initSeed`, `addNode` y `join`. `PN`
no: `Pruned` registra que los padres encogen, no que los nodos que nombran sobrevivan —
cierto porque `removeNode` desenlaza el id que elimina, pero hay que probarlo operación por
operación como en (j). `NotRoot` en `addNode` sale de `MachineOk` (el nodo nuevo lleva
`parent_id := map_parent`, y `MachineOk` da `map_parent ≠ none` en cuanto `current_step > 0`).
Empaquetados en `Shape`, con `Shape_reachable` y `Shape_filterAll`.

**`Model/PathExists.lean` — el descenso.** `parents_ne_nil_of_isValidNode` (un nodo no raíz
tiene padres), `step_down` (un paso hacia abajo desde una `PartialChain`), `descend`
(inducción sobre `lo.toNat`) y **`exists_isChain`**: partiendo de un nodo del paso más alto
(`node_at_every_step`, (j)) se baja hasta el paso 0. `IsChain` demostrado.

**El matiz, anotado:** el camino construido **no tiene por qué estar co-poseído** — se elige
un padre cualquiera en cada paso. Construir *un* camino es fácil; construir *un camino
co-poseído* es el problema. Esto es progreso de fontanería, no de matemáticas. Lo que gana el
proyecto es que `PairwiseOwned` queda **completamente aislado**: ya no hay nada mezclado con
él que sea cuestión de invariantes de la máquina.

**Restos de `ChainSound`:** `root_shape` parece casi inmediato desde `NotRoot`; `son_link`
pediría un invariante de simetría padre/hijo (mismo idioma); `self_owned` es menos claro
porque `intersectOwners` puede quitarlo. `PairwiseOwned` no parece alcanzable por esta vía.

Documentado en `lean_project/verificacion_inseguridad_autor_v27.md`.

**2026-09-09 (k) — `FilteredChain`: separada la vacuidad de la elección; la vacuidad, demostrada.**

**`Model/Candidates.lean`.** Una cadena es una *selección*, así que antes de preguntar si
existe una coherente hay que saber si hay algo que seleccionar. Hasta (j) no se podía
responder — y por eso `degenerate` funcionaba: soporte no vacío que no nombra nada.

- `owner_mem_gowners` — los owners de un nodo superviviente son owners globales
  (`owners_mem_gowners` + `review_owners_within_gowners` + `hasStepEntry_of_isValid`).
- **`owner_is_node`** — encadenado con `GownersAreNodes` (j): **todo owner de un nodo
  superviviente es él mismo un nodo superviviente.** Justo lo que a `degenerate` le faltaba.
- **`candidate_at_step`** — para cualquier nodo y cualquier paso, su soporte ahí es no vacío
  y está hecho de nodos. (`owners_ok_of_isValidNode` da la primera mitad; la segunda es
  nueva.) Y `candidate_at_step_filterAll` / `domains_nonempty` lo ponen sobre los grafos de
  la obligación.
- **`chainG_gowners_free`** — una cadena construida desde el soporte de un solo nodo vive
  automáticamente en `gowners`, así que una de las cuatro condiciones extra de `ChainSound`
  ya está pagada.

**Lo que queda:** los dominios del CSP son no vacíos y concretos; falta que exista una
**selección coherente** — encadenada padre→hijo y co-poseída dos a dos. La obligación ya no
mezcla "¿hay candidatos?" con "¿se pueden elegir a la vez?".

**Anotado como próximo paso plausible:** `IsChain` parece alcanzable por la misma vía
(haría falta `ParentsAreNodes` y "los padres están un paso por debajo", en el idioma de (j)).
`PairwiseOwned` no parece alcanzable así — ahí está la propiedad de Helly.

Documentado en `lean_project/verificacion_inseguridad_autor_v26.md`.

**2026-09-09 (j) — `GownersAreNodes` demostrado para toda la máquina, y corrección de (i).**

**Corrección de (i)/v24.** Allí escribí que `filterRequire` rompe este invariante. Falso:
`GownersAreNodes` es **gowners ⊆ nodes**, y `filterRequire` *encoge* `gowners` sin tocar los
nodos, luego lo preserva. Lo que rompe es la **recíproca** (`nodes ⊆ gowners`), que `review`
limpia. Direcciones intercambiadas. Consecuencia buena: el invariante no vive solo en los
puntos fijos, vale en todas partes.

**`Model/GownersNodes.lean`**, en la forma de `Pruned.lean`. Operación por operación:
`filterRequire` (encoge gowners), `updateAt` (no toca gowners, preserva ids), `removeNode`
(quita owner y nodo a la vez), `cleanInvalidGo`/`cleanInvalid`, `reviewNode`/`reviewLine`/
`reviewSteps`/`reviewPass`/`reviewFuel`/`review`, `addNode` (añade owner con su nodo),
`up`/`upFiltering`, `join`, `initSeed`. De ahí `GN_reachable`,
**`GownersAreNodes_reachable`** y **`GownersAreNodes_filterAll`** (esta última es la que
importa: los intermedios filtrados son donde vive la obligación).

**El corolario que hace el trabajo:** `node_at_every_step`. `isValid` dice "hay un owner
global en cada paso"; el invariante lo convierte en **"hay un nodo en cada paso"** — justo lo
que a `degenerate` le faltaba. La clase de contraejemplos degenerados queda eliminada.

**Lo que no cierra:** que haya un nodo por paso no da que se pueda *seleccionar* uno por paso
encadenado y co-poseído. `FilteredChain` sigue abierta. Lo que cambia es que ahora puede
suponer que hay algo que seleccionar, y que el invariante está explícito en vez de escondido
dentro de `Reachable`.

**Nota técnica.** `hasNode_iff` casi entra con `Classical.choice` vía `List.isSome_find?` de
Std; sustituido por inducción propia con `List.find?_cons_of_pos`/`_of_neg` **indicando el
predicado explícitamente** (sin `(p := ...)` el elaborador unifica `p := BEq.beq a.id` y
falla). Cazado por los `#guard_msgs`.

Documentado en `lean_project/verificacion_inseguridad_autor_v25.md`.

**2026-09-09 (i) — `ArcImpliesChain` REFUTADO. Error propio de la entrada (h).**

**El error.** En (h)/v23 celebré que la obligación final ya no contuviera `Reachable`. Quitar
una hipótesis **no debilita** una obligación: la fortalece. Sin `Reachable` el enunciado
tiene que valer para grafos que la máquina no puede construir.

**El contraejemplo, demostrado:**

    degenerate := { nodes := [], gowners := [⟨⟨0,0⟩, none⟩], current_step := 1,
                    map_parent := none }

- `degenerate_valid` : `isValid = true` (hay entrada en todos los pasos) — por cómputo.
- `degenerate_fixpoint` : `review degenerate = degenerate` — no hay nodos que revisar.
- `degenerate_arcConsistent` : las cuatro cláusulas de `ArcConsistent` cuantifican sobre
  nodos, luego son vacías.
- `degenerate_no_chain` : `IsChain` pide un nodo en el paso 0; no hay ninguno.

`not_ArcImpliesChain : ¬ ArcImpliesChain reqOf`, cierre `[propext]`.

**Reparación:** `ArcImpliesChainOn`, con todas las hipótesis del sitio de llamada. Y las dos
direcciones demostradas (`FilteredChain_of_ArcImpliesChainOn`,
`ArcImpliesChainOn_of_FilteredChain`): **son equivalentes**. Es decir, el último escalón de
(h) no era un debilitamiento. Las hipótesis de arco-consistencia y punto fijo siguen siendo
gratis y útiles, pero no achican la obligación.

**Lo que de (h) sobrevive:** `ReqChain → FilteredChain` sí era debilitamiento estricto, y
`arcConsistent_filterAll` / `filterAll_is_review_fixpoint` siguen demostrados. **La escalera
de reducciones toca fondo en `FilteredChain`.**

**Lo que el contraejemplo nombra:** `GownersAreNodes h : ∀ q ∈ h.gowners, (h.node? q).isSome`
— todo owner global es un nodo. Es lo que `degenerate` viola y lo que `Reachable`
suministraba en silencio; cualquier demostración lo necesita explícito.
`GownersAreNodes_initSeed` hecho; `addNode` / `review` / `join` pendientes. Nota:
`filterRequire` **rompe** este invariante temporalmente (quita owners sin quitar nodos) y
`review` lo restaura, así que vale en los puntos fijos, no en los intermedios.

**Lección de método, anotada:** quitar hipótesis parece limpieza y es lo contrario. Un
enunciado que se ve "más elegante" por haber perdido contexto de la máquina es sospechoso.
Lo detectó el propio método: intentar demostrarlo produjo el contraejemplo.

Documentado en `lean_project/verificacion_inseguridad_autor_v24.md`.

**2026-09-09 (h) — `ReqChain` debilitado tres veces: la obligación final es el enunciado clásico de CSP.**

**Se podía pedir menos.** `ChainSound_upFiltering` empuja la cadena de `ReqChain`
inmediatamente por `ChainSound_filterAll` y solo usa el resultado. Así que la obligación se
enuncia un paso más tarde, sobre el grafo **filtrado**: `FilteredChain`. Estrictamente más
débil — `ReqChain_gives_FilteredChain` da una dirección, y la vuelta necesitaría transferir
`ChainSound` hacia atrás a través de una poda, cosa que `Pruned` no suministra (registra
owners y parents, no sons).

**El colapso.** Las seis obligaciones perseguidas (`Supported`, `Extendable`, `PickValid`,
`UpCertifies`, `ReqChain`, `FilteredChain`) son el mismo enunciado sobre grafos distintos:

    ValidHasChain h : isValid h = true → ∃ sel, ChainSound h sel

**La clase más estrecha.** `FilteredChain` lo necesita solo sobre `filterAll g reqs`, y esos
son **puntos fijos de `review`** (`filterAll_is_review_fixpoint`, vía `review_idempotent`).
El punto fijo es donde valen las propiedades de `Fuel.lean` (`review_node_valid`,
`review_owners_within_gowners`, `review_owners_coherent_parents`/`_sons`) y la estructura
`ArcConsistent` de `ArcConsistency.lean`.

**La obligación final:**

    ArcImpliesChain : ∀ h, ArcConsistent reqOf h → isValid h = true → review h = h →
                        ∃ sel, ChainSound h sel

con `Certifies_of_ArcImpliesChain`. Las dos hipótesis nuevas están **demostradas** de la
clase a la que se aplica: `arcConsistent_filterAll` (los filtrados heredan `ReqFiltered` de
`g` por L1 + `filterAll_preserves_ReqFiltered`; el resto lo pone el punto fijo — hizo falta
`arcConsistent_of_ReqFiltered`, variante de `review_arcConsistent` sin la hipótesis
`Reachable`, que allí solo servía para llegar a `ReqFiltered` por L1) y
`filterAll_is_review_fixpoint`.

**Lo que ya no queda dentro:** `addNode`, el bucle de fuel, `join`, la semilla, `MachineOk`,
rangos de nodos, ni `Reachable`. Queda: **consistencia local ⟹ solución global.**

**Precisión sobre v13, que sigue en pie.** `ArcConsistent` tiene cuatro cláusulas: `pinned`
es `ReqFiltered` (L1), que habla de los **requisitos** — donde el 0/1/all de
`MapReqs.Functional` está demostrado. Las otras tres hablan de las **tablas `owners`**, y de
esas v13 demostró con 164 testigos que no heredan la forma 0/1/all. No se afirma que CCJ
aplique; se afirma solo que es el primer enunciado del proyecto donde la estructura de los
requisitos y la propagación de las tablas son hipótesis de la **misma** proposición.

Documentado en `lean_project/verificacion_inseguridad_autor_v23.md`.

**2026-09-09 (g) — `UpCertifies` reducido a `ReqChain`, el primer enunciado que menciona los requisitos.**

**Desmontar el paso.** `upFiltering g reqs d = up (filterAll g reqs) d`, y `up` es `addNode`
cuando el filtro deja válido. `addNode` solo crece; el filtro ya tenía
`ChainSound_filterAll`, con la condición de que la cadena satisfaga los requisitos.

**Cambio de moneda.** v21 enunciaba el invariante en `Inhabited`, pero toda la maquinaria
demostrada está en `ChainSound` (`ChainSound_initSeed`, `ChainSound_join_left`,
`ChainSound_filterAll`, `ChainSound_addNode`, `ChainSound_upFiltering`). Reenunciado como
`CertifiesS`, el ledger se cierra salvo una cosa.

**Condiciones laterales de `ChainSound_upFiltering`, ahora todas demostradas:**

- el paso del nodo nuevo — `Reachable.up` + `(pruned_filterAll _).step_eq`;
- nodos por debajo del paso actual — `nodes_below_of_pruned` sobre `steps_below_current`;
- `MachineOk` — inducción propia sobre `Reachable`: **`MachineOk_reachable`** (nueva; seed vía
  `MachineOk_initSeed`, up vía `MachineOk_upFiltering`, join porque `join` hereda
  `current_step`/`map_parent` de `g₁`).

**Los teoremas:** `CertifiesS_of_ReqChain` y `Certifies_of_ReqChain`.

**La obligación, mínima:**

    ReqChain : ∀ g d, Reachable g → isValid g → (∃ sel, ChainSound g sel) →
      isValid (filterAll g (reqOf d)) → ∃ sel, ChainSound g sel ∧ sel satisface reqOf d

No menciona `addNode`, ni las pasadas de review, ni el nodo nuevo, ni el grafo filtrado.
Solo: **la validez que la máquina comprueba tras filtrar está atestiguada por una cadena
que pasa por los requisitos.**

**Y aquí entra el mapa.** `ReqChain` es el primer enunciado del ledger que menciona los
**requisitos**; todos los anteriores (`PickValid`, `UpCertifies`, `Supported`, `Extendable`)
hablaban solo de owners, cadenas y validez. `GraphMap.MapReqs.Functional` —demostrado el
2026-09-08, que `ImportCnf` solo genera requisitos 0/1/all— llevaba desde entonces sin poder
conectarse con nada. Es la primera vez que las dos mitades del trabajo se tocan en el mismo
enunciado.

**Medición:** `Certifies` no necesita falsador nuevo — es lo que `lake exe validate` y
`lake exe extend --descend` ya comprueban en cada estado, con certificados verificados por
`Certificate.isCert`. 16.444 + 5.466 estados, 1.048.889 nodos, 0 violaciones.

Documentado en `lean_project/verificacion_inseguridad_autor_v22.md`.

**2026-09-09 (f) — Corrección del autor sobre el régimen, y el invariante enunciado en la construcción.**

**Corrección aceptada.** En v20 §6 escribí que "la review tiene que poder invalidar — así
reporta UNSAT la máquina". Eso mezcla dos regímenes. El autor:

> Si la máquina obtiene un conjunto válido tras toda la construcción con revisiones, es
> porque hay al menos un certificado que el Reader podrá leer. UNSAT se filtra **antes** de
> llegar al Reader: la máquina directamente no puede construir un conjunto solución. El
> `filter` durante la lectura está porque al seleccionar un nodo válido se filtran **otros**
> caminos válidos, los que ese nodo no necesita.

Es decir: la invalidación **es** el veredicto en `upFiltering` (construcción), y **sería una
violación del invariante** en la lectura. v20 §6 retirada y marcada; docstring de
`not_isValid_removeNode_of_only` corregida.

**`Model/Certifies.lean` — el invariante donde va.**

    def Certifies : Prop := ∀ g, Reachable reqOf g → isValid g = true → Inhabited g

Inducción sobre `Reachable`, con el ledger:

| caso | estado |
|---|---|
| `seed` | **demostrado** (`Inhabited_initSeed`) — la semilla tiene un nodo y es su propia cadena |
| `join` | **demostrado** (`Inhabited_join`) — `okJoin` ya exige `isValid` de ambas ramas, y join solo crece |
| `up` | `UpCertifies`, la obligación |

Lemas de apoyo, ambos del diseño del propio código:

- `isValid_of_pruned` — la validez solo baja al podar; quitar owners globales nunca hace
  válido lo que no lo era.
- `isValid_of_upFiltering` — **un `upFiltering` válido solo pudo venir de un grafo válido**,
  porque si el filtro invalida, `up` devuelve el grafo invalidado sin añadir nodo. Es lo que
  hace usable la hipótesis de inducción.

**Orden correcto de ataque, revisado:** `UpCertifies` primero (construcción), `PickValid`
después (lectura) — no al revés, como estaba planteado. El punto (3) del autor dice además
que el filtro del Reader **debe** quitar caminos: eso es su función. Lo único que no puede
es quitarlos todos, y eso es consecuencia de (1) aplicado al nodo elegido.

Documentado en `lean_project/verificacion_inseguridad_autor_v21.md`.

**2026-09-09 (e) — `PickValid`, molida hasta una sola eliminación de nodo.**

Ataque a la única obligación que dejó A′. No demostrada; reducida.

**La mitad gratis.** `filterAll g [mid] = review (filterRequire g mid)`, y el pinchazo es
inofensivo: `isValid_filterRequire` — para los pasos ≠ `req.step` el predicado del filtro es
verdadero de entrada, y en el paso de `req` sobrevive el owner elegido. **Toda la dificultad
está en `review`.**

**Obligación estrechada.** El descenso solo elige en pasos donde los owners aún discrepan, y
`filterRequire_eq_self_of_pinned` muestra que un pick en un paso determinado no filtra nada.
Añadida la guarda `choiceAt` a `PickValid` sin debilitar `Inhabited_of_descent`.

**La escalera:**

    Inhabited g
      ⟸ Inhabited_of_pickValid       PickValid + caso base sin elección
      ⟸ isValid_filterRequire        el pinchazo es inofensivo
      ⟸ isValid_review_of_pass       el bucle de fuel → una pasada (sin ningún axioma)
      ⟸ isValid_removeNode_of_other  una pasada → una eliminación

Queda debiendo: **ninguna eliminación de la review es el último owner global de su paso.**

**El límite de la ruta, demostrado a propósito.** `not_isValid_removeNode_of_only`: si el
nodo eliminado era el único owner de su paso, el grafo se invalida. La review **tiene** que
poder invalidar — así reporta UNSAT — así que `PickValid` no puede demostrarse haciendo
imposibles las eliminaciones; tiene que decir que *estas* no dejan un paso a cero.

**La circularidad, anotada.** `isValid_filterAll_of_ChainSound` da `PickValid` en un pick a
partir de una cadena sonora en el grafo pinchado (vía `ChainSound_review`), pero esa
hipótesis es L6 a nivel de mapa. **A′ no reduce L6 a algo más débil: la reempaqueta en un
enunciado de un paso.** Lo que gana el reempaquetado: es combinatoria finita de `review` en
vez de existencia de un objeto global, y las mitades del pinchazo y del bucle de fuel ya
están fuera de la cuenta.

Cierres: `[propext, Quot.sound]`; `isValid_review_of_pass` sin ningún axioma. Fijados por
`#guard_msgs`.

Documentado en `lean_project/verificacion_inseguridad_autor_v20.md`.

**2026-09-09 (d) — Ruta A′: la propagación conduce la inducción, y la terminación es un teorema.**

**`Model/PickInduction.lean`.** La inducción que v18 señaló: elegir un nodo de mapa que
los owners globales aún permitan en un paso donde discrepan, propagar (`filterAll`),
aterrizar en un grafo válido estrictamente menor, repetir hasta que no quede elección.

**La terminación no se supone, se demuestra.** `measure g = g.gowners.length + Σ pesos`, y
`filterRequire` tira exactamente los owners globales del paso que nombran otro nodo de
mapa. De ahí `measure_filterRequire_lt` y `measure_filterAll_lt`, teoremas. (Si `measure`
contase solo nodos, esto no saldría — es el diseño de la medida el que lo da.)

**El teorema.** `Inhabited_of_pickValid` reduce `Inhabited` — la mitad de L6 que consume el
veredicto — a **una obligación y un caso base**:

- `PickValid g` — seleccionar un nodo de mapa permitido y propagar deja el grafo válido.
  Forma de un paso de `Verdict.ReadStable`.
- `NoChoice g → Inhabited g` — un grafo cuyos owners globales coinciden en un nodo de mapa
  por paso denota algo.

La vuelta atrás es gratis (`denot_filterAll_subset`, L2 estrechamiento).

Comparado con A: A pedía dos obligaciones y una era falsa; A′ pide una obligación y un caso
base, ninguno refutado, con la terminación demostrada.

**El probe mide las dos a la vez.** `lake exe extend --descend` ejecuta el descenso real; un
pick que rompe validez es violación de `PickValid`, y todo endpoint sin elección se verifica
con `Certificate.isCert` (ruta C). Familias adversarias: 310 estados, **310 descensos
completados, 0 violaciones, 310/310 endpoints con cadena certificada**. Campaña aleatoria
(150 instancias, 3–10 vars, semilla 4242): **150/150 limpias, 16.444 estados, 16.444
descensos completados, 0 violaciones de `PickValid`, 16.444/16.444 endpoints con cadena
certificada**.

**Lo que falta:** `PickValid` (la última pieza del puente, ahora la **única**), el caso base
(no trivial: varios `PathNodeId` comparten id de mapa, así que quedan padres por elegir), y
que esto es `Inhabited`, no `Supported` — arrancar el descenso filtrando por un nodo pinza
su id de mapa, no su `PathNodeId`.

Documentado en `lean_project/verificacion_inseguridad_autor_v19.md`.

**2026-09-09 (c) — Ruta A: teorema demostrado, hipótesis refutada, y el ingrediente que falta.**

**El teorema — `Model/Extendable.lean`.** `Supported_of_Extend : NodesInRange g → ExtendUp g
→ ExtendDown g → Supported g`, por **inducción sobre el índice de paso**, sin análisis de
casos sobre `Reachable`. Cambia el ∃ global de L6 por un ∀ local (Freuder,
backtrack-free). Cierre `[propext, Quot.sound]`. Lo decisivo: un ∀ local es **decidible
sobre un mapa concreto**, y eso permitió medirlo.

**La refutación — `Model/ExtendSearch.lean`, `lake exe extend`.** Explora *todas* las
cadenas parciales consistentes de cada estado válido, en las dos direcciones, desde cada
nodo. Campaña 3–8 vars, 60 instancias: **14 con cadena atascada, 1.574 cadenas parciales
muertas** (1.517 arriba, 57 abajo), sobre 5.720 estados válidos (4.177 con ramificación) y
188.413 nodos. Testigo en la transición de fase: una cadena parcial **completa de 0 a 12**,
consistente y co-poseída, sin continuación al 13. **`Extendable` es falsa; A tal como se
enunció está cerrada.**

**El hallazgo.** La búsqueda solo comprueba co-posesión **por pares**. El lector
**propaga**: tras cada selección corre `filterAll` y sigue en el grafo filtrado. Con
propagación (`lake exe extend --read`), sobre las mismas instancias, **cero** fallos — ni
de un paso ni de lectura completa, en todos los estados y todas las ramas. Campaña
aleatoria (120 instancias, 3–9 vars): **120/120 con `ReadStable`, 13.894 estados, 604.178
nodos, 0 runs inconcluyentes** — el presupuesto no se agotó en ninguna, así que "sin
fallos" significa explorado entero.

> La co-posesión por pares no basta — que es exactamente por qué v13 (anchura) y v17
> (hipergrafo) se quedaban cortos. Lo que recupera la propiedad es **la propagación
> después de cada decisión**.

Tres medidas independientes convergen: la máquina no funciona por la estructura del mapa,
funciona por cómo filtra.

**Diana sucesora, enunciada no demostrada:** `PickStable` (seleccionar cualquier nodo de
mapa superviviente y propagar deja el grafo válido — la forma de un paso de
`Verdict.ReadStable`) y `Determined` (la propagación ha dejado un nodo de mapa por paso).
No refutadas por el falsador. La inducción iría sobre pasos indeterminados, con caso base
`Determined`, que es un enunciado mucho menor que L6 general.

**Reservas anotadas:** el falsador con propagación es exponencial en el peor caso y corre
con presupuesto — un run que lo agota se reporta **inconcluyente**, no limpio (ninguno lo
agotó). Los mapas sintéticos de `l6search` no violan `Extendable` a los tamaños
alcanzables (244 estados / 99 ramificaciones frente a 5.720 / 4.177), así que **no** se
concluye de ahí que la estructura 3SAT sea la culpable: es diferencia de tamaño.

Estado de las siete rutas: A refutada → A′; B (cadena canónica) cae con A; C y D hechas
(v16); E cerrada (v17); F sin tocar; G pendiente.

Documentado en `lean_project/verificacion_inseguridad_autor_v18.md`.

**2026-09-09 (b) — Corrección del autor sobre el Reader, y ruta E cerrada.**

**Corrección aceptada.** En v16 escribí que un zombi "hace que el lector tenga que
retroceder". Es falso. `Reader/PathReader.lean` toma `ids.toList.head?`, filtra, y si el
filtro invalida el grafo pone `error` y **para** — no prueba otro nodo.
`Reader/PathExpReader.lean` aborta **la enumeración entera** ante una sola rama con
error (el `GRAVE ERROR READER... GPATH INVALID` de Julia, cuyo comentario ya enunciaba el
invariante de diseño: todo nodo superviviente es extensible). Consecuencia correcta: un
zombi es una **parada en seco** que destruye el conjunto de soluciones, y `Supported` es
**precondición de corrección del lector**, no una propiedad de rendimiento.

Lo que no cambia: el veredicto sale de `have_solution` (validez del grafo), no del lector
(`DiffTest.run_case`), así que `Inhabited` sigue siendo lo que consume el veredicto y la
localización de `Verdict.lean` se mantiene. Y `denot_has_no_zombies` sigue en pie: un
zombi no puede *inventar* una solución.

**Hallazgo que sale de la corrección.** Como el lector re-filtra tras cada selección, lo
que necesita es `Supported` **preservado por ese filtro** — enunciado como
`Verdict.ReadStable`. Que es el mismo enunciado abierto del puente. La corrección del
lector y el hueco de L6 son **una sola obligación**.

**Ruta E — `GraphMap/Hypergraph.lean` + `lake exe hyper`.** ¿Aplica BFMY (α-aciclicidad ⇒
la consistencia por pares implica consistencia global) en vez de CCJ? Construido el CSP
explícito (variables = pasos, dominios = nodos del mapa, restricciones = `requires`), los
dos hipergrafos (`scopesByStep`, el honesto para BFMY; `scopesByNode`, cota optimista) y
la reducción GYO como `Bool` decidible. Sin `native_decide`: los casos de prueba se
verifican con `decide`.

*El techo de la ruta:* los CSP α-acíclicos son polinómicos, así que un mapa α-acíclico
pondría 3SAT en P por un teorema de 1983 — E no era un atajo, era la afirmación entera.
Un "no" no refuta nada del algoritmo.

*Medición:* no α-acíclico. `sample.cnf` (núcleo 5/5), literal repetido (8/8), UNSAT
forzado (11/11), transición de fase (32/32). **Sí** α-acíclico: la cadena implicativa
larga, cuyo grafo de restricciones es un camino — señal de que el probe mide lo correcto.
Campañas: 16/200 (3–10 vars), 5/100 (3–4), 7/100 (8–12); el núcleo cíclico es casi
siempre el hipergrafo entero y crece con la instancia (media 10 → 22 → 37 aristas).
Verificado con `decide` dónde está el ciclo: dos cláusulas que comparten dos variables
reducen; tres encadenadas, no. **El ciclo es la estructura de variables compartidas.**

**Conclusión.** E cerrada. Junto con lo que `l6search` ya decía (sin contraejemplos ni con
requisitos arbitrarios sin estructura 3SAT), apunta a que si la propiedad se cumple **se
cumple por cómo poda la máquina, no por cómo está hecho el mapa** — lo que descarta E/F y
señala A (`Extendable`, backtrack-free), que es además lo que el Reader necesita de
verdad.

Documentado en `lean_project/verificacion_inseguridad_autor_v17.md`; v16 §2 corregida in
situ.

**2026-09-09 — Rutas C y D: el checker demostrado, y la separación de las dos mitades de L6.**

De las siete rutas alternativas discutidas para "sin zombis", el autor pidió atacar **C**
(certificado por instancia) y **D** (cambiar el teorema). Ninguna cierra L6.

**Ruta C — `Model/Certificate.lean`.** El `validate` de v15 daba un resultado con estatus
lógico "mi programa buscó y encontró". Ahora el *checker* está demostrado correcto:

- `isCert_sound` — si el `Bool` acepta, existe una selección que cumple `IsChain` y
  `PairwiseOwned` **en el sentido de `Denot.lean`**, no en el del código del checker.
- `Supported_of_checkSupported` — un grafo aceptado satisface `Supported`, que es
  literalmente la L6 abierta.
- `Validate.Supported_of_zombiesOf_nil` — el enlace con el ejecutable.

La búsqueda que *encuentra* los certificados (`searchFrom`, `partial`) sigue **sin
teoremas a propósito**: un fallo en ella solo puede hacer que el checker rechace, nunca
que acepte un grafo con zombis. Separación buscar/verificar, como en los verificadores de
pruebas SAT.

*Detalle que no era cosmético:* `isGoodChain` comprobaba las condiciones en los índices
que la lista tuviera, así que una lista corta pasaba vacíamente en los pasos ausentes.
`isCert` añade `sel.length = current_step`, que es lo que hace cuadrar los índices `Nat`
del checker con los pasos `Int` del modelo. Sin eso el lema de reflexión es falso.

**Ruta D — `Model/Verdict.lean`.** `L6.lean` enunciaba dos propiedades y las trataba como
un lema. No valen lo mismo:

| | lo consume |
|---|---|
| `Inhabited g` | el veredicto SAT/UNSAT |
| `Supported g` | el lector (no retroceder) |

- `denot_has_no_zombies` — un zombi no ensucia la denotación (cierto por definición, y ese
  es el contenido): "sin zombis" sostiene la cota de lectura, no la corrección del
  veredicto.
- `Inhabited_iff_SupportedAt` — **`Inhabited` es L6 en un solo nodo**. `Supported` es el
  mismo `SupportedAt` cuantificado sobre todos. La mitad que sostiene el veredicto hay que
  resolverla una vez, en un nodo *que uno elige*, no contra un adversario que lo elige.
- `Certificate.Inhabited_of_isCert` — y se certifica con **un** certificado, no uno por
  nodo.

**Cierres de axiomas.** `Certificate`: `[propext, Quot.sound]`. `Verdict`: `[propext]`, y
dos teoremas sin ningún axioma. Todos fijados por `#guard_msgs`.

**Resultados.** `validate` reporta ahora las dos mitades por separado. Campaña aleatoria
(semilla 2026, 3–7 vars): 40/40 limpias, 3.808 estados, 116.330 nodos, `Inhabited`
certificado 3.808/3.808, 0 zombis. Las cinco familias adversarias de v15, limpias y con
`Inhabited` certificado al 100%. `diffTest` 200/200. `lake build AbsSat` verde, 55
módulos, 0 `sorry`.

**Lo que sigue abierto:** L6 en general; el puente `GPath ↔ GPathM` (empírico); y el
enlace `denot` → asignación satisfactoria, que vive en el lado del mapa (L7) — `Inhabited`
da *una cadena*, no *una solución*.

Documentado en `lean_project/verificacion_inseguridad_autor_v16.md`.

**2026-09-08 (i) — Comprobación directa de validez: `lake exe validate`.**

**Corrección aceptada:** la lentitud a `n=12` que reporté como anomalía no lo era. Con
`O(S⁴·78)` y `S = 2|U|+|C|+2` (libro p. 76), `n=12,m=15` da `S=41` y `41⁴·78 ≈ 2·10⁸`
operaciones — en el espejo interpretado sobre `List` son minutos. La §3 de v14 queda
retirada.

**El punto ciego de `diffTest`:** compara veredicto y conjunto de soluciones. Un zombi
solo se ve ahí **si además cambia uno de los dos**; puede aparecer a mitad y ser podado
después, y el resultado final sale bien.

**`Model/Validate.lean` + `lake exe validate`** comprueba la propiedad **directamente**,
como invariante interno, en cada estado que la máquina sostiene: *todo nodo que sigue en
el grafo pertenece a alguna cadena co-poseída completa*. Dos decisiones para que no sea
el algoritmo juzgándose:

- la búsqueda de cadena es **backtracking propio, independiente del Reader**;
- toda cadena encontrada se **re-verifica desde las definiciones** (`isGoodChain`).

Modos: `validate <cnf>...` y `validate --random <casos> <semilla> [minVars] [rango]`.
Sale con código 1 y vuelca `validate_failure_<k>.cnf`.

**Resultados.** Campaña aleatoria (mismos regímenes de densidad que `diffTest`):
60/60 limpias, **5.466 estados válidos, 161.839 nodos verificados, 0 zombis**. Familias
adversarias, todas limpias: literal repetido (**viola `hreqs_distinct`**, cae fuera de lo
demostrado), cláusula tautológica, UNSAT forzado, transición de fase `m≈4.26n`, cadena
implicativa larga. Más ~7.000 nodos sobre mapas sueltos.

**Cómo leerlo:** no demuestra nada, pero es evidencia de mejor clase — es **la propiedad
abierta** y no un proxy, es **por nodo** (161.839 oportunidades de fallar, no 60), es
independiente, y es falsable barato. No cubre: rangos mayores (el `S⁴` limita, no el
checker), ni el ejecutable (solo el espejo), ni adversarios diseñados *contra el
invariante*.

**2026-09-08 (h) — El enlace: la ruta de v12 NO cierra (`Model/Link.lean`, v13).**

**Demostrado — el "1" del 0/1/all, en las tablas de la propia máquina.**
`owners_pinned_at_required_step`: en un paso que uno de sus requisitos nombra, los owners
de un nodo proyectan **exactamente** a ese requisito. Es L1 leído a nivel de **mapa** —que
es donde vive la red de restricciones; `owners` son `PathNodeId` y varios comparten id de
mapa—. Con `owners_nonempty_at_step` es un singleton de verdad, no posiblemente vacío.

**Refutado — el "todo".** La otra mitad sería que en un paso que ningún requisito nombra,
los owners proyecten a **todos** los nodos de mapa disponibles. `lake exe l6search` reporta
**164 pares (nodo, paso) en grafos válidos** cuya proyección es un subconjunto propio de
≥2 nodos de mapa. Testigo: proyección `{(2,0),(2,1)}` contra dominio `{(2,0),(2,1),(2,2)}`.

**Mecanismo, y no es un fallo:** la pasada de coherencia interseca contra la **unión** de
los owners de los vecinos (`unionOwnersOf`), y la unión de dos singletons tiene dos
elementos. Las tablas **agregan sobre vecinos**: son arco-consistencia por los enlaces
padre/hijo, no las filas de la red.

**Consecuencia.** Las restricciones crudas del mapa sí son 0/1/all (`MapReqs`, se
mantiene) y los soportes todo-o-uno sí tienen Helly (`ZeroOneAll`, se mantiene). Lo que no
se sostiene es el paso que los conecta: **las tablas de la máquina no son esos soportes.**
El hueco no era `owners ⊆ soporte`: es que 0/1/all es cerrado bajo mayoría → **anchura
estricta 2** → pide **consistencia de caminos**, y la máquina mantiene algo más débil.

**La pregunta abierta ya no es "¿vale CCJ?"** sino **"¿basta esa propagación más débil
para este mapa concreto?"**. Dos vías: (a) reforzar la propagación a consistencia de
caminos —cambia el algoritmo y probablemente su coste—; (b) demostrar que para *este* mapa
la débil basta, usando estructura que CCJ no ve (requisitos hacia atrás, bloque negativo
biyectivo, 7 nodos con 3 requisitos por cláusula). La (b) preserva la apuesta.

**2026-09-08 (g) — Paso (3): el núcleo matemático (`Model/ZeroOneAll.lean`).**

**Corrección a v12, y va a favor del algoritmo.** v12 decía "en una red 0/1/all la
consistencia de **arcos** decide". Es impreciso: las restricciones 0/1/all son cerradas
bajo el discriminador dual, una polimorfía **de mayoría**, y los lenguajes cerrados bajo
mayoría tienen **anchura estricta 2** — lo que garantiza solución global es la
consistencia **por pares** (tabla de pares permitidos), no la de arcos sobre dominios.

Y `owners` **no es un dominio**: es una tabla **por nodo y por paso**, es decir
exactamente una estructura de 2-consistencia. La máquina lleva manteniendo el invariante
fuerte desde el principio. `PairwiseOwned` está bien llamado.

**Demostrado — `helly`:** *una familia de soportes 0/1/all que interseca por pares,
interseca globalmente.* Un soporte es `none` ("todo") o `some a` ("solo a"); el caso "0"
es el que `MapReqs.Functional` descarta de la construcción. Si alguno pinza `a`, el
acuerdo por pares obliga a los demás que pinzan a pinzar `a` también, y los que no pinzan
lo aceptan. Cierre `[propext]`.

**Ahí es donde se disuelve el obstáculo de v11.** Para restricciones arbitrarias, la
compatibilidad por pares no dice nada de la global — ése es el fallo de Helly. Para
soportes todo-o-uno lo dice todo.

- `choose_at_step`: el mismo hecho en la forma que usa la construcción greedy — dados
  elementos ya elegidos cuyos soportes para un paso concuerdan por pares, hay un valor en
  ese paso que los satisface a todos a la vez.
- `sat_supAt_of_mem`: ata con el mapa — `Functional` es exactamente lo que hace que una
  lista de requisitos induzca un soporte 0/1/all de verdad y no uno que reporte en
  silencio solo su primera entrada.

**Lo que sigue faltando:** el ensamblaje greedy sobre el rango de pasos y, lo de verdad,
el enlace con la máquina — `helly` habla de soportes, y los soportes de la máquina son las
tablas `owners`; usarlas exige `owners ⊆ soporte`. Ese enunciado está en
`ArcConsistency.lean` y sigue sin demostrar. Es la mitad abierta desde v11 y ya es **lo
único** entre este fichero y "sin zombis".

**2026-09-08 (f) — Paso (2): el punto fijo de `review` es arco-consistente
(`Model/ArcConsistency.lean`).**

**La consistencia de arcos no es una noción nueva aquí: es `is_valid_node`.** Leyendo la
máquina como CSP —variables = pasos, dominio del paso `k` = los nodos del paso `k`, y los
`owners` de un nodo en el paso `j` = su tabla de soporte para `j`—, la arco-consistencia
son tres cláusulas, y el algoritmo ya impone las tres:

- **soporte** — todo nodo superviviente tiene al menos un owner en cada paso por debajo de
  `current_step`. Es, palabra por palabra, la cláusula de owners de `is_valid_node`
  (`owners_ok_of_isValidNode` la aísla de las de padres/hijos). El punto fijo de `review`
  la da: `review_arcSupported`, sobre `review_node_valid` de F2.c.
- **pinned** — en un paso que algún requisito nombra, el soporte queda estrechado a ese
  requisito. Es el "1" de 0/1/all, y es el **lema L1** (`ReqFiltered`), de la fase F5.
- **coherencia** — el soporte es consistente con el de padres e hijos:
  `review_owners_coherent_parents`/`_sons`, de F2.c.

`review_arcConsistent` ensambla las cuatro. **No hay matemática nueva**: lo nuevo es la
lectura — tres resultados demostrados por motivos sin relación son las tres cláusulas de
una noción estándar.

**Lo que el paso (3) todavía necesita, con precisión.** CCJ es un teorema sobre los
conjuntos de soporte del propio CSP. Aquí lo arco-consistente son las tablas `owners`.
Para aplicar CCJ tienen que **ser** los conjuntos de soporte, y eso son dos inclusiones de
dificultad muy distinta:

- `owners ⊇ soporte` — las tablas nunca tiran un soporte genuino. Es el trabajo de
  preservación de `CleanInvalid.lean`/`Coherence.lean`, ya hecho.
- `owners ⊆ soporte` — las tablas no guardan nada espurio, es decir, la propagación es lo
  bastante fuerte como para haber alcanzado el punto fijo AC de verdad. **No demostrado**,
  y es la misma dirección "podar lo suficiente" que lleva abierta desde v11.

Es decir: paso (2) hecho, paso (3) bloqueado en **exactamente una inclusión** — la misma
que es la mitad abierta desde el principio.

**2026-09-08 (e) — Formalizado: la construcción del mapa solo genera 0/1/all
(`AbsSat/GraphMap/MapReqs.lean`).**

`Functional rs` := **como mucho un requisito por paso**. Es decir: para cualquier nodo y
cualquier paso, los nodos compatibles de ese paso son *todos* (sin requisito) o
*exactamente uno* (con requisito). Eso es 0/1/all. **Y es, literalmente, la hipótesis
`hreqs_distinct` de `Reachable.up`** — así que demostrarlo del mapa es descargar esa
hipótesis desde el lado del mapa, parte de lo que debe la fase L7.

**No hizo falta espejo puro.** `MapDocNode` y `MapColLines` ya son puros; el único `IO`
de la construcción es `register_var!`, que escribe la tabla de nombres de variable y no
toca ningún nodo. Y `add_require!` se llama en **exactamente cinco sitios** en todo el
código —dos en `add_var!`, tres en `add_gate_case!`—, uno a uno con el Julia original:

    GraphMap.lean:81,87        graph_map.jl:86,91
    GraphMap.lean:143,144,145  graph_map.jl:156,157,158

Así que `addVar_negBlock_ok` y `addGateCase_ok` **cubren todos los conjuntos de requisitos
que la construcción puede producir**. Nada más añade requisitos: `link_nodes!` solo toca
padres e hijos (`add_parent_requires`, `add_son_requires`).

**La hipótesis de la cláusula es real, no burocrática.** `addGateCase_ok` pide los tres
pasos de literal distintos dos a dos. Dos literales caen en el mismo paso si y solo si
son la misma variable con la misma polaridad, así que la hipótesis es *no repetir literal
dentro de una cláusula*. `ImportCnf` ni normaliza ni rechaza, y
`repeated_literal_not_functional` exhibe el fallo.

**Cierre de axiomas.** Este módulo es el primero que razona sobre pertenencia en
`Std.HashSet`, y `Std.HashSet.mem_insert` es él mismo `[propext, Classical.choice,
Quot.sound]` en Std. Es dependencia de Std, no axioma de proyecto — y **retro-justifica
la decisión §6.1 del plan** de construir el espejo `GPathM` sobre `List` y no sobre
`HashMap`: esa elección es lo que mantiene los cierres del espejo en `[propext,
Quot.sound]`.

**2026-09-08 (d) — La construcción del mapa da el mecanismo de "sin zombis" (v12).**

Leyendo `GraphMap.lean` / `ImportCnf.lean`: **cada requisito fija exactamente un nodo en
exactamente un paso, y no dice nada sobre los pasos que no menciona.** Sin excepciones —
el bloque negativo tiene un requisito, los nodos de cláusula tres (en pasos distintos),
los de fusión ninguno. Los enlaces padre/hijo cumplen lo mismo (todos los del paso
anterior, o exactamente uno en el bloque negativo).

Es decir: el mapa genera una red de restricciones **0/1/all** (implicacionales), clase
para la que **la consistencia de arcos decide la satisfacibilidad** (Cooper, Cohen y
Jeavons, 1994). Eso es exactamente "sin zombis". La estructura del mapa sí hace falta —
como predecía el doc del puente— pero la propiedad relevante no es "ser 3SAT", es la
forma de los requisitos.

Y `intersectOwners` **es el propagador exacto de esa clase**: "todo" donde la restricción
no habla del paso, "solo esos" donde sí. No es una comodidad de implementación.

Además: la cláusula no se comprueba, se codifica **por ausencia** — el caso `"000"` no
tiene nodo.

**Estrategia concreta para la mitad abierta:** (1) formalizar que `ImportCnf` genera solo
restricciones 0/1/all; (2) que el punto fijo de `review` alcanza AC (F2.c da coherencia
con vecinos; falta ver que eso es AC); (3) aplicar CCJ.

**Dos defectos encontrados en la importación:**
- Literal repetido con la misma polaridad (`x ∨ x ∨ y`) genera **dos requisitos en el
  mismo paso** con índices distintos, lo que **viola `hreqs_distinct`** de `Reachable`.
  La máquina se comporta bien (el grafo se invalida) pero ese nodo cae fuera de todo lo
  demostrado. `ImportCnf` no normaliza ni rechaza. Con `x ∨ ¬x ∨ y` no pasa: pasos
  distintos.
- `cnf_or!` toma los tres primeros literales y descarta el resto en silencio; con menos
  de tres, salta la línea sin avisar.

**2026-09-08 (c) — `join` en moneda `ChainSound`, y una corrección de alcance importante.**

- `Grown` pasa a registrar hijos y owners globales, además de owners y padres. Con eso
  `ChainSound_of_grown` lleva una cadena de cualquiera de las dos ramas al grafo unido, y
  sale `SupportedS_join`.
- **Los cuatro lemas de preservación están completos:** `ChainSound_initSeed`,
  `ChainSound_upFiltering`, `ChainSound_join_left/_right`, `ChainSound_review`. Juntos
  dicen: **una cadena que satisface los requisitos sobrevive a todo lo que hace la
  máquina.**

**Corrección de alcance (importante, y va contra lo que dejé escrito ayer).** L6 dice
*todo nodo superviviente está en alguna cadena*. Los lemas de arriba dicen *una cadena
buena sobrevive*. **No son lo mismo.** Tres de los cuatro constructores cierran la
diferencia solos —la semilla construye la cadena, el `join` la toma de un lado, `addNode`
la extiende, y ninguno quita nada—, pero `filterAll` no:

    SupportedS g → SupportedS (filterAll g reqs)          -- NO demostrado

De `SupportedS g` un nodo superviviente tiene *alguna* cadena, pero no tiene por qué
satisfacer los requisitos, y `ChainSound_filterAll` solo rescata las que sí. Cerrarlo
pide el recíproco de todo lo demostrado hasta ahora: que `review` **elimine** todo nodo
cuyo soporte haya muerto — que no deje zombis. Ése es el significado original del nombre
de L6, y es exactamente la propiedad que `lake exe l6search` no ha conseguido romper.

He corregido los docstrings de `Review.lean` y `Coherence.lean`, que daban a entender que
la preservación cerraba L6. **La mitad "una cadena no se puede cortar" está hecha, y no
necesitó la estructura 3SAT. La mitad "un nodo no puede sobrevivir a sus cadenas" no está
ni empezada.**

**2026-09-08 (b) — `addNode`, y la forma correcta del caso `up` (`Model/AddNode.lean`).**

- **`MachineOk`.** El campo `root_shape` de `ChainSound` dice que solo el nodo del paso 0
  es raíz, y el `parent_id` del nodo nuevo es exactamente `g.map_parent`. Así que
  `addNode` solo puede establecerlo si `map_parent` dice lo que debe: `none` antes de
  visitar nada, `some` después. Eso es `MachineOk`, y lo mantienen todas las operaciones
  — `addNode` lo fija, y el resto son pasos `Pruned`, que ahora lleva `map_parent_eq`.
- **`ChainSound_addNode` demostrado.** Los tres campos extra los establece `addNode`: el
  nodo nuevo se posee a sí mismo (sus owners son `gowners ++ [nuevo]`), los nodos de la
  línea `cs-1` lo ganan como hijo (vía `mem_line_of_node?`), y `root_shape` sale de
  `MachineOk`.
- **Corrección a `L6Up.lean`.** Aquel módulo planteaba el caso `up` como "`SupportedG` se
  preserva", y observaba que el campo `gowners` **no** se preserva bajo `filterRequire`.
  La observación era correcta y el planteamiento equivocado: podar `gowners` **debe**
  matar cadenas — las que no satisfacen el requisito. El enunciado correcto no es que
  sobreviva toda cadena, sino que sobrevivan las que deben:

      ChainSound_filterRequire :
        ChainSound g sel → (sel req.step).id = req → ChainSound (filterRequire g req) sel

  Plegado sobre la lista de requisitos y compuesto con `ChainSound_review` da
  `ChainSound_filterAll`: **una cadena que satisface los requisitos sobrevive al filtro
  entero.** Eso es la dirección ⊇ de L2, y la de L3, en la forma que siempre debieron
  tener. `ChainSound_upFiltering` le pone el nodo nuevo encima.
- **Estado de L6:** tres de las cuatro obligaciones de preservación están ya en moneda
  `ChainSound` — `ChainSound_initSeed`, `ChainSound_upFiltering`, `ChainSound_review`.
  Falta el `join`, que sigue solo en moneda `ChainG` (`Join.Supported_join`); subirlo
  pide extender `Grown` para que registre también hijos y owners globales, el mismo
  trabajo pequeño que `Pruned` ya ha necesitado dos veces.

**2026-09-08 — `review` preserva el soporte total (`Model/Coherence.lean`).**

**Obligaciones 2 y 3 de `Review.lean`, cerradas**, y con ellas el enunciado en el que
estaba bloqueado todo el puente:

    SupportedS_review : SupportedS g → SupportedS (review g)

`reviewPass = reviewSons ∘ reviewParents ∘ cleanInvalid`. `CleanInvalid.lean` hizo la
primera etapa; este módulo hace las otras dos, las compone y corre la inducción sobre el
fuel para llegar a `review`.

**El argumento de coherencia.** `cleanInvalid` poda contra `gowners` y la cadena
sobrevive porque todo nodo suyo es owner global. Las pasadas de coherencia podan contra
`unionOwnersOf g (nb d)` —la unión de los owners de los *vecinos*—, así que hace falta
otro argumento, y es `chain_mem_unionOwnersOf`:

> si **algún** nodo de la cadena `sel w` está entre los vecinos, entonces **todos** los
> nodos de la cadena están en la unión de owners de los vecinos — por co-propiedad
> cuando `i ≠ w`, y por auto-posesión cuando `i = w`.

Así que cada pasada solo necesita **un** nodo de la cadena entre los vecinos, y la cadena
lo aporta: en la pasada descendente el predecesor `sel (k-1)` es padre (el enlace de
`IsChain`), en la ascendente el sucesor `sel (k+1)` es hijo (`son_link` de `ChainSound`).
Aquí es donde los dos campos de enlace de `ChainSound` se ganan el sitio, y donde lo hace
la auto-posesión: sin ella falla el caso `i = w` y **la cadena se podaría a sí misma**.

Los rangos hacen el resto. `reviewParents` recorre `1..cs-1`, exactamente donde existe
predecesor; `reviewSons` recorre `1..cs-2`, exactamente donde existe sucesor. Ninguna
pasada visita nunca un nodo que no pueda justificar.

**Lo que todavía no da.** `SupportedG_upFiltering` de `L6Up.lean` está enunciado sobre
`SupportedG`/`InhabitedG`, cuyos testigos son `ChainG`, no `ChainSound`. Para enchufarle
`SupportedS_review` hay que subir `ChainG_addNode` a `ChainSound_addNode`, es decir
demostrar que `addNode` establece los tres campos extra. Dos son inmediatos (el nodo
nuevo se posee a sí mismo; los padres lo ganan como hijo). El tercero, `root_shape`,
necesita un hecho estructural que el desarrollo aún no lleva: `g.map_parent ≠ none`
cuando `current_step > 0`, porque el `parent_id` del nodo nuevo es exactamente
`g.map_parent`. Todo `up` lo establece, así que vale para grafos alcanzables; solo hay
que enunciarlo y enhebrarlo.

**Nada de esto resultó ser el problema de Helly que temía el doc del puente.**

**2026-09-07 (b) — `cleanInvalid` preserva una cadena sólida (`Model/CleanInvalid.lean`).**

**Obligación 1 de `Review.lean`, cerrada.** `ChainSound_cleanInvalid`: la primera de las
tres etapas de una pasada de revisión no puede cortar una cadena sólida.

El recorrido es un fold cuyo grafo muta debajo, así que el argumento se enhebra paso a
paso con `cleanInvalidGo_cons` (de `Fuel.lean`) y `ChainSound_cleanStep`. Cada paso hace
una de dos cosas, y la cadena está a salvo de ambas:

- **el nodo se queda**, y la intersección de owners no pudo tocar la cadena: todo nodo de
  la cadena es owner global (tercer campo de `ChainG`), y un owner global siempre
  sobrevive a una intersección contra `gowners`;
- **el nodo se tira**, y entonces no podía ser un nodo de la cadena: `isValidNode_of_chain`
  dice que un nodo de cadena sólida siempre pasa la validez, así que esa rama es
  inalcanzable para él. Quitar un nodo que no es de la cadena es inocuo — `removeNode` no
  toca owners, y los filtros de padres, hijos y `gowners` solo descartan el id quitado,
  que la cadena no usa.

**El segundo punto es el que hay que recordar:** el recorrido no puede cortar la cadena
*porque la cadena se protege sola* — la validez es exactamente lo que ella aporta.

Precio mecánico: dos lemas de `node?` (`updateAt_node?`, `removeNode_node?`), porque
`node?` es búsqueda de primera coincidencia y hay que seguir al nodo a través de una
actualización y de la eliminación de *otro* nodo.

**Siguen abiertas las obligaciones 2 y 3:** las dos pasadas de coherencia
(`reviewParents`, `reviewSons`) y la preservación de los campos extra de `ChainSound` a
través de ellas. Podan contra los owners de los vecinos, no contra `gowners`, así que
necesitan el argumento esbozado en `Review.lean`.

**2026-09-07 — `review`: el mecanismo, identificado y formalizado (`Model/Review.lean`).**

**L6 sigue sin demostrar.** Lo que hay es el *porqué* una pasada de revisión no puede
cortar una cadena, con las dos piezas locales demostradas.

Una pasada solo puede dañar una cadena de dos maneras: podando owners
(`intersectOwners`) o tirando nodos que dejan de pasar `isValidNode`. La cadena está
protegida contra ambas, por razones distintas:

- **Contra la poda global.** `cleanInvalid` interseca los owners de cada nodo contra
  `gowners`. Un owner que *es él mismo* owner global siempre sobrevive a esa intersección
  (`mem_intersectOwners_of_mem`). **Ésa es la razón de ser de la condición `gowners` de
  `ChainG`**: no era contabilidad, es lo que impide que el filtro global corte la cadena.
- **Contra ser tirado.** `isValidNode` pide owners que cubran todos los pasos, más padres
  y hijos en los casos no frontera. Una cadena aporta las tres: sus propios nodos están
  dentro de los owners y cubren todos los pasos (`owners_ok_of_chain`), el predecesor es
  padre y el sucesor es hijo. De ahí `isValidNode_of_chain`: **un nodo por el que pasa
  una cadena sólida nunca falla la validez**, así que ninguna pasada puede quitarlo.

Los rangos de las pasadas tampoco son arbitrarios: `reviewParents` recorre `1..cs-1` y
`reviewSons` recorre `1..cs-2`, que es exactamente lo que deja fuera a los nodos frontera
—el que no tiene padre y el que no tiene hijo— de las pasadas que si no los rechazarían.

**`ChainSound`.** `ChainG` no basta porque `isValidNode` mira padres, hijos y el flag de
raíz. `ChainSound` añade las tres que cierran el hueco: cada nodo de la cadena se posee a
sí mismo, el enlace de hijos refleja el de padres, y solo el nodo del paso 0 es raíz. Las
tres las establece `addNode`.

**Lo que sigue faltando** (y es bookkeeping, no el problema de Helly):
1. La inducción sobre el recorrido de `cleanInvalidGo` — el grafo muta mientras se
   recorre, así que "este nodo nunca se tira" hay que enhebrarlo por un fold cuyo estado
   cambia debajo.
2. Para las pasadas de coherencia: `sel i ∈ unionOwnersOf g (padres de sel j)`. El
   argumento está resuelto pero no formalizado: sale de la co-propiedad de `i` y `j-1`
   cuando `i ≠ j-1`, y de la auto-posesión cuando `i = j-1`.
3. Que los campos extra de `ChainSound` sobrevivan a una pasada.

**Gotcha de Lean:** `omega` demostrando una **conjunción** arrastra `Classical.choice`;
partida en dos lemas, no. Sumado a los ya anotados (`beq_self_eq_true`,
`ne_of_beq_false`, `by_cases`, `simp only` sobre defs con `let`).

**2026-09-06 (f) — el caso `up` de L6, reducido a un solo enunciado (`Model/L6Up.lean`).**

`upFiltering g reqs d title` es `up (filterAll g reqs) d title`: un fold de `filterRequire`,
luego `review`, luego `addNode`. Se demuestran el primero y el tercero.

- **`filterRequire`: gratis.** Solo reescribe `gowners`, y `Supported` nunca lo lee —
  `Supported_filterRequire` es `Iff.rfl`.
- **`addNode`: demostrado** (`SupportedG_addNode`), por una construcción explícita de
  extensión de cadena (`ChainG_addNode`): se toma la cadena del grafo base y se
  selecciona el nodo nuevo en el paso nuevo. Por debajo no se movió nada; en el paso
  nuevo el único nodo está forzado.
- **`review`: NO demostrado. Es todo L6.**

**Por qué `SupportedG` y no `Supported`.** `addNode` da al nodo nuevo exactamente
`gowners` como owners. Para que el nodo nuevo *co-posea* una cadena existente, esa cadena
tiene que vivir dentro de `gowners`. `ChainG` lleva esa condición, y `SupportedG` e
`InhabitedG` son las dos formas en que debe viajar: un nodo necesita una cadena que pase
por él, y el nodo nuevo necesita *alguna* cadena a la que engancharse. `InhabitedG` es la
segunda mitad de L6 (`valid ⇒ denot ≠ ∅`), así que **las dos mitades de L6 se alimentan
mutuamente**, no son objetivos independientes.

Esa condición **no** se preserva bajo `filterRequire` por separado —podar `gowners` puede
tirar un nodo de la cadena—, que es exactamente por lo que la inducción hay que correrla
sobre el compuesto `upFiltering` entero y no paso a paso, y por lo que todo aterriza en
`review`.

**El hueco que queda, enunciado una sola vez:**

    SupportedG g → SupportedG (review g)        (con InhabitedG al lado)

Es la misma frase que la dirección ⊇ de L2 y que la dirección ⊇ de L3. **Los tres cabos
abiertos del puente son este único enunciado.**

- **Sonda empírica reforzada:** `lake exe l6search` inspecciona ahora **todos** los
  estados que la máquina sostiene en cada paso, no solo el último: 1.680 estados sobre
  150 mapas sintéticos con requisitos arbitrarios y sin estructura 3SAT. Todos los
  válidos tenían cadena completa co-poseída.
- **Gotcha de Lean encontrado por el camino:** sobre `Int`, `beq_self_eq_true` y
  `ne_of_beq_false` arrastran `Classical.choice` en la toolchain v4.33.1; `beq_iff_eq.mpr
  rfl` y `eq_of_beq` no. `by_cases` también. Todo el fichero está en `[propext,
  Quot.sound]` por evitarlos.

**2026-09-06 (e) — L3, dirección de soundness (`Model/Up.lean`).**

- **Demostrado (L3-⊆):** `denot_upFiltering` y `denot_upFiltering_base` — todo camino que
  denota el grafo extendido es `d` seguido de un camino que denotaba el grafo base.
- **El argumento es estructural, no analítico:** `up` añade **exactamente un** nodo, así
  que la línea superior tiene un solo nodo y toda cadena está obligada a seleccionarlo
  ahí (`chain_top_is_new`); por debajo de ese paso el grafo extendido tiene exactamente
  los nodos de `g`, con los padres intactos y los owners crecidos en el único id nuevo
  (`addNode_node?_below`), así que el resto de la cadena se restringe a una cadena de `g`.
  `pathOf` se construye sobre el rango de pasos **invertido**, que es por lo que el nodo
  nuevo acaba en la **cabeza** del camino.
- La otra mitad de la ⊆ —"satisface `requires d`"— es `Filter.chain_selects_req`, ya
  demostrada. Las dos juntas son el contenido de soundness de L3.
- **Corrección al enunciar `addNode`:** el nodo nuevo **no** pasa por la pasada de sons;
  se añade *después* de ella y solo recibe el owner. El primer intento de
  `addNode_nodes` lo enunciaba mal y no compilaba.
- **No demostrado (L3-⊇):** que una cadena de `g` que satisface los requisitos sobreviva
  al filtro y se extienda. Necesita dos cosas que este módulo no tiene: que filtrar no
  mate la cadena, que es **L6**; y que todo nodo de la cadena sea owner global, para que
  el nodo nuevo (cuyos owners son exactamente `gowners`) lo co-posea.

**2026-09-06 (d) — L4, dirección monótona; y con ella el caso `join` de L6.**

- **`Model/Join.lean`.** Se introduce `Grown`, la contrapartida de crecimiento de
  `Pruned`, enunciada **directamente sobre `node?`** en vez de sobre pertenencia a la
  lista. Eso es lo que permite transferir `IsChain` y `PairwiseOwned` hacia delante
  **sin hipótesis de unicidad de ids** — al contrario que la transferencia hacia atrás
  de `Filter.lean`, que necesita `NodupIds` justo porque podar puede borrar el primer
  nodo con un id y dejar a `node?` apuntando a otro. El crecimiento no puede hacer eso:
  `join_node?_left` demuestra que el nodo fusionado queda en el mismo índice.
- **Demostrado (L4-⊇):** `denot_join_union` — `denot g₁ ∪ denot g₂ ⊆ denot (join g₁ g₂)`.
- **Demostrado de propina (L6, caso `join`):** `Supported_join`. Con el caso semilla ya
  hecho, **dos de los tres constructores de `Reachable` están cerrados para L6**; el
  caso `up` es toda la dificultad restante.
- **No demostrado, y a propósito (L4-⊆):** una cadena co-poseída del grafo unido puede
  mezclar aristas de ambas ramas por nodos compartidos. La recomendación del propio doc
  del puente (§5-L4) es **no** enunciar L4 como igualdad exacta por gpath sino en forma
  relajada (soundness respecto a `ChoicesValid` + completitud de la unión), porque es lo
  único que el puente necesita y evita pelear con mezclas benignas. El contenido de esa
  forma relajada vive del lado de `run_pure` (E2), al que este módulo no llega.

**2026-09-06 (c) — L6: enunciado formal, caso semilla, y un falsador ejecutable.**

- **L6 NO está demostrado.** Lo que hay: `Model/L6.lean` enuncia `Supported` (todo nodo
  que la máquina puede consultar está en alguna cadena co-poseída completa) y
  `Inhabited` (un grafo válido denota algo), y demuestra el **caso semilla**.
- **Dónde se rompe la inducción.** El caso `join` es monótono (`join` solo añade nodos,
  padres y owners, y los nodos de `g₁` conservan su posición, así que `node?` los sigue
  encontrando): necesita la contrapartida "de crecimiento" de `Pruned`, que aún no
  existe. El caso `up` **es toda la dificultad y no se reduce**: en una línea,
  `L6-up ≡ L2-⊇ ≡ "filtrar nunca mata una cadena que pasa por un nodo superviviente"`.
- **Hallazgo empírico que va en contra de lo que este plan esperaba.** `Model/L6Search.lean`
  + `lake exe l6search [steps] [width] [trials]` construye estados con
  `initSeed`/`upFiltering`/`join` sobre mapas sintéticos cuyos requisitos son
  arbitrarios salvo por las hipótesis del propio `Reachable` (hacia atrás y distintos
  por paso), **sin ninguna estructura 3SAT**, y enumera todas las selecciones
  candidatas. Sobre 310 mapas, con estados de hasta **81 selecciones**, no encontró
  ningún estado válido sin cadena.
  Si L6 necesitara la estructura del mapa 3SAT — como este plan y el doc del puente
  predicen— una búsqueda sobre requisitos arbitrarios debería haberlo roto. O bien la
  propia construcción de la máquina (los owners nacen como "todos poseen a todos" y solo
  se podan coherentemente) fuerza la propiedad de Helly por sí sola, o el falsador aún
  no es lo bastante adversario. Conviene saberlo antes de invertir en la demostración.

**2026-09-06 (b) — L2, dirección de soundness, y una corrección al plan del puente.**

- **Corrección:** el doc del puente descompone L2 en "`filter_require` (poda owners del
  paso — directo) + `make_review_owners` (la clausura)". En `GPathM` el primer sumando
  **no aporta nada**: `denot` se define a partir de `nodes` y `current_step`, y
  `filterRequire` solo reescribe `gowners`, así que es denotacionalmente inerte — y lo
  es *definicionalmente*: `denot_filterRequire` es `Iff.rfl`. Todo el contenido de L2
  vive en `review`, que es donde `cleanInvalid` lleva por primera vez los owners
  globales fijados a las listas de owners de cada nodo.
- **Demostrado (`Model/Filter.lean`):** `chain_selects_req` — en un grafo filtrado
  válido, **toda** cadena co-poseída selecciona exactamente `req` en el paso de `req`.
  La ruta es la del libro: el filtro fija `req` en los owners globales
  (`filterRequire_gowners_pinned`), `review` empuja los owners globales dentro de los
  owners de cada nodo (F2.c, `review_owners_within_gowners`), `isValid` garantiza que
  ese paso tiene entrada global (`hasStepEntry_of_isValid`), y la co-propiedad par a par
  traslada eso de los nodos a la selección de la cadena. Cierre `[propext, Quot.sound]`.
- **Dirección de estrechamiento, también cerrada** (misma fecha): `Pruned` pasa a
  registrar el encogimiento de los enlaces a padres además del de ids y owners
  (`nodes_derived` lleva ahora un cuarto conyunto; `pruned_updateAt` gana una hipótesis
  `hpar`). Con eso, `denot_of_pruned` transfiere `IsChain` y `PairwiseOwned` hacia
  atrás, y salen `denot_review_subset` y `denot_filterAll_subset`: **todo camino que
  denota el grafo revisado ya lo denotaba antes**. Estrechar puede perder cadenas,
  nunca inventarlas.
- **La transferencia exige `NodupIds`, y la hipótesis es real, no burocrática:** `node?`
  devuelve el *primer* nodo con un id dado, así que si los ids se repiten, la poda puede
  borrar el primero y dejar a `node?` apuntando a otro nodo cuyos padres y owners no
  guardan relación con los del original. El modelo puro ya asume ids únicos
  (`WellFormedGMap`); esto es la misma hipótesis, hecha explícita a nivel de espejo.
- **Lo que sigue abierto: la dirección ⊇** (ninguna cadena que pasa por `req` se pierde
  al filtrar) es exactamente **L6**. Sigue intacta.

**2026-09-06 — F2.c: la pasada es la identidad en el punto fijo.**

- La familia "filter de longitud igual = identidad" está enhebrada por todas las
  operaciones de la revisión (`Model/Fuel.lean`): `updateAt_eq_self`,
  `intersectOrDrop_eq_self`, `cleanInvalid_eq_self`, `reviewNode_eq_self`,
  `reviewLine_eq_self`, `reviewSteps_eq_self` y, arriba del todo,
  `reviewPass_eq_self`. La pieza que hace desaparecer las ramas de borrado es
  `measure_removeNode_lt`: quitar un nodo que *está* en el grafo baja la medida
  estrictamente, así que en el punto fijo esas ramas son inalcanzables.
- **Resultado (`reviewPass_review`):** `reviewPass (review g) = review g`, más el
  corolario `review_idempotent` (`review (review g) = review g`).
- **La hipótesis `isValid (review g)` no es un artefacto.** Cuando el grafo ya es
  inválido el bucle sale *sin* ejecutar una pasada, mientras que `reviewPass` corre
  `cleanInvalid` incondicionalmente y todavía puede podar. Un grafo inválido es una
  salida del bucle pero no tiene por qué ser punto fijo de la pasada.
- Cierre de axiomas `[propext, Quot.sound]` para las tres (F2.a, F2.b, F2.c), fijado
  con `#guard_msgs` en `Fuel.lean`. 0 `sorry`.
- **Enunciado por nodo del §4, también cerrado** (misma fecha): `review_node_valid`,
  `review_owners_coherent_parents` y `review_owners_coherent_sons`. La derivación pasa
  por reforzar los lemas de punto fijo a "cada paso del recorrido fue *él mismo* la
  identidad, y sobre el grafo original" (`cleanInvalidGo_steps_eq_self`,
  `reviewSteps_lines_eq_self`, `reviewLine_nodes_eq_self`): si cada paso visitado es la
  identidad, ese nodo tomó por fuerza la rama válida, y `updateAt_pointwise` lee del
  `updateAt` fijo que la intersección de owners no tocó nada.
- **Dos precisiones sobre el §4, que el enunciado informal no distinguía:**
  1. Se enuncia sobre `node?`, no sobre `∈ nodes`. `node?` devuelve la *primera*
     coincidencia y nada en el modelo obliga a que los ids de nodo sean únicos, así que
     un duplicado ensombrecido es un nodo que la propia máquina no puede alcanzar
     (todas las búsquedas, aquí y en el ejecutable, pasan por `node?`). Certificarlo
     exigiría una hipótesis de unicidad que el modelo no tiene.
  2. "Owners contenidos en la unión de los de padres e hijos" se formaliza como
     `intersectOwners d.owners (unionOwnersOf g d.parents) = d.owners`, que es la noción
     de contención del propio algoritmo: un owner en un paso donde la unión no tiene
     ninguna entrada se deja intacto; donde sí la tiene, solo sobreviven sus miembros.
     No es contención de conjuntos sin más.
  3. La coherencia con los hijos vale en el rango `1..current_step-2`, no
     `1..current_step-1`: es el rango que recorre la pasada ascendente.

**2026-07-05 — F3, F4 y F5 completadas: L1 y L1-cor demostrados sin axiomas.**

- La primera versión de F5 (DeepSeek, commits `dcb8569`..`5a5e4e7`) llegó a L1 vía
  9 axiomas; la auditoría del 2026-07-04 encontró **dos falsos** (A8 hacía el
  desarrollo inconsistente — se derivó `False` en Lean; A9 tenía `g'` libre sin
  conexión con `g`). Reparación: `IsChain` fija `(sel k).id.step = k` (como
  especificaba F4), el lema de `addNode` se enuncia sobre `filterAll g (reqOf d)` y
  se demuestra, y A1–A7 se sustituyen por pruebas vía la relación `Pruned`
  (`Model/Pruned.lean`, §7.2 del plan). Detalles: `docs/summary_formalization.md`.
- **DoD F5 cumplido:** `#print axioms` de `L1` y `L1_cor` = `[propext, Quot.sound]`,
  fijado con guards `#guard_msgs` que rompen el build si reaparece un axioma.
- L1-cor quedó en la forma autocontenida prevista (el empalme con `ChoicesValid`
  y P3 siguen diferidos a la fase de pegamento L7).

**2026-07-04 — F1, F2 (a+b) y F6 completadas.**

- **F1 ✅** `Model/GPathM.lean`: estructuras y operaciones, con tests embebidos que
  reproducen las cadenas del libro, el join con sufijo compartido y el escenario L1.
  *Desviación:* el `updateNode` esbozado en §2.2 (reemplazo de todas las coincidencias)
  hace **falso** F2.a en presencia de ids duplicados (estados no alcanzables, pero el
  lema cuantifica sobre todos); se sustituyó por `updateAt` — primera coincidencia +
  transformador uniforme que no aumenta el peso — que además elimina la necesidad de
  `LawfulBEq` en toda la fase F2.
- **F2 (parcial) ✅** `Model/Fuel.lean`: F2.a (`measure_reviewPass_le`) y F2.b
  (`review_stable`) demostrados sin `sorry`. **F2.c aplazado** deliberadamente: solo lo
  consume L6, nada de F3–F5 depende de él, y exige la familia "filter de longitud
  igual = identidad" enhebrada por todas las operaciones. Debe aterrizar antes de L6.
  *(Cerrado parcialmente el 2026-09-06 — véase la entrada de esa fecha.)*
- **F6 ✅** `Model/MirrorTest.lean` + `diffTest` a **tres bandas** (oráculo /
  ejecutable IO / espejo puro): 2.000 casos de aceptación con dos semillas
  (261 UNSAT), 0 desacuerdos; más tandas adicionales.
- **Ajuste de alcance para F3/F5:** en lugar de parametrizar `Reachable` por
  `PureGMap` (que usa ids `Nat`), se parametriza por una función abstracta
  `reqOf : NodeId → List NodeId` — es lo único que L1 usa (determinismo de los
  requisitos respecto al id de mapa), y difiere el mapeo `Nat ↔ NodeId` a la fase de
  pegamento con E2 (L7). Por lo mismo, **P3 se difiere** a esa fase y el corolario
  L1-cor se enuncia en forma autocontenida (sin `ChoicesValid`). Los constructores de
  `Reachable` llevan las hipótesis estructurales del mapa real: pasos honestos
  (`d.step = current_step` en `up`, `= 0` en `seed`) y requisitos estrictamente hacia
  atrás (`req.step < current_step`); la fase L7 las descargará desde el driver.
- **Nota técnica para F5:** `deriving BEq` no da `LawfulBEq`; se cambia `NodeId` /
  `PathNodeId` a `deriving DecidableEq` en `Alias.lean` (el `==` pasa por
  `instBEqOfDecidableEq`, que sí es lawful), validado por las tres bandas.

**Estado previo del que parte** (2026-07-04):
- Filtro de Owners del ejecutable corregido y `do_join!` cableado (commit `7092d75`).
- Reader portado + arnés `diffTest`: 5.210 casos aleatorios, 0 desacuerdos (commit `1b70d2e`).
- Modelo puro E2 (`run_pure`) demostrado sin axiomas bajo `WellFormedGMap`.

---

## 0. Principios de diseño (decisiones cerradas antes de escribir código)

1. **Solo `List`, nada de `Finset` ni `Std.HashMap` en el modelo.** El proyecto depende
   únicamente de std4 (no hay Mathlib, luego no hay `Finset`), y el modelo puro
   existente (`PureSatMachine`) ya razona con `List` + pertenencia. Los duplicados en
   listas son inofensivos para razonamiento por `∈`.
2. **Owners como lista plana.** Un `PathNodeId` ya contiene su paso (`id.step`), así que
   no hace falta la tabla `paso → conjunto`: los owners de un nodo son
   `List PathNodeId`, y "owners en el paso k" es `filter (·.id.step == k)`. Elimina una
   capa de estructura anidada y todas las lemas de coherencia tabla/contenido.
3. **La validez es un predicado derivado, no un flag almacenado.** En el ejecutable,
   `valid`/`emptySteps` son estado mutable que hay que mantener coherente (origen del
   bug arreglado el 2026-07-04). En el espejo, `isValid g` se *calcula*: todo paso
   `0 ≤ k < current_step` tiene algún owner global. Cero lemas de coherencia de flags.
4. **El espejo es la especificación, no una transcripción bit a bit.** Debe coincidir
   con el ejecutable en los resultados observables del filtro (qué nodos/owners
   sobreviven, validez), no en la representación interna. La equivalencia se valida
   empíricamente con el arnés (§4), y a medio plazo el ejecutable se puede reconstruir
   como el espejo envuelto en un `IO.Ref` (§6.1 del doc del puente), eliminando el
   teorema de refinamiento.
5. **Todo total, sin `partial` en lo que se demuestra.** La única recursión no
   estructural es la revisión de owners; se modela con *fuel* explícito (§2.3) y un
   lema de suficiencia de fuel. `partial def` queda prohibido en `Model/` (bloquea
   `unfold`/inducción).
6. **Cero axiomas, cero `sorry`, `warningAsError` en verde** — mismo estándar que
   `SatMachine/Model/`.

---

## 1. Estructura de ficheros

```
lean_project/AbsSat/GraphPath/Model/
  GPathM.lean            -- F1: estructuras + operaciones puras
  Fuel.lean              -- F2: revisión con fuel + lema de punto fijo
  Reachable.lean         -- F3: estados alcanzables por la máquina
  Denot.lean             -- F4: IsChain / PairwiseOwned / denot (solo definiciones)
  OwnersInvariants.lean  -- F5: invariante ReqFiltered + preservación + L1
  MirrorTest.lean        -- F6: validación diferencial espejo ↔ ejecutable
```

`AbsSat.lean` importa `OwnersInvariants` (y por transitividad todo lo demás) para que
las pruebas se comprueben en el build por defecto, igual que Soundness/Completeness.

---

## 2. Fase F1 — `GPathM.lean`: estructuras y operaciones

### 2.1 Estructuras

```lean
structure PNodeM where
  id      : PathNodeId
  title   : String                 -- solo para el Reader; irrelevante en pruebas
  parents : List PathNodeId
  sons    : List PathNodeId
  owners  : List PathNodeId        -- plana; paso = owner.id.step
  deriving Repr, BEq

structure GPathM where
  nodes        : List PNodeM       -- todas las líneas, plana; paso = node.id.id.step
  gowners      : List PathNodeId   -- owners globales, plana
  current_step : Nat
  map_parent   : Option NodeId
  deriving Repr
```

Vistas derivadas (definiciones, no campos):

```lean
def GPathM.line (g : GPathM) (k : Nat) : List PNodeM
def GPathM.ownersAt (owners : List PathNodeId) (k : Nat) : List PathNodeId
def GPathM.node? (g : GPathM) (id : PathNodeId) : Option PNodeM
def GPathM.isValid (g : GPathM) : Bool     -- ∀ k < current_step, ownersAt ≠ []
```

### 2.2 Operaciones (espejo de las del ejecutable ya corregido)

| Espejo | Ejecutable (GraphPath.lean) | Notas |
|---|---|---|
| `initSeed node title` | `GPath.new` + primer `do_up!` | |
| `filterRequire g req` | `filter_require!` | poda `gowners` en `req.step` |
| `cleanInvalid g` | `clean_invalid_nodes!` | un solo barrido (fold sobre `nodes`): intersecar owners de nodo con `gowners`, eliminar nodos no válidos (reglas 1–4 de `is_valid_node`), limpiar enlaces |
| `reviewParents g` / `reviewSons g` | `review_owners_parents_sons!` / `review_owners_sons_parents!` | un barrido ascendente / descendente |
| `reviewStep g` | una pasada de `make_review_owners!` | `cleanInvalid` + coherencia; devuelve `(g', changed : Bool)` |
| `upFiltering g reqs d title` | `do_up_filtering!` | usa `review` con fuel (F2) |
| `join g₁ g₂` | `do_join!` | unión de nodos (fusionando los de mismo id), unión de `gowners` |

Detalle importante para las pruebas: **las operaciones de poda solo eliminan elementos
de listas** (nodos, owners, enlaces) — nunca añaden. Formular cada op de poda como un
`filter`/`filterMap` hace que la monotonía (§5, P2) salga por lemas genéricos de
`List.filter` en lugar de análisis por casos.

**Hecho (DoD F1):** compila; `#eval`-tests reproducen a mano el ejemplo del libro
(Fig. 1.15: filtrar `X=1, Y=0, Z=0` sobre el PathSet de 3 variables) y el fixture
`test_sat_medium.cnf` a nivel de una sola cadena de UPs.

## 3. Fase F2 — `Fuel.lean`: la revisión termina

```lean
def measure (g : GPathM) : Nat :=
  g.nodes.length + (g.nodes.map (·.owners.length)).sum + g.gowners.length

def review (g : GPathM) : GPathM := reviewFuel (measure g + 1) g

def reviewFuel : Nat → GPathM → GPathM
  | 0, g => g
  | fuel+1, g =>
      let (g', changed) := reviewStep g
      if changed then reviewFuel fuel g' else g'
```

Lemas:
- **F2.a (decrecimiento):** `changed = true → measure g' < measure g`
  (consecuencia directa de "las pasadas solo podan": cada `reviewStep` con cambio
  elimina al menos un elemento).
- **F2.b (suficiencia):** con fuel `measure g + 1` se alcanza el punto fijo:
  `reviewStep (review g) = (review g, false)`.
- **F2.c (caracterización del punto fijo):** tras `review`, todo nodo superviviente
  pasa `is_valid_node` y sus owners están contenidos en la unión de los de sus padres
  y en la de sus hijos (la postcondición que L6 explotará más adelante).

**Hecho (DoD F2):** F2.a–F2.c demostrados sin `sorry` ni axiomas de proyecto;
`review` es `def` total. F2.c en sus dos formas: punto fijo
(`reviewPass (review g) = review g`) y caracterización por nodo
(`review_node_valid`, `review_owners_coherent_parents/_sons`), ambas bajo
`isValid (review g)` y enunciadas sobre `node?`.

## 4. Fase F6 (en paralelo desde F1) — `MirrorTest.lean`: el espejo no miente

Antes de demostrar nada sobre el espejo, comprobar que computa lo mismo que el
ejecutable. Reutilizar la infraestructura de `DiffTest`:

- Una función `runMirrorMachine : PureGMap → …` que ejecuta el bucle de la máquina
  (init/up_filtering/join por timeline) **sobre `GPathM`**, y un lector exponencial puro
  (~30 líneas: es `filterRequire` + `review` con requisito unitario).
- Extender `diffTest` a comparación a tres bandas: `ExhaustiveSolver` vs máquina IO vs
  máquina espejo, comparando veredicto y conjuntos de soluciones.
- Tanda de aceptación: ≥ 2.000 casos, 0 desacuerdos, mismas semillas registradas.

Esto convierte "el espejo refleja el ejecutable" de esperanza en evidencia, sin pagar
un teorema de refinamiento IO ↔ puro que no aporta nada al puente.

**Hecho (DoD F6):** tres bandas en verde con ≥ 2.000 casos y dos semillas.

## 5. Fase F3 — `Reachable.lean`: estados alcanzables

L1 no es cierto para un `GPathM` arbitrario — solo para los que la máquina construye.
Se formaliza con un inductivo parametrizado por el mapa (que aporta `requiresOf`):

```lean
def requiresOf (gmap : PureGMap) (id : NodeId) : List NodeId  -- de PureNode.requirements

inductive Reachable (gmap : PureGMap) : GPathM → Prop where
  | seed  : ∀ n ∈ capa 0, Reachable gmap (initSeed n …)
  | up    : Reachable gmap g → d ∈ capa (g.current_step) →
            Reachable gmap (upFiltering g (requiresOf gmap d.id) d.id …)
  | join  : Reachable gmap g₁ → Reachable gmap g₂ → okJoin g₁ g₂ →
            Reachable gmap (join g₁ g₂)
```

donde `okJoin` captura las precondiciones de `is_valid_join` (mismo `current_step`,
mismo `map_parent`). Lemas básicos de sanidad estructural, todos por inducción sobre
`Reachable`:

- **P1 (pasos honestos):** todo nodo/owner de `g` tiene paso `< g.current_step`.
- **P2 (monotonía de poda):** si `g ⟶ g'` por cualquier op que no sea `up`/`join`,
  entonces nodos, owners y enlaces de `g'` ⊆ los de `g`.
- **P3 (procedencia):** todo `PathNodeId` presente proyecta a un nodo del mapa de su
  capa (el análogo de `path_confined_to` del modelo E2, que el puente reutilizará).

**Hecho (DoD F3):** `Reachable` + P1–P3 sin `sorry`.

## 6. Fase F4 — `Denot.lean`: la denotación (solo definiciones)

Las definiciones del §3 del doc del puente, para poder *enunciar* el corolario de L1
(demostrarlas en general es L2–L7, fuera de alcance aquí):

```lean
def IsChain (g : GPathM) (sel : Nat → PathNodeId) : Prop := …
def PairwiseOwned (g : GPathM) (sel : Nat → PathNodeId) : Prop :=
  ∀ i j, i < g.current_step → j < g.current_step → i ≠ j →
    sel i ∈ GPathM.ownersAt (nodeOwners g (sel j)) i
def pathOf (sel : Nat → PathNodeId) (S : Nat) : PurePath := …  -- orden de fold_choices
```

**Hecho (DoD F4):** definiciones compilan y un `#eval`-test con `Decidable` ad hoc las
ejercita sobre el ejemplo del libro.

## 7. Fase F5 — `OwnersInvariants.lean`: el Lema L1

### 7.1 El invariante inductivo

> **ReqFiltered:** para todo nodo `d` del grafo y todo `req ∈ requiresOf gmap d.id.id`,
> los owners de `d` en el paso `req.step` solo apuntan al nodo requerido:
>
> ```lean
> def ReqFiltered (gmap : PureGMap) (g : GPathM) : Prop :=
>   ∀ d ∈ g.nodes, ∀ req ∈ requiresOf gmap d.id.id,
>     ∀ q ∈ d.owners, q.id.step = req.step → q.id = req
> ```

### 7.2 Cadena de preservación (el orden de ataque)

| Lema | Enunciado | Por qué sale |
|---|---|---|
| L1.a | `ReqFiltered` tras `initSeed` | vacuo (sin requisitos en capa 0) o directo |
| L1.b | poda preserva `ReqFiltered` | por P2: los owners de `g'` ⊆ owners de `g`; una propiedad ∀-sobre-owners sobrevive a cualquier `filter` |
| L1.c | `upFiltering` establece `ReqFiltered` para el nodo nuevo | el nodo nuevo hereda `gowners` *después* de `filterRequire` por cada `req`: en `req.step` solo queda el requerido; para los nodos viejos, L1.b |
| L1.d | `join` preserva `ReqFiltered` | **el corazón de L1**: `join` fusiona owners solo entre nodos con el *mismo* `PathNodeId`; por `Reachable`, ambos operandos contienen ese id solo si ambos pasaron `upFiltering` con los *mismos* `requiresOf` (mismo id de mapa ⟹ mismos requisitos, usando `WellFormedGMap.unique_ids`); la unión de dos listas que cumplen la propiedad la cumple |
| **L1** | `Reachable gmap g → ReqFiltered gmap g` | inducción sobre `Reachable` con L1.a–L1.d |

Nota técnica sobre L1.d: necesita el lema auxiliar *"mismo `PathNodeId` alcanzable ⟹
mismo historial de filtrado de requisitos"*. No hace falta rastrear historiales: basta
que `requiresOf` sea función del id de mapa (determinista) y que ambos operandos
cumplan ya `ReqFiltered` — la preservación es puramente algebraica
(`∈ unión ⟹ ∈ alguno`). El párrafo del historial es motivación, no parte de la prueba.

### 7.3 El corolario a nivel de cadena (la conexión con el puente)

> **L1-cor:** si `Reachable gmap g`, `IsChain g sel`, `PairwiseOwned g sel`, entonces
> para todo `j < g.current_step` y todo `req ∈ requiresOf gmap (sel j).id`:
> `(sel req.step).id = req` — y por tanto `pathOf sel` satisface
> `satisfies_requirements` en cada prefijo (enunciado exactamente en los términos de
> `ChoicesValid` del modelo E2).

Demostración: `PairwiseOwned` da `sel req.step ∈ owners (sel j)` en ese paso; `ReqFiltered`
(por L1) fuerza `(sel req.step).id = req`. El empalme con `ChoicesValid` es un
desplegado de definiciones más P3.

**Este corolario es la mitad "soundness" del puente en miniatura**: deja demostrado que
ninguna cadena co-poseída puede violar un requisito. Lo que L2–L7 añadirán después es
que las cadenas co-poseídas son exactamente lo que la máquina representa y el Reader
enumera.

**Hecho (DoD F5):** L1 y L1-cor sin `sorry` ni axiomas; `#print axioms` limpio.

---

## 8. Orden de trabajo, tamaños y riesgos

Orden: **F1 → F6(smoke) → F2 → F3 → F4 → F5 → F6(aceptación)**.
F6 arranca en cuanto F1 compila: si el espejo divergiera del ejecutable, mejor saberlo
antes de demostrar nada sobre él.

| Fase | Tamaño | Riesgo principal | Mitigación |
|---|---|---|---|
| F1 | M | desviarse semánticamente del ejecutable al "simplificar" | F6 smoke temprano; revisar contra `GraphPath.lean` corregido, no contra Julia |
| F2 | M | formular `reviewStep` de modo que el decrecimiento no sea evidente | diseñar cada pasada como `filter` explícito (P2 gratis) |
| F3 | S | precondiciones de `okJoin` incompletas | copiarlas de `is_valid_join` y del uso real en `ColTimelineStep.impact!` |
| F4 | S | — | — |
| F5 | M/L | L1.d: tentación de rastrear historiales | quedarse en el argumento algebraico de §7.2 |
| F6 | S/M | duplicar el bucle de máquina (IO y puro) y que diverjan | factorizar el driver de timeline sobre una interfaz común si se puede sin fricción; si no, aceptar la duplicación con el diff de 3 bandas como red |

Dependencias externas: ninguna nueva (solo std4). Convención de calidad: la de
`SatMachine/Model/` (docstrings con la intención, teoremas nombrados por contenido,
nada de `native_decide`).

## 9. Qué NO está en alcance (para no deslizarse)

- L2–L8 del puente (filtro↔denotación, join↔unión, L6/Helly, Reader). F4 solo *define*.
- Teorema de refinamiento IO ↔ espejo (sustituido por F6 + plan §6.1 del puente).
- E1 (CNF ↔ GMap) — independiente; puede avanzar en paralelo si hay energía.
- Cualquier afirmación de complejidad.

---
*Plan escrito por Claude (Fable 5) el 2026-07-04, como continuación de
`formal_bridge_owners_runpure.md` tras cerrar el arnés diferencial (5.210 casos, 0
desacuerdos).*
