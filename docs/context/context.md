# Documento Maestro de Contexto

> Qué es esto: el contexto del algoritmo tal y como está **en el repo**, no como se
> recuerda. Cada afirmación apunta a un fichero. La separación que vertebra todo el
> documento es una sola: **probado** / **hipótesis declarada con nombre** / **abierto**.
> Última revisión contra el código: 2026-09-21, rama `spaik-window3`, `lake build AbsSat`
> verde (231 jobs), `lake exe runTests` verde.

---

## 0. Descripción general del algoritmo

### 0.1 Qué hace

Dada una fórmula 3-SAT `φ`, el algoritmo **no busca una asignación**: construye un
objeto —un grafo de caminos con tablas de *owners*— que representa de golpe el conjunto
de todas las asignaciones parciales todavía vivas, lo va podando, y al final **lee** una
solución de él si queda alguna.

Son cuatro piezas, y el documento las recorre en ese orden:

| pieza | qué es | dónde |
|---|---|---|
| **Mapa** | la fórmula convertida en un DAG por niveles, pura aritmética | `lean_project/AbsSat/GraphMap/CnfMap.lean` |
| **Machine** | el driver: una línea de estados por paso, que avanza, filtra y une | `lean_project/AbsSat/GraphPath/Model/PureDriverImproves.lean` |
| **GPath** | la estructura de datos que cada estado es, y sus filtros | `lean_project/AbsSat/GraphPath/Model/GPathM.lean` |
| **Reader** | el que extrae una asignación concreta del estado final | `lean_project/AbsSat/GraphPath/Model/ReaderExec.lean` |

### 0.2 El bucle, en una frase

El mapa tiene `stepCount φ = 2n + m + 2` pasos. La máquina mantiene una **línea**:
una lista de pares `(nodo de mapa visitado, GPath)`. En cada paso envía cada estado a
cada hijo de su nodo de mapa; cada envío filtra el grafo por los requisitos del destino,
lo revisa hasta punto fijo, y añade una fila nueva encima (`up`). Los estados que llegan
al mismo nodo de mapa se **fusionan** (`doJoin`). Un estado que se queda sin owners
globales en algún paso es inválido y se descarta.

### 0.3 La idea que lo sostiene: *owners*

Cada nodo del grafo lleva una tabla `owners : List PathNodeId`: los nodos que **pueden
estar en un mismo camino que él**. Esa tabla es a la vez el certificado y el mecanismo
de poda:

* **validez** = todo paso por debajo de `current_step` conserva algún owner global
  (`isValid`, derivada, no almacenada);
* **poda** = la revisión elimina owners incoherentes y nodos que se quedan sin owners en
  algún paso;
* **lectura** = fijar un nodo ("pin") y revisar; si el estado sigue válido, ese valor está
  en alguna solución.

### 0.4 Lo que está demostrado de punta a punta

Dos resultados, **sin hipótesis ninguna**, en `lean_project/AbsSat/GraphPath/Model/Answer.lean`:

* `answer_unsat_sound` — si la máquina responde UNSAT, `φ` no tiene modelo.
* `answer_sat_sound` — si responde `SAT a`, entonces `a` satisface `φ` (se devuelve
  certificado y se comprueba con `satB`).
* `answer_ne_unsat_of_sat` — sobre una fórmula satisfacible nunca responde UNSAT.

Es decir: **ninguna respuesta que dé la máquina puede ser incorrecta.** Lo único que
podría fallar es que responda `unknown` sobre una fórmula satisfacible, o sea que el
lector se atasque. Esa es la frontera real del trabajo (§5).

### 0.5 Higiene de axiomas

No hay ni una declaración `axiom` ni un `sorry` en las pruebas. Hay **524 bloques
`#guard_msgs`** que fijan el cierre de axiomas de los teoremas cabecera y **rompen el
build** si alguno empieza a depender de algo nuevo. El cierre normal es
`[propext, Quot.sound]`; `Classical.choice` se evita a propósito (ver §3.3).

### 0.6 La estrategia de espejo

Lo que corre (`IO.Ref`, `Std.HashMap`) y lo que se demuestra son objetos distintos, unidos
por bandas diferenciales:

```
GMap  (IO, HashMap)      ←→  CnfMap    (aritmética pura)
GPath (IO.Ref)           ←→  GPathM    (listas puras)
driver IO                ←→  PureDriverImproves
```

`lake exe diffTest` compara **tres bandas** —oráculo por fuerza bruta / ejecutable IO /
espejo puro— en veredicto *y* conjunto completo de soluciones. `lake exe runTests` incluye
la cross-validation contra `ExhaustiveSolver`.

---

## 1. Mapa

### 1.1 Descripción funcional

Convierte `φ` en un DAG por niveles donde **un camino de arriba abajo = una asignación**.
El mapa no se representa como dato en el lado de las pruebas: es aritmética sobre
`(step, index)`.

Para `n` variables y `m` cláusulas:

| paso | nodos | requisitos |
|---|---|---|
| `2v` | `⟨2v,0⟩` (`v=0`), `⟨2v,1⟩` (`v=1`) | ninguno |
| `2v+1` | `⟨2v+1,i⟩` (`!v=i`) | `⟨2v, 1-i⟩` |
| `2n` | un `FusionNode` | — |
| `2n+1+j` | siete `⟨·,r⟩` con `r ∈ 1..7`, `r = 4b₁+2b₂+b₃` | `⟨lₚ.step, bₚ⟩` por literal |
| `2n+1+m` | un `FusionNode` | — |

`stepCount φ = 2n + m + 2`, `litBlock φ = 2n`, `clauseStep φ j = 2n+1+j`,
`fusionTop φ = 2n+1+m`.

### 1.2 Subcomponentes clave

* `CnfMap.lean` — la aritmética: `varStep`, `negStep`, `mapNodes`, `mapSons`, `reqOfCnf`.
* `CnfSel.lean` — la dirección inversa: `selOfAssign` (qué nodo elige una asignación en
  cada paso), `rowOf` (la fila de 3 bits de una cláusula), `bit`.
* `CnfMapImproves.lean` — `weakReqOfCnf`: información **de pares** que el mapa regala.
* `CnfReducer.lean` — `rowPairs`, `pairsAgree`, `allRows`.
* `ImportCnf.lean` — DIMACS → `GMap` (lado `IO`, solo para correr).

### 1.3 Claves del diseño

**(a) La fila `000` es la que no existe.** Los siete nodos de una cláusula son
`r ∈ 1..7`: falta exactamente la fila "los tres literales falsos". *Ahí y solo ahí entra
la satisfacibilidad* — `CnfSel.rowOf_pos`: una cláusula satisfecha nombra una fila ≠ 000.
Todo lo demás del mapa es contabilidad.

**(b) Asimetría deliberada en `reqOfCnf`.** Es **total y uniforme** sobre un paso de
cláusula: no comprueba que el índice esté en `1..7`. El índice `0` devuelve la fila
todo-falso. Mantener esa comprobación fuera de `reqOfCnf` es lo que deja a `Functional` y
`Backward` sin hipótesis de rango; la omisión vive entera en `mapNodes`.

**(c) Requisitos débiles = arc-consistencia gratis.** Dos nodos de cláusula que hablan de
la misma variable llevan más información que sus requisitos duros: o coinciden en todas
las variables compartidas o no pueden estar los dos en una solución. `weakReqOfCnf φ d`
lista eso. Tres detalles que importan:
* un paso **sin variable compartida está ausente**, no es "todos los nodos";
* un conjunto débil es un *conjunto*, puede ser vacío → el nodo muere en el acto;
* es **sano pero no completo**: pares sí, tríos no. Por eso la revisión sigue haciendo falta.

### 1.4 Teoremas principales probados

* `CnfSel.reqSat_selOfAssign` — la selección de *cualquier* asignación satisface todos
  los requisitos de los nodos que elige. No necesita satisfacibilidad.
* `CnfSel.selOfAssign_onMap` — la selección de una asignación satisfactoria está sobre el
  mapa. Aquí entra `Sat`, vía `rowOf_pos`.
* `CnfMapImproves.weakReqOfCnf_sound` — la selección de una solución cae siempre dentro de
  todo conjunto débil de los nodos que elige ⇒ filtrar por él **nunca pierde una solución**.
* `CnfMap.reqOfCnf_functional`, `reqOfCnf_backward`, `reqOfCnf_shape` — los requisitos son
  funcionales (uno por paso), miran siempre hacia abajo, y tienen la forma que la clase
  0/1/todos pide. (`MapReqs.Functional` / `Backward` son las propiedades genéricas.)

### 1.5 Teoremas pendientes

Ninguno bloqueante. El lado del mapa es la parte cerrada del proyecto. Lo que queda es
medición, no demostración: la **anchura inducida** del mapa por familia de fórmulas
(`lake exe width`, `HyperProbe.lean`, `CnfHypergraph.lean`), que es lo que acota el coste.

### 1.6 Invariantes

* `NodesOnMap φ g` — todo nodo del grafo proyecta a un nodo que el mapa construye.
* `ReqFiltered (reqOfCnf φ) g` — los requisitos duros ya están aplicados.
* `ReqBack φ g` — la información hacia atrás del mapa se respeta.
* `MapReachable` — el estado se alcanzó por la secuencia legal de `up`/`join` del mapa.

---

## 2. Machine

### 2.1 Descripción funcional

El driver. Mantiene `PureLine = List (NodeId × GPathM)`: una línea de estados indexada por
el nodo de mapa que cada uno acaba de visitar.

```
pureRunW φ            -- correr hasta el final
  = pureStepsW φ (stepCount φ - 1) (pureInit φ)
pureAdvanceW φ line   -- un paso: cada estado a cada hijo, filtrar, insertar
sendToW  φ g next d   -- un envío concreto
insertPure line k g   -- los que caen en el mismo nodo de mapa se FUSIONAN (doJoin)
```

El envío es una sola expresión, y es donde está todo:

```lean
upFilteringWeak g ws reqs d = up (filterAllAgg (filterWeakAll g ws) reqs) d
```

1. `filterWeakAll` — recorta los owners globales por los requisitos **débiles** del destino;
2. `filterAllAgg` — aplica los requisitos **duros** y corre la **revisión agresiva** a punto fijo;
3. `up` — añade la fila nueva si el estado quedó válido; si no, el estado se descarta.

### 2.2 Subcomponentes clave

* `PureDriver.lean` — el driver base (solo requisitos duros, revisión base).
* `PureDriverImproves.lean` — el driver real: débiles + revisión agresiva.
* `ConservationImproves.lean` — la ley de conservación.
* `Answer.lean` — el veredicto de tres valores y `readGreedy`.
* `BranchLines.lean`, `PinHistory.lean` — las *ramas*: la línea restringida a los estados
  cuya clave concuerda con una lista de pines. Es el andamio de casi todas las rutas de §5.
* Ejecutable: `AbsSat/SatMachine/PureSatMachineImproves.lean`, `SatMachine.lean`, `DiffTest.lean`.

### 2.3 Claves del diseño

**(a) La fusión por clave es lo que evita la explosión.** Dos historias distintas que
llegan al mismo nodo de mapa no se guardan por separado: se unen con `doJoin`. La línea
tiene como mucho tantos estados como nodos tiene el paso del mapa.

**(b) Filtrar antes de crecer.** El orden `débiles → duros → revisión → up` es esencial:
un conjunto débil vacío deja un paso sin owner global, `isValid` falla, y el estado muere
**antes** de pagar la fila nueva.

**(c) La revisión va dentro del filtro, no después.** `filterAllAgg` = revisión base hasta
punto fijo, luego una pasada agresiva, y otra vez mientras la pasada quite algo.

**(d) Los títulos no se copian.** El driver real copia el título del nodo de mapa; el
modelo pasa `""`. Nada en `isValid`, `owners` o `denot` lo lee, así que la banda
diferencial compara claves, número de nodos y validez — no títulos.

### 2.4 Teoremas principales probados

* **`ConservationImproves.pureRunW_ne_nil`** — *la ley de conservación*: sobre una fórmula
  bien formada y satisfacible, la corrida termina con la línea **no vacía**. O sea: el
  filtro débil, los requisitos duros y la revisión agresiva **nunca pierden una solución**.
  Es la mitad UNSAT del veredicto, y está cerrada.
* `pureRunW_full_state` — además da el estado válido e inhabitado aparcado en el nodo final
  de la asignación.
* `ChainSound_filterWeak`, `AggressiveReview.ChainSound_reviewAgg` — los dos ingredientes:
  ninguna de las dos podas separa dos nodos de una misma cadena sana.
* `Answer.answer_unsat_sound` / `answer_sat_sound` / `answer_ne_unsat_of_sat` — sin hipótesis.

### 2.5 Teoremas pendientes

* **`answer_unsat_of_unsat`** está probado **bajo `RoundInvariant.GhostsLine φ`**: tras la
  revisión base de todo estado pinchado de la línea, *todo fantasma es detectable*. Es la
  completitud del veredicto UNSAT.
* El resto de lo pendiente no es del driver sino del salto "estado válido ⇒ satisfacible" (§5).

### 2.6 Invariantes

`ReaderAggRun.MInv φ g` es el paquete que el driver arrastra:

| campo | dice |
|---|---|
| `rctx` | todos los invariantes del lector (§3.6) |
| `mok` | `MachineOk`: `0 ≤ current_step`, y `map_parent` es `none` sii el paso es 0 |
| `tl` | `ParentId.TL`: **todo nodo de la línea superior lleva el `map_parent` del estado** |
| `rf` / `back` / `onMap` | los tres invariantes de mapa (§1.6) |
| `smp` / `pms` / `sn` | coherencia de hijos y padres |
| `own` | los owners de un nodo son nodos |

Y por estado de línea, `ConservationFilter.StateOkF φ k kv`: `kv.1` está en el mapa al paso
`k`, `kv.2.current_step = k+1`, `kv.2.map_parent = some kv.1`, y `isValid kv.2`.

---

## 3. GPath

### 3.1 Descripción funcional

La estructura de cada estado.

```lean
structure PNodeM where
  id : PathNodeId; title : String
  parents : List PathNodeId; sons : List PathNodeId; owners : List PathNodeId

structure GPathM where
  nodes : List PNodeM; gowners : List PathNodeId
  current_step : Int;  map_parent : Option NodeId
```

`isValid g` = todo paso en `0..current_step-1` conserva algún owner global. **Derivada, no
almacenada** — esa desincronización fue exactamente el bug de 2026-07-04.

### 3.2 Subcomponentes clave

* `GPathM.lean` — estructura, `up`/`addNode`, `review`, prunings.
* `AggressiveReview.lean` — la pasada del autor, `reviewAgg`, `ReviewOk`.
* `Join.lean`, `ReviewJoin.lean` — la unión y su interacción con la revisión.
* `Pruned.lean` — la relación "es un estrechamiento de".
* `ParentId.lean` — `PMP`, `GPMP`, `TL`, `chain_eq_of_mapIds_eq`.
* `Descent.lean`, `NoDeadEnd.lean` — el descenso (§5).
* `ImprovesCima.lean` (3.4k líneas) — la regla del top y las familias.

### 3.3 Claves del diseño

**(a) La ventana del identificador, a 3.** Un `PathNodeId` es
`(id, parent_id, gparent_id)`: el nodo de mapa, el de su padre y el de su abuelo. La
operación que lo mueve es

```lean
shiftPid last d = { id := d, parent_id := some last.id, gparent_id := last.parent_id }
```

`up` ya no añade *un* nodo: agrupa la última fila por el identificador desplazado y crea
**un nodo por grupo** (`newRow`). Consecuencias medidas (`test_window/w2.tsv` vs `w3.tsv`,
22 instancias): veredictos y número de soluciones idénticos, nodos +0…18 %, segundos +5…19 %.

**(b) Los owners de un nodo de fila no son los globales.**
`rowOwners = (⋃ owners de los padres) ∩ gowners + él mismo`. Un nodo de fila hereda **solo
lo de sus propios padres**, así que el `up` es por sí mismo un paso de poda. Esto es lo que
rompió el atajo "el nodo nuevo posee a todo el mundo", del que colgaban media docena de
construcciones.

**(c) Owners planos y podas como `filter`.** La tabla por pasos del ejecutable aquí es un
índice: "owners al paso k" es un `filter`. Y toda poda es un `List.filter`, así que la
monotonía sale de lemas genéricos en vez de análisis de casos.

**(d) `Classical.choice` se evita a propósito**, y hay una trampa concreta documentada:
`omega` zeta-reduce un `let` local y parte por casos lo que encuentra dentro *usando
`Classical`*. Por eso `SupRow`/`SupRw` en `HereditaryUp.lean` son definiciones de nivel
superior y no `let`s — como `let` metían `Classical.choice` en el cierre de todo lo de abajo.

**(e) `rowOwners` corta con un `filter` plano, no con `intersectOwners`.** Coinciden en todo
estado que la máquina construye; el filtro plano da
`rowOwners_mem_gowners_or_self` **sin hipótesis de validez**, que si no habrían tenido que
arrastrar decenas de lemas.

### 3.4 Teoremas principales probados

**De la ventana:**
* `ParentId.GPMP_reachable` — *el abuelo que el id declara es el padre de todo padre*,
  sin axiomas, por construcción.
* `ParentWitness.parents_differ_below` — **dos padres de un nodo difieren solo en el abuelo**:
  comparten id de mapa por `PMP` y padre por `GPMP`. Es el nivel extra de historia, dicho
  como teorema.
* `ParentId.chain_eq_of_mapIds_eq` — una cadena queda determinada por su sucesión de ids de mapa.

**De la revisión:**
* `pruned_reviewAgg` — solo quita.
* `ChainSound_reviewAgg` — no pierde ninguna solución.
* `Fuel.lean`: `review_stable`, `review_idempotent`, `reviewPass (review g) = review g`.

**Del descenso (§5):**
* `Descent.extend_of_common_owner` — la extensión de una cadena parcial *es* un owner común.
* `Descent.extend_anchor` (un pick) y `extend_pair` (dos, por consistencia de pares).
* **`Descent.commonOwner_of_singleParents`** — con un solo padre por nodo, la intersección
  `k`-aria que pide el descenso **es la binaria leída `k` veces en el mismo nodo**.
* `ParentWitness.par_witness_triple`, `owners_below_unique` — con un padre, el pasado de un
  nodo es un camino forzado.

### 3.5 Teoremas pendientes

* **`extend_triple` sin `SingleParent`** — elegir, entre padres que solo difieren en el
  abuelo, uno que posea a los tres picks. La ventana ancla dos de los tres componentes del
  candidato y deja libre justo el tercero, que es donde los padres difieren. **No lo cierra.**
  Y no lo cerraría una ventana más ancha: con ventana `w` dos padres coinciden en `w-1`
  componentes y difieren en el más viejo — el desacuerdo se muda, no desaparece.
* **`SpcSupport.SpcStable`** — la primerísima forma del mismo muro: pide un owner común de
  `x`, `y` **y** `v`, y `Spc` recorre parejas arbitrarias, no enlaces de padre, así que la
  determinación por identificador no le llega.
* **`ImprovesCima.FamTopSingle`** — *el último paso de una familia tiene un solo nodo, su top*.
  Con la fila es falso: `restTest` lee el ancla **solo** para elegir qué lado puede avalar
  el par, así que dos tops de un mismo lado se quedan los dos dentro. Vuelve a ser hipótesis
  con nombre. Trampa para quien lo retome: **`ConeAt` tiene dos cláusulas y las dos cuelgan
  de ella**, porque la primera se deriva de la segunda.

### 3.6 Invariantes

`Reader.RCtx g` es el paquete que todo lo demás asume:

| campo | dice |
|---|---|
| `oos` | **`SelfOwn.OOS`**: al paso propio de un nodo, sus owners no contienen más que él |
| `snn` | los pasos de los nodos son ≥ 0 |
| `gn` | todo owner global es un nodo |
| `shape` | `Parents.Shape`: los padres están un paso por debajo y son nodos |
| `rootz` | `Sons.RootAtZero` |
| `pmp` / `gpmp` | el id declara padre y abuelo correctamente |
| `ownb` | **`SelfOwn.OwnBelow`**: los owners viven por debajo de `current_step` |
| `below` | todo nodo está por debajo de `current_step` |
| `nodup` | los ids no se repiten |

> **`OOS` es el invariante más rentable del proyecto.** "Un owner al paso propio *es* el
> nodo" es la pieza que cerró `FabricAdd`, `HereditaryUp.add_new`, `PinSend.pin_send`,
> `ClauseReview` y `PinDeath.tops_unique`. Cuando algo del puerto de la ventana se rompe,
> `OOS` es lo primero que hay que probar.

Otros: `Pruned g g'` (estrechamiento: mismo paso, gowners ⊆, nodos derivados con owners y
padres contenidos), `Keeps`, `AggFixpoint.AggOk` (consistencia de pares tras la revisión),
`AdjacentOwners.Adj` (owners adyacentes ⇔ padres/hijos).

---

## 4. Reader

### 4.1 Descripción funcional

Extrae asignaciones concretas del estado final. Dos versiones y un modelo:

* **`PathReader`** (`Reader/PathReader.lean`) — una solución. Selecciona un nodo por paso,
  registra el bit y avanza.
* **`PathExpReader`** (`Reader/PathExpReader.lean`) — **todas**. En vez de elegir, bifurca
  un lector derivado por candidato, filtra cada rama por su selección, y recoge las
  soluciones de las ramas que llegan al final del bloque de literales.
* **`ReaderExec`** (`Model/ReaderExec.lean`) — el lector como programa demostrable, el que
  usa el veredicto.

`ReaderExec` es el lector del autor **sin backtracking**: toma el primer paso que aún tiene
elección, prueba sus nodos en orden, fija el primero que la revisión agresiva deja válido, y
sigue. **Nunca deshace un pin.** Cada ronda cuesta como mucho una revisión por nodo del paso,
y las rondas están acotadas por `measure` (todo pin quita algo).

### 4.2 Subcomponentes clave

* `Model/Reader.lean` — `RCtx`, `Readable`, el bucle como relación, `Pinned`.
* `Model/ReaderAgg.lean` — el mismo bucle sobre `reviewAgg`.
* `Model/ReaderExec.lean` — el bucle como programa, `readerVerdictW`.
* `Model/PickInduction.lean` — `choiceAt`, `hasChoice`, la inducción sobre `measure`.
* `Answer.lean` — `readGreedy`: variable a variable, pin `v=0`, revisar, y si el estado
  muere pin `v=1`.

### 4.3 Claves del diseño

**(a) Bifurcar por id de *mapa*, no por `PathNodeId`.** Desviación deliberada respecto de
Julia: varios `PathNodeId` de un mismo paso comparten id de mapa (mismo valor alcanzado desde
padres distintos), y `filter!` compara por id de mapa — así que bifurcar por `PathNodeId`
produce grafos filtrados byte a byte idénticos y soluciones duplicadas. Deduplicar al
bifurcar es equivalente y deja la enumeración lineal en el número de configuraciones distintas.

**(b) La revisión se re-ejecuta tras cada pin**, y eso es lo que evita tener que pedir
ninguna propiedad Helly estática de las tablas de owners. Es la diferencia entre pedir
consistencia global de antemano y comprobarla incrementalmente.

**(c) Sin backtracking, a propósito.** El lector no desanda. Eso hace la corrección trivial
(solo acaba en un estado que denota un camino) y mueve toda la dificultad a la completitud
(que no se atasque).

### 4.4 Teoremas principales probados

* **`ReaderExec.readerVerdictW_sound`** — *sin hipótesis*: si el lector termina sobre algún
  estado de la línea final, `φ` es satisfacible. Da igual lo que las tablas hayan tomado
  prestado: el lector solo termina en un estado que denota un camino, y ese camino es un modelo.
* `Reader.Inhabited_of_pickSome_readable` — el bucle de lectura cierra para la revisión base.
* `ReaderAgg.Inhabited_of_pickSomeAgg` — y para la agresiva.
* `ReaderAgg.reviewAggFuel_form` — **todo resultado de `reviewAgg` es un resultado de
  `review`** de un estado con `RCtx`, así que todo hecho estático del lector base se aplica.
* `Answer.answer_sat_sound` — la asignación que devuelve satisface `φ`, comprobado.

### 4.5 Teoremas pendientes

* **`ReaderExec.ProgressAgg`** (= `readerVerdictW_complete`) — *el lector nunca se atasca*:
  en todo estado que visita, el primer paso con elección tiene un nodo cuyo pin deja el grafo
  válido. **Es lo único abierto en esta ruta**, y es exactamente la diferencia entre
  "unknown" y "SAT".
* `ReaderAgg.PickSomeAgg` — la misma frase, en la versión relacional.

### 4.6 Invariantes

* `RCtx` (§3.6), que el lector arrastra a través de cada pin.
* `Readable` / `ReadableAgg` — el estado es un punto fijo de la revisión con `RCtx`.
* `Pinned` / `NoChoice` — **el caso base**: si no queda elección en ningún paso, el estado
  denota un camino, y ese camino decodifica a un modelo.
* `measure` — decrece con cada pin; es lo que hace terminar el bucle.

---

## 5. Estado de la verificación y rutas abiertas

> *(sección añadida — es el objetivo del documento)*

### 5.1 El único hueco, dicho con precisión

Todo lo que separa al proyecto de un teorema sin hipótesis cabe en una frase:

> **Un estado final válido está inhabitado** — si el grafo sobrevivió a todos los filtros y
> sigue siendo válido, contiene un camino completo, o sea una solución.

La dirección contraria (no se pierde ninguna solución) **está cerrada**:
`ConservationImproves.pureRunW_ne_nil`. Y la corrección de las respuestas también, porque
`answer` devuelve certificado.

**Y esa frase es una sola, no dos.** Las dos formas de responder `unknown` son las dos
caras de ella:

* sobre `φ` satisfacible, el lector se atasca ⇒ falta *"válido ⇒ inhabitado"*;
* sobre `φ` insatisfacible, sobrevive un estado válido ⇒ ese estado es un **fantasma**, un
  válido sin cadena, que es la negación de la misma frase.

Por eso `DeclaredVerdict.verdict_iff` sale entera de una hipótesis: no hay una mitad SAT y
otra UNSAT que atacar por separado.

### 5.2 Por qué es difícil: el muro

La máquina mantiene **2-consistencia** (consistencia de pares, `AggOk`). El descenso
necesita **k-consistencia**. En lenguaje de propagación de restricciones, eso no se sigue
para una red arbitraria; aquí solo puede seguirse de la estructura que la máquina mantiene.

Concreto: `Descent.extend_of_common_owner` pide un owner común de **todos** los picks ya
hechos. Para uno es gratis (`extend_anchor`), para dos también (`extend_pair`, por
consistencia de pares). Para tres, la consistencia de pares da un testigo por pareja y nada
obliga a que coincidan. La transitividad de la posesión lo cerraría, pero es falsa: medido,
52.720 de 380.746 tríos ordenados la incumplen.

### 5.3 Lo que sí se cerró, y qué clase cubre

`Descent.commonOwner_of_singleParents` + `NoDeadEndVerdict.sat_of_singleParents` cierran el
veredicto **sin ninguna hipótesis abierta** para los estados con `SingleParents`: *ningún
nodo tiene dos padres*. Y por `parents_differ_below` eso significa exactamente:

> la línea anterior no tiene dos nodos con la misma historia de dos pasos.

Con ventana `w` sería "la misma historia de `w-1` pasos". **Ensanchar la ventana nunca lo
convierte en teorema** (el desacuerdo se muda al componente más viejo) **pero sí agranda la
clase**, porque fusionar exige coincidir en más historia. Eso, y no otra cosa, es lo que se
compra con el +0…18 % de nodos.

### 5.4 Las rutas abiertas, y qué pide cada una

Todas son intentos del mismo salto. Cada una es una hipótesis con nombre, medida por sondas:

| familia | hipótesis raíz | dónde |
|---|---|---|
| **A** fantasmas | `RoundInvariant.GhostsLine` — *la hipótesis declarada actual* | `RoundInvariant.lean` |
| **B** nada prestado | `PinClause.SideKeepAt` y sus seis entradas | `PinDeath.lean`, `PinClause.lean` |
| **C** validez hereditaria | `HereditaryValid.ChainClosureAt` / `OwnSupportAt` | `HereditaryValid.lean` |
| **C'** regla del top | `ImprovesCima.FamTopSingle` + `FamTriOkCone` | `ImprovesCima.lean` |
| **D** descenso | `Descent.CommonOwner` — cerrada bajo `SingleParents` | `Descent.lean` |
| **E** lector | `ReaderExec.ProgressAgg` | `ReaderExec.lean` |
| **F** rebanada | `SpcSupport.SpcStable` | `SpcSupport.lean` |

El mapa de dependencias entre ellas está en §5.6; la lectura corta es que **son seis
cortes distintos de la misma frase**, no seis problemas.

### 5.5 El grado de entrada de la fila, medido

`lake exe row-degree` (sonda `Probes/RowDegree.lean`) mide `SingleParents` directamente:
el histograma de `n.parents.length` sobre **todo nodo de todo estado de toda línea**. Por
`parents_differ_below`, el grado de entrada de un nodo es exactamente el número de
historias de dos pasos distintas que convergen en él.

`random 20 3 31337` — 20 fórmulas, 1.241 estados, 23.758 nodos por encima del paso 0:

| | |
|---|---|
| grado 1 | **92,7 %** |
| grado ≥2 | **7,2 %** — máximo **3**, media **1,07** |
| en el bloque de literales | 9,8 % |
| en el bloque de cláusulas | 4,0 % |

Y el contrafactual, agrupando la línea anterior por sus primeros `w-1` componentes:

| ventana | 23.365 ids → grupos | padres por grupo |
|---|---|---|
| `w = 2` | 19.714 | 1,185 |
| `w = 3` | 21.833 | **1,070** |

**Tres lecturas, y la tercera es la que cambia el plan.**

1. **`SingleParents` no vale.** Falla en el 7,2 % de los nodos, así que la clase que
   `commonOwner_of_singleParents` cierra **no es «casi todo»**. El resultado de §5.3 es
   real pero no es el resultado principal.
2. **El tercer componente se cobró el 62 % del exceso.** De 0,185 padres extra por grupo a
   0,070. Eso es lo que compra el +0…18 % de nodos, cuantificado.
3. **El residuo es pequeño y acotado: máximo 3.** Esto es lo importante. El
   `extend_triple` abierto no es *«elegir entre los nodos del paso de abajo»*: es **elegir
   entre ≤3 candidatos que coinciden en dos de sus tres componentes** y difieren solo en el
   abuelo. Un enunciado acotado, no uno cuantificado sobre todo el paso.

> Medido sobre fórmulas aleatorias pequeñas (3+ variables). Las instancias estructuradas
> (Tseitin, coloreo) están sin medir — la sonda las aguanta pero tarda.

### 5.6 Mapa de dependencias entre las rutas

Trazado leyendo los teoremas de implicación, no supuesto. La convención `X_of_Y` del repo
hace el grafo rastreable: cada flecha de abajo es un teorema con nombre.

#### El objetivo, único

```
                    ┌────────────────────────────────────────┐
                    │  «un estado válido está inhabitado»    │
                    │  (Certifies.ValidHasChain, en los      │
                    │   estados que la máquina construye)    │
                    └────────────────────────────────────────┘
                         ↓                          ↓
        DeclaredVerdict.verdict_iff        Answer.answer_unsat_of_unsat
        (la máquina decide)                (nunca dice «unknown»)
```

#### Las seis familias

```
A  GhostsLine ──tablesSound_of_ghosts──▶ TablesSound
                filterSlices_of_ghosts ─▶ FilterSlices ──sat_of_ghosts──▶ ★
                                                            │
                                            DeclaredVerdict.sat_sound
                                            Answer.answer_unsat_of_unsat

B  SideKeepFarAt ──sideKeep_of_far───┐
   RowWitnessAt  ──sideKeep_of_row───┤
   SemWitnessFarAt ─semWitness_of_far─▶ SemWitnessAt ─rowWitness_of_sem─┤
   TopSideAt + TopKeepAt ─sideKeep_of_top─┤
   ClosedWitnessAt ──sideKeep_of_closed──┤
   ChainSideAt ──sideKeep_of_chainSide───┤
                                         ▼
                                  ★ SideKeepAt ──flipSat_of_sideKeep──▶ FlipSatAt
                                         │                                  │
                                    sat_of_sideKeep                    flipAt_of_sat
                                                                            ▼
                                                                         FlipAt
                                                                    pathAt_of_flip
                                                                            ▼
                                                                         PathAt
                                                          pinJoinAt_of_paths│
                                                                            ▼
                                       PinJoinVar (PROBADO) ──┐         PinJoinAt
                                       PinJoinClause ─────────┴─pinJoin_of_stages─▶ PinJoin
                                                                      sat_of_pinJoin

C  ChainClosureAt ─topValid_of_chainClosure─▶ TopValidAt ─validSide_of_topValid─┐
   OwnSupportAt ──validSide_of_ownSupport───────────────────────────────────────┤
   RulePreservesValidity ─validSide_of_rulePreserves────────────────────────────┤
                                                                                ▼
                                   ValidSideAt ──(+ ValidWitAt, SendPinAt)──▶ sat_of_validSide
                                                                              sat_of_validSideOnly

C' FamTopSingle + FamTriOkCone ──famTriOk_of_cone──▶ FamTriOk ──sat_of_famTriOk──▶ ★
   SideChainAt ─chainSide_of_sideChain─▶ ChainSideAt ─pairSide_of_chainSide─┐
   SideSupportAt ──pairSide_of_sideSupport───────────────────────────────────▶ PairSideAt
                                                        pinned_source_valid_of_pairSide

D  SingleParents ──commonOwner_of_singleParents──▶ CommonOwner
                                    noDeadEnd_of_commonOwner│
                                                            ▼
                                                        NoDeadEnd ──sat_of_noDeadEnd──▶ ★

E  ProgressAgg ──readerVerdictW_complete──▶ el lector termina ──readerVerdictW_sound──▶ ★

F  SpcStable ──supported_of_spcStable──▶ soporte de la rebanada ─sat_of_someSpcStable─▶ ★
```

#### Lo que el mapa enseña

**1. Seis de las «rutas» eran una.** La familia B tiene **un tronco**
(`SideKeepAt → FlipSatAt → veredicto`) y **seis puertas de entrada** distintas, todas
probadas. `TopKeepAt`, `TopSideAt`, `ChainSideAt`, `RowWitnessAt`, `SemWitnessAt`,
`ClosedWitnessAt` y `SideKeepFarAt` **no son siete problemas**: son siete maneras de decir
lo mismo, y basta cerrar una cualquiera. Eso reduce el inventario real de frases abiertas
de ~15 a **6**.

**2. La mitad de la corrida ya está cerrada.** `PinVar.pinJoinVar` es incondicional (solo
pide `hwf`): **el estadio de las variables no necesita hipótesis**. Solo queda el estadio
de las cláusulas (`PinJoinClause`), que `pinJoinClause_of_paths` reduce a `PathAt`. Es el
recorte más concreto que hay sobre la mesa.

**3. No hay flechas entre familias.** Ninguna de A–F implica a otra. Son **condiciones
suficientes independientes** para el mismo objetivo, cada una cortando el problema por un
sitio distinto. Así que no hay que elegir «la correcta»: basta con que **una** cierre.

**4. El eje para elegir es la localidad**, no la fuerza. Ordenadas de más local a más global:

| familia | sobre qué habla | tamaño del cuantificador |
|---|---|---|
| **A** `GhostsLine` | **una pasada de una operación** sobre un estado pinchado | el más pequeño |
| **E** `ProgressAgg` | la trayectoria que el lector recorre, no todos los estados | pequeño |
| **B** `SideKeepAt` | las uniones pinchadas de una línea | medio |
| **C/C'** | los lados y sus familias en una unión | medio |
| **F** `SpcStable` | las parejas `Spc` de una rebanada, en todos los pasos | grande |
| **D** `CommonOwner` | **toda cadena parcial de todo estado** | el más grande |

Esa es la razón documentada de que `GhostsLine` sustituyera a `CommonOwner` (v133) como
hipótesis declarada: dice menos y basta igual. Medida sin excepción (sonda `helly ghosts`,
3,02 M entradas fantasma sobre K4 y paridad).

**5. D es la única con descarga parcial probada.** `commonOwner_of_singleParents` cierra la
familia D entera para la clase `SingleParents`. Ninguna otra familia tiene todavía una
clase nombrada donde su raíz sea teorema. Si el grado de entrada de la fila (§5.5) resulta
ser 1 casi siempre, D deja de ser la más cara y pasa a ser la más barata.

#### Rutas muertas o superadas, para no reabrirlas

* `Descent.CommonOwner` como *hipótesis declarada* está superada por `GhostsLine` (v133).
  Sigue viva como **teorema bajo `SingleParents`**, que es otra cosa.
* `ImprovesCima.FamTopSingle` **era** teorema y la ventana lo devolvió a hipótesis
  (§3.5). No es una ruta nueva: es una regresión conocida y localizada.
* `SymTriReview` (1.757 líneas) se borró: modelaba una revisión triangular abstracta que la
  máquina no ejecuta.

### 5.7 A qué rutas le llega el tercer componente

La ventana no es uniformemente buena: **paga donde el argumento es «identificar un nodo
desde su historia» y cuesta donde era «un nodo por paso»**. Por familia, y con el teorema
concreto en cada caso:

#### Paga, y ya está cobrado

* **D — descenso.** `commonOwner_of_singleParents`. Y, con §5.5, el residuo abierto deja de
  ser *«un nodo cualquiera del paso de abajo»* y pasa a ser *«≤3 candidatos que coinciden en
  dos de tres componentes»*.
* **C — validez hereditaria.** El mismo residuo, literalmente. La cláusula `par` de un
  soporte pide un padre de `x` enlazado a `x` **y** a un segundo miembro; restringida a una
  rebanada hace falta un testigo de **terna**, que la consistencia de pares no da. Por
  `parents_id_eq` los dos testigos que sí da llevan el **mismo nodo de mapa**, y
  `par_witness_triple` los identifica en cuanto el nodo tiene un padre.

  > Esto corrige a la baja mi «no hay flechas entre familias» de §5.6: C y D **no se
  > implican**, pero **tocan fondo en el mismo lema**. Cerrar `extend_triple` cierra las dos.

* **A — fantasmas, por la vía de la identificación.** La cadena
  `PinExtends.eq_of_ids` → `chain_of_ids` → `PairPins.realizes_of_entryPins` →
  `tablesSound_of_entryPins` produce `TablesSound`, que es **hipótesis de `GhostsLine`**. La
  ventana obligó a `eq_of_ids` a levantar la igualdad de ids de mapa a los **tres**
  componentes, y lo hace.
* **B — nada prestado.** `RunNoBorrow.Genuine` y `canon` llevan ya los tres componentes, y
  `glue_canon` demuestra que dos asignaciones que coinciden en un nodo coinciden también en
  su **abuelo**. Con el estadio de variables ya cerrado (`pinJoinVar`), eso cae entero del
  lado abierto, el de las cláusulas.

#### Cuesta

* **C' — regla del top.** Un lado ya no deja *un* top sino una **familia**: `FamTopSingle`
  dejó de ser teorema, `cert_top_of_top` se debilitó a «un top del mismo lado», y
  `tops_unique` hubo que rehacerlo por `OOS`. Es el precio, y está pagado y localizado (§3.5).
* **`PairPins.entryPins` crece.** Identificar un nodo pide fijar sus `w` ids de mapa, así
  que pasa de dos pines por extremo a tres: la hipótesis `EntryPin` —*que fijarlos mantenga
  el estado válido*— es ahora **más fuerte**. La conclusión a cambio es correcta, que con
  ventana 2 sobre una máquina de ventana 3 no lo sería.

#### Ni paga ni cuesta

* **F — `SpcStable`.** `Spc` recorre **parejas arbitrarias** a pasos arbitrarios, no enlaces
  de padre. La determinación por identificador no le llega. Es la que menos se beneficia y
  la que más global es (§5.6): dos razones para no atacarla primero.
* **E — el lector.** Pincha **ids de mapa**, y la ventana afina los nodos sin cambiar el
  conjunto de decisiones del lector. El beneficio sería indirecto —tablas más finas ⇒ menos
  fantasmas ⇒ la validez es un test más afilado— y no hay teorema que lo diga.

#### La regla, en una frase

> El tercer componente paga exactamente donde el argumento necesitaba **identificar un nodo
> por su pasado**, y no paga donde el argumento cuantifica sobre **parejas cualesquiera**.

### 5.8 `extend_triple`, explorado

Exploración aparte en [extend_triple.md](extend_triple.md): la obligación acotada, la
medición que dice que **lo que hace casi todo el trabajo no es la cota ≤3 sino que los picks
formen un clique** (566 fallos de 1.457 sin la condición, 3 de 16.364 con ella — y los tres
resultan no ser realizables como picks de una cadena, así que `CommonOwner` sobrevive), la
reformulación a *«el owner común de dos picks un paso más abajo, ¿posee al nodo?»*, y tres
ángulos de ataque valorados.

### 5.9 La multiplicidad no es el muro: el lector decide antes de andar

Dos días de exploración del descenso convergieron en un obstáculo, y está ahora demostrado que es
**ese y no otro**:

* `Descent.parent_owns_of_coherent` — un owner de `x` lo posee ya **algún** padre de `x`, y sale de
  la *coherencia del punto fijo* (`cohP`), no de la consistencia de pares;
* `Descent.parents_own_unique_owner` — y si en ese paso la tabla de `x` tiene **un solo** owner, lo
  poseen **todos** sus padres.

> Lo único que impide al descenso elegir un padre es que las tablas tengan más de un candidato por
> paso. Donde la revisión dejó la tabla decidida, no hay nada que elegir.

Medido: de 999.560 celdas `(nodo, paso)` no vacías, **56,1 % decididas**, 43,8 % con dos o más
(máximo 512), y solo el **11 %** de los nodos tiene todas sus celdas decididas.

**Y ahí está el error de encuadre de toda la ruta D.** `NoDeadEnd` pide que el descenso funcione en
un estado **estático y todavía indeciso**. La máquina no trabaja así: `ReaderExec` **pincha y
vuelve a revisar** en cada paso, y cada pin decide más tablas. Nunca tiene que extender una cadena
parcial en un estado indeciso — decide primero.

El repo ya lo dice, y conviene citarlo literal:

* `ReaderAgg`: *«la revisión se re-ejecuta tras cada pin, así que **no se pide ninguna propiedad
  Helly estática** de las tablas de owners»*;
* `PinExact`, sobre la sonda `helly pins` (v117): un pin *«elimina exactamente los nodos fuera de su
  rebanada… y todo pin es válido, **aunque la rebanada tiene muchos huecos Helly-3**»*.

Esa última frase es la medición de lo que dices: **los huecos de Helly no afectan a la validez del
pin.** El fallo de Helly bloquea el descenso y le da igual al lector, porque el pin quita *nodos*,
y lo que la criba tira son *pares de owners*, que no matan nodos.

**Así que la obligación viva es `PinExact g mid`** — *un pin solo quita nodos fuera de su rebanada* —
y su estado es bastante mejor que el del descenso:

| pieza | estado |
|---|---|
| `ReaderExec.readerVerdictW_sound` | ✅ **sin hipótesis** |
| `PinExact.inSlice_of_survives` (la otra mitad) | ✅ probado |
| `PinExact.isValid_pin_of_pinExact` | ✅ probado: `PinExact` + simetría ⟹ el pin es válido |
| `PinExactSome.pickSomeAgg_of_somePinExact` | ✅ probado, y solo pide `PinExact` en **un** owner de **un** paso con elección |
| `PinExact` | ❌ abierto, medido sin excepción |

Y nótese lo barato de la última fila: no hace falta `PinExact` en todos los owners globales
(`pickSomeAgg_of_pinExact`), basta en **uno** por estado.

> **Corolario para el mapa de §5.6:** dije que no hay flechas entre familias. Sigue siendo cierto
> como implicación lógica, pero hay una flecha **conceptual** que no había visto: lo que bloquea D
> (la multiplicidad de las tablas) es exactamente lo que E disuelve por construcción, porque E
> decide antes de andar. D y E no son dos intentos independientes: son el problema visto desde el
> estado estático y desde la dinámica.

### 5.10 Y el lector tampoco reduce: `PickSome` ⟺ `Inhabited`

La intuición de §5.9 —*el lector decide antes de andar, así que la multiplicidad no le afecta*— es
**correcta como mecanismo y está demostrada en el repo**:

> `Reader.isValid_pin_of_chain` — *«el lector siempre puede seguir una cadena que exista: pinchar
> el nodo de mapa que la cadena elige en un paso mantiene el grafo válido — a través del pin, de la
> pasada de `cleanInvalid` **y de las dos pasadas de coherencia**»*.

O sea: **si hay camino, la multiplicidad da igual**, exactamente como decías. El pin no lo rompe en
ninguna de las tres operaciones.

**Pero eso cierra el círculo en vez de abrirlo.** `Reader.PickSome_of_Inhabited` está demostrado, y
con `Inhabited_of_pickSome_readable` en la otra dirección el repo lo dice sin rodeos:

> *«`PickSome` e `Inhabited` caen o se sostienen juntos. Así que el `throw("GRAVE ERROR")` del
> lector no es un asidero más débil que "no hay zombis": **es el mismo enunciado**.»*

Así que la familia **E no es una condición suficiente independiente: es equivalente al objetivo.**
No hay nada que ganar atacándola esperando que sea más barata.

### 5.11 Tres equivalencias, y lo que quedan de rutas

Corrección al mapa de §5.6, que las presentaba como seis condiciones suficientes independientes.
**Dos de las seis son equivalencias al objetivo**, demostradas:

| | |
|---|---|
| **E** `PickSome` ⟺ `Inhabited` | `Reader.PickSome_of_Inhabited` + `Inhabited_of_pickSome_readable` |
| **D**, caso del filtro: `ReqCompletion g reqs` ⟺ `NoDeadEnd (filterAllAgg g reqs)` | `DescentRun.reqCompletion_of_noDeadEnd` + `DescentFilter.noDeadEnd_filterAllAgg_of_completion` |

Y `PinExact`/`PinCovers` viven dentro de E, así que heredan lo mismo: son formas de decir *«hay
camino en el nodo que se pincha»*.

**Lo que eso deja en pie**, y es la lista corta que yo usaría de ahora en adelante:

* lo que está **cerrado sin hipótesis**: la conservación (`pureRunW_ne_nil`), la corrección de las
  tres respuestas (`answer_*_sound`), el veredicto para la clase `SingleParents`
  (`sat_of_singleParents`), y que el lector nunca se equivoca cuando termina
  (`readerVerdictW_sound`);
* lo que es **equivalente al objetivo** y por tanto no es un atajo: E entera, el caso del filtro
  de D, `PinExact`, `ValidHasChain`, `Inhabited`, `SupportedG`;
* lo que sigue siendo **genuinamente una condición suficiente más fuerte**, o sea donde de verdad
  se puede ganar terreno: `GhostsLine` (A, y es la más local de todas), el tronco de B
  (`SideKeepAt` con sus seis puertas), C/C' y F.

> La lección de método: antes de invertir en una hipótesis de este repo, **comprobar si es
> equivalente al objetivo**. Tres de las que parecían reducciones no lo eran, y las tres se
> detectan demostrando la vuelta, que en los tres casos salió en menos de treinta líneas.

### 5.12 `GhostsLine` explorado: la hipótesis declarada tampoco es más barata

Aplico la lección de §5.11 a la que quedaba primera de la lista, **A**, y el resultado es el cuarto
de la serie — y el más incómodo, porque `GhostsLine` es *la hipótesis declarada del resultado de
cabecera* (v141, `DeclaredVerdict.verdict_iff`).

**Lo que dice.** Para cada entrada `(x, v)` del estado `B` que queda tras el review base del estado
fijado, una de tres: la entrada es **asimétrica**, o las dos tablas **no comparten owner** en algún
paso, o la entrada **está en un camino** del estado final `R`. Las dos primeras son exactamente las
dos patas del filtro agresivo del autor; la tercera es realizabilidad.

**Lo que encontré, leyendo la prueba que ya existía.** `tablesSound_of_ghosts` aplica la hipótesis
**solo a pares que siguen siendo entrada de `R`**, y en sus dos primeras ramas *refuta* las dos
patas en vez de usarlas. Eso no era un detalle de estilo: es el enunciado entero colapsando.

* **`legs_dead`** (nuevo) — si `(x, v)` sobrevive hasta `R`, entonces en `B` es simétrica **y**
  comparte todos los pasos. Razón: `R` es `AggOk`, y las dos propiedades **suben** a las tablas más
  grandes de `B` (la segunda por el contrarrecíproco de `shares_false_of_sub`, que ya estaba).
* **`GhostsDetectableR`** (nuevo) — la misma hipótesis restringida a esos pares. Basta para el
  veredicto (`tablesSound_of_ghostsR`), o sea que restringir no pierde nada.
* **`ghostsR_iff_tablesSound`** — y restringida **es** el objetivo: `GhostsDetectableR B R ↔
  TablesSound R`. Con las dos patas muertas, solo queda el tercer disyunto, que es la definición de
  tabla exacta.
* **`ghostsLineR_iff_filterSlices`** — lo mismo a nivel de la ejecución: `GhostsLineR φ ↔
  FilterSlices φ`.

Todo con cierre `[propext, Quot.sound]`.

**Cómo hay que leerlo.** `GhostsLine` no es una reducción de `FilterSlices`: es `FilterSlices` **más
un excedente que el veredicto no lee nunca**. El excedente es la parte que habla de las entradas que
*mueren* en el review agresivo — «toda entrada fantasma era ya detectable tras la primera pasada»,
que es la medida de v140 (3,02 M fantasmas, ninguna excepción). Esa medida es real y es buena
evidencia; simplemente **valida la parte que no se usa**, además de la que sí.

Esto también explica algo que en §5.6 anoté como raro sin entenderlo: `GhostsLine` sustituyó a
`CommonOwner` en v133 *por localidad*, no por fuerza — y v141 ya lo advertía («no está demostrado
que `GhostsLine` sea más débil que `CommonOwner`»). La localidad es cierta: habla de una pasada de
una operación. La debilidad no: por debajo es el objetivo.

**Recomendación concreta, y es un cambio de enunciado, no de prueba.** Declarar `FilterSlices` (o
`GhostsLineR`) en lugar de `GhostsLine` en `DeclaredVerdict`: es estrictamente menos obligación,
tiene exactamente las mismas consecuencias, y deja de pedir nada sobre entradas que el algoritmo
tira.

**Y dónde queda el terreno que sí se gana.** Con A caída, el tronco de B es el único de la lista
corta que pide **menos** de forma visible, y en dos ejes a la vez
(`RunInhabited.FilterSoundAt` frente a `FilterSlices`):

| eje | `FilterSlices` | `FilterSoundAt` |
|---|---|---|
| qué entradas | **todas** | solo las que apuntan a un **paso literal** o al paso 0 (`LitStep`) |
| qué fijaciones | `ws`, `rq` **arbitrarios** | las del propio envío: `weakReqOfCnf φ d`, `reqOfCnf φ d`, con `d` hijo real |

Con la advertencia de rigor: no son comparables como implicación, porque `FilterSoundAt` también
**arrastra un invariante más débil** (`SoundAt` en vez de `TablesSound`). Es el intercambio normal
de una inducción: invariante más débil, obligación más débil. Y por delante tiene ya dos puertas
demostradas (`filterSoundAt_of_sends`, `filterSoundAt_of_pins`).

> Cuarta equivalencia, mismo método, otra vez por debajo de treinta líneas de vuelta. Ya no es
> casualidad: en este repo **las hipótesis que hablan del estado final tienden a ser el objetivo**,
> y las que hablan de *qué entradas* y *qué fijaciones* son las que de verdad recortan.

### 5.13 `FilterSoundAt` atacado: qué es libre, qué no se puede factorizar, y qué cambiaría en la máquina

Primero el test de §5.11: **`FilterSoundAt` no es una equivalencia**. Es un invariante sobre todos
los estados de la ejecución y el objetivo es un bit (`Satisfiable φ`); no hay vuelta. Pasa el test,
y por eso es el sitio donde trabajar.

**La cadena ya está reducida al mínimo en el repo**, y conviene tenerla a la vista:

`FilterSoundAt` ⟸ `SendPinSoundAt` (los requisitos débiles no hacen nada, v144) ⟸ `PinStepSoundAt`
(un pin cada vez, v143) ⟸ **`PinPairSoundAt`** — *un solo pin `r`, y solo las entradas hacia pasos
literales **distintos** del pinchado*. El paso pinchado ya está demostrado (`pinStep_of_pairs`).

#### Lo nuevo: el pin no crea callejones sin salida

**`RunSteps.realizes_pin`** (demostrado, `[propext, Quot.sound]`, sin hipótesis nuevas):

> tras un pin `r`, **todo nodo que sigue en pie está en una cadena del estado pinchado que pasa por
> el pin**.

La prueba es corta y dice exactamente dónde está el filo: un nodo vivo posee algo en el paso
pinchado; lo que posee lleva el pin (`ReaderComplete.pin_id`); el paso pinchado **es un paso
literal**, así que el invariante de la inducción entrega una cadena de `g` por `x` y por él; y esa
cadena pasa el pin, luego sobrevive.

Consecuencia de lectura: `Inhabited`/«no hay zombis» **para un paso de pin** sale gratis del
invariante. Lo que `PinPairSoundAt` pide de más es la **segunda** marca: que la cadena se pueda
obligar además a pasar por una entrada `q` dada.

#### Por qué `L = LitStep` es exactamente el tamaño correcto (un callejón que comprobé)

`SoundAt` está parametrizado por un conjunto de pasos `L`, y toda la cadena
(`soundAt_initSeed`/`join`/`addNode`/`sent_ofL`) solo pide `L 0` y que `L` sea cerrado hacia abajo.
El veredicto (`sat_of_lineSound`) solo usa **la diagonal en el paso 0**. Tentación obvia: tomar
`L := (· ≤ 0)` y quedarse con un invariante mucho más pequeño.

**No sirve, y la razón es informativa**: los dos únicos resultados libres que hay sobre un pin —la
rama gratis de `pinStep_of_pairs` y el nuevo `realizes_pin`— aplican el invariante **en el paso
pinchado**. Si `L` no contiene los pasos de los pines, se pierden los dos. `LitStep` es el menor
`L` cerrado hacia abajo que contiene el 0 **y todos los pasos donde caen pines**. Está calibrado,
no elegido a ojo.

#### Lo que no se puede factorizar (y ahorra una ruta entera)

La tentación siguiente es sacar el filtro de la ecuación: tenemos cadena por `(x,q)` y cadena por
`(x,r)`; ¿basta un lema puro de *fusión de cadenas*?

> `ChainMerge`: dos cadenas de un mismo estado que pasan ambas por `x` se pueden fusionar en una que
> pase por `x`, por la marca de una y por la marca de la otra.

**`ChainMerge` es falso**, y sin necesidad de buscar nada: basta una fórmula donde `v1` puede ser
cierta, `v2` puede ser cierta, y no a la vez. En un estado con ambas entradas en la tabla de un
mismo nodo, cada una realizable por separado, `ChainMerge` afirmaría una asignación con las dos.

Lo que eso dice: **la hipótesis de supervivencia al review no es decorado**. `PinPairSoundAt` no es
«pares realizables ⟹ triple realizable»; es «pares realizables **y la entrada sobrevive al filtro
agresivo** ⟹ triple realizable». Toda reducción que tire el filtro es falsa, así que no hay que
gastar tiempo en buscarla.

#### Cambios en el algoritmo, y lo que cuesta cada uno

Puesto en el lenguaje estándar: la máquina guarda una tabla por **par** de nodos y exige simetría
más «comparten owner en todo paso» — es decir, **consistencia de caminos (3-consistencia)** sobre un
grafo de restricciones **completo** (hay tabla entre todos los pares de pasos). El resultado clásico
de Freuder es que con grafo completo de `n` variables hace falta `n`-consistencia; 3 no basta *en
general*.

| cambio | qué compraría | coste |
|---|---|---|
| guardar tablas de **tripletas** (4-consistencia) | el pin pasa a ser consulta en un nivel | ×N por nivel; **polinómico**, pero la escalera no termina: cada nivel reproduce la obligación un piso arriba |
| tablas **condicionadas** por (variable, valor) | `PinPairSoundAt` se vuelve consulta | ×2n; mismo problema: condicionar por dos variables reaparece |
| que el identificador lleve **toda** la asignación | 2-consistencia ⟹ global, trivial | 2^n identificadores; **muere** |
| ventana de identificador de tamaño `k` (hoy `k=3`) | fuerza el encaje local hasta `k` | `|mapa|^k`, polinómico con `k` fijo; cierra si el ancho inducido del incidence graph es `< k`, que en 3-SAT no está acotado |
| **no unir filas cuando la unión crearía in-degree > 1** | `SingleParents` vale en todo estado, y su veredicto **ya está demostrado** (`sat_of_singleParents`) | ramifica en el 7,3% de las filas (medido §5.5: in-degree 1 en el 92,7%, máx 3–4) |

La última es la única que **cierra** algo, y por eso merece decirse con precisión: el `doJoin` del
driver —unir dos estados con la misma clave— es exactamente el punto donde la máquina cambia
ramificación por tablas. Es lo que la mantiene polinómica, y es lo que rompe `SingleParents`.

> Dicho al revés, y creo que es la forma más útil de tenerlo: **la máquina ya tiene una demostración
> completa para la parte del mapa donde no hay uniones, y el hueco abierto es exactamente el precio
> de las uniones.** No es un hueco difuso repartido por el algoritmo; está localizado en una
> operación y medido (7,3% de las filas).

#### Lo que yo atacaría a continuación

Dentro de `PinPairSoundAt`, el caso más prometedor es **`q` en un paso literal de la misma variable
que el pin**: `WeakNoop.lit_consistent` ya demuestra que un nodo vivo en un paso literal coincide
con todo pin sobre su misma variable, y el mapa enlaza `2v → 2v+1` **cruzado**, así que el `id` y el
`parent_id` de `q` quedan forzados por el pin. Lo único que no queda forzado es el **`gparent_id`**
—el tercer componente de la ventana—, y ahí es donde entraría un paso de descenso, uno solo. Es el
sitio del repo donde la ventana de 3 y el hueco abierto se tocan directamente.

### 5.14 La fila sin uniones: tienes razón, y aquí está la cuenta

La línea de la tabla de §5.13 («ramificar cuesta el 7,3% de las filas») **estaba mal contada**, y la
objeción es exactamente la correcta: partir un nodo obliga a crear identificadores nuevos, y eso se
propaga. Lo he demostrado, y sale peor de lo que yo sugería.

#### El teorema que lo decide

Dos lemas nuevos en `ParentId.lean`, y salen **sin ningún axioma** (ni `propext`):

* **`parents_agree_but_gparent`** — `PMP` fija el `id` de todos los padres de un nodo y `GPMP` fija
  su `parent_id`. Nada fija su `gparent_id`.
* **`singleParent_iff_gparents`** — luego **un nodo tiene un solo padre exactamente cuando sus
  padres coinciden en el `gparent_id`**.

Léelo así: un nodo del paso `s` lleva los ids de mapa de `s`, `s-1`, `s-2`. Sus padres coinciden en
`s-1` y `s-2` y solo pueden diferir en el de **`s-3`** — la primera coordenada que cae **fuera de la
ventana**.

#### Por qué no hay versión polinómica

De ahí sale la consecuencia que responde a tu «mmm», y es estructural, no empírica:

> **Ensanchar la ventana no baja el in-degree.** Con ventana `k`, los padres de un nodo siguen
> siendo libres en su propia componente `k`-ésima: la ambigüedad se muda del paso `s-3` al `s-k`,
> pero no desaparece. El in-degree está acotado por *una capa del mapa* (≤7 aquí) para **cualquier**
> `k` fijo.

Y por tanto: forzar in-degree 1 en todas partes = que el identificador distinga la historia
completa = **la ventana es el prefijo entero**. Eso es `|mapa|^pasos` identificadores. La única
ventana que da `SingleParents` siempre es la que convierte el identificador en el camino, que es
justo lo que la máquina existe para no hacer.

Y el 7,3% tampoco salva la cuenta, por la razón que apuntabas: los cortes **se componen**. Partir un
nodo distingue a todos sus descendientes; bajo la regla «no unir nunca», la anchura de la fila
multiplica por el in-degree en cada corte, así que con una fracción constante de filas ambiguas la
anchura es `2^Θ(n)`. Sin un teorema que acote cuántas copias mata el review después, la cuenta
honesta es exponencial. Dicho de otro modo: **la máquina que no une es búsqueda con retroceso**, y
proponerla como algoritmo no aporta nada.

#### Corrección a §5.13

Escribí que «el hueco abierto es exactamente el precio del `doJoin`». **No es exacto.** El olvido lo
hace **la ventana del identificador**; el `doJoin` lo amplifica al fundir procedencias distintas
bajo la misma clave, pero aunque no hubiera uniones de línea, dos historias que solo difieren en el
paso `s-3` colapsan igual en el mismo nodo. El precio es el de **olvidar**, y la ventana es el
tamaño del olvido.

#### Un atajo que puedo descartar ya, y me ahorra proponerlo

La alternativa barata al corte sería no partir el nodo sino **partir su tabla**: guardar los owners
por padre (×in-degree ≤ 7, local, sin propagarse, polinómico). **No compra nada**, y ahora sé por
qué con precisión: el descenso de un paso **ya es gratis** en la máquina actual —
`Descent.parent_owns_of_coherent` demuestra que todo owner de un nodo coherente es owner de *algún*
padre—, así que bajar manteniendo vivo **un** objetivo siempre se puede. Lo que `ChainSound` pide de
más es que los nodos **del propio camino** sean compatibles **entre sí**, todos contra todos, no
solo padre-hijo. Particionar la tabla por padre no toca esa demanda.

#### Lo que sí queda en pie de todo esto

`SingleParents` deja de ser «una clase de fórmulas» y pasa a ser **una medida del estado**: *no queda
ambigüedad en la coordenada olvidada*. Y entonces la pregunta barata —y creo que la buena— ya no es
cómo forzarla, sino:

> **¿qué parte de esa ambigüedad la colapsa ya el review agresivo?** Medido: in-degree 1 en el
> **92,7%** de las filas, máximo 3–4 sobre un techo teórico de 7. Eso no es suerte: es el filtro
> haciendo el trabajo. Un teorema de la forma «tras el review agresivo, in-degree > 1 implica *X*»
> sería nuevo, local, y ataca el hueco por donde el algoritmo ya está ganando.

### 5.15 «Tras el review agresivo, in-degree > 1 implica X»: la X, y por qué no puede venir del review

Atacada la pregunta, y tiene dos mitades. La segunda corrige la primera.

#### La X existe, y es local: `ParentMeet`

Releyendo `commonOwner_of_singleParents` se ve que la hipótesis de padre único **solo se usa para
una cosa**: identificar entre sí los testigos que la criba produce. Para cada pick de la cadena por
encima de `lo`, `shared_owner` entrega un owner común un paso por debajo, que por
`owners_below_iff_parents` **es un padre**; `SingleParents` los declara a todos el mismo. La
unicidad nunca hizo falta: hacía falta **elegir una vez, para todos los picks a la vez**.

Eso es un enunciado por nodo, y lo he separado (`Descent.lean`, `[propext, Quot.sound]`):

```
ParentMeet g :=  para todo nodo x con tabla n,  ∃ c ∈ n.parents,
                 todo owner y de x tiene a c en su propia tabla
```

* **`commonOwner_of_parentMeet`** — y basta para `CommonOwner`, **sin la criba y sin `AggOk`**: el
  padre que se encuentran se le entrega directamente a cada pick.
* **`parentMeet_of_singleParents`** — y `SingleParents` lo da gratis; `commonOwner_of_singleParents`
  pasa a ser la composición de los dos, con el mismo enunciado de antes.

Ganancia real: `SingleParents` ⟹ `ParentMeet` ⟹ `CommonOwner` ⟹ veredicto, con la de en medio
**estrictamente más débil que la primera** y, sobre todo, **local**: habla de un nodo y su tabla, no
de cadenas. Es comprobable nodo a nodo, así que se puede medir.

#### Y la X **no** puede salir del review agresivo

Aquí está la corrección, y es la parte que ahorra trabajo. Demostrado
(`parents_never_own_each_other`):

> **dos padres de un mismo nodo nunca se poseen mutuamente** — están en el mismo paso, y un owner en
> el paso propio de un nodo **es** ese nodo (`OOS`).

Y `aggPair` solo dispara sobre un par `(x, w)` con `w` ya en la tabla de `x`. Juntando las dos:

> **ninguna pasada del filtro agresivo compara jamás dos padres del mismo nodo.** La ambigüedad que
> el in-degree mide es **invisible** para las dos patas del review.

Así que la pregunta tal como la formulamos —«tras el review agresivo, in-degree > 1 implica X»— no
puede tener una X sobre el *par de padres* deducida de `AggOk`: el review no mira ahí. Lo que el
review sí hace con el in-degree es bajarlo **indirectamente**, matando nodos por otras razones. Eso
explica el 92,7% medido sin necesidad de un teorema sobre padres.

#### Y tampoco se puede añadir como pata del filtro

La tentación inmediata es convertir `ParentMeet` en un test y añadirlo al barrido: para cada nodo
`n`, si `⋂_y (parents(n) ∩ owners(y)) = ∅`, quitar `n`. El coste sería del mismo orden que el
barrido actual (|owners|×|parents| frente a |owners|²), o sea **polinómico y barato**.

**Pero no es sano.** Si `n` está en un camino real por su padre `c*`, su tabla contiene además
owners que vienen de caminos reales por *otro* padre `c'`, y para esos `y` el conjunto
`parents(n) ∩ owners(y)` puede no contener `c*`. La intersección puede ser vacía con `n` siendo
perfectamente real: el test borraría nodos buenos.

Y la razón es la misma de siempre, dicha una vez más: **la tabla de un nodo es la unión de sus ramas,
y `ParentMeet` es una condición sobre la intersección de toda la tabla.** Separar las ramas para que
la condición sea por rama es exactamente partir el nodo — §5.14, exponencial. La escalera vuelve a
cerrar solo por el extremo caro.

#### Balance del ataque

| | |
|---|---|
| nuevo y utilizable | `ParentMeet`: la hipótesis local exacta que el descenso consume; `SingleParents` es un caso suyo |
| nuevo y negativo | el review agresivo no ve los pares de padres, así que no puede ser la fuente de la X |
| descartado con razón | añadir `ParentMeet` como tercera pata del filtro (no conserva soluciones) |

Lo siguiente que haría, y es barato: **medir `ParentMeet`** con una sonda sobre los estados reales.
Si se cumple siempre, es la hipótesis declarada que yo pondría en lugar de `SingleParents` — más
débil, local, y con el veredicto ya demostrado detrás. Si falla, el contraejemplo es un nodo
concreto con su tabla, que es el objeto más pequeño con el que se ha podido mirar este hueco.
