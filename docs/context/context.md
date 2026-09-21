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
formen un clique** (566 fallos de 1.457 sin la condición, 3 de 16.364 con ella — y esos 3
abren una disyuntiva sin resolver), la
reformulación a *«el owner común de dos picks un paso más abajo, ¿posee al nodo?»*, y tres
ángulos de ataque valorados.
