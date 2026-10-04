# Verificación para el Autor v131: el invariante de ejecución, y el mapa completo de la demostración

Ricardo, soy Claude (Opus 5). Este informe hace dos cosas: cierra el **invariante de ejecución** que me
pediste —tu par `(destino, origen)` convertido en teorema— y, sobre todo, pone por escrito **dónde está
la demostración entera y qué camino falta**, porque llevamos trece informes y conviene tener el mapa en
una sola página.

Todo en la rama `spaik`, build de `AbsSat` (186 jobs), sin `sorry`, con cierre de axiomas
`[propext, Quot.sound]` en cada teorema citado. Ninguna afirmación de aquí depende de módulos viejos.

---

## 1. El invariante de ejecución: nada se inventa (`RunEnv.lean`)

Tu observación: *un UP queda ligado únicamente a un par (destino, origen); internamente el destino puede
ser el mismo pero unir historias completas distintas*. Y las claves de una línea son únicas
(`PureDriver.key_inj`), así que el nodo `(d, q)` lo crea **un solo** UP, desde el **único** estado con
clave `q`. Formalizado como una **cota por nodo**:

- **`WithinBelow E g`** — toda tabla del estado, en su propio paso o por debajo, cae dentro de la cota
  `E`. Acotar solo el pasado es lo que hace el invariante estable: cada UP añade el nodo nuevo a *todas*
  las tablas, pero queda **por encima**, así que la cota de los nodos viejos no se toca. (Con la cota
  sobre la tabla entera, el invariante crecía en cada paso y se volvía vacuo; ese fue mi primer intento.)
- **`WithinBelow_join`** — una unión mantiene la cota **sin extenderla**. Se apoya en
  `Join.join_owners_source` (nuevo): toda entrada de un nodo unido viene de uno de los dos lados. Es tu
  "el join une historias del mismo destino sin inventar nada", como teorema.
- **`WithinBelow_addNode`** con `bornEnv` y `bornEnv_ne` — un UP extiende la cota **solo** en el nodo que
  crea, y no toca ningún otro. Aquí entra la unicidad de claves: los nacimientos de envíos distintos no
  colisionan.
- El pliegue: `lineWithin_insertPure` → `lineWithin_sendTo` → `lineWithin_sons` → `lineWithin_line` →
  `lineWithin_advance` → `lineWithin_steps`, con la semilla en `lineWithin_init` (cada semilla tiene un
  nodo, que solo se posee a sí mismo).
- **`runWithin_of_wf`** — **incondicional**: para toda φ bien formada, cada línea de la ejecución tiene
  una cota común para todos sus estados. Los hechos de paso que cada envío necesita se sacan del
  `LineInv` que la máquina ya tenía demostrado (`sendsOk_of_lineInv`).

**El pago**, y es el que buscabas: **`shared_tables_common_bound`** — dos estados de la misma línea están
acotados por la **misma** cota, así que para un nodo que comparten, una entrada que uno lleva y el otro no
es una que el otro **podó**, no una que nunca tuvo.

## 2. Recap: las demostraciones que sostienen todo

### 2.1 La dirección cerrada: el veredicto UNSAT es sólido

| resultado | contenido |
|---|---|
| `ConservationImproves.chainSound_alongW` | si φ tiene modelo, la cadena de ese modelo sobrevive a cada filtro débil y al review agresivo |
| `ConservationImproves.isValid_alongW`, `inhabited_alongW` | por tanto el estado que la lleva sigue válido y habitado |
| **`ConservationImproves.pureRunW_ne_nil`** | **si φ es satisfacible, la ejecución no muere**: veredicto vacío ⟹ φ insatisfacible |

Esto está cerrado. El filtro débil y el barrido agresivo —tus dos últimas mejoras— **no pierden
soluciones**, y eso es lo que hace que un "no hay camino" sea de fiar.

### 2.2 Los invariantes de la máquina

| resultado | contenido |
|---|---|
| `ReaderAggRun.MInv` (rctx, mok, tl, rf, back, onMap, smp, pms, sn, own) | todo estado de la ejecución los cumple, y se conservan por semilla, filtro, UP y join |
| `ReaderAggRun.LineInv`, `LineInv_steps` | línea a línea, con claves únicas y el paso correcto |
| `AggFixpoint.aggOk_reviewAgg` | un estado revisado es **punto fijo** del barrido: tablas simétricas y pares consistentes en **todos** los pasos (v121, tu filtro simétrico) |
| `AdjacentOwners.owners_below_iff_parents` / `_above_iff_sons` | los owners del paso contiguo son **exactamente** los padres (o los hijos) |
| `ParentWitness.parents_id_eq` | todo padre de un nodo lleva el nodo de mapa que nombra el ID del propio nodo |
| `RunEnv.runWithin_of_wf` | la cota de este informe |

### 2.3 Las reducciones del veredicto SAT (todas demostradas)

Cada una dice: *si se cumple X, entonces leer un camino implica que φ tiene modelo*. Son puertas
distintas al mismo sitio.

| teorema | condición X |
|---|---|
| `PinExact.sat_of_pinExact` | cada fijación es exacta (no pierde nada de su rebanada) |
| `PinExactSome.sat_of_someSupported` | en cada estado con elección, **alguna** elección tiene soporte |
| `SpcSupport.sat_of_someSpcStable` | ... y ese soporte es estable por pares (v122) |
| `PairChain.sat_of_pairChain` | cada par de owners está sobre una cadena completa (v123) |
| `BranchReader.sat_of_noBorrow` | una rama válida tiene subrama válida en cada paso con elección (v127) |
| `Hereditary.sat_of_hpv` | validez hereditaria de fijaciones (v128) |
| `HereditaryRun.sat_of_joinSplit` | **`JoinsSplit`**: toda unión reparte sus elecciones entre sus dos lados |

Y la inducción sobre la construcción está hecha entera: semilla (`hpv_initSeed`), filtro + review
(`hpv_filter`), UP (`hpv_addNode`), línea y ejecución completas (`lineHPV_steps`). **El único caso que
queda es el `join`.**

### 2.4 Lo demostrado sobre el `join` (v129–v131)

| resultado | contenido |
|---|---|
| `JoinProvenance.slice_of_exclusive_top` | la rebanada de un nodo que un lado **no tiene** está entera en el otro lado; aplicado al paso alto, da el lado de cualquier elección |
| `JoinProvenance.slice_side_of_tops` | si todos los nodos altos de una elección son de un lado, su propia rebanada también |
| `ParentWitness.par_witness_triple` | en un nodo con **un solo** padre, la consistencia de pares entrega el **trío** que la condición de padres necesita |
| `ParentWitness.owners_below_unique` | con un solo padre por nodo, el pasado de un nodo es un **camino único** |
| `PairChain.node_id_of_pin` | en un estado fijado, todos los nodos del paso fijado llevan el nodo de mapa de la fijación |
| `RunEnv.shared_tables_common_bound` | los dos lados de una unión acotan un nodo compartido con la **misma** cota |

## 3. Estado general: lo medido y lo refutado

**Medido sin una sola excepción** (sondas en `lean_project/Probes/`, todas reproducibles):

| hecho medido | volumen |
|---|---|
| las fijaciones son exactas (punto fijo = tablas en cascada) | 19,2 M entradas |
| fijar = construir la rama (conmutación exacta) | 1.725 fijaciones |
| `PairChain`: ningún par de owners sin cadena | todas las líneas y recorridos del lector |
| las uniones no prestan elecciones | 2,5 M elecciones, 2.474 uniones |
| el lado de una elección se lee del paso alto | coincidencia exacta en las dos familias |

**Refutado por medida** (no volver sobre esto):

| ruta | por qué cae |
|---|---|
| relación de soporte estática (v119) | 32 nodos de rebanada perdidos en K4 par |
| cierre de triángulos `SPC` (v122) | estado abstracto de 3 colores en K4 |
| soporte de doble rebanada en el estado base | 2.026 nodos eliminados en `par_k3` |
| `PinExact` en toda fijación con el barrido viejo | fallaba en las fijaciones del paso 0 |
| rebanada del ancla con la relación de owners entera (v130) | 72 / 15.180 (K4), 5.712 / 439.091 (cubo), 592 / 122.050 (K3,3) sin trío |

**El obstáculo, dicho con precisión**: las tablas guardan compatibilidad **por pares**; leer de ahí "existe
un camino" pide un testigo común a **tres** cosas. Y eso no es un defecto de la prueba: si el ID llevara la
cadena completa del padre, cada nodo tendría un solo padre y el trío se cerraría por diseño
(`par_witness_triple`), pero el ID sería un camino y eso es la explosión espacial que tu abstracción evita.
El salto de pares a tríos es **el precio de la abstracción**.

## 4. El camino que falta

Quedan **dos puertas**, y basta cualquiera de las dos. Las dos están medidas como ciertas.

**Puerta A — `JoinsSplit`** (`HereditaryRun`). Es la que está más cerca, porque de sus tres partes dos ya
están:

1. *reparto de nodos*: hecho (`slice_of_exclusive_top`, con el criterio del paso alto);
2. *cobertura*: sale de la consistencia de pares con el nodo alto;
3. *entradas*: **lo que falta**. Hay que llevar el soporte de las tablas de la unión a las del lado. Con
   `shared_tables_common_bound` de este informe, una entrada prestada es una **poda del otro lado**; el
   siguiente paso concreto es usar eso para reconstruir el soporte con las tablas del lado, y medir antes
   las entradas prestadas **dentro de la rebanada** (la única medida del `join` que no he hecho aún).

**Puerta B — `FilterKeepsPairChain`** (`PairChain`). Gracias a `node_id_of_pin` ya está en su forma
limpia: no hay que *dirigir* la cadena por la fijación (una cadena del estado fijado la respeta sola), sino
que la cadena del par **sobreviva** a la fijación. Es tu "no se pierde ninguna solución", par a par — la
misma propiedad que ya está demostrada para la cadena de un modelo (§2.1), pero para un par de owners
cualquiera.

**Mi lectura**: la puerta B es la que encaja con la forma del obstáculo, porque en `PairChain` el testigo
**varía por par** y no hace falta ninguno común. Y hay un puente que no he explorado: la conservación de
§2.1 ya demuestra exactamente eso para la cadena de un modelo; si el argumento se puede repetir con un par
de owners en lugar de una asignación, la puerta B se abre con maquinaria que ya existe.

**Lo que no cambia con nada de esto**: todo lo anterior es sobre el veredicto de *esta* máquina. La
dirección UNSAT está cerrada; la dirección SAT queda a una de esas dos puertas.

---

## 5. Apéndice: el puente de §4 no se sostiene, y hay una puerta más simple

Puse el puente de §4 a trabajar y hay que descartarlo, además de una medida que cierra la puerta A.
Y de paso aparece una puerta mejor. Lo escribo en el orden en que ocurrió.

**El puente de §4 es circular.** El argumento de conservación (§2.1) arranca de una **asignación** —un
objeto semántico que satisface φ— y de ahí saca que su cadena sobrevive a los filtros. Un par de owners
no es un objeto semántico: repetir el argumento con un par pide justo la cadena que se quiere construir.
Refutado por análisis, no por medida.

**La puerta A, medida y refutada.** Faltaba medir las entradas prestadas **dentro de la rebanada**
(`helly slices`): para cada nodo alto exclusivo de un lado, su rebanada en la unión restringida, y cada
par de owners de dentro contra las tablas **de ese lado**. En Tseitin K4 par: 32 uniones, 896
restricciones, 1.229 nodos altos exclusivos, 31.459 nodos de rebanada, 810.999 pares y **1.328 pares
ajenos**. El soporte de la rebanada **sí** usa entradas que el lado no tiene, así que `JoinSplit` no se
cierra por ahí. (Ya lo apuntaba v130: la condición de padres falla en esa rebanada; la medida lo confirma
por el otro lado.)

**La puerta más simple** (`NoDeadEndVerdict.lean`, demostrado, axiomas limpios). Todas las reducciones
de §2.3 hablan de fijaciones, uniones o pares. Esta no:

- **`sat_of_denotS`** — la forma **mínima**: el veredicto es sólido en cuanto el estado del lector
  **denota** un camino. Una sola cadena basta, y decodifica a un modelo. Todo lo demás de §2.3 es una
  manera de producir esa cadena.
- **`sat_of_noDeadEnd`** — y la forma **local** que la da: si el estado del lector **no tiene callejones
  sin salida** (`NoDeadEnd`: toda cadena parcial desde el paso alto se extiende un paso), leer da un
  modelo. Lo demás es gratis: el **ancla del paso alto siempre existe** (`NoDeadEnd.topAnchor_of`, ya
  demostrado) y una cadena que llega al paso 0 es exactamente una cadena `ChainSound`.

Es decir, todo el problema abierto se reduce a: **una cadena parcial de un estado válido se extiende un
paso hacia abajo.** Un estado, un paso, sin cuantificar sobre fijaciones, pares ni uniones. Es tu propia
afirmación —cada nodo está en al menos un camino, y el review es lo que lo mantiene— en su forma más
desnuda.

**El camino, corregido**: no dos puertas, sino esta. `JoinsSplit` y `FilterKeepsPairChain` siguen siendo
suficientes, pero son más fuertes de lo necesario; la obligación mínima es la de arriba, y es la que hay
que atacar o medir.
