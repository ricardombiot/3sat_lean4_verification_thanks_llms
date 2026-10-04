# Verificación para el Autor v175: el lector no añade nada al problema, y dónde vive cada nivel de consistencia

Ricardo, soy Claude (Opus 5). Esta sesión no produjo un teorema grande como la anterior. Produjo
algo distinto y, creo, más útil: **el frente encogió cinco veces seguidas**, y al final se ve con
precisión en qué escalón vive cada pieza del problema. También se cayó una hipótesis —la tuya sobre
los ancestros— y el diagnóstico de por qué se cae resultó ser un acierto del diseño, no un fallo.

Rama `spaik-window3`. `lake build AbsSat` verde (236 jobs), `lake exe runTests` verde, sin `sorry`.
Todos los cierres `[propext, Quot.sound]`.

Commits: `8ebdf5b`, `03c1d75`, `f25d117`, `1ee54d3`, `6f7f0b1`, `8217351`, `e6aa171`.

---

## 0. Resumen

* **El resultado**: el lector sin retroceso es completo desde `TablesSound` —uno de los dos
  invariantes que se miden al 100%—, y su propagación por la lectura se parte en dos, con el paso
  pinchado **demostrado** y el resto aislado.
* **La estructura, que es lo que de verdad salió**:
  `singles ← pares ← tríos`. El lector necesita singles. Propagar el invariante del autor pide
  pares. Propagar pares pide tríos. **El muro está enteramente del lado de la corrida, no de la
  lectura.**
* **Tu frase sobre los ancestros**: demostrada para el `up` (`ancOwned_addNode`), medida falsa tras
  el `doJoin` — y la razón es que el `doJoin` está bien y el enunciado pedía de más.
* **El frente encogió así**: `SupportedS` → `ChainPairwise` → `PinReachable` → `TablesSound` →
  `PinPairSound` → `RootPinChained`, y este último **cerrado**.
* **Sondas nuevas**: `anc`, `anc-all`, `anc4`, `pinreach`, `tsread`, `roots`, `roots-all`.
* **Sección 6**: cómo usaré el nodo de fusión inicial cuando lo tengamos.

---

## 1. Tu frase sobre los ancestros: cierta en el `up`, falsa tras el `doJoin`

Lo dijiste así:

> *cuando se construye un nuevo nodo se le da la compatibilidad con todos sus ancestros, siendo sus
> owners la unión de los de sus padres*

La escribí como invariante y la usé:

```lean
inductive Anc (g : GPathM) : PathNodeId → PathNodeId → Prop
def AncOwned (g : GPathM) : Prop :=
  ∀ y n, g.node? y = some n → ∀ a, Anc g y a → a ∈ n.owners
```

Y el pago era grande: `pairwiseOwned_of_ancOwned` cierra **entero** el residuo de la ruta B. Una
cadena enlazada es un camino de ancestros, así que sus nodos se poseen entre sí —hacia abajo por
`AncOwned`, hacia arriba por la simetría de owners—, y de ahí sale `SupportedS`.

**Y el `up` la cumple, demostrado**: `ancOwned_addNode`. La prueba es literalmente `rowOwners` —la
fila hereda entera la tabla de cada padre, recortada a `gowners`, y el recorte no estorba porque un
owner en rango es owner global (`ownGow`)—.

### 1.1 Pero la medida

Sonda `row-degree anc4`, cuatro fotos por envío, 918 envíos sobre 6 fórmulas:

| foto | ancestros fuera de la tabla |
|---|---|
| 1. estado de partida | 13.0% (arrastrado de joins previos) |
| 2. tras filtro + criba | **4.2%** — la revisión *mejora*; 0/918 envíos empeoran |
| 3. tras `addNode` (el up) | 4.3% — solo propaga lo que recibe |
| 4. **tras `doJoin`** | **22.8%** — 259 de 375 joins crean ancestros sin tabla |
| 5. join + `reviewAgg` | 22.8% — la revisión no repara nada |
| 6. join + tabla reconstruida | 6.3% |

El barrido de padres e hijos —que sospechaste que faltaba— **sí está** en `review`
(`reviewParents` / `reviewSons` con `unlinkIncompatible`). Lo que pasa es que **interseca**: solo
quita. Lo que falta tras un join habría que añadirlo, y ninguna criba de esa forma puede hacerlo.

### 1.2 Y tú tenías razón sobre la unión

Propuse que `doJoin` reconstruyera la tabla del nodo fusionado como la construye el `up`. Lo
mediste mentalmente antes que yo:

> *hacemos la unión entre los conjuntos según se han ido construyendo en la máquina… esas
> diferencias entre las tablas son precisamente las que nos permiten contener todas las soluciones
> SAT en la estructura de datos*

Es exacto, y la medida lo dice igual. **No hay fallo en la unión.** Tras fusionar, el enlace
padre-hijo sobre-aproxima —junta procedencias— mientras la tabla sigue siendo exacta —guarda cada
procedencia como se construyó—. Un «ancestro» por enlaces ya no es un ancestro forzado, así que
pedir que esté en la tabla es pedir de más; y ponerlo ahí borraría justo la información que sostiene
las soluciones. Retiré la sugerencia.

**Lección de encuadre**: la relación de padre-hijo es más gruesa que la tabla. Cualquier enunciado
que razone por enlaces en vez de por tablas hereda esa sobre-aproximación. `AncOwned` fue la sexta
hipótesis caída de la serie, y la primera que cae por una razón que es una virtud del diseño.

---

## 2. El frente estaba mal dimensionado

Fui a leer qué pide exactamente `ReaderExec.progressAgg_of_chains`, que es el teorema que conecta
con el veredicto:

```
∀ g, ReadFrom g₀ g → isValid g = true → ∃ sel, ChainSound g sel
```

**Una** cadena por estado. No una por nodo. `SupportedS` —y con ella `ChainPairwise`, y con ella
`AncOwned`— daban una cadena **por cada nodo de cada estado**. Sobraba casi todo.

`ReaderChain.lean` escribe la escalera con la cima mínima:

* `HasChain g` — `∃ sel, ChainSound g sel`;
* `PinKeepsChain` — el residuo: **un estado, un pin**;
* `hasChain_readFrom`, `progressAgg_of_pinKeepsChain`, `readerVerdictW_of_pinKeepsChain`;
* `PinReachable` y `pinKeepsChain_of_pinReachable` — el review no estorba
  (`ChainSound_filterAllAgg` lleva la cadena al otro lado entera);
* `hasChain_of_supportedS` — cuánto sobraba, escrito.

Medido (`row-degree pinreach`, trayectoria real del lector): **86 pines válidos, 86 con cadena
completa por ellos, 0 contraejemplos, 0 indecisos**. Muestra pequeña —buscar la cadena es caro— pero
sin excepción, y el 100% de los candidatos dejaban el grafo válido, que es la otra cara de que el
retroceso nunca haga falta.

---

## 3. `realizes_pin` usaba `LitStep` en un solo sitio

`RunSteps.realizes_pin` estaba demostrado y mencionaba el bloque literal **una vez**: para alimentar
el predicado de `SoundAt`. Nada más de la prueba mira los pasos literales.

Generalizado a un predicado cualquiera (`realizes_pin_gen`, misma prueba; `realizes_pin` queda como
corolario), con `TablesSound` el pin puede estar en cualquier paso. Y un pin fuera de rango no pide
nada a la cadena (`hasChain_out_of_range`). Resultado:

```lean
readerVerdictW_of_tablesSound
  (hts : ∀ g, ReadFrom g₀ g → isValid g → TablesSound g)
  (h₀  : HasChain g₀)
  → readerVerdictW φ = true                     [propext, Quot.sound]
```

**El lector sin retroceso es completo suponiendo solo `TablesSound`**, que es uno de los dos
invariantes que se miden sin una sola excepción.

Sonda nueva `row-degree tsread`, que recorre la **trayectoria real del lector** y cuenta *todas* las
entradas:

| corpus | estados de lectura | entradas | fantasmas |
|---|---|---|---|
| 10 fórmulas aleatorias (semilla 1) | 29 | 56.549 | 0 |
| 10 fórmulas aleatorias (semilla 7) | 39 | 92.486 | 0 |
| `dos_de_tres.cnf` | 3 | 1.089 | 0 |
| **total** | **71** | **150.124** | **0** |

---

## 4. La propagación, y el frente unificado

El paso de la inducción es el pin, y se rompe limpio en dos:

* **`tablesSound_pin_of_pairs`** — el paso **pinchado** es gratis. Una entrada al paso del pin
  *lleva* el pin (`ReaderComplete.pin_id`), la entrada ya estaba en un camino, y ese camino pasa por
  el pin. Es la prueba de `RunSteps.pinStep_of_pairs` sin la restricción al bloque literal.
* **`PinPairSound`** — el resto: las entradas hacia pasos **distintos** del pinchado.

Lo que se gana frente a `RunSteps.PinPairSoundAt`: **`PinPairSound` no menciona φ**. Es una frase
sobre un estado de la máquina y un pin. Y las dos rutas de la sesión anterior terminan en el mismo
sitio: la corrida cuelga de `PinPairSoundAt`, el lector de `PinPairSound`. **Un solo frente.**

---

## 5. El trío se deshace: el lector no añade nada

### 5.1 La raíz no es única

Sonda `row-degree roots` / `roots-all`: **dos nodos en el paso 0 en el 20% de los estados de lectura
y el 36% de los de la máquina** (máximo 2). `pureInit` arranca cada semilla de una sola raíz y el
`up` nunca toca el paso 0; el único que mete dos es el `doJoin`, fundiendo estados que vienen de
raíces distintas.

### 5.2 Pero el lector tira la pata de la raíz

`realizes_pin_at` devolvía `Realizes g x w` —una frase sobre **dos** nodos— y quien la consume solo
usa que el estado pinchado tenga *alguna* cadena. `RunSteps.chain_pin_at` pide y entrega solo eso.

Con eso el invariante a propagar pasa a ser **tu frase, literal**:

```lean
def RootChained (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → x.id.step = 0 →
    ∀ w, w ∈ n.owners → 0 ≤ w.id.step → w.id.step < g.current_step →
      ∃ sel, ChainSound g sel ∧ sel w.id.step = w
```

*Todo lo que el nodo del paso 0 posee está en una cadena completa.* Un enunciado sobre **un** nodo.
Y que la raíz no sea única deja de importar, porque su identidad ya no interviene.

### 5.3 Y el residuo se cierra con pares

```lean
rootChained_pin_of_tablesSound : TablesSound g → RootChained (filterAllAgg g [r])
```

La supervivencia al pin da un testigo `z` en el paso pinchado que la raíz y `w` **comparten**
(`shared_pin_witness`, vía `AggOk` del estado pinchado). `TablesSound` del estado de antes da una
cadena por `w` **y por `z`** —un par, no un trío— y esa cadena pasa por el pin porque `z` lleva el
pin. Luego sobrevive a la criba. **No se pega nada**: es justo lo que `ChainMerge` no podía hacer y
aquí no hace falta.

### 5.4 La estructura entera

```
el lector necesita                SINGLES   (HasChain)
propagar RootChained pide         PARES     (TablesSound — medido 100%)
propagar TablesSound pide         TRÍOS     (PinPairSound)   ← el muro
```

**El lector no añade nada al problema abierto de la máquina.** El muro es el mismo de siempre, la
frontera 2-vs-3 donde han caído seis hipótesis, y está enteramente del lado de la corrida.

### 5.5 Lo que esto no hace

No cierra el bucle. La hipótesis sigue siendo `TablesSound` en cada estado de lectura, igual que en
`readerVerdictW_of_tablesSound`. La ganancia es **estructural** —ahora se ve en qué escalón vive
cada nivel de consistencia— no una hipótesis más débil. Conviene no darlo por ganado.

---

## 6. El nodo de fusión inicial: cómo lo usaré

Lo propusiste así:

> *podríamos añadir un nodo adicional en el mapa en el primer paso que fuera de tipo fusión, y así
> lograríamos que el primer paso fuera una fusión de todo el árbol y fuera una raíz única*

Es coherente con el diseño: el mapa **ya** termina en `fusionTop`. Poner el simétrico abajo lo
cierra, y `pureInit` pasa de una semilla por nodo de mapa a **una sola**.

Cuando esté, esto es lo que hago con él, en este orden.

### 6.1 Lo primero: `RootChained` pasa de inclusión a igualdad

Hoy `RootChained` dice *todo lo que la raíz posee está en una cadena*. Con raíz única y simetría de
owners se puede demostrar el recíproco: **toda cadena pasa por la raíz**, luego todo nodo que esté
en una cadena es poseído por ella. Es decir:

> la tabla de la raíz **es** el conjunto de nodos con camino.

Eso convierte tu intuición de siempre —*el review deja solo nodos con camino*— en una **igualdad**
comprobable en un solo sitio, en vez de una inclusión repartida por todas las tablas. Y una igualdad
es mucho mejor sitio desde el que demostrar: da las dos direcciones, y la dirección «⊇» es la que
ahora mismo no tengo por ningún lado.

El lema a escribir es corto y ya sé su forma: `sel 0` es un nodo del paso 0 y, con raíz única, **es**
la raíz; combinado con `OOS` eso fija el pick sin hipótesis.

### 6.2 Lo segundo, y es lo que puede mover el muro

El muro actual es propagar **pares** por un pin, que pide **tríos**. Con la raíz única aparece una
tercera pata gratis en cada par: la raíz misma, que está en toda cadena.

Es decir: el trío `(x, q, r)` que hoy me bloquea se convierte en `(raíz, w, r)` con la primera pata
**forzada**. Y un trío con una pata forzada es un par. Esa es la razón de verdad por la que la
fusión inicial me interesa: no es cosmética, **cambia de qué lado del muro cae la propagación**.

No prometo que cierre. Prometo que es el único movimiento que he visto en dos sesiones que ataca la
frontera 2-vs-3 por la estructura del mapa en vez de por las tablas, y que los demás ataques ya los
he agotado por arriba.

### 6.3 Lo tercero: la simetría con `fusionTop`

Con fusión abajo y fusión arriba, el mapa queda simétrico, y varios lemas que hoy tienen dos formas
—`reviewParents` sobre `intRange 1 (cs-1)` y `reviewSons` sobre `intRange 0 (cs-2)`, con esa
asimetría en el límite inferior que documenta v48— pasan a tener una. No es prioritario, pero abarata
todo lo que venga después.

### 6.4 El coste, dicho claro

`varStep`, `negStep`, `litBlock`, `clauseStep`, `fusionTop`, `stepCount` y `LitStep` desplazan todos
sus índices, y eso atraviesa el repo. Los `#guard_msgs` y los tests de `CnfMap` se van a mover en
bloque. Es una tarde de trabajo mecánico, no un rediseño — pero hay que hacerlo de una vez y con la
batería de tests delante, porque un desplazamiento mal puesto no rompe la compilación, rompe la
semántica.

Mi recomendación: hacerlo, pero **después** de intentar una vez más el muro por 6.2 sobre el papel,
para saber exactamente qué lema quiero escribir cuando el refactor esté hecho. Si el argumento de
la pata forzada no se sostiene ni en papel, el refactor no compra lo importante y solo queda la
limpieza.

---

## 7. Qué hay abierto, con su nombre

| enunciado | dónde | estado |
|---|---|---|
| `ReaderChain.RootPinChained` | lector | **cerrado** con pares (`rootChained_pin_of_tablesSound`) |
| `ReaderChain.PinPairSound` | corrida | abierto — **el muro** |
| `RunSteps.PinPairSoundAt` | corrida | abierto — el mismo muro, con `LitStep` |
| `SupportedRun.TriplePin` | corrida | abierto — el mismo muro, dicho sobre un estado sin pinchar |
| `HasChain` / `TablesSound` en la semilla | corrida | invariantes de la corrida, no del lector |

Las tres primeras son la misma frase vista desde tres sitios. Eso, que suena a mala noticia, es la
buena: **hay un solo agujero.**

---

*Claude Opus 5, con Ricardo M. Biot.*
