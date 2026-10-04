# Verificación para el Autor v139: la máquina como oráculo comprimido, y la propiedad que falta

Ricardo, soy Claude (Opus 5). Este informe recoge todo lo hecho desde v138 y termina con lo que pediste
expresamente: una exploración del **proceso de review** y del **mapa**, buscando la propiedad que haría
demostrable lo único que queda abierto.

Resumen en cuatro frases:

1. **Tu lectura está confirmada**: cada estado de la máquina es, tabla a tabla, **exactamente la unión de
   los caminos del oráculo** (la fuerza bruta) que llegan a su clave. 0 diferencias en todas las familias.
2. **Demostrado sin hipótesis**: si un solo camino del oráculo sobrevive por sí mismo, φ es satisfacible;
   y **toda entrada que sobrevive al review está en una cadena enlazada completa** (el contenido
   constructivo del review).
3. **Lo único abierto** es `FilterSound`: tras fijar un paso y revisar, las tablas siguen siendo exactas.
   Se cumple en **todas** las medidas (21.709 fijaciones arbitrarias), pero **todas** las formas locales
   o estáticas de enunciarlo que probé son falsas: solo es cierta la afirmación global.
4. La exploración del mapa sugiere una hipótesis concreta y **falsable** sobre la propiedad que falta:
   una propiedad de **anchura** de la fórmula respecto a lo que cada nodo lleva en su identidad (§6).

Rama `spaik`, build de `AbsSat` (198 jobs), sin `sorry`, `[propext, Quot.sound]` en todos los teoremas
nuevos. Commits desde v138: `7fe4ce3` … `8220574`.

---

## 1. De `ReviewJoin` a la cobertura de apoyos (demostrado)

v138 dejó el veredicto bajo `ReviewJoin` (revisar una unión cabe en la unión de lo revisado). El paso
siguiente fue usar la teoría de punto fijo que el proyecto ya tenía: un **conjunto de apoyo** (`Sup`)
dentro de un estado sobrevive a su review (`AOk_filterAllAgg`).

`SupportSplit.lean`:

* **`reviewJoin_of_split`** — si las entradas del review de la unión se cubren con un apoyo dentro de
  cada lado, `ReviewJoin` se cumple (cada apoyo sobrevive al review de su lado).
* **`sup_greatest`** — la unión de todos los apoyos dentro de un estado es un apoyo. Por tanto el mejor
  reparto es el **mayor apoyo** de cada lado, y lo único que queda es **`SupportCover`**: *toda entrada
  del review de la unión está en un apoyo de uno de los lados*. Es "no hay préstamo" en su forma exacta
  (`sat_of_cover`).

**Un reparto concreto, y dónde falla.** Repartir por el testigo del paso alto (`PartSplit`) cumple todas
las condiciones en las uniones del driver (0 fallos en 1,77 M entradas), pero **falla** en las uniones de
trozos que hace la prueba (`split_branch`): ahí dos lados pueden compartir el nodo alto, porque sus
historias se separan más abajo. Anclar en el **paso de separación** (el más alto donde ningún nodo es de
los dos lados) arregla K4 por completo (0 fallos en 2,1 M entradas de uniones de trozos). La
**dominancia del ancla** (que la tabla del ancla contenga todo lo anclado) está **refutada** (22 % de
fallos en paridad).

## 2. La máquina es el oráculo comprimido (medido y demostrado)

Tu intuición: la abstracción comprime, pero lo que se construye es el conjunto de caminos que la fuerza
bruta comprobaría uno a uno. La sonda `helly oracle` compara cada estado de la máquina con la unión de
los estados **de un solo camino** (un nodo de mapa fijado en cada paso) que llegan a su clave:

| familia | estados | caminos individuales | iguales tabla a tabla |
|---|---|---|---|
| Tseitin K4 | 108 | 664 | **108** |
| paridad k3 | 81 | 4.726 | **81** |
| Tseitin prisma / K3,3 | 164 / 164 | 5.364 / 5.364 | **164 / 164** |
| Tseitin cubo | 220 | 42.988 | **220** |
| Tseitin sobre grafos 3-regulares aleatorios (6 vértices, dos semillas; 8 vértices) | 164 / 164; 220 | 5.364 / 5.364; 42.988 | **164 / 164; 220** |
| aleatorias, semillas 1001 / 2002 | 4.066 / 3.966 | 43.231 / 42.507 | **4.066 / 3.966** |

Nunca falta un camino y nunca sobra una entrada. Formalmente (`OraclePath.lean`):

* **`sat_of_oracle_path`** — **sin hipótesis**: si la ejecución restringida a **un** camino del oráculo
  llega válida a la clave final, φ es satisfacible (con todos los pasos fijados no queda elección y el
  lector lee ese camino).
* **`exists_oracle_path`** — bajo la distributividad (v138): un estado final válido contiene un camino
  del oráculo que sobrevive **por sí solo** (es `split_branch` aplicado paso a paso).
* **`sat_of_oracle`** — el veredicto: la máquina solo dice SAT si uno de los caminos de la fuerza bruta
  sobrevive por sí mismo.

**Las dos inclusiones.** "La máquina = el oráculo" son dos afirmaciones:

| dirección | significado | estado |
|---|---|---|
| máquina ⊇ oráculo | ningún camino válido se pierde | **demostrado sin hipótesis** |
| máquina ⊆ oráculo | la compresión no añade caminos | medido sin excepción; **abierto** |

## 3. El lema de las uniones de caminos: cuándo es cierto

La segunda inclusión, paso a paso, dice: *el review de una unión de caminos, tras fijaciones unarias,
conserva exactamente los caminos que pasan las fijaciones*. Lo probé sobre conjuntos generados al azar
(sondas `pathunion`, `pathunionrec`, `pathcsp`):

| conjunto de caminos | review tras fijar |
|---|---|
| unión **arbitraria** | **falla** a partir de 6 pasos (mínimo: anchura 2, 3 caminos); a veces queda válida sin ningún camino superviviente |
| unión **cerrada por recombinación** en nodos de mapa compartidos | exacto (0 / 18.116) |
| **todas las soluciones** de requisitos "si en t está y, en i está r" | exacto (0 / 22.486, hasta 13 pasos y anchura 4) |

El contraejemplo mínimo (p1 = 1 0 0 0 1 0, p2 = 0 0 0 0 0 0, p3 = 0 0 1 0 1 0, fijación "paso 2 = 0")
enseña el mecanismo: el nodo que comparten p1 y p3 en el paso 4 guarda el pasado de p3, que muere, pero
ese pasado sigue vivo gracias a p2. Y enseña también por qué en tu máquina no pasa: allí ese nodo nace
**una sola vez**, del estado que contiene **todos** los prefijos que llegan a su clave. La recombinación
p2[..3] + p1[4..] es entonces un camino vivo que contiene la entrada "espuria". **El review por pares
calcula el cierre por recombinación.**

## 4. El ataque a `FilterSound`

`TablesSound` (v135) está cerrado para semilla, UP y unión; falta el filtro. Lo ataqué de frente.

**Demostrado** (`LinkedChain.lean`):

* **`entry_on_linked_chain`** — toda entrada (x, v) de un estado revisado está en una **cadena enlazada**
  padre-hijo que cubre todos los pasos y pasa por x y por v, y cuyos nodos poseen todos v. Se construye
  siguiendo las condiciones `par` (hacia abajo) y `son` (hacia arriba) del review; en el paso de v, el
  nodo de la cadena **es** v porque un nodo solo se posee a sí mismo en su propio paso (`OOS`).

**Medido, exacto sin excepción** (sonda `pinexact`): fijando **cualquier** nodo de mapa sobre estados
exactos —no solo los requisitos reales— y revisando, el resultado es exactamente la unión de las
soluciones que pasan por él:

| familia | fijaciones | exactas |
|---|---|---|
| K4 | 2.943 | 2.943 |
| paridad k3 | 2.380 | 2.380 |
| Tseitin 3-regular aleatorio, 6 vértices (dos semillas) | 8.193 + 8.193 | todas |

**Refutado** — cada forma local o estática de `FilterSound` que probé:

| enunciado | medida |
|---|---|
| toda cadena enlazada de un estado revisado es un camino | falla: 2.532 de 3.196 en K4 (las 664 válidas son **exactamente** los caminos del oráculo) |
| Helly-3: tres nodos compatibles por pares están en un camino | falla: 14.504 de 1,9 M en K4; 7.084 de 3,8 M en paridad |
| la rebanada es cerrada por enlaces (cadena enlazada con todos sus nodos poseyendo v ⟹ camino) | falla: 7.168 de 16.970 en K4 |

**Cómo lo consigue el review** (sonda `why`, 300 contraejemplos de Helly-3 con la fijación aplicada): x y
v **sobreviven siempre**, los dos enlazados con la fijación; lo único que el review borra es **la entrada**
(x, v), en cascada a lo largo de los enlaces. Es decir: el review no decide por nodos, sino por **pares a
lo largo de cadenas**, y lo que queda posee v en el estado **ya revisado**, una relación mucho más
estrecha que la del estado de antes. Por eso ninguna propiedad estática del estado de antes lo captura.

## 5. Cómo queda todo

| afirmación | estado |
|---|---|
| UNSAT: ejecución vacía ⟹ φ insatisfacible | demostrado sin hipótesis |
| SAT con camino; un camino del oráculo superviviente ⟹ SAT | demostrado sin hipótesis |
| toda entrada revisada está en una cadena enlazada | **demostrado sin hipótesis (nuevo)** |
| estado final válido ⟹ φ satisfacible | demostrado bajo la distributividad (`SendDistrib`/`ReviewDistrib`), o bajo `SupportCover`, o bajo `CommonOwner` |
| `FilterSound` (el filtro conserva la exactitud) | **medido sin excepción; abierto** |

Todas las hipótesis abiertas son la misma cosa vista desde sitios distintos: **la compresión no añade
caminos**. Y ya sabemos que eso **no** es una propiedad del review sobre cualquier conjunto (§3): depende
de cómo tu máquina construye sus conjuntos.

## 6. Exploración: el proceso de review, el mapa, y la propiedad que falta

### 6.1 Qué es un camino del mapa

El mapa de φ con n variables y m cláusulas tiene 2n + m + 2 pasos:

| paso | nodos | requisitos |
|---|---|---|
| 2v | "v = 0", "v = 1" | ninguno |
| 2v + 1 | "¬v = i" | exige "v = 1 − i" en el paso 2v |
| 2n | nodo de fusión | — |
| 2n + 1 + j | siete filas r = 4b₁ + 2b₂ + b₃ (las siete asignaciones que satisfacen la cláusula j) | cada fila exige un nodo concreto en el paso de cada uno de sus tres literales |
| 2n + 1 + m | nodo de fusión | — |

Consecuencia importante: **un camino está determinado por su tramo de variables**. Las filas de cláusula
son funciones de la asignación. Así que los caminos válidos son, uno a uno, **las asignaciones que
satisfacen φ** (lo que ya usan `CnfChain.decode` y `selOfAssign`), y el conjunto de caminos de un estado es
un conjunto de asignaciones.

### 6.2 Qué guardan las tablas

Con esa lectura, las tablas tienen un significado muy concreto:

* un nodo de variable lleva **1 variable**; un nodo de cláusula lleva **3**;
* pero la identidad de un nodo es **(nodo de mapa, nodo de mapa del padre)**: un nodo de cláusula lleva la
  fila de su cláusula **y** la de la anterior, hasta **6 variables**;
* una entrada de tabla empareja dos nodos: es una **marginal conjunta de hasta 12 variables** del conjunto
  de soluciones.

Es decir: la máquina no guarda compatibilidades de pares de variables, sino **marginales sobre ventanas de
variables** determinadas por el orden de las cláusulas. Esto explica por qué es mucho más fuerte que la
consistencia por pares clásica, y por qué la identidad (destino, origen) es tan importante: **cada nodo es
una ventana de dos cláusulas consecutivas**.

### 6.3 Qué hace el review

* La coherencia con padres y con hijos (`reviewParents`, `reviewSons`) es, en términos de bases de datos,
  un **programa de semijoins a lo largo del orden de los pasos**: la tabla de un nodo se recorta a lo que
  sus vecinos admiten.
* El barrido agresivo (`sharesEveryStep`) exige que dos owners compartan un testigo **en cada paso**: es
  consistencia de caminos a través de cada tercer paso.
* La traza de §4 dice cómo actúa tras una fijación: **conserva los nodos y borra pares en cascada** a lo
  largo de los enlaces.

### 6.4 Propiedades candidatas, y su estado

| propiedad candidata | la explicaría | estado |
|---|---|---|
| **cierre por recombinación** del conjunto de caminos | sí, sin requisitos cruzados (§3) | falsa en la máquina: los requisitos de cláusula cruzan pasos |
| **cierre por mayoría** del conjunto de soluciones (teorema de Jeavons–Cohen–Cooper: con un polimorfismo de mayoría, la consistencia local es exacta) | sí | **no** explica tus datos: las soluciones de paridad son espacios afines, cerrados por x ⊕ y ⊕ z pero no por mayoría, y la máquina es exacta en paridad |
| Helly-3 en estados exactos | sí | refutada |
| rebanada cerrada por enlaces | sí | refutada |
| **anchura** (abajo) | sí | **hipótesis abierta, falsable** |

### 6.5 La hipótesis: anchura respecto a las ventanas de la máquina

En teoría de bases de datos hay un resultado clásico (Yannakakis): un programa de semijoins es **exacto**
—deja solo tuplas que están en alguna solución— cuando la estructura se descompone en un árbol cuyos
"separadores" están cubiertos por las relaciones que se guardan. Cuando no se descompone así, la
propagación local puede dejar basura, y eso es exactamente lo que hacen las uniones arbitrarias de §3.

Tu máquina guarda marginales sobre ventanas de hasta 12 variables ordenadas por las cláusulas (§6.2).
Eso sugiere esta hipótesis:

> **La exactitud del review tras una fijación se cumple cuando las dependencias de la fórmula a través de
> cada corte del orden de pasos caben en lo que guardan dos nodos** (una medida de anchura de φ respecto al
> orden de sus cláusulas).

Es coherente con todo lo medido: todas las instancias probadas tienen anchura pequeña (K4, K3,3, prisma,
cubo, Petersen y los grafos 3-regulares aleatorios de hasta 12 vértices). Y es **falsable**:

* **predicción**: en fórmulas de Tseitin sobre grafos bien conectados (expansores) de tamaño creciente, la
  anchura crece con el número de vértices, y en algún tamaño la exactitud debería **fallar**;
* **si nunca falla**, la hipótesis es falsa y la propiedad que falta es otra, más fuerte y más
  interesante: habría que buscarla en cómo el UP crea cada nodo con **todos** los owners globales del
  estado (tu observación de hoy), que hace que cada tabla nazca como el estado entero y no como pares.

### 6.6 Qué formalizar en cada caso

* **Si la hipótesis de anchura se confirma**: `FilterSound` es demostrable **para la clase de fórmulas de
  anchura acotada** respecto a las ventanas, con un argumento de tipo Yannakakis sobre el orden de pasos.
  Sería un teorema de corrección para una clase amplia y bien definida.
* **Si no se confirma**: la propiedad está en la construcción, no en la fórmula, y el invariante a
  formalizar es el de **rebanadas** (la tabla de cada nodo es exactamente el conjunto de nodos de los caminos
  que pasan por él), cierto al nacer cada nodo por construcción del UP. Habría que demostrar que el review
  tras una fijación lo conserva, razonando sobre la cascada de §4 y no sobre propiedades estáticas.

## 7. Próximos pasos

1. **Terminar la batería de Tseitin sobre grafos 3-regulares aleatorios** (8, 10 y 12 vértices, en marcha)
   y ampliarla a 16, 20 y más vértices, que es donde la hipótesis de anchura predice fallos.
2. Medir una **anchura** concreta de cada instancia respecto al orden de sus cláusulas, para poder cruzarla
   con los resultados.
3. Según salga 1–2, formalizar la versión de §6.6 que corresponda.

## 8. Artefactos

* Lean: `SupportSplit.lean` (reparto, mayor apoyo, `SupportCover`, reparto en el paso de separación),
  `OraclePath.lean` (el oráculo), `LinkedChain.lean` (cadena enlazada).
* Sondas (`Probes/Helly.lean`): `split`, `pieces`, `oracle`, `pathunion`, `pathunionrec`, `pathcsp`,
  `linked`, `helly3`, `pinexact`, `why`, `sliceclosed`.
* Instancias: `Probes/cnf/tseitin_rr/` (Tseitin satisfacibles sobre grafos 3-regulares aleatorios).
