# `extend_triple`, explorado

> Nota de método: esto es una exploración, no un parte. Lo que hay aquí es una medición
> nueva, una reformulación y tres ángulos de ataque con su valoración honesta. Nada de esto
> está demostrado. Lo que sí está medido lleva el número al lado.

---

## 1. El enunciado, acotado

`Descent.CommonOwner` pide: dada una cadena parcial sana `sel` desde `lo`, un `c` en el paso
`lo-1` que **todos** los picks posean. Tres hechos lo acotan, y los tres son teoremas:

1. `c` tiene que ser owner de `sel lo` un paso por debajo, luego por
   `owners_below_iff_parents` **`c` es un padre de `sel lo`**. El candidato no es un nodo
   cualquiera del paso: es uno de los padres.
2. Por `parents_differ_below`, todos los padres de un nodo **coinciden en `id` y en
   `parent_id`** y difieren solo en `gparent_id`. La ventana fijó dos de los tres componentes.
3. Medido (§5.5 del contexto): **el 92,7 % de los nodos tiene un solo padre**, y el máximo
   observado es **3**.

Con un padre no hay nada que elegir: la consistencia de pares da, para cada pick, un owner
común en `lo-1`, que es un padre, que es *el* padre. Eso es
`commonOwner_of_singleParents`, ya demostrado. **Así que la obligación entera vive en el
7,2 % de los nodos, y allí es elegir 1 de ≤3.**

---

## 2. La medición, y lo que resultó no ser

Dos tests sobre el mismo corpus, con la misma sonda (`lake exe row-degree`):

| test | picks considerados | casos | fallos |
|---|---|---|---|
| sobre-aproximado | **todos** los owners de `x` por encima | 1.457 | **566** (39 %) |
| clique (`tripleAt`) | pares de owners que **se poseen entre sí** | 16.364 | **3** (0,018 %) |

Desglose del segundo, corpus por corpus (barrido completo):

| corpus | grado máx. | casos | fallos |
|---|---|---|---|
| `random 20 3 31337` | 3 | 1.267 | **0** |
| `random 20 4 2026` | **2** | 4.267 | **0** |
| `random 20 4 11` | 4 | 4.229 | 1 — `line 21 key ⟨21,0⟩ step 6` |
| `random 20 4 777` | 4 | 2.765 | 1 — `line 22 key ⟨22,0⟩ step 4` |
| `random 20 4 90210` | 4 | 3.836 | 1 — `line 25 key ⟨25,6⟩ step 6` |
| **total** | | **16.364** | **3** (0,018 %) |

**Una correlación que conviene no sobreleer.** Los tres fallos salen de los tres corpus cuyo
grado de entrada llega a **4**; los dos corpus con grado máximo ≤3 no tienen ninguno. Con
`n = 5` eso es una sugerencia, no un dato — pero es **comprobable** y es exactamente la
frontera que el nombre `extend_triple` insinúa. Si aguantara, el enunciado a demostrar
sería *«con ≤3 padres la terna cierra»*, y el trabajo se movería a acotar el grado.

**Dos lecturas, y la segunda me obliga a corregir la primera versión de esta nota.**

1. **Lo que hace casi todo el trabajo no es la cota ≤3: es que los picks formen un clique.**
   Con owners arbitrarios por encima la obligación falla un 39 % de las veces; exigiendo lo
   que una cadena sana sí cumple —que **se posean mutuamente** (`SoundFrom.owned`)— los
   fallos caen a 1 de cada 4.000. Para la prueba eso significa algo concreto: **hay que usar
   `AggOk` sobre la pareja `(u,w)`**, y el argumento de `extend_pair` no lo hace — solo usa
   `(x,u)` y `(x,w)`. Ahí está el hueco.
2. **Pero el clique no basta.** Hay 3 fallos en 16.364. Así que la terna *tal como la relajé*
   —dos owners cualesquiera de `x`, por encima, que se posean— **es falsa**.

### La pregunta que esto abre, y que no he contestado

Un par `(u,w)` que falla **no es todavía un contraejemplo de `CommonOwner`**. Una cadena
parcial sana tiene mucha más estructura que dos nodos que se poseen: picks en **todos** los
pasos de `lo` a `cs-1`, enlazados por **links de padre**, y **todos** poseyéndose entre sí.
Mi test solo comprueba dos.

Así que de los dos fallos solo se sigue una disyuntiva:

* **o** el par que falla no se extiende a una cadena parcial sana — y entonces mi relajación
  era simplemente demasiado débil, y la estructura que falta (links de padre, un pick por
  paso) es justo lo que la prueba tiene que usar;
* **o** sí se extiende — y entonces **`CommonOwner` es falsa**, y con ella la ruta del
  descenso entera.

Son 3 casos concretos, localizados por línea, clave y paso. Decidir cuál de las dos es
requiere reconstruir esos estados y buscar si el par extiende. **No lo he hecho**: eso ya es
una búsqueda de contraejemplo, y en este repo eso se pregunta antes de lanzarlo.

## 3. La reformulación

Con `x = sel lo` al paso `s`, y dos picks `u`, `w` por encima que se poseen entre sí:

```
A := owners(u) ∩ parents(x)     ≠ ∅   por AggOk sobre (x,u) al paso s-1
B := owners(w) ∩ parents(x)     ≠ ∅   por AggOk sobre (x,w) al paso s-1
                                      y owners(x) al paso s-1 = parents(x)
objetivo:  A ∩ B ≠ ∅
extra sin usar:  owners(u) ∩ owners(w) ≠ ∅ al paso s-1   (AggOk sobre (u,w))
```

Con `|parents(x)| ≤ 3`, que `A ∩ B = ∅` obliga a `c₁ ∈ A∖B` y `c₂ ∈ B∖A`. Y entonces:

* `c₁` posee a `x`, y `x` posee a `w`, pero `c₁` **no** posee a `w`;
* o sea, la criba quitó el par `(c₁, w)`, y quitarlo exige un paso `j` con
  `owners(c₁) ∩ owners(w) = ∅` allí;
* pero `owners(c₁) ∩ owners(x) ≠ ∅` en todo paso, y `owners(x) ∩ owners(w) ≠ ∅` en todo paso.

**Conclusión, y es lo más útil de esta nota:**

> `extend_triple` falla en `x` **solo si** queda una violación de Helly en una terna que
> contiene a `x` **y a un padre suyo**.

Eso no es *"Helly falla"* —que sí pasa: 52.720 de 380.746 ternas ordenadas incumplen la
transitividad— sino *"Helly falla en una configuración muy concreta"*. Y la medición dice
que esa configuración **no se da**: 0 de 1.267.

---

## 3bis. La caza, y lo que enseñó

Con la relajación falsa, la pregunta pasó a ser: **¿esos pares se realizan como picks de una
cadena parcial sana?** El test es exacto, y la razón de que lo sea merece escribirse:

> si existiera una cadena sana desde el paso `s-1` pasando por `x`, `u` y `w`, su pick en
> `s-1` sería un **padre de `x`** (link de padre) que **posee a todos los picks** (posesión
> mutua) — justo lo que el fallo dice que no existe.

Así que buscar la cadena decide la disyuntiva. `chainThrough` la busca hacia arriba desde `x`:
picks enlazados por `sons`, todos poseyéndose entre sí, todos owners globales, forzando `u` y
`w` en sus pasos.

**Resultado (semilla 777, el primero resuelto):** `x@4, u@6, w@12` → **no hay cadena**, con
presupuesto sobrante (no es un indeciso). El par no es realizable. `CommonOwner` sobrevive.

### Lo que sale de ahí, y creo que es lo más útil de toda la nota

Si el par que falla no se realiza, lo que falta en mi relajación es **la contigüidad**: una
cadena tiene picks en *todos* los pasos, enlazados por links de padre. Y con eso el problema
se reordena entero:

```
A_k := { c ∈ parents(x) : c ∈ owners(sel k) }     el objetivo es  ⋂ₖ A_k ≠ ∅
```

**Al nacer, `A_k` es creciente en `k`.** Por `mem_rowOwners_iff`, los owners de un nodo de
fila son los de **sus padres** cortados contra `gowners`, más él mismo. Como `sel k` es padre
de `sel (k+1)`:

> `c ∈ owners(sel k)` y `c ∈ gowners`  ⟹  `c ∈ owners(sel (k+1))`.

Y `A_lo = parents(x)` entero, porque todo padre posee a su hijo. Luego **⋂ₖ A_k = parents(x) ≠ ∅
en el momento del nacimiento**: `CommonOwner` es *trivialmente cierta* recién construido el
estado.

**Todo el contenido está en las eliminaciones de la revisión.** Eso reencuadra el problema:
deja de ser un enunciado de Helly sobre tablas y pasa a ser un enunciado de **preservación**,
que es el idioma en el que este repo demuestra todo lo demás:

1. `CommonOwner (addNode g d t)` — el caso de nacimiento, por la monotonía de arriba;
2. `CommonOwner` se conserva por `filterRequire`, `review`, `reviewAgg` y `join`.

(2) es lo difícil, pero es hermana de `ChainSound_reviewAgg` —*la criba no pierde ninguna
cadena sana*, ya demostrada— con «cadena completa» sustituido por «cadena parcial más su
extensión». La única dependencia lateral es `Ownership.NodesAreGowners` (*todo nodo es owner
global*), medida sin violaciones sobre 259.187 nodos y no demostrada.

## 4. Cuatro ángulos, valorados

### (0) Nacimiento + preservación — **el que yo intentaría ahora**

El del §3bis. Es el único que no pelea contra Helly: usa que la obligación nace cierta y
pregunta qué la rompe. Encaja con cómo está demostrado todo lo demás del repo, y el caso de
nacimiento ya está escrito en `mem_rowOwners_iff`.

**Riesgo honesto:** la preservación bajo `reviewAgg` es exactamente donde vive la dificultad,
y no sé si es más fácil ahí que en la forma de Helly. Pero al menos es una inducción sobre las
operaciones de la máquina, no una propiedad estática de las tablas.


### (A) Cerrar la terna usando `AggOk` sobre `(u,w)`

Es el único que la medición señala directamente. El testigo `z ∈ owners(u) ∩ owners(w)` al
paso `s-1` existe y **no se usa**. Si se demostrara que `z` es padre de `x`, se acaba.

Y hay un camino: `z` y `x` están en pasos **adyacentes**, así que
`AdjacentOwners.owners_above_iff_sons` dice que `x ∈ owners(z)` ⟺ `x` es hijo de `z` ⟺
`z` es padre de `x`. O sea el objetivo se reescribe como:

> el owner común de `u` y `w` al paso `s-1`, ¿posee a `x`?

que es una pregunta sobre **dos pasos contiguos**, no sobre toda la cadena. Es el enunciado
más pequeño al que he sabido reducirlo.

**Riesgo honesto:** `z` podría estar en otra rama y poseer a `u` y `w` sin tener nada que
ver con `x`. Nada de lo que he leído lo impide, y los 3 fallos del §2 son exactamente eso
pasando. Así que este ángulo **no puede cerrarse solo con el clique**: necesita además la
estructura de cadena (links de padre, un pick por paso) que mi test no impuso.

### (B) Descender solo por las aristas de requisito

`SoundFrom` exige posesión entre **todos** los pares de picks. El decodificador no necesita
tanto: `MapChain.reqSatisfying_of_pairwiseOwned` consume `PairwiseOwned` **únicamente** en
los pares `(req.step, k)` con `req ∈ reqOf (sel k).id`. Y en este mapa eso es:

* paso de negación `2v+1` → un requisito, a distancia 1;
* paso de cláusula → **tres** requisitos, en los pasos de sus literales.

O sea **≤3 aristas por pick**, no todas las parejas. La obligación del descenso pasaría a
estar indexada por el **hipergrafo variable-cláusula de la fórmula**, no por el prefijo
entero: en el paso `s-1` solo la reclaman el nodo de negación de arriba y las cláusulas que
mencionan esa variable.

Eso conecta con la anchura inducida, que es el parámetro clásico para exactamente esto
(*k-consistencia basta cuando la anchura ≤ k*), y el repo **ya tiene la maquinaria**:
`CnfHypergraph.lean`, `HyperProbe.lean`, `lake exe width`.

**Coste honesto:** el número de restricciones simultáneas pasa a ser `1 + ocurrencias(v)`,
que en 3-SAT al umbral ronda 12, no 3. Así que esto no acota por 3 — **acota por un
parámetro de la fórmula**, que es otra cosa y puede que mejor: da una clase con nombre
clásico en vez de una propiedad del grafo de caminos.

### (C) Pedir menos: una rama, no todas

`NoDeadEnd` dice *«toda cadena parcial extiende»*. El veredicto solo necesita *«alguna
cadena llega abajo»*. Con la cota ≤3, el árbol de búsqueda del descenso tiene factor de
ramificación **1 en el 92,7 % de los pasos y ≤3 en el resto**: es un árbol delgado. Un
descenso **con backtracking** solo necesitaría que quede una hoja a profundidad `cs`.

**Coste honesto:** delgado no es trivial; `3^(0,072·cs)` sigue siendo exponencial en el
peor caso, y una prueba necesitaría un invariante que sobreviva al backtracking. Lo apunto
porque es el único ángulo que **debilita el enunciado** en vez de fortalecer la prueba, y
porque `ReaderExec` ya descarta backtracking por diseño — habría que saber si es una
decisión revisable o un compromiso.

---

## 5. Lo que mediría antes de decidir

1. **Los tres fallos del §2**, antes que nada: ¿el par extiende a una cadena parcial sana?
   Es la disyuntiva del §2 y decide si la ruta D sigue viva. Es una búsqueda de
   contraejemplo, así que se pregunta antes.
2. **Instancias estructuradas.** El contraejemplo de Helly de v114 vivía en Tseitin sobre
   Petersen. *(Corriendo.)*
3. **El grado 4.** Si los fallos solo aparecen con grado ≥4, eso es un enunciado con
   nombre y una frontera clara. Es la medición más barata de las cuatro: basta filtrar el
   test por `n.parents.length ≤ 3` y ver si los fallos desaparecen.
4. **Los testigos `z`.** Cuando hay ≥2 padres, ¿el owner común de `u` y `w` al paso `s-1`
   **es** siempre uno de los padres de `x`? Eso mide directamente el ángulo (A), y es una
   línea más en la sonda.
5. **`1 + ocurrencias(v)` real** por instancia, para saber si el ángulo (B) acota una clase
   interesante o una vacía.

## 6. Lo que no haría

Atacar `SpcSupport.SpcStable` (§5.7 del contexto): es la más global de las seis familias y
la única a la que la ventana no le aporta nada, porque `Spc` recorre parejas arbitrarias y
no enlaces de padre. Cualquier avance en (A) o (B) la deja mejor colocada; al revés no.
