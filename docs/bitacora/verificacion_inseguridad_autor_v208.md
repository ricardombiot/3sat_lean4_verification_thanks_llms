# Verificación para el Autor v208: el join, reducido a una sola afirmación, y las vías para demostrarla

Ricardo, este informe sigue al v207 en la misma sesión (29-sept-2026, rama `reader-stuck`). El v207 terminaba con una
única hipótesis, `SecSplitIn`, en los joins. Aquí cuento cómo la llevé a su forma más pequeña, qué quedó **demostrado
sobre el join por primera vez sin hipótesis**, qué dicen los datos sobre el mecanismo, y dónde está exactamente lo que
falta. La última sección, que me pediste, recoge las vías para seguir.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar):
  * `NodeIn` como invariante de toda la máquina salvo el join;
  * la **completitud para toda selección válida**, que generaliza `steps_inv`;
  * **`CliqueSplit`**: toda camarilla de la unión de dos llegadas es camarilla de un lado. Es el primer hecho
    demostrado sobre el join que no es una hipótesis;
  * la equivalencia `NodeSplitIn` ⇔ `NodeIn` de la unión.
* **La única hipótesis del lector** es ahora que **el join conserve `NodeIn`**. Equivale a: *un núcleo no vacío de la
  unión contiene una selección válida*. La completitud da gratis la dirección contraria.
* **Medido:** el mecanismo, con detalle. Las parejas de un solo lado mueren siempre por la regla de parejas. Fijar un
  color dentro de una estructura de la unión deja **exactamente** los nodos con un testigo de ese color, sin
  excepción. Y lo único que no es local aparece en las instancias con tríos muertos.

---

## 1. `NodeIn`: el invariante natural (`NodeIn.lean`, `cdabce4`)

> **`NodeIn g`**: todo nodo de una estructura cerrada de `g` está en una camarilla que vive dentro de ella.

Es más natural que `SecIn`, y más fuerte: dice que nada de lo que una estructura cerrada contiene está fuera de sus
soluciones.
* **Sin hipótesis** lo conservan el filtro, el review, `dirty`, la semilla y la fila nueva. En la fila nueva hay dos
  casos:
  * un nodo viejo: su camarilla dentro de $V$ se alarga con el hijo de su cima, que también está en $V$;
  * un nodo nuevo: la camarilla de su padre, que está en $V$, se alarga con él.
* **El join**, bajo `NodeSplitIn`: todo nodo de una estructura cerrada de la unión está en una estructura cerrada de un
  lado dentro de ella.
* `readerVerdict_iff_of_nodeIn`, y nodo a nodo `readerVerdict_iff_of_nodeColour` (`NodeColour` + `SideEdgesAt`).

Medido (`probe_secin.jl`, 42 instancias, 4 UNSAT): 432 115 nodos de estructuras cerradas al azar, tras el UP y en
las uniones, **todos** en una camarilla dentro de su estructura. `NodeColour`: 169 949 nodos, 0 fallos.

## 2. `CliqueSplit`, demostrado (`CliqueSplit.lean`, `6c1c27b`)

La razón semántica de que las posesiones de un solo lado no formen soluciones de la unión:
1. **Selecciones válidas** (`ValidSel`): lo que la máquina comprueba en un camino. Son ids encadenados por ventanas,
   hijos del mapa, requisitos cumplidos y ninguna ventana prohibida. No hace falta pasar por $\varphi$ ni por
   asignaciones.
2. **Completitud para toda selección válida** (`steps_has_sel`): la línea del paso $t$ lleva cualquier selección
   válida hasta $t$, en la clave de su último nodo. Y la llegada de un remitente que la lleva también la lleva
   (`carried_arrival`).
3. **`MapLinks`**, invariante nuevo demostrado por toda la línea: los enlaces siguen el mapa, y el paso 0 es la raíz.
4. **Una camarilla de un estado es una selección válida** (`validSel_of_carried`).
5. **`cliqueSplit`**: en la unión de las llegadas de dos remitentes a un destino, una camarilla pasa por uno de los dos
   remitentes; por la completitud, su llegada la lleva.

Medido antes (`probe_cliquesplit.jl`): 33 445 camarillas, 0 fallos. Y con esto (`d68be07`): en el join de dos
llegadas, **`NodeSplitIn` ⇔ `NodeIn` de la unión**. La hipótesis del lector es, literalmente, que el join conserve el
invariante.

## 3. El mecanismo, visto de cerca (Julia)

| sonda | qué mide | resultado |
|---|---|---|
| `probe_shared` | posesiones de un solo lado entre nodos compartidos | existen (14 773 y 16 071) pero **nunca** sobreviven a fijar el otro color; SideEdges: 0 fallos en 7,18 millones |
| `probe_shared` | la unión fijada en el color de $e$ **es** $e$ revisado | 5 376 de 5 376 |
| `probe_shared` | `WitnessAgree` (razón local: un testigo común del color ⟹ posesión en el lado) | **falso**, alrededor del 25 % |
| `dump_gonly` (punto de sonda `:pair_bad`) | qué mata a cada pareja de un solo lado | todas, la regla de parejas. **P1**: sin testigo del color en el paso del remitente. **P2**: sin testigo en $e$ por debajo, sostenidas solo por lo que no es de $e$ |
| `probe_onesided` | **`OneSideSupport`** (hay un paso con todos los testigos comunes fuera del lado) | 14 773/0 en un sentido; 20 fallos de 16 071 en el otro, **solo** en `clause_mix*` (tríos muertos), por cascada |
| `probe_exactside` | fijar un color $c$ dentro de $V$ (con review, como el lector) | sobreviven **exactamente** los nodos con testigo de color $c$ en el paso del remitente: 13 800 de 13 800. Aristas: casi (9 de 9 788 con cortes de más) |

Demostrado a partir de la tabla: **`OneSideSupport` ⟹ `SideEdges`** (`sideEdges_of_oneSideSupport`, `68eba7d`). Así,
el lado de las aristas es **local salvo en las instancias con tríos muertos**.

Los tríos muertos, que en el v207 parecían inofensivos, resultan ser justo donde la demostración deja de ser local.

## 4. Dónde está exactamente lo que falta

Probé tres formas y las tres son la misma afirmación:
* **Estructuras** (`NodeIn`): todo nodo de una estructura cerrada está en una camarilla dentro de ella.
* **Colores** (`NodeColour`): un nodo con testigo de un color sobrevive a fijar ese color.
* **Núcleos** (`SecExact`): un núcleo no vacío contiene una selección válida.

Para núcleos, la completitud da la mitad sin hipótesis. Si el núcleo de un lado fijado en $P$ es vacío, no existe
ninguna selección válida por ese color que concuerde con $P$: si existiera, el lado la llevaría. Lo que falta es la
otra mitad **en la unión**:

> **Un núcleo no vacío de la unión de dos llegadas completas contiene una selección válida.**

Es la afirmación central de la máquina: *la consistencia por parejas de estos estados no deja nada fuera de las
soluciones*. Lo demostrado la confina a un solo sitio: la unión de dos estados de un color cada uno, completos y
exactos en sus camarillas. Los datos no la contradicen nunca. Pero no se deduce de nada local: decide la cascada del
review, y los tríos muertos muestran que esa cascada puede tener profundidad.

---

## 5. Las vías siguientes

Las ordeno de la que veo más directa a la más costosa. Para cada una digo qué habría que demostrar, qué hay ya y cuál
es el riesgo.

### Vía A — Descenso bien fundado sobre el apoyo (la cascada)

**Idea.** Los núcleos de los dos lados, levantados a la unión, forman juntos una estructura cerrada. El núcleo de la
unión es la mayor. Lo que tiene de más son parejas de un solo lado. Hay que demostrar que cada una se queda sin apoyo
en algún paso, siguiendo la cascada: primero caen las **P1** (sin testigo del color en el paso del remitente), luego
las **P2** que solo sostenían ellas, y así.

**Qué hay.** El mecanismo medido (`dump_gonly`); `OneSideSupport` ⟹ `SideEdges` para el caso de profundidad 1;
`CliqueSplit`, que dice que esas parejas no están en ninguna camarilla.

**Qué falta.** Una medida que baje en cada paso de la cascada y que excluya los ciclos de parejas que se sostienen
entre sí. En las instancias con tríos muertos hay cadenas más largas, y el testigo que sostiene una pareja es a su vez
de un solo lado. La sonda natural es medir la profundidad máxima de la cascada, y si el paso del testigo que falla
baja siempre (o sube siempre) a lo largo de ella.

**Riesgo.** Que no exista una medida simple. Si hay ciclos que solo rompe el review por su orden de vueltas, la vía se
cierra.

### Vía B — La caracterización exacta por testigo

**Idea.** `probe_exactside` dice, sin excepción: fijar el color $c$ dentro de una estructura cerrada $V$ deja
**exactamente** los nodos con un testigo de color $c$ en el paso del remitente. Una dirección es fácil de demostrar:
tras fijar, el testigo de un nodo en ese paso es de color $c$. La otra, que un nodo con testigo de color $c$ sobrevive,
es el núcleo en su forma más pequeña.

**Qué hay.** Un hecho nuevo y demostrable: **una cima solo posee, en el paso del remitente, a su propio padre**. Así,
la pareja formada por el nodo y su testigo tiene su testigo en la cima, que es un hijo de ese testigo del color $c$. El
nodo está en la **estrella de una cima de color $c$**.

**Qué falta.** Cerrar esa estrella pide un testigo común a tres nodos. Es `StarRestrict`, medido falso en el 4,9 % de
las cimas **para el estado entero**. Pero no se ha medido dentro de un núcleo fijado en un color, que es lo único que
necesitamos aquí. Primer paso: medir `StarRestrict` restringido a los núcleos fijados en $c$.

**Riesgo.** Que también falle ahí. Entonces la estrella no basta y hay que volver a la vía A.

### Vía C — `OneSideSupport` por la historia, y los tríos muertos aparte

**Idea.** `OneSideSupport` vale en un sentido sin excepción (14 773 de 14 773) y en el otro falla solo en las
instancias con tríos muertos. Demostrarlo por la historia de los dos lados daría `SideEdgesAt` sin cascada en todas
las demás fórmulas.

**Qué falta.** Entender la asimetría: por qué falla solo en un sentido. Y encontrar la propiedad de la historia que lo
da. Los dos lados vienen de remitentes distintos, pero comparten ascendencia por debajo del paso del remitente.

**Riesgo.** Que la asimetría sea accidental, y que el lema necesite una forma más débil en los dos sentidos.

### Vía D — Acotar la clase

**Idea.** Todo lo que no es local aparece en las instancias con tríos muertos, y el Helly local funciona cuando cada
clase de color tiene como mucho dos ventanas. Demostrar el veredicto para una clase definida por una condición medible
en el estado (por ejemplo, «sin tríos muertos en los núcleos fijados», o «clases de color de tamaño ≤ 2») sería un
resultado completo para esa clase.

**Qué hay.** Toda la cadena demostrada. Solo cambiaría la hipótesis del join, y dentro de la clase podría ser
demostrable localmente con las vías B y C.

**Riesgo.** Que la condición no se pueda comprobar en tiempo razonable, o que la clase sea demasiado pequeña para
interesar. Lo medido: clases de 3 o 4 ventanas aparecen ya en instancias de 5 variables.

### Vía E — Guardar los tríos

**Idea.** Si la demostración acaba necesitando consistencia de tres nodos, cambiar la representación: guardar los
tríos prohibidos junto al grafo de posesiones y que la regla de parejas los consulte.

**Qué hay.** La regla de tríos (`TRIO_RULE`, apagada por defecto) ya está implementada. Es correcta, pero no corta
ninguna arista. Para quitar un trío muerto hay que guardarlo como trío, porque ninguna de sus aristas es falsa.

**Riesgo.** Es un cambio de representación caro: tiempo de ×10 a ×30 solo para comprobar, más memoria. Y detrás de los
tríos pueden venir cuartetos muertos. Solo tendría sentido si las vías A–C muestran que hace falta.

### Mi recomendación

Empezar por **B**, porque su primer paso es una sola medida: `StarRestrict` dentro de los núcleos fijados en un color.
Si da 0 fallos, la vía B es la más corta hacia una demostración completa. Si falla, pasar a **A** con la medida de
profundidad de la cascada. **D** es la red de seguridad: con lo demostrado, un resultado completo para una clase
acotada está al alcance.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `NodeIn`, `CliqueSplit`; y en
`SecSplitInParts`, `ColourSurvive`. **Julia (`julia/improves_bingo/test_3sat/`):** `probe_shared`,
`probe_cliquesplit`, `dump_gonly`, `probe_onesided`, `probe_exactside`; en `src`, el punto de sonda `:pair_bad`.
**Commits:** de `8699325` a `2c02856` en la rama `reader-stuck`.
