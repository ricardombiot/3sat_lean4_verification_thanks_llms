# Verificación para el Autor v205: las etiquetas por fila, implementadas en Julia, y cómo etiquetar solo antes de cada join

Ricardo, este informe es corto. Cuenta cómo implementé la propuesta del v204 §7 y qué da hasta ahora. También recoge tu
propuesta de optimización (etiquetar solo antes de cada join real), con el matiz que la hace correcta. Todo está en la
rama `row-tags` (desde `star-rule`), commit `3ec2436`, detrás de `ROW_TAGS` y **apagado por defecto**.

**La conclusión, por adelantado.**
* **Correcto en todo lo medido:** mismos veredictos que el exhaustivo. El lector recorre todas sus ramas sin ningún pin
  muerto, y sus hojas son exactamente las soluciones.
* **La unión sale por la razón buscada** (5 instancias pequeñas): en cada join fijado, la pieza de cada clave queda
  dentro de su llegada fijada igual, con 0 fallos. Sin la regla hay cientos de fallos, así que es la regla la que lo da.
* **La memoria no es problema:** pico de 0,7 GB con etiquetas, frente a 1 GB de la versión sin ellas en el corpus
  completo. Las pruebas corren con un tope de 6 GB que mata el proceso si se pasa (§3).
* **El tiempo sí lo es:** ×25 en las 27 instancias ya medidas, ×38 en la peor. Lo caro es la regla, no las etiquetas.
* **La regla no quita ninguna arista ni ningún nodo**, solo claves: el estado final es idéntico al de la máquina sin
  etiquetas. Lo que hace es refinar a qué pieza pertenece cada arista.

---

## 1. La implementación

### 1.1 Los datos (`src/db/path/docs/path_owners_graph.jl`)

* **`Edge.tags :: Vector{UInt8}`**: un byte por fila de claves y un bit por clave (la clave `(ℓ, i)` es el bit `i`).
  En bin hay como mucho 2 claves por fila, y el código comprueba que el índice cabe en 8 bits.
* **`OwnersGraph.ntags`**: las etiquetas de cada nodo vivo. La arista reflexiva no tiene objeto, y la regla la necesita
  como testigo.
* **`OwnersGraph.krows`**: cuántas filas están marcadas (las filas 0 … `krows−1`).
* **Con `ROW_TAGS = :off`** no se guarda nada. Todas las aristas comparten un mismo vector vacío, así que la máquina de
  siempre no paga memoria.

### 1.2 Dónde se escriben

| operación | qué hace con las etiquetas | dónde |
|---|---|---|
| llegada | `stamp!`: toda arista y todo nodo de la copia del remitente reciben el bit de su clave en la fila de su cima | `do_up_filtering!`, antes del filtro |
| UP | el nodo nuevo recibe la unión de las etiquetas de sus padres; la arista `n–w`, la unión de las de `p–w` | `create_from_parents!` |
| join | OR fila a fila (los dos lados llegan con las mismas filas; se comprueba) | `union!` |
| pin | no las toca; el review hace el resto | — |

### 1.3 La regla (`src/graph_path/graph_path_tags.jl`)

Corre dentro del punto fijo del review, cuando las demás reglas ya no cambian nada. Para cada fila mezclada `ℓ` (con
más de una clave entre los vivos) y cada clave `a`:
1. **Construye la pieza de `a`:** los vivos que llevan `a` y, para cada uno, sus vecinos por aristas que llevan `a`,
   agrupados por paso.
2. **Nodo:** se queda con `a` si tiene vecino de la pieza en cada paso, y un padre (si no es raíz) y un hijo (si no es
   cima) enlazados dentro de la pieza.
3. **Arista `x–w`:** se queda con `a` si los dos extremos la llevan y, en cada paso, tienen un testigo común en la
   pieza (la regla de parejas). Además, cada extremo necesita un padre y un hijo de la pieza que lleguen al otro
   extremo (las pasadas de padres e hijos).
4. **En dos fases**, como la regla de parejas: se marcan todas las claves que caen y se quitan a la vez. Un nodo o una
   arista que se queda sin claves en alguna fila muere, y el review sigue.

**Solidez (deducida, v204 §7.3):** la camarilla de una solución lleva, en cada fila, la clave por la que pasa. Sus
propios nodos son los testigos, padres e hijos que la regla pide, así que la regla nunca le quita nada.

Interruptores: `ROW_TAGS=on|off` guarda o no las etiquetas. `TAG_RULE=on|off` deja correr o no la regla; con `off` se
guardan las etiquetas pero no se reducen, y sirve de control negativo.

## 2. Resultados

**Diferencial contra el exhaustivo** (`test_3sat/probe_row_tags.jl`: máquina entera y lector por todas sus ramas):

| | sin etiquetas | con etiquetas (en curso) |
|---|---|---|
| instancias | 89 (1 error de carga, `simple_v3_c2`, igual que en sondas anteriores) | 28 de 89 |
| veredicto distinto del exhaustivo | 0 | 0 |
| hojas del lector que no son soluciones | 0 | 0 |
| pins muertos / callejones del lector | 0 / 0 | 0 / 0 |
| aristas finales distintas de la versión sin etiquetas | — | 0 |
| aristas / nodos que mata la regla | — | 0 / 0 (21 M claves quitadas) |
| memoria (máximo del proceso) | 978 MB | 723 MB |
| tiempo en las mismas 27 instancias | 44 s | 1 088 s (×25; peor `rand3sat_v8_c10`, ×38) |

**La unión por la razón buscada** (`test_3sat/probe_row_tags_union.jl`, 5 instancias pequeñas, 153 joins, 459
fijaciones). En cada join se guardan las llegadas. Luego se fijan en `Q` la unión y cada llegada, y se comprueba:
* que los nodos de la pieza de cada clave estén vivos en su llegada fijada;
* que sus aristas estén en su llegada fijada;
* que cada cima esté viva en la llegada de su clave.

| | nodos de pieza fuera | aristas de pieza fuera | cimas fuera |
|---|---|---|---|
| con la regla | **0** de 16 895 | **0** de 210 309 | 0 de 818 |
| sin la regla (`TAG_RULE=off`) | 1 460 | 6 236 | 0 |

Sin la regla, casi todos los fallos son piezas de una llegada que, fijada, ya está muerta, pero cuya parte sigue
viva en la unión. Con la regla desaparecen. Eso es lo que la §7.4 del v204 necesitaba para `JoinStarCore`: la pieza de
la clave de una cima está dentro de su llegada.

## 3. El tope de memoria

`test_3sat/run_capped.sh <tope_MB> <tope_s> <comando…>` lanza el comando y cada segundo lee su **huella** con
`footprint`. La huella cuenta la memoria comprimida, que en el v197 escondía 88,7 GB detrás de 6,9 GB residentes. Si
pasa el tope, mata el proceso y sus hijos, y al terminar escribe la huella máxima vista. Probado: mata un proceso de
prueba a 1,1 GB con un tope de 300 MB. Todas las corridas usan 6 GB por proceso, como mucho dos a la vez, en un equipo
de 16 GB, más `--heap-size-hint` para Julia.

## 4. La optimización: etiquetar solo antes de cada join real

**Tu propuesta:** no marcar en cada llegada, sino solo cuando hay un join de verdad, para no guardar más etiquetas de
las necesarias.

**Por qué es correcta.** En un gpath, una fila `ℓ` sin etiquetas explícitas significa que todos sus nodos vivos del
paso `ℓ` son del mismo nodo del mapa `k`. Entonces la etiqueta implícita de todo en esa fila es `{k}`, y se lee de la
propia fila, sin guardarla. La regla ya se salta esas filas (`tag_mixed_rows`), así que no cambia nada.

**El matiz.** La mezcla en la fila `ℓ` no la crea solo un join del paso `ℓ`. La crea **cualquier join posterior** que
junte dos linajes que pasaron por claves distintas en `ℓ`. Por eso, justo antes de cada join:
1. para cada fila `ℓ` por debajo, se miran las claves de cada lado: las explícitas si tiene etiquetas en esa fila, o
   la clave única de sus nodos del paso `ℓ` si no;
2. si los dos lados traen la misma clave única, la fila sigue sin etiquetas;
3. si no, se materializa la fila: cada arista y cada nodo de un lado recibe el bit de su clave, y los del otro el
   suyo;
4. después, la unión hace OR fila a fila.

**Además**, tras un pin una fila mezclada puede volver a tener una sola clave. Entonces se puede soltar.

**Cambio en la estructura.** Cada gpath lleva la lista ordenada de sus filas etiquetadas (`trows`), y cada arista un
vector alineado con ella. En el join se alinean las dos listas y se rellenan las filas que falten con la clave
implícita de su lado. El coste es una pasada por las filas, del mismo orden que la unión.

**Qué se gana y qué no.**
* **Memoria:** solo las filas mezcladas. En las instancias con poca mezcla, casi nada. El v197 midió hasta 89 filas
  mezcladas de 105 en las peores, así que ahí el ahorro será pequeño.
* **Tiempo:** desaparece el marcado de todas las aristas en cada llegada. **Pero el ×25 viene de la regla, no del
  marcado**, así que esta optimización no lo resuelve. Para el tiempo hace falta además que la regla sea incremental:
  que solo vuelva a mirar lo que tocó la última pasada, como ya hacen la limpieza y la regla de parejas.
* **Semántica:** idéntica a la versión actual. Eso da una prueba exacta: las dos versiones deben quitar las mismas
  claves en las filas mezcladas y dejar el mismo estado.

## 5. Lo que sigue

1. Terminar el corpus con etiquetas (quedan 61 instancias) y la sonda de la unión en el corpus entero.
2. La optimización de la §4, con el diferencial exacto contra la versión densa como prueba.
3. La regla incremental, para bajar el ×25.
4. Si todo se mantiene, pasar a Lean (v204 §7.7 paso 4): `TagStruct`, la regla como `Rule` con `keepsSol`, y
   `topUnion_of_tags`.

---

**Ficheros:** `src/db/path/docs/path_owners_graph.jl`, `src/graph_path/graph_path_tags.jl`, y los enganches en
`graph_path_up.jl`, `graph_path_filter.jl` y `graph_path.jl`; sondas `test_3sat/probe_row_tags.jl` y
`test_3sat/probe_row_tags_union.jl`; tope `test_3sat/run_capped.sh`. Todo bajo `julia/improves_bingo/`.
