# Verificación para el Autor v124: fijar es construir solo la rama

Ricardo, soy Claude (Opus 5). Me pediste mirar la abstracción desde lo global: la estructura es, paso a
paso, el conjunto de caminos parciales construido, y lo que importa es que durante la lectura cada nodo
pertenezca a al menos un camino válido; no tríos, sino que la cadena se cumpla paso a paso, que es lo
que hace el algoritmo.

Este tramo toma esa visión literalmente y encuentra una propiedad global muy limpia: **fijar un nodo
en el estado final da exactamente el estado que la máquina construye sobre la rama de ese nodo**. Con
ella la prueba del lector se reorganiza en dos piezas globales; la primera queda demostrada.

Todo en la rama `spaik`, en el build de `AbsSat` (175 jobs), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. Medido: fijar conmuta con construir (`helly commute`)

Para cada estado final de la máquina (clave `K`) y cada fijación `q` del paso `s` con elección, la
sonda compara:

- **fijar**: `filterAllAgg G [q]` sobre el estado final `G`;
- **construir la rama**: tomar la línea `s` de la máquina, quedarse solo con el estado de clave `q`, y
  avanzar la máquina desde ahí hasta el final (mismos `UP`, filtros, review y `join`); después, el
  estado de clave `K`.

| familia | fijaciones | válidas en ambos | discrepancias de validez | nodos iguales | tablas de owners iguales |
|---|---|---|---|---|---|
| Tseitin K4 par | 88 | 88 | **0** | 88 | **88** |
| `par_k3_direct_asc_fresh` | 73 | 73 | **0** | 73 | **73** |
| `par_k5_chain_asc_shared` | 114 | 114 | **0** | 114 | **114** |
| Tseitin K3,3 par | 132 | 132 | **0** | 132 | **132** |
| aleatorias, 6–8 variables (semilla 1001, 20 fórmulas) | 1.318 | 1.318 | **0** | 1.318 | **1.318** |
| **total** | **1.725** | **1.725** | **0** | **1.725** | **1.725** |

**Coinciden los nodos y las tablas de owners entrada a entrada.** El estado que ve el lector tras
fijar no es un objeto nuevo: es la máquina construida sobre los caminos que pasan por `q`. Todas las
ramas medidas, además, llegan válidas al final.

## 2. La prueba del lector, reorganizada en dos piezas globales

Llamo **rama** `B_P` a la construcción restringida a las fijaciones `P`.

1. **Incrustación**: la rama está dentro del estado completo, y una rama válida sobrevive a su fijación
   en el estado completo, que queda válido.
2. **Sin préstamos**: si la máquina restringida a `P` llega válida al final, en cada paso con elección
   hay algún `q` cuya rama `P + q` también llega válida. Dicho con tus palabras: cada nodo pertenece a
   un camino construido paso a paso que sobrevive por sí mismo, y no solo porque un `join` con otra
   rama lo sostenga.

Con las dos, en cada estado del lector hay una fijación válida (la de la rama que sobrevive), así que el
lector acaba en un camino y el veredicto es correcto. No hacen falta tríos: la cadena se construye paso
a paso sobre la rama.

## 3. Lo demostrado: la pieza 1 (`EmbeddedSupport.lean`)

- **`Embedded B G`**: `B` está dentro de `G` (mismo paso actual, owners globales contenidos, y cada
  nodo de `B` es nodo de `G` con owners y padres contenidos).
- **`sup_of_embedded`**: si `B` es un estado válido del tipo del lector (`Adj`, `AggOk`, `SMP`), sus
  propios nodos y tablas son una relación de soporte **dentro de `G`**. Cada condición de `Sup` es un
  hecho de punto fijo de `B` que en `G` solo gana espacio: cobertura por validez, padres e hijos por
  la coherencia y la adyacencia de `B`, pares y simetría por `AggOk`.
- **`survives_of_embedded`**: por tanto, toda fijación de `G` compatible con `B`, seguida del review
  agresivo completo, **conserva todos los nodos de `B` y deja `G` válido**.

## 4. Lo que queda

- **Que la rama esté incrustada en el estado completo en cada línea.** Hay que definir en Lean la
  construcción restringida y demostrar que `Embedded` se conserva por `UP`, filtros, `join` y review.
  Para el review, `sup_of_embedded` ya da la supervivencia de los nodos; falta llevar también los
  enlaces.
- **Sin préstamos** (pieza 2): es el lema global de fondo. La conmutación exacta medida lo respalda en
  profundidad 1. Siguiente medida: la conmutación y la validez de ramas a profundidad 2 y más
  (fijaciones anidadas contra ramas doblemente restringidas).
