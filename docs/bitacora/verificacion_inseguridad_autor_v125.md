# Verificación para el Autor v125: las ramas en Lean, y cómo una rama vive dentro de la construcción

Ricardo, soy Claude (Opus 5). En v124 medimos que fijar un nodo en el estado final da exactamente el
estado que la máquina construye sobre la rama de ese nodo, y reorganizamos la prueba del lector en dos
piezas globales: incrustación y ausencia de préstamos. Este tramo define las ramas en Lean y demuestra
que una rama se mantiene dentro de la construcción completa en **cada operación** de un envío.

Todo en la rama `spaik`, en el build de `AbsSat` (245 jobs con la sonda), sin `sorry`, en
`[propext, Quot.sound]`.

---

## 1. Las ramas (`BranchRun.lean`)

- **`restrictLine P k line`**: en la línea `k`, se quedan solo los estados cuya clave coincide con
  toda fijación de `P` en el paso `k`.
- **`branchRun φ P`**: el driver de *Improves* (`pureAdvanceW`), restringido así en cada línea. Es la
  máquina construida solo sobre los caminos parciales que respetan `P`.
- **`branchRun_nil`**: sin fijaciones, la rama es la máquina (`pureRunW`).

## 2. Un ajuste en el soporte: los enlaces (`AnchoredSurvive.Sup.link`)

Para seguir una rama a través del review no basta con que sobrevivan sus nodos y owners: tienen que
sobrevivir también sus enlaces padre–hijo. `Sup` lleva ahora el campo **`link`**: dos miembros
enlazados en los dos sentidos y en pasos vecinos son un enlace padre–hijo. Se conserva por las
operaciones primitivas (actualizar owners no toca padres; `unlink` conserva los enlaces entre miembros;
`removeNode` no quita miembros) y lo suministran los tres sitios que construyen soportes
(`SpcSupport`, `SliceExact`, `EmbeddedSupport`), con la adyacencia exacta de v122.

`Embedded B G` se restringe a lo que la prueba usa: owners y padres **entre nodos de `B`**.

## 3. La rama dentro de la construcción, operación a operación

| operación de un envío | lema | qué pide |
|---|---|---|
| estrechar la rama | `embedded_of_pruned` | — |
| fijaciones (`filterRequire`) en los dos lados | `embedded_filterRequire` | — |
| filtro débil en los dos lados | `embedded_filterWeakAll` | — |
| **fijaciones + review agresivo completo** en los dos lados | **`embedded_filterAllAgg`** | que el lado de la rama quede válido |
| **UP** del mismo nodo del mapa | **`embedded_addNode`**, `embedded_up` | mismo `map_parent`, nodos por debajo del paso |
| `join` que solo añade al lado completo | `embedded_of_grown` | — |
| **`join` de dos estados de rama** dentro del `join` completo | **`embedded_join`** | owners y padres de la rama son nodos suyos |

El punto clave es el review: si el estado de la rama tras el review es válido, sus propias tablas son
un soporte dentro del estado completo filtrado (`sup_of_embedded`, v124), y `AnchoredSurvive` las lleva
a través del review completo, con enlaces incluidos. **Nada de lo que la rama construye se pierde en la
construcción completa.**

## 4. Lo que queda

1. **La inducción por líneas.** Dentro de una línea, los envíos y los `join` se hacen en orden, y la
   rama hace un subconjunto de ellos. Con los lemas de la sección 3 falta encadenar: toda clave de la
   línea de la rama está, incrustada, en la línea completa.
2. **Los invariantes que piden los lemas**, en los estados de la rama: que los owners sean nodos
   (se construye así en UP y se conserva al filtrar), y los de `MInv` para los estados de rama (que son
   los de la máquina, restringida).
3. **Sin préstamos** (pieza 2 de v124): si la rama de `P` llega válida, en cada paso con elección hay
   un `q` cuya rama `P + q` llega válida.

Con 1 y 2: una rama válida está dentro del estado final, así que su fijación deja el estado del lector
válido (`survives_of_embedded`). Con 3, el lector siempre encuentra esa fijación.
