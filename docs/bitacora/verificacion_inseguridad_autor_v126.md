# Verificación para el Autor v126: cada rama de la máquina vive, línea a línea, dentro de la máquina completa

Ricardo, soy Claude (Opus 5). En v125 demostré que un estado de rama sigue dentro del estado completo en
cada operación de un envío (filtros, review agresivo, UP, `join`). Este tramo hace las dos cosas que
faltaban para una ejecución entera: la **inducción por líneas** y el **invariante de los estados de
rama**.

Todo en la rama `spaik`, en el build de `AbsSat` (246 jobs con la sonda), sin `sorry`, en
`[propext, Quot.sound]`.

---

## 1. El resultado

**`BranchLines.branchRun_embedded`**: para cualquier conjunto de fijaciones `P`,

- **todo estado de la línea final de la rama cumple los invariantes de la máquina** (`MInv`, y las claves
  de la línea son únicas);
- **todo estado de la rama está dentro (`Embedded`) del estado con la misma clave de `pureRunW`**, la
  máquina completa.

Es decir: lo que la máquina construye sobre los caminos que respetan `P` está entero, nodos, owners y
enlaces, dentro de lo que construye sobre todos los caminos.

## 2. La inducción por líneas, sin depender del orden

Dentro de una línea, el driver hace los envíos en orden y une con `join` los que llegan al mismo nodo
del mapa. La rama hace solo algunos, y sus claves pueden llegar en otro orden que en la línea completa.
La prueba evita el orden:

- **`embedded_send`**: un envío de un estado de rama está dentro del mismo envío del estado completo, y
  este es válido. Encadena los lemas de v125: filtro débil, fijaciones + review agresivo, UP.
- **`full_reach`**: en la línea completa, todo envío válido **crece** (`Grown`) hasta la entrada de su
  nodo del mapa. Una entrada solo crece al insertar (`insert_grows`) y lo insertado crece hasta su
  entrada (`insert_new`).
- **`branch_union`**: en la línea de la rama, la entrada de un nodo del mapa está dentro de cualquier
  estado que contenga todos los envíos de la rama a ese nodo. La unión de estados contenidos sigue
  contenida (`embedded_join_same`).
- **`lineEmb_advance`**: con las claves únicas de la línea completa, todos esos envíos crecen hasta la
  **misma** entrada, así que la entrada de la rama está dentro de ella.
- `advance_inv`, `advance_reach`: los dos esquemas de inducción sobre `pureAdvanceW`.

## 3. El invariante de los estados de rama

- Las líneas de rama cumplen `LineInv` (los invariantes de la máquina en cada estado): la restricción
  de una línea conserva `LineInv` (`lineInv_restrict`), y el avance ya lo conservaba.
- **`MInv.own`, nuevo**: los owners de un nodo son nodos del estado. Lo necesitaba la unión de estados
  de rama. Se construye en la semilla, en UP (el nodo nuevo posee los owners globales), en `join`, y se
  conserva al filtrar: un owner viene del estado anterior, así que está por debajo del paso actual, y en
  un estado válido tras el review es owner global y por tanto nodo.

## 4. La cadena, tal como queda

```
rama válida de P  (branchRun φ P)                       MInv en todos sus estados   demostrado (v126)
  está dentro del estado final de la máquina            branchRun_embedded          demostrado (v126)
  un estado válido dentro de otro sobrevive a toda
  fijación compatible, que lo deja válido               survives_of_embedded        demostrado (v124)
  → la fijación P del estado final es válida            (falta el enlace, §5.1)
  sin préstamos: una rama válida tiene, en cada paso
  con elección, una sub-rama válida                     medido en profundidad 1     abierto
  → el lector acaba en un camino ⇒ modelo de φ          demostrado (v116)
```

## 5. Lo que queda

1. **Enlazar con la fijación del lector.** `survives_of_embedded` pide que los nodos de la rama sean
   compatibles con la fijación: en el paso de cada `r ∈ P`, sus nodos llevan el identificador `r`. Es
   un invariante de las ramas (la restricción deja solo la clave `r` en la línea `r.step`, y después
   solo se unen estados de la rama), que falta demostrar por la misma inducción.
2. **Sin préstamos**: si la rama de `P` llega válida al final, en cada paso con elección hay un `q`
   cuya rama `P + q` también llega válida. Medido en profundidad 1 (v124: 1.725 fijaciones, todas las
   ramas válidas); falta medir en profundidad mayor y demostrarlo.
