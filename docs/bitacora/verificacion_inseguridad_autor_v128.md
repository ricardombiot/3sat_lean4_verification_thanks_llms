# Verificación para el Autor v128: la inducción sobre la construcción, completa salvo el `join`

Ricardo, soy Claude (Opus 5). Me pediste la demostración por inducción sobre la construcción. Este tramo
la hace entera: define un invariante de un solo estado, demuestra que lo conservan la semilla, el filtro
con el review agresivo y el UP, y lo ensambla línea a línea hasta el estado final. El único caso que queda
como condición es el `join`, y es exactamente la ausencia de préstamos que hemos visto desde v124.

Todo en la rama `spaik`, en el build de `AbsSat` (183 jobs), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. El invariante: validez hereditaria de fijaciones (`Hereditary.lean`)

- **Restricciones** `C`: en un paso, los nodos del mapa permitidos. Una fijación es la restricción que
  permite uno solo. `Fw g C` es el estado `g` bajo `C`, seguido del review agresivo.
- **`HPV g`**: si `g` es válido bajo `C`, fijar cualquier owner global que siga vivo lo mantiene válido.

**`sat_of_hpv`** (**demostrado**): **si un estado final válido de la máquina tiene `HPV`, φ tiene un
modelo.** El estado del lector (fijaciones una a una) y `Fw` (restricciones a la vez) se relacionan en los
dos sentidos por la incrustación:

- `reader_inside_Fw`: el estado del lector tras `P` está dentro de `Fw G P`, que es válido;
- `pin_valid_of_Fw`: si `Fw G (P ++ [q])` es válido, fijar `q` en el estado del lector es válido;
- `embedded_weak`, `embedded_weak_pins`: la incrustación atraviesa filtros débiles y fijaciones.

## 2. La construcción, caso a caso

| paso de la construcción | lema | estado |
|---|---|---|
| semilla | `hpv_initSeed` (un solo nodo: fijarlo no cambia nada) | **demostrado** |
| filtro débil + fijaciones + review agresivo | `hpv_filter` | **demostrado** |
| UP | `hpv_addNode` | **demostrado** |
| un envío (filtro y UP) | `hpv_sent` | **demostrado** |
| `join` de dos envíos a la misma clave | `hpv_join` bajo `JoinSplit` | **condición abierta** |
| una línea, la ejecución entera | `lineHPV_advance`, `lineHPV_steps` | **demostrado** |

**El filtro** (`HereditaryBuild.lean`). Restringir el estado filtrado con `C` equivale, para la validez y
para los owners globales que quedan, a restringir el estado original con las restricciones del filtro
seguidas de `C` (`Fw_filter_inside`, `Fw_filter_valid`).

**El UP** (`HereditaryUp.lean`). Con `A = addNode F d`:

- fijar el nodo nuevo no cambia nada: es el único nodo de su paso;
- **`drop_new`**: si `A` es válido bajo `C`, las tablas revisadas sin el nodo nuevo son un soporte dentro
  de `F` bajo `C`; así `F` es válido bajo `C` y conserva los owners antiguos;
- **`add_new`**: si `F` es válido bajo `C` más una fijación antigua `q`, las tablas revisadas con el nodo
  nuevo añadido son un soporte dentro de `A`; así `A` es válido bajo `C + q`.

## 3. El veredicto

**`HereditaryRun.sat_of_joinSplit`** (**demostrado**): **si toda unión que puede hacer la máquina reparte
sus elecciones entre sus dos lados, un estado final válido de *Improves* da un modelo de φ.**

- **`JoinSplit g₁ g₂`**: bajo cualquier restricción `C`, todo owner global del `join` restringido lo es
  de alguno de los dos lados restringidos igual, y ese lado es válido. Si se cumple, el lado que tiene la
  elección conserva `HPV`, está dentro del `join` y sobrevive a la nueva fijación (`hpv_join`).
- **`JoinsSplit φ`**, la hipótesis del teorema: `JoinSplit` para todo par de estados con los invariantes
  de la máquina, `HPV` y compatibles para unirse. Es más fuerte de lo estrictamente necesario, porque la
  máquina solo une estados concretos; se puede afinar a las uniones que el driver hace de verdad.

## 4. Medido: las uniones de la máquina no prestan (`helly joins`)

La sonda recorre el driver y, en cada unión que hace, compara el `join` restringido con sus dos lados,
sin restricción y con cada fijación de un paso con elección:

| familia | uniones | restricciones | owners globales comprobados | prestados | `join` válido con ambos lados inválidos |
|---|---|---|---|---|---|
| Tseitin K4 par | 32 | 896 | 27.670 | **0** | **0** |
| aleatorias, 6–8 variables (semilla 1001, 20 fórmulas) | 2.442 | 66.835 | 2.473.189 | **0** | **0** |

`par_k3`, `par_k5` y K4 menos una arista (3 colores) siguen en marcha; se añadirán al terminar.

## 5. Lo que queda

1. **`JoinSplit`**: demostrarlo, o afinarlo a las uniones que hace el driver. Es la forma local de "sin
   préstamos": lo que sobrevive en la unión viene de un camino que sobrevive por sí solo en un lado. La
   conmutación exacta de v124 (fijar = construir la rama) apunta a que es cierto.
2. **Ampliar la medida**: restricciones con varias fijaciones y filtros débiles, no solo una fijación.
