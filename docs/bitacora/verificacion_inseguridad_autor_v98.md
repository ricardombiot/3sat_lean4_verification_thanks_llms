# Verificación para el Autor v98: sin zombis — la inducción se cierra salvo un lema sobre el mapa

Ricardo, soy Claude (Opus 5). En v97 lo abierto era `FabricOutside`: que, tras fijar los pins, los nodos
fuera del cierre de eliminación `R` tuvieran un `Fabric`. En este tramo esa hipótesis se ha reducido
dos veces, siempre a algo más simple. Ahora hay una inducción completa sobre la construcción de la
máquina con una sola hipótesis, `LossInClosure`, que se cumple en todo lo medido. Las mediciones
también han dejado claro qué forma tiene que tener el lema que falta: no sale de propiedades generales
de las tablas, sale de lo que codifican los ids de los nodos del mapa.

Todo lo de Lean está en el build de `AbsSat` (122 módulos), sin `sorry`, en `[propext, Quot.sound]`,
sobre las definiciones actuales. Las mediciones son sobre `SatMachinePure`, semillas 1001, 7777, 31337 y
90210 (44 fórmulas de 4 a 7 variables), con los scripts compilados a ejecutable.

---

## 1. La inducción del `Fabric` (`FabricInduction.lean`)

`FullFabric g`: algún `Fabric` tiene como miembros a todos los nodos de `g`.

| Paso | Teorema | Cómo |
|---|---|---|
| semilla | `fullFabric_initSeed` | `Fabric_initSeed` |
| `join` | `fullFabric_join` | los `Fabric` de cada lado pasan al `join`, y **`fabric_union`** los une: todas las cláusulas de un `Fabric` son locales |
| `addNode` | `fullFabric_addNode` | `Fabric_addNode` añade el nodo nuevo |
| filtro | `fullFabric_filterAll` | bajo `FabricOutside`, el review conserva el `Fabric` (`FOk_review`) y borra el resto (`unsupported_removed`) |
| todo | `fullFabric_reachable` | todo estado alcanzable válido está cubierto, bajo `FilterFabric` |

Las piezas `Fabric_initSeed`, `Fabric_addNode` y `Fabric_join_*` ya estaban en el proyecto; comprobé que
hablan de las definiciones actuales antes de usarlas.

Medido: los estados guardados tienen un `Fabric` que cubre todos sus nodos (3.774 de 3.774). Si se
restringe al estado filtrado, es ya un `Fabric` en 6.090 de 6.111 filtros. En los otros 21 fallan solo
entradas concretas: 118 que pierden su único respaldo, que cae en `R`. En todos esos casos el nodo tiene
otra entrada respaldada en el mismo paso.

## 2. Los caminos forman un `Fabric` (`ChainFabric.lean`)

La tabla más natural resultó ser la de los caminos completos:

- **`Fabric_chains`**: los nodos que están en alguna cadena `ChainSound`, con los pares que comparten
  una, forman un `Fabric`. El respaldo por padre e hijo lo dan los vecinos de la propia cadena.
- `fabricOutside_of_noZombie`: si todo nodo de `P` está en `R` o en un camino por los pins
  (`NoZombieOutside`), se cumple `FabricOutside`.
- **`survives_iff_onChain`**: con esa hipótesis, un nodo sobrevive al filtro **si y solo si** está en un
  camino completo que pasa por los pins.

Medido: ninguno de los 117.518 nodos de `P ∖ R` es zombi, ni en `P` ni en el estado filtrado.

## 3. Sin zombis, como invariante de la construcción (`NoZombies.lean`)

`NoZombie g`: todo nodo de `g` está en un camino completo.

| Paso | Teorema |
|---|---|
| semilla | `noZombie_initSeed` |
| `join` | `noZombie_join` |
| `addNode` | `noZombie_addNode` — un camino extendido por el nodo nuevo pasa por los viejos y por él |
| filtro | `noZombie_filterAll` — sobreviven los nodos de caminos por los pins, y esos caminos sobreviven al review |
| **todo** | **`noZombie_reachable`**, bajo `LossInClosure` |

Además `fullFabric_of_noZombie` (sin zombis ya da el `Fabric`) y **`filter_keeps_chains`**: bajo
`LossInClosure`, en cada filtro válido **el review conserva exactamente los nodos de los caminos
completos por los pins**.

> **`LossInClosure`**: partiendo de un estado alcanzable sin zombis, todo nodo que pierde todos sus
> caminos al fijar los pins está en `R`.

| Medido | |
|---|---|
| zombis en los estados guardados | 0 de 92.985 nodos |
| nodos que pierden todos sus caminos al fijar los pins | 41.501 |
| de ellos, en `R` | 41.501 — y `R` tiene exactamente 41.501 nodos |

## 4. Cómo detecta `R` la pérdida de caminos

**Rondas.** Calculado como punto fijo sin orden, `R` cae casi entero de golpe:

| Ronda | Nodos | Motivo |
|---|---|---|
| 0 | 41.470 | en un paso con pin, ninguno de sus owners es el nodo pineado |
| 1 | 31 | un paso cuyos owners murieron en la ronda 0 |
| 2 o más | 0 | |

Esto corrige una lectura de v97: la «cascada» de 4.612 casos venía del orden del barrido de
`cleanInvalid`, no de la estructura.

**Formas sencillas que no bastan.** Solo importan los filtros de cláusula (3 pins); con 1 pin el filtro
no elimina nada (5.764 nodos):

| Forma | Fallos |
|---|---|
| por parejas: `x` posee al nodo pineado ⟹ camino por los dos | 41 de 393.507 |
| triple: `x` posee nodos vivos con el id de los 3 pins ⟹ camino por los tres | 25 (más 6 con owners muertos) |

**Los 31 de la ronda 1 son de dos clases:**

| Clase | Nodos | Qué es |
|---|---|---|
| A | 10 | owners obsoletos: `x` posee un nodo pineado con el que no comparte camino; siempre son entradas que no encajan con su arista (el padre codificado no es owner de `x` en el paso anterior) |
| B | 21 | configuración tipo Helly real: cada pin es alcanzable con `x`, pero sus caminos se saltan pins distintos y ninguno respeta los tres |

La coherencia de aristas de las tablas es casi exacta: 29 entradas incoherentes en 2.157.071, y la clase A
coincide exactamente con ellas.

## 5. El separador: lo que codifican los ids

En la clase B, `R` atrapa a `x` por un **paso separador**: un paso donde cada owner de `x` solo está en
caminos que se saltan un pin. Busqué qué lo determina.

- **No es el primer paso donde divergen los caminos**: en 11 de los 21 casos el separador no está ahí.
- **Sí es un paso que codifica conjuntamente los valores pineados.** Interpretando el id de cada owner
  (su nodo de mapa más el de su padre) como las variables que fija:

| | |
|---|---|
| nodos de clase B con un separador donde **el id de cada owner contradice un pin** | **21 de 21** |
| separadores de ese tipo en pasos de valor | fijan 2 variables pineadas: el valor y, por el padre, la variable anterior |
| separadores de ese tipo en filas de cláusula | fijan 2 o 3 variables pineadas (L1) |

Ejemplo (semilla 90210): pins `v4 = 0`, `v2 = 0`, `v1 = 0`. Los caminos de `x` toman combinaciones que se
saltan pins distintos. En los pasos de cláusula 13 y 14, cada owner de `x` es una fila que fija dos de esas
variables con un valor contrario a un pin; en el 15, filas que fijan las tres.

Así que el lema que falta tiene esta forma, y es combinatoria sobre el mapa:

> Si todos los caminos de `x` se saltan algún pin, en algún paso de esos caminos el id de cada owner de
> `x` fija un valor contrario a un pin.

Con él, la ronda 0 mata esos owners (su tabla no tiene el pin en ese paso), y la ronda 1 mata a `x`.

## 6. Estado

| Pieza | Estado |
|---|---|
| `FullFabric` por inducción, bajo `FilterFabric` | ✅ demostrado |
| los caminos forman un `Fabric`; `FabricOutside ⇐ NoZombieOutside` | ✅ demostrado |
| **sin zombis por inducción; el filtro conserva exactamente los caminos por los pins** | ✅ bajo `LossInClosure` |
| `LossInClosure` | medido sin excepciones; abierto |
| candidato a lema: separador por ids | medido 21 de 21 en la clase B; abierto |
| `PinnedCompletion` (cadenas desde el último paso) | abierto |
| `JoinCovered` | abierto |

Los puntos abiertos principales son dos, con la misma forma: `LossInClosure` para nodos y
`PinnedCompletion` para cadenas. En los dos, lo que hay que ver es que la eliminación por pins detecta la
falta de caminos compatibles. Las mediciones indican que esa detección descansa en la codificación: cada
nodo guarda su arista, y las filas de cláusula fijan asignaciones conjuntas.

Build: `lake build AbsSat` verde, 122 módulos, 0 `sorry`, `[propext, Quot.sound]`.

## Anexo: cómo se midió

Todo con ejecutables compilados desde el scratchpad (`lake env lean --root=<dir> -c`, objetos C de
`AbsSat` compilados con `leanc -c`, enlazado con `leanc`), sin tocar el repositorio.

- **Zombis:** búsqueda exhaustiva de un camino `ChainSound` forzado por el nodo.
- **Rondas de `R`:** la ronda `i + 1` usa solo nodos de rondas anteriores.
- **Clases A y B:** A si algún owner pineado vivo no comparte camino con el nodo (búsqueda forzada por
  los dos); B en otro caso.
- **Coherencia de aristas:** para cada owner `q` de `x` en el paso `j ≥ 1`, si el nodo de mapa del padre
  de `q` es el id de algún owner de `x` en `j − 1`.
- **Separadores:** todos los pasos donde los owners globales de `x` murieron en la ronda 0. El id se lee
  así: un nodo de valor fija su variable, uno de negación la del valor que requiere (`reqOfCnf`), una
  fila de cláusula las de sus literales. Cada nodo suma lo que fija su padre.
