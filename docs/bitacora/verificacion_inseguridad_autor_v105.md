# Verificación para el Autor v105: requires débiles y una máquina donde probar mejoras

Ricardo, soy Claude (Opus 5). En este tramo hemos pasado de tu idea de los `requires_debiles` a una máquina paralela,
`SatMachinePureImproves`, en la rama `spaik`. `SatMachinePure` queda como referencia. La nueva máquina da los mismos
veredictos, ahorra trabajo al review y está demostrado que no pierde soluciones.

Todo está en el build de `AbsSat` (`lake build AbsSat` verde), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. La idea, tal como la cerramos

Un nodo de cláusula `n` enlaza con los nodos de las cláusulas anteriores con las que comparte alguna variable. En cada
una de esas filas solo valen las filas que dan el mismo valor a **todas** las variables compartidas, leído sobre la
variable (con `¬x` el bit se invierte). Las filas que no comparten variables no se tocan. Al añadir `n`, los owners
globales de esas filas se restringen a sus requires débiles **antes** de los requires duros y del review.

Por ejemplo, con `C1 = (x1 ∨ x2 ∨ x3)` y `C4 = (x1 ∨ x2 ∨ x7)`, el nodo `C4 = 101` (x1=1, x2=0) solo admite `{100, 101}`
en la fila de C1. Con `C6 = (¬x1 ∨ ¬x2 ∨ ¬x3)`, el nodo `111` exige `000` en C1, que no existe: su conjunto débil queda
vacío y el nodo muere en el acto porque `isValid` falla.

## 2. Qué hay en el repositorio

| Módulo | Contenido |
|---|---|
| `GraphMap/CnfMapImproves` | `weakReqOfCnf`; apunta hacia atrás (`weakReqOfCnf_backward`); es correcta (`weakReqOfCnf_sound`) |
| `GraphPath/Model/PureDriverImproves` | `filterWeak` (`filterRequire` con un conjunto), `upFilteringWeak`, el driver `pureRunW` |
| `GraphPath/Model/ConservationImproves` | no pierde soluciones: `pureRunW_ne_nil`, `pureRunW_full_state` |
| `GraphPath/Model/ReviewWorkImproves` | el filtro débil solo quita lo que el review quitaría: `review_gowners_sub_startW` |
| `SatMachine/PureSatMachineImproves` | el envoltorio `SatMachinePureImproves` |
| `SatMachine/PureProofsImproves` | el puente del envoltorio con `pureRunW`: `final_line_run_pure`, `completeness_improves` |
| `SatMachine/ImprovesLoad`, `lake exe improves-diff` | compara las dos máquinas y el oráculo, y mide la carga del review |
| `Cnf/ClauseOrder`, `lake exe order-search` | órdenes de cláusulas (frecuencia, voraz, `minfront`, búsqueda local) y su medición |

Se reutiliza `rowPairs`/`pairsAgree` de `CnfReducer`: hay una sola definición de "coinciden en la variable".

## 3. Lo demostrado

- **`weakReqOfCnf_sound`**: si `a` satisface `φ`, el nodo que `a` elige en cada paso está dentro de todos los conjuntos
  débiles de los nodos que elige.
- **`pureRunW_ne_nil`**: si `φ` está bien formada y es satisfacible, la última línea de la máquina nueva no está vacía.
  **`pureRunW_full_state`**: el estado en el nodo final de cada asignación satisfactoria recorre el mapa, es válido y
  representa algún camino.

La prueba es la ley de conservación de `Conservation`: la asignación aporta la cadena y la máquina solo tiene que no
destruirla. Lo nuevo es poco. El filtro débil solo toca los owners globales, así que la cadena lo atraviesa
(`ChainSound_filterWeak`), y el estado filtrado es un recorte (`Pruned`) del original, sobre el que el paso de siempre
vale sin cambios (`chainSound_up_of_pruned`). Un estado con filtro débil no es `MapReachable`, pero el argumento solo
leía de ahí dos cosas, nodos por debajo del paso actual y `MachineOk`, y ambas se conservan: en la contabilidad del
driver `ShapeOk` sustituye a `MapReachable`.

- **`review_gowners_survive_weak`**: en cada envío de la máquina de referencia (estado alcanzable, destino en el paso
  siguiente, filtro válido), todo owner global que conserva el review base sobrevive también al filtro débil. Por tanto
  el review mejorado parte de un estado que aún contiene todo lo que el review base conserva
  (`review_gowners_sub_startW`): **lo que quita el filtro débil lo habría quitado el review**. Adelanta trabajo, no
  añade ninguno.

La prueba reutiliza dos resultados que ya estaban. Si el filtro débil quita `q`, la fila de `q` discrepa de la de `d` en
una variable compartida; esa variable es un literal de `d`, así que `d` la fija con un pin y el id de `q` contradice ese
pin (`idContradicts_of_weak_removed`, un lema solo de mapa). Un owner global cuyo id contradice un pin es `Unsupported`
(`IdDiesProof.idDies`), y el review elimina todo lo `Unsupported` (`RemovalClosure.unsupported_removed`).

## 4. Lo medido

`improves-diff` sobre 4 ficheros de `test/cnf` y 13 fórmulas aleatorias (hasta 8 variables, 6 UNSAT):

| Medida | Resultado |
|---|---|
| veredicto frente a `SatMachinePure` y la fuerza bruta | igual en todas |
| última línea (claves, owners globales, nodos por estado) | idéntica en todas |
| owners que elimina el review | −0 a −16 % |
| pasadas del review | −0 a −5 % |

El review ya eliminaba todo lo que quita el filtro débil, y ahora está demostrado (sección 3). La ganancia está en el
**trabajo**, no en el resultado, y en lo medido crece con el tamaño.

Envío a envío, en 1.569 envíos de tres fórmulas aleatorias pequeñas: el review mejorado nunca hace más pasadas ni elimina
más que el base, y los owners que quita el filtro débil ya desaparecen en la primera limpieza (`cleanInvalid`) del review
base. Esto es más fuerte que el teorema, porque compara el trabajo de dos reviews y ese trabajo depende del orden en que el
review recorre los nodos; queda como medición. En 5 de los 9 ficheros de `test/cnf` (tseitin, pigeonhole, graph-coloring, `test_2lit`) se
salta la comparación porque no cumplen `wfB`.

## 5. El orden de las cláusulas

Tu idea fue ordenar las cláusulas por el uso de sus literales (`x` y `¬x` por separado, suma de los tres, las de más uso
en los primeros pasos) para dar más fuerza al filtro débil. La medida corrigió el planteamiento en dos puntos.

- **El número de enlaces débiles no depende del orden.** Cada par de cláusulas que comparten variable da exactamente un
  enlace, que queda en la que va después. Reordenar solo decide quién filtra a quién y cuándo.
- **Lo que sí depende mucho del orden es el trabajo del propio review.** El orden por frecuencia lo aumenta (peor que el
  original en 11 de 13 fórmulas). El que lo reduce es **`minfront`**: colocar en cada paso la cláusula que deja menos
  variables compartidas entre lo ya colocado y lo que queda (la *frontera*).

La suma de la frontera tiene forma cerrada: es la suma de la distancia entre la primera y la última aparición de cada
variable. Sobre ella probé una búsqueda local (mover una cláusula a otra posición mientras baje la suma), partiendo de
`minfront` (`local`) y del orden original (`local-orig`).

Owners que elimina el review de la máquina mejorada, relativos al orden original (media geométrica por lote; veredicto
igual en todos los órdenes):

| Lote | freq | greedy | **minfront** | local | local-orig | aleatorios |
|---|---|---|---|---|---|---|
| 5×40, 6 fórmulas | ×4,53 | ×4,53 | ×0,26 | **×0,22** | ×0,32 | ×0,95–×1,55 |
| 6×24, 6 fórmulas | ×1,80 | ×1,29 | ×0,42 | **×0,36** | ×0,43 | ×0,90–×0,99 |
| 7×30, 4 fórmulas | ×1,94 | ×0,86 | ×0,41 | ×0,36 | **×0,29** | ×0,96–×1,26 |
| 8×34, 3 fórmulas | ×1,36 | ×0,47 | ×0,172 | **×0,171** | ×0,23 | ×0,61–×0,74 |
| 10×42, 2 fórmulas | — | — | **×0,19** | ×0,26 | — | — |

- `minfront` gana en todas las fórmulas frente al original, al voraz y a los aleatorios, y la ganancia crece con el
  tamaño: en 10×42 semilla 500 el review elimina 206.460 owners frente a 1.970.998.
- La búsqueda local aporta poco y no es fiable: **una suma de frontera menor no siempre es menos trabajo**. En 10×42
  semilla 501 bajó la suma de 267 a 252 y casi duplicó el trabajo (389.564 → 723.921); en 7×30 semilla 401, `local-orig`
  con suma 147 trabaja cuatro veces menos que `local` con 154.

Conclusión: `minfront` es el orden de referencia. Para bajar más hace falta una métrica que explique el trabajo mejor que
la frontera. Reordenar cláusulas no cambia la satisfacibilidad, así que lo demostrado sigue valiendo; falta el lema
"reordenar conserva `Satisfiable`" para enlazarlo formalmente.

## 6. Lo que queda

| Pieza | Estado |
|---|---|
| requires débiles correctos | demostrado |
| la máquina nueva no pierde soluciones (`pureRunW`) | demostrado |
| puente `SatMachinePureImproves.run_pure` ↔ `pureRunW` | demostrado (`final_line_run_pure`, `completeness_improves` en `PureProofsImproves`) |
| el filtro débil solo quita lo que el review quitaría | demostrado (`review_gowners_sub_startW`) |
| el review mejorado trabaja menos en cada envío | abierto: medido en todos los envíos, sin prueba |
| `minfront` reduce el trabajo del review | medido (21 fórmulas, ×0,17–×0,42 por lote), sin prueba |
| una métrica de orden que prediga el trabajo mejor que la frontera | abierto |
| línea no vacía ⇒ satisfacible | abierto, igual que en la máquina de referencia |
