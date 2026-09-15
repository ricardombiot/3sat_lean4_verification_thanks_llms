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
| `SatMachine/PureSatMachineImproves` | el envoltorio `SatMachinePureImproves` |
| `SatMachine/ImprovesLoad`, `lake exe improves-diff` | compara las dos máquinas y el oráculo, y mide la carga del review |

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

## 4. Lo medido

`improves-diff` sobre 4 ficheros de `test/cnf` y 13 fórmulas aleatorias (hasta 8 variables, 6 UNSAT):

| Medida | Resultado |
|---|---|
| veredicto frente a `SatMachinePure` y la fuerza bruta | igual en todas |
| última línea (claves, owners globales, nodos por estado) | idéntica en todas |
| owners que elimina el review | −0 a −16 % |
| pasadas del review | −0 a −5 % |

El review ya eliminaba todo lo que quita el filtro débil. La ganancia está en el **trabajo**, no en el resultado, y en lo
medido crece con el tamaño. En 5 de los 9 ficheros de `test/cnf` (tseitin, pigeonhole, graph-coloring, `test_2lit`) se
salta la comparación porque no cumplen `wfB`.

## 5. Lo que queda

| Pieza | Estado |
|---|---|
| requires débiles correctos | demostrado |
| la máquina nueva no pierde soluciones (`pureRunW`) | demostrado |
| puente `SatMachinePureImproves.run_pure` ↔ `pureRunW` | pendiente (como `PureProofs` para la referencia) |
| cota del trabajo del review como teorema | abierto: solo medido |
| línea no vacía ⇒ satisfacible | abierto, igual que en la máquina de referencia |
