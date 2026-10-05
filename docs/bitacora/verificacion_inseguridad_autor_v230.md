# Verificación para el Autor v230: el lector por ventanas en todo árbol de cláusulas

5 de octubre de 2026, rama `reader-window`. Continúa el v229. En una frase: **la propuesta del v229 está formalizada
entera: para toda fórmula cuyo grafo de incidencia es un árbol (Berge-acíclica), una vez acolchada, tu lector por nodos
de ventana no se atasca en Lean, y lo único que queda por demostrar para que sea sin hipótesis es que la máquina
construya sus líneas sin fantasmas (`PhantomAtW`).** Al formalizar encontré un hueco en mi demostración a mano del v229
y lo cerré con un argumento más simple que el original.

> **Estado**: todo compila (`lake build`, 197 trabajos), sin `sorry`; los teoremas solo dependen de `propext`,
> `Classical.choice` y `Quot.sound` (`satisfiable_pad`, ni de `Classical.choice`). Cuatro módulos nuevos, 1 127 líneas.

## 0. Resumen

| | v229 | v230 |
|---|---|---|
| árboles de cláusulas | teorema a mano (§6), con un hueco | **demostrado en Lean** (`twoWitnessF_of_forest`) |
| lecturas locales | propuesta: acolchar la fórmula | **acolchado en Lean** (`padCnf`), con la satisfacibilidad, las libres y las lecturas locales |
| corte fijado | las variables de las elecciones | **las constantes de la familia** (mayor, y `hfix` gratis) |
| variables libres | propuesta | **en el pegado** (`glue_pegF`) |
| resultado | `Peg ⇒ H2′ ⇒ lector` | **para todo árbol `φ`: el lector sobre `padCnf φ` no se atasca, dadas sus líneas** (`reader_winNode_pad`) |
| abierto | líneas en árboles | líneas en árboles (lo único) |

## 1. El plan del v229, paso a paso

| paso | qué | módulo | commit |
|---|---|---|---|
| 1 | el corte fijado son las constantes de `P` (`ConstIn`) | `ForbidOnGluePegF` | `2bba399` |
| 2 | variables libres en el pegado (`FreeOK`, `PegF`, `glue_pegF`) | `ForbidOnGluePegF` | `2bba399` |
| 3a | el bosque de incidencia con raíz y sus ramas (`IncForest`, `br`, `br_clause`) | `ForbidOnIncForest` | `b06c10d` |
| 3b | el separador de tres bloques (`sep_three`) | `ForbidOnIncForest` | `eb240c8` |
| 4 | H2′ y el lector en los árboles con lecturas locales (`twoWitnessF_of_forest`, `reader_winNode_of_forest`) | `ForbidOnForestPeg` | `6e3414e` |
| 5 | el acolchado (`padCnf`, `satisfiable_pad`, `freeOK_pad`, `localBlocks_pad`, `IncForest.pad`, `reader_winNode_pad`) | `ForbidOnPad` | `e6c6bc4` |
| 6 | sondas de la máquina real sobre árboles acolchados | — | pendiente |

## 2. Las piezas

### 2.1 El corte de las constantes y las variables libres (pasos 1 y 2)

El corte del pegado eran las variables de las elecciones. Ahora es `ConstIn P`: toda variable en la que las ramas de la
familia coinciden. Es mayor (incluye lo que la fórmula fuerza) y la condición de que las fuentes coincidan en el corte
sale por definición.

Las **libres** son las que solo aparecen en cláusulas de una sola variable, como la tautología `(x₀ ∨ ¬x₀ ∨ x₀)`. No
cuentan para las regiones: una región libre puede tocar los tres nodos. El pegado les da el valor de cualquier nodo del
trío que las lea; todos coinciden porque cada pareja tiene una rama común (`fv`, en `glue_pegF`).

### 2.2 El bosque y sus ramas (paso 3)

`IncForest φ`: un padre por vértice (variables y cláusulas), una profundidad que baja hacia la raíz, y **toda incidencia
es una arista padre-hijo**. Se admiten aristas de más, que solo juntan componentes: así toda fórmula Berge-acíclica
tiene un bosque con raíz común.

* Los antepasados de un vértice están en cadena (`anc_total`).
* La **rama** de `v` respecto de `m` es el hijo de `m` que es antepasado de `v`, o «arriba» si `m` no lo es; es única
  (`inBr_unique`), y una arista sin `m` no la cambia (`br_edge`). Por eso **ninguna cláusula cruza ramas** al quitar `m`
  (`br_clause`).
* **`sep_three`**: el antepasado común más profundo de alguna pareja de tres bloques deja los bloques distintos de él en
  ramas distintas. Es la mediana del v229, sin tener que calcularla.

### 2.3 H2′ en los árboles (paso 4) y el hueco que cerró

Para un trío Helly-fallido, `sep_three` da `m`. El paso de corte `cutStep m` es el paso de su variable o el tercer paso
de su cláusula (que leen todo lo de `m`); las regiones son las ramas respecto de `m`. Entonces vale `PegF`
(`pegF_forest`): las cláusulas no cruzan ramas fuera del corte y cada región toca a lo sumo un nodo del trío.

**El hueco.** En el v229 hice casos según qué pasos de la cláusula mediana ocupaba el trío, y suponía que como mucho dos
nodos tenían esa cláusula como bloque. Con el acolchado pueden ser los tres (por ejemplo en `c'.l₂`, `c'.l₃` y el paso
siguiente).

**El cierre, más simple que el original.** Si `cutStep m` cae en el paso de un nodo `y` del trío, ese nodo es alcanzable
desde los tres: las ramas de sus parejas pasan por él. El pegado con `s = y` da una rama de `P` por los tres, así que el
trío no era Helly-fallido. Si no cae en ninguno, es el λ de H2′. Sin subcasos y sin recuento de pasos.

### 2.4 El acolchado (paso 5)

`padCnf φ`: la variable real `v` pasa a `2v + 1`; las pares son de relleno; las cláusulas son
`T, C₀', T, C₁', …, T` con `T = (x₀ ∨ ¬x₀ ∨ x₀)`. Basta una variable de relleno para todas las tautologías (el gemelo en
Python, `pad_formula.py`, quedó igual).

* `satisfiable_pad`: la acolchada es satisfacible si y solo si `φ` lo es.
* `freeOK_pad`: las pares solo están en la tautología.
* `localBlocks_pad`: toda ventana lee, fuera de las pares, una sola variable o una sola cláusula. En la parte de
  variables, la ventana toca dos índices seguidos y solo uno es impar; en la de cláusulas, toca dos cláusulas seguidas y
  solo una es real; en la frontera, solo relleno.
* `IncForest.pad`, `pad_root`: el bosque de `φ` pasa a la acolchada; el relleno cuelga de la raíz y las tautologías de
  `x₀`.

## 3. El resultado

$$\varphi\ \text{Berge-acíclica}\ \land\ \mathrm{PhantomAtW}(\mathrm{padCnf}\,\varphi)\ \Longrightarrow\ \text{el lector por nodos de ventana sobre }\mathrm{padCnf}\,\varphi\ \text{no se atasca}$$

y `padCnf φ` es satisfacible si y solo si `φ` lo es. La cadena completa en Lean:

`sep_three` → `pegF_forest` → `twoWitnessF_of_forest` (H2′) → `phantomFree_of_twoWitnessF` → `snd3_filterW` (la
ventana entera, un review) → `reader_winNode_of_twoWitnessF` → `reader_winNode_of_forest` → `reader_winNode_pad`.

## 4. Lo que queda abierto

1. **Las líneas en árboles.** `PhantomAtW (padCnf φ)`: que la máquina construya la línea final sin fantasmas. Está
   demostrado para las clases de los v223–v228 (bloques, cadenas), no para árboles con ramificaciones ni para la
   acolchada. Es **lo único** que separa el resultado de uno sin hipótesis en árboles. El candidato natural es el mismo
   pegado por regiones: el filtro y el UP de las líneas piden `PhantomFree` con la misma forma que el lector.
2. **Fórmulas con ciclos.** H2′ se cumple en lo medido (`parity_use`, `clause_mix`), pero el pegado por un corte del
   tamaño de una ventana no la explica sola. Es un límite de esta prueba, no una medida de la máquina.
3. **El paso 6 del plan**: medir la máquina real (Julia) sobre árboles acolchados. La fuerza bruta en Python no llega:
   el relleno multiplica las soluciones.

## 5. Trucos técnicos de esta vuelta

1. **El nodo del trío como testigo.** Si el corte cae en un nodo del trío, ese nodo ya es alcanzable desde los tres:
   no hace falta buscar otro λ, el trío no era Helly-fallido.
2. **Regiones por ramas, no por componentes.** Las regiones son las ramas respecto del separador en el bosque con raíz:
   no hay que calcular componentes del grafo, y juntar componentes con aristas de más no estorba.
3. **El antepasado común más profundo** en vez de la mediana: un máximo sobre una cadena finita (`exists_deepest`).
4. **Una sola tautología de relleno** basta para las lecturas locales.
5. **`Classical.choose` en vez de `choose`** (sin Mathlib) para elegir una fuente por región.

## Ficheros

| fichero (`lean/improves_bingo/AbsSatBingo/Model/`) | qué | commit |
|---|---|---|
| `ForbidOnGluePegF.lean` | `ConstIn`, `FreeOK`, `PegF`, `glue_pegF`, `reader_winNode_of_pegF` | `2bba399` |
| `ForbidOnIncForest.lean` | `IncForest`, `Anc`, `br`, `br_clause`, `sep_three` | `b06c10d`, `eb240c8` |
| `ForbidOnForestPeg.lean` | `LocalBlocks`, `cutStep`, `pegF_forest`, `twoWitnessF_of_forest`, `reader_winNode_of_forest` | `6e3414e` |
| `ForbidOnPad.lean` | `padCnf`, `satisfiable_pad`, `freeOK_pad`, `localBlocks_pad`, `IncForest.pad`, `reader_winNode_pad` | `e6c6bc4` |
| `lean/improves_bingo/scripts/pad_formula.py` | el acolchado, gemelo de `padCnf` | `e6c6bc4` |
