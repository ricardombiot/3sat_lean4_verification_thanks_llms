# Verificación para el Autor v229: el lector por ventanas, de las cadenas a los árboles

5 de octubre de 2026, rama `reader-window` (sale de `reader-stuck`). Continúa el v228. En una frase: **tu lector que
fija solo nodos de ventana (el tercer literal de una cláusula, cuyo id lleva abuelo, padre e hijo) no se atasca en
ninguna cadena en orden, sin hipótesis; para una fórmula cualquiera la prueba se reduce, sin condiciones de forma, a una
propiedad de dos testigos (H2′) que se cumple en todo lo medido; y H2′ sale de un lema de pegado sobre el grafo de la
fórmula que, con lecturas locales, vale en todo árbol de cláusulas.** Lo último está demostrado a mano y medido; queda
formalizarlo.

> **Estado**: todo compila (`lake build`, 193 trabajos), sin `sorry`; los teoremas solo dependen de `propext`,
> `Classical.choice` y `Quot.sound`. Las sondas nuevas están en `lean/improves_bingo/scripts/` (Python, fuerza bruta sobre
> las soluciones, con tope de memoria de 3 GB).

## 0. Resumen

| | v228 | v229 |
|---|---|---|
| lector | por separadores, en cadenas | **por nodos de ventana**: fija `[abuelo, padre, hijo]` en un solo filtro y un review |
| cadenas | toda cadena vía preproceso | el lector por ventanas no se atasca en `ChainOrdN`, en cualquier orden de ventanas |
| fórmula cualquiera | — | lector ⇐ líneas (`PhantomAtW`) + **H2′** por ventana, sin condiciones de forma |
| H2′ | — | ⇐ **`Peg`** (pegado por regiones del grafo primal en un paso λ) |
| medido | — | H2′ en 5 fórmulas, todas las ventanas previas, todos los tríos: 5 232 de 5 232 |
| propuesto | — | `Peg` en todo **árbol de cláusulas** con lecturas locales (demostración a mano, §6) |

## 1. Tu pregunta y cómo la modelé

Preguntaste si un lector que solo eligiera pasos de ventana prohibida y aplicara el review se podría demostrar sin
atasco. El atasco ya estaba reducido (`ReaderStuck.lean`): si el lector se para, el estado es un zombi (válido sin
camarillas), y fijar el nodo de una camarilla la conserva. Eso no depende de qué paso se fije, así que el contenido de tu
pregunta está en otro sitio: **que fijar una ventana no deje familias fantasma**.

Un nodo de ventana `q` del paso `σ = clauseStep j 2` tiene `q.id`, `q.parent_id`, `q.gparent_id`: los nodos de los tres
pasos de copia de la cláusula. Fijarlo es `filterAllOn [abuelo, padre, q.id]`: tres requisitos y **un solo review**. Lo
modelé así (`WinReading`), primero como tres elecciones seguidas (`ForbidOnWinRead`) y después tal cual
(`ForbidOnWinPin`, `ForbidOnWinBridge`).

## 2. Lo demostrado en Lean

| módulo | qué | teoremas |
|---|---|---|
| `ForbidOnWinRead` | la ventana como tres elecciones, separadores primero | `reader_win_on`, `phantomFree_pinnedNear` (T1 local), `sepPinAny_of_local`, `reader_win_of_chainOrd` |
| `ForbidOnWinPin` | **el filtro de varios requisitos con un review** | `snd3_filterL` (una `PhantomFree` por requisito, en cualquier orden, sobre la misma estructura), `WinReading`, `win_sels`, `reader_winNode_of_chainOrd`, `reader_winNode_of_winPinFree`, `winPinFree_of_chainOrd` |
| `ForbidOnTwoWitness` | dos testigos | `pairs_of_anchor` (con el ancla en σ las parejas son gratis), `phantomFree_of_twoWitness` (H2), `phantomFree_of_twoWitnessF` (H2′) |
| `ForbidOnWinBridge` | **el puente**: la ventana entera con el ancla en su paso | `snd3_filterW` (una sola `PhantomFree`), `WinPinFreeW`, `reader_winNode_of_twoWitnessF` |
| `ForbidOnGluePeg` | **el pegado en λ** | `Peg`, `glue_peg`, `noCommon_of_peg`, `twoWitnessF_of_peg`, `reader_winNode_of_peg` |

La cadena entera, sin condiciones de forma sobre la fórmula:

$$\mathrm{Peg}\ \Rightarrow\ \text{H2′}\ \Rightarrow\ \mathrm{PhantomFree}\ (\text{ventana entera, ancla en }\sigma)\ \Rightarrow\ \text{el lector por nodos de ventana no se atasca}\quad(\text{con }\mathrm{PhantomAtW}).$$

### 2.1 Las piezas que lo hicieron posible

1. **Una estructura para varios requisitos** (`snd3_filterL`). El estado fijado y revisado es una sola estructura cerrada
   para los tres requisitos; basta aplicar `PhantomFree` una vez por requisito y la familia crece en uno cada vez.
2. **El ancla en el paso del nodo de ventana** (`snd3_filterW`). Una rama de antes que pasa por un vivo `s` del paso `σ`
   lee también los requisitos de `σ - 1` y `σ - 2`: `s` forma pareja con un vivo fijado de cada uno de esos pasos y dos
   ramas con el mismo nodo en `σ` leen lo mismo en los dos pasos anteriores (`sels_of_pid_eq`). Con eso la condición se
   pide una sola vez por ventana.
3. **Las parejas son gratis** (`pairs_of_anchor`). Con el ancla en σ, ningún nodo ni pareja de la estructura puede ser
   fantasma; solo tríos. Lo medí antes de demostrarlo (0 nodos y 0 parejas fantasma en todas las sondas).
4. **H2′**. Un trío es *Helly-fallido* si hay rama de antes por los tres, rama de después por cada pareja y ninguna de
   después por los tres. H2′ pide, para cada uno, un paso λ fuera de los suyos en el que todo nodo `s` alcanzable desde
   los tres deja alguna cara `(y, z, s)` sin rama de antes. El testigo de la regla no forma tríos prohibidos con las
   caras, así que serían caras de la estructura, y la estructura las hace de antes: contradicción.
5. **El pegado** (`glue_peg`). Ver §5.

## 3. Lo medido

| sonda | qué | resultado |
|---|---|---|
| `win_pin_formula.py` | `WinPinFree` (todos los pasos) al fijar ventanas, dos órdenes | 0 fantasmas en `clause_mix`, `clause_mix_sep`, `parity4`, `parity_use`, `chain4_cross` (1 551 ventanas) |
| `… --helly` | la condición de **un** paso | **falla**: por id (1, 19, 2 casos) y con la ventana entera (18 en `chain4_cross`, 4/7 en `parity_use`) |
| `win_pin_witness.py` | cuántos testigos hacen falta | siempre σ y **un** paso más; ninguna ventana necesita dos |
| `win_pin_rule.py` | «λ separa el fantasma» en el grafo de variables | necesaria en lo medido, **no suficiente** (sobrevive en el 11–49 % de los pares) |
| `win_pin_dump.py` | volcado de fantasmas y testigos | «caras sin nodo común en λ» es necesaria; «nodos sin nodo común» es suficiente; todo trío fantasma se refuta por propagación unitaria |
| `win_pin_descent.py` | H2′ sobre los fantasmas | 4 328 de 4 328 al primer nivel |
| `win_pin_h2all.py` | **H2′ tal cual**: todas las familias de ventanas previas, todos los tríos Helly-fallidos | `chain4_cross` 2 448/2 448 (884 familias), `parity_use` 2 784/2 784; las otras tres sin tríos |
| `win_pin_peg.py` | ¿hay λ con `Peg`? | `tree9` (árbol de tres ramas) **516/516**; `chain4_cross` con numeración cruzada 2 048/2 448; `chain4_cross` preprocesada: ningún trío Helly-fallido |

Dos lecturas de la tabla:

* La regla que buscaba al principio («un paso que separa») era el **grafo equivocado**. Lo que funciona es el pegado del
  §5, que mira la ventana fijada y lo que lee cada nodo, no solo el grafo de variables.
* En `chain4_cross`, `Peg` cubre el 84 % de los tríos con la numeración cruzada y **no hace falta** con la numeración del
  preproceso del v228: allí no hay ni un trío Helly-fallido. La localidad de las lecturas es lo que separa los dos casos.

## 4. Lo que la medida me corrigió

Mis dos primeras reglas para elegir el segundo testigo eran de grafo de variables y fallaron al medirlas. El volcado del
§3 enseñó el mecanismo con un trío concreto de `chain4_cross` (ventana `x1 = 0, x3 = 0, x6 = 1`, nodos que leen
`{x1, x2}`, `{x4, x5}`, `{x8, x9}`): `x5 = 0` fuerza `x7 = 1` por c1; con `x2 = 0`, c2 fuerza `x8 = 1`; el nodo de `x9`
lee `x8 = 0`. Los λ que matan son los que leen dos variables de c1 o c2 (el camino de la propagación). De ahí salió el
pegado: no se trata de separar variables sino de que **ninguna región del corte toque lo que leen los tres nodos**.

## 5. El lema de pegado (`ForbidOnGluePeg.lean`)

**Corte** `K`: las variables fijadas en la familia (`KF`; las de las ventanas y la nueva) y las que lee la ventana del
paso λ. **Regiones**: el resto, con las variables de cada cláusula fuera del corte en una sola región (las componentes del
grafo primal sin `K`).

**`Peg`**: (no3) ninguna región toca lo que leen los tres nodos; (two) si toca lo de dos, `y` y `z`, las variables de λ
vecinas de la región las lee `y` o `z`.

**`glue_peg`**: si un nodo `s` de λ fuera alcanzable desde los tres por ramas de `P` (`a_x, a_u, a_w`), se elige una
fuente por región (la rama del único nodo que toca, la de la pareja, o `a_x`), el corte toma los valores comunes, y la
asignación pegada está en `P` (`p0_of_sources`: cada cláusula lee de una sola fuente) y pasa por los tres. Contradice que
el trío sea Helly-fallido. Luego con `Peg` ningún `s` es alcanzable desde los tres (H2 en λ), y vale H2′.

`reader_winNode_of_peg` lo junta con el lector, con `KF` las variables de las elecciones.

## 6. La propuesta: los árboles de cláusulas

### 6.1 El enunciado

**Clase.** `φ` es **Berge-acíclica** si su grafo de incidencia (un vértice por variable y por cláusula, arista si la
variable está en la cláusula) es un bosque: dos cláusulas comparten a lo sumo una variable y no hay ciclos. Incluye
todas las cadenas del v226–v228 y los árboles con ramificaciones.

**Lecturas locales.** Para cada nodo `y`, lo que lee fuera de `K₀` (lo fijado) y fuera de las variables **libres** (las
que solo están en cláusulas tautológicas o en ninguna) cae dentro de un **bloque**: una variable o una cláusula.

**Teorema (a mano).** Si `φ` es Berge-acíclica con lecturas locales, todo trío Helly-fallido de cada ventana tiene un
paso λ fuera de los suyos con `Peg` (con regiones libres). Con las líneas, el lector por nodos de ventana no se atasca.

### 6.2 La demostración

* **Lema A.** Si ninguna región de `G − K₀` toca los tres nodos, se pega sin λ (la rama de la pareja coincide en `K₀`) y
  sale una rama de `P` por los tres. En un trío Helly-fallido los tres bloques están en un mismo árbol `T` de `F − K₀`.
* **Lema B.** Tres vértices de un árbol tienen una **mediana** `m`; quitando `m`, los bloques distintos de `m` quedan en
  ramas distintas. En un bosque, el único camino entre dos ramas de `m` pasa por `m`: quitando sus variables, cada región
  toca a lo sumo un nodo, y `Peg` se cumple (no3 directo, two vacía). Quitar variables de más solo parte más.
* **Caso `m` variable.** λ = cualquier paso cuya ventana lea `m`. Hay `2 + Σ_d (4 − i_d) ≥ 3` (sus dos pasos de variable
  y, en cada cláusula `d` con `m` en la posición `i_d`, los pasos `d.l_{i_d} … d.l₃`). Si son exactamente 3 y el trío los
  ocupa, dos de sus nodos solo leen `m` y la pareja de `P` fija el mismo valor: habría rama de `P` por los tres.
* **Caso `m` cláusula `c'`.** (a) λ = `c'.l₃` si está libre (quita las tres variables). (b) Si un nodo `y` está en
  `c'.l₃` (y lee las tres) y `c'.l₂` está libre: λ = `c'.l₂` quita dos; la región de la tercera variable toca a `y` y a
  lo sumo otro, y sus vecinas en λ las lee `y` (two). (c) Si `y` está en `c'.l₃` e `y'` en `c'.l₂`: λ = un paso de
  variable de la variable `a_i` de `c'` donde cuelga el tercer bloque; el lado de `c'` toca a `y`, `y'`, y `a_i` la lee
  `y` (two).

### 6.3 Cómo conseguir lecturas locales

El mapa actual **no** es local en general: el nodo de una variable lee `{v, v − 1}` y la copia `l₁` de una cláusula lee el
final de la anterior. Tres maneras, de menos a más invasiva:

1. **Renumerar** (como el preproceso del v228) cuando el árbol admite un orden en el que variables consecutivas
   comparten cláusula y cada cláusula empieza por la variable que comparte con la anterior. Comprobado a mano en dos
   árboles pequeños (`scripts/cnf/tree/*_loc.cnf`). No todo árbol lo admite.
2. **Acolchar la fórmula** (`scripts/pad_formula.py`, un preproceso, **sin tocar la máquina**): una variable de relleno
   antes de cada variable real y al final, y una cláusula tautológica `(d ∨ ¬d ∨ d)` antes y después de cada cláusula
   real. Las soluciones son las mismas (por cualquier valor del relleno) y cada ventana lee, fuera del relleno, una sola
   variable o una sola cláusula. El precio: el relleno es libre pero lo leen varios nodos, así que hace falta `Peg` con
   **regiones libres** (la región de una variable libre toma el valor común de los nodos que la leen; las parejas de `P`
   garantizan que coinciden). Sigue siendo Berge-acíclica.
3. **Acolchar el mapa** (cambio en la máquina, Julia y Lean): dos pasos vacíos entre bloques. Es lo más limpio para el
   teorema pero toca toda la aritmética de pasos (`CnfMapBin`) y todas las pruebas que dependen de ella.

Recomiendo la 2: no cambia la máquina, encaja con el preproceso del v228 y el teorema la cubre con una extensión pequeña
de `glue_peg`.

## 7. Plan de formalización

1. **`KF` = las constantes de `P`.** Restablecer `reader_winNode_of_peg` con `KF z := ∀ a b, P a → P b → a z = b z`
   (`hfix` sale por definición; el corte es mayor y `Peg` más fácil). Pequeño.
2. **Regiones libres en `glue_peg`.** Las variables libres toman el valor de cualquier nodo del trío que las lea (todos
   coinciden por las parejas de `P`); las cláusulas tautológicas se satisfacen con cualquier valor. Mediano.
3. **Berge-acíclica y bloques en Lean**: el grafo de incidencia como bosque (una función de padre y una profundidad, o
   «dos cláusulas comparten a lo sumo una variable y no hay ciclos» por un orden), la mediana de tres vértices y el
   lema de la rama única. Es lo más largo.
4. **El teorema del §6** sobre esas piezas, con el recuento de pasos que leen `m` y los tres casos de `c'`.
5. **El acolchado** en Lean (`padCnf`), su corrección (`Renaming` del v228 más variables libres) y que deja lecturas
   locales.
6. **Sondas** en Julia sobre la máquina real con fórmulas acolchadas (la fuerza bruta en Python no llega: el relleno
   multiplica las soluciones por `2^(n+1)`).

## 8. Lo que queda abierto

1. **Las líneas para árboles.** El lector usa `PhantomAtW` (que la máquina construya la línea final sin fantasmas). Está
   demostrado para las clases de los v223–v228 (bloques, dos y tres bloques, cadenas), **no para árboles con
   ramificaciones**. El mismo pegado por regiones es el candidato natural para las líneas (el filtro y el UP piden
   `PhantomFree` de la misma forma), pero no lo he intentado aún.
2. **`Peg` fuera de los árboles.** Con ciclos en el grafo de incidencia (`parity_use`, `clause_mix`), H2′ se cumple en
   lo medido pero `Peg` no la explica sola. Este método pasa toda la información por un corte del tamaño de una ventana;
   es un límite de la prueba, no una medida de la máquina.
3. **Las regiones libres** no están medidas: no hay instancia acolchada con tríos Helly-fallidos al alcance de la fuerza
   bruta.

## Ficheros

| fichero | qué | commit |
|---|---|---|
| `lean/improves_bingo/AbsSatBingo/Model/ForbidOnWinRead.lean` | lector por ventanas como tres elecciones; cadenas | `08045ac` |
| `…/ForbidOnWinPin.lean` | filtro de varios requisitos; `WinReading`; `WinPinFree` | `c5c7f9e`, `b558f66` |
| `…/ForbidOnTwoWitness.lean` | H2, H2′ | `89b9563`, `f0786ce` |
| `…/ForbidOnWinBridge.lean` | el puente | `76faa63` |
| `…/ForbidOnGluePeg.lean` | el pegado | `13de49b` |
| `lean/improves_bingo/scripts/win_pin_*.py` | las sondas del §3 | `299703e` … `ff31253` |
| `lean/improves_bingo/scripts/pad_formula.py`, `scripts/cnf/tree/` | el acolchado; árboles de prueba | `ff31253` |
