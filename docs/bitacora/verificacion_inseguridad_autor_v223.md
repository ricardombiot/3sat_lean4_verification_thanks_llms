# Verificación para el Autor v223: las primeras clases con cláusulas de tres literales, y lo que la máquina cumple de verdad

2 de octubre de 2026, rama `reader-stuck`. Continúa el v222. En una frase: **la máquina con tríos es exacta y el
lector no se atasca, sin ninguna hipótesis, en tres clases nuevas de fórmulas con cláusulas de tres literales
distintos** (bloques sueltos, dos bloques que comparten una variable, tres bloques en cadena), y una medida en la
máquina ha corregido el enunciado que se perseguía: la exactitud «fuerte» del v222 no vale en toda fórmula, y la
inducción no la necesitaba.

## 0. Dónde estamos

| | v222 | v223 |
|---|---|---|
| clases sin hipótesis | forma 2-CNF | además: `Blocks3`, `Sep2`, `Chain3` (cláusulas de tres literales distintos, con variables compartidas) |
| técnica | mayoría | parche; pegado en la variable compartida; dos testigos encadenados |
| cómo se demuestra una clase | una vez por situación (filtro, UP, lectura) | una sola vez, sobre familias locales (`LocPair`) |
| ¿`PhantomAt` vale en toda fórmula? | no se sabía | **no**: medido en `chain6_cross` (ocho triángulos de más en llegadas) |
| qué necesita la inducción | `PhantomAt` | `PhantomAtW`, más débil; equivalencia `machineExactW_iff` |
| sonda | `probe_exact3.jl` | además `probe_exactw.jl` (cada llegada contra la entrada que forma) |

Lean: cinco módulos nuevos (`ForbidOnBlock`, `ForbidOnWeak`, `ForbidOnSep`, `ForbidOnLocal`, `ForbidOnChain`),
2 562 líneas, `lake build` completo en verde (149 trabajos), sin `sorry`, axiomas estándar
`[propext, Classical.choice, Quot.sound]`. `ForbidOnHelly` cambió en un lema (`snd3_upOnG`).

## 1. Cómo se llegó aquí

El v222 dejó una pregunta sobre fórmulas: ¿toda 3-CNF está libre de familias fantasma? Mi primera respuesta fue un
argumento de fuera (anchura acotada) para decir que probablemente no. Ricardo lo señaló como sesgo: era un veredicto
sin demostración de que ese argumento se aplicara a su máquina. Desde ahí el trabajo fue el contrario: demostrar clase
a clase, y dejar que la prueba y la máquina digan dónde se para.

* El parche dio la primera clase con cláusulas de tres literales (§2).
* Al atacar las variables compartidas, la condición de un paso dejó de bastar con solo dos cláusulas (§3), y el
  análisis a mano de una cadena más larga dio un candidato concreto. Ricardo pidió comprobarlo **en la máquina**: se
  confirmó (§6).
* Esa medida mostró que la máquina cumple algo más débil que lo que se intentaba demostrar, y que con eso basta (§6).
* Con esa corrección se formalizaron dos y tres bloques en cadena (§3, §5).
* Un segundo candidato mío, para cuatro bloques, **resultó erróneo** al medirlo (§7.3).

## 2. El parche: bloques sueltos (`ForbidOnBlock`)

La mayoría del v222 construye la rama que falta votando entre tres. Aquí se construye **parcheando**: se toma la rama
`a0` que pasa por los tres nodos y se le cambian las variables de un conjunto `B` por las de una de las tres ramas que
pasan por dos nodos y por el nodo fijado.

* `helly4_of_patch` (sin máquina y sin fórmula concreta): si `B` no tiene tres variables distintas además de la del
  paso fijado, y parchear en `B` una rama de `P0` con una de `P` da una rama de `P`, vale la condición de un paso.
  La cuenta: si ninguno de los tres parches pasa por los tres nodos, cada rama discrepa de `a0` en una variable de `B`
  que las otras dos leen igual; son tres variables distintas.
* `Blocks3 φ E`: cada cláusula cae entera en un bloque de a lo sumo tres variables. `ReadOnce φ`: dos cláusulas
  distintas no comparten variable (`blocks3_readOnce`).
* `spineVerdictOn_iff_of_blocks`, `machineExact_of_blocks`, `reader_on_blocks` (y las tres `_readOnce`).

Incluye fórmulas insatisfacibles (las ocho cláusulas sobre tres variables).

## 3. La composición: dos bloques que comparten una variable (`ForbidOnSep`)

Con `(p ∨ q ∨ s) ∧ (¬s ∨ r ∨ v)` la condición de un paso ya falla: los nodos `p = 0`, `q = 0`, `r = 0` van juntos en
una rama, y dos a dos con `v = 0`, pero no los tres con `v = 0`. Lo cierra la regla **en el paso de `s`**, y la prueba
es un argumento de dos pasos sobre la estructura cerrada (`PhantomFree`), sin máquina:

* `tri_glue`: el triángulo tiene un testigo en un paso que lee `s`; si sus tres caras son de ramas de `P`, las tres
  leen `s` igual, y con `s` fijada los dos lados no se ven: se elige una rama para cada lado (`three_cover`) y se
  pegan (`glue`).
* `tri_lam`: las caras ya tienen un nodo que fija `s`; basta el parche del lado derecho.
* `phantomFree_sep` junta los dos pasos. `SepData φ v s L Rr` y `Sep2 φ` son lo que se pide a la fórmula.
* `spineVerdictOn_iff_of_sep2`, `machineExact_of_sep2`, `reader_on_sep2`; `sep2_of_blocks3` (los bloques la cumplen)
  y `machineExact_twoShare` para `(x0 ∨ x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ x4)`.

## 4. Las familias son locales (`ForbidOnLocal`)

En el filtro, el UP y la lectura, las familias de ramas se definen con condiciones sobre un paso cada vez: una ventana
prohibida (el tercer paso de una cláusula) y nodos fijados. `LocPair φ P0 P σ` lo recoge (`sub`, `loc`, `anc`,
`same`) y da la herramienta de todo lo que sigue:

* `p0_of_sources`, `p_of_sources`: una rama se construye **por fuentes**: cada variable toma su valor de alguna rama,
  y las tres variables de cada cláusula, de una misma rama.
* `locPair_filter`, `locPair_up`, `locPair_read`: las tres situaciones.

Una clase nueva se demuestra una vez, sobre `LocPair`.

## 5. Tres bloques en cadena (`ForbidOnChain`)

Bloques `A ∪ {s1}`, `{s1} ∪ M ∪ {s2}`, `{s2} ∪ C`. Hacen falta dos testigos encadenados y el argumento sube por
niveles; en cada nivel los triángulos tienen fijada una variable compartida más.

| `v` en el último bloque, o `v = s2` | `v` en el bloque de en medio |
|---|---|
| 1. triángulos con un nodo que lee `s2` (`tri_lam_any`, o el ancla) | 1. triángulos con nodos en los pasos de `s1` y `s2` (`chain_both`) |
| 2. con un nodo que lee `s1` (`chain_mid`) | 2. con un nodo que lee `s2` (`chain_near`) |
| 3. todos (`chain_far`) | 3. todos (`chain_allmid`) |

En todos los niveles la rama final es `glue3` (una fuente por bloque), y es de `P` (`glue3_P`) si dos fuentes vecinas
leen igual la variable que comparten. La cuenta sobre las tres caras está en `Faces.pick'`: o una de las tres ramas
sirve, o las ventanas del triángulo ya leen tres variables distintas, y entonces la variable compartida está fijada.

* `ChainData φ v s1 s2 A M C`, `Chain3 φ` (cada variable: datos de cadena o de separador).
* `phantomAt_of_chain3`, `hRead_of_chain3`; `spineVerdictOn_iff_of_chain3`, `machineExact_of_chain3`,
  `reader_on_chain3`; `machineExact_threeChain` para `(x0 ∨ x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ x4) ∧ (¬x4 ∨ x5 ∨ x6)`.

Las tres clases valen **con cualquier numeración de las variables**.

**Dónde se acaba el método.** Con cuatro bloques, tras fijar una variable compartida queda a un lado una cadena de
dos bloques con variables fijadas por las tres ventanas, y haría falta un testigo vecino de cuatro nodos. Eso es un
límite de esta prueba, no una medida de la máquina (§7.3).

## 6. Lo que la máquina cumple: las llegadas solo deben ramas de la unión (`ForbidOnWeak`)

`PhantomAt` pide, en el UP, que todo objeto de la llegada `k → d` sea de una solución que elige `k` y `d`. En
`chain6_cross` (seis cláusulas en cadena, 13 variables, numeración cruzada) la máquina no lo cumple: hay llegadas con
ocho triángulos de nodos viejos que ninguna solución de esa llegada recorre. Por `machineExact_iff`, esa fórmula
incumple `PhantomAt`.

La inducción nunca usó tanto. Una llegada solo sirve para formar la entrada `d` de la línea siguiente, y a la entrada
le basta que sus objetos sean de soluciones que eligen `d`, vengan del remitente que vengan.

* `snd3_upOnG` (`ForbidOnHelly`): el UP conserva el invariante hacia cualquier familia que contenga las ramas de la
  llegada. Los objetos con un nodo de la fila nueva son siempre de la propia llegada.
* `PhantomAtW φ T`: como `PhantomAt`, con la condición del UP hacia `SolE φ (T + 1) d`. Es más débil
  (`phantomAtW_of_phantomAt`).
* `spineVerdictOn_iff_of_phantomW`, `reader_onW` y la equivalencia **`machineExactW_iff`**:
  `MachineExactW φ ↔ ∀ T ≥ 1, PhantomAtW φ T`.

También están con la condición débil la escalera de niveles (`hypsTriKeep_of_phantomAtW`,
`hypsNodeKeep_of_phantomAtW`) y la equivalencia del lector (`readerExactW_iff`).

## 7. Comprobaciones en la máquina (`FORBID = :on`, con tope de memoria de 3,5 GB)

### 7.1 `probe_exact3.jl`: objetos fuera de toda camarilla del propio estado

| fórmula | var / cl | llegadas: triángulos fuera | cima / filtro / uniones / final | camarillas finales | soluciones | tiempo / pico |
|---|---|---|---|---|---|---|
| `chain6_cross` | 13 / 6 | **8** de 15 579 811 | 0 | 3 264 | 3 264 | 510 s / < 3,5 GB |
| `chain6_order` | 13 / 6 | 0 | 0 | 3 264 | 3 264 | 564 s / 961 MB |
| `chain4_cross` | 9 / 4 | 0 de 2 247 670 | 0 | 280 | 280 | 31 s / 545 MB |

`chain6_cross` y `chain6_order` son la misma fórmula con las variables renombradas: los triángulos de más dependen
solo de la numeración. Nodos y aristas salen limpios en todos los grupos, y los triángulos con un nodo en la cima
también. Ningún callejón en ningún estado.

### 7.2 `probe_exactw.jl`: cada llegada contra sus camarillas y las de su hermana a la misma entrada

| fórmula | llegadas | triángulos fuera de las propias | fuera también de la hermana (`MachineExactW` pide 0) | con / sin hermana | tiempo / pico |
|---|---|---|---|---|---|
| `chain6_cross` | 138 | 8 | **0** | 100 / 38 | 243 s / 1,26 GB |
| `chain4_cross` | 94 | 0 | 0 | 68 / 26 | 21 s / 617 MB |

En `chain6_cross` la máquina incumple la exactitud fuerte y cumple la débil.

### 7.3 Un candidato mío que era erróneo

Tras demostrar tres bloques, el análisis a mano me dio un candidato para cuatro (`chain4_cross`) en el que el
triángulo de más llegaría a la entrada. La medida lo desmiente: la máquina es exacta ahí en todos los estados, también
en el sentido fuerte. El error fue no seguir un segundo nivel de la regla (la cara que yo daba por viva la mata el
testigo de la cima). Consecuencia: que la prueba actual se pare en tres bloques no dice que la máquina falle en
cuatro.

### 7.4 Lo que no se pudo comprobar

`scripts/helly_formula.py --phantom-all` sobre `chain6_cross` no terminó en más de media hora (13 variables, Python
puro) y se paró. La condición sobre la fórmula no está comprobada ahí por fuerza bruta; lo que hay es la medida en la
máquina.

## 8. Lo que es falso (para no volver)

* **«Toda 3-CNF cumple `PhantomAt`»**: falso, por `chain6_cross` (medido) y `machineExact_iff` (demostrado).
* **La condición de un paso (`HellyAt`) con variables compartidas**: falla ya con dos cláusulas que comparten una.
* **Mi candidato de cuatro bloques**: erróneo (§7.3).
* **«La exactitud de cada llegada es necesaria»**: no; basta la de la unión (§6).

## 9. Lo que no se sabe

* Si toda 3-CNF cumple `PhantomAtW`. Solo hay una fórmula medida donde la fuerte falla, y ahí la débil se cumple.
* Si la máquina es exacta en cadenas de cuatro y cinco bloques con otras numeraciones (una medida de cuatro: sí).
* Cómo demostrar cuatro bloques: el método de niveles no llega.
* El efecto en el lector de los triángulos de más de `chain6_cross` (no medido; el estado final es exacto).
* La condición débil en las paridades y `clause_mix` (allí la fuerte ya salió exacta, así que la débil también).

## 10. Plan

1. Medir `MachineExactW` con `probe_exactw.jl` en cadenas de cinco y seis con varias numeraciones, para saber si la
   condición débil aguanta donde la fuerte cae.
2. Hecho tras cerrar el informe: `readerExactW_iff`.
3. Buscar la prueba de cuatro bloques apuntando a `PhantomAtW`, que es lo que la máquina cumple.

## Ficheros y teoremas

| fichero | líneas | lo principal |
|---|---|---|
| `Model/ForbidOnBlock.lean` | 312 | `helly4_of_patch`, `Blocks3`, `ReadOnce`, `machineExact_of_blocks`, `reader_on_blocks` |
| `Model/ForbidOnWeak.lean` | 280 | `PhantomAtW`, `phantomAtW_of_phantomAt`, `machineExactW_iff`, `reader_onW` |
| `Model/ForbidOnSep.lean` | 687 | `phantomFree_sep`, `SepData`, `Sep2`, `machineExact_of_sep2`, `machineExact_twoShare` |
| `Model/ForbidOnLocal.lean` | 320 | `LocPair`, `p0_of_sources`, `p_of_sources`, `locPair_filter` / `_up` / `_read` |
| `Model/ForbidOnChain.lean` | 963 | `glue3_P`, `ChainData`, `Chain3`, `phantomAt_of_chain3`, `machineExact_threeChain` |
| `Model/ForbidOnHelly.lean` | — | `snd3_upOnG` (el UP hacia cualquier familia que contenga las ramas de la llegada) |
| `test_3sat/probe_exactw.jl` | — | la sonda de `MachineExactW` |
| `scripts/cnf/chain6_cross.cnf`, `chain6_order.cnf`, `chain4_cross.cnf` | — | las cadenas medidas |

Commits: `9b54f67` (bloques), `7fcbf7d` (condición débil), `d592d88` (sonda), `0031c4f` (dos bloques), `c630405`
(familias locales y tres bloques). La tabla de sincronía Julia/Lean está en `docs/plans/lean_bingo.md`.
