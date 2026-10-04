# Verificación para el Autor v228: el preproceso de renumeración

4 de octubre de 2026, rama `reader-stuck`. Continúa el v227. En una frase: **toda cadena de 3-cláusulas, de cualquier
longitud y con cualquier numeración de sus variables, se reescribe (sin cambiar sus soluciones) en una cadena de la clase
`ChainOrdN`, y la espina de la máquina `:on` sobre la reescrita decide la original. Está demostrado en Lean, sin
hipótesis; el preproceso está escrito en Julia y medido.**

> **Estado**: todo compila (`lake build`, 182 trabajos), sin `sorry`; los teoremas solo dependen de `propext`,
> `Classical.choice` y `Quot.sound`. Dos sondas de la máquina seguían en curso al escribir esto, sin fallos en lo
> medido (§5).

## 0. Resumen

| | v227 | v228 |
|---|---|---|
| cadenas cubiertas | numeradas en el orden de la cadena, la de dentro en medio (`ChainOrdN`) | **todas** (`ChainIn`): cualquier numeración, orden de cláusulas y de literales |
| cómo | la máquina tal cual | la máquina sobre la fórmula **preprocesada** |
| resultado | `machineExact_of_chainOrd` | **`spineVerdictOn_pre_iff`**: `SpineVerdictOn (preCnf …) ↔ Satisfiable φ` |
| el preproceso | — | `test_3sat/preprocess_chain.jl` y su gemelo Lean `preCnf` |

## 1. Por qué un preproceso

El v227 demostró la máquina exacta en las cadenas con **lecturas locales**: la variable de dentro de cada bloque de en
medio numerada entre sus dos separadores (`NumLocal`) y como literal de en medio (`LitLocal`). Con la numeración cruzada
eso falla, y `chain6_cross` lo muestra en la máquina: ocho triángulos de más en las llegadas (v223).

Pero las dos condiciones son de **nombres**, no de la fórmula: renombrar variables y reordenar literales y cláusulas no
cambia las soluciones. Así que basta reescribir la cadena antes de dársela a la máquina.

## 2. El preproceso en Julia (`test_3sat/preprocess_chain.jl`)

1. Detecta la cadena: las variables compartidas (separadores) están en dos cláusulas, y las cláusulas forman un camino.
   Si no, devuelve «no es una cadena» y no toca nada.
2. Ordena las cláusulas a lo largo del camino.
3. Numera las variables en ese orden: las de dentro del primer bloque, `s1`, la de dentro del bloque 1, `s2`, …
4. En cada cláusula de en medio pone (separador izquierdo, la de dentro, separador derecho), con los signos de entrada.
5. Escribe el renombrado en líneas `c map viejo nuevo`.

Salidas para las diez cadenas cruzadas medidas: `lean/improves_bingo/scripts/cnf/pre/`. `chain6_cross` preprocesada
resulta ser exactamente `chain6_order`.

## 3. La corrección en Lean (`ForbidOnChainPre.lean`)

* **`Renaming φ φ' f g`**: `f` lleva las variables de `φ` a las de `φ'`, `g` las devuelve en las variables usadas, cada
  cláusula de `φ'` es la imagen literal a literal de una de `φ` (y al revés). El orden de las cláusulas no cuenta.
* **`satisfiable_iff_of_renaming`**: `Satisfiable φ ↔ Satisfiable φ'`, con `a ∘ g` en un sentido y `a' ∘ f` en el otro.
* **`spineVerdictOn_iff_of_pre`**: si la preprocesada está en `ChainOrdN`, la espina sobre ella decide la original.
* La instancia: `chain6X` (`chain6_cross`), su preprocesada `chain6P`, el renombrado `f6, g6` (las líneas `c map`) y
  **`spineVerdictOn_pre_chain6X`**, todo comprobado con `decide`.

## 4. El teorema general (`ForbidOnChainPreGen.lean`)

* **`ChainIn φ n zone sv zi e0a e0b eLa eLb cl`**: una cadena de `n` bloques (`n` cualquiera), una cláusula por bloque
  (`cl p`, y toda cláusula de `φ` es una de ellas), la de en medio `p` con exactamente sus dos separadores y su variable
  de dentro `zi p` (distintas), y a lo sumo dos variables de dentro en los bloques de los extremos.
* **La construcción** (la misma de Julia): `fPre` (el bloque `0` a `0, 1`; el separador `i` a `2i`; la de dentro del
  bloque `p` a `2p + 1`; el último a `2n − 1, 2n`), `gPre` (su inversa), `preCl` (las cláusulas de en medio en el orden
  separador, de dentro, separador), `preCnf`, y la zona nueva `zoneO`.
* **`renaming_pre`**, **`bounded_pre`**, **`chainOrd_pre`**, y de ahí **`spineVerdictOn_pre_iff`** y
  **`machineExact_pre`**.
* **`chainIn_chain6X`**: `chain6_cross` está en la clase de entrada, y **`spineVerdictOn_pre_chain6X_gen`** la decide por
  la construcción general.

## 5. Medidas

| sonda | antes del preproceso | después |
|---|---|---|
| `probe_split.jl` (el corte estático), cadenas cruzadas de 4 a 12 bloques | fallaba en algunos lados (37 de 45 con 10 bloques, 54 de 66 con 12) | **todos los lados** |
| máquina, `chain4_cross` | exacta | exacta (94 llegadas) |
| máquina, `chain5_cross` | exacta | exacta (116 llegadas) |
| máquina, `chain6_cross` | **8 triángulos fuera** en llegadas | es `chain6_order`: exacta (v223) |
| máquina, `chain7_cross` | exacta (v227) | en curso: 0 fuera en 115 llegadas |
| máquina, `chain8_order` | — | en curso: 0 fuera en 110 llegadas; 6 estados sin juzgar (pasan del tope de 50 000 camarillas) |

Lo que cambia, en la máquina real, es lo que predice el teorema: la instancia que fallaba (`chain6_cross`) sale exacta
tras el preproceso, y ninguna preprocesada tiene fallos en lo medido.

## 6. Trucos técnicos de esta vuelta

1. **Las condiciones del v227 son de nombres**: se consiguen renombrando, sin tocar las soluciones.
2. **El renombrado no pide el orden de las cláusulas**: `Renaming` pide «existe una cláusula imagen», así que reordenarlas
   no cuesta nada.
3. **`zoneO ∘ fPre = zone`** (`fPre_zone`): la zona nueva de la numeración nueva es la vieja, y la pertenencia de cada
   cláusula a su bloque pasa reescribiendo.
4. **`zoneO_cases`**: la zona nueva en cinco casos aritméticos; cardinales y separadores salen con `rcases … <;> omega`.
5. **`litOf`**: el literal de una variable en su cláusula; con las tres variables distintas, `litOf c l.v = l`, que da el
   sentido inverso del renombrado sin perder signos.
6. **`a ∘ g` y `a' ∘ f`**: la semántica no acota las asignaciones, así que la corrección del renombrado son dos
   composiciones.

## 7. Lo que queda abierto

1. **La forma de las cadenas.** `ChainIn` pide una cláusula por bloque, con sus dos separadores y una variable de dentro.
   Bloques con varias cláusulas, sin variable de dentro o con variables repetidas en una cláusula quedan fuera, aunque
   Julia los detecta.
2. **El preproceso en la máquina.** Hoy es una herramienta aparte (`preprocess_chain.jl`) y una construcción Lean
   (`preCnf`); integrarlo en `SatMachine` y en el modelo Lean del driver.
3. **Más allá de las cadenas.** Árboles de bloques y anchura mayor, con las mismas piezas: lecturas locales y regiones
   contadas por lecturas.
4. **Terminar las dos sondas en curso** y anotarlas aquí.

## 8. Plan

1. Terminar `chain7_cross` preprocesada y `chain8_order`.
2. Ampliar `ChainIn` a bloques con varias cláusulas, que es la forma común en fórmulas reales.
3. Un primer paso hacia árboles: un bloque con tres separadores, y qué pide el lado que se ramifica.

## Ficheros

| fichero | qué es | commit |
|---|---|---|
| `julia/improves_bingo/test_3sat/preprocess_chain.jl` | el preproceso | `1099d55` |
| `lean/improves_bingo/scripts/cnf/pre/` | las cadenas preprocesadas | `1099d55` |
| `lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainPre.lean` | `Renaming`, `satisfiable_iff_of_renaming`, la instancia `chain6_cross` | `1099d55` |
| `lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainPreGen.lean` | `ChainIn`, `preCnf`, `spineVerdictOn_pre_iff` | `29d0c1d` |
| `julia/improves_bingo/test_3sat/output_probes/exact3_pre/` | la máquina en las preprocesadas | `0f47716` |
