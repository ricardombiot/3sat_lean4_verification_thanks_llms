# Verificación para el Autor v220: caen `PrevCut` y `CrossCut`, `TopSideAt` sin pins queda demostrada, y una propuesta para la parte con pins

1 de octubre de 2026, rama `reader-stuck`. Continúa el v219. En una frase: las dos hipótesis de las que colgaba el
veredicto (`PrevCut` y `Star4At`) resultan **falsas en instancias `v7`**; la prueba se ha rehecho para no depender de
ellas; el caso sin pins de `TopSideAt` está **demostrado**; y lo que queda abierto es `TopSideAt` con pins, para lo que
se propone un cambio de la máquina (§7).

## 0. Dónde estamos

| | v219 | v220 |
|---|---|---|
| veredicto | `spineVerdictOn_iff_of_prev4` bajo `PrevCut` + `Star4At` | `spineVerdictOn_iff_of_topPins` bajo `TopSideAt` **solo con pins** |
| `PrevCut` | medida sin fallos (6 instancias, hasta `v6`) | **falsa** en 2 de 12 instancias `v6`/`v7` |
| `CrossCut` | medida sin fallos | **falsa** en 1 de 12 |
| `Star4At`, `StarTriAt` | medidas sin fallos | **falsas** en la misma instancia, sin pins y con pins |
| `TopSideAt` sin pins | hipótesis | **demostrada** (`topSideAt_nil_line`) |
| `TopSideAt` con pins | hipótesis | hipótesis; 0 cimas muertas de unas 2 100 con pins en tres `v7` |

Todo lo de Lean compila con `lake build`, sin `sorry` y con los axiomas estándar. Ocho módulos nuevos, unas 3 950
líneas.

## 1. Lo que se hizo sobre `PrevCut`, antes de saber que era falsa

El trabajo es correcto y parte de él se reutiliza, pero su objetivo ha muerto (§3).

### 1.1 Herencia (`ForbidOnInherit`)

* **`up_forbid` es completo** (`upOn_face_parent`, `arrOn_face_parent`): una cara `(t, x, y)` de una cima nueva que no
  está prohibida en la llegada la sostiene un padre de `t` en el remitente. Es el contrapositivo de la regla del UP,
  más que el review solo añade tríos.
* **La base muerta de una unión es la de un lado** (`deadBase_joinOn`, con `tF_joinOn_inv`: los tríos del join los
  cortan los dos lados).
* **`prevCut_inherit`**, **`hPrevCut_succ`**: `PrevCut` de una línea y `HPrevNew` de la siguiente dan `PrevCut` de la
  siguiente. `HPrevNew` = `PrevCut` solo para las bases que la entrada no tenía ya muertas bajo una cima suya.

### 1.2 El residuo, medido (`probe_prevnew.jl`, 7 instancias, todas las llegadas)

| clase | bases | |
|---|---|---|
| nacimiento (ningún padre sostiene las tres caras) | 3 474 | 90 %; siempre exactamente dos padres |
| herencia | 322 | solo en `v5_c20_i1` y `v6_c26_i2` |
| salvedad (un nodo en la cima de la línea anterior) | 75 | las mismas dos instancias |
| caso C (la base no estaba prohibida en la entrada) | 0 | |

### 1.3 La división (`ForbidOnHi`) y la forma normal del nacimiento (`ForbidOnBirth`)

* **`prevCut_hi`**: bajo `HNoRule`, toda base con un nodo `q` en la cima de la línea anterior. Las entradas de otra
  clave no tienen a `q`; la de su clave tiene la base prohibida, porque el sostén de la arista opuesta es hijo de `q`
  (`AdjPar`), luego es de su lado, y el join habría prohibido su cara.
* **`HNoRule`**: una llegada no prohíbe un triángulo viejo que su entrada no tuviera prohibido. **Sin restricción es
  falsa** (16 triángulos en `v6_c26_i1`, 12 en `v6_c26_i5`, 160 en `set011221_2004_i3_v7_c27`, todos bajos y con una
  cima de dos caras vivas). Quedó restringida a los dos casos que usa la prueba (base muerta bajo una cima de la
  llegada; triángulo con un nodo en la cima de la entrada), sin fallos en lo medido.
* **`birth_pattern`** (sin hipótesis): una base muerta que la entrada ya tiene prohibida y que ninguna cima suya
  sostiene entera tiene dos padres distintos `pf`, `ph`; `pf` sostiene las dos caras con un nodo `v` y tiene escrito
  el trío con la arista opuesta `u–w`; `ph` sostiene `(u, w)`. Piezas: `holdsFace_down` (una cara sostenida por una
  cima de una entrada baja a la entrada que creó esa cima), `holder_gparent_mem` y el palomar `pigeon3` (una línea del
  mapa bin tiene como mucho dos entradas, así que una cima tiene como mucho dos padres).
* **El nacimiento por dentro** (`probe_birth.jl`, 3 474 casos, 7 instancias): el patrón es siempre el del teorema, y
  dos líneas atrás el corte es estructural, sin tríos: la entrada del abuelo de `pf` no tiene la arista `u–w` y la del
  abuelo de `ph` no tiene vivo a `v` (3 031 de 3 031; las otras 443 tienen un nodo en la cima de la línea anterior).
  Los dos enunciados sueltos, sin el contexto de la base, son falsos (`probe_topback.jl`).

## 2. `Star4At` en el paso de los padres (`ForbidOnSplit`)

Independiente de `PrevCut`, y se reutiliza. Sin hipótesis y sin usar que la base esté viva:

* **`tetra_parent_or_split`**: en el paso de los padres de la cima, o un padre completa el tetraedro (`Wit4`), o la
  cima tiene dos padres complementarios (`ParSplitAt`): uno con todas sus caras vivas salvo una, otro que sostiene esa
  cara sin completarlo. Es la misma forma que el nacimiento, vista en la unión fijada.
* **`star4At_of_low_noSplit`** y su recíproco **`noParSplit_of_star4`**.

Piezas: `fix_witness` (los testigos del punto fijo, en el cierre simétrico) y `unionParent_gparent`.

## 3. Los contraejemplos

### 3.1 El aviso

Los triángulos que la regla prohíbe en una llegada (`probe_rulenew.jl`, `v6_c26_i1`) tienen exactamente el patrón del
nacimiento, y la entrada que los envía los tenía **abiertos**. Si uno sobreviviera bajo la cima de la llegada
siguiente, sería una base de `PrevCut` con una entrada de la línea anterior sin cortarla. En `v6_c26_i1` no llega a
pasar: en las 32 llegadas siguientes el triángulo se rompe.

### 3.2 La medida en `v7` (`probe_prevbig.jl`, `FORBID=:on`, todas las llegadas)

La sonda procesa línea a línea y solo retiene dos líneas de envíos (pico por debajo de 1,2 GB; las anteriores morían
en `v7` con 4 GB).

| instancia | `PrevCut` abiertas / bases | `CrossCut` abiertas / bases | prohibidos por la regla |
|---|---|---|---|
| `v6_c26_i1` (UNSAT) | 0 / 520 | 0 / 471 | 16 |
| `v6_c26_i3` | 0 / 1 736 | 0 / 1 204 | 0 |
| `v6_c26_i4` | 0 / 222 | 0 / 273 | 0 |
| `v6_c26_i5` | 0 / 2 841 | 0 / 1 486 | 12 |
| `v6_c26_i6` (UNSAT) | 0 / 4 854 | 0 / 3 152 | 0 |
| `set011221_2004_i1_v7_c27` | 0 / 18 570 | 0 / 10 266 | 0 |
| `set011221_2004_i2_v7_c27` | 0 / 20 547 | 0 / 18 360 | 0 |
| `set011221_2004_i3_v7_c27` | **24** / 18 633 | **24** / 12 787 | 160 |
| `v7_c30_i1` (UNSAT) | 0 / 3 308 | 0 / 1 370 | 0 |
| `v7_c30_i2` | **16** / 42 574 | 0 / 23 187 | 16 |
| `v7_c30_i3` (UNSAT) | 0 / 18 871 | 0 / 15 608 | 0 |
| `v7_c30_i4` | 0 / 19 071 | 0 / 17 007 | 0 |

Las dos `v8_c30` se cortaron por el tope de 45 min sin salida.

### 3.3 Qué pasa

La regla prohíbe una base en un solo linaje; la otra llegada la tiene abierta; el join reinicia los tríos y conserva
solo los que cortan los dos lados; **la base revive en la unión**. Formalizado: `revive_sender_open` (una base
prohibida en la llegada de una entrada y viva en la unión fijada es un triángulo sin prohibir en la otra entrada).

Consecuencia: los veredictos bajo `PrevCut` o `CrossCut` (`_prev4`, `_cross4`, `_sender4`, y los de este informe
`_new4`, `_lo4`, `_two4`) tienen hipótesis falsas en esas instancias y allí no dicen nada.

## 4. El arreglo de la prueba (`ForbidOnStarD`, `ForbidOnFam`, `ForbidOnApart`)

### 4.1 `star_coreD`

`star_core` pedía (`hlow1`) que una base prohibida en el lado estuviera prohibida en la unión; eso salía de
`CrossCut`. En `star_coreD` la familia de la cima lleva sus propios tríos: los de la unión fijada **y las bases
prohibidas en su lado**. Desaparece `hlow1`. A cambio, los testigos tienen que esquivar esas bases:

| | condición |
|---|---|
| `hface` | cada cara viva `(a, b, t)` tiene en cada paso un testigo bueno `s` de la unión fijada con `(a, b, s)` sin prohibir también en el lado |
| `hbase` | cada base viva en la unión fijada y sin prohibir en el lado, o no está en los tríos del lado fijado, o tiene en cada paso un nodo que completa el tetraedro con sus tres caras nuevas sin prohibir en el lado |

Veredicto: `spineVerdictOn_iff_of_starD` bajo `HypsStarDOn`.

### 4.2 Lo que se sabe de la hipótesis nueva

* **Es más débil que las anteriores**: `hypsStarDOn_of_cross4` (`HypsCross4On ⟹ HypsStarDOn`).
* **En una cima sin bases revividas es `Star4At`** (`starD_of_noRevive`).
* **En el paso de los padres es gratis** (`starD_of_low`): los nodos de ese paso son de un solo lado, así que un
  triángulo con uno de ellos prohibido en el lado lo guarda el join. `starDAt_of_low_noSplit`: basta la parte por
  debajo del paso de los padres más la ausencia de padres complementarios.
* **Las dos primeras líneas, sin hipótesis**: `AdjApart` (dos vecinos distintos están en pasos distintos, invariante
  de la máquina) hace trivial `StarDAt` en una unión de tres pasos (`starDAt_of_le3`, `hStarDOn_line1`). Veredicto
  `spineVerdictOn_iff_of_starDLowOnly`.
* **No se puede debilitar por este camino**: `star_coreD_fam` y `hface_of_sideFace` dicen que, dada `hbase`, `hface`
  equivale a «las caras de la cima viven en su lado fijado», que es más fuerte que la conclusión que se busca. Los
  únicos testigos que se saben construir son los de un punto fijo: el de la unión no sabe nada de los tríos del lado,
  y el del lado fijado solo existe si la cara ya vive en él.

## 5. `TopSideAt` sin pins, demostrada (`ForbidOnNoPin`)

**`topSideAt_nil_line`**: en un join de dos llegadas de la máquina, toda cima viva de la unión revisada está viva en un
lado revisado. Sin hipótesis.

* **`TopCT g`**: toda cima viva del estado sin revisar está en una camarilla que esquiva los tríos de `g`. Invariante:
  - filtro (`topCT_filterAllOn`): si mata algo, el estado filtrado es el fijado y sirve `TopAt`, que ya era invariante
    de la línea; si no, la camarilla de la entrada cumple el requisito sola (`filterRequire_noVictims`);
  - UP (`topCT_upOn`): la cima nueva tiene un padre vivo (`exists_rowParent`) y su camarilla se alarga (`ct_upOn`);
  - join (`topCT_joinOn`).
* Una camarilla que esquiva los tríos sobrevive a cualquier review (`ct_pinOn`).
* Invariante auxiliar que no estaba para la máquina con tríos: `DocsAlive` (`docsAlive_reviewOn`, `_upOn`, …).

Con eso el veredicto solo necesita su hipótesis **con pins**:

| veredicto | hipótesis (solo para listas de pins no vacías) | estado en lo medido |
|---|---|---|
| `spineVerdictOn_iff_of_topPins` | `TopSideAt` | sin fallos; es la mínima |
| `spineVerdictOn_iff_of_starDPins` | las dos condiciones de `star_coreD` | sin fallos |
| `spineVerdictOn_iff_of_starTriPins` | `StarTriAt` | **falsa** en `set011221_2004_i3_v7_c27` |

## 6. Las medidas con pins (`probe_topdead.jl`)

Mide, en cada join y para cada lista de pins, sobre cada cima viva de la unión fijada: si la cima vive en su lado
fijado (`TopSideAt`); las bases que reviven; si cada cara viva es un triángulo sin prohibir del lado fijado
(`SideFace`); y, en las cimas con alguna base revivida, las condiciones de `star_coreD`. Lleva contadores aparte para
las uniones con pins.

**Un aviso sobre el muestreo.** Los pins de caminos largos del mapa dejan la unión fijada inválida casi siempre (457 de
480 intentos en `set011221_2004_i3_v7_c27`), así que las primeras tandas medían sobre todo el caso sin pins. Con
caminos cortos (uno a tres pasos, seis muestras por join):

| instancia | uniones con pins | cimas | muertas en su lado | caras fuera del lado fijado | bases revividas con pins |
|---|---|---|---|---|---|
| `set011221_2004_i3_v7_c27` (108 de 120 joins) | 375 | 781 | 0 | 0 de 1 160 869 | 24, en una unión |
| `v7_c30_i1` (final) | 339 | 684 | 0 | 0 de 949 356 | 0 |
| `v7_c30_i2` (107 de 142 joins) | 355 | 737 | 0 | 0 de 1 218 141 | 0 |

En la unión con pins que tiene 24 bases revividas (y en la misma unión sin pins):

| | resultado |
|---|---|
| `StarTriAt` (base viva en la unión fijada y prohibida en el lado fijado) | falla en las 24 |
| `Star4At` (celdas sin testigo con los tríos de la unión sola) | falla en 792 = 24 × 33 |
| condiciones de `star_coreD`: aristas, caras, bases | 0 de 286 104, 0 de 279 188, 0 de 6 021 756 |
| la cima, en su lado fijado | viva |

Límites: son tres instancias; dos de las tres tandas no han terminado al cerrar este informe; fuera de las cimas con
bases revividas, `hbase` se reduce a `Star4At`, que en `v7` no está medida.

## 7. Propuesta: cuartetos anclados en la cima

**Es una propuesta razonada. No está demostrada ni implementada.**

### 7.1 Por qué `TopSideAt` con pins no es un teorema de la máquina actual

Dado lo que ya es invariante de la línea, `TopSideAt` con pins `R` equivale a que el review fijado sea exacto en la
unión: toda cima viva de la unión fijada está en una camarilla de un lado que esquiva sus tríos y cumple todos los
pins. Sin pins bastaba una camarilla cualquiera por la cima (§5). Con `k` pins hace falta una que pase además por los
`k` colores fijados, y eso no lo da ningún invariante actual.

El motivo de fondo es que **un trío prohibido es un hecho relativo al linaje** («esta base está muerta dado el color
`ka` del paso anterior») que la máquina guarda como absoluto. El join solo conserva los tríos que cortan los dos
lados. Por eso el lado fijado sabe más que la unión fijada, y nada impide por lógica una cima viva en la unión que su
lado mataría. En lo medido no ocurre.

### 7.2 El único momento con pérdida

Un trío de un solo lado **que no contiene ningún nodo exclusivo de ese lado**, en un join.

Si contiene uno (una cima del lado, o una cima del remitente), el otro lado lo corta por no tener ese nodo, el join lo
guarda, y desde ahí lo cortan todas las entradas de la línea y persiste. Las dos piezas están demostradas: el lema
`excl` de `starD_of_low` y `lineCut_advance`.

Lo que se pierde es, por tanto, un hecho de cuatro nodos: «esta base está muerta bajo las cimas de este lado».

### 7.3 El cambio

| dónde | hoy | propuesta |
|---|---|---|
| **join** | un trío muerto en un solo lado se cae | se convierte en **cuartetos** `(t, x, y, z)`, uno por cada cima `t` de ese lado vecina de los tres |
| **UP** | `up_forbid` hereda tríos: `(n, w, r)` si todos los padres cortan `(p, w, r)` | además hereda cuartetos: `(n, x, y, z)` si todos los padres cortan `(p, x, y, z)` |
| **review** | la regla prohíbe un triángulo sin testigo bueno en algún paso | además: un testigo de una cara con la cima no vale si su cuarteto con la cima está prohibido; y un tetraedro con cima sin nodo que lo complete en algún paso queda prohibido |

La conversión del join no pierde nada: toda camarilla de la unión pasa por una cima de un lado, así que «la base está
muerta en este lado» dice lo mismo que «el cuarteto con cada cima de este lado está muerto».

### 7.4 Por qué cerraría el argumento de la estrella

* Las dos condiciones que hoy son hipótesis (`hface`, `hbase`) pasarían a salir del **punto fijo** de la regla, igual
  que hoy sale el testigo de cada trío (`trioGood_low`): `hface` del veto de cuartetos en los testigos, `hbase` de la
  regla de nivel cuatro.
* Todo objeto de la familia de una cima contiene a la cima o es una base bajo ella. Los que contienen a la cima son
  exclusivos de su lado, así que el join los guarda; las bases quedan cubiertas por la conversión.
* Por eso el nivel no tendría que seguir subiendo: un cuarteto anclado ya lleva su nodo exclusivo, y a partir del join
  siguiente lo cortan todas las entradas.

Lo ya formalizado encaja: `star_coreD` es exactamente el argumento con las bases del lado tratadas como prohibidas, y
la conversión del join haría que la unión las tratara así por sí misma.

### 7.5 Lo que respalda la propuesta

Los únicos fallos medidos de `Star4At` y `StarTriAt` son las bases revividas (792 celdas, 24 bases), y tratándolas
como prohibidas no falla nada (§6). Es lo que la conversión del join haría de forma automática.

### 7.6 Lo que no se sabe

* Si aparece un **nivel cinco** en otra parte de la cadena: la llegada (`topAt_arrival`, `good_arrivalOn`) y la
  solidez de las camarillas frente a cuartetos están demostradas para tríos y habría que rehacerlas.
* Si la regla de nivel cuatro, al prohibir cuartetos, corta aristas que hoy sobreviven y cambia las vueltas del review.
* El **coste**: del orden de `N³` cuartetos por cima. La regla de tríos ya multiplicó el tiempo por 18–65 sin
  optimizar.
* Si con la regla nueva sigue valiendo `TopSideAt` sin pins tal como está demostrada (la prueba usa que una camarilla
  que esquiva los tríos sobrevive al review; con cuartetos tendría que esquivarlos también).

### 7.7 Cómo probarla barato

1. Prototipo en Julia de la conversión del join, la herencia en el UP y el veto en los testigos (sin la regla de nivel
   cuatro).
2. Medir en `set011221_2004_i3_v7_c27` si con eso la condición de las caras sale sola del punto fijo y si las 792
   celdas dejan de ser fallos.
3. Si sale, añadir la regla de nivel cuatro y medir `hbase`; después, y solo después, Lean.

## 8. Lo que es falso (para no volver)

| afirmación | medida |
|---|---|
| `PrevCut` | 24 de 18 633 (`set011221_2004_i3_v7_c27`), 16 de 42 574 (`v7_c30_i2`) |
| `CrossCut` | 24 de 12 787 (`set011221_2004_i3_v7_c27`) |
| `StarTriAt`, sin pins y con pins | 24 bases, en una unión de esa instancia |
| `Star4At`, sin pins y con pins | 792 celdas, la misma unión |
| `HNoRule` sin restricción | 16, 12 y 160 triángulos en tres instancias |
| un nodo vivo en la entrada del abuelo es vecino de la cima | 8 960 de 42 889 (4 instancias) |
| un trío prohibido con la cima implica que la entrada del abuelo no tiene la arista | 1 773 de 3 765 |
| `PrevCut` sin la llegada (el patrón del nacimiento en la entrada basta) | razonado: los 28 triángulos de la regla de `v6` la contradirían |
| sin pins `TopSideAt` es trivial | no en Lean: una llegada no es punto fijo de la regla; hizo falta `TopCT` |

## 9. Lecciones de método

* **Medir en `v7` antes de formalizar una cadena.** Cinco instancias pequeñas dieron por buena `HNoRule`, y seis
  `PrevCut`; las dos cayeron al subir de tamaño.
* **Volcar parciales.** Una sonda que solo escribe al final lo pierde todo si la corta el tope de tiempo.
* **Mirar qué se está midiendo.** Los pins de caminos largos casi nunca dan una unión fijada válida.
* **No dar un parcial por final.** «Con pins no revive ninguna base» fue cierto durante media tanda.

## 10. Plan

1. Decidir sobre la propuesta del §7 y, si procede, el prototipo del §7.7.
2. Terminar las tandas de pins cortos y medir `hbase` en todas las cimas de tres o cuatro `v7`, no solo en las que
   tienen bases revividas.
3. Relanzar `v8_c30` con volcado parcial.

## Ficheros y teoremas

| fichero | qué tiene |
|---|---|
| `ForbidOnInherit` | `upOn_face_parent`, `arrOn_face_parent`, `DeadBase`, `deadBase_joinOn`, `prevCut_inherit`, `HPrevNew` |
| `ForbidOnHi` | `HNoRule`, `tri_side`, `prevCut_hi`, `HPrevLo`, `HPrevLo2` |
| `ForbidOnBirth` | `holdsFace_down`, `holder_gparent_mem`, `pigeon3`, `birth_pattern` |
| `ForbidOnSplit` | `fix_witness`, `unionParent_gparent`, `tetra_parent_or_split`, `star4At_of_low_noSplit`, `noParSplit_of_star4` |
| `ForbidOnStarD` | `star_coreD`, `StarDAt`, `starD_of_noRevive`, `starD_of_cross4`, `starD_of_low`, `revive_sender_open` |
| `ForbidOnFam` | `star_coreD_fam`, `hface_of_sideFace`, `hStarDOn_init` |
| `ForbidOnApart` | `AdjApart`, `starDAt_of_le3`, `hStarDOn_line1`, `HStarPinOn` |
| `ForbidOnNoPin` | `TopCT`, `docsAlive_reviewOn`, `topSideAt_nil_line`, `HTopPinsOn`, `HStarDPinsOn` |

| veredicto | hipótesis | en lo medido |
|---|---|---|
| `spineVerdictOn_iff_of_topPins` | `TopSideAt` con pins | sin fallos |
| `spineVerdictOn_iff_of_starDPins` | `StarDAt` con pins | sin fallos |
| `spineVerdictOn_iff_of_starDLowOnly` | `StarDLowAt` + `NoParSplitAt` desde la tercera línea | sin medir aparte |
| `spineVerdictOn_iff_of_starD` | `StarDAt` | sin fallos |
| `spineVerdictOn_iff_of_starTriPins` | `StarTriAt` con pins | falsa en una instancia |
| `spineVerdictOn_iff_of_lo4`, `_two4`, `_new4` | `HNoRule` + nacimiento bajo + `Star4At` | falsas en dos instancias |

Sondas nuevas: `probe_prevnew.jl`, `probe_birth.jl`, `probe_topback.jl`, `probe_norule.jl`, `probe_rulenew.jl`,
`probe_prevbig.jl`, `probe_topdead.jl`. Commits desde el v219: de `4f9a1e4` a `9cc9959`.
