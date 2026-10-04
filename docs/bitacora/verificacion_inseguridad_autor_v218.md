# Verificación para el Autor v218: el veredicto `:on` bajo dos hipótesis de tríos en el join

1 de octubre de 2026, rama `reader-stuck`. Continúa el v217, que dejó demostrada la dirección 2 de la llegada fijada y
pendientes la dirección 1, el join con pins y la inducción de línea.

## Resumen

1. **Las llegadas ya no piden nada.** La dirección 1 está demostrada (`ct_arrival_up`), y con ella `good_arrivalOn`:
   `LiveExt` tras todo pin pasa del remitente a su llegada, sin hipótesis.
2. **La inducción de línea `:on` está hecha.** El veredicto de la espina con la regla activa queda bajo una sola
   hipótesis, en los joins (`spineVerdictOn_iff_of_joinOn`), y solo para los pins que la máquina usa de verdad.
3. **Esa hipótesis se ha ido estrechando en cuatro pasos**, cada uno con su teorema:
   cadenas (`PinSideAt`) → cimas (`TopSideAt`) → tríos (`StarTriAt`) → dos hechos simples
   (`CrossCut` + `Star4At`).
4. **Lo que queda abierto** son esas dos, medidas sin fallos:
   * `CrossCut`, de las dos llegadas solas, sin pins ni review;
   * `Star4At`, de la unión fijada sola: la estrella de una cima cierra a nivel cuatro.
5. **Las dos respuestas definidas de la máquina son correctas sin hipótesis** (`verdictOn_certified`).

Todo compila sin `sorry` y solo con los axiomas estándar (`propext`, `Classical.choice`, `Quot.sound`). Son ocho
ficheros nuevos, unas 2 950 líneas.

## 1. La llegada fijada, completa (`ForbidOnArr.lean`)

Con `E` el remitente, `h = pinOn (upOn (filterAllOn E reqs) d) R` la llegada fijada y `X = pinOn E (reqs ++ R)` la
entrada fijada:

| lema | qué dice |
|---|---|
| `ct_arrival_up` (dirección 1) | una camarilla de `X` que esquiva sus tríos, más una cima viva de `h` que la tiene por padre, es camarilla de `h` y esquiva los suyos. Solo usa la solidez del filtro, el UP y el pin (`ct_pinOn`, nuevo) |
| `liveExt_arrivalOn` | `LiveExt X` da `LiveExt h`: la cadena baja (dirección 2), se completa en `X` y sube con la cima |
| `valid_down` | si `h` es válido, `X` lo es (de `downInv_arrival`, separado de `liveChain_down`) |
| `good_arrivalOn` | `GoodOn E ⟹ GoodOn` de la llegada, con `GoodOn g` = `LiveExt` con los tríos reales tras todo pin válido |

El caso frontera que el v217 no preveía era real: la cadena de un solo nodo (la cima) no pasa por `X`. Se alarga con
un padre porque `h` está cerrado, y con dos nodos no hay tríos que comprobar.

## 2. El join y la inducción de línea (`ForbidOnGood.lean`, `ForbidOnDriver.lean`, `ForbidOnSide.lean`)

**La hipótesis, en su primera forma.** `PinSideAt A B R`: toda cadena viva de la unión fijada
`pinOn (joinOn A B) R` es cadena viva de `pinOn A R` o de `pinOn B R`, con los tríos de ese lado. Bajo ella,
`good_joinAt`.

**La inducción.** `entry_shapeOn` (una entrada de `advanceM .on` es una llegada o la unión de dos), `LInvOn`
(`LineOn`, `SInvB`, `NoDegT`, `GoodAt`) y `spineVerdictOn_iff_of_joinOn`.

**Solo los pins que la máquina usa.** `PinsFrom φ k R`: `R` es la concatenación de los requisitos de un camino del
mapa que sale de `k`. El veredicto solo mira `R = []` en la línea final, y cada llegada a `d` pide a su remitente
`reqOf φ d ++ R`. La hipótesis se pide solo para esos `R`.

**El recíproco, sin hipótesis** (`ForbidOnSide.lean`). Un lado fijado y válido vive entero en la unión fijada
(`downInv_side`, `liveChain_side_left/right`, `valid_joinOn_of_left/right`): salió del punto fijo de la regla, y el
join solo guarda tríos que cortan los dos lados. Así `PinSideAt` dice exactamente que las cadenas vivas de la unión
fijada son las de sus dos lados (`pinSideAt_iff`). De paso, **más pins, menos cadenas vivas** (`liveChain_pin_mono`).

**Medida** (`probe_pinside.jl`, `FORBID=:on`): cadenas vivas de la unión fijada que no son vivas en ningún lado.

| instancia | pins | cadenas | fuera de los dos lados |
|---|---|---|---|
| `clause_mix` | al azar | 22 101 | 0 |
| `rand3sat_v8_c10` | al azar | 186 162 | 0 |
| `clause_mix` | reales | 15 789 | 0 |
| `clause_mix_sep` | reales | 78 691 | 0 |
| `rand3sat_v8_c10` | reales | 108 338 | 0 |
| `v5_c20_i2` (UNSAT) | reales | 12 420 | 0 |
| `v6_c26_i1` (UNSAT) | reales | 26 147 | 0 |

Tampoco hay callejones, y ninguna cadena es viva en los dos lados a la vez.

## 3. De cadenas a cimas (`ForbidOnTop.lean`)

El veredicto solo necesita que un estado final válido tenga una camarilla, no que toda cadena viva se alargue.

* **`TopAt g R`**: toda cima viva de `pinOn g R` está en una camarilla que esquiva sus tríos.
* **`topAt_arrival`, sin hipótesis**: la cima tiene un padre (cierre), la pareja baja (dirección 2) y la camarilla del
  padre sube (dirección 1).
* **`topAt_join`, bajo `TopSideAt`**: una cima viva de la unión fijada está viva en un lado fijado. Es el caso de un
  solo nodo de `PinSideAt` (`hypsTopOn_of_joinOn`).
* **`spineVerdictOn_iff_of_topOn`**.
* **`verdictOn_certified`, sin hipótesis**: si la línea final queda vacía, la fórmula es insatisfacible; y toda
  camarilla de un estado final se descodifica en una asignación que satisface.

**Medida** (`probe_pinside.jl`, `CHAINS=0`): 0 de 1 531 cimas fuera de los dos lados con pins reales (6 instancias) y
0 de 4 222 con pins al azar (2 250 uniones fijadas).

## 4. `TopSideAt` en piezas (`ForbidOnParts.lean`)

La conclusión «`t` está viva en `pinOn A R`» esconde un «existe»: un nodo sobrevive a un pin revisado si hay una
estructura cerrada con testigos buenos que lo contiene y cumple los pins. La estructura construida es la unión fijada,
además, en el color `b` del padre de `t`.

| pieza | qué dice | estado |
|---|---|---|
| `TopKeepAt` | fijar el color del padre de una cima viva no la mata | hipótesis; 0 fallos |
| `sideGraph` | esa unión fijada es, como grafo, parte del lado de `t` (`tF_joinOn_of_cut`) | **demostrado** |
| `TriSideAt` | un triángulo suyo prohibido en el lado está prohibido en ella | hipótesis; 0 fallos |

`topSideAt_of_parts` y `spineVerdictOn_iff_of_parts`. Medida (`probe_topparts.jl`): `TopKeepAt` 0 de 1 262 cimas y
`TriSideAt` 0 de 11,5 M triángulos con pins reales (6 instancias).

**Dos avisos.** `TopKeepAt` no es más pequeña que el núcleo: equivale a que toda cima de la unión esté en una
camarilla. Y **`TopFace` es falso**: en un lado, un triángulo prohibido sí puede tener una cima vecina con sus tres
caras sin prohibir (300 de 2 775 en `clause_mix`, 1 688 de 13 671 en `clause_mix_sep`, 144 de 764 en `v5_c20_i2`).
`TriSideAt` no se reduce a un hecho del lado solo.

## 5. «El primero que muere» (`ForbidOnKeep.lean`, `ForbidOnStar.lean`)

**La familia de la cima `t`** en la unión fijada `u`: `t`, sus vecinos, y las parejas entre vecinos cuyo trío con `t`
no está prohibido en `u`.

**El argumento.** Si algo de la familia muriera en el review del lado fijado, se mira lo primero que muere. Todo lo
que contiene a `t` tiene en `u` un testigo que todavía no ha muerto, así que la regla no dispara. Lo único sin
testigo propio son los triángulos entre vecinos de `t` que no contienen a `t` (las **bases**).

| pieza | fichero | qué |
|---|---|---|
| `TrioGoodK`, `downInv_pinOnK` | `ForbidOnKeep` | el review conserva una estructura aunque una clase `K` de sus triángulos no tenga testigo, si `K` no aparece en la lista de tríos del estado final (los tríos solo crecen) |
| `AdjPar` | `ForbidOnStar` | dos vecinos en pasos consecutivos son padre e hijo; se conserva por la fila, el join y el review |
| `star_core` | `ForbidOnStar` | la familia es una estructura cerrada del lado sin fijar y sobrevive entera en el lado fijado, si las bases cumplen dos condiciones (abajo) |
| `StarTriAt`, `topSideAt_of_starTri`, `spineVerdictOn_iff_of_starTri` | `ForbidOnStar` | la hipótesis de tríos: una base viva en `u`, con sus tres caras con `t` vivas, no está en los tríos del lado fijado |

**Medida** (`probe_startri.jl`): la familia sobrevive entera (0 nodos, aristas o tríos de menos) y ningún testigo
bueno tiene su base prohibida en el lado fijado: 0 de 29 M con pins reales (5 instancias), 0 de 5,3 M con pins al azar
(2). `AdjPar`: 0 aristas entre pasos consecutivos que no sean padre–hijo.

## 6. Las dos mitades de `StarTriAt`

Una base puede fallar de dos maneras, y cada una tiene su hipótesis:

| mitad | hipótesis | de qué habla |
|---|---|---|
| la base ya está prohibida en el lado sin fijar | **`CrossCut S O`**: una base prohibida en `S` bajo una cima suya con sus tres caras sin prohibir la corta también `O` | las dos llegadas, sin pins ni review |
| la regla la prohíbe durante el review del lado fijado | **`Star4At J R`**: todo tetraedro vivo con cima tiene en cada paso un nodo que lo completa (sus seis caras nuevas sin prohibir) | la unión fijada sola |

Con `CrossCut` el join guarda la base (la cortan los dos lados), así que no está viva en la unión. Con `Star4At` los
tríos sin la cima tienen testigo propio dentro de la familia. `topSideAt_of_cross4` y
**`spineVerdictOn_iff_of_cross4`**.

**Medida** (`probe_tetra.jl`, `FORBID=:on`).

*Corte cruzado*, sin pins:

| instancia | bases prohibidas bajo cima viva | las corta el otro lado | abiertas |
|---|---|---|---|
| `clause_mix` | 378 | 378 | 0 |
| `clause_mix_sep` | 2 214 | 2 214 | 0 |
| `v5_c20_i2` (UNSAT) | 192 | 192 | 0 |
| `v5_c20_i3`, `xor3`, `v4_c12_i1` | 0 | — | — |

Al otro lado le falta un nodo (1 488), una arista (176) o tiene la base prohibida (1 120). En la unión fijada ningún
tetraedro de `TopFace` sigue vivo: lo guarda el join, o el pin mata la cima, un nodo o una arista. La regla de la unión
no interviene nunca.

*Cierre a nivel cuatro*, sin muestreo (`TRI_CAP=0`), pins reales:

| instancia | tetraedros vivos con cima | pasos | sin nodo que complete |
|---|---|---|---|
| `clause_mix` | 589 663 | 11 132 815 | 0 |
| `xor3` | 36 662 | 482 064 | 0 |
| `v4_c12_i1` | 629 731 | 18 853 928 | 0 |
| `v5_c20_i2` (UNSAT) | 1 569 062 | 50 109 298 | 0 |

Con muestreo (150 tetraedros por cima, 4 instancias): 0 de 4,5 M pasos con pins al azar y 0 de 2,8 M con pins reales.

## 7. La cadena de hipótesis

    CrossCut + Star4At  ⟹  TopSideAt  ⟹  SpineVerdictOn φ ↔ Satisfiable φ
          StarTriAt     ⟹  TopSideAt
          PinSideAt     ⟹  TopSideAt

| teorema | hipótesis en los joins | tamaño |
|---|---|---|
| `spineVerdictOn_iff_of_joinOn` | `PinSideAt` | cadenas |
| `spineVerdictOn_iff_of_topOn` | `TopSideAt` | nodos (cimas) |
| `spineVerdictOn_iff_of_parts` | `TopKeepAt` + `TriSideAt` | una cima y un pin más; triángulos |
| `spineVerdictOn_iff_of_starTri` | `StarTriAt` | tríos bajo una cima |
| `spineVerdictOn_iff_of_cross4` | `CrossCut` + `Star4At` | dos hechos, cada uno de un solo objeto |

Todas se piden solo para los pins de `PinsFrom`, salvo `CrossCut`, que no tiene pins.

## 8. Por qué no basta con una regla más

En el join, un trío muerto solo en el lado `A` y vivo en `B` queda vivo en la unión. Esa información es «muerto junto
con un nodo exclusivo de `A`»: es de cuatro nodos, y los tríos no la guardan. Guardar cuartetos anclados en el nodo
exclusivo solo retrasa el problema un nivel, porque cada bifurcación del mapa que se vuelve a unir con requisitos
distintos sube uno. Lo que las medidas dicen es que la máquina no necesita ese nivel: `CrossCut` y `Star4At` son la
forma precisa de esa afirmación.

## 9. Próximos pasos

**`CrossCut`** es la más accesible: no tiene pins ni review, y habla de dos llegadas a un mismo destino. La sonda da
tres motivos por los que el otro lado corta la base (le falta un nodo, una arista, o la tiene prohibida). Lo primero es
separarlos y ver cuáles salen de la historia común de las dos llegadas (los mismos remitentes de la línea anterior,
con requisitos distintos).

**`Star4At`** es donde está el contenido: consistencia de cuatro a cinco nodos en la estrella de una cima. Antes de
atacarla conviene medirla en instancias mayores (`v6`, `v7`) y ver qué nodo completa el tetraedro (¿siempre un padre
o un hijo de alguno de los cuatro?).

**Acotar la clase.** Antes de la fusión central el join sale por parcheo (`PreClause`, en `:off`). Portarlo a `:on`
dejaría las hipótesis solo en las líneas de cláusula.

**Mantenimiento.** `docs/plans/lean_forbid_on.md` y la tabla de sincronía de `docs/plans/lean_bingo.md` están al día.

## Ficheros y commits

* **Lean** (`lean/improves_bingo/AbsSatBingo/Model/`): `ForbidOnArr.lean`, `ForbidOnGood.lean`,
  `ForbidOnDriver.lean`, `ForbidOnSide.lean`, `ForbidOnTop.lean`, `ForbidOnParts.lean`, `ForbidOnKeep.lean`,
  `ForbidOnStar.lean`; `ForbidOnPin.lean` (separado `downInv_arrival`).
* **Julia** (`julia/improves_bingo/test_3sat/`): `probe_pinside.jl`, `probe_topparts.jl`, `probe_startri.jl`,
  `probe_tetra.jl`; salidas en `output_probes/`.
* **Commits:** `becd957`, `2f194ac`, `fec9f47`, `f00186b`, `90ce74a`, `0ae2c04`, `0102019`, `a8c5020`, `df9ea09`,
  `4521816`, `3361266`, `6adfa86`, `4c65e95`, `5e8f745`, `0c96f28`, `a40fe90`, `a5d83b9`.
