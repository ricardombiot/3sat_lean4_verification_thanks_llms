# Verificación para el Autor v217: la máquina con la regla activa, reflejada en Lean

30 de septiembre y 1 de octubre de 2026, rama `reader-stuck`. Continúa el v216, que concluyó que las medidas de la
rama eran de Julia con `FORBID=:on` mientras Lean modelaba `:off`, y propuso hacer en Lean el espejo de `:on`.

## Resumen

1. **Lean ya refleja la máquina con la regla activa**, y está comprobado. El diferencial compara los volcados de Lean
   y Julia, tríos incluidos, y da lo mismo en 4 instancias con `:on` y en 1 con `:off`. `:off` sigue siendo, por
   definición, la máquina de siempre: ningún teorema anterior cambia.
2. **Con la regla activa, la máquina dice SAT en toda fórmula satisfacible**, sin hipótesis
   (`machineVerdictOn_of_sat`). La rama de una solución nunca pasa por un trío guardado: ni la regla, ni el UP, ni el
   join la tocan.
3. **El veredicto de la espina con la regla** queda reducido a una hipótesis sin familias fantasma
   (`spineVerdictOn_iff_of_liveExt`): `LiveExt` de los estados finales revisados con **sus propios tríos**. Medida en
   Julia `:on`: 0 callejones.
4. **Tres operaciones conservan `LiveExt` con los tríos reales:** el review con la regla, el UP con `up_forbid!`, sin
   hipótesis, y el join, bajo (★).
5. **La dirección 2 de la llegada fijada está demostrada sin hipótesis** (`liveChain_down`): toda cadena viva de la
   llegada fijada, sin su cima, es viva en la entrada fijada. La clave es que la regla llega a su punto fijo
   (`forbidRule_closed`) y ese punto fijo da testigos buenos. Esto es lo que la regla `:on` añade frente a `:off`.

Todo compila sin `sorry` y solo con los axiomas estándar (`propext`, `Classical.choice`, `Quot.sound`).

## 1. El espejo de `:on` en Lean (`docs/plans/lean_forbid_on.md`)

| fase | commits | qué |
|---|---|---|
| F1 modelo | `e11aa73` | `GPathB.trios` (los tríos de Julia `Edge.forbid`, `[]` por defecto); `ForbidOn.lean`: `deadTrio`, `forbidTrio`, `sideForbidsB`, `upForbidRow` (Julia `up_forbid!`), `joinOn` (`join_forbid` + `set_forbid!`), la regla en dos fases (`forbidRound`, `forbidRule`), `reviewOn`, `upOn`, y la máquina con modo (`runM`). Con `.off` todo es la máquina de siempre por `rfl` |
| F2 diferencial | `a18b59b` | índice por estado en tablas hash (`Idx`), para que Lean termine; `bingo-dump SALIDA f.cnf on` y `test_3sat/dump_forbid.jl` |
| F3 contabilidad y cierre | `0cf4677`, `eddcaae`, `028db8f` | los invariantes de siempre por el review `:on`; `closedState_reviewOn`; el índice dice lo mismo que las listas |
| F3 solidez | `f4d40c4`, `b9a97e4`, `ed6b2ab` | `CT` (la rama llevada esquiva los tríos) por regla, review, filtro, join y UP; `run_carriesOn`, `machineVerdictOn_of_sat` |
| F3/F4 forma y veredicto | `a948b61` | `BK`, `LinksInv` y `Struct` en la línea `:on`; `spineVerdictOn_iff_of_liveExt` |

**Diferencial Lean ↔ Julia.** Compara los volcados de la línea final: nodos, vivos, tablas, padres, hijos y los tríos
de cada arista.

| instancia | modo | líneas | aristas con tríos | diferencias |
|---|---|---|---|---|
| `clause_mix` | `:off` | 525 | 0 | 0 |
| `clause_mix` | `:on` | 1 472 | 947 | 0 |
| `v4_c12_i1` | `:on` | 469 | 0 | 0 |
| `clause_mix_sep` | `:on` | 2 345 | 1 724 | 0 |
| `rand3sat_v4_c20` | `:on` | 289 | 0 | 0 |

Los tríos se guardan como lista y la consulta pide la arista, como Julia: un trío escrito en sus tres aristas y una
arista borrada que nunca vuelve con su `forbid` son lo mismo. `TriClq` se revirtió (`c693d31`), como proponía el v216.

## 2. Solidez y completitud de la máquina `:on`

**`TF g`**: los tríos que guarda `g`, como relación, con la guarda de Julia (`a ≠ b` y el trío sobre la arista
`a–b`). **`CT g S`**: `g` lleva la rama `S`, `S` esquiva `TF g`, y no hay aristas de un nodo a sí mismo.

| operación | lema | por qué no toca la rama |
|---|---|---|
| regla, fase 1 | `newTrios_notOnS` | el nodo de la rama en cada paso es testigo bueno de los triángulos de la rama |
| regla, fase 2 | `edgeAlive_of_onS` | lo mismo para sus aristas |
| review `:on` | `ct_reviewOn` | lo anterior más las operaciones de siempre |
| filtro `:on` | `ct_filterAllOn` | la rama cumple los requisitos |
| join `:on` | `ct_doJoinOn_left/right` | el join prohíbe lo que cortan los dos lados, y el lado de la rama no corta nada suyo |
| UP `:on` | `ct_upOn` | `up_forbid!` prohíbe `(n, w, r)` si todo padre de `n` corta `(p, w, r)`, pero el padre de la rama no lo corta |

De ahí `run_carriesOn` y **`machineVerdictOn_of_sat`**: con la regla activa, toda fórmula satisfacible da SAT.

**El veredicto** (`ForbidOnLine.lean`, `a948b61`). Los estados finales `:on` tienen la forma que hace falta (`BK`,
`LinksInv`, `Struct`, cierre), y
`spineVerdictOn_iff_of_liveExt : SpineVerdictOn φ ↔ Satisfiable φ` bajo
`∀ kv ∈ runM .on φ, válido (reviewAllOn kv.2) → LiveExt (reviewAllOn kv.2) (TF (reviewAllOn kv.2))`.

Lo mide `probe_liveext.jl` con `:on`, que ahora es el espejo exacto:

| instancia | estados finales | cadenas | callejones |
|---|---|---|---|
| `clause_mix` (SAT) | 1 | 37 | 0 |
| `rand3sat_v8_c10` (SAT) | 1 | 92 | 0 |
| `clause_mix_sep` (SAT) | 1 | 296 | 0 |
| `v5_c20_i2`, `v6_c26_i1` (UNSAT) | 0 | — | — |

Tampoco hay callejones en filtros, llegadas ni uniones (columnas `flt_*`, `arr_*`, `join_*`, `jrev_*`).

## 3. `LiveExt` con los tríos reales, operación por operación (`ForbidOnLive.lean`)

La maquinaria de `LiveUp` y `LiveJoin` es genérica en la relación de tríos. Hicieron falta dos ajustes:
* **`liveExt_of_keep'`**: la monotonía de los tríos solo se pide en los triángulos del estado menor. Al cortar una
  arista, los tríos que colgaban de ella dejan de contar, pero ahí no hay cadenas.
* **`NoDegT`**: los tríos guardados tienen tres nodos distintos. La regla, el UP y el join lo conservan si no hay
  aristas de un nodo a sí mismo.

| lema | commit | hipótesis |
|---|---|---|
| `liveExt_reviewOn` | `a30ace0` | ninguna (contabilidad) |
| `liveExt_upOn` | `a994f21` | ninguna (contabilidad). La fila nueva no cambia la relación (`tF_addNode`), y `up_forbid!` no toca ninguna camarilla que esquive los tríos (`upTodo_notOnS`) |
| `liveExt_joinOn` | `48aeab5`, `5d7dd82` | (★) con los tríos reales de los lados. En los triángulos de la unión, los tríos de `join_forbid` son `joinF` con los tríos reales (`addTrios_covers`) |

## 4. Los pins y la dirección 2

**Por qué hacen falta pins.** El UP filtra la entrada por su requisito, así que para encadenar hace falta `LiveExt` de
la entrada fijada, y en la línea siguiente con dos pins, y así sucesivamente: `LiveExt` tras todo pin (lo que en `:off`
es `Good`). El paso clave compara:
* la **llegada fijada** `h = pinOn (upOn (filterAllOn E reqs) d) R`;
* la **entrada fijada** `X = pinOn E (reqs ++ R)`.

**Medida** (`probe_pinstable.jl` ampliada con `com_triBA`, `com_triAB` y `com_deadA`, `:on`, `b4bc73f`): la llegada
fijada frente al UP de la entrada fijada.

| instancia | comparaciones | vivos / aristas / documentos distintos | tríos distintos en triángulos | callejones en la llegada fijada |
|---|---|---|---|---|
| `clause_mix` | 304 | 0 | 0 | 0 |
| `rand3sat_v8_c10` | 640 | 0 | 0 | 0 |
| `v5_c20_i2` | 688 | 0 | 0 | 0 |
| `v6_c26_i1` | 960 | 0 | 0 | 0 |

Los conjuntos de tríos por arista sí difieren (58, 125, 13 y 50 casos), pero solo en aristas cuyo triángulo ya no
existe. Esos tríos no cuentan en ninguna cadena.

**Por qué el método `:off` no sirve.** La prueba `:off` de la conmutación (`arrival_pin_commute`) usa que el estado
revisado es exactamente la unión de sus estructuras cerradas. Con `:on` eso falla: el estado revisado puede contener
triángulos prohibidos que no están en ninguna estructura buena.

**La prueba con `:on`: dos direcciones.**
* **Dirección 1** (pendiente, §6): si la cadena sin su cima se completa en `X`, la completación sube a `h`. Solo usa
  los lemas de solidez.
* **Dirección 2** (hecha, `liveChain_down`, `7ea78ae`): toda cadena viva de `h` con sus tríos, sin su cima, es viva en
  `X` con los suyos. Sin hipótesis.

Las piezas de la dirección 2:

| pieza | lema | commit |
|---|---|---|
| la regla llega a su punto fijo: el potencial "triángulos abiertos entre los candidatos + medida" baja en cada vuelta que sigue; tope `forbidBound = aristas × vivos + medida + 1` | `forbidRound_dec`, `forbidRule_closed` | `5289cd8` |
| el review `:on` sale en ese punto fijo | `fixClosed_reviewOn` | `77e3f02` |
| del punto fijo, la parte baja de `h` tiene testigos buenos para sus aristas y sus triángulos sin prohibir | `trioGood_low` | `77e3f02` |
| la parte baja de `h` es una estructura cerrada que baja al remitente (`secStruct_addNode_down`) y cumple los pins | — | `7ea78ae` |
| el review `:on` de `X` conserva esa estructura y no prohíbe ninguno de sus triángulos que `h` no prohíba | `downInv_reviewOn` | `b4bc73f` |
| los enlaces padre de la cadena, por la completitud de enlaces (`LinksInv`) | `liveChain_down` | `7ea78ae` |

**El paso nuevo es la regla.** Si el review de `X` prohibiera un triángulo de la cadena, sería por falta de testigo
bueno en algún paso. Pero `h` salió del review en el punto fijo de la regla, así que ese triángulo tiene en `h` un
testigo bueno. Ese testigo lo es también en `X`, porque la parte baja de `h` está dentro de `X` y los tríos de `X` sobre
ella están entre los de `h`.

## 5. Tiempos de Julia con `:on`

Una instancia por proceso, con `run_capped.sh` (4 GB, 20 min):

| tamaño | medido | total estimado |
|---|---|---|
| v3 (8), v4 (10) | 3,6–17 s | ~1,5 min |
| v5_c20 (37) | 20 y 41 s | ~18 min |
| v5_c25 (6), v6 (7) | 60 s, 84 s | ~15 min |
| v7_c27 (10), v7_c30 (4) | 419 s, 313 s | ~90 min |
| v8_c10 (1), v9_c4 (1) | 133 s, 18 s | ~2,5 min |
| v8_c30 (5), tseitin v15_c40 (1) | más de 20 min cada una | más de 2 h |

Suite completa en serie: **al menos unas 4 horas**, sin techo conocido por `v8_c30` y `tseitin`. En las instancias
medidas la regla no cortó ninguna arista y solo descubrió tríos en 2 de 10: el coste está en comprobarla.

## 6. Próximos pasos

### 6.1 Dirección 1 y la llegada (siguiente)

**Enunciado.** Sea `C` una cadena viva de `h` desde su cima hasta `j ≥ 1`, y `D` una camarilla de `X` que esquiva sus
tríos y coincide con `C` por encima de `j`. Entonces `D` más la cima de `C` es una camarilla de `h` que esquiva sus
tríos.

**Piezas, todas existentes:**
* `D` cumple los pins, porque `X` está fijado (`pinned_pinOn`).
* `D` está en `E` y esquiva sus tríos: los tríos de `E` están entre los de `X` (`trios_grow_pinOn`).
* Solidez por el filtro, el UP y el pin: `ct_filterAllOn`, `ct_upOn` y `ct_reviewOn`. `ct_upOn` necesita que el padre
  de la cima sea `D (c-1) = C (c-1)`, lo que da el enlace de `C` en `h`.
* `liveChain_of_carried`, para volver a cadena viva.

**`good_arrivalOn`.** Si `LiveExt (pinOn E R')` vale para todo pin `R'`, vale `LiveExt (pinOn A R)` para todo `R`.
Dada una cadena viva de `h`: la dirección 2 la baja a `X`; `LiveExt X` la completa a `D`; la dirección 1 sube `D` con
la cima.

Estimación: un fichero del tamaño de `ForbidOnPin`. Sin hipótesis.

### 6.2 El join con pins

Hace falta el análogo para las entradas que son uniones: `LiveExt (pinOn (joinOn A B) R)` a partir de los lados.
Hay dos caminos.

1. **Reproducir la dirección 2 para la unión** (preferido). Sus piezas:
   * la parte baja de la unión fijada ya no baja al remitente, sino a los dos lados fijados;
   * cada cadena viva de la unión fijada vive en el lado de su cima, que es (★) con pins;
   * los testigos salen igual del punto fijo de la regla en la unión fijada.

   Lo nuevo es partir la estructura por lados. Es el análogo `:on` de `cliqueSplit` y de `PinJoinSplitAll`.
2. **Dejarlo como hipótesis medida**: `PinJoinSplitAll` con tríos sobre triángulos, más (★) con los tríos reales de
   los lados fijados.

**Medidas previas, con `:on` y tope de RAM:**
* `probe_pinjoin.jl` ampliada con los tríos sobre triángulos (hoy compara solo vivos y aristas);
* `probe_joinside.jl` con pins al azar, porque hoy mide (★) sin pins.

### 6.3 La inducción de línea `:on`

Es el análogo de `LiveDriver`, más sencillo porque no hay familias fantasma. La familia en `R` es la de los tríos de
`pinOn E R`, así que desaparecen `FamMono`, `Triv`, `AboveTriv` y `CrossClosed`.
* **Invariante por entrada:** `SInvB`, `NoSelf`, `NoDegT`, `TB`, y `LiveExt (pinOn E R) (TF (pinOn E R))` para todo
  `R` válido (`GoodOn`).
* **Base:** la semilla.
* **Paso:** las entradas de una llegada, por `good_arrivalOn`; las de dos, por §6.2. La negación y la fusión central
  tienen un solo remitente.
* **Veredicto:** con `R = []`, `GoodOn` de las entradas finales es la hipótesis de `spineVerdictOn_iff_of_liveExt`.
  El teorema final queda **bajo la única hipótesis del join de §6.2**, o sin hipótesis si §6.2.1 sale.

### 6.4 Julia

* **El modo por defecto:** ¿`FORBID=:on` en `reader-stuck`? Es la máquina que Lean refleja y la que mide todo, pero la
  suite pasa de minutos a horas (§5).
* **Rendimiento de la regla:** hoy recorre todos los triángulos en cada vuelta. Llevar solo los candidatos que
  cambian (lo que tocó la vuelta anterior) no cambia el resultado, y el diferencial lo comprobaría.
* **El diferencial** con más instancias de las pequeñas (v5_c20). Lean tarda 60–70 veces lo que Julia.

### 6.5 Mantenimiento

* Poner al día `docs/plans/lean_forbid_on.md` (F4) y la tabla de sincronía de `docs/plans/lean_bingo.md` con
  `liveChain_down` y `probe_pinstable` `:on`.
* Las sondas nuevas o relanzadas siempre con `run_capped.sh` y en el modo del enunciado Lean que respaldan.

## Ficheros y commits

* **Lean** (`lean/improves_bingo/AbsSatBingo/Model/`): `ForbidOn.lean`, `ForbidOnBook.lean`, `ForbidOnClosed.lean`,
  `ForbidOnIdx.lean`, `ForbidOnSound.lean`, `ForbidOnMachine.lean`, `ForbidOnLine.lean`, `ForbidOnLive.lean`,
  `ForbidOnDown.lean`, `ForbidOnFix.lean`, `ForbidOnPin.lean`; ejecutable `bingo-dump` (`Exe/Dump.lean`).
* **Julia** (`julia/improves_bingo/test_3sat/`): `dump_forbid.jl`, `probe_forbid_time.jl`, `probe_pinstable.jl`
  (ampliada), `probe_liveext.jl` y `probe_crossl.jl`.
* **Commits:** `c693d31`, `e11aa73`, `a18b59b`, `0cf4677`, `eddcaae`, `028db8f`, `f4d40c4`, `b9a97e4`, `ed6b2ab`,
  `a948b61`, `e578375`, `a30ace0`, `a994f21`, `48aeab5`, `5d7dd82`, `b4bc73f`, `5289cd8`, `77e3f02`, `7ea78ae`.
