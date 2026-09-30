# Verificación para el Autor v216: auditoría Lean ↔ Julia de la rama `reader-stuck`

30-sept-2026, rama `reader-stuck`. Informe de revisión, sin código nuevo. La pregunta es qué máquina modela Lean, qué
máquina midieron las sondas de hoy y qué conviene hacer: revertir Julia, revertir Lean o hacer en Lean el espejo de
Julia.

## Conclusiones y acciones

**El hallazgo.** Lean modela la máquina de Julia con `FORBID=:off` y le añade tríos prohibidos **fantasma**, que no
tocan la máquina. Todas las sondas desde las 08:31 corrieron con `FORBID=:on`. Esa máquina es otra, porque la regla de
tríos corta aristas en cada review. Por eso **las dos hipótesis que quedan en el teorema (`PinJoinSplitAll` y `HClq`)
no tienen hoy ninguna medida en la máquina que modela Lean**. Las demostraciones de Lean son correctas; lo que falta es
el respaldo empírico de sus hipótesis.

**Las acciones**, en este orden:

1. **No revertir Julia.** `FORBID` es un modo aparte, `:off` por defecto (`55ddcc3`). Revertirlo no hace válida ninguna
   medida y quita la máquina de la que sí tenemos datos: la espina sin revisión no se atasca con `:on` y sí con `:off`.
2. **No revertir Lean, salvo `TriClq` (`f36bfd8`).** Todos los teoremas de hoy son correctos y siguen valiendo para la
   máquina `:off`. `TriClq` es la excepción: su comentario dice "cadena viva", pero la definición no lo pide (§5), y en
   el modelo Lean es probablemente falsa. Ese commit se revierte.
3. **Hacer en Lean el espejo de Julia `:on`** (opción C, §7). Casa con todas las medidas y con tu preferencia, y Lean ya
   tiene casi todas las piezas: la regla, el corte y su solidez están en `ForbidSound.lean` sin conectar. Propongo
   hacerlo con un **modo como parámetro**: `:off` queda definicionalmente igual, así que nada de lo demostrado se rompe,
   y `:on` añade los tríos al estado. El paso de control es un **diferencial** Lean ↔ Julia `:on` en instancias
   pequeñas. Hasta que salga igual no se re-demuestra nada encima.
4. **Regla desde hoy:** una medida solo respalda una hipótesis de Lean si corrió en el modo que Lean modela. La tabla de
   sincronía de `docs/plans/lean_bingo.md` anotará el modo en cada fila.

## 1. Qué modela Lean hoy

| pieza | Lean (`lean/improves_bingo`) | ¿igual a Julia `:off`? |
|---|---|---|
| review | `Ops.reviewPass` = `cleanPair` (limpieza + parejas), `pruneLinks`, padres, hijos, `pruneLinks`; `finalPass` | sí |
| UP | `addNode`, `up`, `upFiltering` (ventanas prohibidas del mapa, `isProhibited`, que no son tríos) | sí |
| join | `join`, `doJoin` | sí |
| pin | `pinF g R = review {foldl filterRequire g R with dirty := true}` | sí (`filter!`) |
| veredicto | `SpineVerdict φ` = algún estado final, tras `reviewAll`, es válido (`LiveExt.lean:126`) | sí: el veredicto de la máquina `:off` |
| tríos | **familias fantasma** `famsAt` (`LiveDriver.lean:187-211`); no cambian ningún estado | Julia `:off` no tiene tríos |

Cómo son las familias fantasma:
* **Llegada** (`shiftF`): la familia del remitente fijada en `reqOf d ++ R`.
* **Unión** (`joinFam`, `joinFD`): para cada lista de pins `R`, se prohíbe lo que cortan **los dos lados ya fijados en
  `R`**.
* **Ni UP ni review añaden tríos.** Que el UP no necesite heredarlos está demostrado (`liveExt_addNode_same`,
  `01e383a`).
* **Una familia por cada lista de pins** (`FamT := List NodeId → Trios`).

Lean ya tiene, **sin conectar a la máquina**, los operadores de `:on`, todos con su solidez demostrada:
* `upF` (la herencia del UP);
* `joinF` (el join);
* `ruleF` (la fase 1 de `forbid_rule!`);
* `forbidSweep` (la fase 2, el corte de aristas, construido con `removeEdge`);
* `carried_forbidSweep` (el corte conserva las ramas solución);
* `liveExt_of_keep` y `liveExt_review` (conservar camarillas conserva `LiveExt`).

## 2. Qué hace Julia con `FORBID=:on` (`55ddcc3`)

* **UP:** `up_forbid!` prohíbe `(n, w, r)` si todos los padres de `n` cortan `(p, w, r)`.
* **Join:** `join_forbid` (en `union!`) prohíbe lo que cortan los dos lados, calculado **una vez, con los lados sin
  fijar**.
* **Review:** `forbid_rule!` entra en `make_review_owners!`, tras la limpieza y la regla de parejas, y hace dos fases
  hasta el punto fijo:
  1. prohíbe los tríos sin testigo bueno en algún paso;
  2. **corta las aristas** sin testigo bueno.
* **Pin:** `filter!` más review, que también aplica la regla. No recalcula los tríos de los joins pasados.
* **Un solo conjunto de tríos por estado**, guardado en las aristas.

| | Lean | Julia `:on` |
|---|---|---|
| aristas del estado | las de `:off` | menos: la regla corta |
| tríos del UP | ninguno | `up_forbid!` |
| tríos del join | por cada `R`, sobre los lados fijados | uno, sobre los lados sin fijar |
| tríos del review | ninguno | `forbid_rule!` |
| cadenas de la espina (`OnChain3`) | las del estado `:off` | menos |
| veredicto | máquina `:off` | máquina `:on` |

## 3. La demostración tal como está

La cadena del veredicto, de abajo arriba:

| teorema | fichero | hipótesis |
|---|---|---|
| `spineVerdict_iff_of_liveExt` | `LiveExt.lean` | `LiveExt` en los estados finales, con alguna familia |
| `lInv_steps` y la inducción de línea con pins extra | `LiveDriver.lean` | `HSplit` (= `PinJoinSplitAll` en cada join) + `HNew` |
| antes de las cláusulas, la fusión central, desde la fusión final, la negación | `PreClause.lean`, `LiveDriver.lean` | ninguna |
| `AvoidV` (solidez de las familias con pins) | `CliqueSound.lean` | ninguna |
| `HNew ⇐ HMixed ⇐ HClq` | `PreClause.lean`, `CliqueSound.lean` | — |
| **`spineVerdict_iff_of_clq`** | `CliqueSound.lean` | **`PinJoinSplitAll` + `HClq`** |
| `good_joinL` bajo `CrossClosedL` (`861bc41`) | `LiveJoin.lean`, `LiveLine.lean` | debilitamiento correcto; no cambia el veredicto |
| `spineVerdict_iff_of_triClq` (`f36bfd8`) | `CliqueSound.lean` | `PinJoinSplitAll` + `TriClq` — **defectuoso, §5** |

Todo compila, y los veredictos dependen solo de `propext`, `Classical.choice` y `Quot.sound`. Como matemática, todo es
correcto: son teoremas sobre la máquina `:off` con familias fantasma. Lo abierto es si `PinJoinSplitAll` y `HClq` son
**verdaderas en ese modelo**.

## 4. Todas las medidas de hoy y su modo

"Pre-FORBID" significa que la sonda es anterior a `55ddcc3`: la máquina era `:off`, la misma que modela Lean.

| hora | commit | sonda | qué midió | resultado | modo | ¿respalda a Lean? |
|---|---|---|---|---|---|---|
| 00:11 | `7d1848a` | `probe_spinehyps` | ≤ 2 padres en el lector; espina sin revisión | 2 padres siempre; la espina **se atasca** en `clause_mix` | pre-FORBID | sí (máquina `:off`) |
| 00:26 | `92c6b85` | `probe_sibstar` | `SibStarInv`, primer pin | 0 fallos | pre-FORBID | sí |
| 00:30 | `8d28e3c` | `probe_sibstar` (requisitos) | testigos fuera de la estrella | descripción | pre-FORBID | sí |
| 08:31 | `ab36634` | `probe_forbid` | espina sin revisión | `:off` se atasca; `:on` 0 atascos | **los dos** | compara las máquinas |
| 08:31 | `ab36634` | `probe_quartet` | camarillas vivas en cualquier orden | se completan | `:on` (control `:off`) | no |
| 08:31 | `ab36634` | `probe_liveext` | `LiveExt` en filtro, llegadas, joins, final | 0 callejones con `:on`; **con `:off` sin tríos sí los hay** | `:on` (control `:off`) | no: Lean es `:off` **con** familias fantasma, y eso no se midió |
| 08:48 | `0933492` | `probe_pinstable` | PinStable en el UP | 0 fallos | `:on` | no (luego demostrado sin hipótesis, `1dc69f0`) |
| 09:14 | `6f4b268` | `probe_joinside` | (★) `JoinSide` | 0 en 79 040 cadenas, 131 joins | `:on` | no (en Lean sale de `CrossClosed`) |
| 09:14 | `6f4b268` | `probe_topdom` | `TopDom` | **falsa** | `:on` | — |
| 10:11 | `901385b` | `probe_joinside` ABL | sin tríos del UP / del join | sin UP 0 fallos; sin join, 18 de 48 | `:on`, la regla siempre activa | no |
| 10:43 | `e3c58fa` | `probe_joinside` | mecanismo de (★) | `cand` = 0 | `:on` | no |
| 11:09 | `1878e89` | `probe_joinside`, `probe_chainopen` | `CrossClosed` (`sbad_open`); `ChainOpen` | 0; `ChainOpen` **falsa** | `:on` | no |
| 11:28 | `c43b9f2` | `probe_crossline` | `CrossClosed` entre las entradas de la línea | 0 abiertos | `:on` | no |
| 11:46 | `526ea7b` | `probe_crossline`, `probe_pinedge` | tríos lejanos; `PinEdgeMono` | `PinEdgeMono` **falsa** | `:on` | — |
| 12:03 | `c381c4e` | `probe_crossline` | `NoNewClose` conjunta | 300/300 | `:on` | no |
| 12:12 | `bfb20ed` | `probe_crossline`, `probe_pinjoin` | M1/M2; **`PinJoinSplitAll`** | 10 692/10 692 (**solo vivos y aristas**, no tríos) | `:on` | **no, y es hipótesis actual** |
| 12:50 | `a871837` | `probe_crossline` | `NoNewClose` con pins extra | 150/150 | `:on` | no |
| 13:28 | `a8edd89` | `probe_crossline` | `HNew` | cláusula 0 abiertos, 285 cortados | `:on` | no |
| 14:00 | `1b818c4` | `probe_hnewcl` | `HNew` en cláusulas con dos remitentes | 0 abiertos | `:on` | no |
| 14:09 | `5e641c9` | `probe_hnewcl` | lo que ya prohíbe el remitente = mezclados de su join | 18/18, 48/48 | `:on` | no |
| 14:23 | `54c47a9` | `probe_hnewcl` PURE | tríos de un solo lado en camarillas | 68 000; 320 sin camarilla del remitente | `:on` | no |
| 14:34 | `d763fe6` | `probe_hnewcl` | **`HClq`** | 68 000/68 000 | `:on` | **no, y es hipótesis actual** |
| 14:43 | `a1fd4eb` | `probe_triexact` | prohibido ⟺ en ninguna camarilla | 150 000, 0 excepciones | `:on` | no |
| 14:54 | `227954a` | `probe_hnewcl` CHAIN | papel de la cima de la cadena | 59 269/59 272 | `:on` | no |
| 14:55 | `d444766` | `probe_hnewcl` DUMP | las 3 excepciones | descripción | `:on` | no |
| 18:22 | `53ecae7` | `probe_crossl` | `CrossClosedL` sin pins y con pins | 0 en 428 000 cadenas | `:on` | no |
| 18:35 | `75ade30` | `probe_triexact` PINS | `TriClq` con pins | 0 excepciones en 110 000 | `:on` | no |
| 19:xx | (sin commit) | `probe_triexact` `chain_through` | prohibidos en cadenas de la espina | `clause_mix`: 0 | `:on` | no; interrumpida, está en el árbol sin commit |

**Resumen:** 24 medidas con `:on` (dos de ellas con un control `:off` sin tríos), 1 que compara las dos máquinas y 3
anteriores a FORBID. **Ninguna** mide la máquina
`:off` con las familias fantasma de Lean. Las dos medidas de las hipótesis actuales (`PinJoinSplitAll`, `HClq`) son de
`:on`. Además, `probe_pinjoin` no compara los tríos, y en `:on` los tríos son parte del estado.

La única pista sobre el modelo Lean va en su contra. En `probe_liveext`, la máquina `:off` **sin** tríos tiene
callejones, y la espina de `probe_spinehyps` y `probe_forbid` se atasca en `:off`. Nadie ha medido `:off` **con** tríos
solo de join.

## 5. El error de `TriClq` (`f36bfd8`)

* **Qué dice el código:** `OnChain3 E C j p q r` es solo `SpineChain E C j` más los rangos. No pide que la cadena esté
  viva.
* **Qué dice el comentario:** "trío de una cadena viva". Es falso.
* **Por qué la hipótesis es probablemente falsa:** en el estado `:off` de una unión, un trío mezclado (lo cortan los dos
  lados y el join lo prohíbe) puede estar en una cadena de la espina. Por la solidez (`AvoidV`), ese trío no está en
  ninguna camarilla.
* **Por qué la sonda no lo vio:** la medida de hoy (0 prohibidos en cadenas, `clause_mix`) es de `:on`, donde la regla
  ya cortó esas aristas.
* **Qué se salva:** la reducción `TriClq ⟹ HClq` es correcta, pero la hipótesis nueva no sirve. Se revierte `f36bfd8`.

## 6. `CrossClosedL` (`861bc41`)

Es un debilitamiento correcto (`good_join` sale como corolario) y se queda. La medida (`53ecae7`) es de `:on`. Además,
sobre cadenas vivas de la unión dice lo mismo que (★), así que no reduce el problema (lo dije en el chat).

## 7. Las opciones

### A. Revertir Julia (quitar FORBID)

* **Qué haría:** volver a antes de `55ddcc3`.
* **Qué gana:** nada. `:off` ya es el modo por defecto, y las medidas de `:on` no pasan a valer para Lean.
* **Qué pierde:** la única máquina de la que hay evidencia de que la espina no se atasca, y las 24 medidas.
* **Veredicto:** no.

### B. Revertir Lean

* **Qué haría:** volver a antes de la línea `LiveExt` y las familias (`2711a5a` y siguientes).
* **Qué gana:** solo quitar `TriClq`. El resto son teoremas correctos sobre `:off`: la solidez, `LiveExt` en el UP,
  el join bajo (★), la inducción, antes de las cláusulas sin hipótesis.
* **Qué pierde:** unas 5 200 líneas demostradas (`ForbidSound`, `LiveExt`, `LiveUp`, `LiveJoin`, `LivePin`,
  `LiveCommute`, `LiveLine`, `LiveDriver`, `PreClause`, `CliqueSound`) que sirven de base al espejo (C).
* **Veredicto:** revertir solo `f36bfd8`.

### C. Espejo de Julia `:on` en Lean (recomendada)

* **Qué haría:** la máquina de Lean pasa a ser la `:on`, y los tríos dejan de ser fantasma: son del estado.
* **A favor:**
  * Las medidas de hoy pasan a hablar de la máquina que modela Lean, aunque hay que re-enunciar dos cosas: `PinJoinSplitAll`
    con tríos, y las familias por pins.
  * Es la máquina con evidencia de que no se atasca.
  * Las piezas existen, con su solidez: `ruleF`, `forbidSweep`, `carried_forbidSweep`, `liveExt_of_keep`.
  * El corte de aristas es un `removeEdge`, así que los invariantes probados con `RevPrims` pasan casi gratis.
  * La familia "a cada `R`" deja de ser un objeto aparte: es la de los tríos de `pinF g R`.
* **En contra:**
  * **Hay que re-demostrar.** Tocar el review afecta a 13 ficheros que usan sus tripas (`ReviewClean`, `ClosedReview`,
    `Struct`, `Keeps`, `EdgeCliqueUp`…), la terminación incluida: la medida tiene que contar también los tríos. Y la
    inducción de línea de hoy hay que re-enunciarla sobre tríos reales, porque `joinFam` por pins no es lo que hace
    Julia.
  * **Para el diferencial**, `ruleF` y `forbidSweep` necesitan versiones computables (hoy `forbidSweep` es
    `noncomputable`).
* **Cómo, por fases, con una puerta:**
  1. **Modelo.** Un parámetro de modo en el review, el UP, el join y el pin, con `:off` definicionalmente igual al actual
     para que ningún teorema existente se rompa. `:on` lleva los tríos en el estado, `upF` en el UP, `joinF` sin pins en
     el join, y la regla en dos fases a punto fijo tras `cleanPair`, en el mismo orden que Julia.
  2. **Diferencial (la puerta).** `bingo-dump` con tríos y `compare_bingo.jl` contra Julia `FORBID=:on`, en instancias
     pequeñas y con tope de RAM: mismos veredictos, vivos, aristas y tríos. No se sigue hasta que salga igual.
  3. **Invariantes de contabilidad** por `RevPrims`, más una primitiva nueva (cambiar tríos). Hay que rehacer la
     terminación del review.
  4. **La inducción de línea** sobre tríos reales: `Good`, `FamMono`, `PinJoinSplitAll` con tríos, `HClq`.
  5. **Medir** las hipótesis resultantes, ya en el modo espejo.

### D. Un modo Julia `:ghost` que refleje a Lean tal como está

* **Qué haría:** la máquina `:off` sin tocar, más una función que calcule las familias fantasma de Lean para cada `R`.
* **A favor:** es menos trabajo que C, y se conserva todo lo demostrado.
* **En contra:**
  * Las medidas de hoy no sirven, y hay que rehacerlas todas.
  * Calcular las familias por pins es caro.
  * La única pista (`probe_liveext` sin tríos) sugiere que el modelo `:off` puede tener callejones. Si los tiene,
    el trabajo es en vano.
  * No es lo que prefieres.
* **Veredicto:** solo como control barato opcional. Una medida de `LiveExt` en los estados finales con `:off` y tríos
  solo de join, sin pins, dice si la línea actual de Lean es siquiera viable.

## 8. Qué no cambia

* Las demostraciones de hoy siguen siendo teoremas correctos sobre la máquina `:off`.
* La solidez de los tríos (`ForbidSound`, `AvoidV`) vale para las dos máquinas.
* Las refutaciones (`TopDom`, `ChainOpen`, `PinEdgeMono`) son de `:on`. Como afirmaciones sobre esa máquina siguen
  siendo falsas.
* Las sondas corren siempre con `run_capped.sh` (tope de RAM), desde hoy.

## Commits y ficheros de referencia

* Julia: `55ddcc3` (FORBID), `src/graph_path/graph_path_forbid.jl`, `src/db/path/docs/path_owners_graph.jl`
  (`up_forbid!`, `join_forbid`, `union!`), `src/graph_path/graph_path_filter.jl` (el review).
* Lean: `Ops.lean` (review), `LiveDriver.lean` (familias fantasma), `ForbidSound.lean` (operadores `:on` sin conectar),
  `LiveExt.lean` (`SpineVerdict`), `CliqueSound.lean` (`HClq`, `TriClq`).
* Informes anteriores: v214 (`a8edd89`), v215 (`c6c8559`).
