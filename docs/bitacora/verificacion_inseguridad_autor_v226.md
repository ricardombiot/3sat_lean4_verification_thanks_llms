# Verificación para el Autor v226: cadenas en orden de bisección, seis y siete bloques sin hipótesis

4 de octubre de 2026, rama `reader-stuck`. Continúa el v225. En una frase: **si la máquina procesa las cláusulas de una
cadena en orden de bisección de bloques (cada mitad desde su extremo y la cláusula que las une al final), sale exacta
en la condición fuerte, y eso está demostrado en Lean, sin hipótesis, para toda cadena de seis y de siete bloques con ese
orden, con cualquier numeración de variables; el lector por separadores, en orden de bisección, tampoco se atasca en
ellas.**

> **Estado**: todo compila (`lake build`, 173 trabajos) y los teoremas nuevos solo dependen de `propext`,
> `Classical.choice` y `Quot.sound`. Las seis sondas de este informe están completas (§6). Abierto: ocho bloques o más
> (§9).

## 0. Resumen

| | cinco bloques (v225) | seis bloques | siete bloques |
|---|---|---|---|
| orden de las cláusulas | el de la cadena | bisección `B0, B1, B2 \| B5, B4 \| B3` | bisección `B0, B1, B2 \| B6, B5, B4 \| B3` |
| la clase en Lean | `Chain5C` | **`Chain6BC`** | **`Chain7BC`** |
| máquina exacta (condición fuerte) | `machineExact_of_chain5C` | **`machineExact_of_chain6BC`** | **`machineExact_of_chain7BC`** |
| la espina decide | `spineVerdictOn_iff_of_chain5C` | **`spineVerdictOn_iff_of_chain6BC`** | **`spineVerdictOn_iff_of_chain7BC`** |
| lector por separadores sin atasco | `reader_sep_of_chain5C` | **`reader_bisect_of_chain6BC`** | **`reader_bisect_of_chain7BC`** |
| orden del lector | `s1, s2, s3, s4` | `s3, s1, s2, s4, s5` | `s3, s1, s2, s5, s4, s6` |
| la sonda de la instancia | `chain5_cross`: exacta | `chain6_bisect_lit`: exacta | `chain7_bisect_lit`: exacta |

## 1. De dónde partía

El v225 cerró los cinco bloques. Para ir más allá hacía falta, en el lector, el lema de «media cadena»: al fijar un
separador, cada lado de la cadena se cierra con una cuenta de cardinales (una cara del testigo por bloque) si tiene a lo
sumo cuatro bloques. Y en las líneas de la máquina, la última cláusula ve la cadena entera desde un extremo.

El plan tenía cuatro pasos: infraestructura de `n` bloques, el lema de un lado, el lector en orden de bisección y las
líneas de la última cláusula. Los tres primeros salieron; el cuarto no, y obligó a cambiar el orden de las cláusulas
(§4, §5).

## 2. Infraestructura de `n` bloques

* **`ChainN φ n zone`** (`ForbidOnChainN.lean`): una sola función de zona describe la cadena. El interior del bloque
  `j` tiene zona `j`, el separador `i` (entre los bloques `i - 1` e `i`) zona `n + i`, y lo de fuera `n` o `≥ 2n`. Los
  extremos tienen a lo sumo dos variables de dentro y los de en medio una. Cada cláusula está entera en un bloque cerrado
  (su interior y sus dos separadores) o entera fuera.
* **`glueN`**: una fuente por bloque, para cualquier `n`; sustituye a `glue4` y `glue5`. Con `glueN_P0`, `glueN_P`,
  `glueN_pid` y `glueN_tri` cierra un triángulo si las fuentes vecinas leen igual el separador que comparten.
  `chainN_of_chain5Data`: los cinco bloques del v225 son un caso.
* **Un lado** (`ForbidOnChainSide.lean`): las fuentes del lado derecho de `v` según el primer separador `t_r` que lee el
  triángulo (`side_right1`, `side_right2`, `side_right3`). Las caras del testigo llegan como `SideCap`: lo que se usa de
  ellas (una de `P0` que coincide con `a0` en tres variables, una de `P` en una, y que todas leen igual la ventana).
  El lado izquierdo es el derecho de la cadena al revés (`chainN_rev`). `glue_sides_tri` pega los dos lados en `v`.

## 3. El lector en orden de bisección

* **`phantomFree_bisect`** (`ForbidOnChainBisect.lean`): fijar el separador `v` con los dos lados abiertos. El rango es
  la suma de los primeros separadores leídos de cada lado. El testigo de un lado abierto **conserva el nodo que lee el
  primer separador del otro lado** (`capKeep`, `faces_Pwx` en cualquier posición del triángulo): sus subtriángulos dejan
  ese lado en `1` y no suben el otro.
* **`BisectOrder`** y **`sepPinFree_of_bisect`**: T2 para un orden en que cada separador tiene, a cada lado, uno ya fijado
  (o el extremo) a la distancia que el lado admite. Los fijados por el prefijo leído son extremos fijos
  (`fixed_of_prefix`), y no tienen por qué ser los más cercanos.
* **El límite**: un lado libre, con el otro abierto, cierra con tres bloques; con el extremo fijo, con cuatro. Con
  cuatro libres, el bloque de `v` y su vecino juntos piden una cara de `P` en dos variables, y las caras que conservan un
  nodo solo dan dos de `P`. Por eso el primer corte (con los dos extremos libres) llegaba a seis bloques, no a ocho como
  había previsto.

## 4. Lo que no cerraba: la última cláusula en el orden de la cadena

Con las cláusulas en el orden de la cadena, las líneas de la última cláusula con `v = s5` ven un lado de cinco bloques
libre. Lo analicé caso por caso: ninguna ventana sola cierra. La ventana `(s2, s3)` deja `Z0 ∪ Z1` (tres variables) sin
unir en `s1`, y la `(s1, s2)` deja `Z2 ∪ Z3 ∪ Z4`. Las dos fallan solo si el triángulo lee las seis variables de dentro,
ninguno de `s1 … s4`, y cada nodo una variable de cada grupo; entonces los tres nodos están en pasos de variable. Y dos
testigos distintos no se pueden unir en un separador que el triángulo no lee.

Esto era un límite del método, no de la máquina: en `chain6_cross` la condición débil sí se cumple. Pero hacía falta otra
vía.

## 5. El cambio: procesar las cláusulas en orden de bisección

La máquina ya está demostrada así: **cada línea solo ve el prefijo de cláusulas procesadas** (`phantomAt_of_prefix`), y
una cláusula no restringe nada hasta su tercer paso. En el prefijo, los bloques procesados forman trozos, y un separador
que da a un bloque aún no procesado se comporta como un extremo libre. La dificultad de una línea es la longitud del trozo
de `v`, no la de la cadena entera.

Con el orden de la cadena, el trozo crece desde un extremo y la última cláusula lo ve todo. **Con el orden de bisección**
(cada mitad desde su extremo exterior y la cláusula que las une al final), los trozos son cortos, y en la unión el nodo
`k` de la línea (el del paso `T - 1`) fija la variable del literal anterior y corta la cadena. El preproceso solo permuta
cláusulas (y, en dos de ellas, literales): la fórmula y sus soluciones no cambian.

## 6. Medidas

`test_3sat/probe_exact3.jl`, `FORBID = :on`, condición fuerte (camarillas de todos los estados). Salidas en
`test_3sat/output_probes/exact3_bisect/`. «Fuera» cuenta nodos, aristas y triángulos que no están en ninguna camarilla;
`arr_t_out` es el que fallaba.

| fórmula | estados (filtro / llegadas / uniones / final) | fuera | tiempo / memoria |
|---|---|---|---|
| `chain6_cross` (orden de la cadena) | 136 / 138 / 50 / 1 | **8** triángulos en llegadas | 510 s |
| `chain6_bisect` (bisección, separadores primero en la unión) | 142 / 144 / 56 / 1 | **0** | 628 s / 1,2 GB |
| `chain6_bisect_raw` (bisección, literales como el original) | 142 / 144 / 56 / 1 | **0** | 629 s / 1,1 GB |
| `chain6_bisect_lit` (la variante de la prueba Lean) | 140 / 142 / 54 / 1 | **0** | 967 s / 1,1 GB |
| `chain7_cross` (orden de la cadena) | 158 / 160 / 58 / 1 | **0** | 2900 s / 1,6 GB |
| `chain7_bisect` (bisección) | 166 / 168 / 66 / 1 | **0** | 3251 s / 2,0 GB |
| `chain7_bisect_lit` (la variante de la prueba Lean) | 164 / 166 / 64 / 1 | **0** | 2130 s / 2,0 GB |

Lo que dicen: en `chain6_cross` el orden de bisección quita los ocho triángulos de más. `chain7_cross` sale exacta ya en el
orden de la cadena, así que el fallo de la condición fuerte depende de la instancia y no solo de la longitud. Las dos
variantes que la prueba usa, con los literales ordenados, salen exactas, como predicen los teoremas.

## 7. Seis bloques

* **Las piezas** (`ForbidOnChain6B.lean`):
  * `phantomAt_of_lineLocalF`: como el `phantomAt_of_lineLocal` del v225, pero cada caso sabe además la posición del
    literal y que **todas las ramas leen igual la variable del paso `T - 1`** (la que fija `k`).
  * `phantomFree_fixedLoc`: si la variable fijada ya la leen igual todas las ramas, no hay nada que demostrar.
  * `phantomFree_inner`: la variable de dentro de un bloque, con el separador de ese lado fijado; un solo lado.
  * `zoneV` y `chainN_of_vals`: una cadena concreta como lista de zonas, comprobada con `decide`.
* **La instancia** (`ForbidOnChain6BI.lean`): `chain6B` es `chain6_bisect_lit`. Cada línea de las cinco primeras
  cláusulas es un separador de una cadena corta de su prefijo (`case_sep`, quince cadenas concretas). En la unión
  `B3 = (s4, ¬s3, z3)`, `k` fija `s4` (primer literal: ya fijada), `s4` (`v = s3`: lados de tres bloques libre y uno
  fijo) o `s3` (`v = z3`: un solo lado de tres). `machineExact_chain6B`.
* **La clase** (`ForbidOnChainOps.lean`, `ForbidOnChain6BC.lean`): para cualquier numeración, las cadenas cortas salen de
  la cadena entera con dos operaciones:
  * **truncar** (`chainN_truncS`): quedarse con los bloques leídos y el separador siguiente, con un bloque vacío detrás;
  * **intercambiar** (`chainN_swap`): la variable de dentro del último bloque pasa a ser el último separador.

  `line_comp` resuelve cualquier línea de un prefijo con hasta tres bloques leídos; la mitad derecha, con la cadena al
  revés. **`Chain6BC`** pide: el orden `B0, B1, B2, B5, B4, B3`; que `B1` lea `s1` y `s2`; que `B4` termine en `s4` y
  lea `s5`; y que la unión sea `(s4, s3, z3)`. Los signos y el orden de los literales de las otras cuatro cláusulas son
  libres. `chain6BC_chain6B`: la instancia está en la clase.
* **El lector** (`ForbidOnChain6BR.lean`): `BisectOrderW` dice qué ventanas usa el orden; `[3, 1, 2, 4, 5]` solo usa las
  de `B1` y `B4`, las que da la clase. **`reader_bisect_of_chain6BC`**.

## 8. Siete bloques

* **La pieza nueva** (`ForbidOnChain7B.lean`): en la unión, `v = z3` deja un solo lado, `B3 … B6`, de cuatro bloques
  libre. Como el otro lado está fijado, las tres caras del testigo son de `P`: la ventana de `B5` (lee `s5`, `s6`) da una
  fuente para `B3` y `B4` juntos (dos variables) y una para cada uno de los otros (`side_right4free`,
  `phantomFree_inner4`).
* **La clase** (`ForbidOnChain7BC.lean`): **`Chain7BC`**, con el orden `B0, B1, B2, B6, B5, B4, B3`, `B1 ∋ s1, s2`,
  `B5 ∋ s5, s6`, `B4` terminando en `s4` y leyendo `s5`, y la unión `(s4, s3, z3)`. Los prefijos usan `line_comp` igual
  que en seis (la mitad derecha tiene ahora tres bloques y usa la ventana de `B5`). `machineExact_chain7B`.
* **El lector** (`ForbidOnChain7BR.lean`): el primer corte deja lados de tres y cuatro, los dos libres, que es justo el
  caso del límite de §3. Se cierra **pesando el doble el lado largo** en el rango (`2·frR + frL`). Cuando el lado largo
  no lee ninguno de sus separadores, se usa su testigo (la ventana del bloque `m + 2`) con las caras completas, sin
  conservar nada. Sus subtriángulos lo bajan de `4` a `≤ 2`, que con el peso doble resta cuatro, y el otro lado sube a lo
  sumo tres. El otro lado saca su fuente de esas mismas caras, todas de `P`, o de su propio testigo, también con caras
  completas porque el lado largo ya está en su máximo y no puede subir. Los demás casos son los de §3 y con el peso
  siguen bajando.

  `phantomFree_bisectL`, `BisectOrderL`, `sepPinFree_of_bisectL`, `bisectOrderL_7` (`[3, 1, 2, 5, 4, 6]`, ventanas de
  `B1`, `B4`, `B5`) y **`reader_bisect_of_chain7BC`**. Para no duplicar lemas, `SideData` admite lados de cuatro y la
  condición del cuatro libre pasa a `side_window` y `open_cap`; `open_cap` recibe la inducción en forma de cotas (el lado
  abierto baja a `1` y el otro no sube) en lugar de una suma fija.

## 9. Lo que queda abierto

1. **Ocho bloques o más.** El peso doble solo sirve con un lado largo. Con `4 + 4`, el primer corte de ocho bloques, cada
   lado tendría que pesar más que el otro. Para las líneas de la máquina el límite es parecido: el lado libre de la unión
   tiene que caber en los lemas.
2. **Una clase para `n` bloques.** Las clases de seis y siete repiten la misma estructura (prefijos por `line_comp`,
   unión por lo que fija `k`); falta enunciarla una vez para cualquier `n` donde los lados quepan.
3. **El orden de la cadena.** `chain7_cross` sale exacta sin reordenar, pero con este método no sé demostrarlo: la última
   cláusula sigue viendo un lado de cinco bloques o más.
4. **El preproceso en la máquina.** Las fórmulas reordenadas están escritas a mano (`scripts/cnf/chain*_bisect*.cnf`).
   Si se adopta, hay que añadir el preproceso en Julia y en Lean (calcular el orden de bisección de una cadena) y su fila
   en `docs/plans/lean_bingo.md`.

## 10. Plan

1. La clase de `n` bloques en bisección, con las piezas de §7 y §8.
2. Ocho bloques: buscar el arreglo del lector para `4 + 4` (por ejemplo, un orden que corte primero un lado con un
   extremo ya fijado) o medir antes si hace falta.
3. El preproceso de orden de bisección en Julia, con una sonda que lo compare con el orden original en las cadenas
   medidas.

## Ficheros

| fichero (`lean/improves_bingo/AbsSatBingo/Model/`) | qué es | commit |
|---|---|---|
| `ForbidOnChainN.lean` | `ChainN`, `glueN`, `sepCover_of_chainN` | `de8e9c0` |
| `ForbidOnChainSide.lean` | un lado, la cadena al revés, el pegado en `v` | `fd8d4d8` |
| `ForbidOnChainBisect.lean` | `phantomFree_bisect`, `BisectOrder`, `reader_bisect` | `d1f4bf0`, `80dbd58`, `edbbd27`, `fa4e21d` |
| `ForbidOnChain6B.lean` | `phantomFree_fixedLoc`, `phantomFree_inner`, `phantomAt_of_lineLocalF`, `zoneV` | `edbbd27` |
| `ForbidOnChain6BI.lean` | `chain6B`, `machineExact_chain6B` | `5fb4df8` |
| `ForbidOnChainOps.lean` | `chainN_truncS`, `chainN_swap`, `line_comp` | `a7dad85` |
| `ForbidOnChain6BC.lean` | `Chain6BC`, `machineExact_of_chain6BC` | `a7dad85` |
| `ForbidOnChain6BR.lean` | `BisectOrderW`, `reader_bisect_of_chain6BC` | `3e3097a` |
| `ForbidOnChain7B.lean` | `side_right4free`, `phantomFree_inner4` | `3f16dff` |
| `ForbidOnChain7BC.lean` | `Chain7BC`, `machineExact_of_chain7BC`, `chain7B` | `3f16dff` |
| `ForbidOnChain7BR.lean` | `phantomFree_bisectL`, `reader_bisect_of_chain7BC` | `fa4e21d` |
| `lean/improves_bingo/scripts/cnf/chain6_bisect*.cnf`, `chain7_bisect*.cnf` | las fórmulas reordenadas | `22458fa`, `edbbd27`, `3f16dff` |
| `julia/improves_bingo/test_3sat/output_probes/exact3_bisect/` | las medidas de §6 | `22458fa`, `c117967`, `3f16dff`, `fa4e21d` |
