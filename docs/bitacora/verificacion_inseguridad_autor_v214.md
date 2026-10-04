# Verificación para el Autor v214: los tríos prohibidos, `LiveExt` y la inducción con pins extra hasta la máquina real

Ricardo, este informe sigue al v213. Cubre la sesión del 30-sept-2026 en la rama `reader-stuck`, de `f49ad82` a
`b2f1380`.

El v213 terminaba así: con revisión, el lector por caminos no se atasca nunca, y lo que faltaba demostrar era el
acuerdo entre dos ramas. Me preguntaste por el problema de los tríos: si las aristas son legítimas, ¿dónde está el
fallo? ¿Podríamos guardar en las aristas los tríos prohibidos? A partir de ahí salió todo esto:
* **FORBID**, los tríos prohibidos en las aristas, en Julia;
* su **solidez**, en Lean;
* un invariante nuevo, **`LiveExt`**, que por sí solo da el veredicto;
* la **inducción de línea completa sobre la máquina real**, con dos hipótesis medidas.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar `propext`, `Classical.choice`, `Quot.sound`):
  * **`spineVerdict_iff_of_liveLine`** (`LiveDriver.lean`): la **espina con tríos** decide la satisfacibilidad sobre
    `Driver.run`. La espina con tríos es: SAT si algún estado final, revisado, es válido; no fija nada y no revisa al
    leer. Vale bajo dos hipótesis:
    * **`PinJoinSplitAll`** en los joins que hace la máquina;
    * **`NoNewClose`** hacia los remitentes de las otras entradas, fuera de los nodos de negación.
  * En los nodos de negación, `NoNewClose` ya no es hipótesis: está demostrado.
* **Medido, 0 fallos:**
  * `PinJoinSplitAll`: 10 692 de 10 692;
  * `NoNewClose` en su forma conjunta: 300 de 300 sin pins extra y 150 de 150 con pins extra;
  * `HNew`, la forma exacta de la hipótesis final: ningún trío abierto en los remitentes. En las líneas de variable y
    de negación no hay ni un trío prohibido en una cadena.
* **Refutado por medida:** `TopDom`, `ChainOpen`, que los lados coincidan en sus tríos, `PinEdgeMono`, y `NoNewClose`
  llegada a llegada.
* **Un resultado de límite:** la revisión sola no basta. `closed_not_chainInv` da un estado cerrado en el que falla
  `ChainInv`.

---

## 1. Dónde fallaba: aristas legítimas, tríos imposibles

Cada arista del grafo de dueños es legítima: une dos nodos que están juntos en alguna solución parcial. El problema
aparece con tres nodos: $x, y, z$ pueden ser vecinos dos a dos, cada arista por una rama distinta, sin que ninguna
rama pase por los tres. La espina los elige porque son vecinos, y más abajo se atasca. Es el "acuerdo entre ramas" de
los v211–v213, visto en su forma más pequeña.

**FORBID** (`55ddcc3`, en Julia, `:off` por defecto) guarda en las aristas los tríos que ninguna rama recorre:
* **el UP** hereda un trío si todos los padres lo prohíben;
* **el join** prohíbe un trío si los dos lados lo cortan, bien porque falta el triángulo, bien porque ya está
  prohibido. Así caen los tríos que mezclan ramas;
* **la revisión** descubre tríos nuevos con `forbid_rule!`.

Deshacer sigue siendo exacto con FORBID. La **ablación** (`901385b`) dice qué parte importa: sin los tríos del join,
la espina se atasca (18 de 48 tríos); sin los que hereda el UP, todo sigue a 0 fallos. Lo demostré después en Lean:
**el UP no necesita heredar tríos** (`liveExt_addNode_same`, `01e383a`).

## 2. El límite de la revisión (`ClosedLimit.lean`, `f49ad82`)

Me preguntaste si la revisión convierte lo ternario en binario, y si podía demostrarse que basta. La respuesta es que
no, y está demostrado.

**`closed_not_chainInv`**: el grafo completo $K_5$ con 4 colores y la cima fijada es válido, cerrado (`ClosedState`) y
cerrado por parejas, pero no cumple ni `ChainInv` ni `NoZombie`.

La técnica es la **construcción de un contraejemplo** (Solow, cap. 4): para refutar un "para todo" basta un objeto
concreto. El palomar, que está fuera del libro, da el atasco. Cualquier demostración tiene que usar **cómo construye
la máquina** sus estados, no solo que estén cerrados. Por eso el resto del informe es una inducción sobre la
construcción.

## 3. Los tríos prohibidos son sólidos (`ForbidSound.lean`, `380869d`)

Si $S$ es el conjunto de ramas solución, **`ForbidSound Sol g F`** dice que ninguna rama de $S$ pasa por un trío de
$F$. Se conserva:
* en el UP (`avoids_upF`);
* en el join (`avoids_joinF_left/right`, `forbidSound_join`). Una rama del lado izquierdo no pasa por un trío que el
  izquierdo corta;
* en la revisión (`avoids_ruleF`, `forbidRound_sound`).

No hace falta ni B1 ni `SibStarInv`. Esto garantiza que FORBID no pierde soluciones. Lo que queda es que la espina no
se atasque.

## 4. `LiveExt`: un invariante que da el veredicto (`LiveExt.lean`, `2711a5a`)

Una **cadena viva** es una cadena de la espina (de una cima hacia abajo, padres vecinos dos a dos) sin ningún trío de
$F$, en ningún orden. **`LiveExt g F`** dice: toda cadena viva que no ha llegado al paso 0 se alarga, viva, un paso
más.

$$\mathrm{LiveExt}(g,F) \;\Longrightarrow\; \text{desde cualquier cima viva hay una cadena viva hasta el paso } 0
\;\Longrightarrow\; \text{camarilla}.$$

* **`liveChain_full`**: el paso de en medio, por inducción sobre la longitud (Solow, cap. 6).
* Una cadena completa es una camarilla, y una camarilla es una solución (`Decode`). No hace falta que $F$ sea sólida
  para esto; la solidez es lo que hace creíble que `LiveExt` se cumpla.
* **`spineVerdict_iff_of_liveExt`**: si todos los estados finales revisados cumplen `LiveExt` para alguna $F$, la
  espina con tríos decide la satisfacibilidad, sin pins ni revisión al leer.

Todo el trabajo siguiente es demostrar `LiveExt` en la línea final.

## 5. El UP conserva `LiveExt` (`LiveUp`, `LiveCommute`, `LivePin`)

* **La fila nueva** (`liveExt_addNode_same`): con la misma $F$, sin heredar nada.
* **La revisión y la regla de tríos** (`liveExt_of_keep`): lo que conserva camarillas conserva `LiveExt`.
* **El filtro de requisitos** es el pin del UP. Es lo delicado: `LiveExt` tras el filtro equivale a `PinLive`
  (`liveExt_filterAll`). Por eso el invariante tiene que valer **tras todo pin**, no solo en el estado.
* **Filtrar y subir conmutan** (`filter_up_commute`, `arrival_pin_commute`): fijar una llegada con $R$ da el UP del
  remitente fijado con los requisitos del UP y $R$, en vivos y aristas. Con eso, `pinStableF_arrival`: el UP conserva
  el invariante reforzado, sin hipótesis.

## 6. El join: `CrossClosed` (`LiveJoin.lean`)

El join conserva `LiveExt` si toda cadena viva de la unión es viva en uno de los lados: es la condición **(★)**
`JoinSide`, y con ella vale `liveExt_join`. (★) medida: 0 violaciones en 79 040 cadenas vivas de 131 joins.

**`joinSide_of_crossClosed`** reduce (★) a una condición más fácil de manejar. **`CrossClosed A B`**: un trío de una
cadena de $A$ que $A$ prohíbe está cortado en $B$ (falta el triángulo o está prohibido). Hace falta en los dos
sentidos, y además que las cimas de un lado no vivan en el otro.

Lo que **no** es cierto, medido:
* **`TopDom`**: miles de fallos;
* **`ChainOpen`**, que ninguna cadena contenga un trío prohibido: hay cadenas mezcladas;
* que **los dos lados coincidan en sus tríos**: 184 desacuerdos. Todos quedan fuera de las cadenas;
* **`PinEdgeMono`**: los pins sí cortan aristas entre supervivientes;
* **`NoNewClose` llegada a llegada**: un trío abierto en el remitente puede cerrarse en una llegada (7 794 casos en
  `clause_mix`).

Lo que **sí** vale es la **forma conjunta**, **`NoNewClose`**: un trío de una cadena de una entrada que cortan *las dos*
llegadas ya lo cortaban *los dos* remitentes. Medido: 300 de 300 sin pins extra. De ahí sale `PinSwap` por
monotonía (`pinSwap_of_noNewClose`), y de `PinSwap` sale `CrossClosed` entre las entradas (`crossClosed_join`).

## 7. La inducción con pins extra (`LiveLine.lean`)

`CrossClosed` tiene que valer entre estados **fijados** con cualquier lista de pins $R$, porque (★) se pide tras cada
pin. Una sola relación de tríos por estado no basta: al fijar con $R$ la relación cambia. Por eso cada estado lleva
una **familia** $F : \text{List NodeId} \to \text{Trios}$, la relación de "la máquina con los requisitos $R$
añadidos":
* **llegada** `up (filterAll D reqs) d`: $R \mapsto F_D(\mathit{reqs} \mathbin{+\!\!+} R)$;
* **unión** `join A B`: $R \mapsto$ `joinF` de los dos lados fijados por $R$, o la del lado válido si solo uno lo es
  (`joinFam`).

**`Good g F`** reúne:
* la contabilidad (`SInvB`) y el paso $\ge 1$;
* para todo $R$ con `pinF g R` válido, `LiveExt (pinF g R) (F R)`;
* $F$ por debajo del paso y sin tríos degenerados.

| pieza | lema | hipótesis |
|---|---|---|
| llegada | `good_arrival` | ninguna |
| unión | `good_join` | `CrossClosed` entre los lados fijados y `PinJoinSplitAll` |
| la familia crece al fijar más | `famMono_arrival`, `famMono_join` | `PinJoinSplitAll` en la unión |
| pins triviales (sin víctimas) | `pinF_triv`, `triv_arrival_top`, `triv_join` | ninguna |

**`PinJoinSplitAll A B`**: fijar la unión da la unión de los lados fijados, en vivos y aristas. Es `SecSplit` con pins.
El sentido fácil está demostrado (`join_pinF_sub`); el difícil es hipótesis, medida 10 692 de 10 692.

**`CrossClosed` pasa a la línea siguiente** en todas las formas de entrada:

| origen → destino | lema | desde |
|---|---|---|
| unión o llegada → unión de dos llegadas | `cc_gen` | `NoNewClose` hacia los dos remitentes del destino |
| cualquiera → una sola llegada | `cc_to_single` | `NoNewClose` hacia su remitente |
| negación | `cc_neg`, `cc_src_arrival` | `CrossClosed` de los remitentes y pins triviales |

## 8. La máquina real (`LiveDriver.lean`, `9e88169`, `b2f1380`)

**El enunciado**, en la forma $A \Rightarrow B$ que propone el método:
* $A$: $\varphi$ acotada, y para cada línea $n$ de `Driver.run` valen `HSplit` y `HNew`;
* $B$: $\text{SpineVerdict}(\varphi) \iff \text{Satisfiable}(\varphi)$.

$B$ es una equivalencia, así que por la regla de la definición basta dar `LiveExt` en los estados finales revisados
(`spineVerdict_iff_of_liveExt`). Eso es un "para todo $n$", y la técnica que pide es la **inducción** sobre las líneas
(Solow, cap. 6).

* **La afirmación $P(n)$** es `LInv φ (n+1) (steps φ n (init φ)) (famsAt φ n)`. Pide:
  * contabilidad y claves únicas en el mapa;
  * cada entrada `Good` y `FamMono` con su familia;
  * los documentos de su cima con su clave;
  * su clave es un pin trivial (`Triv`), y también los pins por encima (`AboveTriv`);
  * `CrossClosed` entre cada par de entradas fijadas.
* **Las familias fantasma** `famsAt` se definen con el mismo pliegue que `advance`, así que las hipótesis se enuncian
  sobre la corrida real y no sobre una familia elegida a posteriori.
* **La forma de cada entrada** (`lookup_advance`, `line_cases`, `entry_shape`). La entrada de una clave tras `advance`
  es el pliegue de las llegadas válidas en el orden de la línea. Como el mapa bin tiene como mucho dos nodos por paso,
  cada entrada es una sola llegada o la unión de dos, y la máquina las une (`doJoin_arr`: mismo paso, mismo nodo,
  válidas).
* **Base, $P(0)$** (`lInv_init`): la semilla, con la relación vacía. Para eso `Good` pide paso $\ge 1$ en vez de
  $\ge 2$. Con un solo paso `LiveExt` no pide nada, y con dos pasos `CrossClosed` tampoco (`crossClosed_small`: no
  cabe un trío de nodos distintos). Solo la monotonía al fijar más pide paso $\ge 2$.
* **Paso, $P(n) \Rightarrow P(n+1)$** (`lInv_advance`): por casos sobre la forma de cada entrada, con los lemas de §7.
* **La negación, sin hipótesis** (`b2f1380`). Un nodo de negación tiene un solo padre en el mapa, que solo lo tiene a
  él de hijo (`sons_neg`). Su requisito es la cima de ese padre (`reqOf_negd`), un pin trivial. El trío prohibido en
  la llegada lo estaba en ese padre, y el `CrossClosed` de la línea lo lleva al otro remitente (`cc_src_arrival`).
* **Las hipótesis se debilitaron**: `NoNewClose` se pide para un $R$ fijo, y solo con la entrada y el remitente
  fijados válidos.

**Comprobación.**
* **La base** cubre la línea inicial, y el caso de dos pasos está tratado aparte.
* **Los casos** de `entry_shape` son exhaustivos, porque `line_cases` descarta tres entradas.
* **Los cuantificadores** de la hipótesis están enunciados sobre objetos de la corrida real.
* **Axiomas:** solo los estándar.

## 9. Medidas de esta sesión

| propiedad | resultado | sonda |
|---|---|---|
| espina con tríos | 0 atascos (`clause_mix`, `clause_mix_sep`, `rand3sat_v8_c10`) | `probe_forbid` |
| `LiveExt` tras filtro, llegadas, joins y final | 0 callejones con FORBID; sin FORBID sí los hay | `probe_liveext` |
| (★) `JoinSide` | 0 en 79 040 cadenas vivas, 131 joins | `probe_joinside` |
| `CrossClosed` entre las dos entradas de cada línea | 0 abiertos; cortes por nodo 156, arista 18, prohibido 30 | `probe_crossline` |
| `NoNewClose` conjunta | 300/300; con pins extra 150/150 (12 máquinas fijadas) | `probe_crossline` |
| `PinJoinSplitAll` | 10 692/10 692 | `probe_pinjoin` |
| `HNew` (la hipótesis final), sin pins extra | cláusula: 0 abiertos, 285 cortados; variable y negación: ningún trío | `probe_crossline` |
| `TopDom`, `ChainOpen`, acuerdo de tríos, `PinEdgeMono`, `NoNewClose` por llegada | **falsas** | varias |

La medida de `HNew` es de las 4 instancias rápidas: `clause_mix`, `rand3sat_v8_c10` (SAT), `v5_c20_i2` y `v6_c26_i1`
(UNSAT). Con 3 pins extra (semilla 2), ninguna de las 4 tiene un trío prohibido en una cadena, así que `HNew` se
cumple sin más: con pins, la medida no pone a prueba la hipótesis. Los 150/150 de `NoNewClose` con pins venían de 12
máquinas fijadas en otras instancias.

## 10. Dónde estamos y siguientes pasos

**Dónde estamos.** Por primera vez hay un teorema sobre la máquina real en el que **todo el montaje está demostrado**:
* la contabilidad;
* el UP con sus pins;
* el join salvo sus dos hipótesis;
* la forma de las entradas, la base, la negación y la conexión con el veredicto.

Lo abierto son dos enunciados locales, cada uno sobre un solo paso de la máquina y medido sin fallos:

| pieza | estado |
|---|---|
| `LiveExt` ⟹ veredicto de la espina | **demostrado** |
| UP (fila, revisión, filtro, conmutación) | **demostrado**, sin hipótesis |
| join bajo `CrossClosed` | **demostrado** |
| `CrossClosed` en toda la línea, con pins extra | **demostrado** desde `NoNewClose` y `PinJoinSplitAll` |
| negación | **demostrada**, sin hipótesis |
| `NoNewClose` fuera de la negación (`HNew`) | abierto; 0 fallos; en la práctica solo muerde en las líneas de cláusula |
| `PinJoinSplitAll` (`HSplit`) | abierto; 0 fallos; es `SecSplit` con pins, el sentido difícil |
| el lector con pins (`readerVerdict`) | no conectado todavía; el teorema es para la espina |

Las dos hipótesis siguen siendo el acuerdo entre ramas. Lo que ha cambiado es la forma:
* **`HNew`** habla de tríos concretos en cadenas y de un solo paso: un trío que la entrada cierra ya lo cerraba el
  remitente vecino;
* **`HSplit`** es la conmutación entre fijar y unir.

**Siguientes pasos**, en el orden que recomiendo:
1. **Demostrar que antes de la primera cláusula no hay tríos prohibidos.** Es lo que mide la sonda en las líneas de
   variable y negación. Con eso `HNew` solo se pide en las líneas de cláusula, que es donde está el contenido.
2. **Atacar `HNew` en las líneas de cláusula**, operación por operación. La idea candidata: un trío prohibido en una
   unión lo cortan las dos llegadas, y cada llegada es su remitente con un literal fijado. Cuando lo corta porque
   falta un nodo o una arista, eso lo puso el pin del literal. Hay que ver si cabe en el patrón de `cc_neg`: el trío
   lo prohíbe un lado, el otro lo corta, y el pin del literal no crea cortes lejos de su paso.
3. **`PinJoinSplitAll`**: su sentido difícil es el B1 de siempre con pins. Antes de atacarlo, conviene medir si basta
   una forma más débil, solo en vivos o solo para los $R$ que usan las otras piezas.
4. **Conectar el lector con pins** (`readerVerdict`): sus estados visitados son filtros sucesivos, y `pinF` es un
   filtro de una vez. Hace falta el puente `pinF` / `Visited`, que es montaje.
5. **Julia**: decidir si FORBID pasa a estar activo por defecto. Hoy cuesta ×18–65 sin optimizar.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `ClosedLimit`, `ForbidSound`, `LiveExt`,
`LiveUp`, `LiveCommute`, `LivePin`, `LiveJoin`, `LiveLine`, `LiveDriver`.

**Julia (`julia/improves_bingo/`):**
* FORBID en `src/db/path/docs/path_owners_graph.jl` y `src/graph_path/graph_path_forbid.jl`;
* sondas en `test_3sat/`: `probe_forbid`, `probe_quartet`, `probe_liveext`, `probe_pinstable`, `probe_joinside`,
  `probe_topdom`, `probe_chainopen`, `probe_crossline` (con la máquina con pins extra `EXTRA`/`SEED` y las columnas
  de `HNew` por tipo de línea), `probe_pinedge`, `probe_pinjoin`.

**Commits:** de `f49ad82` a `b2f1380` en la rama `reader-stuck`.
