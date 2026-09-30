# Verificación para el Autor v215: antes de las cláusulas, la solidez con pins y lo que queda en las cláusulas

Ricardo, este informe sigue al v214 (sesión del 30-sept-2026, rama `reader-stuck`, de `eea54d5` a `d444766`). El v214
cerraba con el teorema sobre la máquina real bajo dos hipótesis, `PinJoinSplitAll` y `NoNewClose`, y con un primer
paso recomendado: demostrar que antes de la primera cláusula no hay tríos prohibidos. Aquí cuento cómo salió eso y todo
lo que vino después.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar):
  * **Antes de las cláusulas, `NoNewClose` sale sin hipótesis** (`PreClause.lean`). Los estados ahí son exactos: una
    selección válida es la rama de una asignación, toda arista está en una rama y los triángulos de una unión caen en
    un lado.
  * **La línea de la fusión central y las líneas desde la fusión final tampoco la necesitan.**
  * **La solidez de las familias con pins** (`CliqueSound.lean`, `AvoidV`): la familia de una entrada, fijada con
    cualquier lista de pins, no prohíbe ningún trío de una camarilla que lleve. Vale para toda camarilla, no solo para
    las ramas solución, y sin ninguna hipótesis.
  * **El veredicto `spineVerdict_iff_of_clq`**: la espina con tríos decide la satisfacibilidad bajo `PinJoinSplitAll`
    y **`HClq`**, dos hipótesis que ya no mencionan las familias de tríos.
* **Medido, 0 fallos:**
  * `HClq`: 68 000 de 68 000;
  * en la zona de cláusulas, **un triángulo está prohibido si y solo si no está en ninguna camarilla** (150 000
    triángulos muestreados).
* **Refutado por medida:** mi explicación de que los tríos prohibidos en el remitente se heredaban del join de la
  variable del literal.
* **Abierto:** `HClq` y `PinJoinSplitAll`.

---

## 1. Antes de las cláusulas los estados son exactos (`PreClause.lean`)

Hasta la fusión central el mapa no tiene ventanas prohibidas, y los únicos requisitos son los de negación, que fijan la
cima del propio remitente. Allí se puede razonar con asignaciones:

* **Selección válida = rama de una asignación** (`validSel_pid`, `pid_of_validSel`). Un nodo solo depende de las
  variables de su ventana (`pid_agree`, `vars_of_pid_eq`).
* **Parcheo** (`patch`): asignaciones que concuerdan dos a dos en lo que fija cada una se juntan en una sola. Es Helly
  para asignaciones parciales. Es un argumento combinatorio que está fuera del libro de Solow.
* **Toda arista está en una rama** (`pre_line`): el filtro de la llegada no toca nada (`foldl_req_pre`) y no se salta
  ninguna ventana (`skips_pre`). Con eso valen los lemas de `EdgeClique` que ya estaban.
* **`triSplit`**: un triángulo de la unión de dos llegadas fijadas es triángulo de una de ellas. Se parchean sus tres
  nodos, los pins y la clave. La rama resultante la lleva el remitente de su clave (`steps_has_sel`), y ese remitente
  es uno de los dos lados, porque la línea tiene como mucho dos entradas.
* **`NoTriF`**: la familia no prohíbe ningún triángulo del estado fijado. Se conserva en la llegada y en la unión, así
  que `NoNewClose` se cumple sin más (`hnew_of_noTri`).

Dos casos más salen gratis (`89171e4`):
* **la línea de la fusión central**: tiene un solo remitente, y una sola llegada conserva `NoTriF`;
* **desde la fusión final**: hay un nodo por paso, así que no hay otra entrada.

Queda `NoNewClose` solo en las **líneas de cláusula con dos remitentes**.

## 2. Qué pide `NoNewClose` en las cláusulas (`probe_hnewcl.jl`)

Tomo un trío de una cadena de una entrada que la entrada prohíbe, y miro cómo lo corta cada remitente:

| instancia | tríos | falta la cima de la entrada | falta la cima del otro remitente | falta un nodo abajo | falta una arista abajo | ya prohibido | abierto |
|---|---|---|---|---|---|---|---|
| `clause_mix` | 57 | 48 | 24 | 9 | 15 | 18 | 0 |
| `rand3sat_v8_c10` | 212 | 188 | 94 | 18 | 76 | 48 | 0 |

(Cada trío se clasifica dos veces, una por remitente.)

* **Si el trío no es triángulo en el remitente, este lo corta sin más.** Formalizado (`9274291`): `HNew` solo pide algo
  cuando el trío es triángulo en el remitente, y entonces pide que la familia del remitente ya lo prohíba.
* **Cuando el remitente ya lo prohíbe, es un triángulo mezclado de su propio join**: no es triángulo en ninguna de las
  dos llegadas que lo formaron (18 de 18 y 48 de 48). Nunca viene de más abajo. Mi explicación por herencia desde el
  join de la variable era falsa: esos tríos siempre tienen algún nodo más reciente que esa variable.
* **`HMixed`** (`7f99928`): la hipótesis en esa forma, y la prueba de que implica `NoNewClose` (`hnew_of_mixed`). La
  familia del join prohíbe por definición los triángulos mezclados.

## 3. La solidez con pins (`CliqueSound.lean`, `f10ffcc`)

`ForbidSound` (v214) solo valía para ramas solución, porque una camarilla de una unión podría mezclar los dos lados.
En la máquina eso no pasa, y ahora está demostrado para toda camarilla y cualquier lista de pins.

**`AvoidV`**: la familia de una entrada, fijada con `R`, no prohíbe ningún trío de una selección válida que acaba en
su clave y concuerda con `R`.
* **Llegada** (`avoid_arr`): la selección pasa por el remitente y concuerda con los requisitos del destino.
* **Unión** (`avoidV_next`): la selección la lleva la llegada de su propio remitente (completitud). En ese lado el
  trío es triángulo y no está prohibido, así que la unión no lo prohíbe.

No usa `PinJoinSplitAll` ni ninguna forma de exactitud.

## 4. `HClq`: hipótesis sin familias (`30a7c27`)

La sonda en modo `PURE` mira los tríos de una cadena de la entrada que son triángulo en un remitente y en una sola de
las dos llegadas que lo formaron ("de un solo lado"):

| instancia | de un solo lado | prohibidos en la entrada | en una camarilla de alguna llegada de la entrada |
|---|---|---|---|
| `clause_mix` | 6 013 | 0 | 6 013 |
| `rand3sat_v8_c10` | 16 286 | 0 | 16 286 |
| `v5_c20_i2` (UNSAT) | 20 285 | 0 | 20 285 |
| `v6_c26_i1` (UNSAT) | 25 393 | 0 | 25 393 |

**`HClq`**: un trío así está en una selección válida que acaba en la clave de la entrada y concuerda con los pins.
Con `AvoidV` en la línea siguiente, la entrada no puede prohibirlo, así que un trío prohibido es mezclado
(`mixed_of_clq`). La inducción lleva ahora `AvoidV` en cada línea (`lInv_stepsA`).

**El teorema**, en la forma $A \Rightarrow B$:
* $A$: $\varphi$ acotada, `PinJoinSplitAll` en los joins de la máquina, y `HClq` en las líneas de cláusula con dos
  remitentes;
* $B$: $\text{SpineVerdict}(\varphi) \iff \text{Satisfiable}(\varphi)$.

## 5. Por qué los tríos de un solo lado están en una camarilla (sondas, sin demostrar)

* **Prohibido si y solo si no está en ninguna camarilla** (`probe_triexact.jl`, `a1fd4eb`). En la zona de cláusulas,
  en llegadas y uniones, los triángulos sin camarilla son exactamente los prohibidos: 0 excepciones en unos 150 000.
  Un sentido es `AvoidV`, ya demostrado. El otro (**`TriComplete`**: un triángulo no prohibido está en una camarilla)
  es nuevo y está medido.
* **Cuenta el lado de la cima** (`227954a`). A veces el remitente solo tiene la camarilla con el valor opuesto del
  literal (320 casos). En todos ellos la cima de la cadena viene del otro remitente, que sí tiene la camarilla buena.
  En la llegada de la cima, el trío junto con la cima son cuatro nodos vecinos dos a dos y están en una camarilla:
  59 269 de 59 272.
* **Las 3 excepciones** (`d444766`, todas en `clause_mix`) son cadenas que dejan de estar vivas justo en su nodo más
  bajo: la cima forma con él un trío que cortan las dos llegadas. A partir de ahí la cadena puede mezclar los lados, y
  el trío de un solo lado resulta ser de la otra llegada.

Lo que se ve es:
1. **Mientras la cadena está viva, se queda en el lado de su cima.** Está demostrado (`liveChain_side`, bajo
   `CrossClosed`).
2. **En ese lado, lo que no está prohibido está en una camarilla.** Es `TriComplete`, medido.

## 6. Lo que dice la demostración de `liveChain_side`

La miré para ver si `CrossClosed` podía debilitarse. En `liveChain_side`, `CrossClosed` se aplica solo a cadenas de
`A` que además son **cadenas vivas de la unión**. Y no se usa para cortar nada: con la cadena viva en la unión, sirve
para concluir que la cadena no tiene ningún trío prohibido en `A`. Así que `good_join` bastaría con esta forma débil:

> **`CrossClosedL A B`**: en una cadena de `A` que es cadena viva de la unión, ningún trío está prohibido en `A`.

Pero hay una pega. Esa vida es la de la unión de la línea siguiente, la de las dos llegadas que se juntan después, y no
la de las cadenas de la propia entrada. El mecanismo de la §5 está medido en las cadenas de la entrada. Para enchufarlo
hace falta relacionar las dos vidas, y eso aún no está hecho.

## 7. Dónde estamos y siguientes pasos

| pieza | estado |
|---|---|
| todo el montaje (UP, join, pins, línea real, base, veredicto) | **demostrado** |
| antes de las cláusulas, la fusión central, desde la fusión final | **demostrado**, sin hipótesis |
| solidez de las familias con pins (`AvoidV`) | **demostrada**, sin hipótesis |
| `NoNewClose` ⇐ `HMixed` ⇐ `HClq` | **demostrado** |
| `HClq` (tríos de un solo lado en camarillas de la entrada) | abierto; 68 000/68 000 |
| `PinJoinSplitAll` (fijar y unir conmutan) | abierto; 10 692/10 692 |
| `TriComplete` (no prohibido ⇒ en una camarilla) | medido, 0 excepciones; no enunciado aún en Lean |
| el lector con pins (`readerVerdict`) | no conectado; el teorema es para la espina |

Las dos hipótesis abiertas son enunciados sobre el grafo de la máquina, sin familias, y cada una sobre un solo paso.
Siguen siendo el acuerdo entre ramas de los últimos informes, pero ahora con un mecanismo medido:
* la cadena viva se queda en el lado de su cima (demostrado);
* allí, lo que no está prohibido está en una camarilla (medido).

**Siguientes pasos**, en el orden que recomiendo:
1. **Formalizar `CrossClosedL`** y hacer que `good_join` la pida en vez de `CrossClosed`. Es mecánico y debilita la
   hipótesis sin perder nada.
2. **Medir `CrossClosedL` en la línea**: si en las cadenas de una entrada que son "vivas junto con la otra entrada" (sin
   ningún trío cortado por las dos) aparece alguna vez un trío prohibido. Si no, la hipótesis que queda es la forma
   viva, que es donde el mecanismo de la §5 aplica.
3. **Intentar `HClq` o `CrossClosedL` desde `TriComplete` + `liveChain_side`**, enunciando `TriComplete` como
   invariante de línea: la familia marca exactamente los grupos vecinos que no están en ninguna camarilla. Ya tenemos
   un sentido (`AvoidV`); el otro sería la hipótesis natural que queda, con forma de exactitud.
4. **`PinJoinSplitAll`**: medir si basta una forma más débil (solo en vivos, o solo para los pins que usan las otras
   piezas).
5. **Conectar el lector con pins** (`readerVerdict`) con el puente `pinF` / `Visited`. Es montaje.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `PreClause`, `CliqueSound`. Cambios en
`LiveDriver` (`HNew` más débil) y `LiveLine` (`Good` con paso $\ge 1$).

**Julia (`julia/improves_bingo/test_3sat/`):** `probe_hnewcl` (modos `PURE`, `CHAIN`, `DUMP`), `probe_triexact`, y
columnas nuevas en `probe_crossline`.

**Commits:** de `eea54d5` a `d444766` en la rama `reader-stuck`.
