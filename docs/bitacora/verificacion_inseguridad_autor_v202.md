# Verificación para el Autor v202: `closed` es teorema, `union` se descompone y dónde se atasca

Ricardo, este informe cuenta lo que se hizo desde el v201 en `lean/improves_bingo` y `julia/improves_bingo`.
El v201 terminaba con el veredicto del lector demostrado bajo tres hipótesis medidas (`closed`, `union`, `skip`) y
una propuesta de cambio en el review. La propuesta se adoptó, `closed` pasó a ser teorema, `skip` se redujo a una
forma más limpia, y el resto del trabajo fue atacar `union`: se descompuso en piezas y se midió cada una. La
descomposición está demostrada, pero la pieza final, que las aristas de un solo lado no sobreviven, no ha cedido a
ningún argumento local. Todos los que se probaron se midieron falsos (§4).

**La conclusión, por adelantado.**
* **El veredicto queda bajo dos hipótesis**, `union` y `skip`, las dos de la forma «el núcleo de una unión es la
  unión de los núcleos» (`readerVerdict_iff_of_hyps`, sin `sorry`, solo los axiomas estándar).
* **`union` se descompone** (demostrado) en tres piezas en el paso de origen `c-2` del join:
  * `sep`: ningún nodo del mapa del origen está vivo en los dos lados. Medido: 0 fallos.
  * `split`: el núcleo de la unión se parte por el nodo del mapa del origen.
  * `side`: fijada la unión en un origen `b`, sus parejas son aristas del lado que tiene a `b`.

  `readerVerdict_iff_of_parts` es el veredicto bajo estas piezas y `skip`.
* **Las piezas no son más fáciles que `union`**: con los lados exactos, `KernelUnion` equivale a `SplitAt` junto
  con `SidePinned` (`kernelUnion_iff_split`).
* **Lo que la máquina hace bien, medido**: el review de la unión fijada en un origen no deja ninguna arista de un solo
  lado (`PinClean`: 0 supervivientes de 513 006).
* **Por qué no se demuestra**: todas las propiedades locales que lo explicarían son falsas. La causa común: las reglas
  del review dan testigos de dos en dos, y las aristas de un solo lado caen en cascada, unas por otras. Hace falta un
  argumento global.

---

## 1. El recorrido

| paso | commit | qué |
|---|---|---|
| comprobación final del review | `b699c68` | propuesta del v201 adoptada (Julia `FINAL_CHECK = :on`, Lean `finalPass` en `reviewFuel`); `closed` pasa a teorema (`closedState_review`) |
| `skip` | `c96eabc` | el UP, con o sin ventana saltada, conserva `KernelExact` bajo `AvoidExact` (`kernelExact_addNode_gen`); sin salto, `AvoidExact` es teorema |
| el núcleo son las camarillas | `1528e69` | toda camarilla es una estructura cerrada; `KernelExact` equivale a «el núcleo son las camarillas»; `kernel_split`; `AvoidExact` medido directamente |
| `union` en dos piezas | `b558fe7` | `KernelUnion` ⇐ `SplitAt` + `SidePinned`; sonda `probe_union_parts` |
| mitad estructural de `SidePinned` | `90e64bb` | fijada en un origen de `e`, toda estructura cerrada de la unión vive en `e` |
| enlaces completos | `6b164a0` | `LinksInv` (enlaces compatibles por ids y completos) lo conservan review, fila nueva y join; `SidePinned` se reduce a la adyacencia (`SideEdges`) |
| el veredicto por partes | `d779d25` | `LinksInv` en el invariante de la línea; `readerVerdict_iff_of_parts` |
| la equivalencia | `53a2061` | `kernelUnion_iff_split`; sonda de la cascada |
| la inducción descendente | `081df93`, `edacbb0` | `SideEdges` ⇐ `PinClean`; el paso de hijos; la inducción completa por conos bajo `ConeClosed`, que se mide falsa |

`lean/improves_bingo/AbsSatBingo/Model/` tiene ahora 8 732 líneas, sin `sorry`. La tabla de sincronía
Julia ↔ Lean (`docs/plans/lean_bingo.md`) tiene una fila por cada pieza.

## 2. `closed` y `skip`

**`closed`.** Las pasadas de padres e hijos solo corrían con `review_owners` activo: si la de hijos cortaba, el apoyo
por padres de un paso superior podía quedar roto sin que nadie lo repasara. Con la comprobación final, el review solo
sale cuando una vuelta completa con todas las reglas no cambia nada, y entonces el estado está cerrado por
construcción (`closedState_review`, `ClosedReview.lean`). Medido antes de adoptarlo: ningún cambio de veredicto,
solución ni estado en 176 ejecuciones, entre un 2 % y un 5 % más de tiempo.

**`skip`.** El UP que salta una ventana prohibida quita las cimas cuyo hijo cae en ella. La hipótesis se reescribió
como `AvoidExact` (`KernelSkip.lean`): las parejas de una estructura cerrada con cimas de hijo permitido están en
camarillas con cima de hijo permitido. Cuando no se salta nada es teorema (`avoidExact_of_noSkip`). Medida
directamente (`probe_avoidexact.jl`): 1 166 UP con salto, 2 467 estados juzgados, **0 fallos**. Es, como `union`, un
núcleo de una unión: evitar la ventana es juntar los pins de las cimas buenas.

## 3. `union`, pieza a pieza

### 3.1 El marco

En un join, los dos lados `e` y `g` están en el mismo nodo del mapa (paso `c-1`) y vienen de orígenes distintos en el
paso `c-2`. La unión `u` junta vivos y aristas. `KernelUnion e g` pide que, fijada en cualquier `P`, toda pareja del
núcleo de `u` esté en el núcleo de `e` o en el de `g`.

### 3.2 Las piezas y lo demostrado

* **`SplitAt`** (`UnionSplit.lean`): el núcleo de `u` fijado en `P` se parte por el nodo del mapa de `c-2`.
* **`SidePinned`**: fijar `u` en un origen `b` da el núcleo del lado de `b` fijado igual.
* **`kernelUnion_of_split`**: `KernelUnion` ⇐ `SplitAt` + `SidePinned`.
* **`kernelUnion_iff_split`** (`UnionEquiv.lean`): el recíproco, con los lados exactos y la separación. Se apoya en
  dos hechos, los dos demostrados:
  * toda estructura cerrada de un lado lo es de la unión;
  * fijada en un origen de un lado, el núcleo del otro lado está vacío.
* **La mitad estructural de `SidePinned`** (`alive_side`, `SideLinks.lean`): fijada en `b`, toda estructura cerrada
  de la unión vive en `e`. El testigo de cada nodo en el paso de origen es de `b`, `b` no está vivo en `g`, y la
  arista que los une viene de `e`.
* **Los enlaces** (`LinksInv`): un enlace padre/hijo solo une nodos cuyos ids encajan como desplazamiento de la
  ventana, y todo par vivo compatible que se posee está enlazado. Con esto, las reglas de enlace de una estructura
  cerrada de la unión pasan solas a `e` (`secStruct_side`), y `SidePinned` queda reducida a la adyacencia:
  **`SideEdges`**, las parejas de la estructura son aristas de `e`.
* **`SideEdges` ⇐ `PinClean`** (`SideDescent.lean`): basta con que el review de la unión fijada en `b` no deje
  aristas que `e` no tiene, porque toda estructura cerrada sobrevive al pin.

### 3.3 Las medidas

Todas con el mapa bin, en las 88 instancias del corpus.

| sonda | qué mide | resultado |
|---|---|---|
| `probe_union_parts.jl` | separación por el origen | 0 fallos en 7 311 joins |
| | `SharedAgree`: los lados coinciden en las aristas entre nodos compartidos | **falso**: 256 503 parejas en desacuerdo, en 79 instancias |
| | `PinnedSide`: fijar la unión en un origen da lo mismo que fijar el lado | 0 fallos en 43 866 comparaciones |
| `probe_side_cut.jl` | aristas de un solo lado que sobreviven al pin de la unión (`PinClean`) | **0 de 513 006** |
| | qué regla las corta | la regla de parejas o la muerte de un extremo; nunca las pasadas de padres/hijos |
| `probe_side_cascade.jl` | quién vacía el paso sin entrada común | ver §3.4 |

### 3.4 La cascada

Para cada arista de un solo lado que corta la regla de parejas se miró el paso más alto en que x y z se quedan sin
entrada común, y qué lo vació:

| paso sin entrada común | vaciado por | aristas |
|---|---|---|
| cima (`c-1`) | limpieza: mueren las cimas del otro lado, cuyo padre mató el pin | 116 030 |
| origen (`c-2`) | el propio pin | 57 018 |
| `c-3` | limpieza / corte de otra arista de un solo lado | 8 539 / 10 073 |
| `c-4` | limpieza / corte de otra arista de un solo lado | 11 270 / 8 145 |
| `c-5` o más abajo | limpieza / corte de otra arista de un solo lado | 30 309 / 15 119 |

**Nunca** las vacían las pasadas de padres/hijos, **nunca** el corte de una arista que tienen los dos lados, y
**nunca** estaban ya vacías antes de fijar. La cascada es cerrada: las aristas de un solo lado caen empujadas por el
pin, por la muerte de nodos y por otras aristas de un solo lado.

## 4. Lo que no funcionó

Cada intento fue un cierre local: una propiedad de `e` que obligaría a la arista x–z a estar en `e`. Todos se midieron
falsos.

| intento | enunciado | medida |
|---|---|---|
| `SharedAgree` | los dos lados coinciden en las aristas entre nodos compartidos | falso, 79 instancias |
| paso de hijos (`SonClosed`) | si `s` es hijo de `x` y posee a `z`, `x` posee a `z` | falso: 42 484 de 256 503 parejas, 72 instancias |
| triángulo en la cima | si una cima posee a x y a z, x posee a z | falso: la cascada tiene 57 018 casos con cima común y sin arista |
| triángulo en el origen | si un nodo de `b` posee a x y a z, x posee a z | falso: 83 455 casos de la cascada con origen común y sin arista |
| cono (`ConeClosed`) | un vecino común de `e` en cada paso por encima ⇒ arista | falso: 6 335 de 256 503 parejas, 64 instancias |

El caso del paso de hijos muestra el mecanismo: `s` puede heredar a `z` de otro padre que solo difiere de `x` en el
`gparent`. En los cinco casos la razón es la misma: las reglas del review dan testigos **de dos en dos**, y un
conjunto de testigos sueltos no obliga a que exista la arista. Es el obstáculo tipo Helly de siempre, ahora con dos
colores (los dos lados, o dos padres).

La inducción descendente por conos quedó formalizada (`sideEdges_of_cone`, `SideCone.lean`). Es correcta y su base
está demostrada:
* las parejas que tocan el origen son de `e` por la separación;
* las que tocan la cima también, porque ningún vivo de `g` es hijo de `b` (`OffSideUp`, que sale de la separación en
  un estado cerrado).

Pero su paso es `ConeClosed`, que es falso.

### Cambiar la máquina tampoco sirve aquí

Se estudió si un cambio en el join haría de `union` un teorema por construcción, como la comprobación final hizo con
`closed`.

* **Cortar las aristas de un solo lado pierde soluciones.** Una arista x–z que solo tiene `g` está en una camarilla de
  `g`, es decir, en un camino parcial real por un origen de `g`.
* **Lo que sobra no es la arista, sino un trío**: x–z de `g` junto con un origen `r` de `e`. Ese trío es falso, porque
  un camino real por r, x y z haría que `e` tuviera x–z. Pero la posesión es un grafo de parejas y no puede decir
  «x–z sí, pero no con r».
* **Las variantes sin pérdida** (no fundir los lados en el join, o marcar cada arista con los orígenes de su lado)
  guardan información de tríos o hacen crecer el número de gpaths por nodo del mapa.

Como la mezcla no aparece nunca en las medidas, el problema es de demostración, no de la máquina.

## 5. Dónde estamos

```
readerVerdict φ ⇔ Satisfiable φ
  ⇐ skip   (AvoidExact; 0 fallos en 2 467)
  ⇐ union  ⇔ SplitAt ∧ SidePinned                    [lados exactos + separación]
              SidePinned ⇐ sep ∧ SideEdgesAt          [demostrado, con LinksInv]
              SideEdges  ⇐ PinClean                   [demostrado; PinClean: 0 de 513 006]
              SideEdges  ⇐ ConeClosed                 [demostrado; ConeClosed FALSO]
```

Hay dos piezas abiertas: `SplitAt` y `PinClean`/`SideEdges`. Las dos son la misma pregunta: por qué una estructura
cerrada no puede combinar testigos de los dos lados.

## 6. El plan

* **Un argumento global para la cascada.** Tratar a la vez el conjunto de todas las aristas de un solo lado: probar que
  la mayor estructura cerrada de la unión fijada no contiene ninguna, no pareja por pareja sino como punto fijo. La
  cascada medida (§3.4) indica el orden: primero caen las de la cima y el origen, luego las demás por la muerte de
  nodos o por otras aristas de un solo lado.
* **`skip` por la misma vía.** Si el argumento global funciona para `union`, `AvoidExact` debería seguir igual.
