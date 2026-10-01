# Verificación para el Autor v221: la escalera de niveles, formalizada; el join deja de llevar hipótesis y todo queda en el filtro

2 de octubre de 2026, rama `reader-stuck`. Continúa el v220. En una frase: en vez de añadir cuartetos a la máquina, se
ha cambiado el **invariante** de la prueba. Ya no habla de listas de requisitos futuros ni de los dos lados de un join:
habla del estado tal cual, por niveles (nodos, aristas, triángulos de cima). Con él **el join y el UP quedan
demostrados sin hipótesis** en los tres niveles, y lo único abierto es **un paso del filtro**, en una forma que no
pasa de cuatro nodos.

## 0. Dónde estamos

| | v220 | v221 |
|---|---|---|
| veredicto | `spineVerdictOn_iff_of_topPins` bajo `TopSideAt` con pins | `spineVerdictOn_iff_of_nodeKeep` bajo `HypsNodeKeep` |
| la hipótesis habla de | un join, sus dos lados y **toda** lista de requisitos futuros | **un estado y un requisito**: el filtro de una llegada |
| el join | hipótesis | **demostrado** (niveles 1, 2 y 3) |
| el UP | demostrado (nivel 1) | **demostrado** (niveles 1, 2 y 3) |
| el filtro | escondido en las listas de pins | niveles 1 y 2 **demostrados** desde el nivel de encima; el nivel 3 es la hipótesis |
| propuesta de cuartetos (v220 §7) | pendiente | **no hace falta para enunciar la prueba**; queda como posible vía para demostrar lo que falta (§6) |

Lean: un módulo nuevo, `ForbidOnExact.lean` (860 líneas), `lake build` completo en verde, sin `sorry`, axiomas
estándar. Julia: dos sondas nuevas, `probe_width.jl` y `probe_exact3.jl`.

## 1. La pregunta

Ricardo, tras el v220: *cuartetos, quintetos, sextetos… niveles y niveles hacen la prueba inviable; debe haber otra
forma de verificar que el lector no se atasca.*

La sospecha es correcta en abstracto. `closed_not_chainInv` (ya en el repo) es un estado cerrado por parejas y sin
camarilla cuyo obstáculo es un cuarteto, y el mismo patrón sube un nivel cada vez. Una prueba basada en «cerrar por la
regla de nivel k» no termina. Lo que sigue es el recorrido de esta sesión: dos atajos descartados (§2), lo que ya
estaba demostrado y no se estaba usando así (§3), y el cambio de invariante (§4–§6).

## 2. Lo que se descartó: el estado final, visto como grafo suelto, no tiene estructura

Hay teoremas clásicos que garantizan lectura sin retroceso a partir de una propiedad del grafo final, sin mirar cómo
se construyó: Freuder (anchura `w` y consistencia fuerte `w+1`) y van Beek–Dechter (relaciones `m`-estrechas y
consistencia fuerte `m+2`). `probe_width.jl` mide las dos cosas, y una tercera, sobre el estado final revisado
(`FORBID=:on`):

| instancia | pasos | pares de pasos restringidos de verdad | anchura mínima | estrechez | soluciones | cuenta local, memoria 1 / 6 |
|---|---|---|---|---|---|---|
| `clause_mix` | 27 | 295 de 351 | 22 | 7 | 37 | 14 553 / 606 |
| `clause_mix_sep` | 33 | 320 de 528 | 16 | 7 | 296 | 133 056 / 6 384 |
| `rand3sat_v8_c10` | 49 | 1 030 de 1 176 | 41 | 6 | 92 | 677 382 664 / 110 889 |
| `v5_c20_i1` | 73 | 378 de 2 628 | 27 | 1 | 2 | 128 / 16 |

* **Anchura**: casi todos los pasos se restringen entre sí. Freuder pediría consistencia de nivel 17 a 42.
* **Estrechez**: 6–7 salvo en `v5_c20_i1` (casi todos sus pasos tienen un solo nodo vivo). Pediría nivel 8–9.
* **Memoria**: contar soluciones sin enumerarlas exigiría que lo local determinara lo global (toda secuencia cuyas
  ventanas de `d+1` pasos son camarillas es ya una camarilla). Con `d` hasta 6 la cuenta local sobrecuenta por
  órdenes de magnitud. Para contar hay que enumerar.

Conclusión: lo que hace que el lector no se atasque no es una propiedad estática del grafo. Tiene que salir de la
construcción.

## 3. Lo que ya estaba: las camarillas son exactas, y qué es un «resto»

* **No falta ninguna solución** (`run_carriesOn`) y **no sobra ninguna camarilla** (`verdictOn_certified`), las dos
  sin hipótesis. La enumeración de `probe_width.jl` da las mismas cuentas que el exhaustivo (37, 296, 92, 2), con
  cero callejones recorriendo **todas** las elecciones posibles de la cima hacia abajo. Esa enumeración es una
  verificación completa por instancia de «el lector no se atasca», con coste proporcional al número de soluciones.
* **Aclaración de Ricardo, que ordena todo lo demás**: un triángulo o un tetraedro hecho de nodos y aristas legítimos
  (cada uno de alguna camarilla) que juntos no caben en ninguna **no es un resto**. Es la consecuencia normal de que
  el grafo comprime muchas soluciones compartiendo piezas. Resto de verdad es solo un nodo o una arista en ninguna
  camarilla. Los niveles no miden cuánto hay que limpiar: miden cuánto hay que mirar para descubrir un nodo malo.

Con eso el objetivo queda en nivel 1: **toda cima viva de cada estado está en una camarilla**. La pregunta es qué
operación puede romperlo.

## 4. El invariante por niveles (`ForbidOnExact.lean`)

Tres propiedades del estado tal cual, sin fijar nada:

| nivel | nombre | dice |
|---|---|---|
| 1 | `TopCT` (ya existía) | toda cima viva está en una camarilla que esquiva los tríos |
| 2 | `TopEdge` | toda arista viva de una cima está en una camarilla |
| 3 | `TopTri` | todo triángulo sin prohibir con una cima está en una camarilla |

Operación por operación:

| operación | nivel 1 | nivel 2 | nivel 3 |
|---|---|---|---|
| **join** | `topCT_joinOn` | `topEdge_joinOn`: una arista de la unión es de un lado | `topTri_joinOn`: un triángulo que la unión no prohíbe no lo corta alguno de los lados (`tF_joinOn_of_cut`) |
| **UP** | `topCT_upOn` | `topEdge_upOn`: al vecino de la cima nueva lo posee un padre suyo | `topTri_upOn`: la cara de la cima nueva la sostiene un padre (`upOn_face_parent`) |
| **filtro** de un requisito | `topAt_of_topEdge`: **sale del nivel 2 de antes** | `topEdge_filterAllOn`: **sale del nivel 3 de antes** | **hipótesis** |

Todas las casillas salvo la última están demostradas sin hipótesis.

**Por qué el join ya no molesta.** El obstáculo del join era de cuatro nodos (v220 §7.2): una base muerta en un lado y
viva en el otro. Eso rompe el nivel 4, no el 3. Como el invariante se para en el nivel 3, el join lo conserva entero.

**Por qué el filtro baja un nivel.** Las dos demostraciones del filtro son la misma idea:

* *Nivel 1 desde el 2.* Una cima `t` que sobrevive al filtro y al review tiene un vecino vivo `w` en el paso del
  requisito (el estado revisado está cerrado por parejas). La arista `t–w` ya estaba antes; por el nivel 2 está en una
  camarilla; esa camarilla pasa por `w`, que es del requisito, así que sobrevive.
* *Nivel 2 desde el 3.* Una arista `t–w` que sobrevive tiene, en el punto fijo de la regla de tríos, un testigo bueno
  `s` en el paso del requisito (`trioGood_low`). El triángulo `(t, w, s)` estaba sin prohibir antes; por el nivel 3
  está en una camarilla, que pasa por `s` y sobrevive.

El mismo argumento para el nivel 3 da un tetraedro `(t, u, w, s)` con sus cuatro caras sin prohibir, y ahí se para:
nada garantiza que ese tetraedro esté en una camarilla (en `v7` hay tetraedros así que no lo están, las bases
revividas del v220).

## 5. La escalera, como teorema

`lInvP_advance` es el paso de la máquina para cualquier propiedad que pase el UP y el join (`OpsP`); `LInvP` es el
invariante de línea, sin listas de pins. Con «nivel k» = *el filtro de cada llegada de la máquina conserva la
propiedad de nivel k*:

```
HypsPinTetra  ⟹  HypsTriKeep (nivel 3)  ⟹  HypsEdgeKeep (nivel 2)  ⟹  HypsNodeKeep (nivel 1)  ⟹  veredicto
```

| veredicto | hipótesis | en lo medido |
|---|---|---|
| `spineVerdictOn_iff_of_nodeKeep` | tras el filtro de cada llegada, toda cima viva sigue en una camarilla | sin fallos |
| `spineVerdictOn_iff_of_edgeKeep` | lo mismo para las aristas de cima | sin fallos |
| `spineVerdictOn_iff_of_triKeep`, `_of_triFlt` | lo mismo para los triángulos de cima sin prohibir | sin fallos |
| `spineVerdictOn_iff_of_pinTetra` | `PinTetra` (§6) | sin fallos |

Las implicaciones entre niveles están demostradas (`hypsNodeKeep_of_edgeKeep`, `hypsEdgeKeep_of_triKeep`,
`hypsTriKeep_of_pinTetra`). `exact_of_triKeep`: bajo el nivel 3, **todo** estado de la máquina cumple los tres
niveles.

Dos lecturas de la escalera:

1. **La mínima es de nodos.** `HypsNodeKeep` es la frase de Ricardo restringida a donde hace falta: *tras cada filtro,
   toda cima viva está en una camarilla*. Un estado, un requisito, solo nodos.
2. **Cada peldaño se demuestra con el de encima.** Ese es exactamente el fenómeno que preocupaba, pero ahora está
   acotado: los peldaños 1 y 2 están cerrados, y el 3 es el último que el join deja pasar.

## 6. Lo que queda: `PinTetra`

**Enunciado.** En el remitente fijado en el requisito `r` de una llegada: un tetraedro `(t, u, w, s)` con `t` cima,
`s` en el paso de `r`, y sus cuatro caras sin prohibir, deja una camarilla **de la entrada** por `t`, `u` y `w` que
cumple `r`. No pide que la camarilla pase por `s`.

`topTriAt_of_pinTetra` demuestra el nivel 3 tras el filtro a partir de él. Cuando el testigo `s` es uno de los tres
nodos del triángulo (el requisito cae en un paso del triángulo) no hace falta nada: basta el nivel 3 de la entrada.

**Qué se sabe de él (razonado, no formalizado).**

* *En una entrada que es una unión.* La cima `t` es de un solo lado `A` (las cimas de un lado no existen en el
  otro), así que toda camarilla por `t` es de `A`. Las tres caras con `t` son de `A`. La base `(u, w, s)` puede no serlo: puede estar prohibida en `A`
  y viva por el otro lado. `PinTetra` falla ahí exactamente si una base revivida de ese tipo es el único testigo que
  le queda, en el paso del requisito, a un triángulo que en `A` fijado estaría muerto. Es el fenómeno del v220, pero
  ahora con **un** requisito y como condición sobre triángulos de cima.
* *En una entrada que es una llegada sola.* Bajar el tetraedro al remitente por los padres de `t` devuelve la misma
  pregunta un nivel de línea más abajo, con un requisito más. Los requisitos se apilan a lo largo del linaje; los
  objetos siguen siendo de cuatro nodos.
* *No es forzoso por lógica.* Con conjuntos de soluciones arbitrarios se puede construir un triángulo que conserva
  testigos buenos en todos los pasos y no está en ninguna camarilla tras fijar un color (una paridad de cuatro
  variables lo hace). Que no ocurra aquí depende de la máquina.

**Sobre los cuartetos del v220.** Guardar cuartetos anclados convertiría `PinTetra` en un hecho del punto fijo, pero
abriría la misma pregunta un nivel más arriba (el nivel 4 tras el filtro pediría el 5). Con el invariante de este
informe no hace falta ninguna regla nueva para *enunciar* la prueba: la máquina actual, en lo medido, ya conserva el
nivel 3. La cuestión es demostrarlo, no añadir memoria.

## 7. Medidas (`probe_exact3.jl`, `FORBID=:on`)

En cada estado se enumeran todas las camarillas y se compara con el grafo. La sonda mide **más** que Lean: todos los
nodos, aristas y triángulos sin prohibir, no solo los de cima. Grupos: remitentes tras el filtro (el estado de
`HypsTriFlt`), llegadas, uniones revisadas y estados finales.

| instancia | | estados | nodos fuera | aristas fuera | triángulos fuera | callejones |
|---|---|---|---|---|---|---|
| `clause_mix` | SAT | 197 | 0 de 8 910 | 0 de 159 489 | 0 de 1 517 255 | 0 |
| `clause_mix_sep` | SAT | 239 | 0 de 14 110 | 0 de 387 876 | 0 de 6 048 672 | 0 |
| `v5_c20_i1` | SAT | 502 | 0 de 30 364 | 0 de 741 574 | 0 de 11 777 688 | 0 |
| `v5_c20_i2` | UNSAT | 454 | 0 de 24 946 | 0 de 519 030 | 0 de 6 669 801 | 0 |
| `v6_c26_i1` | UNSAT | 560 | 0 de 41 065 | 0 de 1 153 551 | 0 de 19 884 687 | 0 |
| `v6_c26_i5` | SAT | 699 | 0 de 67 864 | 0 de 2 436 991 | 0 de 53 436 414 | 0 |
| `set011221_2004_i3_v7_c27` | en curso | 630 | 0 de 65 852 | 0 de 2 581 103 | 0 de 59 629 762 | 0 |
| `v7_c30_i2` | en curso | 460 | 0 de 38 803 | 0 de 1 248 023 | 0 de 22 593 390 | 0 |
| **total** | | **3 741** | de 291 914 | de 9 227 637 | de 181 557 669 | |

En los remitentes filtrados, además: los triángulos de cima con un nodo en el paso del requisito (no piden nada), los
tetraedros de `PinTetra` y cuántos no están en ninguna camarilla.

| instancia | remitentes filtrados | triángulos de cima (fuera) | con un nodo en el paso del requisito | tetraedros de `PinTetra` | en ninguna camarilla |
|---|---|---|---|---|---|
| `clause_mix` | 80 | 71 976 (0) | 7 050 | 55 438 | 0 |
| `clause_mix_sep` | 98 | 218 367 (0) | 22 833 | 198 275 | 0 |
| `v5_c20_i1` | 210 | 293 113 (0) | 15 368 | 282 516 | 0 |
| `v5_c20_i2` | 191 | 205 707 (0) | 12 774 | 194 713 | 0 |
| `v6_c26_i1` | 235 | 487 695 (0) | sin medir | sin medir | sin medir |
| `v6_c26_i5` | 290 | 1 000 448 (0) | sin medir | sin medir | sin medir |
| `set011221_2004_i3_v7_c27` | 260 | 1 150 866 (0) | 45 835 | 1 200 774 | 0 |
| `v7_c30_i2` | 190 | 571 548 (0) | 31 550 | 605 131 | 0 |

`set011221_2004_i3_v7_c27` es la instancia donde cayeron `PrevCut`, `CrossCut`, `StarTriAt` y `Star4At`.

**Las dos filas `v7` son parciales**: las tandas con el grupo de remitentes filtrados seguían corriendo al cerrar este
informe (cifras del volcado parcial). De `set011221_2004_i3_v7_c27` sí hay una tanda anterior **completa**, sin ese
grupo: 419 estados (298 llegadas, 120 uniones revisadas, el final), 0 de 30 684 nodos, 0 de 1 277 194 aristas y 0 de
32 735 511 triángulos fuera en las llegadas; 0 de 20 908 070 triángulos en las uniones. En las dos `v6` los tetraedros
no se midieron (la columna se añadió después de lanzarlas).

**Espejo con Lean.** La camarilla de la sonda pide vecindad dos a dos y ningún trío prohibido; la de Lean (`CT`) pide
además los enlaces padre–hijo. Con `EXACT_LINKS=1` la sonda los exige también: en `clause_mix`, `clause_mix_sep` y
`v5_c20_i1` da las mismas camarillas y los mismos ceros.

## 8. Lo que no se sabe

* **Si `PinTetra` es cierto en general.** Ninguna de las hipótesis anteriores sobrevivió a `v7`; esta sí, en lo
  medido, pero son ocho instancias, dos de ellas con la tanda sin terminar.
* **Instancias de paridad.** No se ha medido ninguna con esta sonda. Son la familia donde las reglas de nivel fijo
  fallan en la literatura. `tseitin_petersen_H` está en el corpus (más de 20 minutos solo la máquina). Es una búsqueda
  de contraejemplo: pendiente de permiso.
* **`v8`.** Sin medir.
* **Estados con muchas camarillas.** La enumeración lleva un tope (50 000 por estado); en lo medido no se alcanzó
  (máximo 128).

## 9. Lo que es falso o no sirve (para no volver)

| afirmación | medida o razón |
|---|---|
| el estado final tiene anchura pequeña | anchura mínima 16–41 de 27–49 pasos |
| las relaciones entre pasos son estrechas | estrechez 6–7 |
| se pueden contar las camarillas con memoria corta | la cuenta local sobrecuenta hasta `d = 6` |
| el nivel 4 es invariante | falso en el join (bases revividas, v220); por eso el invariante se para en el 3 |
| contadores llevados por la máquina darían el número de soluciones | el join suma, pero el filtro pide cuentas por parejas, luego por tríos: la misma escalera |

## 10. Plan

1. Decidir si se mide `probe_exact3.jl` en una instancia de paridad y en `v8` (búsqueda de contraejemplo).
2. Atacar `PinTetra` por sus dos casos: la unión (un requisito, base revivida) y la llegada sola (el linaje).
3. Si `PinTetra` cae en alguna instancia, queda en pie el veredicto certificado (`verdictOn_certified`) y la
   enumeración como verificación por instancia; y la escalera dice exactamente en qué filtro y a qué nivel falló.

## Ficheros y teoremas

| fichero | qué tiene |
|---|---|
| `ForbidOnExact` | `TopEdge`, `TopTri`; join: `topEdge_joinOn`, `topTri_joinOn`; filtro: `topAt_of_topEdge`, `topCT_filter_of_topEdge`, `topEdgeAt_of_topTri`, `topEdge_filterAllOn`, `PinTetra`, `topTriAt_of_pinTetra`, `topTri_filterAllOn`; UP: `rowParent_of_newAdj`, `ct_ext_top`, `topEdge_upOn`, `topTri_upOn`; línea: `LInvX`, `lInvX_init`, `lInvX_advance`, `LInvP`, `OpsP`, `lInvP_advance`; hipótesis: `HypsNodeKeep`, `HypsEdgeKeep`, `HypsTriKeep`, `HypsTriFlt`, `HypsPinTetra` y sus implicaciones; `exact_of_triKeep`; los cinco veredictos del §5 |

Sondas nuevas: `probe_width.jl` (anchura, estrechez, cuenta de camarillas, cuenta local), `probe_exact3.jl` (exactitud
por niveles en todos los estados; grupo `flt` = el estado de la hipótesis). Tabla de sincronía Julia–Lean:
`docs/plans/lean_bingo.md`.
