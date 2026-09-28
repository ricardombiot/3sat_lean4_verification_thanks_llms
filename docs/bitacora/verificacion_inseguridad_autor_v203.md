# Verificación para el Autor v203: `skip` desaparece y la unión se reduce a la estrella de una cima

Ricardo, este informe cuenta lo que se hizo desde el v202 en `lean/improves_bingo` y `julia/improves_bingo`, y
propone los pasos siguientes. El v202 terminaba con el veredicto del lector bajo dos hipótesis (`union` y `skip`) y
con todas las descomposiciones de `union` en piezas locales medidas falsas. Desde entonces hubo dos cambios de
enfoque:

* **Pedir menos.** El lector no necesita que **cada pareja** del núcleo esté en una camarilla (`KernelExact`), solo
  que lo esté **cada cima**. Con esa exactitud más débil, el UP deja de necesitar hipótesis y `skip` desaparece.
* **Mirar la estrella de una cima.** La hipótesis que queda en el join habla de un solo nodo y de su vecindad, y
  ahí el obstáculo tipo Helly no aparece: todas las parejas pasan por la cima.

**La conclusión, por adelantado.**
* **`readerVerdict_iff_of_topUnion`** (`ReaderTop.lean`, sin `sorry`, solo los axiomas estándar): el lector dice SAT
  exactamente cuando la fórmula es satisfacible, bajo **una sola hipótesis**, `TopUnion`: en cada join, una cima del
  núcleo de la unión fijada está en el núcleo de algún lado.
* **`readerVerdict_iff_of_star`**: lo mismo bajo tres hipótesis más concretas, las tres medidas sin fallos:
  * `TopStarK`: una cima del núcleo de la unión fijada está en una estructura cerrada que vive en su estrella;
  * `SepAt`: ningún origen está vivo en los dos lados;
  * `Absorb`: revisar la unión sin los nodos del otro lado devuelve el lado.
* **`skip` ya no es hipótesis**: el UP conserva la nueva exactitud (`TopExact`) con o sin ventana saltada.
* **Lo que sigue abierto** es de la misma naturaleza que antes (que la unión no fabrique estructura mezclando lados),
  pero ahora **local**: una cima y su estrella, o los vivos de un lado.

---

## 1. El recorrido

| paso | commit | qué |
|---|---|---|
| desdoblar nodos | `87f8c2a` | la idea de mantener copias de los nodos compartidos en «superposición»: **no hay cota** (21 % de los compartidos, persiste tras el pin en el 44 % de los envíos, hasta 123 nodos, creciendo con la instancia); descartada como cambio de máquina |
| `Absorb` | `1045e89`, `7480215` | `SidePinned` ⇐ `Absorb`, una igualdad de reviews por lado sin pins; medida: 0 fallos en 14 622 lados |
| `GenAbsorb`, `AncKernel` | `8aa9d65` | `Absorb` entre dos estados cualesquiera del mismo paso: 0 fallos en 10 500 pares. `AncKernel` (el estado es el núcleo de la ascendencia pura sobre sus vivos): **falso**, las tablas llevan historia |
| `KAbsorb` | `5687e6e` | la forma con estructuras; entre nodos del mapa distintos sale de `KernelUnion` del mismo paso. La inducción «un paso abajo» no avanza: exige partir antes la estructura en el paso nuevo |
| `SplitAt` por testigos | `bc50def` … `8d24053` | `SplitAt` medido sin fallos (23,4 M parejas); algún testigo siempre sirve, no cualquiera; las descomposiciones por testigos se miden **falsas** (61 casos) y vuelven a `KernelUnion` |
| **`TopExact`** | `1bdf816` | la exactitud solo para las cimas; el UP la conserva sin hipótesis; **veredicto bajo `TopUnion` sola** |
| `TopSplit`, la estrella | `30d0a48`, `440ffc3` | `TopUnion` ⇐ `TopSplit` + `SidePinned`; `TopSplit` ⇐ `TopStarK` + `TopNbr`; invariantes `TopsApart`, `TopNbr`; **veredicto bajo `TopStarK` + `SepAt` + `Absorb`** |

`lean/improves_bingo/AbsSatBingo/Model/` tiene ahora 9 825 líneas, sin `sorry`. La tabla de sincronía
(`docs/plans/lean_bingo.md`) tiene una fila por pieza.

## 2. Pedir menos: `TopExact`

**`TopExact g`** (`TopExact.lean`): una cima (un nodo del último paso) del núcleo de `g` fijado en `P` está en una
camarilla que concuerda con `P`. Es `KernelExact` restringida a la pareja (cima, cima).

**Por qué basta para el lector** (`noZombie_of_topExact`). Un estado del lector válido tiene alguna cima viva. El
estado está cerrado (`closedState_review`, del v202), así que esa cima está en su núcleo, y `TopExact` le da una
camarilla. Eso es `NoZombie`, lo único que pide el teorema del veredicto.

**Por qué el UP la conserva sin hipótesis** (`topExact_addNode`). Una cima nueva del núcleo tiene su padre en la
estructura. Ese padre es una cima vieja del núcleo, así que por `TopExact` del estado anterior está en una camarilla,
y su hijo, la cima nueva, la alarga. La cima nueva existe, así que su ventana no estaba prohibida: el hijo es
permitido por construcción. Con `KernelExact` hacía falta alargar camarillas de parejas cualesquiera, cuya cima podía
tener el hijo prohibido; de ahí salía `skip` (`AvoidExact`). Con las cimas, esa situación no se da.

**El join** la conserva bajo **`TopUnion`**: una cima del núcleo de la unión fijada está en el núcleo de algún lado.
`TopUnion` es más débil que `KernelUnion`: habla de un nodo, no de parejas.

La cadena entera del lector se rehízo sobre `TopExact` (`ReaderTop.lean`), reutilizando la contabilidad y el cierre
del v202, y da **`readerVerdict_iff_of_topUnion`**.

## 3. La estrella de una cima

### 3.1 Qué es `TopUnion` en la unión

En un join, las cimas son de un solo lado: las de `e` tienen su padre en un origen de `e`, las de `g` en uno de `g`.
Una cima de `e` solo tiene aristas de `e`. La pregunta de `TopUnion` es: si una cima de `e` está viva en la unión
fijada, ¿lo está en `e` fijado?

### 3.2 Las piezas demostradas

* **`TopSplit`**: `SplitAt` solo para las cimas: la cima sobrevive fijando un origen. `TopUnion` ⇐ `TopSplit` +
  `SidePinned` (`topUnion_of_topSplit`), y `SidePinned` ya salía de `Absorb` en el v202 (`topUnion_of_absorb`).
* **`TopStarK`**: la cima está en una estructura cerrada que vive en su **estrella** (la cima y los nodos que posee).
* **`topSplit_of_topStar`**: una estructura así concuerda con el origen de la cima. Sus nodos del paso de origen los
  posee la cima, y una cima, en el paso de sus padres, solo posee a sus padres (`TopNbr`). Por tanto todos tienen el
  id del origen de la cima. **No hay problema de Helly**: todas las parejas de la estructura pasan por la cima.
* **Invariantes** `TopsApart` (dos cimas distintas no se poseen) y `TopNbr`, demostrados para el review, la selección,
  el UP, el join y la semilla, y añadidos al invariante de la línea.
* **`readerVerdict_iff_of_star`**: el veredicto bajo `TopStarK`, `SepAt` y `Absorb`.

### 3.3 Las medidas

Todas con el mapa bin, en el corpus de 88 instancias (las sondas de la estrella, sobre unas 28 cuando se pararon).

| propiedad | resultado |
|---|---|
| `Absorb` (cada lado de cada join) | 0 fallos en 14 622 lados; 256 503 aristas de más absorbidas |
| `GenAbsorb` (cualquier par de estados del mismo paso) | 0 fallos en 10 500 pares |
| `SplitAt` | 0 fallos en 23,4 M parejas |
| `TopSplit`, `TopUnion` | 0 fallos en 9 258 cimas |
| `StarClosed`: la estrella ya es cerrada | **falso**, ~7 % de las cimas de la unión, ~2 % tras un UP |
| **`TopStar`**: el review de la estrella conserva la cima | **0 fallos** en 7 464 cimas de uniones y 9 880 tras un UP |

`StarClosed` falso y `TopStar` sin fallos dicen que la estrella no es cerrada tal cual, pero su núcleo sí contiene
a la cima: el review de la estrella corta algo y la cima sobrevive.

## 4. Lo que no funcionó

| intento | por qué no |
|---|---|
| desdoblar los nodos compartidos | sin cota: la superposición persiste y crece con la instancia |
| `AncKernel` | falso: un estado no está determinado por sus vivos, las tablas llevan historia |
| inducción un paso abajo (NoMix en `T` ⇒ `GenAbsorb` en `T+1`) | para bajar hay que partir antes la estructura en el paso nuevo, que es `SplitAt` |
| testigos (`OwnSideGood`, `PairIn`, `TriIn`) | falsos, 61 casos en `set5830_20211201_i3_v8_c30`: aristas de los dos lados para las que solo sirve el testigo de uno |
| `WitAll` (cualquier testigo sirve) | trivial en el paso de origen de un lado; falso en los demás pasos, incluso en estados revisados |
| cambiar el orden del lector (de la cima hacia abajo) | tampoco evita `SplitAt`: al elegir el origen siguiente la estructura puede mezclar |
| marcas en las aristas, review especial del join | o no cortan nada, o solo certifican el caso sin pins, o guardan tríos y explotan |

## 5. Dónde estamos

```
readerVerdict φ ⇔ Satisfiable φ
  ⇐ TopUnion                                        [ReaderTop: sin skip]
      ⇐ TopSplit ∧ SidePinned
            TopSplit   ⇐ TopStarK ∧ TopNbr            [TopNbr: invariante demostrado]
            SidePinned ⇐ SepAt ∧ Absorb ∧ LinksInv     [LinksInv: invariante demostrado]
```

Las hipótesis que quedan son `TopStarK`, `SepAt` y `Absorb`. `SepAt` es una propiedad de los orígenes del mapa en el
join, previsiblemente estructural. `TopStarK` y `Absorb` son la misma afirmación de fondo, **el review no fabrica
estructura mezclando lados**, pero ahora sobre un conjunto de nodos acotado:

* `Absorb`: los vivos de un lado;
* `TopStarK`: la estrella de una cima (que vive entera en un lado).

## 6. La propuesta: los pasos siguientes

### Paso 1 — Unificar `TopStarK` y `Absorb` en una sola afirmación local

**Qué.** Enunciar **`LocalAbsorb`**: para un conjunto `W` de nodos vivos de un lado `e`, el núcleo de la unión fijada
en `P` y restringida a `W` es el núcleo de `e` fijado en `P` y restringido a `W`. Con `W` = los vivos de `e` es
`Absorb` (con pins). Con `W` = la estrella de una cima de `e`, da `TopUnion` directamente: la cima sobrevive en la
estrella de la unión, luego en la de `e`, luego en el núcleo de `e`.

**Qué espero.** Que la medida dé 0 fallos (lo implican `TopUnion` y `Absorb`, ya medidos) y que la reducción
`TopUnion` ⇐ `LocalAbsorb` sea corta en Lean, con los lemas que ya hay (supervivencia al review, monotonía,
`LinksInv`). Resultado: una sola hipótesis, local y sin pins en su forma más simple.

### Paso 2 — Medir la cascada dentro de la estrella

**Qué.** Para las cimas de la unión fijada, comparar el review de la estrella en la unión con el de la estrella en el
lado: qué aristas de un solo lado hay en la estrella, qué regla las corta, y en qué orden.

**Qué espero.** Que la estrella sea un caso pequeño de la cascada del v202: las aristas del otro lado entre vecinos de
la cima caen por el pin o por la muerte de nodos, nunca sosteniendo a la cima. Si aparece un patrón fijo (por ejemplo,
que siempre caen en la primera vuelta porque en la estrella ya no hay testigo del otro lado), será la pista para el
paso 3.

### Paso 3 — Intentar `LocalAbsorb` por el punto fijo, en la estrella

**Qué.** En la estrella, todo pasa por la cima, y la cima solo tiene aristas de `e`. El intento: demostrar que la mayor
estructura cerrada de la unión dentro de la estrella no puede usar una arista que solo tiene `g`, porque su testigo en
el paso de origen es un padre de la cima, que es de `e`, y en la cima es la propia cima. Esto es lo que en el v202
fallaba pareja por pareja (`ConeClosed`); la diferencia es que ahora los testigos de los pasos de arriba están
**fijados**: son la cima y sus padres.

**Qué espero.** No lo sé. Es el único sitio donde el obstáculo tipo Helly tiene la forma más débil que hemos visto (una
estrella con centro fijo). Si sale, `TopUnion` pasa a teorema y **el veredicto del lector queda demostrado bajo
`SepAt` y `Absorb`**. Si no sale, la medida del paso 2 dirá qué falta, igual que las cascadas del v202 dijeron por qué
fallaban los cierres locales.

### Paso 4 — `SepAt` como teorema

**Qué.** Demostrar que dos llegadas al mismo nodo del mapa vienen de orígenes con ids distintos. Es una propiedad de
cómo el lector de la línea (`Driver.insert`) junta estados por clave, y de que las cimas de un estado tienen el id de su
clave.

**Qué espero.** Que sea contabilidad, como `TopNbr`: un invariante más de la línea.

### Paso 5 — Sincronía con Julia

**Qué.** Llevar a Julia las comprobaciones con el mismo nombre (`top_star_ok`, `absorb_ok`), con tests, y actualizar la
tabla de sincronía. `Absorb` y `SepAt` son comprobables en cada join en tiempo polinómico. Así, una ejecución de la
máquina puede **certificar** esas dos hipótesis para su instancia. `TopStarK` no, porque habla de todos los pins.

**Qué espero.** Un certificado por ejecución para dos de las tres hipótesis, sin cambiar el comportamiento de la
máquina, y la tabla de sincronía al día.

### Orden y criterio

Los pasos 1 y 2 son baratos y dicen si el 3 tiene sentido. El 4 y el 5 son independientes y se pueden hacer en
cualquier momento. El criterio para parar el paso 3 es el mismo de siempre: si el argumento de la estrella se mide
falso en algún caso, se documenta como los de la §4 y se vuelve a pensar, en vez de insistir.
