# Verificación para el Autor v165: la ruta C, validez en lugar de exactitud

Ricardo, soy Claude (Opus 5). Este informe sigue a v164. Rama `spaik`, módulo nuevo
`HereditaryValid.lean`. El build de `AbsSat` (231 jobs) pasa sin `sorry`, con axiomas
`[propext, Quot.sound]`.

## 0. Resumen

* **Cambio de ruta.** Ya no hace falta que las tablas sean exactas. La prueba lleva de línea en línea
  un invariante más débil: **si un estado sigue válido tras fijar valores, existe un camino real por
  esos valores**. Los pares ajenos de la unión, que la máquina guarda (medido en v163), dejan de ser
  un obstáculo.
* **Demostrado:** la inducción completa, el alargamiento de un camino por un hijo del mapa y la
  conmutación de fijar con el envío (`SendPinAt`), esta última sin hipótesis.
* **Queda una sola hipótesis:** `ValidSideAt`, que dice que la validez no se toma prestada en la
  unión. Se reduce a `OwnSupportAt`, el soporte propio de un lado. La medida no encuentra ningún
  fallo, y resulta más fuerte de lo pedido: **todo** lado con la cima viva pasa.

## 1. El invariante: `ValidWitAt`

> Si un estado de la línea `m` sigue válido tras fijar valores de literales Q, existe un camino
> parcial real (cláusulas satisfechas hasta ese paso) que llega a su clave y pasa por todos los
> valores de Q.

En la última línea, sin fijar nada, ese camino es un modelo de la fórmula (`sat_of_validSide`).
Ninguna parte habla de relaciones entre nodos, solo de validez.

## 2. Lo demostrado

| pieza | qué dice |
|---|---|
| `extend_son` | un camino real que pasa por los requisitos de un hijo del mapa se alarga con ese hijo. Cubre todos los tipos de paso: variable nueva, su negación, las dos fusiones y las filas de cláusula |
| `topPin_keyL` | en un estado válido, un valor fijado en el paso de la cima es la clave del estado |
| `req_lit` | los requisitos de un nodo del mapa son valores de literales |
| `validWit_zero`, `validWit_succ` | el invariante en la línea 0 y su paso de una línea a la siguiente |
| **`pinned_source_validL`, `sendPin`** | **si un envío fijado es válido, su origen fijado (con los requisitos del hijo) es válido.** La parte del envío bajo la cima es un soporte del origen que respeta los requisitos y los fijados, y sobrevive a fijar y revisar (`AOk_filterAllAgg`) |
| `sat_of_validSideOnly` | el veredicto bajo `ValidSideAt` y nada más |

Detalle técnico: dos llamadas a `omega` introducían `Classical.choice`. Una cerraba una meta que no
era aritmética; la otra usaba una conjunción negada. Las reescribí de forma constructiva.

## 3. Lo que queda: la validez no se toma prestada

> **`ValidSideAt`**: si la unión fijada es válida, algún lado fijado es válido.

**Reducción demostrada** (`validSide_of_ownSupport`, `sat_of_ownSupport`) a:

> **`OwnSupportAt`**: en la unión fijada X, hay un lado cuya cima t sigue viva y cumple esto: los
> nodos que son dueños de t en X, con los pares que **el propio lado** lleva (sin los pares ajenos),
> forman un soporte del envío de ese lado.

Un soporte así respeta los fijados, porque sus nodos son nodos de X. Por eso sobrevive a fijar y
revisar el envío del lado, y ese envío fijado queda válido.

**Medida** (sonda `ownsupport`, fórmulas aleatorias de 3 y 4 variables, 8 semillas):

| uniones fijadas válidas | con algún lado fijado válido | con soporte propio en algún lado | sin ninguno | lados con cima viva comprobados | fallos |
|---|---|---|---|---|---|
| 32.960 | 32.960 | 32.960 | **0** | 52.506 | **0** |

Todos los lados con la cima viva forman su propio soporte, no solo alguno.

## 4. El intento de demostración de `OwnSupportAt`

Sea X la unión fijada, t la cima viva del lado k y O los nodos que son dueños de t en X.

* **Reglas estructurales** (`gow`, `node`, `step`, `dom`, `own`, `sym`, `link`): salen de que la cima
  solo existe en su lado y de que la unión solo junta tablas. Son laboriosas pero seguras.
* **Reglas de cierre** (`cov`, `agg`, `par`, `son`): son el núcleo. Por ejemplo `cov`: para a en O y
  un paso l, hace falta un b de O en el paso l con el par (a, b) en X **y en la tabla del lado k**.

El review agresivo aplicado al par (a, t) da un z del lado k que es dueño común de a y de t. Pero el
par (a, z) puede venir de otro lado j donde a y z también están. Las reglas del review miran cada par
por separado y no distinguen de qué lado vino una fila de dueños. Que siempre exista un z **propio**
depende de cómo se construyen las tablas de los lados a lo largo de la historia.

## 5. La traza del caso construido, por lados

Esto completa v164, sección 4:

* **x→v:** en la unión la aportan los lados 63.4 y 63.6. Tras fijar C = 1, la revisión agresiva la
  elimina, y ningún lado la conserva.
* **Lados tras fijar:** 63.1, 63.2 y 63.3 siguen válidos; 63.4 a 63.7 quedan inválidos. Es un
  ejemplo de `ValidSideAt`.
* **Un par ajeno inofensivo:** la cima de 63.2 es común a x y v, pero 63.2 no lleva x→v. La unión la
  elimina de todas formas.

## 6. Estado de la cadena del veredicto

| ruta | depende de | estado |
|---|---|---|
| exactitud (`SideKeepAt`) | `ClosedWitnessAt` y otras | abierta; `SemWitnessAt` es falsa |
| lector sin retroceso | `ProgressAgg` | abierta; su respuesta positiva es correcta sin hipótesis |
| **ruta C** | **`OwnSupportAt`** (o `ValidSideAt`) | **una hipótesis, 0 fallos medidos** |

## 7. Siguientes pasos propuestos

1. **Demostrar las reglas estructurales** del soporte propio y dejar `OwnSupportAt` reducida a sus
   cuatro reglas de cierre.
2. **Buscar el invariante histórico:** trazar un caso donde el z que da el review sea ajeno, para ver
   qué nodo propio lo sustituye y por qué existe. Eso daría el enunciado que se lleva de línea en
   línea.

Commits: `4ec9b2f` (ruta C), `a6e6142` (`SendPinAt` demostrada), `2830243` (`OwnSupportAt` y sonda).
