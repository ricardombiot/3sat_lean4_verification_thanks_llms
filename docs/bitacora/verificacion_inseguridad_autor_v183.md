# Verificación para el Autor v183: todo tramo en una cadena — y la escalera reducida a Hellys de un paso

Ricardo, soy Claude (Opus 5.5). Este informe sigue al v182. Allí la parte colectiva («alguna entrada
común sobrevive compatible con todo el tramo») era el punto abierto, y el review simétrico se proponía
para simplificar las pasadas. Aquí se cuenta cómo esa parte colectiva **salió de las vueltas del
review**, qué pasó con la unión, y a qué ha quedado reducida la escalera del lector.

Rama `clean-two-phase`. `lake build AbsSat` verde (265 jobs), sin `sorry`, sin `Classical.choice`.
17 commits desde el v182 (`af3beeb`). Módulos nuevos: `SegExact.lean`, `SegExactUp.lean`,
`SegExactFilter.lean`, `SegExactAdm.lean`.

---

## 0. Dónde estamos, en una línea

```lean
theorem readerVerdictW_iff_of_helly (hStart : …) (hPin : …) (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ
```

El lector sin retroceso decide 3-SAT con dos hipótesis: la **línea final revisada no tiene tramos sin
cadena** (`hStart`) y, en cada pin del lector, **tres afirmaciones de un solo paso** sobre el estado de
antes, las tres de tipo Helly: la compatibilidad de cada nodo por separado implica una compatibilidad
común. El mecanismo del review —cascadas, purgas, pasadas— ya no aparece en ninguna hipótesis.

## 1. El cambio de invariante: `SegExact`

La pregunta del v182 era por qué, en cada vuelta, sobrevive una entrada común compatible con todo el
tramo. En vez de responderla vuelta a vuelta, se pidió algo más fuerte que el review conserve solo:

> **`SegExact`**: todo tramo (enlazado por padres, poseído por pares) se extiende, dentro de la global,
> a una cadena completa del paso 0 al último.

Es la versión por tramos de `TablesExact` (parejas), y tiene dos virtudes, las dos demostradas:

* **implica `SegGood`** (`segGood_of_segExact`): el nodo de la cadena en un paso fuera del tramo está en
  la tabla de todos los nodos del tramo a la vez. Es la entrada común colectiva, gratis;
* **el review lo conserva sin más** (`segExact_reviewAgg`): un tramo de después ya era tramo antes, su
  cadena es sana y el review no rompe cadenas sanas.

Con eso las vueltas del review dejan de ser el problema: no hacen falta ni tu postulado S1′ ni el review
simétrico **para esta ruta** (el v182 §3 sigue siendo una mejora posible, pero ya no está en el camino
principal).

Medido (`segexact`, semillas 1 y 7): 0 tramos sin cadena en los envíos (568.601) y en los estados del
lector (32.522).

## 2. UP, y la unión que mezcla

**UP conserva `SegExact`** (`segExact_addNode`). Un tramo solo con nodos antiguos ya era tramo antes
(las tablas solo ganan ids de la fila nueva) y su cadena crece con el hijo de fila de la cima; un tramo
que acaba en un nodo de fila `v` tiene el resto antiguo, con su cima padre de `v`, y su cadena más `v`
es la completa. Es tu argumento de que UP construye los caminos, como teorema: la fila nueva hereda la
compatibilidad de las cadenas que ya había.

**La unión, en cambio, mezcla**, como dijiste que debía: es una operación de compresión. Medido
(`segmix`, semilla 1, fórmula 6): 24 tramos mezclados de 142.778 —10 nodos compartidos y 2 solo de un
lado; cada pareja se posee en un lado, pero no todas en el mismo—, **ninguno en una cadena completa**, y
los 24 **sobreviven al review agresivo de la unión**: ese estado es un punto fijo de verdad de todas las
etapas (`cleanInvalid₂`, padres, hijos, barrido; medida 4.692 igual). Así que `SegExact` no es
invariante de la línea tras una unión, y las hipótesis que se probaron primero (`SegNoMix`, `MixDies`)
son **falsas**.

Tu frase fue la clave: *aunque se mezcle la información, las cadenas solo se formarán si han pasado por
los envíos correctos*. Medido (`baddie`, `mixtrace`): los tramos mezclados **mueren en el primer filtro
del envío siguiente**, en los 168 seguimientos, y en realidad en cualquier filtro que corte algo (1.260
de 1.260), por un **colapso masivo** —un filtro de envío lleva la medida de 4.692 a 2.303 en el primer
`cleanInvalid₂`—. La mezcla es estable mientras nadie exija nada.

## 3. La escalera se desprende de la línea

Mirando qué consume de verdad la escalera, dos observaciones la simplificaron mucho:

1. **De cada estado del lector solo usa una cadena sana.** En el primer estado ya la hay: la de la
   asignación que satisface. Así que el primer estado —la unión final, con posibles mezclas— no pide
   nada para el veredicto (`readerVerdictW_iff_of_readerPinnedSegExact`).
2. **Los pines del lector cortan siempre** (`pin_cuts`): `firstChoice` solo elige un paso con dos ids
   de mapa distintos.

Y con eso, **la escalera ya no necesita nada de la línea** (UP, unión, envíos): todo lo que pide está
en los estados del lector y en sus pines. Los teoremas de la línea siguen siendo ciertos y útiles, pero
el veredicto no los usa.

La primera formulación usaba `CutKillsMix` («un filtro que corta deshace la mezcla»). `mixtrace` mostró
que la mezcla cae por colapso masivo, no por un argumento local; un corte mínimo podría no bastar. La
escalera se reescribió sin él: `SegExact` en el primer estado del lector (`hStart`) y, por inducción,
cada pin lo conserva (`segExact_readFromR`).

## 4. De la completitud del review a Hellys de un paso

Lo que cada pin pide se fue reduciendo, con cada reducción demostrada:

| obligación | qué dice | cómo se reduce |
|---|---|---|
| `AdmittedExt` | todo tramo que sobrevive al pin tenía antes una cadena por un nodo admitido en el paso fijado | es la completitud del review tras un filtro, por tramos; `segExact_stepFilter_adm` la usa |
| `NodeAdmToChain` | si cada nodo del tramo tiene en su tabla una entrada admitida en el paso fijado, hay cadena por un nodo admitido | `admittedExt_of_nodeAdm`: un superviviente tiene esas entradas (sus nodos son válidos en el revisado). **Ya no menciona el review** |
| (a) `CommonAdm` | si cada nodo tiene su entrada admitida, hay **una** común | Helly de un paso |
| (b) `GapExact` | toda entrada común de un tramo se extiende con él a una cadena | `nodeAdmToChain_of`: (a) + (b) |
| (b) vecina | la entrada justo debajo o encima del tramo | **demostrada** (`gapExact_below/above`): owner vecino = padre/hijo (`AdjacentOwners`), simetría, `SegExact` |
| (b) con hueco | la entrada a más de un paso | **demostrada por inducción** (`gapExactFar_of_steps`) desde `GapStepBelow/Above`: en el paso vecino del tramo hay un nodo común al tramo y a la tabla de `r` |

El mecanismo detrás, medido (`admtrace`, semilla 1): de 39.334 tramos «condenados» (sin salida
admitida), **ninguno sobrevive**, y **los 39.334 tenían algún nodo sin entrada admitida en el paso
fijado** (36.310, el más cercano a él); caen en el primer `cleanInvalid₂` o con el grafo entero. Por eso
la reducción a `NodeAdmToChain` apunta al sitio correcto: un nodo sin entrada admitida es un nodo que la
purga elimina.

## 5. Lo que queda

| hipótesis | qué dice | medido |
|---|---|---|
| `hStart` | la línea final revisada (primer estado del lector) no tiene tramos sin cadena | 0 fallos, semillas 1 y 7 |
| `CommonAdm` (cada pin) | cada nodo con su entrada admitida en el paso fijado ⇒ una admitida común | 3.779/3.779 (`dos_de_tres`); semilla 1 en curso |
| `GapStepBelow/Above` (cada pin) | en el paso vecino del tramo, un nodo común al tramo y a la tabla de una entrada común lejana | equivale a (b): 4.009/4.009 (`dos_de_tres`); semilla 1 en curso |

Las tres son **afirmaciones de tipo Helly sobre las tablas de un único estado**: que la compatibilidad
de cada nodo por separado implique una compatibilidad común, paso a paso. Es tu argumento de
construcción —*si x, y, z tuvieran que estar en el mismo camino, tendrían un nodo en común en cada paso,
por cómo la máquina construye los caminos*—, ya aislado de todo lo demás.

## 6. Cómo seguir

Las hipótesis hablan de estados del lector, que son revisados de líneas construidas por UP. La vía
natural es la de `TablesExact`: demostrarlas como **invariantes de construcción** (UP las crea, el review
y los pines las conservan), igual que se hizo con parejas. La primera en estudiar es `CommonAdm`: dónde
nace la entrada admitida común y qué la mantiene cuando cada nodo tiene la suya.

## 7. Una frase sobre el tamaño de lo que queda

El v182 terminaba diciendo que, quitado todo el ruido, quedaba una pregunta: por qué, entre las
entradas comunes de un tramo, una sobrevive siempre compatible con todos. Ahora esa pregunta ya no tiene
review dentro: es un Helly de un paso sobre las tablas de un estado, y es exactamente lo que tu
construcción dice que se cumple.
