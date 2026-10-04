# Verificación para el Autor v150: la ruta de construcción — el envío contiene un camino

Ricardo, soy Claude (Opus 5). Tras v149 me dijiste que estaba sesgado y que confiara en el diseño. Seguí tu
nota: *si el estado de origen está bien y el envío (fijar los requisitos del destino, revisar, UP) sale
válido, el conjunto contiene al menos un camino parcialmente construido*. Este informe recoge esa ruta, cómo
la he ido reduciendo y el estado general.

Rama `spaik`, build de `AbsSat` (221 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Commits
`dbf0c56`, `7ad77ca`, `bb1eff2`. Módulos: `RunInhabited.lean`, `RunSteps.lean`, `WeakNoop.lean`.

---

## 1. La idea: demostrar el veredicto por inducción sobre la ejecución

Las rutas anteriores partían del estado final y buscaban hacia atrás un camino. Esta va hacia delante, como
la máquina: **todo estado que la máquina guarda contiene caminos parciales**, y se conserva paso a paso.

El invariante (`SoundAt`): *en un estado guardado, toda entrada "el nodo x posee al nodo q", con q en un paso
de literal, está sobre un camino parcial del propio estado que pasa por x y por q*. Pide mucho menos que la
exactitud completa de v144: solo las entradas hacia los literales, y solo que estén en **algún** camino.

## 2. Qué conserva el invariante (sin hipótesis)

| paso de la máquina | resultado |
|---|---|
| semilla | `soundAt_initSeed` |
| unión en destino (`impact!`) | `soundAt_join` |
| UP (añadir el nodo destino) | `soundAt_addNode` |
| review sin fijar nada | `soundAt_review` (el review no pierde caminos) |
| mover el invariante entre estados que se contienen | `soundAt_of_embedded` |
| el estado final válido con el invariante ⇒ satisfacible | `sat_of_soundAt` |

Queda un solo paso: el **envío** (fijar los requisitos del destino y revisar). `FilterSoundAt` lo pide solo
en los envíos reales de la ejecución, desde un estado que ya cumple el invariante.

## 3. El envío, desmontado

1. **Un envío son sus pasos** (`filterSoundAt_of_steps`, por `full_seq`): basta con conservar el invariante
   al aplicar un requisito débil cada vez y un requisito (fijación) cada vez.
2. **Los requisitos de un destino están todos en pasos de literal** (`reqOfCnf_lit`).
3. **Fijar un nodo libera su propio paso** (`pinStep_of_pairs`): una entrada hacia el paso fijado estaba en un
   camino antes de fijar; ese camino pasa por el nodo fijado, luego sobrevive.
4. **Los requisitos débiles no cambian nada** (`WeakNoop`, nuevo). Era tu optimización (v144 midió tablas
   idénticas con y sin ellos); ahora está demostrado por qué: lo que el filtro débil quitaría **contradice una
   fijación**, y en el estado fijado y revisado ningún nodo vivo contradice una fijación, porque sus
   requisitos le obligan a poseer el nodo fijado, que lleva el valor fijado.
   * `lit_consistent`: un nodo vivo en un paso de literal coincide con toda fijación de su variable;
   * `fixes_consistent`: igual para todo valor que el nodo fija, propio o por sus requisitos;
   * `weak_member`: todo nodo vivo pasa los requisitos débiles;
   * `filterSoundAt_of_pins`: el envío con y sin filtro débil son el mismo estado (se contienen
     mutuamente), así que el invariante solo necesita las fijaciones de una en una.

Con eso `WeakStepSoundAt` desaparece y el veredicto queda bajo una sola hipótesis:

```lean
theorem sat_of_pinPairs (hwf : WF φ) (hP : PinPairSoundAt φ) (kv) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ
```

## 4. El núcleo que queda: `PinPairSoundAt`

> En un estado válido del lector que cumple el invariante, **fijar un nodo r en un paso de literal y revisar**,
> si sale válido, deja toda entrada x → q (q en **otro** paso de literal) sobre un camino del nuevo estado.

Es tu frase para un solo requisito: antes de fijar, la entrada estaba en un camino; puede que ese camino no
pase por r. Hay que ver que, si el review deja viva la entrada, hay otro camino que pasa por x, q **y** r.
Es la forma más pequeña a la que he llegado del núcleo: una fijación, un par de pasos, un estado que ya es
bueno.

---

## 5. Estado general de la demostración del veredicto

### Demostrado sin ninguna hipótesis

| resultado | módulo |
|---|---|
| **toda respuesta es correcta** (UNSAT sin modelo; SAT con certificado comprobado) | `Answer` |
| la máquina contiene todas las soluciones, completas y parciales | `ConservationImproves`, `ConservationPrefix` |
| no hay préstamo entre ramas en las uniones | `RunNoBorrow` |
| todo camino de un estado del lector es una solución real | `LiveSolution.path_is_solution` |
| cláusulas decididas, propagación unitaria, filas testigo | `LiveSolution` |
| **semilla, unión, UP y review conservan "hay caminos"** | `RunInhabited` |
| **un envío son sus pasos; fijar libera su propio paso** | `RunSteps` |
| **los requisitos débiles no cambian nada** | `WeakNoop` |

### La única dirección que falta

*Si la máquina termina con un estado válido, la fórmula es satisfacible.* Por la ruta de construcción:

```
veredicto  ⇐  FilterSoundAt (el envío conserva los caminos)
                 ├─ requisitos débiles                ✔ no cambian nada (WeakNoop)
                 └─ una fijación cada vez
                      ├─ entradas hacia el paso fijado  ✔ demostrado (pinStep_of_pairs)
                      └─ entradas hacia otros literales ✘ PinPairSoundAt — el núcleo
```

### Siguiente paso propuesto

Medir `PinPairSoundAt` en la sonda (debería pasar, ya que `PairPinExact`, que es más fuerte, pasó en 21.709
fijaciones) y atacarlo con lo ya demostrado: tras fijar, x y q poseen ambos a r (el review lo exige), y cada
par tiene su fila testigo (`entry_witness`); la pregunta es si el camino antiguo por x y q se puede
reencaminar por esas filas hasta r.
