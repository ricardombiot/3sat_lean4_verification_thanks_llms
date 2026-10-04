# Verificación para el Autor v148: la máquina no pierde soluciones parciales ni mezcla ramas — y el estado global del veredicto

Ricardo, soy Claude (Opus 5). Este informe recoge lo hecho desde v147 y, a petición tuya, hace
**balance global**: qué está demostrado del veredicto de tu máquina, por qué caminos se llega a él y qué
falta en cada uno.

Rama `spaik`, build de `AbsSat` (217 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Commits
`fb776de`, `1d68088`, `c32ad6c`, `aaca265`, `9fff7a1`, `6717c34`.

---

## Parte I — Lo nuevo desde v147

### 1. Qué hay debajo de `RunPaths` (`UnionPaths.lean`)

v147 dejó el veredicto por la construcción bajo `RunPaths`: *en cada unión revisada, toda entrada está
en un camino de una de las dos ramas*. Se parte en dos:

```
RunPaths  ⇐  la unión revisada es exacta  ∧  NoBorrow
│
├─ la unión revisada es exacta
│    ⇐ la unión de dos ramas exactas es exacta          ← demostrado (tablesSound_join)
│    ∧ fijar y revisar conserva la exactitud             ← el núcleo (§ Parte II)
│
└─ NoBorrow: un camino de la unión es camino de una sola rama  ← DEMOSTRADO (§ 4)
```

`path_top_side` (sin hipótesis): todos los nodos de un camino de la unión están en la rama de su nodo de
arriba, porque los nodos de arriba de las dos ramas son distintos (mismo mapa, padre distinto).

### 2. `NoBorrow` no depende del review (medido y demostrado)

La sonda `noborrow` mostró que **ni siquiera la unión sin revisar** mezcla ramas, y que tiene exactamente
los mismos caminos que la unión revisada:

| familia | caminos de la unión simple | de la unión revisada | mezclados |
|---|---|---|---|
| K4 | 224 | 224 | 0 |
| paridad | 2.994 | 2.994 | 0 |
| prisma | 1.904 | 1.904 | 0 |

`noBorrow_of_plain` (sin hipótesis): un camino de la unión revisada es un camino de la unión simple. Así
que `NoBorrow` es una propiedad de la **estructura** de tus uniones.

### 3. La máquina no pierde ninguna solución parcial (`ConservationPrefix.lean`)

La completitud estaba demostrada para asignaciones que satisfacen **toda** la fórmula
(`pureRunW_carries`). Mirando dónde entraba esa hipótesis, solo aparecía en tres sitios —que el nodo
elegido esté en el mapa, que el siguiente sea su hijo, y que los requisitos débiles se cumplan— y en los
tres **solo se miran las cláusulas cuyo paso ya se ha alcanzado**. Con eso:

* **`SatBelow φ a K`**: la asignación satisface las cláusulas por debajo del paso `K`.
* **`pureStepsW_chain_below`** (sin hipótesis): *para toda asignación que satisface las cláusulas por debajo
  de `K`, la línea `K − 1` de la ejecución tiene, en el nodo de la asignación, un estado que contiene la
  rama parcial de la asignación como camino.* Es tu "en cada UP el estado es viable", para prefijos: la
  máquina **no pierde ninguna solución parcial**.
* **`ids_of_reqSat`** (sin hipótesis): *un camino sobre el mapa que cumple sus requisitos es la rama de la
  asignación que deletrea*, nodo a nodo: variables, negaciones, cláusulas (sus tres bits fijan la fila) y
  fusiones.

### 4. `NoBorrow` demostrado en las uniones de tu máquina (`RunNoBorrow.lean`)

> **`noBorrow_at_insert`** (sin hipótesis): cuando el driver inserta un envío en una clave que ya tiene un
> estado, todo camino de la unión de los dos estados **fijados** (con cualquier fijación, en particular la
> del siguiente destino, que es donde tu máquina revisa la unión) es un camino de uno de los dos.

La prueba es tu lectura del oráculo comprimido, en seis piezas:

1. **Un camino queda determinado por sus mapas** (`along_parents`, `chainSound_congr`).
2. **Un camino de la unión es genuino** (`genuine_of_chain`): cumple los requisitos, así que es la rama
   parcial de una asignación que satisface las cláusulas vistas.
3. **Cada estado de una línea contiene todos los caminos genuinos de su clave** (`line_complete`).
4. **Cada envío contiene los caminos genuinos que pasan por su origen** (`send_complete`).
5. **La contabilidad** (`SendsOk`, `acc_sendToW`): cada estado del pliegue que construye una línea conoce
   sus orígenes —sus nodos de arriba son `(d, p)` con `p` en su lista, y contiene los caminos genuinos que
   vienen de esos `p`—. Un envío tiene la lista `[p]`; una unión junta las dos listas.
6. **La unión** (`noBorrow_union`): el nodo de arriba del camino está en una rama e identifica su origen,
   que está en la lista de esa rama; luego el camino es de esa rama, y lo sigue siendo tras fijar porque
   sus nodos cumplen las fijaciones.

### 5. El nivel de pares, como validez (`PairPins.lean`)

* **`realizes_of_entryPins`**: una entrada `(x, q)` de un estado del lector está en un camino si fijar los
  mapas de `x`, `q` y sus padres deja el estado válido (**`EntryPin`**), completando después de abajo
  arriba con `LivePinUp`. El estado final tiene un solo nodo por paso, y en los pasos de `x` y `q` ese
  nodo **es** `x` o `q`.
* **Medido** (`entrypin`): 5.331 entradas en K4 y paridad, **0 fallos**.

---

## Parte II — Estado global de la demostración del veredicto

### 6. Lo demostrado sin ninguna hipótesis

| resultado | módulo |
|---|---|
| **toda respuesta es correcta**: UNSAT solo si no hay modelo; SAT solo con un certificado comprobado | `Answer` |
| a una fórmula satisfacible nunca le responde UNSAT | `Answer` |
| la máquina contiene todas las soluciones (completitud) | `CertificateSet`, `ConservationImproves` |
| **la máquina no pierde ninguna solución parcial** | `ConservationPrefix` |
| un camino que cumple los requisitos es la rama de su asignación | `ConservationPrefix` |
| **no hay préstamo entre ramas en las uniones de la máquina** | `RunNoBorrow` |
| un estado válido con un mapa por paso es un camino | `PinExtends.chain_of_ids` |
| fijar un paso sin elección mantiene la validez | `PinSplit` |
| lo decidido abajo decide negación, fusión y cláusula | `PinUp.decided_off_var` |
| fijar a la vez = fijar en secuencia; un envío = sus pasos | `SeqPin`, `WeakPairs` |
| revisar tras cada unión no cambia nada | `WeakPairs.full_seq` |
| "estar en un camino de una rama" es un soporte; la partición de la unión sale de los caminos | `PartSplitReal` |

Lo que **no** está demostrado es la otra dirección de la completitud del veredicto: *si la máquina
termina con un estado válido, la fórmula es satisfacible* (equivalentemente, que nunca responda "no sé").

### 7. Los caminos hacia el veredicto

Cuatro rutas formalizadas, cada una con lo que le falta:

| ruta | teorema final | lo que falta |
|---|---|---|
| **A. Lectura** (tu lector, de abajo arriba) | `verdict_iff_up`, `answer_unsat_up`, `answer_ne_unknown_up` | **`LivePinUp`**: con el prefijo decidido, fijar cualquier valor vivo de la siguiente variable mantiene la validez |
| **B. Exactitud** (rebanadas) | `sat_of_slices`, `answer_ne_unknown_of_slices` | **`FilterSlices`** ⇐ `PairPinExact` (+ `WeakPairExact`, o probar que los débiles no cambian nada) |
| **C. Construcción** (uniones) | `sat_of_paths` | `RunPaths` ⇐ unión revisada exacta (= B en el estado unido) ∧ `NoBorrow` (**demostrado**); falta además restringir `SupportSplit` a las uniones de la ejecución (mecánico) |
| **D. Pares como validez** | `tablesSound_of_entryPins` | `LivePinUp` ∧ `EntryPin` |

```
             veredicto (valid ⇒ satisfacible) / nunca "no sé"
               ▲                ▲                     ▲
          A: LivePinUp     B: FilterSlices       C: RunPaths
               │                │                  ├─ NoBorrow ✔ (demostrado)
               │                ├─ PairPinExact ◄──┤  unión revisada exacta
               │                └─ WeakPairExact   │  (= B en la unión)
               │                     (o débiles = no-op, medido)
               └──────── D: PairPinExact ⇐ LivePinUp ∧ EntryPin
```

**Todas las rutas desembocan en lo mismo**: *fijar y revisar conserva lo que hay* —en forma de validez
(`LivePinUp`, `EntryPin`) o de exactitud (`PairPinExact`)—. Es el núcleo.

### 8. Lo medido del núcleo (sin un solo fallo)

| hipótesis | sonda | casos |
|---|---|---|
| `LivePinUp` (de abajo arriba, todo candidato vivo) | `pinup` | 5 familias Tseitin/paridad + **240 fórmulas aleatorias**, 0 fallos |
| `PinExtends` (orden aleatorio) | `pinext` | 27.505 comprobaciones de paso, 0 fallos |
| `PairPinExact` / exactitud tras fijar | `pinexact`, `splice` | 21.709 fijaciones; 10,9 M entradas, 0 falsas |
| `EntryPin` | `entrypin` | 5.331 entradas, 0 fallos |
| los débiles no cambian las tablas | `weakcmp` | 530 envíos y 517 estados, idénticos |
| `SideCover` | `sidecls` | 33,2 M entradas, 0 fallos |
| `RunPaths` | `surv` | 615.911 entradas, 0 fallos |

### 9. Lo que se ha descartado (por medición)

Reglas **locales** que no sirven para demostrar el núcleo: el empalme de dos caminos en el nodo del medio,
la construcción voraz sin review, la regla de ternas a través del valor vivo, Helly-3 en estados exactos,
la versión fuerte de `SideCover` y exigir que cada rama explique todas sus entradas. La lección: el núcleo
no sale de una regla sobre pocos nodos; hay que razonar sobre caminos completos o sobre la historia de la
ejecución.

### 10. Los caminos que faltan, en orden de coste

1. **`SupportSplit` restringido a la ejecución** (mecánico). Enunciar la partición solo para las uniones que
   hace el driver, para poder usar `NoBorrow` (demostrado) en la ruta C.
2. **Los débiles no cambian nada** (medio, mecánico). La mitad está demostrada
   (`idContradicts_of_weak_removed`); la otra exige extender tres invariantes (`OwnedCompatible`,
   `ParentInv`, `LitInv`) a la máquina Improves. Quita `WeakPairExact` de la ruta B.
3. **El núcleo: `LivePinUp`** (abierto, el importante). Con el prefijo decidido y el estado válido, todo
   valor vivo de la siguiente variable se puede fijar. La vía nueva y prometedora es la **misma técnica que
   acaba de funcionar para `NoBorrow`**: razonar con la historia de la ejecución (qué caminos genuinos
   contiene cada estado) en lugar de con el estado final aislado. Un valor vivo tras el prefijo pertenece a
   algún camino de la unión revisada; si ese camino es genuino, `line_complete` y `send_complete` lo
   colocan en una rama concreta, y fijarlo conserva esa rama.

## 11. Artefactos

* Lean: `UnionPaths.lean`, `PairPins.lean`, `ConservationPrefix.lean`, `RunNoBorrow.lean`.
* Sondas (`Probes/Helly.lean`): `noborrow` (con la unión simple), `entrypin`.
* Nota de proceso: un commit (`aaca265`) entró con el build roto porque la tubería ocultó el fallo; se
  corrigió en `9fff7a1` y desde entonces el build completo se comprueba antes de cada commit.
