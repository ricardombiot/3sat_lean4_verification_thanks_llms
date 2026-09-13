# Niveles de abstracción de la máquina SAT

Este documento delimita los niveles **tal como están en el código** de la máquina pura ejecutable
(`lean_project/AbsSat`). Cada nivel es un tipo de Lean con sus propias operaciones; lo que sube de un
nivel al siguiente es una construcción concreta, no una idea.

```
Nivel 0  Fórmula          Cnf
   │     CnfMap: pasos, nodos del mapa y requisitos
Nivel 1  Mapa             NodeId, mapNodes, mapSons, reqOfCnf           (estático)
   │     estados que recorren el mapa
Nivel 2  Estado           GPathM: nodos con owners, gowners             (up, filterAll, review, join)
   │     una línea con un estado por clave
Nivel 3  Conductor        PureLine = List (NodeId × GPathM)             (sendTo, pureAdvance, pureRun)
   │     la secuencia de líneas
Nivel 4  Máquina          SatMachinePure: timeline, is_satisfiable

         Lectura semántica de un estado del nivel 2: IsChain, ChainSound, denot, SupportedS, Inhabited
```

---

## Nivel 0 — Fórmula

**Fichero:** `AbsSat/Cnf/Formula.lean`

| Objeto | Definición |
|---|---|
| literal | `Lit { v : Nat, pos : Bool }`, con `Lit.step = 2v + (pos ? 0 : 1)` |
| cláusula | `Clause { l1 l2 l3 : Lit }` |
| fórmula | `Cnf { nVars : Nat, clauses : List Clause }` |
| asignación | `Assign := Nat → Bool` |
| semántica | `Sat a φ` (toda cláusula satisfecha), `Satisfiable φ := ∃ a, Sat a φ` |
| buena forma | `WF φ`: cada literal usa una variable `< nVars` y los tres literales de una cláusula ocupan pasos distintos |

**No hay operaciones de la máquina aquí.** Es el objeto del que se pregunta: *¿es satisfacible?*

---

## Nivel 1 — Mapa

**Ficheros:** `AbsSat/GraphMap/CnfMap.lean`, `AbsSat/GraphMap/CnfSel.lean`

El mapa es **estático**: no tiene estado, owners ni caminos. Es el grafo por el que los estados avanzan.

| Pasos | Nodos (`NodeId { step, index }`) | Requisitos (`reqOfCnf`) |
|---|---|---|
| `2v` (`varStep v`) | `(2v, 0)` y `(2v, 1)`: el valor de `x_v` | ninguno |
| `2v+1` (`negStep v`) | `(2v+1, i)`: `¬x_v = i` | `(2v, 1−i)` |
| `2n` (`litBlock`) | fusión, índice 0 | ninguno |
| `2n+1+j` (`clauseStep j`) | filas `1..7` de la cláusula `j` | `(l1.step, b1 r)`, `(l2.step, b2 r)`, `(l3.step, b3 r)` |
| `2n+1+m` (`fusionTop`) | fusión final, índice 0 | ninguno |

- Una fila `r` de cláusula codifica qué literales son verdaderos con sus bits
  `b1 = r/4 % 2`, `b2 = r/2 % 2`, `b3 = r % 2`; el índice 1 de un nodo de literal (`litReq l 1`) es «el
  literal es verdadero».
- `mapSons φ k i` son las aristas: desde un paso de variable, al nodo de negación `(2v+1, 1−i)`; desde los
  demás, a todos los nodos del paso siguiente.
- `stepCount φ = 2n + m + 2`.

**Demostrado en este nivel:**

| Teorema | Qué dice |
|---|---|
| `bits_not_all_zero` | toda fila `1..7` nombra algún literal como verdadero: las 7 filas son las que satisfacen la cláusula |
| `reqOfCnf_backward` | los requisitos de un nodo están siempre en pasos anteriores (con `WF`) |
| `reqOfCnf_clause`, `reqOfCnf_neg`, `mapNodes_var`, `mapNodes_clause` | la forma exacta de requisitos y nodos en cada tipo de paso |

---

## Nivel 2 — Estado

**Fichero principal:** `AbsSat/GraphPath/Model/GPathM.lean`

Un estado es un conjunto de caminos por el mapa **fusionados en un solo grafo**, con una tabla de
compatibilidades.

```lean
structure PathNodeId where id : NodeId; parent_id : Option NodeId
structure PNodeM    where id : PathNodeId; title : String;
                          parents sons owners : List PathNodeId
structure GPathM    where nodes : List PNodeM; gowners : List PathNodeId;
                          current_step : Int; map_parent : Option NodeId
```

- Un **nodo del estado** es un nodo del mapa *junto con el nodo del mapa del que viene* (`parent_id`):
  el mismo valor puede aparecer varias veces con padres distintos.
- **`owners`** de un nodo: con qué nodos del estado es compatible, paso a paso.
- **`gowners`**: los owners globales del estado.
- **`isValid g`**: hay algún owner global en cada paso `0 … current_step − 1`.
- **`isValidNode g n`**: `n` tiene owner en cada paso por debajo del actual, padres si no es raíz e hijos si
  no es el último.

**Operaciones:**

| Operación | Qué hace |
|---|---|
| `addNode g d` | añade el nodo `(d, map_parent)` con padres en la línea anterior y `owners = gowners`; **todo nodo recibe al nuevo como owner**; `current_step + 1` |
| `up g d` | `addNode` si `g` es válido; si no, deja `g` |
| `filterRequire g req` | **pin**: solo toca `gowners`, quitando en el paso de `req` todo id distinto de `req` |
| `review g` | hasta el punto fijo: `cleanInvalid` (owners ∩ owners globales, quitar nodos inválidos), `reviewParents` (owners ∩ owners de los padres), `reviewSons` (owners ∩ owners de los hijos) |
| `filterAll g reqs` | `review (reqs.foldl filterRequire g)`: **los pins y el review son una sola operación** |
| `upFiltering g reqs d` | `up (filterAll g reqs) d`: primero se fija y se limpia, después se añade |
| `join g₁ g₂` | une nodos con el mismo `PathNodeId` y los owners globales (`doJoin` exige mismo paso, mismo padre de mapa y ambos válidos) |

**Alcanzabilidad:** `Reachable reqOf` (semilla, `up`, `join`) en `Reachable.lean`, y `MapReachable φ`,
que además exige que cada nodo añadido sea del mapa (`MapReachable.lean`).

**Demostrado en este nivel** (todo sin axiomas de proyecto):

| Teorema | Módulo | Qué dice |
|---|---|---|
| `L1` | `OwnersInvariants` | los owners de un nodo en los pasos de sus requisitos son exactamente sus requisitos |
| `OOS_reachable` | `SelfOwn` | en su propio paso, un nodo solo se posee a sí mismo |
| `GN_reachable` | `GownersNodes` | todo owner global es un nodo del estado |
| `pruned_filterAll` | `Pruned` | el filtro solo encoge |
| `review_node_valid`, `review_owners_within_gowners` | `Fuel` | en un punto fijo válido, todo nodo es válido y sus owners son owners globales |
| `ChainSound_filterAll`, `SupportedS_review` | `AddNode`, `Coherence` | el filtro conserva las cadenas que respetan los requisitos; el review conserva el soporte |
| `SupportedS_filterAll_easy` | `NodeInvariant` | en pasos sin requisitos o con uno inmediato, el filtro conserva el soporte |
| `owns_required` | `NodeInvariant` | un nodo que sobrevive posee, **uno a uno**, un nodo con cada id requerido |
| `OwnedCompatible_reachable` | `UnitPropagation` | ningún nodo posee a otro cuyo requisito en su paso sea distinto de él (dual de `L1`) |
| `invalid_filterAll_of_UPConflict` | `UnitPropagation` | si la propagación unitaria desde los pins llega a conflicto, el filtro invalida el estado |
| `pinned_support`, `removed_unless_supported` | `PinSupport` | un valor sobrevive al filtro solo si convivía, en cada paso fijado, con el valor fijado |

**Medido, no demostrado:** la tabla de owners no es exacta por pares (v69, v93: pares co-poseídos sin
solución común).

---

## Nivel 3 — Conductor

**Fichero:** `AbsSat/GraphPath/Model/PureDriver.lean`

```lean
abbrev PureLine := List (NodeId × GPathM)     -- un estado por clave: el nodo del mapa recién alcanzado
```

| Operación | Qué hace |
|---|---|
| `pureInit φ` | una semilla por nodo del paso 0 |
| `sendTo φ g next d` | calcula `upFiltering g (reqOfCnf φ d) d`; **solo si es válido** lo inserta en la clave `d` |
| `insertPure` | si la clave ya existe, **fusiona** con `doJoin`; si no, añade |
| `sendAll φ kv next` | `sendTo` a todos los hijos en el mapa de la clave |
| `pureAdvance φ line` | `sendAll` de todos los estados de la línea |
| `pureRun φ` | `stepCount − 1` avances desde `pureInit` |

Aquí ocurren las dos cosas que el nivel 2 no hace por sí solo: **ramificar** (un estado por clave) y
**fusionar** ramas que llegan a la misma clave.

**Demostrado en este nivel:**

| Teorema | Módulo | Qué dice |
|---|---|---|
| `LineOk_pureAdvance` | `PureDriver` | cada estado de una línea es alcanzable en el mapa, está en su paso y es válido |
| `pureRun_carries`, `pureRun_full_state`, `pureRun_ne_nil` | `PureDriver` | **completitud**: toda asignación que satisface la fórmula deja su rama en la última línea |
| `sendTo_of_refuted`, `pureAdvance_origin` | `DriverPropagation` | una rama que la propagación unitaria refuta nunca entra en la línea siguiente |
| `pureAdvance_keyPure`, `pureAdvance_drops_key_conflict` | `KeyBranching` | cada estado lleva fijados los literales de su fila clave; una fila que la contradice no se extiende |
| `decides_of_ClauseStepExact` | `Decision` | con `ClauseStepExact`, «última línea con un estado válido» ⇔ satisfacible |

**Medido:** medir sobre estados fusionados mezcla ramas; lo que parecía deducción del review eran ramas
que el conductor ya había descartado (v95).

---

## Nivel 4 — Máquina ejecutable

**Fichero:** `AbsSat/SatMachine/PureSatMachine.lean` (entrada/salida en `PureSatMachineIO.lean`)

```lean
structure SatMachinePure where cnf : Cnf; timeline : List PureLine; current_step : Nat
```

- `init_pure`: `timeline = [pureInit cnf]`.
- `step_pure`: añade `pureAdvance` de la línea actual hasta el último paso.
- `run_pure`: ejecución completa con combustible.
- `is_satisfiable`: la última línea no está vacía.

**Demostrado** (`AbsSat/SatMachine/PureProofs.lean`):

| Teorema | Qué dice |
|---|---|
| `run_pure_eq_driver` | la última línea del timeline es exactamente `pureRun`: **el nivel 4 es el nivel 3** |
| `is_satisfiable_run_pure_iff` | la máquina dice SAT ⇔ `pureRun` no está vacía |
| `completeness_pure` | satisfacible ⇒ la máquina dice SAT (con `WF`) |
| `soundness_pure`, `run_pure_decides` | la máquina dice SAT ⇒ satisfacible, **bajo `ClauseStepExact`** |

Fuera de estos niveles quedan la máquina imperativa antigua (`SatMachine.lean`, `MSat`) y el grafo con
`IO.Ref` del ejecutable original: las pruebas hablan del modelo puro, no de esa implementación.

---

## Lectura semántica de un estado

No es un nivel de ejecución: es cómo se pregunta **qué significa** un estado del nivel 2.

| Concepto | Módulo | Definición |
|---|---|---|
| `IsChain g sel` | `Denot` | un nodo del estado por paso, cada uno padre del siguiente |
| `PairwiseOwned g sel` | `Denot` | todos los nodos de la cadena se poseen dos a dos |
| `denot g p` | `Denot` | `p` es el camino de una cadena con owners mutuos: lo que el estado *representa* |
| `ChainSound g sel` | `Review` | `ChainG` (cadena, owners dos a dos y todos sus nodos son owners globales) más autoposesión, enlace a hijos y raíz solo en el paso 0 |
| `SupportedS g` | `Coherence` | **todo nodo del estado está en alguna cadena sonora** |
| `Inhabited g` | `L6` | el estado representa algún camino |

El puente con el nivel 0 está demostrado: una cadena sonora de longitud completa se lee como una
asignación que satisface la fórmula (`L7.satisfiable_of_inhabited`, vía `Certifies.Inhabited_of_ChainSound`).

---

## Dónde vive el problema abierto

**`ClauseStepExact φ`** (`NodeInvariant.lean`) es una afirmación **del nivel 2 medida con la lectura
semántica**:

> Si `g` es alcanzable, válido y `SupportedS`, y `d` es una fila de cláusula del paso actual, entonces,
> cuando `filterAll g (reqOfCnf φ d)` es válido, sigue siendo `SupportedS`.

- **Por qué no sale sola:** `owns_required` da un owner para **cada** requisito por separado; `SupportedS`
  pide que un nodo esté en **una** cadena con los tres a la vez. Es un salto de tipo Helly.
- **Reducido a una pieza:** `ClauseStepExact_of_FlipCore` (`ClauseFilter.lean`) lo deja en el caso de
  cambiar un literal y seguir teniendo cadena (`FlipCore`).
- **Todo lo de arriba ya está conectado:** `decides_of_ClauseStepExact` (nivel 3) y `run_pure_decides`
  (nivel 4) convierten `ClauseStepExact` en «la máquina decide 3SAT».
- **Para toda fórmula equivale a P = NP**, porque la máquina es polinómica (v70, v76); el objetivo
  realista es demostrarlo para una clase.

---

## Qué pregunta pertenece a qué nivel

| Pregunta | Nivel |
|---|---|
| ¿Es satisfacible la fórmula? | 0 |
| ¿Qué exige una fila de cláusula? ¿Quién es hijo de quién? | 1 |
| ¿Qué quita un filtro? ¿Qué garantiza el review? | 2 |
| ¿Qué ramas avanzan? ¿Qué se fusiona y dónde? | 3 |
| ¿Qué responde la máquina? | 4 |
| ¿Qué caminos representa un estado? ¿Está todo nodo en una solución? | lectura semántica del nivel 2 |

## Resumen

| Nivel | Objeto | Operaciones | Ya demostrado | Abierto |
|---|---|---|---|---|
| 0 Fórmula | `Cnf` | — | — | ¿satisfacible? |
| 1 Mapa | `NodeId`, `reqOfCnf` | estático | forma del mapa, requisitos hacia atrás | — |
| 2 Estado | `GPathM` | `up`, `filterAll` (pins + review), `join` | `L1`, dual de `L1`, propagación unitaria, soporte de pins | **`ClauseStepExact`** (con la lectura semántica) |
| 3 Conductor | `PureLine` | `sendTo`, `pureAdvance`, `pureRun` | completitud, ramas por clave, descarte de ramas refutadas | — (reducido al nivel 2) |
| 4 Máquina | `SatMachinePure` | `step_pure`, `run_pure` | ≡ nivel 3, completitud, corrección condicionada | — (reducido al nivel 2) |
