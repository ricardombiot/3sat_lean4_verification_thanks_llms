# Plan: `lean/improves_bingo`, el espejo Lean de `julia/improves_bingo`

27-sept-2026. Rama `graph_owners`. Estado: **L0–L3, L5 (parcial) y L6 (núcleo) hechos**; L4 aplazado (modelo muy lento). L5: `Shrinks` y `AliveDocs` para todo el review; faltan los demás invariantes de forma y el orden dentro de una línea. L6: `Carried`, el review la conserva, `Rule`, y `readG_isSome_of_noZombie`; L6b hecho: `run_carries`, `machineVerdict_of_sat`, `readerVerdict_of_sat_noZombie`. **L7 hecho: `readerVerdict_iff_of_noZombie`** (el veredicto del lector es la satisfacibilidad si ningún estado visitado es un zombi), con una prueba propia (`Struct` + `sat_of_carried`) en lugar del puente; la solidez sin hipótesis queda como L7b opcional. Decisiones: (1) `require` de `improves_bin`, (2) aristas en una orientación con `Adj` simétrica por definición, (3) rama `graph_owners`.

## Objetivo

Un proyecto Lean 4 nuevo, `lean/improves_bingo`, que modele la máquina de `julia/improves_bingo`: los owners como
un **grafo por gpath** (vivos + aristas simétricas), sin tablas por nodo. No es una copia de `lean/improves_bin`:
es un modelo nuevo, pensado para que **cada regla del review sea un operador que solo borra** y para que añadir una
regla cueste un lema.

La meta de fondo es el veredicto del lector. En `lean/improves_bin`:
* `readerVerdictW_sound` está demostrado **sin hipótesis**: si el lector termina, la fórmula es satisfacible;
* lo abierto es la **completitud del lector**: que nunca llegue a un callejón sin salida (`NoDeadEnd`, y sus formas
  `KernelSplit`, `TriPin₁`, `CliqueTri`, `PieceLocal`, M1…).

Con el grafo, eso se enuncia de forma directa: **basta que todo punto fijo válido del review que el lector visita
contenga una solución compatible con sus pins** (§ «La meta», abajo). Las reglas nuevas sobre aristas (informe v199
§6) son el camino para llegar ahí, y este proyecto es el marco para escribirlas y demostrarlas.

## Principios de diseño

1. **Especificación, no implementación.** Como `GPathM`: listas planas, validez derivada, cada poda es un
   `filter`. El modelo no tiene que ser rápido; tiene que coincidir en lo observable con Julia (diferencial, L4)
   y ser fácil de demostrar. Si hace falta velocidad, versiones rápidas con `@[csimp]` (el patrón de
   `pairShares_eq_fast`).
2. **La simetría, por definición.** Sin Mathlib no hay `Sym2`. Propuesta: `edges : List (PathNodeId × PathNodeId)`
   y
   ```lean
   def adj (g : GPathB) (x w : PathNodeId) : Prop := x = w ∧ x ∈ g.alive ∨ (x, w) ∈ g.edges ∨ (w, x) ∈ g.edges
   theorem adj_symm : adj g x w ↔ adj g w x   -- por definición, sin orden entre ids
   ```
   Quitar una arista quita las dos orientaciones. No hace falta un orden total en `PathNodeId` (la clave ordenada
   de Julia es una optimización, no parte de la especificación).
3. **Los datos de las aristas se calculan, no se guardan.** Julia guardará contadores y testigos como caché; Lean los
   define como funciones del estado (`parSupport g x w := (parentsOf g x).countP (adj g · w)`). Así los lemas no
   tienen que mantener cachés, y el diferencial solo compara lo observable.
4. **La capa de base se reutiliza, no se copia.** `Cnf`, `Formula`, `CnfMapBin`, `CnfSelBin`, `Alias` vienen de
   `lean/improves_bin` como dependencia de Lake (decisión 1). Mismos tipos, así que el puente de la L8 es directo.
5. **`warningAsError = true` y 0 `sorry`** desde el primer commit, como en `improves_bin`.

## La meta: qué hay que demostrar para el veredicto

Con `Sol φ g` = «el conjunto de nodos que decodifica una solución de φ está vivo en g, con todas sus aristas y
enlaces» (una camarilla que toca cada paso):

* **Completitud de la máquina** (la parte fácil con el grafo): toda regla conserva `Sol` (`KeepsSol`), así que si φ
  es satisfacible, la línea final tiene un estado con `Sol`. Es el análogo de `completeness_pure`.
* **Solidez del lector**: si el lector termina (un nodo por paso), eso es una solución. En bin está demostrado
  (`readerVerdictW_sound`, vía `L7`); aquí se reutiliza por el puente estructural (L7, abajo).
* **Completitud del lector**, lo abierto. Con el grafo se enuncia así:
  ```lean
  def NoZombie (g : GPathB) : Prop := isValid g → ∃ S, Sol φ g S
  theorem readerVerdict_iff_of_noZombie :
      (∀ g ∈ estados que el lector visita, NoZombie g) → (readerVerdict φ ↔ Satisfiable φ)
  ```
  Si un estado válido contiene una solución, el pin del nodo de esa solución en el primer paso con elección deja el
  estado válido (por `KeepsSol`), así que el lector nunca se queda sin pin. **Cada regla nueva es un intento de
  hacer demostrable `NoZombie`**: cuanto más fuerte el review, más cerca un estado válido está de contener una
  solución.

## Fases

### L0 — esqueleto del proyecto

* `lean/improves_bingo/`: `lakefile.toml` (namespace `AbsSatBingo`, `warningAsError`), `lean-toolchain` igual al de
  `improves_bin` (`v4.33.1`), `require` de `improves_bin` por ruta (decisión 1), `README.md` con la tabla de
  procedencia de módulos (el formato del README de `improves_bin`), `scripts/gen_root.sh`.
* Criterio: `lake build` compila un módulo vacío que importa `AbsSatBin.GraphMap.CnfMapBin`.

### L1 — el modelo

`AbsSatBingo/Model/GPathB.lean`:
```lean
structure PNodeB where id : PathNodeId; title : String; parents sons : List PathNodeId
structure GPathB where
  nodes : List PNodeB
  alive : List PathNodeId                    -- Julia og.alive (antes gowners)
  edges : List (PathNodeId × PathNodeId)     -- Julia og.edges (una orientación basta)
  current_step : Int
  map_parent : Option NodeId
```
Vistas derivadas: `adj` (con `adj_symm`), `neighbors g x k`, `isValid` (cada paso con un vivo), `isValidNode`
(cada paso con un vecino vivo + padres/hijos, la de Julia), `measure` (vivos + aristas + enlaces).
Primitivas: `removeNode` (sale de `alive`, de `edges` y de los enlaces), `removeEdge`, `addEdge`.
Criterio: lemas básicos (`adj_symm`, `removeNode` solo quita, `measure` baja).

### L2 — las operaciones, espejo de `julia/improves_bingo`

| Julia (`improves_bingo`) | Lean |
|---|---|
| `add_row!` + `create_from_parents!` (vecinos de los padres, vivos, pasos anteriores) | `addNode … forb`, `up`, `upFiltering` (UP de `GPathM` con ventanas prohibidas) |
| `filter_require!` → `remove_node!` | `filterRequire`: quita de `alive` y de `edges`; el documento sigue hasta la purga |
| `clean_invalid_nodes!` (una fase, hasta el punto fijo) | `purgeFuel` (el de `CleanTwoPhase`, sin `cutAll`) |
| `pair_consistency_after_clean!` | `pairSweep` sobre aristas (todas contra el mismo estado) + purga, `pairFuel` |
| `prune_stale_links!` | `pruneLinks`: un enlace vive si `adj` |
| pasadas de padres / hijos (`cut_by_support!`) | `reviewParents` / `reviewSons` con `cutSupport` |
| `make_review_owners!` | `reviewPass`, `reviewFuel`, `review`; `filterAll` |
| `do_join!` (`PathOwnersGraph.union!`) | `join` / `doJoin` |
| máquina (`sat_machine.jl`) | `PureDriver`: `pureRun` |
| lector sin retroceso | `ReaderExec`: `readerVerdict` (el de `improves_bin`, sobre `GPathB`) |

Terminación por `measure`, como `Fuel.lean`. Criterio: todo compila y `lake exe bingo-check` da el mismo veredicto
que la fuerza bruta en `cnf/random_small` y `cnf/crafted`.

### L3 — ejecutables

* `bingo-dump`: vuelca el estado final **en el formato de `julia/improves_bingo/test_3sat/dump_final.jl`** (por
  gpath: nodos, global, tabla de cada nodo, padres, hijos), para reutilizar `compare_bingo.jl` tal cual.
* `bingo-check`: veredicto contra `bruteSat` y ningún nodo muerto (como `driverbin-check`).

### L4 — diferencial Lean ↔ Julia (bingo)

`scripts/diff_bingo.sh`: `dump_final.jl` en Julia y `bingo-dump` en Lean sobre el mismo corpus, y
`compare_bingo.jl` entre los dos. El modelo en listas es lento: corpus de instancias pequeñas (hasta `v5_c20`),
con límite de tiempo. Criterio: mismos veredictos y mismos estados finales en todo lo que termine; y una mutación
del modelo (por ejemplo, olvidar la simetría en `pairSweep`) tiene que detectarse.

### L5 — invariantes de forma

`WF g`: aristas entre vivos, ids sin repetir, enlaces ⊆ `adj` tras `pruneLinks`, vivos = ids de nodos tras la purga,
aristas solo entre pasos distintos. Se demuestra que todas las operaciones de L2 lo conservan. Aquí entra también el
**orden dentro de una línea no importa** en las pasadas (dos hermanos no son vecinos; Julia recorre en orden de hash):
un lema, no una suposición.

### L6 — el marco de reglas

```lean
structure Rule where
  apply    : GPathB → GPathB
  defl     : ∀ g, Sub (apply g) g            -- solo borra: vivos, aristas y enlaces
  keepsSol : ∀ φ g S, Sol φ g S → Sol φ (apply g) S
```
* `review` como punto fijo de una lista de reglas (purga, parejas, enlaces, pasadas) con combustible.
* Teoremas genéricos: el review es `defl`, conserva `Sol`, y **si las reglas son monótonas, el punto fijo no depende
  del orden** (el mayor estado estable por debajo de g). Esto sustituye, de una vez, a los resultados por modo de
  `improves_bin` (`CleanTwoPhase`, `pairSweep`, espejo).
* `completeness_bingo`: φ satisfacible ⇒ la máquina dice SAT (`Sol` a lo largo de `pureRun`; la idea de
  `PrefixCarry`).
* `readerVerdict_iff_of_noZombie` (§ «La meta»).

### L7 — puente estructural con `improves_bin`

`toM : GPathB → GPathM` (owners de x := vecinos vivos de x). Solo la parte **estructural**: nodos, ids, enlaces y
cadenas no dependen de las tablas, así que los lemas de decodificación (`PrefixDecode`, `L7.sat_of_inhabited`,
`CnfChain`) se transportan sin rehacerlos. Da la solidez del lector en bingo a partir de `readerVerdictW_sound`.

### L8 — puente completo (opcional)

`toM` conmuta con `filterAll`, `upFiltering` y `join` en los estados alcanzables (igualdad de puntos fijos, no de
estados intermedios: el desfase de ids muertos, el espejo y `cutAll` hacen distintos los pasos intermedios).
Permitiría transportar todo lo demostrado en `improves_bin` (`completeness_pure`, la ruta `PieceLocal`/M1, `KFix`…).
Es la fase más cara y la más arriesgada; la F4 de Julia (estados finales y vueltas idénticos en 81/81) dice que el
enunciado es plausible. Se decide después de L6: si el marco de reglas llega antes a la meta, no hace falta.

### L9 — la primera regla sobre aristas

La elegida del informe v199 §6 (propuesta: 6.1, apoyo contado), **a la vez** en Julia (`improves_bingo`, detrás de un
interruptor, medida con `REMOVED_BY`) y en Lean (una `Rule` con su `keepsSol`), y el diferencial de L4 sobre las dos.

### Sincronía Julia ↔ Lean (desde 28-sept-2026)

Todo lo que se enuncia en un lado tiene su espejo en el otro, con los mismos nombres:

| Lean (`lean/improves_bingo`) | Julia (`julia/improves_bingo`) | Estado |
|---|---|---|
| `SecClosed`/`SecClosedX`, `SecPair`/`SecPairX` (`Model/SecPair.lean`) | `sec_section`, `sec_fix!`, `sec_pair_bad(og; by = :map/:node)`, `sec_pair` (`src/graph_path/graph_path_secpair.jl`), test `test/graph_path/test_secpair.jl` | consulta, no regla |
| `choiceAt` (`Driver.lean`) | `choice_at` (`graph_path_secpair.jl`) | igual |
| `SecPairReader` (abierto) | `test_3sat/probe_tri_sec.jl` modos `sec`/`secx`: 0 cortes en 88 instancias | medido |
| `PinEqSec g b` = mitad fácil `sec_of_pinEdge` (demostrada bajo `PairClosed`) + mitad difícil `SecInPin` (abierta) | `test_3sat/probe_sec_vs_pin.jl`: 17 158 / 17 158 iguales (`sec_miss` = mitad fácil, `sec_bigger` = mitad difícil) | medido |
| `PairClosed` (`ReviewClean.lean`): `pairClosed_review'` demostrado sin hipótesis (`review_exits_clean`: el review que sale válido sale sin `dirty`, `measure + 1` vueltas bastan) | `pair_closed(gpath)` (`graph_path_filter_pair.jl`), test en `test_secpair.jl`; el `while` de Julia llega al punto fijo sin combustible | demostrado / por construcción |
| `noDeadEnd_of_secInPin`: `SecPair` + `SecInPin` ⇒ `NoDeadEndAt` | `dead_pins` = 0 | demostrado / medido |
| `SecStruct g V R` (`SecStruct.lean`): `secStruct_review`, `secStruct_filterAll` (el review y el pin la conservan), `secInPin_of_secStructAt` | `sec_struct_fails(gpath, adj)` (`graph_path_secpair.jl`), test en `test_secpair.jl` | demostrado |
| `secPair_visited`, `noDeadEnd_visited`, `secPair_filterAll` (`SecInduction.lean`) | — | demostrado |
| `SecMeet` (paso local de la inducción para `SecPair`) | `test_3sat/probe_secmeet.jl`: 21 044 casos que fallan | **FALSO** |
| `EdgeClique g` (`EdgeClique.lean`): toda pareja que se posee está en una camarilla llevada. Demostrado: `noDeadEnd_of_edgeClique`, `secPair_of_edgeClique`, `edgeClique_doJoin` | `edge_clique_miss(gpath)`, `edge_clique` (`graph_path_edgeclique.jl`), test en `test_secpair.jl`; `test_3sat/probe_edgeclique.jl`: 0 sin cubrir en F/A/U/L | join demostrado |
| `edgeClique_up` (`EdgeCliqueUp.lean`): el UP conserva `EdgeClique` (sin ventanas saltadas, documentos vivos y bajo la cima, estado sin `dirty`) | `probe_secpair_ops.jl` / `probe_edgeclique.jl`: 0 fallos tras `add_row!`, el review del UP no corre | demostrado |
| `ReviewExact` (abierto): tras seleccionar `b` y revisar, toda pareja está en una camarilla por `b` | `probe_edgeclique.jl` punto F: 0 sin cubrir en 17 139 | medido |
| `Kernel.lean`: núcleo (`pinEdge_iff_kernel`), confluencia (`pin_confluent`), `KernelExact`; la selección lo conserva (`kernelExact_filterAll`) y da `ReviewExact` (`reviewExact_of_kernelExact`), bajo `ClosedState` | `test_3sat/probe_pinexact.jl` (mapa bin): confluencia 30 309 / 0 fallos, `PinExact` 23 297 / 0 fallos | demostrado (bajo `ClosedState`) / medido |
| `Bookkeeping.lean`: `RevPrims`; `EdgesAlive`, `NodupIds` por review, filtro, fila y join | — | demostrado |
| `KernelUp.lean`: `kernelExact_addNode`, la fila nueva conserva `KernelExact` (sin ventana saltada; `LinksStep`, `Below`, `AliveDocs`, `EdgesAlive`) | `test_3sat/probe_kernelexact_up.jl` (mapa bin, antes del review del UP): 0 fallos | demostrado |
| `KernelJoin.lean`: `kernelExact_doJoin` bajo `KernelUnion`; `LinksStep`, `Below` | `test_3sat/probe_kernelunion.jl`: 0 diferencias | demostrado bajo `KernelUnion` |
| Comprobación final del review: Lean `finalPass` en `reviewFuel` (`Ops.lean`) ↔ Julia `FINAL_CHECK = :on`, `final_coherence_check!` | `test_3sat/probe_final_check.jl`: 0 cambios en 176 ejecuciones | **adoptado** (v201 §5) |
| `closedState_review` (`ClosedReview.lean`): el review deja el estado cerrado (antes la hipótesis `closed`) | — | demostrado |
| `KernelSkip.lean`: `kernelExact_addNode_gen`, el UP con o sin ventana saltada conserva `KernelExact` bajo `AvoidExact` (camarillas con cima de hijo permitido); sin salto, `AvoidExact` sale de `KernelExact` (`avoidExact_of_noSkip`); `TopNoSons` | `probe_kernelexact_up.jl` (indirecto) | demostrado bajo `AvoidExact` |
| **`ReaderFinal.lean`: `readerVerdict_iff_of_hyps`**, el veredicto del lector es la satisfacibilidad bajo `Hyps φ` = `union` (`KernelUnion` en los joins), `skip` (`AvoidExact` antes del UP con ventana saltada) | las dos medidas sin fallos | **demostrado bajo dos hipótesis, las dos de la forma «el núcleo de una unión es la unión de los núcleos»** |
| `UnionSplit.lean`: `kernelUnion_of_split`, `KernelUnion` ⇐ `SplitAt` + `SidePinned` en el paso de origen `c-2`; mitad estructural (`OffSide`) | `test_3sat/probe_union_parts.jl`: separación 0 fallos, `SharedAgree` **falso** (256503 parejas en 79 instancias), `PinnedSide` 0 fallos en 43866 | demostrado |
| `SideLinks.lean`: `LinksInv` (enlaces compatibles y completos; review, fila nueva, join); `kernelUnion_of_sideEdges`, `KernelUnion` ⇐ `SplitAt` + `SepAt` + `SideEdgesAt` (las parejas de la unión fijada en `b` son aristas del lado de `b`) | `test_3sat/probe_side_cut.jl`: las aristas de un solo lado caen por la regla de parejas o porque muere un extremo, nunca por padres/hijos | demostrado; `SideEdgesAt` abierta. `LinksInv` entra en `KInv`; **`readerVerdict_iff_of_parts`**: el veredicto bajo `HypsParts` (`split`, `sep`, `side`, `skip`). Sonda afinada: las cortadas por parejas fallan sobre todo en la cima, pero también solo en pasos inferiores (cascada) |
| `UnionEquiv.lean`: `kernelUnion_iff_split`, con los lados exactos y la separación `KernelUnion` ⇔ `SplitAt` ∧ `SidePinned` (monotonía: las estructuras cerradas de un lado lo son de la unión; fijada en un origen de un lado, el núcleo del otro está vacío) | `test_3sat/probe_side_cascade.jl`: quién vacía el paso sin entrada común de las aristas de un solo lado — cima: `clean` (mueren las cimas del otro lado); origen: `require` (el pin); pasos bajos: `clean` o `pair*` (el corte de otra arista de un solo lado); nunca padres/hijos ni un corte de parejas de una arista de los dos lados | demostrado |
| `SideDescent.lean`: `sideEdges_of_pinClean` (`SideEdges` ⇐ `PinClean`: el review de la unión fijada en `b` no deja aristas de un solo lado); `son_step`, el paso de hijos de la inducción descendente (con las parejas de arriba en `e`, una pareja de un solo lado (x,z) da un hijo `s` de `x` con x–s, s–z en `e`) | `PinClean`: `probe_side_cut.jl`, 0 de 513006. `test_3sat/probe_son_closed.jl`: la configuración x–s, s–z sin x–z está en el lado (42484 de 256503 parejas, en 72 de 88 instancias), así que el paso **no** cierra solo con los hijos | demostrado; el paso inductivo queda abierto |
| `SideCone.lean`: `sideEdges_of_cone`, la inducción descendente completa de `SideEdges` (base: origen y cima, con `OffSideUp`, que sale de `OffSide` en un estado cerrado; paso: el cono de testigos por la regla de parejas) bajo `ConeClosed` | `test_3sat/probe_cone_closed.jl`: **`ConeClosed` FALSA** (6 335 de 256 503 parejas, 64 instancias) | demostrado; el paso por conos no vale |
| `SideAbsorb.lean`, `ReaderAbsorb.lean`: **`sideEdges_of_absorb`**, `SideEdges` ⇐ `Absorb` (revisar la unión sin los nodos que solo tiene el otro lado devuelve las posesiones del lado; argumento global por monotonía: la estructura vive en el lado, matar los de fuera y revisar la conservan); `readerVerdict_iff_of_absorb` bajo `split`, `sep`, `absorb`, `skip` | `test_3sat/probe_absorb.jl`: **0 fallos en 14 622 lados**; antes del review hay 256 503 aristas de más, todas absorbidas, ninguna de las del lado perdida | demostrado |
| (sondas) `AncKernel`: el estado es el núcleo de la ascendencia pura sobre sus vivos; `GenAbsorb`: `Absorb` entre dos estados cualesquiera del mismo paso (nodos del mapa distintos) | `test_3sat/probe_anckernel.jl`: **FALSO** (las tablas llevan historia; p. ej. 65 de 72 uniones en `rand3sat_v4_c20`). `test_3sat/probe_genabsorb.jl`: **0 fallos en 10 500 pares**, 500 992 aristas de más absorbidas | medido |
| `SplitWitness.lean`: `secStruct_iUnion`, `WitSplit` ⇔ `KernelUnion` (lados exactos); `SingleAt`/`witAll_of_single` | `probe_splitat.jl`: `SplitAt` 0 fallos (23,4 M parejas); `probe_badwit.jl`, `probe_triangle.jl`, `probe_witall.jl`: `OwnSideGood`, `PairIn`, `TriIn` **falsos** (61 casos), `WitAll` **falso** fuera del origen | demostrado; las descomposiciones por testigos no avanzan |
| **`TopExact.lean`, `ReaderTop.lean`**: `TopExact` (exactitud solo para las cimas); el UP la conserva **sin hipótesis, con o sin ventana saltada** (`topExact_addNode`); la selección y el join bajo `TopUnion`; `noZombie_of_topExact`; **`readerVerdict_iff_of_topUnion`: el veredicto del lector es la satisfacibilidad bajo una sola hipótesis, `TopUnion`** (una cima del núcleo de la unión fijada está en el núcleo de algún lado; por nodo, no por pareja; `skip` desaparece) | implicada por `KernelUnion` (medida sin fallos) | **demostrado** |
| `TopExact.lean`, `TopNbr.lean`, `ReaderTop.lean`: `TopSplit`; `TopUnion` ⇐ `TopSplit` + `SidePinned`; **`topSplit_of_topStar`** (la estrella de la cima concuerda con su origen: sin Helly); invariantes `TopsApart`, `TopNbr` (review, UP, join, semilla); **`readerVerdict_iff_of_star`**: el veredicto bajo `TopStarK` + `SepAt` + `Absorb` | `test_3sat/probe_topsplit.jl`: `TopSplit`, `TopUnion` 0 fallos; `StarClosed` (la estrella ya cerrada) **falso** (~7 %). `test_3sat/probe_topstar.jl`: **`TopStar` 0 fallos** (el review de la estrella conserva la cima) | demostrado |
| `StarLocal.lean`: `LocalAbsorb`, `TopsSep`, `topUnion_of_local`, `readerVerdict_iff_of_local`; **`noBad_of_descent`** (descenso bien fundado), `StarOrder`, `starAbsorb_of_order`, `topUnion_of_order`; orden A (`keyA`), `StarKinds`, `starOrder_of_kinds` | `test_3sat/probe_star_cascade.jl` (`TopsSep` 0; absorción en la estrella 0; todas las aristas del otro lado las corta la regla de parejas), `probe_stargap.jl` (**`StarGap` 0 en 2,3 M**; `StarCone` falso 5 %), `probe_starorder.jl` (**orden A 0 fallos en 87 372**; huecos de cuatro tipos, sin otro caso; `StarGapLow` falso 8 %) | demostrado bajo `TopStarK` + `StarKinds` + `TopsSep` |
| `Lineage.lean`, `FamKernel.lean`, `LineStep.lean`, `DriverFam.lean`, `LineInduction.lean`: la inducción por linajes y por la línea; estructuras sobre familias (`FamStruct`, `Covers`), bajada por filas nuevas en familia, `ltuf_core`/`ltuf_stepC`/`topExact_next`, los hechos de `advance` (cobertura por llegadas, `LineUpC`, claves únicas), la contabilidad de las entradas, el caso base; **`readerVerdict_iff_of_pinFree`: el veredicto del lector es la satisfacibilidad bajo `HypsPin` (`PinFree` en cada línea) como única hipótesis** | `test_3sat/probe_pinfree.jl`: `PinFree` 0 fallos | **demostrado** |
| `StarCore.lean`: núcleo por parejas de la estrella de una cima (`StarCore`, testigo explícito); **`topStarF_of_starCore`** (`StarCoreH` ⇒ `TopStarF`) y `pinFreeF_of_topStarF` (con la contabilidad de la fila) | `src/graph_path/graph_path_star.jl` (`STAR_RULE`, :off; 0 cortes); `test_3sat/probe_starcore.jl`: `StarCoreH` 0 fallos | **demostrado** (bajo `StarCoreH`) |
| `RowAgree.lean`: la contabilidad de la fila (`RowAgree`: los vivos de una entrada cumplen `rq` de su clave; `reqOf_step_lt`, llegada, join, `advance_rowAgree`, `rowOwn_line`); **`readerVerdict_iff_of_starCore`: el veredicto del lector bajo `HypsStarCore` (`StarCoreH` en cada línea) como única hipótesis** | `test_3sat/probe_inv_ops.jl`: el invariante StarCore por operación (solo el pin sin review lo rompe; con review, UP y join, 0) | **demostrado** |
| `JoinStar.lean`: `TopStarR` (estructura de la estrella con la cima relacionada con todos sus nodos; monótona), `topStarR_of_topExact`, `topExact_arrival` (pin, fila nueva y review sin hipótesis); **`readerVerdict_iff_of_joinStarCore`: el veredicto bajo `JoinStarCore` (llegadas con `TopStarR` ⇒ `TopStarR` en la unión de la línea siguiente) como única hipótesis** | `test_3sat/probe_starcore.jl` (0 fallos en la unión de la línea) | **demostrado** |
| **Modo `FORBID` (desde 30-sept-2026):** Lean modela `:off` por defecto y `:on` con `Mode` (`ForbidOn.lean`: `runM .on`, `reviewOn`, `upOn`, `joinOn`, tríos en `GPathB.trios`). `spineVerdictOn_iff_of_liveExt` (`ForbidOnLine.lean`) | `FORBID=:on` (`graph_path_forbid.jl`, `up_forbid!`, `join_forbid`); diferencial `test_3sat/dump_forbid.jl` ↔ `lake exe bingo-dump SALIDA f.cnf on`; `probe_liveext.jl` `fin_*` mide la hipótesis | demostrado bajo `LiveExt` con los tríos reales; **toda medida anota su modo** |
| **Llegada fijada `:on`** (`ForbidOnPin.lean`, `ForbidOnArr.lean`): dirección 2 `liveChain_down` (+ `downInv_arrival`, `valid_down`), dirección 1 `ct_arrival_up`, `liveExt_arrivalOn`, **`good_arrivalOn` / `good_arrivalAt`** (`GoodOn`/`GoodAt` = `LiveExt` con `TF` tras un pin válido) | `test_3sat/probe_pinstable.jl` (`FORBID=:on`): `com_*` 0 diferencias, `com_deadA` 0 | **demostrado sin hipótesis** |
| **Join fijado `:on`** (`ForbidOnGood.lean`, `ForbidOnSide.lean`): `good_joinAt` bajo `PinSideAt A B R` (toda cadena viva de `pinOn (joinOn A B) R` es viva en `pinOn A R` o `pinOn B R`); el recíproco `liveChain_side_left/right` y `valid_joinOn_of_left/right` sin hipótesis (`downInv_side`); `pinSideAt_iff` | `test_3sat/probe_pinside.jl` (`FORBID=:on`; `PIN_MODE=random` todo pin, `PIN_MODE=real` los pins de `PinsFrom`): columna `none` = cadenas vivas de la unión fijada fuera de los dos lados; `dead`, `side_dead` de control | **`PinSideAt` abierta, medida 0 fallos**; el recíproco demostrado |
| **Veredicto `:on` bajo el join** (`ForbidOnDriver.lean`): `entry_shapeOn`, `LInvOn`, `PinsFrom` (requisitos de un camino del mapa desde el destino), **`spineVerdictOn_iff_of_joinOn`** bajo `HypsJoinOn` (`PinSideAt` en los joins de la máquina, solo para `PinsFrom`) | `probe_pinside.jl` con `PIN_MODE=real` es la medida de `HypsJoinOn` | **demostrado bajo una hipótesis** |
| **Veredicto `:on` bajo una hipótesis de nodos** (`ForbidOnTop.lean`): `TopAt` (toda cima viva del estado fijado está en una camarilla que esquiva sus tríos); `topAt_arrival` sin hipótesis; `topAt_join` bajo `TopSideAt` (una cima viva de la unión fijada está viva en un lado fijado); `hypsTopOn_of_joinOn` (`PinSideAt` ⇒ `TopSideAt`); **`spineVerdictOn_iff_of_topOn`** bajo `HypsTopOn` | `probe_pinside.jl` columnas `tops` / `top_none` (`CHAINS=0` para medir solo esto; `PIN_MODE=real` son los pins de `PinsFrom`) | **demostrado bajo `TopSideAt`; medida 0 fallos** |
| **`TopSideAt` en piezas** (`ForbidOnParts.lean`): `sideGraph` (la unión fijada además en el color del padre de la cima es, como grafo, parte del lado de la cima; demostrado con `tF_joinOn_of_cut`), `side_of_parts`, **`topSideAt_of_parts`** bajo `TopKeepAt` (fijar el color del padre de una cima viva de la unión no la mata) y `TriSideAt` (un triángulo de esa unión fijada prohibido en el lado está prohibido en ella); `TopsFrom`/`TopDocsId` por las llegadas `:on`; **`spineVerdictOn_iff_of_parts`** | `test_3sat/probe_topparts.jl` (`FORBID=:on`): `keep_fail`, `tri_fail`; `top_other`, `node_out`, `edge_out` (lo demostrado, de control) | **demostrado bajo las dos piezas; medidas 0 fallos** |
| (sonda) `TopFace`: en un lado, un triángulo prohibido no tiene una cima vecina de los tres con sus tres caras sin prohibir | `probe_topparts.jl` columnas `face_fail` / `face_low`: 300 de 2 775 (`clause_mix`), 1 688 de 13 671 (`clause_mix_sep`), 144 de 764 (`v5_c20_i2`) | **FALSO**: `TriSideAt` no se reduce a un hecho del lado solo |
| **«El primero que muere» en la estrella de la cima** (`ForbidOnKeep.lean`, `ForbidOnStar.lean`): `TrioGoodK`/`downInv_pinOnK` (el review conserva una estructura con tríos protegidos por hipótesis sobre el estado final); `AdjPar` (vecinos en pasos consecutivos son padre e hijo; fila, join, review); `star_alive`: la familia de la cima (vecinos, y parejas con el trío con la cima vivo) es una estructura del lado y sobrevive en el lado fijado; **`topSideAt_of_starTri`** y **`spineVerdictOn_iff_of_starTri`** bajo `StarTriAt` (un triángulo entre vecinos de la cima, vivo en la unión fijada y con sus tres caras con la cima vivas, no está en los tríos del lado fijado) | `test_3sat/probe_startri.jl` (`FORBID=:on`): `m3_dead` (la hipótesis), `m1_*` (la familia sobrevive: demostrado bajo la hipótesis), `consec_fail` (`AdjPar`, demostrado) | **demostrado bajo `StarTriAt`; medida 0 de 29 M (pins reales, 5 instancias)** |
| **Las dos mitades de `StarTriAt`** (`ForbidOnStar.lean`): `star_core` (la familia de la cima sobrevive si una base prohibida en el lado lo está en la unión fijada, y una base viva o no está en los tríos del lado fijado o tiene en cada paso un nodo que completa el tetraedro); `CrossCut S O` (una base prohibida en un lado bajo una cima suya con sus tres caras sin prohibir la corta también el otro lado) y `Star4At J R` (todo tetraedro vivo con cima de la unión fijada tiene en cada paso un nodo que lo completa); **`topSideAt_of_cross4`**, **`spineVerdictOn_iff_of_cross4`** | `test_3sat/probe_tetra.jl` (`FORBID=:on`): `x_tetra` / `x_open` (`CrossCut`), `q_cells` / `q_fail` (`Star4At`; `TRI_CAP=0` sin muestreo), `k_*` (qué mata en la unión los tetraedros de `TopFace`) | **demostrado bajo `CrossCut` + `Star4At`; medidas 0 fallos** |
| `SecStructAt g b` (abierto): toda sección de `b` se extiende a una `SecStruct` que concuerda con `b` | `test_3sat/probe_secinpin.jl`: `sec_struct_fails` = (0, 0, 0) en 17 158 secciones; padres/hijos cortan 0 en los pins | medido |
| `NoDeadEndAt`, `SecDeadEnd` (abierto) | `probe_tri_sec.jl`: `dead_pins`/`dead_ends` = 0 | medido |

## Decisiones antes de L0

1. **Dependencia de `improves_bin`.** (a) `require` por ruta: mismos tipos, puente directo, sin duplicar; pero
   depende de un proyecto que otra sesión modifica a diario (solo se compilan los módulos que se importan; la capa
   de base casi no cambia). (b) Copiar la capa de base (~1.100 líneas) con namespace propio: independiente, pero el
   puente de L7/L8 necesitaría convertir tipos gemelos. **Propuesta: (a).**
2. **Representación de las aristas**: pares en una orientación con `adj` simétrica por definición (propuesta), o
   pares normalizados por un orden total (más cerca de Julia, pero exige el orden y sus lemas).
3. **Rama**: seguir en `graph_owners` o abrir `lean_bingo`. Ojo: otra sesión está haciendo commits de Lean en
   `graph_owners` porque comparte la carpeta de trabajo.

## Riesgos

* **Lentitud del modelo.** El diferencial solo cubrirá instancias pequeñas; si hace falta más, versiones `@[csimp]`.
* **`NoZombie` puede ser falso** para el review actual (es otra forma de lo abierto en bin). El marco no lo hace
  cierto; hace que cada regla nueva cueste un lema y que su efecto sobre `NoZombie` se pueda medir y enunciar.
* **Deriva Julia ↔ Lean.** Cada regla entra a la vez en los dos lados (L9), con el diferencial de L4 en verde.

## Commits

Uno por fase, con `lake build` en verde y 0 `sorry`; L4 y L9 con la tabla del diferencial en el mensaje.
