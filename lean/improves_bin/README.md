# lean/improves_bin — proyecto Lean del mapa bin

Espejo en Lean de `julia/improves_bin` (plan: `docs/plans/bin-map.md`). Proyecto independiente de
`lean_project/`: namespace `AbsSatBin`, sin dependencias. Los módulos se traen **poco a poco**,
solo cuando la migración los necesita.

Cada módulo que entra se registra aquí con su procedencia:

- **copia** — idéntico al original salvo el namespace; debe compilar sin cambios de prueba.
- **reescrito** — depende del mapa o del UP; escrito de nuevo para el mapa bin.
- **revisado** — copiado y re-demostrado sobre los módulos reescritos.

| módulo | origen (`lean_project@sha`) | tipo | notas |
|---|---|---|---|
| `Utils/Alias`, `Cnf/Dimacs` | `53e2be6` | copia | |
| `Cnf/Formula` | `53e2be6` | revisado | `Lit.step` → `Lit.binStep` (`2v+1`/`2v+2`); añade `Bounded` |
| `GraphMap/CnfMapBin` | — | reescrito | el mapa bin como aritmética: `reqOf`, `mapNodes`, `sonsOfMap`, `isProhibited`, `clauseWindow` |
| `GraphMap/CnfSelBin` | — | reescrito | la selección de una asignación está en el mapa **sin** `Sat`; `Sat` entra solo en `pidOfAssign_not_prohibited` |
| `GraphMap/MapBinDump` | — | nuevo | volcado canónico para el diferencial con Julia |
| `GraphPath/Model/GPathM` | `53e2be6` | reescrito (UP) | `addNode`/`up`/`upFiltering` con `forb`; `shiftRowIds` = candidatos, `newRowIds` = sin prohibidos; revisión solo si se saltó una ventana |
| `Pruned`, `Denot`, `Fuel`, `Filter`, `Join`, `Review`, `CleanInvalid`, `Coherence`, `Certificate`, `Verdict`, `Extendable`, `JoinSound`, `PickInduction`, `ArcConsistency`, `Candidates`, `PathExists`, `Ownership`, `MapChain`, `Bridge`, `Pinned`, `NodeIds`, `Survive` | `53e2be6` | copia (+`forb` mecánico) | |
| `Reachable` | `53e2be6` | reescrito | parámetro `forb` en `up` |
| `OwnersInvariants`, `L6`, `L6Search`, `GownersNodes`, `Parents`, `Sons`, `SelfOwn`, `ParentId`, `Threaded`, `Reader` | `53e2be6` | revisado | ramas con revisión tras ventana saltada por `X_review`/`X_of_pruned`; `NodupIds_review` nuevo |
| `Up` | `53e2be6` | revisado | **`rowParents_of_not_mem` cambia de hipótesis** (`p ∉ shiftRowIds`) |
| `L6Up` | `53e2be6` | revisado | un alargamiento de cadena exige que no esté prohibido; `SupportedG_upFiltering` para el UP sin ventana saltada (el otro caso es `SkipExact`) |
| `AddNode` | `53e2be6` | revisado | `ChainSound_upFiltering` pide alargamiento no prohibido; revisión por `ChainSound_review` |
| `Certifies` | `53e2be6` | revisado | `ReqChain`/`FilteredChain`/`ArcImpliesChainOn`/`ValidHasChainW` piden alargamiento no prohibido |
| `MapReachable` | `53e2be6` | reescrito | `Reachable (reqOf φ) (isProhibited φ)`; invariante nuevo **`NoForb`** |
| `CnfChain` | `53e2be6` | reescrito | decodificación: la elección en `L3` es `clauseWindow j b₀ b₁ b₂` y `NoForb` la excluye |
| `L7`, `Conservation` | `53e2be6` | reescrito | `extendPid_eq_pidOfAssign`; conservación sin `sorry` |
| `PureDriver` | `53e2be6` | revisado | `sonsOfMap`, `reqOf`, `isProhibited`; `pureRun_ne_nil` sin `sorry` |
| `DriverBin` | — | nuevo | tests de índices y errores 3/4 de Julia; `noDeadNodes`, `bruteSat` |
| `NodeInvariant` | `53e2be6` | revisado | pasos difíciles = los `3m` pasos `L`; obligación nueva **`SkipExact`** (revisión tras ventana saltada) |
| `SkipReview` | — | nuevo | `SkipExact` ⇐ `SkipChain` (solo los nodos viejos supervivientes) ⇐ `SkipChainBin` (esos supervivientes están sobre una cadena sólida que elige `L1 = 1`) |
| `Decision`, `SatMachine/PureSatMachine`, `SatMachine/PureProofs` | `53e2be6` | revisado | `WF` → `Bounded` |
| `AggressiveReview`, `ReaderAgg` | `53e2be6` | copia (+`forb`) | revisión agresiva y relación de lectura; `upFilteringR` recibe `forb` |
| `CleanTwoPhase` | `53e2be6` | copia | limpieza en dos fases: `Stable`, `nodupIds_cleanInvalid₂` |
| `PairInactive` | `53e2be6` | extracto | de `SegReview`, `SymInvariant`, `PinDoomed`, `PairHelly`: `aggInactive_of_revOk`; nuevo `reviewAgg_eq_review`/`filterAllAgg_eq_filterAll` bajo `RevOk` |
| `SymMachine` | — | nuevo | `CutClosed` (punto fijo del review, `addNode`, `join`); `sym_join`; `symInv_reachable`: todo estado válido de la máquina es simétrico; a lo largo del lector `filterAllAgg = filterAll` (`start_agg_eq`, `pin_agg_eq`) |
| `ReaderExec` | `53e2be6` | revisado | el lector sin retroceso sobre `pureRun` (bin, sin débiles), **con el review normal** (`filterAll`, como Julia desde `4c644ac`); `readerVerdictW_sound` vía `L7` |
| `ReaderPrefix` | — | nuevo | el lector lee un prefijo (`ReadFirst`, `PrefixUpTo`, `firstChoice_pin_gt`); `readerVerdictW_iff_of_pinChain` con una sola hipótesis abierta, `PinChain` |
| `PinChainBin` | — | nuevo | dos bits por paso (`entry_bit`, `entry_flip`); el bit de la cadena es gratis; `PinChain` ⇐ `OtherBit` (y `chainG_through_pin`: es también necesario); `readerVerdictW_iff_of_otherBit` |
| `OtherBitSem` | — | nuevo | `OtherBit` sobre la fórmula: los pins son una asignación parcial; la línea final lleva todas las soluciones (`carried_unique`); `readerVerdictW_iff_of_otherBitSem` con esa única hipótesis |
| `NoDeadEnd` | — | nuevo | decodificación exacta (`selOfAssign_decode`), pins fijados (`PinNodes`), descenso; `OtherBitSem ⇐ NoDeadEnd`, `soundness_of_noDeadEnd` (con `RootValid`, sin `ClauseStepExact`/`SkipExact`), `readerVerdictW_iff_of_noDeadEnd` |
| `Kernel` | — | nuevo | `Kernel` (propiedades estáticas de un punto fijo válido del review) y `Below`; `below_review`: el review nunca baja de un kernel; `isValid_filterAll_of_kernel`: un pin sobrevive si un kernel válido por debajo concuerda con él |
| `KernelReader` | — | nuevo | `OwnAbove` (entradas en pasos ≥ 0) en toda la máquina; `kernel_of_review`: un review válido es un kernel; `kernel_readPins`: todo estado válido del lector es un kernel; `NoDeadEnd ⇐ KernelSplit`, `readerVerdictW_iff_of_kernelSplit` |
| `KernelSplit` | — | nuevo | subkernel de un pin (`restrictPin`); `TriPin` (regla de parejas con el pin como tercer miembro fijo); `restrict_kernel`, `pin_survives_of_triPin`; `KernelSplit ⇐ TriPin` en la primera elección; `readerVerdictW_iff_of_triPin` |
| `KernelIff` | — | nuevo | el review nunca añade hijos (`sonsSub_review`); `below_filterAll_self`; `kernelSplit_iff_noDeadEnd` |
| `TriPinCore` | — | nuevo | un miembro exclusivo del pin cierra el trío (`tri_of_exclusive`); `TriPin ⇐ AmbTri` (solo parejas ambiguas) |
| `AmbTriCore` | — | nuevo | bajo la elección el camino está fijado (`gowner_eq`); la ventana hace exclusivos los nodos de `k…k+2` (`excl_near`); `AmbTri ⇐ AmbFar` (parejas ambiguas fuera de la ventana, pasos `l > k`) |
| `AmbHighCore` | — | nuevo | un nodo bajo la elección está en todas las tablas y posee a todos (`forced_owns_all`); `AmbFar ⇐ AmbHigh` (ambos miembros en pasos `≥ k+3`) |
| `TriPinCut` | — | nuevo | `TriPin₁`: regla de parejas tras una ronda de cortes de enlaces incompatibles con el pin (`Cx`); `TriPin ⇒ TriPin₁`; subkernel cortado `restrictPin₁` (`restrict₁_kernel`); `KernelSplit ⇐ TriPin₁` |
| `TriPinAll` | — | nuevo | invariante `AllTriPin₁` (`TriPin₁` para todo nodo vivo) ⇒ todo pin en la primera elección sobrevive (`allPinsAlive_reader`) y el lector decide (`readerVerdictW_iff_of_allTriPin₁`) |
| `CliqueTri` | — | nuevo | `TriP g P` (regla de parejas relativa a una clique `P`), `CliqueTri` (para toda clique) ⇒ `AllTriPin₁`; **el pin es el subkernel cortado** (`pin_eq_cut`); **el pin conserva `CliqueTri`** (`cliqueTri_pin`); el lector decide si `CliqueTri` vale en los estados de partida (`readerVerdictW_iff_of_cliqueTri`) |
| `CertFix` | — | nuevo | caracterización del punto fijo por certificados (`ChainSound`): `CertLink` (todo enlace compatible relativo a una clique está, con ella, en un certificado); `cxP_of_cert` (converso, siempre); `cutTable_iff_cert`; `CertLink ⇒ CliqueTri`; `readerVerdictW_iff_of_certLink` |
| `CertDescent` | — | nuevo | `CliqueTri ⇒ CertLink` haciendo crecer una clique con testigos hasta un certificado (`grow`, `cover`, `chain_of_cover`); `certLink_iff_cliqueTri` |
| `CertInvariant` | — | nuevo | `CertClique` (toda clique con testigos está en un certificado) ⇔ `CertLink`; **el review lo conserva** (`certClique_filterAll_nil`); basta en la salida cruda de la máquina (`readerVerdictW_iff_of_certClique`) |
| `PrefixTri` | — | nuevo | el lector solo necesita cliques **prefijo** (un nodo por paso `0…k`): `PrefixTri` ⇐ `CliqueTri`; da `TriPin₁` en la primera elección; el pin lo conserva (`prefixTri_pin`); basta en los estados de partida (`readerVerdictW_iff_of_prefixTri`) |
| `OneShot` | — | nuevo | **`TriPin₁` ⇔ el review tras el pin es de una sola ronda** (`triPin₁_iff_oneShot`: el estado pinchado contiene el subkernel cortado, sin cascada); en un nodo con un único padre el corte no toca ese enlace (`cx_unique_parent`, `cx_unique_son`): los cortes solo actúan en las fusiones; `cx_to_unique_parent` (la compatibilidad sube a un padre único), `tri_below`/`tri_above` y **`fail_is_merge_separated`**: un fallo de `TriPin₁` está separado por fusiones de ambos extremos |
| `BranchFull` | — | nuevo | ramas llenas: `FullBranch`/`CommonBranch` ⇐ `TriPin₁` (necesarias); `FullBranch` ⇐ `PairExact` (todo enlace en un certificado); **`PairExact` se conserva por el review, `join` y `addNode` sin ventana saltada, fusiones incluidas** (`pairExact_filterAll_nil`, `pairExact_join`, `pairExact_addNode`) |
| `SymReview`, `Fabric` | — | **no portados** | fuera del cierre de constantes de `completeness_pure`/`soundness_pure` |

## Estado de los teoremas finales

- `completeness_pure` (satisfacible ⇒ la máquina dice SAT): **demostrado**, `[propext, Quot.sound]`,
  solo con `Bounded`.
- `soundness_pure` / `run_pure_decides`: demostrados **bajo `ClauseStepExact`**, que en el mapa bin
  agrupa dos obligaciones abiertas: el filtro en los pasos `L` (`HardStepExact`) y la revisión tras
  una ventana saltada (`SkipExact`). `SkipExact` está reducido (demostrado) a `SkipChainBin`: los
  nodos viejos que sobreviven a la revisión están sobre una cadena sólida que elige `L1 = 1`. Es un
  filtro de un solo valor dos pasos por debajo de la cima: la misma forma que los filtros de
  `HardStepExact` en los pasos `L`.
- Ruta alternativa (v194): `soundness_of_noDeadEnd` da la solidez **sin `ClauseStepExact`** con
  `NoDeadEnd` + `RootValid`; y `NoDeadEnd ⇔ KernelSplit ⇐ TriPin ⇐ AmbTri ⇐ AmbFar ⇐ AmbHigh` (parejas
  ambiguas con ambos miembros en pasos `≥ k+3`, pasos por encima de la elección), la única pieza abierta del lector.
  `TriPin` se midió falso en un pin que sobrevive (`ambhigh-dump`); rama más débil: `KernelSplit ⇐ TriPin₁`
  (`TriPinCut`), una ronda de cortes de enlaces incompatibles con el pin. Invariante candidato:
  `AllTriPin₁` (`TriPinAll`); su forma cerrada `CliqueTri` se conserva con cada pin del lector
  (`CliqueTri`), así que basta en los estados de partida: **abierto** que la máquina lo construya. Forma
  equivalente por certificados: `CertLink ⇔ CliqueTri` (`CertFix`, `CertDescent`).
- `sorry` restantes: 0. `warningAsError = true`.

## Diferencial del mapa

```bash
./scripts/diff_map_bin.sh
```

Compara `CnfMapBin` con `GraphMapBin.load_import_bin!` (Julia) en el corpus de `compare_bin.jl`:
pasos, nodos, requires, sons y ventanas prohibidas. Estado: **74/74 iguales**, 1 saltada
(`simple_v3_c2.cnf`, 2-SAT, que el importador bin rechaza). Una mutación de `sonsOf` da 0/74, así que
el diferencial sí distingue.

## Máquina bin contra fuerza bruta

```bash
lake build driverbin-check
./scripts/driverbin_corpus.sh LISTA_DE_CNF [segundos] [paralelo]
```

Veredicto de `DriverBin.pureRun` contra `bruteSat`, y ningún nodo muerto en el estado final (lo que
Julia reporta como `GRAVE ERROR READER`). El modelo en listas es lento: las fórmulas de 3 variables
tardan milisegundos, las de `v4_c20` o `v8_c10` pasan de 20 s.

## Herramientas de la migración

- `scripts/migrate.sh RUTA` — copia un módulo de `lean_project` cambiando el namespace.
- `scripts/gen_root.sh` — regenera `AbsSatBin.lean` con todos los módulos.
- `scripts/index_lint.py` — nombres del mapa clásico y aritmética de pasos sin `-- idx:` (fuentes de
  aritmética: `CnfMapBin` y `Formula`). Debe dar 0.
- `scripts/sorry_ledger.py` — `sorry` pendientes por módulo (deuda de demostraciones).
- `scripts/thread_forb.py` — hila `forb` por la API del UP (aridad fija, binder explícito junto a
  `title`, nunca en comentarios) y cierra la rama con revisión con `X_review`/`X_of_pruned`.
- `scripts/fix_forb.py` — inserta `forb` solo donde el compilador dice exactamente que falta.
- `scripts/port.sh` — `migrate` + `thread_forb` + `fix_forb` + lint, módulo a módulo.

`warningAsError = true` (reactivado al llegar a 0 `sorry`). `Lit.step` se renombró a
`Lit.binStep` para que ningún uso heredado compile.
