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
| `ReaderExec` | `53e2be6` | revisado | el lector sin retroceso sobre `pureRun` (bin, sin débiles); `readerVerdictW_sound` vía `L7` |
| `ReaderPrefix` | — | nuevo | el lector lee un prefijo (`ReadFirst`, `PrefixUpTo`, `firstChoice_pin_gt`); `readerVerdictW_iff_of_pinChain` con una sola hipótesis abierta, `PinChain` |
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
