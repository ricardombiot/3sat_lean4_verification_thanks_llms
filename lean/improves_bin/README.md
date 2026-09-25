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
| `Utils/Alias` | `53e2be6` | copia | |
| `Cnf/Formula` | `53e2be6` | revisado | `Lit.step` pasa a `2v+1`/`2v+2` (fusión raíz en el paso 0); añade `Bounded` |
| `Cnf/Dimacs` | `53e2be6` | copia | |
| `GraphMap/CnfMapBin` | — | reescrito | mapa bin como aritmética: `reqOf`, `mapNodes`, `sonsOf`, `isProhibited` |
| `GraphMap/MapBinDump` | — | nuevo | volcado canónico para el diferencial |
| `GraphPath/Model/GPathM` | `53e2be6` | reescrito (UP) | `addNode`/`up`/`upFiltering` reciben `forb`; `shiftRowIds` = candidatos, `newRowIds` = sin prohibidos; revisión solo si se saltó una ventana |
| `GraphPath/Model/DriverBin` | — | reescrito | `PureDriver` sin pruebas: `reqOf`, `sonsOf`, `upFiltering … (isProhibited φ)`; tests de índices y de los errores 3 y 4 |
| `GraphPath/Model/Pruned`, `Denot`, `Fuel`, `Filter`, `Join`, `Review`, `CleanInvalid`, `Coherence`, `Certificate`, `Verdict`, `Extendable` | `53e2be6` | copia | |
| `GraphPath/Model/Reachable` | `53e2be6` | reescrito | parámetro `forb` en el constructor `up` |
| `GraphPath/Model/OwnersInvariants` | `53e2be6` | revisado | L1 sin `sorry`; el caso con revisión va por `review_OwnersSubset` |
| `GraphPath/Model/L6`, `L6Search` | `53e2be6` | revisado | `simp` de `initSeed`; mapas sintéticos con `noForb` |
| `GraphPath/Model/Up` | `53e2be6` | revisado | **`rowParents_of_not_mem` cambia de hipótesis**: `p ∉ shiftRowIds` (un id prohibido no está en la fila pero sí tiene padres); `denot_upFiltering` pide `NodupIds` del `addNode` para el caso con revisión |
| `GraphPath/Model/L6Up` | `53e2be6` | revisado | un alargamiento de cadena exige `forb (extendPid …) = false`; `SupportedG_upFiltering`: `sorry` en el caso con ventana saltada (la revisión debe podar el padre sin hijo) |
| `GraphPath/Model/AddNode` | `53e2be6` | revisado | `ChainSound_upFiltering` pide que el alargamiento no esté prohibido; el caso con revisión por `ChainSound_review`, sin `sorry` |

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

`warningAsError = false` mientras dure la migración con `sorry`. `Lit.step` se renombró a
`Lit.binStep` para que ningún uso heredado compile.
