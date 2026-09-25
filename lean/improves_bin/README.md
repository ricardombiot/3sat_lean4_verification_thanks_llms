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
| `Utils/Alias` | `6b6359f` | copia | |
| `Cnf/Formula` | `6b6359f` | revisado | `Lit.step` pasa a `2v+1`/`2v+2` (fusión raíz en el paso 0); añade `Bounded` |
| `Cnf/Dimacs` | `6b6359f` | copia | |
| `GraphMap/CnfMapBin` | — | reescrito | mapa bin como aritmética: `reqOf`, `mapNodes`, `sonsOf`, `isProhibited` |
| `GraphMap/MapBinDump` | — | nuevo | volcado canónico para el diferencial |
| `GraphPath/Model/GPathM` | `6b6359f` | copia | el UP clásico (`addNode`) se queda; el bin va aparte |
| `GraphPath/Model/UpBin` | — | reescrito | `addNodeW`/`upW`: la fila sin las ventanas prohibidas; revisión solo si se saltó una. `addNodeW_none`: sin ventanas es `addNode` |
| `GraphPath/Model/DriverBin` | — | reescrito | `PureDriver` sin pruebas: `reqOf`, `sonsOf`, `upFilteringW … (isProhibited φ)`; tests de índices y de los errores 3 y 4 |

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
