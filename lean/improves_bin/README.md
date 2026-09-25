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

## Diferencial del mapa

```bash
./scripts/diff_map_bin.sh
```

Compara `CnfMapBin` con `GraphMapBin.load_import_bin!` (Julia) en el corpus de `compare_bin.jl`:
pasos, nodos, requires, sons y ventanas prohibidas. Estado: **74/74 iguales**, 1 saltada
(`simple_v3_c2.cnf`, 2-SAT, que el importador bin rechaza). Una mutación de `sonsOf` da 0/74, así que
el diferencial sí distingue.
