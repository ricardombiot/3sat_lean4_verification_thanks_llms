# lean/improves_bingo — el espejo Lean de `julia/improves_bingo`

Modelo Lean de la máquina con **grafo de owners** (plan: `docs/plans/lean_bingo.md`; Julia:
`julia/improves_bingo`, plan `docs/plans/graph_owners.md`; informe v199). Namespace `AbsSatBingo`.

Los owners no son una tabla por nodo sino un grafo por gpath: `alive` (nodos vivos) y `edges` (compatibilidades
entre nodos distintos, en una orientación cualquiera). La posesión `Adj` es reflexiva en los vivos y **simétrica
por definición** (`adj_symm`). Cada regla del review es un operador que solo borra (`Sub`).

## Dependencia

La capa de base viene de `lean/improves_bin` por `require` de Lake (mismos tipos, sin copiar): `Utils/Alias`,
`GraphPath/Model/GPathM` (solo utilidades: `intRange`, …) y, desde L2, `Cnf`, `CnfMapBin`, `CnfSelBin`. Solo se
compilan los módulos que se importan.

## Módulos

| módulo | fase | qué |
|---|---|---|
| `Model/Ops` | L2 | espejo de las operaciones de `julia/improves_bingo`: `filterRequire`, `clean` (purga), `pairSweep`/`cleanPair`, `pruneLinks`, `cutSupport` y las pasadas, `reviewPass`/`review` (con `dirty` = Julia `review_owners`), `filterAll`, `addNode`/`up`/`upFiltering`/`initSeed`, `join`/`doJoin` |
| `Model/Driver` | L2 | la máquina (`run`, sobre `CnfMapBin`), el lector sin retroceso (`readerVerdict`), `bruteSat`, `noDeadNodes` |
| `Exe/Dump` | L3 | volcado en el formato de `dump_final.jl` |
| `Model/GPathB` | L1 | `PNodeB`, `GPathB`; `Adj`/`adj_symm`, `neighborsAt`, `ownersOk`, `isValid`, `isValidNode`, `measure`; primitivas `removeEdge`, `addEdge`, `killVertex`, `removeNode`; `Sub` (refl, trans, y para cada primitiva); lo que se va (`not_adj_removeEdge`, `not_adj_killVertex`); la medida baja (`measure_removeEdge_lt`, `measure_removeNode_lt`) |

## Ejecutables

* `lake exe bingo-check f.cnf …` — máquina y lector contra fuerza bruta, y nodos muertos. `cnf/crafted` de
  `improves_bin`: 8/8 OK (máquina y lector = fuerza bruta, sin nodos muertos). **Muy lento**: el modelo en listas
  recorre todas las aristas en cada consulta de posesión (0,7 s con 3 variables; 6 min con `clause_mix_sep`,
  9 variables). Versiones rápidas `@[csimp]` pendientes antes del diferencial (L4).
* `lake exe bingo-dump SALIDA f.cnf` — volcado para `compare_bingo.jl`.

## Construcción

```bash
lake build            # warningAsError = true; 0 sorry
./scripts/gen_root.sh # regenera AbsSatBingo.lean
```
