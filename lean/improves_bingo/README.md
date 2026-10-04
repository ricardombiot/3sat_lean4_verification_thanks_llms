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
| `Model/Shrink` | L5 | `Shrinks` (solo borra + la medida no sube) para cada operación del review y para `filterAll` |
| `Model/Carried` | L6 | `Carried g S`: la selección `S` (un nodo por paso) viva, poseída dos a dos y enlazada; `isValid_of_carried`, `isValidNode_of_carried`; qué primitivas la conservan |
| `Model/Keeps` | L6 | **el review conserva toda camarilla llevada** (`carried_review`), y el filtro por requisitos que concuerdan (`carried_filterAll`), regla a regla |
| `Model/Reader` | L6 | `AliveDocs` (lo conserva el filtro); un pin en un paso con elección baja la medida; **`readG_isSome_of_noZombie`**: si ningún estado que el lector visita es un zombi, el lector termina |
| `Model/Rule` | L6 | el marco: `Rule` = `apply` + `shrinks` + `keeps` + `docs`; `comp`, `fuel`; las reglas de hoy como instancias (`purge`, `pairs`, `links`, `parents`, `sons`, `pass`, `review`) |
| `Model/Grow` | L6b | el join conserva la camarilla por cualquiera de los dos lados (`carried_join_left/right`); **el UP la alarga** (`carried_addNode`, `carried_up`) |
| `Model/Machine` | L6b | inducción sobre las líneas (`LineOk`, `Has`, `StateOk`); **`run_carries`**: la línea final lleva la camarilla de toda solución; `machineVerdict_of_sat`; **`readerVerdict_of_sat_noZombie`** |
| `Model/Struct` | L7 | invariantes estructurales (`PMP`, `GPMP`, `NoForb`, `OnMap` y **`ReqEdges`: los requisitos como invariante de aristas**); los conserva todo lo que solo borra, el UP y el join; `struct_run`, `struct_visited` |
| `Model/Decode` | L7 | **`sat_of_carried`**: una camarilla llevada en el último paso es una solución; **`readerVerdict_iff_of_noZombie`** |
| `Exe/Dump` | L3 | volcado en el formato de `dump_final.jl` |
| `Model/GPathB` | L1 | `PNodeB`, `GPathB`; `Adj`/`adj_symm`, `neighborsAt`, `ownersOk`, `isValid`, `isValidNode`, `measure`; primitivas `removeEdge`, `addEdge`, `killVertex`, `removeNode`; `Sub` (refl, trans, y para cada primitiva); lo que se va (`not_adj_removeEdge`, `not_adj_killVertex`); la medida baja (`measure_removeEdge_lt`, `measure_removeNode_lt`) |

## Ejecutables

* `lake exe bingo-check f.cnf …` — máquina y lector contra fuerza bruta, y nodos muertos. `cnf/crafted` de
  `improves_bin`: 8/8 OK (máquina y lector = fuerza bruta, sin nodos muertos). **Muy lento**: el modelo en listas
  recorre todas las aristas en cada consulta de posesión (0,7 s con 3 variables; 6 min con `clause_mix_sep`,
  9 variables). Versiones rápidas `@[csimp]` pendientes antes del diferencial (L4).
* `lake exe bingo-dump SALIDA f.cnf` — volcado para `compare_bingo.jl`.

## Estado de los teoremas

* **`readG_isSome_of_noZombie`** (`Model/Reader`): el lector termina sobre un estado si el estado revisado es válido,
  todo vivo tiene documento y **todo estado que visita cumple `NoZombie`** (válido ⇒ lleva una camarilla). Es la
  completitud del lector con una sola hipótesis, sobre los estados.
* **`carried_review`, `carried_filterAll`** (`Model/Keeps`): ninguna regla del review pierde una camarilla llevada.
* **`run_carries`** (`Model/Machine`): si `a` satisface `φ`, el estado de la línea final en la clave de `a` lleva
  la camarilla de `a` (`pidOfAssign φ a`). **`machineVerdict_of_sat`**: la máquina dice SAT en toda fórmula
  satisfacible (solo con `Bounded`).
* **`readerVerdict_of_sat_noZombie`**: si `φ` es satisfacible y ningún estado que el lector visita desde la línea
  final es un zombi, el lector dice SAT. **La única hipótesis abierta del lector es `NoZombie`.**
* **`sat_of_carried`** (`Model/Decode`): una camarilla llevada por un estado de la máquina o del lector, en el último
  paso, se decodifica en una asignación que satisface `φ` (el argumento de `CnfChain`, con `ReqEdges` en lugar de
  las tablas). Axiomas: `propext`, `Quot.sound`.
* **`readerVerdict_iff_of_noZombie`**: si ningún estado que el lector visita desde la línea final es un zombi,
  **`readerVerdict φ = true ↔ Satisfiable φ`**. Es la meta del plan: la única hipótesis abierta es `NoZombie`.
* Pendiente (L7b, opcional): la solidez sin hipótesis (como `readerVerdictW_sound` de `improves_bin`), que exige
  demostrar que el review termina en un estado limpio (combustible suficiente).
* 0 `sorry`. Axiomas: `propext`, `Classical.choice`, `Quot.sound` (el `Classical.choice` viene de tácticas; se puede
  limpiar).

## Construcción

```bash
lake build            # warningAsError = true; 0 sorry
./scripts/gen_root.sh # regenera AbsSatBingo.lean
```
