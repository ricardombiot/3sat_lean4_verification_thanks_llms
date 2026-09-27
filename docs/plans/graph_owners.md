# Plan: grafo de owners (rama `graph_owners`, `julia/improves_bingo`)

27-sept-2026. Estado: **F0 hecho** (commit 1c93bd8). F1 en adelante, pendiente del ok.

## Objetivo

Sustituir las tablas de owners por nodo (`PathDocNode.owners :: PathDocOwners`) por un grafo de
owners por gpath (`PathOwnersGraph.OwnersGraph`): cada compatibilidad es una arista `Edge` guardada una
vez, simétrica por construcción, con la incidencia por nodo y paso para buscar por id.

Qué se busca:

1. **Tiempo**: desaparecen los `deepcopy` + `union!` de tablas del review (pasadas de padres e hijos),
   los de `create_node_from_parents!`, la fase 2 de `clean` y el espejo.
2. **Reglas sobre aristas**: un sitio donde colgar datos por arista (contadores, marcas) y reglas
   nuevas (p. ej. la del segmento), con `removed_by` midiendo cuánto corta cada regla.
3. **Formalización**: la simetría pasa a ser del tipo, no un invariante que se demuestra.

Qué no se espera: menos memoria. La incidencia guarda los dos sentidos como hoy y `edges` se suma
encima; la copia del gpath en cada UP (`sat_machine.jl:110`) se queda. Se mide en F5.

`improves_bin` no se toca: es la referencia del diferencial.

## Traducción de la máquina

| Hoy (`improves_bin`) | En `improves_bingo` |
|---|---|
| `GPath.owners` (global) | `og.alive` |
| `PathDocNode.owners` | `og.inc[x]` (el campo desaparece del nodo) |
| `PathDocumentNode.new` → `add_owner!(id)` | `register!` (reflexiva implícita) |
| `add_son!` / `add_parent!` → `add_owner!` | `add_edge!` (el enlace implica arista) |
| `create_node_from_parents!` + `its_owners_are_owned_by_me!` | `create_from_parents!` |
| `filter_require!` / `remove_node_owner!` | `remove_node!(og, x; rule = :require / :clean …)` |
| `check_if_graph_valid!` | `og.valid` (paso sin vivos) |
| `clean` fase 1: `is_valid_intersect` | `is_valid_owners` |
| `clean` fase 2 (corte con la global) | desaparece: `remove_node!` ya borra las aristas |
| pasadas padres/hijos: `deepcopy` + `union!` + `cut_owners!` | `cut_by_support!(og, x, x.parents / x.sons; rule)` |
| `mirror_remove!`, `SYM_MODE` | desaparecen (siempre simétrico) |
| `CLEAN_MODE = :sequential` | desaparece (solo dos fases) |
| `prune_stale_links!` | enlace vive si `has_edge(og, p, s)` |
| `pair_consistency_after_clean!` + `shares_every_step` | igual, sobre `inc[x]` e `inc[w]` |
| `do_join!` | `PathCollectionLines.union!` (sin owners) + `PathOwnersGraph.union!` |
| `deepcopy(gpath)` en el UP | igual (copia también el grafo) |

## Fases

### F0 — copia y borrador (hecho)

`julia/improves_bingo` = `improves_bin` en 0e2af47; `src/db/path/docs/path_owners_graph.jl` sin incluir.

### F1 — el módulo solo, con tests

- Incluir `PathOwnersGraph` en `DBDocuments`.
- `test/db/path/docs/test_owners_graph.jl`:
  - simetría: tras cualquier secuencia de `add_edge!`/`remove_edge!`/`remove_node!`,
    `w ∈ inc[x] ⇔ x ∈ inc[w] ⇔ haskey(edges, key)`; una función `check_invariants(og)` reutilizable;
  - `remove_node!` deja sin rastro al nodo y marca `valid = false` si vacía su paso;
  - `is_valid_owners` con paso vacío y con paso sin línea;
  - `cut_by_support!` en un caso de padres a mano; `union!` de dos grafos con aristas comunes.

### F2 — GPath sobre el grafo

- `GPath`: `owners :: PathDocOwners` → `og :: OwnersGraph`. `PathDocNode` pierde `owners`;
  `link!` llama a `add_edge!` desde `GraphPath` (el nodo no conoce el grafo).
- Reescribir `graph_path_constructor.jl`, `graph_path_up.jl`, `graph_path_filter.jl`,
  `graph_path_filter_pair.jl`, `graph_path_join.jl` según la tabla.
- `PathDocumentOwners` se queda solo si algo lo sigue usando (ver decisión 2); si no, se borra.
- Asserts temporales (quitables con un flag): `check_invariants(og)` al final de cada review.

**Punto delicado — el desfase de ids muertos.** Hoy, dentro de una pasada, un nodo eliminado sigue
en las tablas de los demás hasta la fase 2 del siguiente `clean`, y `is_valid_node` mira la tabla
sin cortar con la global: un id muerto puede sostener un paso un rato más. En el grafo, el id muerto
desaparece al instante. Por tanto:

- **se espera** el mismo estado final (el review es borrar hasta un punto fijo);
- **no se espera** la misma traza vuelta a vuelta: `REVIEW_ROUNDS` y los contadores pueden bajar.

Si F4 muestra estados finales distintos, se añade un modo `LAG_MODE` que replique el desfase
(el vértice muere en `alive` pero sus aristas se borran en el `clean` siguiente) para localizar la
diferencia.

**Punto a comprobar — pasos sin línea.** Hoy una tabla es inválida si `global.max_step > max_step`
o si una línea queda vacía; `is_valid_owners` exige una línea no vacía en cada paso `0:nsteps-1`.
Son lo mismo si ninguna tabla tiene huecos intermedios. Se comprueba con un assert en F2.

### F3 — accesorio de compatibilidad y visual

- `GraphPath.owners_table(gpath, id) :: Dict{Step, Set{PathNodeId}}` = `as_table`, para tests y
  para `graph_path_visual.jl` (`draw_owners`).
- Adaptar los tests de `test/graph_path` y `test/db/path` que leen `node.owners`.

### F4 — diferencial contra `improves_bin`

Las dos máquinas definen `AbsSat`, así que no conviven en un proceso:

- `test_3sat/dump_final.jl <src_root> <out.tsv>`: para cada instancia del corpus de `compare_sym.jl`,
  veredicto, soluciones del lector comprobadas con `CheckerCnf`, verdad del exhaustivo, y estado
  final de la línea como conjuntos ordenados (nodos, global, tabla, padres e hijos de cada nodo).
  En `improves_bin` la tabla sale de `node.owners`; en `improves_bingo`, de `owners_table`.
- `test_3sat/compare_bingo.jl`: compara las dos salidas. Criterio de paso: mismos veredictos,
  mismas soluciones y mismos estados finales en todo el corpus.

### F5 — medida

Por instancia (test_window y test_3sat), en las dos máquinas: tiempo, `@allocated` del `run!`,
`Sys.maxrss()`, vueltas del review. Y en bingo, `removed_by` por regla. Si la memoria empeora mucho:
crear los `Edge` solo cuando una regla necesite datos (el grafo queda en `alive` + `inc`).

### F6 — reglas sobre aristas (fuera de este plan, con ok aparte)

Regla del segmento, contadores de apoyo con cola de trabajo. Cada una detrás de un flag y medida con
`removed_by`.

## Decisiones antes de F2

1. **Filtros fuera del review** (`agresive`, `witness`, `chain`, `triangle`): hoy no se llaman desde
   `make_review_owners!`, solo desde tests. ¿Se portan al grafo o se quitan de bingo?
2. **Sondas** (`test_3sat/probes`, ~80 ficheros que leen `node.owners`): propuesta, quitarlas de bingo;
   siguen en `improves_bin`.
3. **`Edge` desde el principio**: sí (decidido 27-sept). F5 dirá si conviene hacerlos perezosos.

## Commits

Uno por fase (F1, F2, F3, F4, F5), cada uno con los tests en verde; F4 con la tabla del diferencial
en el mensaje del commit.
