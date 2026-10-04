# Mapa binario (`bin`) con ventana prohibida — Plan

> Rama de trabajo: `bin-map` (desde `pair-mode`).
> Código: `julia/improves_bin/` (copia dedicada; `julia/improves/` queda **congelada** como referencia clásica).
> Origen: v187 §5 (propuesta) y v191 §6.1 (límite: no arregla el trío, sí trivializa el Helly de un paso).

## 1. Objetivo

Crear **desde cero** un tipo de mapa nuevo, `bin`, con estructura **simétrica**
`[fusión][variables][fusión][cláusulas][fusión]`, donde cada cláusula son **3 pasos de 2 nodos**
(valores `0`/`1` de cada literal de la cláusula) y una **ventana prohibida `(0,0,0)`** al final de los
tres. **No se toca** el mapa clásico. Se **adapta la máquina y el lector** para leer el mapa bin.
Sin los "requires negados" del clásico (refuerzo 15-09-2026).

**Qué se busca:** que el Helly de un paso (alargar un tramo un paso) sea siempre el lema de dos
elementos, porque todo paso del mapa bin tiene **2 nodos**. La disyunción sale de las tablas y pasa a la
**existencia de nodos**: una ventana prohibida no existe, y una cadena completa nunca puede pasar por
ella (hecho de forma, no de exactitud). No resuelve el fallo de tríos de la semilla 11 (v191 §6.1).

## 2. Especificación del mapa `bin` (pasos 0-indexados, `n` variables, `m` cláusulas)

| paso | contenido |
|---|---|
| `0` | **Fusión raíz** (1 nodo, sin requires) |
| `2v-1` (v=1..n) | positivos `⟨2v-1,0⟩` "v=0", `⟨2v-1,1⟩` "v=1" — sin requires |
| `2v`   (v=1..n) | negados `⟨2v,i⟩` "!v=i", requiere `⟨2v-1, 1-i⟩` |
| `2n+1` | **Fusión media** |
| `2n+2+3j` | `L1_j`: 2 nodos; `L1_j=b` requiere `⟨step(l1), b⟩` |
| `2n+3+3j` | `L2_j`: 2 nodos; `L2_j=b` requiere `⟨step(l2), b⟩` |
| `2n+4+3j` | `L3_j`: 2 nodos; `L3_j=b` requiere `⟨step(l3), b⟩`; **ventana prohibida `(0,0,0)`** |
| `2n+3m+2` | **Fusión final** |

- `stepCount = 2n + 3m + 3`.
- `step(lp) = get_step_var(lp)` (paso positivo si `lp` es "v", negativo si "!v"); el índice `b` es el
  **valor de verdad del literal**.
- **Ventana prohibida** de la cláusula `j` (un `PathNodeId` concreto):
  ```
  PathNodeId(gparent=(2n+2+3j, 0), parent=(2n+3+3j, 0), id=(2n+4+3j, 0))
  ```
  El `shift_path_id` del UP produce `(map@h-2, map@h-1, map@h)`, y en `L3_j` esos tres pasos son
  exactamente `L1_j, L2_j, L3_j`.

**Corrección informal.** Camino superviviente ↔ asignación + elección de literal satisfecho por
cláusula: los requires fijan cada literal a su valor, y la ventana prohibida descarta el caso "los tres
falsos". Misma semántica que el 7-filas, repartida en 3 pasos.

## 3. Arquitectura

- **`julia/improves`** → congelada (referencia clásica y máquina "de producción").
- **`julia/improves_bin`** → todos los cambios.
  - **Nuevo módulo** `GraphMapBin` (`src/graph_map/graph_map_bin.jl`), escrito de cero:
    - `mutable struct GMapBin` = campos de `GMap` + `prohibited_windows :: Set{PathNodeId}`.
    - `new()`, `make_fusion_node!`, `add_var!`, `add_gate_bin!`, `close_vars!`, `close_gates!`,
      `load_import_bin!`, `cnf_p!`, `cnf_or!`.
    - **Reutiliza** `MapColLines`, `MapColVars`, `MapDocumentNode` (genéricos).
  - `graph_map.jl` clásico queda **intacto** dentro de `improves_bin` (para el diferencial intra-copia).
  - **Máquina** (`SatMachine`) lee ambos: `send_to_destine!` pasa `prohibited_windows` al UP
    (clásico → conjunto vacío).
  - **UP** (`graph_path_up.jl`): `do_up_filtering!`/`do_up!`/`add_row!`/`group_parents_by_shifted_id`
    reciben `prohibited :: Set{PathNodeId}` (default vacío) y **saltan** el `path_id_node` que esté en él.

## 4. Pruebas unitarias del mapa `bin`

Fichero nuevo: `julia/improves_bin/test/graph_map/test_graph_map_bin.jl` (estilo `@testset`/`@test`,
como `test_pair_mode.jl`), registrado en `test/runtests.jl` bajo un `@testset "GraphMapBin"`.

Para un mapa pequeño (`n=3..4`, `m=2..3`), construido con `load_import_bin!` sobre un `.cnf` del
corpus (p. ej. `simple3sat_v3_c2.cnf`) o con `add_var!`/`add_gate_bin!` directo:

1. **Estructura y conteo**
   - `@test gmap.step == 2n + 3m + 3`.
   - Nº de nodos por paso: `0 → 1`, `1..2n → 2`, `2n+1 → 1`, pasos de cláusula `→ 2`,
     `2n+3m+2 → 1`.
   - Títulos: paso `0`, `2n+1` y `2n+3m+2` son `"FusionNode"`.

2. **Requires por literal**
   - Para cada cláusula `j`, el nodo `Lp_j=b` requiere **exactamente** `⟨step(lp), b⟩`
     (un solo require; sin "negados"): `@test Set(node.requires) == Set([(step=step(lp), index=b)])`.

3. **Ventanas prohibidas**
   - `@test length(gmap.prohibited_windows) == m`.
   - Para cada `j`:
     `@test PathNodeId((2n+2+3j,0), (2n+3+3j,0), (2n+4+3j,0)) ∈ gmap.prohibited_windows`.

4. **Variables (desplazadas)**
   - Positivos en `2v-1` (índices `0,1`), negados en `2v`.
   - El nodo negado `⟨2v,i⟩` requiere `⟨2v-1, 1-i⟩`.

5. **Enlaces (sons/parents)**
   - Fusión raíz tiene `sons = {⟨1,0⟩, ⟨1,1⟩}` (los dos positivos de `v=1`).
   - Fusión media es hija de los dos negados de `v=n`.
   - Cada paso de cláusula encadena con el paso anterior (los `sons` del paso `k` apuntan al `k+1`).

6. **Semántica (mapa ↔ fórmula, sin máquina)** — el test que valida la codificación bin + la ventana
   prohibida de forma exhaustiva e independiente del review:
   - Ayudante `chain_exists(gmap, asig) :: Bool`: recorrer el DAG por capas (sons + requires), guardando
     los nodos alcanzables consistentes con la asignación; devolver `true` si el último paso tiene al
     menos un nodo alcanzable.
   - Para `n` pequeño, enumerar las `2^n` asignaciones y comprobar
     `chain_exists(gmap, asig) == CheckerCnf.test(asig, fichero)` (donde `asig` es el `BitArray`).
   - Esto cubre en concreto el caso `(0,0,0)`: la asignación "los tres literales falsos" no debe tener
     cadena, y sí las siete restantes de cada cláusula.

Criterio: la batería corre con `julia --project=. test/runtests.jl` (desde `improves_bin`) en verde, y
`@testset "GraphMapBin"` no deja ningún fallo antes de tocar la máquina.

## 5. Fases de implementación

**Fase A — mapa `bin` desde cero** (`src/graph_map/graph_map_bin.jl`):
1. `GMapBin` + `new()` con `prohibited_windows = Set{PathNodeId}()`.
2. `make_fusion_node!` (idéntico al clásico).
3. `add_var!` (idéntico al clásico; solo cambian los nº de paso).
4. `add_gate_bin!(gmap, la, lb, lc)`:
   - L1: 2 nodos `⟨step, b⟩` requieren `⟨step(la), b⟩`; enlazar al último paso; `step += 1`.
   - L2: análogo con `lb`; `step += 1`.
   - L3: análogo con `lc`; `step += 1`; y
     `push!(prohibited_windows, PathNodeId((L1,0),(L2,0),(L3,0)))`.
   - `clausule_counter += 1`.
5. `load_import_bin!`: fusión raíz → `cnf_p!` (vars) → `close_vars!` (fusión media) → `cnf_or!`
   (cláusulas) → `close_gates!` (fusión final).

**Fase A.5 — pruebas unitarias** (sección 4): escribir y pasar `test_graph_map_bin.jl` antes de seguir.

**Fase B — UP con ventana** (`graph_path_up.jl`): parámetro `prohibited` + salto en
`group_parents_by_shifted_id`.

**Fase C — máquina + lector polimórficos:**
- `sat_machine.jl`: pasar `prohibited_windows`.
- `path_reader.jl` / `path_exp_reader.jl`: añadir `first_lit_step :: Step` a `GPathReader`
  (`0` clásico / `1` bin); el resto (`step += 2`, parar en `"FusionNode"`/`"or"`) queda igual. El
  `PathExpReader` propaga el mismo valor. Para el clásico, comportamiento idéntico al actual.

**Fase D — validación diferencial** (`test_3sat/compare_bin.jl`, esqueleto de `compare_pair.jl`):
clásico vs binario con `PAIR_MODE=:on`; compara veredicto, nº de soluciones (`PathExpReader`), validez
(`CheckerCnf`) y contra el exhaustivo; columnas `peak_row`, `peak_nodes`, `stepCount`, `secs`.
**Aceptación:** 0 desacuerdos en ≥80 instancias sembradas.

## 6. Estrategia diferencial (dos niveles)

1. **Intra-copia (rápida, para iterar)** — `improves_bin` conserva el mapa clásico y añade el `bin`;
   `compare_bin.jl` corre **cada instancia bajo los dos mapas** en el mismo proceso (igual que
   `compare_pair.jl` alterna `PAIR_MODE`).
2. **Cross-copia (comprobación final)** — correr `improves/.../compare_pair.jl` (clásico) y
   `improves_bin/.../compare_bin.jl` (bin) sobre el mismo corpus y `diff` de los TSV. Como ambos usan el
   módulo `Main.AbsSat`, no conviven en un proceso; se comparan salidas.

## 7. Riesgos

- **Lector** (Fase C): mayor riesgo nuevo; el diferencial lo cubre comparando conjuntos de soluciones.
- **Coste**: `stepCount` de `m` a `3m` pasos de cláusula; se mide `peak_nodes`/`secs`.
- **Ventana en paso equivocado** (solo `L3` la lleva): cubierto por el test unitario 3 y el diferencial.
- **Sin "requires negados"**: si el pruning baja y crecen los nodos, se mide y se decide reintroducirlos.

## 8. Fuera de alcance

- `GraphPow`/`SatMachinePow` (mapa clásico).
- Espejo Lean `CnfMap.lean` (se escribe después, alineado con la Fase A).

## 9. Rama

Nueva `bin-map` desde `pair-mode`. `julia/improves_bin` ya está trackeado por git; el clásico queda como
referencia viva para el diferencial.
