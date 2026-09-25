# Verificación para el Autor v193: el mapa bin en el diferencial — 73/73, y el coste que quitó el filtro agresivo

Ricardo, aquí está el cierre del trabajo del mapa binario en `julia/improves_bin`: la implementación de
las fases A–D, los cuatro errores que aparecieron por el camino, y el resultado del diferencial tras el
ajuste de rendimiento que hiciste. Lo cuento primero, porque es la conclusión: **el mapa bin da los
mismos veredictos y las mismas soluciones que el clásico y que el exhaustivo en las 73 instancias del
corpus, y quitar el filtro agresivo del review lo acelera ~3,5× sin cambiar ningún resultado**.
Complementa al v192, que analiza qué gana la prueba Lean con el mapa bin; este es el lado de la
máquina.

Rama `improves_bin`. Módulos `GraphMapBin` (`src/graph_map/graph_map_bin.jl`), el UP
(`graph_path_up.jl`), la máquina y el lector polimórficos (`sat_machine.jl`, `path_reader.jl`), y el
harness diferencial `test_3sat/compare_bin.jl`. Commits `ccc2006`, `5c8a6ae`, `92315b1`, `ba6cc6d`,
`6b6359f`.

---

## 1. Contexto: qué se implementó

El plan `docs/plans/bin-map.md` (desde v187 §5) proponía **binarizar las cláusulas** para que todo paso
del mapa tenga **2 nodos**, de modo que el Helly de un paso sea siempre el lema de dos elementos. La
disyunción sale de las tablas y pasa a la **existencia de nodos**: la ventana `(L1,L2,L3)=(0,0,0)` no
existe.

Se creó, desde cero y sin tocar el mapa clásico, el módulo `GraphMapBin` con la estructura simétrica:

```
[0 fusión raíz][1..2n variables][2n+1 fusión media][2n+2..2n+3m+1 cláusulas: 3 pasos × 2 nodos][2n+3m+2 fusión final]
```

- `stepCount = 2n + 3m + 3`.
- Cada cláusula `j` son 3 pasos (`L1_j`, `L2_j`, `L3_j`) de 2 nodos; el nodo `Lp_j=b` **requiere** el
  literal `lp` con valor `b` (un solo require, sin los "requires negados" del clásico).
- La **ventana prohibida** de la cláusula `j` es el `PathNodeId`
  `((2n+2+3j,0), (2n+3+3j,0), (2n+4+3j,0))`, filtrado en el UP (`group_parents_by_shifted_id`).

La máquina y el lector se hicieron polimórficos (leen `GMap` y `GMapBin`): el lector ganó un
`first_lit_step` (0 clásico / 1 bin) porque el fusión raíz desplaza las variables a pasos impares.

## 2. Los cuatro errores (resumen)

Documentados en `docs/bitacora/bin-map_informe_errores.md`:

| # | error | causa | solución |
|---|---|---|---|
| 1 | fusión raíz sin enlazar con la variable 1 | `get_ids_last_step` heredó `step-1 > 0` | `step > 0` |
| 2 | `round(x, 2)` posicional en el harness | 2º argumento de `round` es `RoundingMode` | `round(x, digits=2)` |
| 3 | falso positivo UNSAT | `add_row!` no invalidaba el gpath al quedar sin candidatos | `is_valid=false` + re-check en `do_up!` |
| 4 | nodo muerto en gpath SAT | el review corre antes de `add_row!` y no repasaba | `review_owners=true` al saltar la ventana |

Los errores 3 y 4 son los que tienen contenido: son consecuencias de que la ventana prohibida **puede
dejar un paso de cláusula sin candidato**, algo que al mapa clásico no le pasa nunca. El 3 hacía que el
gpath "avanzara" vacío (falso SAT); el 4 dejaba viva una rama muerta (nodo sin hijo que el lector
detectaba como `GRAVE ERROR`). Ambos los cazó el diferencial, que es justo su razón de ser.

## 3. Resultado del diferencial

`compare_bin.jl` sobre el corpus (`test/example_cnf` + `test_window/instances` + 45 sembradas en
`instances_bin`), con `PAIR_MODE = :on`:

| métrica | resultado |
|---|---|
| instancias | 73 (1 saltada: `simple_v3_c2.cnf`, un 2-SAT) |
| mismo veredicto (clásico == bin) | **73 / 73** |
| ambos aciertan la verdad (vs exhaustivo) | **73 / 73** |
| mismas soluciones (lector exponencial) | **73 / 73** |
| fallos de checker | **0** |

El mapa bin es semánticamente equivalente al clásico en todo el corpus.

## 4. El filtro agresivo, y qué compró quitarlo

El review (`make_review_owners!`) llamaba a `agressive_consistence_filter!` en cada pasada. Es el paso
caro: recorre, para cada nodo `x`, todos sus owners `w` en todos los pasos, y comprueba simetría e
intersección — un `O(S²)` sobre las tablas (fichero `graph_path_filter_agresive.jl`, contadores
`AGG_ASYM`/`AGG_INCONS`).

Lo comentaste, y además dejaste `pair_consistency_after_clean!` condicionado a `PAIR_MODE = :on`
(antes se llamaba incondicionalmente). El resultado:

| | antes | después | mejora |
|---|---|---|---|
| tiempo máquina bin | 3036,3 s | **860,8 s** | ~3,5× |
| tiempo máquina clásico | 139,7 s | **52,4 s** | ~2,7× |
| tiempo lectores | 188,2 s | **52,6 s** | ~3,6× |
| ratio máx. `steps` (bin/clásico) | 2,37 | 2,37 | — |
| ratio máx. `peak_nodes` | 4,09 | 4,09 | — |

Los ratios de estructura no cambian: **el resultado es idéntico, solo cae el coste**. Es coherente con
lo que ya se sabía — en v189, `AggInactive` es teorema: en el punto fijo del review, el barrido
agresivo es la identidad, así que quitarlo no pierde nada y se ahorra la pasada `O(S²)` en cada vuelta.
La ganancia beneficia a los dos mapas, porque el review es el mismo.

## 5. Lo previsto

1. **Adoptar el cambio en `improves`** (el clásico): quitar `agressive_consistence_filter!` y
   condicionar la regla de parejas a `PAIR_MODE`, si quieres que la máquina de referencia se beneficie
   de la misma ganancia (~2,7×).
2. **El espejo Lean del mapa bin** (`CnfMap.lean`), alineado con `GraphMapBin`: `reqOfCnf` por literal,
   `mapNodes` de 2 por paso, y la ventana prohibida como predicado de forma. Es la vía que el v192
   analiza en detalle: desaparecen las cajas y la escalera `OneStep → SegGood/PairHelly` queda con una
   sola hipótesis sobre las tablas (el triángulo con el extremo, `TriTop`).
3. **Medir si el bin, con el filtro agresivo fuera, ya no necesita más optimización** (el coste restante
   es el triple de pasos de cláusula, `m → 3m`, que es estructural).

## 6. Una frase

El mapa bin es el clásico reescrito para que el Helly de un paso sea trivial; el diferencial dice que
deciden lo mismo en las 73 instancias, y quitar el filtro agresivo —que en el punto fijo era la
identidad— lo dejó ~3,5× más rápido sin tocar un solo resultado.
