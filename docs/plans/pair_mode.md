# Plan: la regla de parejas tras la limpieza (`PAIR_MODE`), en Julia Improves y en Lean 4

Informe de referencia: `docs/bitacora/verificacion_inseguridad_autor_v185.md`, §5–§6.
Rama de trabajo: `pair-mode` (sale de `spaik`, que ya incluye `review-symmetric`).

## Principio

Si dos nodos vivos `x`, `w` se poseen y en algún paso sus tablas no comparten ninguna entrada,
ninguna solución pasa por los dos: la posesión se deshace **en las dos direcciones**. Es la rama
«inconsistente» del filtro agresivo, adelantada a **justo después de la limpieza**, que es donde el pin
deja los tramos sin entrada común (v185 §1: los 86 condenados tienen un conflicto de pareja).

Objetivo para la prueba: cambiar la hipótesis por pin `RoundExact` (dinámica: una vuelta entera) por
`PairHelly` (estática: un solo estado).

## Decisión de diseño: la regla en dos fases, como `cleanInvalid₂`

El borrador del v185 recorría los nodos y quitaba parejas sobre la marcha. Propongo cambiarlo por la
versión en **dos fases**:

1. con las tablas **tal como están** (una instantánea), se marcan todas las parejas malas;
2. se quitan todas a la vez;
3. se purga (`clean_invalid_nodes!`), y se repite mientras algo cambie.

Por qué:

* **no depende del orden** en que se recorren los nodos. En Julia, además, el orden de un `Set` es
  el del hash, así que la versión secuencial podría dar resultados distintos que el modelo;
* el modelo Lean queda en **un `map`**, sin `fold`: `pairSweep g` = cada nodo filtra su tabla contra el
  estado `g` de antes. Las pruebas de forma salen casi gratis, y la simetría sale de que el test es
  simétrico;
* la regla es monótona (quitar entradas solo puede hacer fallar más parejas), así que el punto fijo es
  el mismo con cualquier orden. La versión secuencial tendría el mismo punto fijo, pero puede hacer
  otro número de vueltas.

**El test de pareja** debe ser simétrico y comportarse como el `intersect!` de Julia: un paso cuenta
solo si **las dos** tablas tienen entradas en él. El `sharesEveryStep` del modelo agresivo no es
simétrico cuando una tabla no tiene ninguna entrada en un paso y la otra sí; para esta regla se define
uno nuevo, `pairShares`.

## Cómo se decide (antes de nada)

Igual que con el espejo: detrás de un interruptor, medir, y adoptar solo si

1. los **veredictos** coinciden en todo el corpus (obligatorio);
2. los **estados finales** coinciden, o las diferencias se explican y tú las aceptas;
3. el **coste** es comparable;
4. **`PairHelly` se mide sin fallos** en los estados del lector (sonda `pairhelly`, C1). Si falla, la
   regla no simplifica la prueba y no merece la pena adoptarla.

---

## Fase A — Julia (`julia/improves`)

### A0. Medir la situación actual (sin cambiar la máquina)

En `agressive_consistence_filter!`, contador `AGG_INCONS` en la rama «inconsistente» (la que la regla
adelanta). Anotar sus valores de base en `test_window` y en las 80 instancias de `compare_sym.jl`.

### A1. El test de pareja

En `PathDocumentOwners`:

```julia
# ¿Comparten las dos tablas al menos una entrada en cada paso que tienen las dos?
# Simétrica; sin copias (misma semántica que intersect! + is_valid sobre los pasos comunes).
function shares_every_step(owners_a :: PathDocOwners, owners_b :: PathDocOwners) :: Bool
    #! [for] $ O(S) $
    for (step, set_a) in owners_a.table
        set_b = get(owners_b, step)
        set_b === nothing && continue
        short, long = length(set_a) <= length(set_b) ? (set_a, set_b) : (set_b, set_a)
        #! [fixed] $ O(7) $
        any(id -> id in long, short) || return false
    end
    return true
end
```

Test (`test/db/test_path_doc_owners.jl`, o donde vivan los de `intersect_removed!`):

* simetría: `shares_every_step(a, b) == shares_every_step(b, a)`;
* coincide con `intersect!` + `is_valid` sobre una copia cuando `max_step` es el mismo;
* casos: un paso solo en una tabla (se ignora); un paso con las dos y disjunto (falla).

### A2. La regla

En un fichero propio, `src/graph_path/graph_path_filter_pair.jl`, incluido en `graph_path.jl` junto a
los demás filtros (hecho: commit `e2cf8ba`). El test de pareja (A1) va en `PathDocumentOwners`.

```julia
# Regla de parejas tras la limpieza (informe v185 §5, plan pair_mode).
const PAIR_MODE = Ref(:off)     # :off | :on

const PAIR_REMOVED = Ref(0)     # parejas deshechas
const PAIR_ROUNDS  = Ref(0)     # vueltas regla + purga
const PAIR_MAXSTEP = Ref(0)     # parejas con max_step distinto (debería ser 0)

# Fase 1: con las tablas tal como están, se marcan las parejas malas.
# Fase 2: se quitan todas (las dos direcciones), se purga, y se repite mientras algo cambie.
function pair_consistency_after_clean!(gpath :: GPath)
    changed = true
    #! [while] $ O(N*7) $ vueltas como mucho: cada vuelta que sigue ha deshecho una pareja
    while changed && gpath.is_valid && gpath.table_lines.is_valid
        changed = false
        PAIR_ROUNDS[] += 1
        bad = Tuple{PathNodeId, PathNodeId}[]
        #! [fn-iter] $ O(S*7*7) $
        PathCollectionLines.for_each(gpath.table_lines, function (node_x)
            for (_, ids_w) in node_x.owners.table
                #! [for] $ O(7*7) $
                for node_id_w in ids_w
                    node_id_w == node_x.id && continue
                    node_w = PathCollectionLines.get_node(gpath.table_lines, node_id_w)
                    node_w === nothing && continue
                    PAIR_MAXSTEP[] += node_w.owners.max_step != node_x.owners.max_step
                    #! [fixed] $ O(S*7) $
                    if !PathDocumentOwners.shares_every_step(node_x.owners, node_w.owners)
                        push!(bad, (node_x.id, node_id_w))
                    end
                end
            end
        end)
        #! [for] $ O(|bad|) $
        for (x_id, w_id) in bad
            node_x = PathCollectionLines.get_node(gpath.table_lines, x_id)
            node_w = PathCollectionLines.get_node(gpath.table_lines, w_id)
            node_x !== nothing && PathDocumentNode.remove_owner!(node_x, w_id)
            node_w !== nothing && PathDocumentNode.remove_owner!(node_w, x_id)
            PAIR_REMOVED[] += 1
            changed = true
        end
        if changed
            gpath.review_owners = true
            clean_invalid_nodes!(gpath)
        end
    end
end
```

Se llama en `make_review_owners!`, justo después de `clean_invalid_nodes!(gpath)`:

```julia
        clean_invalid_nodes!(gpath)
        if PAIR_MODE[] == :on
            pair_consistency_after_clean!(gpath)
        end
        review_owners_coherence_with_its_parents_sons!(gpath)
```

Nota: con `SYM_MODE = :on` cada pareja mala aparece dos veces en `bad`, como `(x, w)` y como `(w, x)`.
`remove_owner!` de un id que ya no está debe ser inocuo; si no lo es, se deduplica `bad`. En ese caso
`PAIR_REMOVED` cuenta cada pareja dos veces, cosa que hay que tener en cuenta al leerlo.

### A3. Test en `runtests`

`test/graph_path/test_pair_mode.jl`: con `PAIR_MODE = :on`, en `test_window` y en los estados
pinchados:

* tras `pair_consistency_after_clean!`, toda pareja mutua viva comparte entrada en cada paso (`PairOk`);
* la simetría se conserva (0 parejas asimétricas);
* `PAIR_MAXSTEP == 0`;
* mismos veredictos que con `:off`.

### A4. Comparación diferencial

`test_3sat/compare_pair.jl`, como `compare_sym.jl`: las 80 instancias con `:off` y con `:on`. Se
comparan veredictos, estados finales (`owners` de cada nodo, global), número de vueltas del review,
tiempo, `PAIR_REMOVED`, `PAIR_ROUNDS` y `AGG_INCONS`. Lo esperado: mismos veredictos, mismos estados
finales, `AGG_INCONS` mucho más bajo con `:on`, y quizá menos vueltas.

### A5. Adopción

Si A3 y A4 salen bien y C1 da 0 fallos: `PAIR_MODE = :on` por defecto.

---

## Fase B — Lean 4, el modelo (`lean_project/AbsSat/GraphPath/Model`)

### B0. Definiciones (`GPathM.lean`)

```lean
/-- Las dos tablas comparten una entrada en cada paso que tienen las dos (Julia
`shares_every_step`). Simétrica por construcción. -/
def pairShares (cs : Int) (xo wo : List PathNodeId) : Bool :=
  (intRange 0 (cs - 1)).all (fun k =>
    !hasStepEntry xo k || !hasStepEntry wo k || (ownersAt xo k).any (fun r => wo.contains r))

/-- `w` es una pareja mala de `n` en `g`: vivo, distinto, y sin entrada común en algún paso. -/
def pairBad (g : GPathM) (n : PNodeM) (w : PathNodeId) : Bool :=
  w != n.id && match g.node? w with
    | some nw => !pairShares g.current_step n.owners nw.owners
    | none => false

/-- **La regla de parejas, una fase**: cada nodo quita de su tabla sus parejas malas, todas contra
el mismo estado `g`. -/
def pairSweep (g : GPathM) : GPathM :=
  { g with nodes := g.nodes.map (fun n => { n with owners := n.owners.filter (fun w => !pairBad g n w) }) }

/-- Regla + purga hasta que no cambie nada (Julia `pair_consistency_after_clean!`). -/
def pairFuel : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    if isValid g then
      let g' := cleanInvalid₂ (pairSweep g)
      if measure g' < measure g then pairFuel fuel g' else g'
    else g

/-- **La limpieza con parejas**: la de siempre y después la regla hasta el punto fijo. -/
def cleanPair (g : GPathM) : GPathM :=
  let g₀ := cleanInvalid₂ g
  pairFuel (measure g₀ + 1) g₀

def reviewPass (g : GPathM) : GPathM :=
  reviewSons (reviewParents (cleanPair g))      -- antes: cleanInvalid₂ g
```

Clave del diseño: **`cleanPair` siempre termina en un `cleanInvalid₂`**, o es `cleanInvalid₂ g` si la
regla no quita nada. Todo lo que la limpieza *establece* (enlaces en la tabla, nodos en la global,
tablas cortadas) sigue siendo cierto sin esfuerzo. Lo que hay que demostrar de nuevo es lo que la
limpieza solo *conserva*: para esas propiedades hace falta la versión `pairSweep`.

### B1. `PairSweep.lean` (módulo nuevo): lo que hace `pairSweep`

Los lemas de forma. `pairSweep` solo encoge tablas: no toca ids, enlaces, global ni paso.

| lema nuevo | modelo en el que se basa |
|---|---|
| `pairShares_comm` | — (simetría del test) |
| `pairSweep_node?` / `pairSweep_node?_inv` | `mirrorDrop_node?` / `_inv` (`Pruned.lean`) |
| `pruned_pairSweep` | `pruned_mirrorDrop` |
| `measure_pairSweep_le` | `measure_cleanInvalid₂_le` |
| `ids_pairSweep`, `nodupIds_pairSweep` | `ids_cleanInvalid₂`, `nodupIds_cleanInvalid₂` |
| `isValid_pairSweep` (la validez global no cambia) | — |
| `pairFuel_inv` (una propiedad que conservan `pairSweep` y `cleanInvalid₂` pasa a `pairFuel`) | `purgeFuel_inv` |
| `cleanPair_eq_cleanInvalid₂_or` (`cleanPair g` es `cleanInvalid₂ h` para algún `h` podado de `g`) | — (el puente de B2) |

**La corrección** de la regla (la regla no pierde soluciones):

| lema nuevo | modelo en el que se basa |
|---|---|
| `pairShares_of_chain` (en una cadena sana, dos nodos de la cadena comparten entrada en cada paso) | `sharesEveryStep_of_chain` (`AggressiveReview.lean`) |
| `ChainSound_pairSweep` | `ChainSound_aggPair` / `ChainSound_cleanInvalid₂` |
| `ChainSound_cleanPair` | `ChainSound_cleanInvalid₂` |

### B2. Los lemas `…_cleanInvalid₂` que hay que llevar a `cleanPair`

Hay 26 lemas `P_cleanInvalid₂`. Para cada uno: o bien lo establece la limpieza sola (**gratis**, por
el puente de B1), o bien hace falta `P_pairSweep` (**conservación**).

| lema de hoy | archivo | tipo | nota |
|---|---|---|---|
| `pruned_cleanInvalid₂` | Pruned | conservación | `pruned_pairSweep` |
| `measure_cleanInvalid₂_le` | Fuel | conservación | `measure_pairSweep_le` |
| `ids_cleanInvalid₂`, `nodupIds_cleanInvalid₂` | NodeIds | conservación | directos |
| `keeps_cleanInvalid₂`, `RCtx_cleanInvalid₂` | CleanTwoPhase | conservación | revisar qué pide `keeps` |
| `owners_in_gowners_cleanInvalid₂`, `owners_live_cleanInvalid₂` | CleanTwoPhase | gratis | termina en limpieza |
| `isValidNode_cleanInvalid₂` | CleanTwoPhase | gratis | idem |
| `nodesGow_cleanInvalid₂` | ReadyInv | gratis | idem |
| `links_cleanInvalid₂` | ReadyInv | gratis | idem |
| `ownLive_cleanInvalid₂` | SelfOwn | conservación | la regla nunca quita `n.id` de su tabla (`w != n.id`) |
| `OwnSymmetric_cleanInvalid₂` | SymInvariant | conservación | **simetría de `pairBad`** vía `pairShares_comm` |
| `GN_cleanInvalid₂` | GownersNodes | conservación | la global no cambia |
| `PN_cleanInvalid₂` | Parents | conservación | los enlaces no cambian |
| `SMP_cleanInvalid₂`, `PMS_cleanInvalid₂`, `SAbove_cleanInvalid₂`, `SN_cleanInvalid₂` | Sons | conservación | **las que más cuestan**: hablan de tablas de padres e hijos, y la regla las encoge. Seguir el patrón del espejo (B2 del plan simétrico) |
| `AOk_cleanInvalid₂` | AnchoredSurvive | conservación | idem |
| `FOk_cleanInvalid₂` | Fabric | conservación | idem |
| `WOk_cleanInvalid₂` | Survive | conservación | idem |
| `ChainSound_cleanInvalid₂` | CleanInvalid | conservación | B1 |
| `cleanInvalid₂_eq_self`, `cleanInvalid₂_fixed_node` | Fuel / Coherence | ver B4 | punto fijo |
| `cleanInvalid₂_eq_self_of_ready` | PinDoomed | ver B4 | ahora hace falta `PairOk` además de `Ready` |

Riesgo principal: **`SMP`/`PMS`/`SN`/`SAbove`/`AOk`/`FOk`/`WOk`**. Con el espejo pasó lo mismo (las
tablas de otros nodos dejan de ser constantes), y se resolvió porque la cadena completa de un miembro
protegía la entrada. Aquí el argumento debería ser más fácil: `pairSweep` es un `map` contra un estado
fijo, no un `fold`.

### B3. Los teoremas de `reviewPass` que se abren por dentro

Cada uno cambia una línea: el lema de `cleanInvalid₂` por el de `cleanPair`.

| teorema | archivo |
|---|---|
| `pruned_reviewPass` | Pruned |
| `measure_reviewPass_le`, `reviewPass_eq_self`, `reviewPass_stages_eq_self` | Fuel |
| `ChainSound_reviewPass` | Coherence |
| `FOk_reviewPass` | Fabric |
| `GN_reviewPass` | GownersNodes |
| `PN_reviewPass` | Parents |
| `OOS_reviewPass` | SelfOwn |
| `SMP_reviewPass`, `PMS_reviewPass`, `SAbove_reviewPass`, `SN_reviewPass` | Sons |
| `WOk_reviewPass` | Survive |
| los que escriben `reviewParents (cleanInvalid₂ …)` a mano | Fabric, Fuel (2), PickInduction, ReadyInv, Survive (2) |
| `OwnSymmetric_reviewPass`, `pstateG_reviewPass'`, `pstateG_reviewPass_of` | SymInvariant |
| `nodesGow_reviewPass`, `links_reviewPass` | ReadyInv |

Y los que dependen de ellos sin abrir `reviewPass` (`…_review`, `…_reviewAgg`, `…_filterAllAgg`, la
escalera) no deberían cambiar.

### B4. El punto fijo y la terminación

* `reviewPass_eq_self`: si `reviewPass g` no baja la medida, es `g`. Ahora hace falta que `cleanPair`
  sea la identidad sin bajar la medida: `pairSweep` que no baja la medida no quita nada (cada quitada
  baja `weight`), así que es la identidad, igual que la limpieza.
* `cleanInvalid₂_eq_self_of_ready` → `cleanPair_eq_self_of_ready`: sobre un estado `Ready` y con
  `PairOk`, `cleanPair` es la identidad. **`PairOk` no se conserva en las pasadas** (cortar tablas
  puede crear parejas malas). No hace falta para la escalera nueva (B6), que va por `RoundExact`.
  Afecta a `LaterValid`/`ready_iterPass` (PinDoomed): se dejan como están, o se añade la hipótesis.
* `Fuel.lean`: `pairFuel` tiene suficiente con `measure g₀ + 1` unidades (cada vuelta que sigue baja la
  medida). Mismo esquema que `purgeFuel`.

### B5. `PairOk` y `PairHelly` (`PairHelly.lean`, módulo nuevo)

```lean
/-- Toda pareja que se posee comparte entrada en cada paso. -/
def PairOk (g : GPathM) : Prop :=
  ∀ x n w, g.node? x = some n → w ∈ n.owners → w ≠ x → ∀ nw, g.node? w = some nw →
    pairShares g.current_step n.owners nw.owners = true

theorem pairOk_cleanPair (g) (hv : isValid (cleanPair g) = true) : PairOk (cleanPair g)
-- en el punto fijo de pairFuel: la última pairSweep no quitó nada. Cuidado: la última
-- cleanInvalid₂ corta tablas; hay que ver que el corte con la global no rompe PairOk
-- (con Ready, el corte es la identidad: cutNode_eq_self_of_ready).

/-- **La hipótesis por pin nueva**: con parejas compatibles, todo tramo tiene entrada común. -/
def PairHelly (C : GPathM) : Prop := isValid C = true → PairOk C → SegGood C
```

### B6. La escalera nueva

```lean
theorem roundExact_of_pairHelly (X) (…contexto del pin…) (hH : PairHelly (cleanPair X)) : RoundExact X
-- SegGood (cleanPair X)  (PairHelly + pairOk_cleanPair)
-- → SegGood tras reviewParents y reviewSons  (segGood_reviewNode_parents/sons, ya demostrados,
--   con PStateG a la entrada de las pasadas: pstateG_reviewPass_of)
-- → SegExact (reviewPass X)  (SegGood + PStateG en la salida de la vuelta ⇒ cadena completa;
--   el camino de readerVerdictW_iff_of_pinDoomed)

theorem readerVerdictW_iff_of_pairHelly (hStart …) (hPin : … → PairHelly (cleanPair (filterWeak g …))) …
```

Nota honesta: `SegGood` tras la vuelta **no** es todavía `SegExact` sin más. En `PinDoomed`, `SegGood`
llegaba al punto fijo, y allí `pstateG_of_reader` daba `SegExact`. Hay que ver si ese paso sirve para
la salida de la primera vuelta o si la escalera pasa por el punto fijo. Es la primera cosa que
comprobar en B6, antes de escribir código.

## Fase C — el ejecutable IO y las sondas

### C1. Sonda `pairhelly` (antes de B, justo después de A4)

En `Probes/RowDegree.lean`, con el modelo **sin cambiar** (se aplica `cleanPair` a mano dentro de la
sonda): en los 86 pines, tras `cleanPair X`, ¿algún tramo sin entrada común? ¿`PairOk` se cumple? ¿y
tras la primera vuelta, `SegExact`? Si `PairHelly` da 0 fallos, se sigue con B. Si no, se para aquí.

### C2. El ejecutable (`GraphPath.lean`)

`pair_consistency_after_clean!` en IO, en dos fases como en Julia, llamada desde
`make_review_owners!` justo después de `clean_invalid_nodes!`.

### C3. Diferencial

`exec-diff` (500 casos contra el oráculo exhaustivo) y `diffTest` con sus tres bandas. `sym2` adaptado:
el modelo con y sin regla, mismos estados en los envíos y los pines.

---

## Orden de trabajo

1. **A0–A1** y **C1**: medir primero, sin cambiar la máquina.
2. **A2–A4** (Julia) si C1 da 0 fallos.
3. **B0–B1**, después **B2–B4** (la parte más larga: 26 + 20 lemas, la mayoría de una línea, unos siete
   con contenido), después **B5–B6**.
4. **C2–C3**.
5. Informe cuando lo pidas.
