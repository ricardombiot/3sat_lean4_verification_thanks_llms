# Plan: un review simétrico, en Julia Improves y después en Lean 4

Informe de referencia: `docs/bitacora/verificacion_inseguridad_autor_v182.md`, §3.
Rama de trabajo: `clean-two-phase` (o una nueva que salga de ella).

## Principio

Cuando el review quita `r` de la tabla de `x`, afirma *ninguna solución pasa a la vez por `x` y por
`r`*. La frase es simétrica; la máquina solo la escribe en un lado. **Cada vez que se borra un owner de
la tabla de un nodo, si el otro sigue vivo, se borra también el espejo.**

Solo se toma la idea de `SymReview.lean`; aquel modelo no representaba bien el review y no se reutiliza.

## Cómo se decide (antes de nada)

Igual que con `cleanInvalid₂`: detrás de un interruptor, medir, y adoptar solo si

1. los **veredictos** coinciden en todo el corpus (obligatorio);
2. los **estados finales** coinciden, o las diferencias se explican y tú las aceptas (el espejo borra
   más, así que puede cambiar estados intermedios del lector);
3. el **coste** es comparable (el espejo puede obligar a revisar otra vez nodos ya procesados).

Hay un riesgo concreto que medir desde el principio. Hoy las pasadas **no eliminan nodos** (medido, y
en eso se apoyan `PassCtx`, `PassSons` y `OwnLive`). Con el espejo, un nodo `m` que pierde a `x` puede
quedarse sin entrada en el paso de `x` y volverse inválido. Si eso pasa a mitad de pasada, el argumento
de «las pasadas no eliminan nodos» deja de valer y hay que rehacerlo.

---

## Fase A — Julia (`julia/improves`)

### A0. Medir la situación actual (sin cambiar la máquina)

Script `test_3sat/measure_symmetry.jl` que, en `test_window` y en los estados pinchados del test de
`cleanInvalid`, cuente:

* pares vivos asimétricos (`w ∈ owners(x)`, `x ∉ owners(w)`) tras cada `review_owners_parents_sons!`,
  `review_owners_sons_parents!`, `clean_invalid_nodes!` y `agressive_consistence_filter!`;
* cuántas veces se dispara la rama «asymmetric» del filtro agresivo;
* **tras UP** (`create_node_from_parents!` + `register_node!`): ¿el nodo nuevo `d` está en la tabla de
  cada owner suyo? (si no, la asimetría nace también en UP y hay que tratarla aquí).

### A1. API de owners

En `PathDocumentOwners`:

```julia
# El mismo corte que intersect!, devolviendo los ids que quita (sin copias).
function intersect_removed!(owners_a, owners_b) :: Vector{PathNodeId}
```

Test: mismo resultado que `intersect!` y la lista devuelta es exactamente la diferencia.

### A2. El espejo

En `graph_path_filter.jl`:

```julia
const SYM_MODE = Ref(:off)   # :off | :on

# x perdió estos owners: cada uno que siga vivo pierde a x.
function mirror_remove!(gpath, x_id, removed)
    for w_id in removed
        node_w = PathCollectionLines.get_node(gpath.table_lines, w_id)
        if node_w !== nothing
            PathDocumentNode.remove_owner!(node_w, x_id)
            gpath.review_owners = true
        end
    end
end
```

`w` no se valida en ese momento: si queda inválido lo elimina la purga de la vuelta siguiente, o la
propia pasada cuando lo procese. Lean hará lo mismo, para que Julia y Lean coincidan paso a paso.

### A3. Dónde se llama

| sitio | cambio |
|---|---|
| `review_owners_parents_sons!` | `removed = intersect_removed!(...)`; si `SYM_MODE[] == :on`, `mirror_remove!(gpath, path_node.id, removed)` |
| `review_owners_sons_parents!` | lo mismo |
| `clean_invalid_nodes_two_phase!`, fase 2 | **en principio no hace falta** (ver nota); se deja un contador que lo compruebe |
| `agressive_consistence_filter!`, rama «inconsistent» | ya es simétrica |
| `agressive_consistence_filter!`, rama «asymmetric» | sin cambio; contador (debería quedar en 0 con `:on`) |
| UP | según lo que diga A0 |

**Nota sobre la fase 2 del corte.** Tras la purga, todo nodo vivo está en la global: un nodo fuera de
la global pierde su propio id al cortarse, y como en su paso solo se posee a sí mismo (`OOS`), su tabla
queda vacía en ese paso y la purga lo elimina. Así que el corte de la fase 2 solo quita ids muertos y no
hay espejo que escribir. Esto se demuestra en Lean (B3) y aquí se comprueba con el contador.

### A4. Tests

`test/graph_path/test_symmetric_review.jl`, en `runtests`:

* en los estados pinchados (reutiliza `pinned_states`) y en `test_window`: tras cada review con `:on`,
  **simetría entre nodos vivos**;
* la rama «asymmetric» del filtro agresivo no se dispara;
* contador de **nodos eliminados en las pasadas** (el riesgo de arriba);
* idempotencia: aplicar el review otra vez no cambia nada.

### A5. Comparación diferencial

Extender `test_3sat/compare_clean.jl` (o uno nuevo `compare_sym.jl`) para `SYM_MODE`: en `test_window`
y `test_3sat`, veredicto, verdad del exhaustivo, soluciones del lector comprobadas con `CheckerCnf`,
estados finales, vueltas del review y tiempo, `:off` frente a `:on`.

### A6. Adopción

Si se cumplen los criterios de arriba: `SYM_MODE` a `:on` por defecto, commit, y el test entra en
`runtests`.

---

## Fase B — Lean 4

### B0. La sonda en el modelo (antes de tocar `GPathM`)

Sonda `sym2` en `Probes/RowDegree.lean`, con una copia local de `reviewNode` con espejo (como hicimos
con `reviewAggSeq`). En `dos_de_tres` y las semillas 1 y 7: estados finales y veredictos frente a la
máquina actual, asimetrías a mitad de pasada (0), nodos eliminados en las pasadas, vueltas, UP
simétrico, y **que coincida con Julia `:on`** en las instancias comunes.

### B1. Definiciones, en `GPathM.lean`

```lean
/-- `x` perdió los owners `removed`: cada nodo vivo de esa lista pierde a `x`. -/
def mirrorDrop (g : GPathM) (x : PathNodeId) (removed : List PathNodeId) : GPathM :=
  { g with nodes := g.nodes.map (fun m =>
      if removed.contains m.id then { m with owners := m.owners.filter (· != x) } else m) }
```

`reviewNode` pasa a: cortar la tabla de `x` → `mirrorDrop` con los ids quitados → `unlinkIncompatible`
(que ya quita los enlaces entre `x` y los que deja fuera) → validez de `x`. El orden es el de Julia A3.
`cleanInvalid₂` no cambia (nota de A3).

### B2. Teoremas afectados

Inventario con `Probes/DepsClosure.lean` y búsqueda: **88 teoremas** desdoblan `reviewNode`; **17**
están en el cierre de la escalera (`readerVerdictW_iff_of_readerSegGood`), marcados con ★.

El espejo solo **quita entradas de tablas** (nunca añade, nunca toca ids, padres ni hijos), así que la
mayoría se repara con un lema de forma para `mirrorDrop`.

| fichero | teoremas | qué cambia |
|---|---|---|
| `Pruned` | `pruned_reviewNode` ★, `pruned_reviewLine` | `pruned_mirrorDrop` (solo encoge tablas) |
| `Fuel` | `measure_reviewNode_le` ★, `reviewNode_eq_self` ★, `reviewNode_owners_fixed` ★, `reviewLine_*`, `review_owners_coherent_*` | medida: el espejo no la sube; `eq_self`: si la medida no baja, el espejo no quitó nada |
| `NodeIds`, `GownersNodes`, `Parents` | `ids_` ★, `GN_` ★, `PN_reviewNode` ★ (+ `reviewLine`) | nada de fondo: el espejo no toca ids, global ni padres |
| `Sons` | `SMP_` ★, `PMS_` ★, `SN_` ★, `SAbove_reviewNode` (+ `reviewLine`) | no toca enlaces; el `unlinkIncompatible` de después ya es el que había |
| `SelfOwn` | `OOS_reviewNode` ★ | sale de `Pruned` |
| `Coherence` | `ChainSound_reviewNode` ★, `ChainSound_foldl_reviewNode` ★, `reviewNode_current_step` ★ | el espejo solo quita `x` de tablas de nodos que `x` dejó fuera, y dos nodos de una cadena sana se poseen entre sí: ninguno se deja fuera |
| `AnchoredSurvive` | `AOk_reviewNode` ★, `AOk_reviewLine_*` | igual: `R` es simétrica y los `R`-owners se conservan |
| `Survive` | `Closed_`, `Woven_`, `WOk_reviewNode_*`, `WOk_reviewLine_*` | igual, con «todo miembro posee a todo miembro» |
| `Fabric` | `FOk_reviewNode`, `FOk_reviewLine_*` | igual, con la tabla `T` simétrica |
| `PinAliveChain` | `Anchored_reviewNode_other`, `reviewNode_keep`, `Anchored_reviewNode_all` | revisar: hablan de tablas de nodos distintos de `x` |
| `SegReview` | `reviewNode_owners`, `segGood_reviewNode_parents/sons` | **de fondo**: otras tablas ya no son constantes |
| `PassCtx` (18), `PassSons` (8), `PassPlain` (7) | `kept_*`, `node_after`, `kept_form`, `segGoodL_*`, `i1L_*`, `i1sL_*`, `pLive_*`, `sLive_*`, `selfL_*`, `ownLive_*`, `pstate*` | **de fondo**: `node_after` cambia (un `m ≠ x` puede perder a `x`); `SegGoodL`/`SegGood` hay que volver a mirarlo: un tramo que contenga a `m` pierde la entrada `x` (pero entonces `m` y `x` ya no se poseen, así que no forman tramo con ella: a demostrar) |
| `CompatLoss` | `owners_other_reviewNode`, `owners_after_sub`, `owners_self_after`, `sep_of_drop_*` | `owners_other_reviewNode` pasa a «las otras tablas solo pierden a `x`» |

Los de fondo están todos fuera del cierre de la escalera salvo por lo que la escalera use de
`PassPlain` cuando se ensamble; se pueden rehacer después de lo marcado ★.

### B3. Teoremas nuevos

| teorema | enunciado | papel |
|---|---|---|
| `pruned_mirrorDrop`, `measure_mirrorDrop_le`, `mirrorDrop_eq_self` | forma del espejo | reparar B2 |
| `live_in_gowners_purge` | tras la purga, en un grafo válido, todo nodo vivo está en la global | justifica que el corte de `cleanInvalid₂` no necesita espejo |
| `OwnSymmetric_cleanInvalid₂` | la purga y el corte conservan la simetría entre nodos vivos | entrada de la vuelta |
| `OwnSymmetric_filterRequire` | un pin no toca tablas | entrada tras un pin |
| `OwnSymmetric_up` (si A0/B0 lo confirman) | UP deja tablas simétricas | envíos |
| **`OwnSymmetric_reviewNode`** | si hay simetría antes, `reviewNode` (con espejo) la conserva | **el invariante nuevo** |
| `OwnSymmetric_reviewPass`, `OwnSymmetric_review`, `OwnSymmetric_reviewAgg` | lo mismo por pasada, vuelta y review | |
| `LocSym_of_ownSymmetric`, `LocSymUp_of_ownSymmetric` | la simetría local se sigue de la global (una línea) | **quita `LocSymStable` y `LocSymStableS`** |
| `pstateG_reviewPass'` | `PStateG` a la salida de `cleanInvalid₂` ⇒ `PStateG` tras la vuelta, **sin hipótesis** | las pasadas, cerradas |
| `lost_parents_sym`, `lost_sons_sym` | `lost_parents`/`lost_sons` con la simetría ya como invariante | tu postulado en el paso de los vecinos, siempre |
| **`commonLoss_round`** (S1′) | en una vuelta, una entrada común viva que sale de una tabla del tramo queda separada de algún nodo del tramo en algún paso | S1′ para la vuelta entera |
| `aggPair_asym_never` | con simetría, la rama «asymmetric» de `aggPair` no se dispara | simplifica `AggressiveReview` / `AggFixpoint` |

### B4. El ejecutable y el espejo con Julia

`GraphPath.lean` (el ejecutable Lean) sigue limpiando en secuencial: pasarlo a dos fases y añadir el
espejo; `MirrorTest` / `ImprovesDiff` frente a Julia `:on`.

### B5. Cierre

`lake build AbsSat` verde, `DepsClosure` sobre la escalera, axiomas (`propext`, `Quot.sound`), y
volver a pasar `clean2`, `roundseg` y `midsym` (esta última debería dar 0 asimetrías).

---

## Orden y ladrillos

| # | ladrillo | depende de |
|---|---|---|
| 1 | A0: medir asimetrías actuales y UP en Julia | — |
| 2 | A1–A2: `intersect_removed!`, `mirror_remove!`, interruptor | 1 |
| 3 | A3–A4: llamadas y tests (simetría, rama asimétrica, eliminaciones en pasadas) | 2 |
| 4 | A5: comparación diferencial `:off` / `:on` | 3 |
| 5 | B0: sonda `sym2` en el modelo, y que coincida con Julia | 4 |
| — | **decisión**: adoptar o no (criterios de arriba) | 4, 5 |
| 6 | A6: `:on` por defecto en Julia | decisión |
| 7 | B1 + lemas de forma de `mirrorDrop` | decisión |
| 8 | B2 ★ (el cierre de la escalera) y cambio de `reviewNode` | 7 |
| 9 | B3: `OwnSymmetric_*`, `LocSym_of_ownSymmetric`, `pstateG_reviewPass'` | 8 |
| 10 | B2 de fondo (`PassCtx`, `PassSons`, `SegReview`, `CompatLoss`, `PinAliveChain`) | 8 |
| 11 | B3: `commonLoss_round`, `aggPair_asym_never` | 9, 10 |
| 12 | B4–B5 | 8 |

## Qué no resuelve

La parte colectiva: que alguna entrada común de un tramo siga siendo compatible con **todo** el tramo
tras cada vuelta. El review simétrico deja S1′ demostrable y las pasadas sin hipótesis; la pregunta de
fondo sigue siendo esa.
