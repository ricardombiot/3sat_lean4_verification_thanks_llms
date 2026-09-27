# Verificación para el Autor v196: una etiqueta de clave de un nivel para cerrar M1b

Ricardo, este informe es una propuesta de cambio de la máquina, y la escribo porque me la pediste. Tú decides si
entra. Antes explico por qué la propongo: qué he demostrado de M1b, qué he medido y dónde se atasca la prueba sin
cambios. El detalle técnico está en `docs/context/escalera_reader.md` §4.2ο.2.

**La conclusión, por adelantado.**
* El lector decide `φ` bajo `M1aAll` y `M1bLowOwn` en cada join (`M1Parts.readerVerdictW_iff_of_own`). Está
  **demostrado**, con 0 `sorry` y solo `[propext, Quot.sound]`. `M1aAll` lo lleva otra sesión, por `KeyTri₁` y
  `KeyExact`.
* `M1bLowOwn` dice que, fijada la clave `k` en el estado unido `J`, las tablas de las filas de abajo son tablas de la
  pieza `k`. **No falla en nada de lo medido, pero no he conseguido demostrarlo.**
* Las dos formas locales que lo darían, `KTri` y `KTriK`, son **falsas**. La forma que no falla, **`KFix`**, es un
  punto fijo: la regla de parejas relativa a la clave. `KFix ⇒ M1bLowOwn` está **demostrado**. `KFix` está **medido**
  sin fallos en 24,7 M enlaces, pero demostrarlo pide una inducción sobre la historia de la máquina.
* **La propuesta:** en el join, cada entrada de las filas de abajo anota de qué clave viene, y solo durante una línea.
  Con eso `M1bLowOwn` es inmediato y M1 se reduce a `M1aAll`. Cuesta como mucho ×2 en memoria durante una línea, y
  cambia la conducta de la máquina solo cuando un filtro fija un nodo del paso de las claves.

Cada afirmación lleva su estado: **demostrado** (teorema Lean), **medido** (sonda), **deducido** (argumento sin
formalizar), **falso** (contraejemplo), **propuesto** o **abierto**.

Commits de esta sesión: `5a79e8a`, `06b91fc`, `65bb769` y `c3089d5`, en la rama `lean_improves_bin`.

---

## 1. Dónde estamos: M1 partido en dos

La inducción del lector (§4.2ο.1) solo pide **M1** en cada join: si el estado unido `J`, fijado en unos pins `R`, es
válido, alguna pieza fijada igual es válida. `J` es la unión de piezas `P_k = up(filterAll X_k (reqOf d)) d`, una por
cada clave `k` (el nodo de mapa del paso `n` de su fuente `X_k`). Las filas de los pasos `n` y `n+1` son **puras**:
cada nodo viene de una sola pieza. Por debajo de `n`, las tablas son uniones.

M1 se reparte en dos (`M1Parts.lean`), **demostrado**:
* **`M1aAll`**: fijar cualquier clave viva no deja `J` inválido.
* **`M1bLowOwn`**: con la clave `k` fijada, toda entrada de un nodo por debajo de `n` es entrada de ese nodo en `P_k`.
  Es exactamente lo que mide la sonda (M1b-entradas).
* `m1bLow_of_own`: los padres y los hijos no hace falta pedirlos. Salen de los owners, porque en la pieza una entrada
  del paso de al lado es padre o hijo (`parent_of_owner`, `son_of_owner`).

Las dos están **medidas sin fallos** (`m1split_probe.jl`, `m1aall_probe.jl`).

## 2. `M1bLowOwn`: lo que no funciona

La idea obvia es esta. En `J` fijado en `k :: R`, solo vive `k` en el paso `n`. Si `p` posee `v`, la regla de parejas
les da una entrada común en el paso `n`, y es un nodo de `k`. Como la fila de `k` es pura, `p` y `v` deberían poseerse
en `P_k`. Falta el lado p–v, que es otra vez el hecho de tres miembros.

Lo he intentado de dos formas, sobre `J` fijado en `R` y sin fijar la clave (`M1bOwn.lean`, `ktri_probe.jl`):

| enunciado | qué pide | fallos (R vacío / R no vacío) |
|---|---|---|
| `KTri` | p–v con un nodo común `x` del paso `n` ⇒ p–v en `P_{x.id}` | **716 / 10.530** en `clause_mix`; también en `clause_mix_sep` y `random_small` |
| `KTriK` | además, en cada paso, un testigo común que posee un nodo de `k` ⇒ p–v en `P_k` | **8 / 56** en `clause_mix`; 32 / 544 en `clause_mix_sep`; 0 en `random_small` |

`KTriK ⇒ M1bLowOwn` está **demostrado**, pero `KTriK` es **falso**. Los fallos de `KTri` son los mismos enlaces que
rompían `KeyTri`: parejas que se poseen pero cuyos testigos de algún paso no posee la clave.

### 2.1 Dónde mueren esos enlaces

Con `keycut_trace.jl` rehice el review de `J` fijado en `k :: R` operación por operación en los 704 casos donde
`KTriK` falla. Todos caen igual (**medido**):
1. Vuelta 1 del review, dentro de la regla de parejas.
2. En su ronda 1 se deshacen **otras** parejas (8 en `clause_mix`, 24 o 32 en `clause_mix_sep`), y la purga se lleva
   sus nodos.
3. Con eso p–v pierde sus testigos en algún paso, y en la ronda 2 la propia p–v es una pareja mala.

No intervienen el corte contra padres o hijos ni los enlaces caducados. Lo que corta es la **cascada de la regla de
parejas relativa a la clave**.

### 2.2 `KFix`: la forma que no falla

Un conjunto de enlaces de `J` fijado en `R` es **cerrado para `k`** (`KClosed`) si cada enlace (a, b) tiene, en cada
paso, un testigo `r` que posee un nodo de `k`, con (a, r) y (b, r) también en el conjunto. **`KFix`**: todo enlace de
un conjunto cerrado para `k` que sale de un nodo por debajo de `n` es un enlace de `P_k`. `KTriK` es su primera ronda.

* **`m1bLowOwn_of_kFix`**: con `k` fijada, todos los enlaces del estado forman un conjunto cerrado.
  **`readerVerdictW_iff_of_kFix`**: el lector decide bajo `M1aAll` y `KFix`. **Demostrado.**
* `kfix_probe.jl` calcula el mayor conjunto cerrado por iteración. En `clause_mix`, `clause_mix_sep` y 6 de
  `random_small`: 24.560 pares (estado, clave), **24,7 M enlaces** comprobados, **0 fallos**. **Medido.**

`KFix` es la forma coinductiva de «la unión de piezas es exacta por debajo de la clave». No depende del review del
estado fijado, pero tampoco sale de la estructura de `J` en un paso. Hay que seguirlo a lo largo de las líneas: `X_k`
es a su vez una unión de piezas de la línea anterior. **Abierto.**

## 3. La propuesta: etiqueta de clave de un nivel

**Propuesto.** El problema de `M1bLowOwn` es que el join olvida de qué pieza viene cada entrada de las filas de
abajo, y al fijar la clave la review tiene que recuperarlo por cascada. Si el join lo recuerda durante una línea, fijar
la clave es simplemente quedarse con las entradas de esa pieza.

### 3.1 La regla

* **En el UP:** la pieza entera es de una sola clave, el nodo de mapa de su fuente. Se anota solo esa clave (etiqueta
  implícita, coste O(1)). Las etiquetas del nivel anterior se descartan, así que nunca hay más de un nivel.
* **En el join:** cada entrada (p, v) con `p` por debajo de la fila de claves guarda el conjunto de claves de las
  piezas que la traen. El join une esos conjuntos entrada a entrada.
* **Al fijar la clave `k`** (`filter_require!` en el paso de las claves): además de quitar los otros nodos del paso,
  cada nodo de abajo se queda solo con las entradas etiquetadas `k`. Un nodo que no está en la pieza `k` pierde su
  propia entrada y lo purga la review.
* **La review no cambia.** Las etiquetas de entradas que la review quita quedan huérfanas y desaparecen en el
  siguiente UP.
* Solo se etiquetan owners. Los enlaces que se quedan sin posesión mutua los corta `prune_stale_links!`, como ya hace.

**No pierde soluciones (deducido).** Una solución que pasa por `k` en el paso `n` es un camino de `P_k`, así que
todas sus entradas llevan la etiqueta `k`.

### 3.2 La implementación en Julia

Un campo nuevo en `GPath`, un fichero `graph_path_key.jl` con cuatro funciones, tres enganches en código existente y
un interruptor `KEY_MODE` (`:on`/`:off`), como `PAIR_MODE` y `LINK_MODE`, para medir con y sin la regla.

**El dato** (`graph_path.jl`; `new()` en `graph_path_constructor.jl` pasa `nothing`):

```julia
# Etiqueta de clave de un nivel: de qué pieza viene cada entrada de las filas bajo la fila de claves.
mutable struct KeyTags
    key_step :: Step                         # paso de las claves
    single   :: Union{NodeId, Nothing}       # pieza sin unir: toda entrada es de esta clave (etiqueta implícita)
    tags     :: Dict{Tuple{PathNodeId, PathNodeId}, SetNodesId}   # (p, v) => claves; solo tras un join
end

mutable struct GPath
    # ... campos actuales ...
    key_tags :: Union{KeyTags, Nothing}      # `nothing` en la raíz y con KEY_MODE = :off
end

const KEY_MODE = Ref(:on)
```

La fila de claves y la cima no llevan etiqueta porque son puras: la clave de un nodo de la fila de claves es su `id`,
y la de la cima es su `parent_id`.

**Las funciones** (`graph_path_key.jl`):

```julia
# Tras el UP: la pieza entera es de una sola clave. Descarta las etiquetas del nivel anterior.
function init_key_tags!(gpath :: GPath, key :: NodeId)
    KEY_MODE[] == :on || return
    gpath.key_tags = KeyTags(key.step, key, Dict{Tuple{PathNodeId, PathNodeId}, SetNodesId}())
end

# Pasa de etiqueta implícita a explícita: toda entrada (p, v) con p bajo la fila de claves recibe su clave.
function materialize_key_tags!(gpath :: GPath)
    kt = gpath.key_tags
    (kt === nothing || kt.single === nothing) && return
    PathCollectionLines.for_each(gpath.table_lines, function (node)
        node.id.id.step < kt.key_step || return
        for (_, set) in node.owners.table, v in set
            kt.tags[(node.id, v)] = SetNodesId([kt.single])
        end
    end)
    kt.single = nothing
end

# En el join: unión de etiquetas, entrada a entrada, antes de unir las tablas.
function join_key_tags!(gpath :: GPath, other :: GPath)
    (gpath.key_tags === nothing || other.key_tags === nothing) && return
    materialize_key_tags!(gpath)
    ot = deepcopy(other); materialize_key_tags!(ot)
    for (e, ks) in ot.key_tags.tags
        union!(get!(gpath.key_tags.tags, e, SetNodesId()), ks)
    end
end

# Al fijar la clave k: las filas de abajo se quedan solo con las entradas de la pieza k.
function restrict_to_key!(gpath :: GPath, k :: NodeId)
    kt = gpath.key_tags
    (kt === nothing || kt.single !== nothing) && return    # sin join, ya es una sola pieza
    PathCollectionLines.for_each(gpath.table_lines, function (node)
        node.id.id.step < kt.key_step || return
        for (_, set) in node.owners.table, v in collect(set)
            k in Base.get(kt.tags, (node.id, v), SetNodesId()) && continue
            PathDocumentNode.remove_owner!(node, v)
            gpath.review_owners = true
        end
    end)
    gpath.key_tags = KeyTags(kt.key_step, k, empty(kt.tags))   # de aquí en adelante, pieza k
end
```

**Los tres enganches:**

```julia
# graph_path_up.jl, do_up!: la clave es el nodo de mapa de la fuente, antes de que el UP lo cambie
if gpath.is_valid
    key = gpath.map_parent_id
    add_row!(gpath, map_id_node, title, prohibited)
    if gpath.is_valid
        key === nothing || init_key_tags!(gpath, key)        # nuevo
        gpath.current_step += 1
        # ...

# graph_path_join.jl, do_join!
if is_valid_join(gpath, gpath_inmutable)
    join_key_tags!(gpath, gpath_inmutable)                  # nuevo, antes de la unión
    # ...

# graph_path_filter.jl, filter_require!: tras quitar los otros nodos del paso fijado
if gpath.key_tags !== nothing && step_selection == gpath.key_tags.key_step
    restrict_to_key!(gpath, map_node_id_req)                # nuevo
end
check_if_graph_valid!(gpath)
```

### 3.3 Qué cuesta

* **Memoria:** como mucho una etiqueta por clave y entrada, durante una sola línea. En el mapa bin son hasta 2 claves
  por paso, así que como mucho ×2 en las entradas de las filas de abajo.
* **Tiempo:**
  * `materialize_key_tags!` recorre las entradas una vez por join.
  * `restrict_to_key!` las recorre una vez por pin en el paso de las claves.
  * El resto no cambia.
* **Cambio de conducta:** solo cuando un filtro fija un nodo del paso de las claves de un estado unido. Eso pasa en el
  lector y en `filterAll X (reqOf d)` si los requisitos de `d` llegan a ese paso. Ahí la máquina poda más, sin perder
  soluciones (§3.1). Hay que medir cuánto cambian los veredictos, los tamaños y las vueltas de review.
* **Relación con los owners por rama:** es el mismo tipo de idea que descartaste por la compresión. La diferencia es
  que aquí está acotada a un nivel: la etiqueta nunca pasa del siguiente UP, y las tablas siguen unidas como ahora.

### 3.4 Qué gana la prueba

* **`M1bLowOwn` sale inmediato.** `filterRequire J k` deja exactamente las tablas de `P_k`, y la review solo quita.
  Así, `J` fijado en `k :: R` queda por debajo de `P_k` sin argumento de punto fijo, y M1 se reduce a `M1aAll`.
* **Lo que hay que hacer en Lean (deducido, sin empezar):**
  * Añadir las etiquetas a `GPathM`: un campo con las entradas por clave de la línea en curso.
  * Cambiar `filterRequire` en el paso de las claves.
  * Demostrar la **exactitud de las etiquetas**: la etiqueta `k` está en (p, v) si y solo si `v` está en la tabla de
    `p` en `P_k`. Es una inducción sobre `insertPure`/`join`, del mismo tipo que `LineSem.src_pureAdvance`, que ya da
    la dirección «toda entrada viene de alguna pieza».
  * Revisar los lemas que usan `filterRequire` (`Kernel.below_filterRequire`, `Pruned`, `SymMachine`,
    `ReaderAgg.keeps_filterRequire`). El filtro deja de tocar solo los owners globales y pasa a quitar entradas de las
    tablas. Como solo quita, debería seguir siendo una poda, pero hay que comprobarlo lema a lema.
* **Riesgo principal.** La simetría de las tablas (`OwnSymmetric`) tiene que sobrevivir a `restrict_to_key!`. Debería,
  porque (p, v) y (v, p) vienen de la misma pieza y llevan las mismas claves. Pero con las etiquetas implícitas de una
  pieza sin unir hay que cuidar que las dos direcciones se traten igual.

## 4. Qué haría a continuación

Si decides probarla:
1. Implementarla en Julia detrás de `KEY_MODE`, sin tocar nada con `:off`.
2. Medir veredictos, tamaños y vueltas de review con `:on` y `:off` (`compare_*.jl`, `test_3sat`, `test_window`).
3. Repetir `m1split_probe.jl` con `:on`: M1b-entradas debería valer por construcción, y M1a-todas seguir sin fallos.
4. Solo después, portarla a Lean y demostrar la exactitud de las etiquetas.

Si prefieres no tocar la máquina, el camino es demostrar `KFix` por inducción sobre las líneas. No ha fallado en
nada de lo medido, pero no tengo todavía el argumento de historia que lo cierre. Lo más natural es intentar un
`KFix` en la línea `n` que implique el de la línea `n+1`, siguiendo `X_k` como unión de piezas de la línea anterior.

En cualquiera de los dos casos, `M1aAll` sigue abierto por su lado (`KeyTri₁`, `KeyExact`).

---

**Ficheros de esta sesión:**
* `lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean`: `M1bLowOwn`, `m1bLow_of_own`, `piece_pinCtx`, `KeyTri`
  (⚠ falso), `KeyTri₁`, `m1aAll_of_keyTri₁`.
* `lean/improves_bin/AbsSatBin/GraphPath/Model/M1bOwn.lean`: `KTri` y `KTriK` (⚠ falsos), `KClosed`, `KFix`,
  `m1bLowOwn_of_kTriK`, `m1bLowOwn_of_kFix`, `readerVerdictW_iff_of_kFix`.
* Sondas en `julia/improves_bin/test_3sat/probes/`: `keytri_common.jl`, `keytri_probe.jl`, `m1aall_probe.jl`,
  `ktri_probe.jl`, `keycut_trace.jl`, `kfix_probe.jl`.
