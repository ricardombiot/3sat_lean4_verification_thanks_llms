# Verificación para el Autor v196: una etiqueta de clave de un nivel para cerrar M1b, y una comprobación de claves para M1a

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
* **Una segunda regla, independiente (§3.5):** una comprobación de claves en el review de los estados unidos. Cada
  clave viva se fija en una copia, y la que no sobrevive se quita. Da `M1aAll` por construcción. Cuesta hasta ×3 en
  cada review de un estado unido del mapa bin.
* **Formalizado en Lean (§6), y con una corrección de alcance.** Con las dos reglas, M1 vale en el join donde actúan
  (`KeyRules.m1_keyRules`, **demostrado**), y el lema de riesgo también sale (`below_reviewKC`, **demostrado**). Pero
  **las reglas de un nivel no cierran la inducción del lector**: la inducción pide M1 en cada línea con el filtro que
  usa en las fuentes, y ahí las etiquetas de un nivel ya no están. Lo que antes decía este informe («con las dos
  reglas, M1 sale entero y el lector decide») era demasiado fuerte.
* **El riesgo (§3.5):** toda la prueba del lector se apoya en que el review nunca baja de un kernel, y la comprobación
  de claves puede romper ese lema. La revisión del otro agente (§5.2) da un argumento corto para kernels cerrados por
  claves. Sigue sin formalizar: hasta que lo esté, las dos reglas no dan el veredicto del lector.
* **Implementadas y medidas en Julia (§5.1)**, en la rama `julia_key_rules`, apagadas por defecto. En 76 instancias,
  los cuatro modos aciertan todos los veredictos, el lector sin retroceso acierta siempre y las soluciones leídas son
  las mismas. **La comprobación no quita ninguna clave.** Las etiquetas son exactas en las dos direcciones (999.222
  entradas). Coste en tiempo: +55 % cada regla, +121 % las dos.

Cada afirmación lleva su estado: **demostrado** (teorema Lean), **medido** (sonda), **deducido** (argumento sin
formalizar), **falso** (contraejemplo), **propuesto** o **abierto**.

Commits de esta sesión: `5a79e8a`, `06b91fc`, `65bb769` y `c3089d5`, en la rama `lean_improves_bin`; la
implementación en Julia, `aeeb001` y `cac23ff`, en la rama `julia_key_rules`.

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

### 3.5 Segunda regla: comprobación de claves (para `M1aAll`)

**Propuesto.** La etiqueta no ayuda con `M1aAll`. Con ella, `M1aAll` pasa a decir exactamente «si `k` sigue viva en `J`
fijado en `R`, la pieza `k` fijada en `R` es válida», que es lo difícil de M1. El paso queda limpio, pero no
demostrado, porque mientras no se fija `k` el review trabaja sobre las tablas unidas.

**La regla.** Al terminar el review de un estado con dos o más claves vivas en su fila de claves:
1. Para cada clave viva `k`, se hace una copia, se fija `k` en la copia y se hace su review.
2. Si la copia queda inválida, se quita `k` de los owners globales del estado.
3. Si se quitó alguna, se repite el review, y con él la comprobación.

Todas las claves se comprueban contra el mismo estado y se quitan a la vez, en dos fases, como la regla de parejas.
Así el resultado no depende del orden. Solo quita claves, así que termina.

**No pierde soluciones (deducido).** Si fijar `k` deja el estado inválido, ninguna solución pasa por `k`, porque el
review no pierde soluciones. Quitar `k` no quita ninguna.

**No necesita las etiquetas.** Con una sola clave viva, fijarla no cambia nada y la comprobación se salta. Por eso las
piezas recién subidas y los estados de una sola pieza no pagan nada. La fila de claves es la penúltima
(`current_step - 2`), la misma que da `KeyTags.key_step` con la etiqueta.

**Borrador en Julia** (`graph_path_key.jl`, junto a las funciones de §3.2):

```julia
# Comprobación de claves (v196 §3.5): en el punto fijo del review, toda clave viva sobrevive a su pin.
#   :off — el review de siempre.
#   :on  — make_review_owners! llama a key_check! al llegar al punto fijo.
const KEYCHECK_MODE = Ref(:off)
const KEYCHECK_REMOVED = Ref(0)     # claves quitadas (solo para medir)
const KEYCHECK_COPIES  = Ref(0)     # copias revisadas (solo para medir)

key_step(gpath :: GPath) :: Step =
    gpath.key_tags !== nothing ? gpath.key_tags.key_step : gpath.current_step - 2

# Las claves vivas: nodos de mapa de los owners globales en la fila de claves.
function live_keys(gpath :: GPath) :: Vector{NodeId}
    ks = key_step(gpath)
    ks >= 0 || return NodeId[]
    ids = PathDocumentOwners.get(gpath.owners, ks)
    ids === nothing && return NodeId[]
    unique([pid.id for pid in ids])
end

# Fase 1: qué claves no sobreviven a su pin, todas contra el estado de ahora.
# Fase 2: se quitan a la vez. Devuelve true si quitó alguna (hay que repetir el review).
function key_check!(gpath :: GPath) :: Bool
    (KEYCHECK_MODE[] == :on && gpath.is_valid) || return false
    keys = live_keys(gpath)
    length(keys) >= 2 || return false

    dead = NodeId[]
    #! [for] $ O(K) $   K = claves vivas (≤ 2 en el mapa bin)
    for k in keys
        g = deepcopy(gpath)
        KEYCHECK_COPIES[] += 1
        # filter! = filter_require! (con etiquetas, restrict_to_key!) + review. En la copia queda una sola
        # clave viva, así que su propia comprobación no hace nada: no hay recursión.
        filter!(g, SetNodesId([k]))
        g.is_valid || push!(dead, k)
    end

    #! [for] $ O(K*7) $
    for k in dead
        for pid in PathCollectionLines.get_ids_step(gpath.table_lines, k.step)
            pid.id == k && remove_node_owner!(gpath, pid)
        end
        KEYCHECK_REMOVED[] += 1
    end
    isempty(dead) && return false
    gpath.review_owners = true
    return true
end
```

**El enganche** (`graph_path_filter.jl`, `make_review_owners!`, al final de la vuelta):

```julia
        if gpath.review_owners
            make_review_owners!(gpath)
        elseif key_check!(gpath)          # nuevo: punto fijo alcanzado; si cae una clave, otra vuelta
            make_review_owners!(gpath)
        end
```

Si quitar una clave deja el estado inválido (era la única que quedaba), `remove_node_owner!` ya lo marca con
`check_if_graph_valid!`, y la vuelta siguiente no hace nada.

**Qué da (deducido; ⚠ corregido en §6.2: esto vale solo en el join donde actúan las reglas, no en la inducción entera):**
* **`M1aAll` por construcción.** En el punto fijo del review, toda clave viva sobrevive a su pin: si no, la
  comprobación la habría quitado. Falta el lema de que el review de `J` fijado en `k :: R` y el de la copia coinciden
  en validez. La copia fija `R` primero y `k` después, y `filterAll` los fija en el otro orden. El puente es el de
  siempre: la copia es un kernel válido por debajo de `J` que respeta `k :: R` (`isValid_filterAll_of_kernel`).
* **Con la etiqueta, M1 entero.**
  * Por la comprobación de claves, alguna clave viva `k` deja válido `J` fijado en `k :: R`.
  * Por la etiqueta, ese estado queda por debajo de la pieza `k`.
  * Por `isValid_filterAll_of_kernel`, la pieza fijada en `R` es válida.

  M2w, M3w y la inducción `lExt_line` están demostrados **para la máquina actual**. Con las dos reglas, el lector
  decidiría `φ` sin hipótesis abiertas **si** esos lemas se trasladan a la máquina nueva. Eso depende del riesgo que
  sigue: `below_review` con la comprobación de claves. Quedarían además el trabajo de §3.4 (portar las reglas y
  demostrar la exactitud de las etiquetas), el lema del orden de los pins y volver a demostrar que la máquina no
  pierde soluciones (`completeness_pure`).
* **Sin la etiqueta**, la comprobación sola da `M1aAll`, y M1 queda en `M1bLowOwn` (vía `KFix`).

**Qué cuesta:**
* Cada punto fijo del review de un estado con K ≥ 2 claves vivas añade K copias con su review. En el mapa bin, K ≤ 2:
  hasta ×3 por review de un estado unido.
* Cada clave quitada añade otra vuelta, como mucho K por estado.
* Las piezas y los estados de una clave no pagan nada.

**Qué cambia en la conducta:**
* En la máquina actúa en `filterAll X (reqOf d)` cuando `X` es un estado unido, y en el lector.
* Sin pins no debería dispararse (deducido): `sendTo` solo guarda piezas válidas, y en el estado unido sin pins cada
  clave conserva su pieza.

**El riesgo: el review nuevo podría bajar de un kernel.** Toda la cadena demostrada del lector se apoya en que el review
nunca baja de un kernel (`Kernel.below_review`, y por él `isValid_filterAll_of_kernel`). Lo usan M3w, `lExt_succ`,
`fExt_of_kExt` y `m1_of_parts`. La comprobación de claves puede romper ese lema:
* Un kernel válido con dos claves vivas puede tener las dos claves muriendo al fijarlas una a una. Es justo la unión
  no exacta de piezas que M1 intenta excluir.
* Si eso pasa, el review nuevo quita claves que el kernel conserva, y los lemas anteriores dejan de valer tal como
  están.

**La salida probable (propuesta, sin intentar): kernels cerrados por claves.** Un kernel es cerrado por claves si cada
clave viva sobrevive a su pin. Habría que demostrar `below_review` solo para ellos:
* Los estados que produce el review nuevo lo son por construcción.
* Los kernels que usa la prueba de M1 están por debajo de una sola pieza, con una sola clave en la fila de claves, así
  que la comprobación no actúa sobre ellos.
* El caso delicado son los estados del lector con dos claves vivas. Ahí hay que demostrar que un kernel cerrado por
  claves por debajo de `g` hace que `g` fijado en `k` sea válido. Parece salir por inducción sobre el fuel del review.

**Este es el lema del que depende todo.** Si no sale, las dos reglas no cierran el lector, aunque en Julia funcionen.

**Cómo leerla.** Es una anticipación de un paso sobre la fila de claves: la máquina hace ella misma la prueba que ahora
hace el lector con cada pin. El coste sigue siendo polinómico, pero es un cambio de diseño y te toca valorarlo. Hay dos
maneras de verla:
* Como una regla del review más, de la familia de la regla de parejas: quita lo que ninguna solución puede usar.
* Como una forma de trasladar al review la dificultad del lector. `M1aAll` deja de ser un teorema sobre la máquina de
  ahora y pasa a ser una propiedad de diseño de la máquina nueva.

Las dos lecturas son correctas. La segunda es la que hay que tener presente al decidir.

## 4. Qué haría a continuación

Si decides probarlas:
1. ~~Implementarlas en Julia detrás de `KEY_MODE` y `KEYCHECK_MODE`.~~ **Hecho** (§5.1).
2. ~~Medir veredictos, tamaños, vueltas de review y los contadores.~~ **Hecho** en 76 instancias (§5.1). Falta el
   corpus grande de `test_window` y `test_3sat/output*`.
3. ~~Comprobar M1b-entradas con las dos reglas.~~ **Hecho** (§5.1, 24.501 sin fallos).
4. En Lean, **primero el lema de riesgo**, con el argumento de §5.2: `below_review` con la comprobación de claves, sobre kernels cerrados por
   claves. Si no sale, lo demás no vale la pena.
5. Después, portar las etiquetas y `filterRequire`, demostrar la exactitud de las etiquetas, el lema del orden de los
   pins y `completeness_pure` con las reglas nuevas.

Si prefieres no tocar la máquina, el camino es demostrar `KFix` por inducción sobre las líneas. No ha fallado en
nada de lo medido, pero no tengo todavía el argumento de historia que lo cierre. Lo más natural es intentar un
`KFix` en la línea `n` que implique el de la línea `n+1`, siguiendo `X_k` como unión de piezas de la línea anterior.

Sin la comprobación de claves, `M1aAll` sigue abierto por su lado (`KeyTri₁`, `KeyExact`). La otra alternativa sin
cambios es `PairExact` con pins, que da M1 entero (§5.2, punto 3).

## 5. La implementación y la revisión

### 5.1 Medido en Julia (rama `julia_key_rules`)

El código de §3.2 y §3.5 está en `julia/improves_bin/src/graph_path/graph_path_key.jl`, con los enganches en
`do_up!`, `do_join!`, `filter_require!` y `make_review_owners!`. Las dos reglas están apagadas por defecto
(`KEY_MODE`, `KEYCHECK_MODE`), así que con `:off` la máquina es la de siempre. El lector sin retroceso fija sus pins
con `GraphPath.filter!`, así que las reglas también actúan en él.

**Diferencial** (`test_3sat/compare_key.jl`). 76 instancias (ejemplos, `test_window`, `crafted` y `random_small` del
proyecto Lean), mapa bin, cuatro modos:

| modo | veredictos | lector sin retroceso | tiempo | vueltas de review | pico de nodos | actividad de las reglas |
|---|---|---|---|---|---|---|
| ninguna | 76 / 76 | 76 bien | 193,6 s | 15.088 | 314 | — |
| etiqueta | 76 / 76 | 76 bien | 299,3 s | 15.088 | 314 | 4.019 joins etiquetados; 4 fijaciones de clave en la máquina (740 entradas cortadas) |
| comprobación | 76 / 76 | 76 bien | 302,1 s | 29.948 | 314 | 7.430 copias; **0 claves quitadas** |
| las dos | 76 / 76 | 76 bien | 427,2 s | 29.948 | 314 | 7.434 fijaciones (casi todas en las copias), 8,7 M entradas cortadas; 0 claves quitadas |

* Todos los veredictos coinciden con el exhaustivo, y el lector exponencial lee **las mismas soluciones** en los cuatro
  modos. Una instancia (`simple_v3_c2`) se salta porque el exhaustivo no la acepta.
* La etiqueta sola solo actúa dentro de la máquina en dos instancias (`v5_c20_i2`, `v5_c20_i4`): un filtro de
  requisito llega a la fila de claves y corta 370 entradas. No cambia ni el veredicto ni el pico. Es el cambio de
  conducta de §3.3, y es pequeño.
* Las vueltas de review se duplican con la comprobación porque el contador incluye las copias.

**Exactitud de las etiquetas** (`test_3sat/probes/keytags_probe.jl`, con las dos reglas; `clause_mix`,
`clause_mix_sep` y 6 de `random_small`). Toda entrada (p, v) de un nodo por debajo de la fila de claves y toda clave k
cumplen «etiqueta k ⇔ v está en la tabla de p en `P_k`»: **999.222 entradas, 0 fallos**. Con las dos reglas,
M1b-entradas vale en los 24.501 estados fijados medidos, como debía, por construcción.

**Lectura.** Las dos reglas no cambian nada de lo que la máquina decide en este corpus, y la comprobación de claves no
llega a actuar nunca. Es coherente con que `M1aAll` no fallara en ninguna sonda. Eso tiene dos caras:
* En la práctica, la comprobación es una red de seguridad que no cuesta ninguna solución ni ningún veredicto; solo
  tiempo.
* En la prueba, justo por eso, «la máquina nueva decide» solo dice algo de la máquina de siempre si se demuestra que
  la comprobación nunca actúa. Y eso es `M1aAll` otra vez.

### 5.2 La revisión del otro agente

Otra sesión (la que lleva `KeyTri₁`, `KeyExact` y `KeyCone`) revisó este informe. Recojo sus cuatro puntos con mi
valoración.

**1. El riesgo de `below_review` es menor de lo que dice §3.5.** Su argumento: sea h un kernel cerrado por claves por
debajo del estado actual g′ del review, y k una clave viva de h.
* h fijado en k es un kernel válido (`kernel_of_review`), por debajo de g′ y que respeta k.
* Por el `below_review` actual, g′ fijado en k es válido, así que la comprobación nunca quita k.
* La copia tiene una sola clave viva, así que en ella el review nuevo es el de siempre, sin recursión.
* Las claves que sí se quitan no están en h, así que `Below g′ h` se conserva.

**De acuerdo; es más corto que mi propuesta de inducción sobre el fuel.** Añado una precisión: el argumento hay que
aplicarlo a cada kernel que llega a `isValid_filterAll_of_kernel`, y comprobar que tiene una sola clave o es cerrado
por claves.
* En la ruta de M1 creo que todos tienen una sola clave en su fila de claves: las piezas, J fijado en k y los de
  `lExt_succ`, que quedan por debajo de una pieza. Eso incluye M3w, cuyo kernel está por debajo de la fuente X, un
  estado unido.
* Los de `restrictPin` en un paso cualquiera pueden tener dos claves, pero esa ruta (`KeyTri`, `TriPin`) es la que
  sustituye la comprobación.

**2. Basta una dirección de la exactitud de las etiquetas.** «Etiqueta k en (p, v) ⇒ v está en la tabla de p en
`P_k`» basta para `M1bLowOwn`. **De acuerdo, con una precisión:** la dirección contraria («entrada de `P_k` ⇒ lleva la
etiqueta k») la necesita `completeness_pure` con las reglas nuevas, porque asegura que fijar la clave no quita
entradas de la pieza y por tanto no pierde soluciones. Las dos salen de la construcción del join. En Julia están
medidas las dos (§5.1).

**3. Una alternativa sin tocar la máquina: `PairExact` con pins.** Todo enlace de J fijado en R está en una cadena que
respeta R. Lo midió en 5,4 M enlaces sin fallos. Implica `CertPin`, y con ello M1 entero (`m1_of_certPin`). **De
acuerdo en citarlo**, con el mismo estado que `KFix`: medido y abierto.
* La ventaja: es un solo enunciado, y es un invariante sobre la máquina, no sobre el lector, así que podría romper el
  círculo de §4.2ο.2 (M1 ⇐ `CertPin` ⇐ `LExt` de J ⇐ M1).
* La reserva: es del tipo de enunciado semántico que más ha costado. `CertClique` y `FCert` de estados de línea
  resultaron falsos, aunque aquellos eran de tríos, no de enlaces.

**4. La lectura de diseño es la correcta.** Con la comprobación, el mérito pasa a ser «esta máquina, con esta regla,
decide», no «la máquina de siempre decide». De acuerdo. Su propuesta de medir `KEYCHECK_REMOVED` ya tiene respuesta:
0 en todo el corpus (§5.1).

## 6. La formalización en Lean, y lo que las reglas no dan

### 6.1 Demostrado (`KeyRules.lean`, solo `[propext, Quot.sound]`, 0 `sorry`)

Las dos reglas están en el modelo de listas como operaciones nuevas, sin tocar la máquina ni el review de siempre.
* **La etiqueta** es `restrictTo g P`: cada tabla se queda con lo que la pieza `P` tiene para ese nodo. Como las
  etiquetas de Julia son exactas (§5.1), el modelo toma como etiqueta la pertenencia a la tabla de la pieza, dada por
  un mapa de claves a piezas (`pieceOf`). Las filas de la clave y de la cima son puras, así que restringirlas también
  no cambia lo que sobrevive al review.
* **La comprobación** es `reviewKC`: el review hasta su punto fijo; después se quitan a la vez las claves vivas cuyo pin
  con etiqueta deja inválida la copia (`deadKeys`, `dropKeys`), y se repite. El modelo comprueba también una sola clave
  viva; Julia se alineó con eso (commit `98923f0`, rama `julia_key_rules`), porque con tablas mezcladas una sola clave
  puede morir al aplicar su etiqueta.
* **`filterKC`**: pins, etiquetas de los pins de la fila de claves y `reviewKC`.

Teoremas:
* **`m1_keyRules`: M1 donde actúan las reglas.** En un estado unido de la línea `n+1`, si `filterKC` deja válidos los
  pins `ps`, alguna pieza es válida con el filtro de siempre y los mismos pins. Tres pasos:
  1. `kc_spec`: en una salida válida de `reviewKC` ninguna clave viva muere al fijarla.
  2. `below_piece`: fijar una clave con su etiqueta y revisar da un kernel válido por debajo de su pieza. Es
     `M1bLowOwn`, ahora por construcción.
  3. `isValid_filterAll_of_kernel` en la pieza.
* **`below_reviewKC`: el lema de riesgo de §3.5**, con el argumento de §5.2. El review con la comprobación nunca baja de
  un kernel **cerrado por claves** (`KeyClosed`). Una clave viva del kernel sobrevive a su pin con etiqueta en todo
  estado mayor (`survives_of_keyClosed`), así que nunca se quita. Cada vuelta que quita claves baja la medida
  (`measure_dropKeys_lt`), así que el fuel no se agota.
* **`isValid_filterKC_of_kernel`**: el análogo de `isValid_filterAll_of_kernel` para `filterKC`. Un conjunto de pins
  sobrevive si un kernel válido y cerrado por claves por debajo del estado respeta los pins y lleva la etiqueta de
  cada pin de la fila de claves (`TagBelow`).

### 6.2 Lo que no dan: la inducción del lector

Al formalizar lo anterior revisé cómo usa M1 la inducción (`FExtInd.lExt_succ`), y eso corrige lo que decía este
informe en §3.4 y §3.5 (**deducido**, el razonamiento no está formalizado):
* Para extender los pins de un estado unido `J`, la inducción usa M1 para llegar a una pieza, **baja a su fuente `X`**
  (M2w), extiende allí y vuelve a subir (M3w). `X` es a su vez un estado unido de la línea anterior. Por eso la
  inducción pide M1 **en todas las líneas**, con el mismo filtro que se usa en las fuentes.
* Si el filtro nuevo se usa en todas las líneas, M1 vale en cada una (`m1_keyRules`). Pero el paso de bajada M2w pasa a
  pedir que el kernel que viene de la pieza sea cerrado por claves y lleve las etiquetas de la fila de claves de `X`
  (las hipótesis de `isValid_filterKC_of_kernel` una línea más abajo). **Con etiquetas de un nivel eso no está:** la
  pieza hereda las tablas mezcladas de `X` por debajo de su propia fila de claves, y sus etiquetas ya solo hablan de
  la fila nueva. Pedir que ese kernel respete las etiquetas de `X` es otra vez `M1bLowOwn`, una línea más abajo.
* Si el filtro nuevo se usa solo en la última línea, la inducción sigue necesitando la M1 de siempre en todas las
  demás.

**Qué lo arreglaría, y a qué precio (propuesto):**
* **Etiquetas de todos los niveles.** Cada entrada guarda, por cada fila de claves por la que pasó, de qué claves venía.
  Las piezas heredan las etiquetas de sus fuentes. Así, `TagBelow` en la bajada saldría por construcción, y la parte M1b
  quedaría resuelta en todas las líneas. El coste es polinómico, hasta ×2 por nivel (unas ×2S en el peor caso), y es
  pariente de los owners por rama que descartaste.
* **La comprobación de claves en todos los niveles no basta.** La copia de la comprobación usa el review de siempre, así
  que el kernel que deja por debajo de la pieza no es cerrado por claves en los niveles de abajo. Hacer que la copia
  use el review nuevo lleva la anticipación a una profundidad que crece con el número de filas: deja de ser
  polinómico. Así que **`M1aAll` sigue siendo el núcleo abierto**, con o sin reglas.

**Con etiquetas de todos los niveles y sin comprobación de claves**, la inducción quedaría así (deducido): el lector
decide bajo `M1aAll` (con el filtro etiquetado) en cada línea. `M1bLowOwn` desaparecería como hipótesis.

### 6.3 Qué haría ahora

* **Sin cambiar la máquina** siguen abiertos `M1aAll` (`KeyTri₁`, `KeyExact`) y `M1bLowOwn` (`KFix`), o los dos a la vez
  por `PairExact` con pins (§5.2, punto 3).
* **Con cambio**, la regla que vale la pena es la etiqueta de **todos** los niveles, no la comprobación de claves: es la
  que quita una hipótesis de verdad. Antes de formalizarla habría que medir su coste de memoria en Julia.
* La comprobación de claves solo aporta a M1 en la línea donde actúa. No quita nada en todo lo medido. No la
  recomiendo como cambio de la máquina.

---

**Ficheros de esta sesión:**
* `lean/improves_bin/AbsSatBin/GraphPath/Model/M1Parts.lean`: `M1bLowOwn`, `m1bLow_of_own`, `piece_pinCtx`, `KeyTri`
  (⚠ falso), `KeyTri₁`, `m1aAll_of_keyTri₁`.
* `lean/improves_bin/AbsSatBin/GraphPath/Model/M1bOwn.lean`: `KTri` y `KTriK` (⚠ falsos), `KClosed`, `KFix`,
  `m1bLowOwn_of_kTriK`, `m1bLowOwn_of_kFix`, `readerVerdictW_iff_of_kFix`.
* Sondas en `julia/improves_bin/test_3sat/probes/`: `keytri_common.jl`, `keytri_probe.jl`, `m1aall_probe.jl`,
  `ktri_probe.jl`, `keycut_trace.jl`, `kfix_probe.jl`.
* `lean/improves_bin/AbsSatBin/GraphPath/Model/KeyRules.lean`: `restrictTo`, `reviewKC`, `filterKC`, `pieceOf`,
  `kc_spec`, `below_piece`, `m1_keyRules`, `KeyClosed`, `TagBelow`, `below_reviewKC`, `isValid_filterKC_of_kernel`.
* Rama `julia_key_rules`: `julia/improves_bin/src/graph_path/graph_path_key.jl` (las dos reglas), los enganches,
  `test_3sat/compare_key.jl` y `test_3sat/probes/keytags_probe.jl`.
