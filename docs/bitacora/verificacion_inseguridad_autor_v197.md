# Verificación para el Autor v197: las reglas de un nivel, formalizadas, y la propuesta de etiquetas de todos los niveles

Ricardo, este informe cierra lo que empezó el v196 y presenta la propuesta con la que sigo. En pocas palabras:
implementé en Julia las dos reglas de la fila de claves, las medí y las formalicé en Lean. Al formalizarlas vi que no
bastan para el lector. La regla que sí bastaría para quitar una de las dos hipótesis es una etiqueta de clave en
**todos** los niveles, y es la que propongo hacer a continuación.

**La conclusión, por adelantado.**
* **Hecho en Julia** (rama `julia_key_rules`): la etiqueta de clave de un nivel y la comprobación de claves, apagadas
  por defecto. En 76 instancias no cambian ningún veredicto ni ninguna solución leída. **La comprobación no quita
  ninguna clave nunca.** Las etiquetas son exactas (999.222 entradas).
* **Hecho en Lean** (`KeyRules.lean`, 0 `sorry`, solo `[propext, Quot.sound]`):
  * con las dos reglas, M1 vale en el join donde actúan (`m1_keyRules`);
  * el review con la comprobación no baja de un kernel cerrado por claves (`below_reviewKC`), que era el riesgo del
    v196;
  * el lema de kernels para el filtro nuevo (`isValid_filterKC_of_kernel`).
* **La corrección:** las reglas de un nivel **no cierran la inducción del lector**. La inducción baja de cada estado
  unido a las fuentes de sus piezas, que son estados unidos de la línea anterior. En esa bajada las etiquetas de un
  nivel ya no están. El v196 decía más de la cuenta, y ya está corregido (§6).
* **La propuesta:** etiquetas de todos los niveles. Cada entrada guarda, por cada fila de claves por la que pasó, de
  qué claves venía. Con eso `M1bLowOwn` desaparecería como hipótesis en todas las líneas (deducido), y el lector
  decidiría bajo `M1aAll` sola. Coste polinómico, como mucho un factor S en memoria.
* **Implementada y medida (§8).** Las etiquetas de todos los niveles son **exactas** y no cambian ningún veredicto
  ni ninguna solución en las 29 instancias terminadas. Con ellas, M1b-entradas vale por construcción (24.560 estados).
  Pero la mezcla es casi total (hasta 89 de 105 filas) y la representación con diccionarios es inviable: 88,7 GB en
  `clause_mix_sep` y ×12,8 en tiempo. **Está desactivada** (`KEYTAGS_MODE = :off`) hasta rehacer la representación.
  Las dos reglas de un nivel se han quitado del código.

Cada afirmación lleva su estado: **demostrado** (teorema Lean), **medido** (sonda), **deducido** (argumento sin
formalizar), **propuesto** o **abierto**.

Commits: `82c121f`, `5815b66` y `6c4841c` en `lean_improves_bin`; en `julia_key_rules`, `aeeb001`, `cac23ff` y
`98923f0` (reglas de un nivel), `a7b3dd7` (las quita), y `f218230`, `47d00be` y `cfc92c9` (etiquetas de todos los
niveles, desactivadas).

---

## 1. De dónde venimos

El lector decide `φ` bajo una sola hipótesis, **M1**, en cada join (`FExtInd.readerVerdictW_iff_of_m1`): si un estado
unido `J`, fijado en unos pins, es válido, alguna de sus piezas fijada igual es válida. `J` es la unión de piezas
`P_k`, una por cada clave `k`, que es el nodo de mapa de la fila de claves (el paso `n`) de su fuente. M1 se parte en
dos (`M1Parts.lean`):
* **`M1aAll`**: fijar cualquier clave viva no deja `J` inválido. Abierto; la otra sesión lo lleva por `KeyTri₁`,
  `KeyExact` y `KeySplit`.
* **`M1bLowOwn`**: con la clave `k` fijada, toda entrada de las filas de abajo es entrada de la pieza `k`. Abierto;
  la forma que no falla es `KFix`, medida en 24,7 M enlaces.

El v196 proponía dos reglas para cerrarlas por construcción: la **etiqueta de clave**, para `M1bLowOwn`, y la
**comprobación de claves**, para `M1aAll`.

## 2. Qué he cambiado

### 2.1 En Julia (rama `julia_key_rules`)

* `src/graph_path/graph_path_key.jl`: las dos reglas y sus contadores.
  * `KeyTags`: la etiqueta de un nivel, implícita en una pieza sin unir y explícita tras un join.
  * `init_key_tags!`, `materialize_key_tags!`, `join_key_tags!` y `restrict_to_key!`: la etiqueta.
  * `live_keys` y `key_check!`: la comprobación. Mira también una sola clave viva cuando las tablas están mezcladas
    (commit `98923f0`, para que coincida con el modelo Lean).
* Enganches en `do_up!`, `do_join!`, `filter_require!` y `make_review_owners!`. Con `KEY_MODE = :off` y
  `KEYCHECK_MODE = :off`, que es lo que hay por defecto, la máquina es la de siempre.
* `test_3sat/compare_key.jl`: diferencial en cuatro modos (ninguna regla, solo etiqueta, solo comprobación, las dos).
* `test_3sat/probes/keytags_probe.jl`: exactitud de las etiquetas y M1b-entradas con las dos reglas.

### 2.2 En Lean (`KeyRules.lean`, rama `lean_improves_bin`)

Las reglas entran como operaciones nuevas del modelo de listas, sin tocar la máquina ni el review de siempre:
* **`restrictTo g P`**, la etiqueta: cada tabla se queda con lo que la pieza `P` tiene para ese nodo. Como las
  etiquetas de Julia son exactas, el modelo toma la pertenencia a la tabla de la pieza como etiqueta, a través de un
  mapa de claves a piezas (`pieceOf`).
* **`reviewKC`**, la comprobación: review hasta el punto fijo; después se quitan a la vez las claves cuyo pin con
  etiqueta deja inválida la copia (`deadKeys`, `dropKeys`), y se repite.
* **`filterKC`**: pins, etiquetas de los pins de la fila de claves y `reviewKC`.

## 3. Resultados

### 3.1 Medidos en Julia

Diferencial en 76 instancias del mapa bin:

| modo | veredictos | lector sin retroceso | tiempo | claves quitadas |
|---|---|---|---|---|
| ninguna regla | 76 / 76 | 76 bien | 193,6 s | — |
| solo etiqueta | 76 / 76 | 76 bien | 299,3 s | — |
| solo comprobación | 76 / 76 | 76 bien | 302,1 s | **0** |
| las dos | 76 / 76 | 76 bien | 427,2 s | **0** |

* En los cuatro modos, el lector exponencial lee **las mismas soluciones** y el pico de nodos es el mismo.
* La etiqueta sola solo actúa dentro de la máquina en `v5_c20_i2` y `v5_c20_i4`: un filtro de requisito llega a la fila
  de claves y corta 370 entradas en cada una, sin cambiar nada del resultado.
* **Etiquetas exactas** en las dos direcciones (etiqueta `k` en (p, v) si y solo si `v` está en la tabla de `p` en
  `P_k`): 999.222 entradas, 0 fallos. Con las dos reglas, M1b-entradas vale en los 24.501 estados fijados medidos.

### 3.2 Demostrados en Lean (solo `[propext, Quot.sound]`, 0 `sorry`)

* **`m1_keyRules`, M1 donde actúan las reglas.** En un estado unido de la línea `n+1`, si `filterKC` deja válidos los
  pins, alguna pieza es válida con el filtro de siempre y los mismos pins. La prueba:
  1. `kc_spec`: en una salida válida de `reviewKC` ninguna clave viva muere al fijarla.
  2. `below_piece`: fijar una clave con su etiqueta y revisar da un kernel válido por debajo de su pieza. Es
     `M1bLowOwn`, por construcción.
  3. El lema de kernels de siempre en la pieza.
* **`below_reviewKC`, el riesgo del v196.** El review con la comprobación nunca baja de un kernel cerrado por claves.
  Una clave viva del kernel sobrevive a su pin con etiqueta en todo estado mayor, así que nunca se quita
  (`survives_of_keyClosed`). Y cada vuelta que quita claves baja la medida, así que el fuel no se agota
  (`measure_dropKeys_lt`). Es el argumento que propuso el otro agente.
* **`isValid_filterKC_of_kernel`**, el lema de kernels para `filterKC`: los pins sobreviven si un kernel válido y
  cerrado por claves por debajo del estado los respeta y lleva la etiqueta de cada pin de la fila de claves
  (`TagBelow`).

## 4. Lo que las reglas de un nivel no dan

Al formalizar revisé cómo usa M1 la inducción del lector (`FExtInd.lExt_succ`). Para extender los pins de un estado
unido `J`:
1. usa M1 para llegar a una pieza;
2. **baja a la fuente `X` de la pieza** (M2w);
3. extiende allí los pins;
4. vuelve a subir a la pieza (M3w) y de la pieza a `J`.

`X` es a su vez un estado unido de la línea anterior. Por eso la inducción pide M1 **en todas las líneas**, con el
mismo filtro que usa en las fuentes (**deducido**):
* Si el filtro nuevo se usa solo en la última línea, las demás siguen necesitando la M1 de siempre.
* Si se usa en todas, M1 vale en cada una (`m1_keyRules`). Pero la bajada del paso 2 pasa a pedir que el kernel que
  viene de la pieza respete las etiquetas de la fila de claves de `X`. Con etiquetas de un nivel no las respeta: la
  pieza hereda las tablas mezcladas de `X` por debajo de su propia fila de claves, y sus etiquetas ya solo hablan de la
  fila nueva. Pedirlo es otra vez `M1bLowOwn`, una línea más abajo.
* La comprobación de claves tampoco escala. Su copia usa el review de siempre, así que el kernel que deja no es cerrado
  por claves en las filas de abajo. Hacer que la copia use el review nuevo lleva la anticipación a una profundidad que
  crece con el número de filas, y deja de ser polinómico. Además no quita nada en todo lo medido. **No la recomiendo.**

Lo que este análisis señala es la etiqueta, pero en todos los niveles.

## 5. La propuesta: etiquetas de clave de todos los niveles

**Propuesto.**

### 5.1 La idea

La etiqueta va por **entrada**, es decir, por el par (nodo `p`, owner `v`), no por nodo. Un nodo de las filas de abajo
suele estar en varias piezas a la vez, con una tabla distinta en cada una, y el join guarda la unión. La mezcla ocurre
dentro de la tabla de un mismo nodo. Por ejemplo:
* en la pieza `k0`, la tabla de `p` es {a, b};
* en la pieza `k1`, la tabla de `p` es {b, c};
* en el estado unido, la tabla de `p` es {a, b, c}, con etiquetas a → {k0}, b → {k0, k1} y c → {k1}.

Al fijar `k0`, cada tabla se queda con las entradas cuya etiqueta contiene `k0`, y `p` vuelve a {a, b}: exactamente su
tabla en la pieza `k0`. La etiqueta solo recorta; el review de siempre hace el resto.

**De todos los niveles** quiere decir que cada entrada guarda un conjunto de claves por cada fila de claves por la que
pasó:

```
(p, v) → { fila n: {k0, k1},  fila n-1: {j1},  fila n-2: {i0, i1}, … }
```

* **Al fijar una clave en cualquier fila ℓ**, se quedan las entradas que la tienen en su conjunto de la fila ℓ.
* **En el UP**, la pieza hereda las etiquetas de su fuente y añade la fila nueva, con su única clave. El nodo nuevo
  hereda de sus padres.
* **En el join**, los conjuntos se unen fila a fila.

### 5.2 Borrador en Julia

En el mapa bin, las claves de una fila son los nodos de mapa `(ℓ, 0)` y `(ℓ, 1)`, así que un `UInt8` basta por fila. Para
no pagar donde no hay mezcla, cada fila tiene una máscara **uniforme**, común a todas las entradas, y solo se
materializan por entrada las filas que un join ha mezclado.

```julia
# Etiquetas de clave de todos los niveles.
# Máscara de una fila ℓ: bit i ⇔ la entrada viene de la pieza cuya clave es el nodo de mapa (ℓ, i).
const KeyMask = UInt8
key_bit(k :: NodeId) :: KeyMask = KeyMask(1) << k.index      # mapa bin: index ∈ {0, 1}

mutable struct KeyTagsAll
    uniform :: Dict{Step, KeyMask}                                       # fila ℓ => máscara común
    mixed   :: Dict{Step, Dict{Tuple{PathNodeId, PathNodeId}, KeyMask}}  # fila ℓ mezclada => (p, v) => máscara
end
# En GPath: `key_tags :: Union{KeyTagsAll, Nothing}`

# La máscara de la entrada (p, v) en la fila ℓ.                                    O(1) esperado
function tag_mask(t :: KeyTagsAll, p :: PathNodeId, v :: PathNodeId, ℓ :: Step) :: KeyMask
    m = get(t.mixed, ℓ, nothing)
    m === nothing ? get(t.uniform, ℓ, KeyMask(0xff)) : get(m, (p, v), KeyMask(0))
end

# Tras el UP (do_up!): la fila de la fuente pasa a ser fila de claves, con una sola clave.   O(1)
# Las filas anteriores se heredan tal cual: la pieza lleva las etiquetas de su fuente.
function init_key_level!(gpath :: GPath, key :: NodeId)
    t = something(gpath.key_tags, KeyTagsAll(Dict(), Dict()))
    t.uniform[key.step] = key_bit(key)
    gpath.key_tags = t
end

# El nodo nuevo del UP hereda, para cada fila mezclada, las máscaras de sus padres (OR), y el espejo (v, nuevo)
# copia la de (nuevo, v). Solo filas mezcladas: las uniformes valen sin tocar nada.
#! [for] $ O(L_mix * 7 * S*7) $   L_mix = filas mezcladas ≤ S; 7 padres; S*7 entradas por padre
function inherit_tags!(gpath :: GPath, new :: PathDocNode, parents :: Vector{PathNodeId})
    t = gpath.key_tags; t === nothing && return
    for (ℓ, m) in t.mixed, c in parents, v in owners_of(gpath, c)
        m[(new.id, v)] = get(m, (new.id, v), KeyMask(0)) | get(m, (c, v), KeyMask(0))
        m[(v, new.id)] = m[(new.id, v)]
    end
end

# Una fila deja de ser uniforme: se materializa entrada a entrada.                 O(E) = O(S²·7²)
function materialize_level!(gpath :: GPath, ℓ :: Step)
    t = gpath.key_tags
    haskey(t.mixed, ℓ) && return
    u = t.uniform[ℓ]
    t.mixed[ℓ] = Dict((p, v) => u for (p, v) in entries(gpath))
    delete!(t.uniform, ℓ)
end

# Join (do_join!, antes de unir las tablas): fila a fila, OR de máscaras.
# Si las dos uniformes coinciden, la fila sigue uniforme; si no, se materializa en los dos estados.
#! [for] $ O(L * E) = O(S · S²·7²) = O(S³·7²) $   peor caso; O(S) si no hay filas nuevas mezcladas
function join_tags_all!(gpath :: GPath, other :: GPath)
    a = gpath.key_tags; b = other.key_tags
    (a === nothing || b === nothing) && (gpath.key_tags = nothing; return)
    for ℓ in union(keys(a.uniform), keys(a.mixed), keys(b.uniform), keys(b.mixed))
        if haskey(a.uniform, ℓ) && haskey(b.uniform, ℓ) && a.uniform[ℓ] == b.uniform[ℓ]
            continue                                                  # fila sin mezcla: nada que hacer
        end
        materialize_level!(gpath, ℓ); materialize_level!(other, ℓ)
        ma = a.mixed[ℓ]
        for (e, mask) in b.mixed[ℓ]
            ma[e] = get(ma, e, KeyMask(0)) | mask
        end
    end
end

# Al fijar la clave k en su fila (filter_require!, en cualquier fila, no solo la penúltima): cada tabla se queda con
# las entradas que llevan k en esa fila. Después la fila vuelve a ser uniforme con solo k.
#! [fn-iter] $ O(E) = O(S²·7²) $ por pin
function restrict_level!(gpath :: GPath, k :: NodeId)
    t = gpath.key_tags; t === nothing && return
    ℓ = k.step
    m = get(t.mixed, ℓ, nothing)
    if m === nothing                                   # fila uniforme: basta mirar la máscara común
        (get(t.uniform, ℓ, KeyMask(0xff)) & key_bit(k)) != 0 || kill_all_entries!(gpath)
        return
    end
    for (p, v) in collect(entries(gpath))
        (get(m, (p, v), KeyMask(0)) & key_bit(k)) != 0 && continue
        PathDocumentNode.remove_owner!(get_node(gpath, p), v)
        gpath.review_owners = true
    end
    delete!(t.mixed, ℓ)
    t.uniform[ℓ] = key_bit(k)
end

# Limpieza de las máscaras de entradas que la review ya quitó; se llama en el UP.  O(L_mix * E)
function prune_tags!(gpath :: GPath) ... end
```

`owners_of`, `entries`, `get_node` y `kill_all_entries!` son ayudantes triviales sobre las tablas que ya existen.

**Enganches:**
* `do_up!`: `init_key_level!` tras `add_row!`, e `inherit_tags!` dentro de `create_node_from_parents!`.
* `do_join!`: `join_tags_all!` antes de unir.
* `filter_require!`: `restrict_level!` en **cualquier** fila con máscara.
* La review no cambia.

### 5.3 Cotas

S es el número de pasos y 7 la cota de ancho de una fila, como en los comentarios `#!` del repositorio. Un estado tiene
E = O(S·7 · S·7) entradas.

| operación | ahora | con etiquetas de todos los niveles |
|---|---|---|
| memoria por estado | O(S²·7²) | O(S³·7²) peor caso · O(S²·7² + S) sin mezcla |
| join | O(S²·7²) | O(S³·7²) peor caso |
| UP (nodo nuevo) | O(7·S·7) | O(S·7·S·7) peor caso |
| pin (`filter_require!`) | O(7) + review | O(S²·7²) + review |
| review | igual | igual (no mira las etiquetas) |

Todo es polinómico y el factor extra es como mucho S. El caso real depende de cuántas filas quedan mezcladas. Si las
piezas de un join suelen compartir sus tablas bajas, muchas filas seguirán uniformes y el coste se acercará al actual.

### 5.4 Qué daría a la prueba (deducido)

* **`TagBelow` en la bajada, por construcción.** El kernel que viene de una pieza vive en las tablas de la pieza, que
  llevan las etiquetas de su fuente en todas las filas. Al fijar una clave de la fuente, ese kernel ya está dentro de
  su parte. Es la hipótesis que faltaba en M2w (§4).
* **`M1bLowOwn` desaparece como hipótesis** en todas las líneas: fijar una clave con su etiqueta deja el estado por
  debajo de su pieza (`below_piece`, ya demostrado para un nivel).
* **El lector decidiría `φ` bajo `M1aAll` sola**, con el filtro etiquetado, en cada línea. La comprobación de claves no
  hace falta.
* **Lo que no daría:** `M1aAll`. Sigue siendo el núcleo abierto, ahora solo, y la otra sesión trabaja en él.

### 5.5 Qué hay que tener presente

* Es de la familia de los owners por rama que descartaste por la compresión. La diferencia es que aquí las tablas
  siguen unidas como ahora, y la etiqueta solo recuerda claves (nodos de mapa, como mucho 2 por fila), no ramas.
* Cambia la conducta de la máquina cuando un filtro fija un nodo de una fila con etiqueta mezclada. Eso pasa en los
  filtros de requisito y en el lector. Poda más, sin perder soluciones: una solución que pasa por `k` en la fila `ℓ` es
  un camino de la pieza `k` de esa línea, así que todas sus entradas llevan `k` (deducido).

## 6. Correcciones al v196

* El v196 decía que con las dos reglas M1 salía entero y el lector decidía. **No es así** (§4). Vale M1 en el join
  donde actúan las reglas, y ya está demostrado. El v196 lo recoge en su §6, y su §3.5 remite allí.
* El riesgo de `below_review` era real pero se resolvió: **`below_reviewKC` está demostrado.** No cambia la
  conclusión, porque la comprobación de claves no llega a cerrar la inducción.

## 7. Qué voy a hacer a continuación (plan inicial; resultado en §8)

1. **Medir la mezcla** (sonda en Julia, sin tocar la máquina). Por cada estado de cada línea: cuántas filas de claves
   quedan mezcladas, el tamaño de `mixed` frente al de las tablas, y la máscara típica de una entrada. Eso dice si el
   coste real está cerca de O(S²·7²) o de O(S³·7²).
2. **Implementarla en Julia** detrás de un interruptor, en la rama `julia_key_rules` (sustituyendo la etiqueta de un
   nivel), y medir veredictos, tamaños y tiempo con `compare_key.jl`. Con `keytags_probe.jl` ampliada a todos los
   niveles, comprobar la exactitud de las etiquetas en cada fila.
3. **Formalizarla en Lean**: extender `KeyRules` a etiquetas de todos los niveles y demostrar la bajada M2w con el
   filtro etiquetado. El objetivo es **el lector decide bajo `M1aAll` sola**.

Si en el paso 1 la mezcla resulta ser casi total, el factor S de memoria será real y lo valoraremos antes de seguir.

## 8. Resultados de las etiquetas de todos los niveles

### 8.1 Qué hice

En la rama `julia_key_rules`:
* **`a7b3dd7`**: quité del código las dos reglas de un nivel (la etiqueta de un nivel y la comprobación de claves).
  Quedan sustituidas por la propuesta de §5. Las dos reglas siguen documentadas en el v196 y formalizadas en
  `KeyRules.lean`.
* **`f218230`**: las etiquetas de todos los niveles, en `src/graph_path/graph_path_keytags.jl`, según el borrador de
  §5.2:
  * `KeyTagsAll`: por cada fila de claves, una máscara uniforme o una por entrada (p, v) si un join la mezcló.
  * `init_key_level!`, `inherit_keytags!`, `prune_keytags!`: el UP (fila nueva con una clave, herencia de los padres,
    limpieza).
  * `join_keytags!`: el join, OR fila a fila; `materialize_level!` cuando una fila se mezcla.
  * `restrict_keytags!`: el pin, llamado desde `filter_require!` en cualquier fila.
  * Diferencial `test_3sat/compare_keytags.jl` y sonda `test_3sat/probes/keytags_all_probe.jl`.
* **`47d00be`**: un error que salió al medir. El review que hace el UP al final (ventanas prohibidas) quitaba entradas
  después de heredar sus máscaras, y el join acumulaba máscaras huérfanas: 318.848 frente a 4.096 entradas vivas en
  `rand3sat_v4_c20`. Ahora se limpian también tras ese review, y quedan 0.
* **`cfc92c9`**: **desactivada** por memoria (§8.4). `KEYTAGS_MODE = :off` por defecto: no se crea ninguna etiqueta y
  los enganches no hacen nada, así que la máquina es la de siempre. Solo las sondas la encienden, explícitamente.

### 8.2 Exactitud (`keytags_all_probe.jl`)

En `clause_mix.cnf`, `clause_mix_sep.cnf` y las 6 primeras de `random_small`, en cada estado unido J de la línea
`n+1`. **0 fallos**:

| comprobación | casos | fallos |
|---|---|---|
| fila n (el último join): etiqueta `k` en (p, v) ⇔ `v` está en la tabla de `p` en la pieza `P_k` | 1.115.403 | 0 |
| fila n-1 (heredada): etiqueta `j` ⇒ la entrada está en alguna pieza `P_k` y en la pieza `Q_{k,j}` de la línea anterior | 695.699 | 0 |
| M1b-entradas con la regla: J fijado en R + k válido ⇒ toda entrada de las filas de abajo es de `P_k` | 24.560 | 0 |

* En la fila n-1 no se comparan 27.162 entradas cuyo owner es un nodo de la cima (paso n+1). Ese nodo no existía en
  la pieza de la línea anterior; su máscara la hereda de sus padres. En la primera pasada la sonda los contó como
  fallos; era un error de la sonda, corregido en `cfc92c9`.
* **Lectura:** la herencia por el UP y la unión por el join hacen lo que dice §5.1. Con las etiquetas, `M1bLowOwn`
  deja de ser una hipótesis y pasa a ser una propiedad por construcción. Esto está medido, no demostrado.

### 8.3 Diferencial (`compare_keytags.jl`, `:off` frente a `:on`)

Se paró tras 29 de las 76 instancias, por memoria (§8.4). En esas 29:
* **Mismo veredicto** en las 29, y todas aciertan frente al exhaustivo.
* **Mismas soluciones** leídas por el lector exponencial, **mismo pico** de nodos, y el lector sin retroceso acierta
  siempre.
* **Tiempo ×12,8** en total (162,9 s → 2.086,2 s). Por instancia, de ×10 a ×31; la peor es `rand3sat_v8_c10`.
* **La regla actúa en la máquina:** los filtros de requisito que fijan una fila mezclada recortan entradas (30.779 en
  `clause_mix`, 1,9 M en `v7_c30_i2`). No cambia nada del resultado: lo que corta no lo usa ninguna solución.
* **La mezcla es casi total:** hasta 89 filas mezcladas de 105 (`v7_c30_i2`); en `clause_mix`, 22 de 25. Tras el
  arreglo de `47d00be`, las máscaras por entrada son exactamente el número de filas mezcladas.

### 8.4 El coste: memoria

`clause_mix_sep.cnf` sola, con la regla encendida, llega a **88,7 GB de huella de memoria** (6,9 GB residentes; el
resto, comprimido) y no termina.
* **Crecimiento lineal en S, no exponencial:** cada entrada lleva como mucho una máscara por fila de claves, 2 bits en
  el mapa bin. Las filas se etiquetan por separado; no se guardan combinaciones entre filas (ramas), que sí serían
  2^S.
* **La causa es la representación:** cada máscara va en un diccionario por fila con clave (p, v).
  * Cada clave son dos `PathNodeId`, cada uno con tres `NodeId` opcionales: unos 150 bytes por máscara.
  * Con 89 filas mezcladas, unos 13 KB de etiquetas por entrada de tabla.
  * La máquina hace `deepcopy` del estado en cada envío a un hijo, con todos los diccionarios.
* **La información real** son 2 bits por fila: unos 26 bytes por entrada con 105 filas, unas 500 veces menos.

### 8.5 Qué queda

* **Correcta, pero cara en esta forma.** Antes de volver a encenderla hay que guardar la máscara **dentro de la tabla
  de owners**: un vector de 2 bits por fila de claves junto a cada owner, no diccionarios aparte. La cota asintótica
  es la misma, pero la constante es unas 500 veces menor, y el join y el pin pasan a ser operaciones sobre bits.
* **Con esa representación:** repetir el diferencial completo (76 instancias) y la sonda de exactitud; después, la
  formalización en Lean (§5.4). El objetivo sigue siendo que el lector decida bajo `M1aAll` sola.
* **Sin cambiar la máquina:** siguen abiertos `M1aAll` (`KeyTri₁`, `KeyExact`, `KeySplit`) y `M1bLowOwn` (`KFix`), o
  los dos por `PairExact` con pins.

---

**Ficheros:**
* `lean/improves_bin/AbsSatBin/GraphPath/Model/KeyRules.lean`: `restrictTo`, `reviewKC`, `filterKC`, `pieceOf`,
  `kc_spec`, `below_piece`, `m1_keyRules`, `KeyClosed`, `TagBelow`, `below_reviewKC`, `isValid_filterKC_of_kernel`.
* Rama `julia_key_rules`: `julia/improves_bin/src/graph_path/graph_path_keytags.jl` (desactivado), sus enganches en
  `graph_path_up.jl`, `graph_path_join.jl` y `graph_path_filter.jl`, `test_3sat/compare_keytags.jl` y
  `test_3sat/probes/keytags_all_probe.jl`. Las reglas de un nivel (`graph_path_key.jl`, `compare_key.jl`,
  `keytags_probe.jl`) se quitaron en `a7b3dd7`.
* Detalle técnico en `docs/context/escalera_reader.md` §4.2ο.2; propuesta anterior en el v196.
