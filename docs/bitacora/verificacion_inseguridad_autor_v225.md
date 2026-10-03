# Verificación para el Autor v225: propuesta del lector por separadores (ReaderSep)

3 de octubre de 2026, rama `reader-stuck`. Continúa el v224. Es una **propuesta**, no un resultado: un cambio pequeño
en el lector (el orden en que fija las variables), con un borrador en Julia que ya funciona en la máquina real y un
borrador en Lean con los enunciados que habría que demostrar. En una frase: **si el lector fija primero las variables
compartidas por varias cláusulas (los separadores), lo que queda por leer se descompone en piezas que no se ven, y la
parte difícil de la demostración se reduce a un solo lema, sobre los separadores.**

> **Estado**: medidas completas (en `chain6_cross` sin juzgar camarillas: estados demasiado grandes). Tras escribir el borrador se demostraron T1 y T3 (§8).

## 0. Resumen

| | lector actual (`PathReader`) | lector por separadores (`PathSepReader`, borrador) |
|---|---|---|
| orden de las variables | `x1, x2, x3, …` (la numeración) | primero los separadores, en el orden de su primera cláusula; después el resto |
| cambio en la máquina | — | ninguno; solo el orden del lector |
| coste | `n` filtros | `n` filtros, más una pasada por las cláusulas para hallar los separadores |
| `chain5_cross`, estados leídos con triángulos fantasma | sí (36 en 470 estados, v224) | **no** (0 en 44 estados, §6) |
| qué hay que demostrar | `PinPairs` para lecturas en cualquier orden (abierto, difícil) | T1 (sencillo) y T2 (un lema sobre separadores) |

## 1. Por qué lo propongo

Tres hechos del v224, medidos y demostrados:

1. **Dónde están los fantasmas.** En `chain5_cross` los 36 triángulos fantasma del lector aparecen al fijar una variable
   **de dentro** de un bloque (la 10 del `.cnf`) cuando el triángulo no lee ningún separador y cada uno de sus nodos lee,
   solo en su ventana, una variable a cada lado de todos los cortes. Es la «configuración doble» (v224, §7).
2. **Por qué hay fantasmas.** Una ventana lee los pasos `k`, `k-1`, `k-2`: con numeración cruzada mezcla bloques
   lejanos. Ninguna elección de testigo cubre los dos lados a la vez, porque los separadores entre medias no están
   fijados ni leídos.
3. **Lo que ya está demostrado.** En cuatro bloques, con los separadores fijados, una variable de dentro se fija sin
   familias fantasma con un parche del interior de su bloque, sin descenso ni testigos (`phantomFree_pinnedSeps`,
   `ForbidOnChain4R`).

De ahí la propuesta: **si todos los separadores están fijados antes de fijar una variable de dentro, la configuración
doble no puede darse**, porque los cortes en los separadores pasan a ser libres para todas las ramas. El orden de las
elecciones es libre (el lector puede fijar cualquier nodo vivo; `Reading` lo admite en Lean), así que elegirlo bien no
cambia lo que la máquina calcula, solo cómo se lee.

## 2. Ventajas para la demostración

1. **Las variables de dentro, en cualquier longitud de cadena (T1).** Con los separadores fijados, todas las ramas de
   las soluciones fijadas leen igual los separadores; los bloques ya no se ven. Fijar una variable de dentro se
   demuestra parcheando la parte de su bloque (`helly4_of_patch` sobre una parte de a lo sumo dos variables). No hace
   falta descenso, ni testigos de ventana, ni condiciones de numeración. Ni siquiera hace falta que sea una cadena:
   basta una **cobertura por separadores** (§5, `SepCover`): quitar los separadores deja partes de a lo sumo dos
   variables, y cada cláusula toca una sola parte.
2. **Lo abierto se reduce a los separadores (T2).** El lema que queda habla solo de fijar el separador `k`-ésimo con los
   anteriores ya fijados. Son pocas elecciones (una por separador), siempre en el mismo orden, y en cada una la parte de
   la cadena a la izquierda del último separador fijado está **congelada** respecto del resto. En cadenas de hasta
   cuatro bloques este lema ya está demostrado (los casos de separador de `ForbidOnChain4`, que valen con cualquier
   lectura previa).
3. **Se recupera la exactitud.** El v224 tuvo que bajar al invariante de aristas (`RInvE`, `PinPairs`) porque el
   lector en cualquier orden no es exacto en triángulos. Si T1 y T2 valen, el lector por separadores conserva la
   exactitud completa (`Snd3`) en todos sus estados, y la prueba es la de siempre (`reading_inv_on`, `GoodAlong`, ya
   en `ForbidOnChain4R`).
4. **La reducción ya está escrita.** `reading_inv_on` pide la hipótesis del lector solo en los pasos de la lectura
   concreta. Basta decir qué elección es «buena» en cada momento: un separador en su turno, o una variable de dentro
   cuando ya están todos los separadores (§5, T3).

## 3. Lo que no resuelve

* **T2 sigue siendo un lema de verdad.** Fijar el primer separador es un problema sobre la cadena entera, y el análisis
  a mano (v224, §10) dice que con el descenso por testigos solo cierra hasta cinco bloques en el caso en que el
  triángulo no lee ningún separador. Para cadenas más largas hará falta una idea más (o la medida dirá que el lema
  falla y que el orden de los separadores importa).
* **No elimina la necesidad de las líneas**: el lector parte de un estado final exacto, y eso lo dan las líneas
  (`phantomAt_of_prefix` y las clases de cuatro bloques; cinco, pendiente).
* **No cambia la clase de fórmulas**: es una propuesta para cadenas y, más en general, para fórmulas con una cobertura
  por separadores; en fórmulas sin esa estructura los separadores pueden ser casi todas las variables y la propuesta
  no simplifica nada.

## 4. Borrador en Julia: `drafts/path_sep_reader.jl`

Derivado de `src/graph_path/reader/path_reader.jl`. Cambia solo el orden y dónde se guarda cada valor; la elección
(el primer nodo vivo del paso) y el filtro son los mismos. No está incluido en `AbsSat`: se carga con `include` después
de `src/main.jl`.

```julia
module PathSepReader

    using Main.AbsSat.Alias: Step, NodeId, SetNodesId, PathNodeId, SetPathNodesId
    using Main.AbsSat.DBCollections.PathCollectionLines
    using Main.AbsSat.GraphPath: GPath
    using Main.AbsSat.GraphPath

    """Separadores: las variables que aparecen en dos o más cláusulas, en el orden de su primera cláusula."""
    function separators(n :: Int, clauses :: Vector{Vector{Int}}) :: Vector{Int}
        count = zeros(Int, n)
        first_clause = fill(typemax(Int), n)
        for (j, c) in enumerate(clauses), v in unique(abs.(c))
            count[v] += 1
            first_clause[v] = min(first_clause[v], j)
        end
        return sort([v for v in 1:n if count[v] >= 2], by = v -> (first_clause[v], v))
    end

    """El orden de lectura: los separadores primero, después el resto en orden creciente."""
    read_order(n :: Int, seps :: Vector{Int}) :: Vector{Int} = vcat(seps, [v for v in 1:n if !(v in seps)])

    mutable struct GPathSepReader
        gpath :: GPath
        order :: Vector{Int}
        pos :: Int
        solution :: BitArray{1}
        is_finished :: Bool
    end

    function new(gpath :: GPath, n :: Int, clauses :: Vector{Vector{Int}}; order = read_order(n, separators(n, clauses)))
        return GPathSepReader(gpath, order, 1, falses(n), false)
    end

    # Mapa bin: la variable `v` (desde 1) está en el paso 2v - 1 y el índice del nodo es su valor.
    var_step(v :: Int) :: Step = Step(2v - 1)

    """Un paso: fijar el primer nodo vivo del paso de la siguiente variable del orden y filtrar."""
    function read_step!(reader :: GPathSepReader; choose = first)
        reader.is_finished && return
        if reader.pos > length(reader.order)
            reader.is_finished = true
            return
        end
        v = reader.order[reader.pos]
        ids = collect(PathCollectionLines.get_ids_step(reader.gpath.table_lines, var_step(v)))
        isempty(ids) && throw("ReaderSep: sin nodos vivos en el paso de x$v")
        selected = choose(ids)
        reader.solution[v] = selected.id.index == 1
        GraphPath.filter!(reader.gpath, SetNodesId([selected.id]))
        reader.gpath.is_valid || throw("ReaderSep: GPATH INVALID tras fijar x$v")
        reader.pos += 1
    end

    function read!(reader :: GPathSepReader; choose = first) :: BitArray{1}
        while !reader.is_finished
            read_step!(reader; choose = choose)
        end
        return reader.solution
    end

end
```

Diferencias con `PathReader`:

* `PathReader` avanza `step += 2` desde el primer paso de literal y acaba al llegar a la fusión; `PathSepReader`
  recorre una lista de variables (`order`) y acaba al agotarla.
* `PathReader` añade cada valor al final de `solution` (orden de lectura = orden de variables); `PathSepReader` lo
  escribe en `solution[v]`, porque el orden de lectura ya no es el de las variables.
* `choose` permite elegir el nodo (por defecto el primero, como `PathReader`); la sonda lo usa para elegir al azar.
* Para integrarlo: incluirlo en `src/graph_path/graph_path.jl` junto a `path_reader.jl`, y que quien llama
  (`dump_final.jl`, la comprobación del veredicto) pase `n` y las cláusulas, que ya tiene al cargar el `.cnf`.

## 5. Borrador en Lean

Compila (fuera del proyecto, sobre `import AbsSatBingo`) con `sorry` en los dos teoremas por demostrar.

```lean
/-- **Una cobertura por separadores**: los separadores `S` y una parte `part z` para cada variable que no es
separador. Cada cláusula tiene sus variables que no son separadores en una sola parte, y cada parte tiene a lo sumo
dos variables. Las cadenas de bloques la cumplen con `S` = las variables compartidas. -/
structure SepCover (φ : Cnf) (S : List Nat) (part : Nat → Nat) : Prop where
  cl   : ∀ c ∈ φ.clauses, ∀ z z', ClVar c z → ClVar c z' → z ∉ S → z' ∉ S → part z = part z'
  card : ∀ p z1 z2 z3, z1 ∉ S → z2 ∉ S → z3 ∉ S → part z1 = p → part z2 = p → part z3 = p →
    z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False

/-- **Separadores primero**: las `S.length` primeras elecciones de la lectura leen los separadores, en el orden de
`S`. -/
def SepFirst (φ : Cnf) (S : List Nat) (R : List NodeId) : Prop :=
  (R.take S.length).map (fun r => stepVar φ r.step) = S.map some

/-- **T1** (a demostrar; generaliza `phantomFree_pinnedSeps`): con los separadores leídos igual por todas las ramas,
una variable que no es separador se fija sin familias fantasma, con cualquier longitud de cadena. -/
theorem phantomFree_pinnedSepCover {P0 P : Assign → Prop} {N σ : Int} {S : List Nat} {part : Nat → Nat}
    (hl : LocPair φ P0 P σ) (hc : SepCover φ S part) {v : Nat} (hv : stepVar φ σ = some v) (hvS : v ∉ S)
    (hsep : ∀ a b, P0 a → P0 b → ∀ s ∈ S, a s = b s) (hσ0 : 0 ≤ σ) (hσN : σ < N) :
    PhantomFree φ P0 P N σ := by
  sorry

/-- **T2** (el núcleo, abierto): fijar el separador `S[k]` con los anteriores fijados no deja familias fantasma. -/
def SepPinFree (φ : Cnf) (S : List Nat) (T : Int) : Prop :=
  ∀ (k : NodeId) (R : List NodeId) (r : NodeId),
    (R.map (fun x => stepVar φ x.step)) = (S.take R.length).map some → R.length < S.length →
    stepVar φ r.step = some (S[R.length]!) → 1 ≤ r.step → r.step < T →
    PhantomFree φ (Pinned φ (SolE φ T k) R) (fun a => Pinned φ (SolE φ T k) R a ∧ selOfAssign φ a r.step = r) T r.step

/-- **T3** (la reducción, a demostrar con `reading_inv_on`): con las líneas, una cobertura por separadores y T2, el
lector por separadores no se atasca y acaba en una solución que coincide con todas las elecciones. -/
theorem reader_sep_on {S : List Nat} {part : Nat → Nat} (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (hc : SepCover φ S part) (h2 : SepPinFree φ S (stepCount φ)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') (hsf : SepFirst φ S R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  sorry
```

Cómo se demostraría cada uno:

* **T1** es la prueba de `phantomFree_pinnedSeps` sin los datos de cuatro bloques: `helly4_of_patch` con la parte de
  `v`; la rama parcheada es de `P0` porque cada cláusula está entera fuera de la parte (la da `a0`) o entera en la parte
  y los separadores (la da la rama de `P`, que lee los separadores como `a0`).
* **T3** es `reading_inv_on` con una elección «buena» que dice: un separador, si es el siguiente de `S`; una variable
  que no es separador, si ya están todos. Las primeras usan T2; las segundas, T1 con `hsep` sacado de las elecciones
  ya hechas (como en `hRead_good`).
* **T2** es el trabajo de verdad: para cadenas de hasta cuatro bloques lo dan los casos de separador de
  `ForbidOnChain4` (valen con cualquier lectura previa). Para más bloques hay que extender el descenso con la parte
  izquierda congelada.

## 6. Medidas

`test_3sat/probe_reader_sep.jl`: desde cada estado final, el lector por separadores con la primera elección, y
lecturas con elección al azar en cada paso; en algunas, los estados leídos juzgados contra sus camarillas.

| fórmula | separadores | primera elección | al azar: lecturas / atascos / soluciones | estados juzgados / triángulos fuera / aristas fuera |
|---|---|---|---|---|
| `chain4_cross` | 3 | solución | 40 / 0 / 40 | 18 / **0** / 0 |
| `chain5_cross` | 4 | solución | 40 / 0 / 40 | 44 / **0** / 0 |
| `chain6_cross` | 5 | solución | 40 / 0 / 40 | — (estados demasiado grandes para enumerar camarillas) |

En `chain5_cross` el lector por separadores **no tiene triángulos fantasma** donde el lector en cualquier orden tenía 36
en 470 estados: la ventaja 3 de §2 (recuperar la exactitud) se confirma en la máquina.

## 7. Plan

1. ~~T1 en Lean~~ y ~~T3~~: hechos (§8).
2. ~~T2 para `chain5_cross`~~: hecho (§9).
3. Las líneas de `chain5_cross`: prefijos (`phantomAt_of_prefix`) más la última cláusula.
4. Si se adopta, llevar `PathSepReader` a `src/` y cambiar a quien llama; la tabla de sincronía Julia/Lean de
   `docs/plans/lean_bingo.md` tendría una fila «ReaderSep».

## 8. Lo demostrado tras el borrador (`Model/ForbidOnSepRead.lean`)

* **T1, `phantomFree_pinnedSepCover`**: como en §5, sin `sorry`.
* `phantomFree_fixedVar`: volver a fijar una variable que todas las ramas ya leen igual (un separador repetido).
* `reading_inv_gen` (`reading_inv_on` para cualquier predicado de elecciones buenas), `SepGood`,
  `goodAlong_of_sepFirst`. `SepFirst` y `SepPinFree` quedaron en forma de elemento a elemento (`R[i]?`), que es la
  misma condición y mucho más manejable.
* **T3, `reader_sep_on`**: como en §5, sin `sorry`.
* **`reader_sep_chain4Cross`**: el caso concreto; T2 sale de los lemas de separador de cuatro bloques
  (`sepPinFree_chain4Cross`).

## Ficheros

| fichero | qué es |
|---|---|
| `julia/improves_bingo/drafts/path_sep_reader.jl` | el borrador del lector |
| `julia/improves_bingo/test_3sat/probe_reader_sep.jl` | la sonda de §6 |
| `julia/improves_bingo/test_3sat/output_probes/hard4/sep_chain*.tsv` | sus resultados |
| (borrador de Lean en §5) | aún no está en el proyecto |

## 9. T2 en cinco bloques (`Model/ForbidOnChain5.lean`)

* `Chain5Data`: los bloques por una función de zona (interiores `0 … 4`, separadores `5`), así la disjunción entre
  interiores es automática. `glue5`, una fuente por bloque.
* **`phantomFree_chain5_s4`**: rango por el primer separador leído de `s3, s2, s1`; testigos de `σ`, del paso de `s3`,
  de la ventana `W2` (lee `s2`, `s3`) y de la ventana `W1` (lee `s1`, `s2`). Solo cuentas de cardinal.
* **`phantomFree_chain5_s3`**: los dos lados se pegan en `v`. Rango primero por la derecha (`s4` leído o no) y después
  por la izquierda (`s2`, `s1`, nada); la derecha sale de la ventana `W3`, la izquierda de `W2` o `W1`, y si se lee
  `s4`, de las dos caras por el nodo que lo lee (`c5s3_four`).
* **`sepPinFree_chain5Cross`**: T2 en `chain5_cross` con los dos lemas en las dos orientaciones (`x5`, `x6` leyendo la
  cadena al revés). **`reader_sep_chain5Cross`**: el lector por separadores no se atasca en `chain5_cross`, con las
  líneas como única hipótesis (la máquina las cumple: 0 fuera en todos los estados).
