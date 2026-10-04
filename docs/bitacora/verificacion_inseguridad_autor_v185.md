# Verificación para el Autor v185: los condenados mueren por parejas, Helly no viene de la forma de las tablas, y una regla de parejas tras la limpieza

Ricardo, soy Claude (Opus 5.5). Este informe sigue al v184. Allí la escalera del lector había quedado
en `hStart` y tres hipótesis por pin; desde entonces se redujo a **una sola** (`RoundExact`, commit
`0f94c49`), y las mediciones de estos días han ido a la pregunta de fondo: por qué la primera vuelta
de un pin deja todo tramo en una cadena completa. La respuesta que ha salido tiene dos partes. Una
buena: los tramos que la limpieza deja sin entrada común tienen **siempre** un conflicto de pareja,
que es información que la máquina ya sabe detectar. Y una que cierra un camino: la propiedad de tipo
Helly que necesitamos **no** sale de la forma de las tablas —ni árbol, ni intervalo, ni mayoría—,
porque las tablas son exactas y la fórmula liga más de dos variables a la vez.

Al final propongo una regla nueva para el review y dejo un borrador en Julia para que lo analices.

Rama `review-symmetric`. Sondas en `lean_project/Probes/RowDegree.lean`, modos `roundexact` y
`majority` (commits `987a909`, `afd6eca`, `4ecfa30`, `2394ef7`). Todas las mediciones: semillas 1 y 7,
12 fórmulas de 4+ variables cada una, 86 pines del lector.

---

## 0. Dónde estamos, en una línea

```lean
theorem readerVerdictW_iff_of_roundExact (hStart : …) (hPin : … → RoundExact (filterWeak g (q.id.step, [q.id])))
    (φ : Cnf) (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ

def RoundExact (X : GPathM) : Prop := isValid (reviewPass X) = true → SegExact (reviewPass X)
```

**La primera vuelta del review de cada pin deja todo tramo en una cadena completa.** Todo lo demás
—las vueltas siguientes, el barrido agresivo, el punto fijo— está demostrado a partir de eso
(`segExact_reviewAgg_of_round`). Medido: la limpieza del pin deja 74 + 12 tramos sin cadena (los
*condenados*) y a la salida de la primera vuelta no queda ninguno (0 de 18.000 tramos).

Lo que sabíamos del v184 sobre cómo mueren los condenados: en la pasada, al procesar su extremo, por
una pérdida de posesión mutua; y la propagación necesita las dos pasadas (`UnionToCommon`, falsa).
Demostrar eso por la dinámica de las pasadas nos llevaba siempre a lo mismo: pasar de «cada miembro
cubierto por algún vecino» a «todos por el mismo», es decir, a Helly.

## 1. Los condenados tienen siempre un conflicto de pareja

Para cada condenado y cada paso `b` sin entrada común del tramo, miré las entradas de cada miembro en
`b`. Dos posibilidades:

* **conflicto de pareja**: hay dos miembros `u`, `v` tales que ninguna entrada de `u` en `b` está en la
  tabla de `v`;
* **conflicto colectivo**: cada pareja comparte alguna entrada en `b`, y solo el conjunto falla (el
  caso «Helly» genuino).

| semilla | condenados | conflicto de pareja | de ellos, pareja contigua en el tramo | solo colectivo |
|---|---|---|---|---|
| 1 | 74 | 74 | 44 | **0** |
| 7 | 12 | 12 | 12 | **0** |

**Todos** los condenados son de pareja. Y esa información ya la sabe leer la máquina: es la rama
«inconsistente» del filtro agresivo (`aggPair` en el modelo, el `intersect!` + `is_valid` de
`agressive_consistence_filter!` en Julia): si dos nodos se poseen y sus tablas no comparten nada en
algún paso, se deshace la posesión en las dos direcciones. El problema es **cuándo** actúa: después
del review base. Por eso hoy a los condenados los mata la propagación de las pasadas, que es lo que no
sabemos demostrar.

## 2. Helly se cumple, pero no por la forma de las tablas

Si la regla de parejas actuara antes (§5), lo que quedaría por demostrar sería: *si todas las parejas
de un tramo comparten entrada en cada paso, el tramo tiene una entrada común*. Eso es una propiedad de
Helly de las tablas, y para conjuntos cualesquiera es falsa (`{a,b}`, `{b,c}`, `{a,c}`). Así que medí
si nuestras tablas tienen alguna de las formas en las que sí es un teorema.

Medido en los estados del lector y en la salida de la limpieza de cada pin:

| qué | semilla 1 | semilla 7 |
|---|---|---|
| tríos de nodos que se poseen mutuamente, dos a dos con entrada común en un paso | 2.303.347 | 3.030.344 |
| … **sin entrada común a los tres** | **0** | **0** |
| tablas (nodo × paso) | 62.321 | 79.575 |
| no son subárbol completo del árbol de prefijos de la ventana (antigua primero / reciente primero) | 4.837 / 5.467 | 4.510 / 4.312 |
| no son intervalo en ese orden | 3.814 / 4.195 | 3.111 / 2.997 |
| parejas mutuas cuyas tablas no son ni anidadas ni disjuntas (de 509.876 / 642.312) | 11.577 | 11.451 |

Helly para tríos se cumple siempre, pero **las tablas no son subárboles, ni intervalos, ni una familia
laminar**: entre el 2 % y el 8 % se salen de cada una de esas formas. La explicación tiene que estar en
otra parte.

## 3. La mayoría: casi siempre, y lo que falla es exacto

El siguiente candidato era el clásico de este tipo (Baker–Pixley): si cada tabla, vista como conjunto de
asignaciones, es **cerrada por mayoría bit a bit** —los conjuntos que se escriben con cláusulas de dos
literales—, entonces «dos a dos ⇒ todos» es un teorema. Encajaría con que las tablas solo guardan
información de parejas.

Para medirlo, cada ventana `(gparent, parent, id)` se traduce a las variables que fija, tal como las
construye el mapa: paso `2v` → `v = i`; paso `2v+1` (`"!v=i"`) → `v = 1-i`; fila `r ∈ 1..7` de una
cláusula → cada literal con su bit de `r` (la fila 000 no existe; las siete filas son las siete formas
de satisfacerla). En todos los pasos la traducción es limpia: ninguna ventana fija una variable a dos
valores, todas las ventanas de un paso fijan las mismas variables, y distintas ventanas dan distintas
asignaciones.

| | semilla 1 | semilla 7 |
|---|---|---|
| tablas | 62.321 | 79.575 |
| no cerradas por mayoría | 251 (0,4 %) | 124 (0,16 %) |
| la mayoría cae en una asignación **sin nodo** (la fila 000 de una cláusula o una combinación que ninguna ventana representa) | 249 | 124 |
| la mayoría cae en una ventana **viva que la tabla no tiene** | **2** | **0** |

Todos los fallos están en pasos de cláusula. Los «sin nodo» son los huecos del propio mapa: la mayoría
de `100`, `010`, `001` es `000`, que no es fila. Esos huecos no contradicen la estructura, pero son
justo donde el teorema clásico deja de aplicarse.

## 4. Los dos casos vivos: la tabla tiene razón

Los dos casos son el mismo, visto desde dos nodos que fijan `x0 = 1` (`0/1` y `1/0<0/1`), en el estado
final del lector (paso 19), en el paso 18. En la tabla hay tres ventanas cuya mayoría es
`x2=1, x3=1, x4=1, x5=0`, que es una ventana viva (`18/0<17/6<16/7`) que la tabla no contiene.

Fuerza bruta sobre la fórmula `(¬x2 ∨ x1 ∨ ¬x3) (x2 ∨ ¬x4 ∨ x0) (¬x4 ∨ ¬x1 ∨ ¬x0) (x3 ∨ x2 ∨ x4)
(x4 ∨ x2 ∨ x5)`: con `x0 = 1` hay 14 soluciones; cada una de las tres ventanas tiene 1 solución con
`x0 = 1`; **la mayoría no tiene ninguna**. La exclusión es real y pasa por `x1`, que no está en la
ventana:

* `(¬x4 ∨ ¬x1 ∨ ¬x0)` con `x0 = x4 = 1` obliga a `x1 = 0`;
* `(¬x2 ∨ x1 ∨ ¬x3)` con `x2 = x3 = 1` obliga a `x1 = 1`.

**La tabla es exacta y no es cerrada por mayoría.** Las restricciones de la fórmula ligan más de dos
variables —aquí `x0, x2, x3, x4` a través de `x1`— y una tabla exacta las refleja. Así que «las tablas
son cerradas por mayoría» es falso en general; el 99,6 % de antes era por lo pequeñas que son las
fórmulas, no por la máquina. **La vía de Baker–Pixley queda cerrada.**

Y eso dice de dónde tiene que salir la propiedad de Helly que sí medimos (0 fallos en 5,3 millones de
tríos): no de cada tabla por separado, sino de que son exactas y de cómo se encadenan los miembros de
un tramo —pasos consecutivos, enlaces de padres e hijos—. Es decir, de la estructura de cadena, no de
la geometría de los conjuntos.

## 5. Propuesta: la regla de parejas justo después de la limpieza

### 5.1 La regla

> Tras `cleanInvalid₂`, para cada pareja de nodos vivos `x`, `w` con `w` en la tabla de `x`: si hay un
> paso en el que sus tablas no comparten ninguna entrada, `w` sale de la tabla de `x` **y** `x` sale de
> la de `w`. Se repite, con la purga de la limpieza en medio, hasta que no cambie nada. Después vienen
> las pasadas como hasta ahora.

No es una regla nueva en contenido: es la rama «inconsistente» del filtro agresivo, adelantada al
momento en que el pin deja los tramos sin entrada común.

**Es correcta** (no pierde soluciones), por el mismo argumento que la rama agresiva: si una solución
pasa por `x` y por `w`, pasa por un nodo `r` en el paso `b`, y `r` está en las dos tablas —la máquina
conserva en cada tabla todos los nodos de las soluciones que pasan por su dueño (no-solución-perdida,
ya demostrado para el review)—. Si en `b` no comparten nada, ninguna solución pasa por los dos, y
deshacer la posesión mutua no pierde ninguna.

### 5.2 Qué gana la demostración

1. **Los condenados mueren en un paso local, con prueba directa.** Medido: los 86 tienen un conflicto
   de pareja (§1). La regla los rompe en la limpieza misma, sin propagación por las pasadas, sin
   uniones de padres, sin `UnionToCommon`.
2. **`RoundExact` pasa a ser una afirmación sobre un único estado.** Tras limpieza + parejas, el estado
   cumple `PairOk`: toda pareja que se posee comparte entrada en cada paso. Lo que quedaría es

   ```lean
   /-- Helly de pareja: en un estado con `PairOk`, todo tramo tiene entrada común en cada paso. -/
   def PairHelly (C : GPathM) : Prop := PairOk C → SegGood C
   ```

   y con `SegGood` a la entrada de las pasadas, lo demás ya está demostrado: las pasadas conservan
   `SegGood` nodo a nodo (`segGood_reviewNode_parents/sons`), las limpiezas siguientes son la
   identidad (`cleanInvalid₂_eq_self_of_ready`), y `SegGood` en el punto fijo da `SegExact`.
   **Desaparece la dinámica** de la hipótesis por pin: ni vueltas, ni orden de las pasadas.
3. **Se puede medir directamente y en un solo sitio.** `PairHelly` es una propiedad de un estado; la
   sonda es: tras limpieza + parejas, ¿algún tramo sin entrada común? Por §1 y §2 debería salir 0.

### 5.3 Qué no resuelve

No elimina Helly: lo deja **aislado**. `PairHelly` es la dificultad de tipo Helly en su forma más limpia
(un estado, sin pasadas), y §3–§4 dicen que no se demostrará por la forma de las tablas, sino por su
exactitud y la estructura de cadena. Es la pieza que quedaría abierta, ahora con un enunciado estático
y medible.

Y hay que comprobar que la regla no cambia lo que la máquina decide. Debería dar los mismos estados
finales —el filtro agresivo ya quitaba esas parejas, solo que más tarde—, pero el orden puede cambiar
las vueltas intermedias y eso hay que medirlo, como con el espejo (A5 del v184).

### 5.4 Obligaciones nuevas en Lean (si se adopta)

* `pairSweep` en el modelo (`GPathM.lean`), con su punto fijo junto a `cleanInvalid₂`.
* `Pruned` de `pairSweep` (solo quita entradas): la mayoría de lemas de forma pasan gratis.
* `OwnSymmetric_pairSweep`: quita las dos direcciones, así que conserva la simetría (como
  `aggPair_asym_never`).
* `PStateG` tras la purga que sigue a la regla: la purga ya está cubierta; hay que ver que la regla no
  deja vivos fuera de su propio corte (`self_in_cut`).
* `PairOk` en su punto fijo (por construcción).
* La escalera: `readerVerdictW_iff_of_pairHelly`, con `hStart` y `PairHelly` por pin.

## 6. Borrador en Julia

Para `julia/improves/src/graph_path/graph_path_filter.jl`, detrás de un interruptor como `SYM_MODE`.
Está en `:off` hasta medir.

```julia
# Regla de parejas tras la limpieza (informe v185, §5).
#   :off — (por defecto hasta medir) el review de siempre.
#   :on  — tras clean_invalid_nodes!, se deshacen las posesiones mutuas de parejas cuyas tablas no
#          comparten nada en algún paso (la rama «inconsistente» del filtro agresivo, adelantada).
const PAIR_MODE = Ref(:off)

# Contadores (solo para medir; no cambian nada).
const PAIR_REMOVED = Ref(0)   # parejas deshechas por la regla
const PAIR_ROUNDS  = Ref(0)   # vueltas regla + purga dentro de una limpieza

function make_review_owners!(gpath :: GPath)
    #! [recursive-if] $ O(S*7*7) $
    if gpath.is_valid && gpath.review_owners
        REVIEW_ROUNDS[] += 1
        gpath.review_owners = false
        clean_invalid_nodes!(gpath)
        if PAIR_MODE[] == :on
            pair_consistency_after_clean!(gpath)
        end
        review_owners_coherence_with_its_parents_sons!(gpath)

        agressive_consistence_filter!(gpath)
        chain_consistence_filter!(gpath)

        if gpath.review_owners
            make_review_owners!(gpath)
        end
    end
end

# ¿Comparten las dos tablas al menos una entrada en cada paso que tienen las dos?
# Versión simétrica y sin copia de `intersect!` + `is_valid` (la del filtro agresivo).
function shares_every_step(owners_a :: PathDocOwners, owners_b :: PathDocOwners) :: Bool
    #! [for] $ O(S) $
    for (step, set_a) in owners_a.table
        set_b = PathDocumentOwners.get(owners_b, step)
        set_b === nothing && continue
        # se recorre la línea más corta y se pregunta en la otra
        short, long = length(set_a) <= length(set_b) ? (set_a, set_b) : (set_b, set_a)
        #! [fixed] $ O(7) $
        any(id -> id in long, short) || return false
    end
    return true
end

# Punto fijo de «regla de parejas + purga». Cada vuelta que sigue ha deshecho al menos una pareja,
# así que termina. La purga va dentro porque deshacer una pareja puede dejar un paso vacío en una
# tabla (nodo inválido), y eliminar ese nodo encoge la global y corta otras tablas.
function pair_consistency_after_clean!(gpath :: GPath)
    changed = true
    #! [while] $ O(N*7) $ vueltas como mucho
    while changed && gpath.is_valid && gpath.table_lines.is_valid
        changed = false
        PAIR_ROUNDS[] += 1
        #! [fn-iter] $ O(S*7*7) $
        PathCollectionLines.for_each(gpath.table_lines, function (node_x)
            #! [for] $ O(S) $
            for step_w in 0:gpath.current_step-1
                ids_w = PathDocumentOwners.get(node_x.owners, step_w)
                ids_w === nothing && continue
                #! [for] $ O(7*7) $  — copia: la tabla cambia dentro del bucle
                for node_id_w in collect(ids_w)
                    node_id_w == node_x.id && continue
                    node_w = PathCollectionLines.get_node(gpath.table_lines, node_id_w)
                    node_w === nothing && continue          # id muerto: lo quita el corte de clean
                    #! [fixed] $ O(S*7) $
                    if !shares_every_step(node_x.owners, node_w.owners)
                        # ninguna solución pasa por los dos: la posesión se deshace en las dos
                        # direcciones (con SYM_MODE :on, la simetría se conserva)
                        PathDocumentNode.remove_owner!(node_x, node_id_w)
                        PathDocumentNode.remove_owner!(node_w, node_x.id)
                        PAIR_REMOVED[] += 1
                        gpath.review_owners = true
                        changed = true
                    end
                end
            end
        end)
        if changed
            clean_invalid_nodes!(gpath)   # purga + corte con la global final
        end
    end
end
```

Notas para el análisis:

* **Coste**: una pasada es `O(S·7·7 · S·7 · S·7)` en el peor caso, del orden del filtro agresivo, que
  hace lo mismo. En la práctica debería ser mucho menos: tras la limpieza casi todas las parejas
  comparten, y `shares_every_step` corta en el primer paso que falla.
* **`shares_every_step` frente a `is_valid_intersect`**: la segunda no es simétrica (devuelve `false`
  si `owners_b.max_step > owners_a.max_step`). Para esta regla conviene la simétrica, o `x` y `w` se
  juzgarían distinto según el orden.
* **Pasos que tiene una tabla y la otra no**: aquí se ignoran, igual que en
  `PathDocumentOwners.intersect!` (solo corta los pasos que tienen las dos). Lo único que el borrador no
  copia es la regla de `max_step` de `intersect!` (`owners_b.max_step > owners_a.max_step` invalida);
  dentro de un mismo `gpath` todas las tablas deberían llegar al mismo paso, pero conviene contarlo en
  la medición.
* **Espejo**: la regla quita las dos direcciones, así que no rompe la simetría, y la rama «asimétrica»
  del agresivo debería seguir en 0.

### Cómo medirla (propuesta)

1. `test_3sat/compare_pair.jl`, como `compare_sym.jl`: 80 instancias con `PAIR_MODE` `:off` y `:on`.
   Mismos veredictos, mismos estados finales, vueltas, tiempo, `PAIR_REMOVED`, y un contador nuevo en
   la rama «inconsistente» del agresivo, que con `:on` debería bajar mucho o a 0.
2. En Lean, sonda `pairhelly`: en los 86 pines, tras limpieza + regla, ¿algún tramo sin entrada común?
   Por §1–§2 debería ser 0. Es la medida directa de `PairHelly`.
3. Solo si las dos salen bien: la regla al modelo y al ejecutable (como el espejo en B0–B4) y la
   escalera nueva.

## 7. Una frase

Los tramos que la limpieza de un pin deja sin entrada común no esconden un conflicto colectivo: todos
tienen dos miembros incompatibles, y la máquina ya sabe verlo, solo que tarde. Adelantar esa regla
convertiría la última hipótesis del lector en una afirmación de Helly sobre un único estado. Y la
medición de la mayoría dice dónde buscar su prueba: no en la forma de las tablas, que son exactas y por
eso reflejan restricciones de más de dos variables, sino en cómo se encadenan.
