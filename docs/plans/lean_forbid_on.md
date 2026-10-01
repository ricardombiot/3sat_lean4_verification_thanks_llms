# Plan: el modo `FORBID=:on` de Julia, reflejado en `lean/improves_bingo`

30-sept-2026, rama `reader-stuck`. Origen: el informe v216. Lean modela la máquina `:off` con familias fantasma, y
todas las medidas de la rama se hicieron con `:on`. Decisiones de Ricardo:
1. un **parámetro de modo** (`:off` queda definicionalmente igual);
2. los tríos **en las aristas, como Julia**;
3. **también la herencia del UP** (`up_forbid!`);
4. revertir `TriClq` (hecho, `c693d31`).

## Estado (30-sept-2026)

| fase | commits | resultado |
|---|---|---|
| F1 modelo | `e11aa73` | `GPathB.trios`, `ForbidOn.lean`, máquina con modo (`runM`); `.off` = lo de siempre por `rfl` |
| F2 diferencial | `a18b59b` | índice hash; **Lean = Julia `:on`** en `clause_mix` (1 472 líneas, 947 aristas con tríos), `v4_c12_i1` (469), `clause_mix_sep` (2 345, 1 724); `:off` en `clause_mix` (525) |
| F3 contabilidad y cierre | `0cf4677`, `eddcaae`, `028db8f` | `revPrims_reviewOn`; **`closedState_reviewOn`**; el índice dice lo mismo que las listas |
| F3 solidez | `f4d40c4`, `b9a97e4`, `ed6b2ab` | la rama solución esquiva los tríos reales por regla, review, filtro, join y UP (`CT`); **`machineVerdictOn_of_sat`** |
| F3/F4 forma y veredicto | `a948b61` | **`spineVerdictOn_iff_of_liveExt`**: la espina `:on` decide la satisfacibilidad si los estados finales revisados cumplen `LiveExt` con sus propios tríos (`TF`). Sin familias fantasma |
| F4 `LiveExt` por operación | `a30ace0`, `a994f21`, `48aeab5`, `5d7dd82` | review y UP sin hipótesis; join bajo (★) con los tríos reales (`ForbidOnLive.lean`) |
| F4 llegada fijada | `b4bc73f`, `5289cd8`, `77e3f02`, `7ea78ae`, `becd957` | la regla llega a su punto fijo; direcciones 2 y 1; **`good_arrivalOn` sin hipótesis** (`ForbidOnFix`, `ForbidOnPin`, `ForbidOnArr`) |
| F4 join fijado e inducción de línea | `2f194ac`, `fec9f47`, `f00186b` | `good_joinAt` bajo `PinSideAt`; el recíproco sin hipótesis (`ForbidOnSide`); `LInvOn`; **`spineVerdictOn_iff_of_joinOn`**: la espina `:on` decide bajo `PinSideAt` en los joins de la máquina, solo para los pins de `PinsFrom` |
| F4 invariante de cimas | `0102019` | `TopAt`, `topAt_arrival` sin hipótesis, **`spineVerdictOn_iff_of_topOn`** bajo `TopSideAt` en los joins (`ForbidOnTop`): la hipótesis mínima, de nodos |
| F4 `TopSideAt` en piezas | `4521816` | `sideGraph` demostrado; `topSideAt_of_parts` bajo `TopKeepAt` + `TriSideAt`; **`spineVerdictOn_iff_of_parts`** (`ForbidOnParts`) |
| F4 la estrella de la cima | `4c65e95`, y el siguiente | `downInv_pinOnK`, `AdjPar`, `star_alive`, **`spineVerdictOn_iff_of_starTri`** bajo `StarTriAt` (`ForbidOnKeep`, `ForbidOnStar`): la hipótesis ya es solo de tríos |

Lo abierto, en su forma más estrecha (1-oct-2026): **`StarTriAt`** en los joins de la máquina: en la unión fijada, un
triángulo entre vecinos de una cima, vivo y con sus tres caras con la cima vivas, no está en la lista de tríos del lado
fijado de esa cima (`probe_startri.jl`, columna `m3_dead`). Implica **`TopSideAt`** en los joins de la máquina: toda cima viva de la unión
fijada `pinOn (joinOn A B) R` está viva en `pinOn A R` o en `pinOn B R` (`probe_pinside.jl`, columnas `tops` /
`top_none`). La versión de cadenas, más fuerte, es **`PinSideAt`** en los joins de la máquina: toda cadena viva de la unión fijada
`pinOn (joinOn A B) R` es cadena viva de `pinOn A R` o de `pinOn B R`, con los tríos de ese lado. El recíproco está
demostrado (`pinSideAt_iff`). La mide `probe_pinside.jl` (`FORBID=:on`; `PIN_MODE=real` para los pins de `PinsFrom`).

## Qué hace Julia `:on` (el objetivo del espejo)

| Julia | dónde | qué hace |
|---|---|---|
| `Edge.forbid` | `path_owners_graph.jl` | cada arista `a–b` guarda los `r` con el trío `(a,b,r)` prohibido |
| `forbid!(g,a,b,r)` | idem | lo escribe en las tres aristas del trío, a la vez |
| `dead_trio(g,a,b,r)` | idem | `r ∈ forbid(a–b)`; solo se consulta con la arista `a–b` presente |
| `side_forbids(g,a,b,r)` | idem | falta una de las tres aristas, o `dead_trio` |
| `remove_edge!`, `remove_node!` | idem | la arista desaparece con su `forbid` |
| `create_from_parents!` + `up_forbid!` | `graph_path_up.jl:93-94` | aristas nuevas `n–w` sin tríos; después, `(n,w,r)` si **todo** padre `p` cumple `side_forbids(p,w,r)` |
| `union!` + `join_forbid` + `set_forbid!` | `path_owners_graph.jl` | unión de vivos y aristas; **se borran todos los `forbid`** y se ponen los de `join_forbid`: `(a,b,r)` si los dos lados, **sin fijar**, lo cortan |
| `forbid_rule!` | `graph_path_forbid.jl` | en el review, tras la limpieza y las parejas, mientras cambie algo: (1) prohíbe los tríos sin testigo bueno en algún paso; (2) quita a la vez las aristas sin testigo bueno y, si quitó alguna, `review_owners = true` y `clean_invalid_nodes!` |
| orden del review | `graph_path_filter.jl` | limpieza → parejas → **regla** → enlaces → padres/hijos → enlaces → (vuelta o comprobación final) |

## Representación en Lean

Un campo nuevo en `GPathB`: `forb : List (PathNodeId × PathNodeId × PathNodeId)`, los tríos escritos con
`forbid!` desde el último join, y la consulta con la guarda de Julia:

    deadTrio g a b r := g.hasEdge a b ∧ (el trío {a,b,r} está en forb, en cualquier orden)

Es **observablemente lo mismo que guardarlos en las aristas**:
* Julia escribe el trío en sus tres aristas a la vez, y una arista borrada nunca vuelve a crearse con su `forbid`
  viejo: el UP solo crea aristas con el nodo nuevo, y el join reinicia todos los `forbid`.
* Así, `r ∈ forbid(a–b)` en Julia ⟺ `a–b` existe y `{a,b,r}` se prohibió desde el último join ⟺ `deadTrio` en Lean.
* El volcado para el diferencial escribe, por arista, `{r | {a,b,r} ∈ forb}`: el mismo conjunto que Julia.

Con `:off` el campo vale siempre `[]`, y ninguna operación `:off` lo toca.

## Fases (cada una con commit, y el diferencial como puerta)

**F1 — el modelo.** `Mode := off | on` y:
* `GPathB.forb`, `deadTrio`, `sideForbids`, `forbidTrio`;
* `upForbid` tras la fila nueva;
* `joinForbid` (sobre los lados sin fijar) y el reinicio en el join;
* `forbidRule` en dos fases, a punto fijo con combustible, con la limpieza tras cortar;
* `reviewPassM m`, `reviewFuelM m`, `reviewM m`, `filterAllM m`, `upM`, `doJoinM`, `advanceM`, `runM`.

Criterio: con `m = off`, cada función es **por definición** la de hoy (`rfl`), así que no se rompe ningún teorema.
Todo computable, para el diferencial.

**F2 — el diferencial (la puerta).** `bingo-dump --forbid on` vuelca además los tríos por arista, y
`compare_bingo.jl` corre contra Julia `FORBID=:on`, en instancias pequeñas y con `run_capped.sh`. Criterio: mismos
veredictos, vivos, aristas y tríos. Hasta que salga igual no se sigue.

**F3 — contabilidad.** `RevPrims` con la primitiva nueva (cambiar `forb`); `EdgesAlive`, `NodupIds`, `LinksInv`,
`Struct`, `MapLinks` y `Carried` por la regla (`carried_forbidSweep` ya existe). Hay que rehacer la terminación del
review: la medida cuenta también los tríos que faltan por prohibir.

**F4 — la inducción de línea sobre tríos reales.** La familia en `R` pasa a ser la de los tríos de `pinF g R` en
modo `:on`, y dejan de hacer falta las familias fantasma. Se re-enuncian `Good`, `FamMono`, `PinJoinSplitAll` (con
tríos) y `HClq`, y el veredicto pasa a ser el de la máquina `:on`.

**F5 — medir** las hipótesis resultantes en Julia `:on`, que ya será el espejo.

## Riesgos

* **Orden de recorrido:** Julia recorre `Dict`s en orden de hash. Las dos fases de la regla deciden contra el mismo
  estado, así que el orden no debería importar. El diferencial lo comprueba.
* **La terminación de la regla:** los tríos crecen dentro de un universo finito (vivos³), y las aristas solo bajan.
* **El tiempo:** con `:on`, Julia es lenta (v216 y la medida de tiempos). El diferencial se queda en instancias
  pequeñas.
