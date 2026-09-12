# Verificación para el Autor v58: el lector, tal y como lo diseñaste — ensamblado

Ricardo, soy Claude (Opus 5). Tenías razón en la corrección. Fui a leer `PathReader` y `filter!` en el original, y el proceso que describes **ya estaba formalizado como inducción** en el desarrollo; lo que faltaba era el ensamblaje para el filtrado **repetido**. Está hecho.

---

## 1. El mecanismo, leído del original

`PathReader.read_step!` hace tres cosas y repite:

```julia
select_id!(reader)        # first(ids) del paso actual; se queda con su id de MAPA
register_selection!       # anota el bit y decide si ha terminado
filter_gpath!(reader)     # GraphPath.filter!(gpath, requires); si no es válido -> ERROR GRAVE
```

y `filter!` es:

```julia
filter!(gpath, requires) = for r in requires; filter_require!(gpath, r); end; make_review_owners!(gpath)
```

- **`filter_require!`** elimina, en el paso de la selección, todo owner global que nombre **otro** nodo de mapa. Eso es literalmente tu «asumimos que hemos seleccionado todos los owners»: el conjunto queda reducido a lo compatible con el nodo elegido.
- **`make_review_owners!`** es recursivo: `clean_invalid_nodes!` + la pasada de coherencia, **hasta que la bandera deja de levantarse** — el punto fijo, «podría requerir varias iteraciones».
- El lector **aborta** si el grafo deja de ser válido. Nunca retrocede.
- Y termina cuando no queda nada que elegir: **un nodo de mapa por paso**, que es una solución.

El espejo Lean reproduce esto exactamente: `filterRequire`, `reviewPass = reviewSons ∘ reviewParents ∘ cleanInvalid`, `review = reviewFuel` hasta el punto fijo, `filterAll = review ∘ folds de filterRequire`.

## 2. Lo que ya estaba, y lo que faltaba

Tu proceso **es** `PickInduction.Inhabited_of_pickSome`: la medida decrece en cada ronda (`measure_lt_of_choiceAt`), así que el bucle acaba, y el caso base —sin elección— lo cierra `Pinned.inhabited_of_noChoice`, que es exactamente tu paso 5: **un owner por paso ⟹ `pairwiseOwned_of_fullyPinned` ⟹ el estado denota una solución**.

Lo que faltaba es que esa inducción pide una clase `P` **cerrada bajo `filterAll`**, y todos los invariantes de la librería estaban enunciados para **un** `filterAll` aplicado a un estado `Reachable`. El lector pina una y otra vez. Sin la clase, el teorema no se podía instanciar.

## 3. Pieza nueva 1: la lista de ids solo encoge

`NodupIds` —ids de nodo distintos dos a dos— era la hipótesis que `Filter.lean` y `PickInduction.lean` piden y **nadie descargaba**.

`Model/NodeIds.lean`: toda operación del bucle de review hace una de dos cosas con la lista de nodos — **mapearla** con una función que no toca `id` (`updateAt`, `unlinkIncompatible`) o **filtrarla** (`removeNode`). Así que la lista de ids es una sublista de lo que era:

```lean
theorem NodupIds_filterAll (g : GPathM) (h : NodupIds g) (reqs : List NodeId) :
    NodupIds (filterAll g reqs)
```

Con eso el lector puede pinar tantas veces como quiera sin volver a suponer nada.

## 4. Pieza nueva 2: la clase del lector

`Model/Reader.lean`. `RCtx` empaqueta los siete invariantes de origen —`OOS`, `SNN`, `GN`, `Shape`, `RootAtZero`, `PMP`, y ahora `NodupIds`— cada uno con su transferencia *invariante → invariante* (no la versión `Reachable`), así que:

```lean
theorem RCtx_filterAll (g : GPathM) (h : RCtx g) (reqs : List NodeId) : RCtx (filterAll g reqs)

def Readable (g : GPathM) : Prop := ∃ g₀ reqs, RCtx g₀ ∧ g = filterAll g₀ reqs
```

`Readable` es «un estado pinado de un estado de la clase», y es cerrada bajo pinado por construcción. Sobre ella:

- `Ctx_of_readable` — el contexto de punto fijo, desde la clase en vez de desde `Reachable`;
- `exists_isChain_of_readable` — el descenso de v27, sin hipótesis de positividad (con `current_step ≤ 0` la cadena es vacua);
- `inhabited_of_noChoice_readable` — **tu paso 5**, sobre la clase.

## 5. Pieza nueva 3: los ids de la máquina son únicos

Y como ya no hay que suponer `NodupIds`, se puede demostrar de raíz:

```lean
theorem NodupIds_reachable (g : GPathM) (h : Reachable reqOf g) : NodupIds g
```

> Semilla: un nodo. `up`: el recién llegado está en `current_step` y todo lo demás estrictamente por debajo. `join`: la unión se toma por id, así que lo de `g₂` que se añade es justo lo que `g₁` no tenía.

## 6. El resultado

```lean
theorem Inhabited_of_pickSome_machine (g : GPathM) (reqs : List NodeId)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true)
    (hpick : ∀ h', Readable h' → isValid h' = true → PickInduction.PickSome h') :
    Inhabited (filterAll g reqs)
```

> **Selecciona, pina, revisa hasta el punto fijo; repite.** La medida cae en cada ronda, así que el bucle termina; termina sin elección; y ahí el estado denota una solución.

Cierre `[propext, Quot.sound]`, 0 `sorry`, 0 axiomas de proyecto. **Una sola hipótesis**: que en un paso que aún tiene elección, *alguna* selección sobreviva al review. Que es exactamente el `throw("GRAVE ERROR READER")` de tu código: la línea que dice que eso no debe pasar nunca.

## 7. Cómo está esa hipótesis, medida

| medición | resultado |
|---|---|
| `--randomread` (pinar + propagar, 40 casos, 3.808 estados, 116.330 nodos) | **40/40**, 0 inconclusos |
| `--pickvalid` (semilla 31337): estados con elección | 2.759, **0 sin selección buena** (`PickSome`) |
| `--pickvalid`: selecciones individuales | 64.144, **0 que invaliden** (`PickValid`) |

## 8. Y una rectificación

Los informes v54–v57 atacaban `support` / `ExtendDownTop` / `GoodParentOnCliques`: enunciados sobre **posesión dos a dos, sin propagación**. Tú me has señalado que el lector no hace eso — pina y propaga después de cada elección. Y es cierto, y cambia el balance:

- lo de v54–v57 sigue siendo válido como matemática (y `Inhabited_of_GoodParentOnCliques` sigue demostrado), pero es una ruta **más difícil de lo necesario**: mide un mecanismo más débil que el de tu máquina. `Extendable` sin propagación está refutado; **con** propagación no se atasca nunca;
- la ruta correcta es esta, y es la que ahora está ensamblada de punta a punta.

## 9. Estado

| | |
|---|---|
| Mitad de completitud (conservación + driver) | cerrada |
| S1 / S2 | cerrados |
| `NodupIds` bajo pinado | **demostrado** |
| `NodupIds` de todo estado de la máquina | **demostrado** |
| Clase cerrada bajo pinado repetido (`Readable`) | **demostrada** |
| Caso base (un owner por paso ⟹ solución) | demostrado (v19 + hoy sobre la clase) |
| **Bucle del lector ⟸ `PickSome`** | **demostrado** |
| `PickSome` | abierto — 0 fallos en 2.759 estados / 64.144 selecciones / 40 campañas `--read` |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, **87 módulos**, 0 `sorry`, 0 axiomas de proyecto.

---

*Claude (Opus 5), 2026-09-11.*
