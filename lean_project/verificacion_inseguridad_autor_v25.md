# Verificación para el Autor v25: `GownersAreNodes`, demostrado para toda la máquina

Ricardo, soy Claude (Opus 5). Atacado `GownersAreNodes`, el invariante que el contraejemplo de v24 sacó a la luz. Está **demostrado**, de punta a punta. Y de paso corrijo un error de v24 que hacía parecer el problema mucho peor de lo que era.

---

## 1. La corrección: me equivoqué de dirección

En v24 escribí que **`filterRequire` rompe temporalmente este invariante**, y que por eso solo valía en los puntos fijos. Es falso.

- `GownersAreNodes` es **gowners ⊆ nodes**: todo owner global es un nodo.
- `filterRequire` **encoge** `gowners` y **no toca** los nodos.

Encoger el lado izquierdo de una inclusión no la rompe. `filterRequire` lo preserva sin despeinarse.

Lo que `filterRequire` sí rompe es la **recíproca** — `nodes ⊆ gowners`, nodos cuyo id ya no es owner global — y `review` es quien limpia esos. **Tenía las dos direcciones intercambiadas.**

Y la consecuencia de la corrección es buena: el invariante no vive solo en los puntos fijos. Vale en todas partes, y por tanto se puede demostrar por inducción sobre la máquina entera.

---

## 2. Demostrado, operación por operación

`Model/GownersNodes.lean`, en la misma forma que `Pruned.lean`:

| operación | por qué |
|---|---|
| `filterRequire` | encoge `gowners`, deja los nodos |
| `updateAt` | no toca `gowners`; el update preserva los `id` |
| `removeNode` | quita el owner **y** su nodo a la vez |
| `cleanInvalidGo` / `cleanInvalid` | composición de los dos anteriores |
| `reviewNode` / `reviewLine` / `reviewSteps` | ídem |
| `reviewPass` / `reviewFuel` / `review` | ídem |
| `addNode` | añade el owner nuevo **junto con** su nodo |
| `up` / `upFiltering` | composición |
| `join` | ambas ramas aportan sus nodos |
| `initSeed` | la semilla |

Y con eso:

```lean
theorem GownersAreNodes_reachable (g : GPathM) (h : Reachable reqOf g) :
    GownersAreNodes g

theorem GownersAreNodes_filterAll (g : GPathM) (reqs : List NodeId)
    (h : Reachable reqOf g) : GownersAreNodes (filterAll g reqs)
```

La segunda es la que importa: los intermedios filtrados son justo donde vive la obligación.

Cierre `[propext, Quot.sound]`.

---

## 3. El corolario que hace el trabajo

```lean
theorem node_at_every_step (g : GPathM) (reqs : List NodeId) (h : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true) (k : Int) (hlo : 0 ≤ k)
    (hhi : k < (filterAll g reqs).current_step) :
    ∃ n ∈ (filterAll g reqs).nodes, n.id.id.step = k
```

Tu `isValid` dice *"hay un owner global en cada paso"*. Este invariante lo convierte en:

> **hay un nodo en cada paso.**

Que es exactamente lo que a `degenerate` le faltaba, y por eso lo tumbaba. La clase entera de contraejemplos degenerados queda eliminada.

---

## 4. Qué queda, y qué no

Esto **no** cierra la obligación. Que haya un nodo en cada paso no dice que se pueda **seleccionar uno por paso** de forma que estén encadenados padre→hijo y que se posean mutuamente. Eso sigue siendo `FilteredChain`, y sigue abierto.

Lo que sí ha cambiado:

- La obligación puede ahora **suponer** que hay algo que seleccionar en cada paso. Antes no podía, y por eso la versión sin `Reachable` era falsa.
- El invariante está disponible **explícitamente** en vez de escondido dentro de `Reachable`, así que cualquier intento futuro puede usarlo sin volver a derivarlo.

---

## 5. Una nota técnica que merece quedar escrita

`hasNode_iff` —el puente entre "algún nodo lleva este id" y `(node? q).isSome`— casi se cuela con `Classical.choice`: la prueba corta pasa por `List.isSome_find?` de Std, que es clásico. Sustituido por una inducción propia sobre la lista con `List.find?_cons_of_pos` / `_of_neg`, indicando el predicado explícitamente (sin eso, el elaborador unifica mal y falla).

Es la enésima vez que un lema de conveniencia de Std arrastra `Classical.choice`. Los `#guard_msgs` lo cazaron otra vez.

---

## 6. Dónde queda todo

| | estado |
|---|---|
| `FilteredChain` | **la obligación**, abierta |
| `GownersAreNodes` | **demostrado** para toda la máquina (v25) |
| `MachineOk` | demostrado (v22) |
| `Certifies` seed / join | demostrados (v21) |
| condiciones laterales de `ChainSound_upFiltering` | demostradas (v22) |
| `measure` decrece en el descenso | demostrado (v19) |
| el checker de `Supported` | demostrado (v16) |
| ~~`ArcImpliesChain`~~ | refutado (v24) |
| ~~`Extendable`~~ | refutado (v18) |
| ~~aciclicidad / BFMY~~ | cerrada (v17) |

---

*Claude (Opus 5), 2026-09-09. Corrige la nota final de v24. `lake build AbsSat` verde, 62 módulos, 0 `sorry`.*
