# Verificación para el Autor v26: Los dominios no están vacíos — lo que queda es la elección

Ricardo, soy Claude (Opus 5). Atacado `FilteredChain`, la obligación. No está cerrada. Lo que he hecho es **separarle la parte que era sobre vacuidad de la parte que es sobre elección**, y demostrar la primera. Que era justo la que `degenerate` explotaba.

---

## 1. Qué pregunta de verdad `FilteredChain`

Pide una cadena sonora de `filterAll g reqs`. Una cadena es una **selección**: un nodo por paso. Antes de preguntar si existe una selección coherente conviene saber si hay **algo que seleccionar**.

Hasta v25 no se podía responder. Y por eso `degenerate` funcionaba: un grafo donde el soporte no está vacío y **no nombra nada**.

## 2. Los dominios: no vacíos y concretos

`Model/Candidates.lean`, dos niveles.

**Globalmente** (v25): todo paso tiene un nodo.

**Relativo a cualquier nodo** — que es el que importa, porque los miembros de una cadena tienen que poseerse entre sí:

```lean
theorem candidate_at_step (h : GPathM) (hv : isValid (review h) = true) (hgn : GN (review h))
    (pid : PathNodeId) (n : PNodeM) (hn : (review h).node? pid = some n)
    (k : Int) (hlo : 0 ≤ k) (hhi : k < (review h).current_step) :
    ∃ q ∈ ownersAt n.owners k, ((review h).node? q).isSome = true ∧ q.id.step = k
```

> Coge el nodo que quieras. En **todos** los pasos su soporte es no vacío **y está hecho de nodos de verdad.**

La primera mitad la daba `isValidNode` desde siempre. La segunda es nueva y sale de v25: los owners de un nodo son owners globales (`owners_mem_gowners`), y los owners globales son nodos (`GownersAreNodes`). Encadenados:

```lean
theorem owner_is_node ... : ((review h).node? q).isSome = true
```

> **Todo owner de un nodo superviviente es él mismo un nodo superviviente.**

Eso es exactamente lo que a `degenerate` le faltaba.

## 3. Y una de las cuatro condiciones extra sale gratis

`ChainSound` es `IsChain ∧ PairwiseOwned` más cuatro condiciones. Una de ellas cae sola:

```lean
theorem chainG_gowners_free ... :
    ∀ k, 0 ≤ k → k < (review h).current_step → sel k ∈ (review h).gowners
```

Una cadena construida desde el soporte de un solo nodo vive automáticamente dentro de `gowners`. Así que esa condición ya está pagada.

---

## 4. Lo que queda, dicho con precisión

`domains_nonempty` recoge las dos mitades demostradas. Y lo que sigue abierto es esto y solo esto:

> Los dominios del problema de restricciones son **no vacíos y concretos**. Falta que exista una **selección coherente** entre ellos: encadenada padre→hijo entre pasos consecutivos, y **co-poseída dos a dos**.

Antes de v25 y v26 la obligación mezclaba dos cosas muy distintas: *"¿hay candidatos?"* y *"¿se pueden elegir a la vez?"*. La primera está demostrada. La segunda es la que tiene el contenido matemático real — y es donde llevo desde el principio diciendo que está la dificultad.

## 5. Lo que sigue sin estar

De las cuatro condiciones extra de `ChainSound`, tres siguen abiertas (auto-posesión, enlace hijo, forma de raíz), y las dos gordas —`IsChain` y `PairwiseOwned`— también. Sospecho que `IsChain` es alcanzable por un camino parecido (haría falta demostrar que los padres son nodos y que están un paso por debajo, en el mismo idioma que v25), y que `PairwiseOwned` **no** lo es por esta vía: ahí está la Helly.

No lo he intentado en este turno para no prometer de más.

---

## 6. Estado

| | |
|---|---|
| **`FilteredChain`** | **la obligación**, abierta — reducida a la *elección*, no a la existencia de candidatos |
| dominios no vacíos y concretos | **demostrado** (v26) |
| `ChainG`, cláusula de `gowners` | **gratis** para cadenas del soporte de un nodo (v26) |
| `GownersAreNodes` | demostrado (v25) |
| `MachineOk`, condiciones laterales | demostrados (v22) |
| `Certifies` seed / join | demostrados (v21) |
| descenso: la medida decrece | demostrado (v19) |
| el checker de `Supported` | demostrado (v16) |

Y sin refutar: 1.048.889 nodos verificados, 604.178 con propagación exhaustiva, 16.444 descensos completos, 0 violaciones.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 63 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
