# Verificación para el Autor v24: `ArcImpliesChain` es falso — lo demuestro, y era error mío

Ricardo, soy Claude (Opus 5). Me pediste atacar `ArcImpliesChain`, la obligación con la que cerré v23. Lo he atacado y **lo he refutado**. El error era mío, de v23, y está demostrado en Lean con un testigo explícito.

---

## 1. Qué hice mal en v23

Escribí, con cierta ceremonia, que la obligación final ya no contenía *"nada de `addNode`, del bucle de fuel, de `join`, de la semilla, de `MachineOk`, de rangos de nodos. Ni siquiera `Reachable`"*.

Eso último no era un logro. **Quitar `Reachable` no debilita la obligación: la fortalece.** Una hipótesis menos significa que el enunciado tiene que valer para más grafos — incluidos grafos que tu máquina **no puede construir**.

Y uno de esos lo tumba.

## 2. El contraejemplo

```lean
def degenerate : GPathM :=
  { nodes := [],
    gowners := [{ id := { step := 0, index := 0 }, parent_id := none }],
    current_step := 1,
    map_parent := none }
```

Un grafo con **un owner global en cada paso y ningún nodo**. Comprobado, todo por cómputo:

| | |
|---|---|
| `degenerate_valid` | `isValid degenerate = true` — hay entrada en todos los pasos |
| `degenerate_fixpoint` | `review degenerate = degenerate` — no hay nodos que revisar |
| `degenerate_arcConsistent` | las cuatro cláusulas de `ArcConsistent` cuantifican sobre nodos: vacías |
| `degenerate_no_chain` | `IsChain` pide un nodo en el paso 0. No hay ninguno |

```lean
theorem not_ArcImpliesChain : ¬ ArcImpliesChain reqOf
```

Demostrado, cierre `[propext]`. No es una sospecha.

---

## 3. La reparación

```lean
def ArcImpliesChainOn : Prop :=
  ∀ g d, Reachable reqOf g → isValid g = true → (∃ sel, ChainSound g sel) →
    ArcConsistent reqOf (filterAll g (reqOf d)) →
    review (filterAll g (reqOf d)) = filterAll g (reqOf d) →
    isValid (filterAll g (reqOf d)) = true →
    ∃ sel, ChainSound (filterAll g (reqOf d)) sel
```

La obligación con **todas** las hipótesis que el sitio de llamada realmente tiene. Y he demostrado las dos direcciones:

```lean
theorem FilteredChain_of_ArcImpliesChainOn : ArcImpliesChainOn reqOf → FilteredChain reqOf
theorem ArcImpliesChainOn_of_FilteredChain : FilteredChain reqOf → ArcImpliesChainOn reqOf
```

**Son equivalentes.** O sea: el último escalón de v23 no era un debilitamiento. Añadir consistencia de arcos y el punto fijo es útil para quien vaya a demostrarlo —son hipótesis gratis, ya demostradas— pero **no hace la obligación más pequeña**.

### Lo que de v23 sí sobrevive

- `ReqChain → FilteredChain` **sí** era un debilitamiento estricto, y está demostrado.
- Las hipótesis de arco-consistencia y punto fijo **son gratis** (`arcConsistent_filterAll`, `filterAll_is_review_fixpoint`), y eso sigue en pie.
- Lo que cae es el último paso y la frase de que "ya no queda nada dentro".

**La escalera tocó fondo en `FilteredChain`.** No en `ArcImpliesChain`.

---

## 4. Lo que el contraejemplo señala, que es lo útil

`degenerate` falla por una razón muy concreta, y merece nombre:

```lean
def GownersAreNodes (h : GPathM) : Prop := ∀ q ∈ h.gowners, (h.node? q).isSome = true
```

> **Todo owner global es un nodo.**

Es exactamente lo que `degenerate` viola, y por tanto lo que `Reachable` estaba suministrando **en silencio**. Cualquier demostración de la obligación va a necesitarlo explícito: sin él, "hay un owner en cada paso" no dice nada sobre que haya algo que seleccionar.

Ya está la semilla:

```lean
theorem GownersAreNodes_initSeed (d : NodeId) (title : String) :
    GownersAreNodes (GPathM.initSeed d title)
```

⚠ **Corregido por v25.** Escribí aquí que `filterRequire` rompe temporalmente este invariante. **Es falso, y me equivoqué de dirección.** `filterRequire` *encoge* `gowners` y deja los nodos intactos, así que `gowners ⊆ nodes` lo atraviesa sin despeinarse. Lo que `filterRequire` rompe es la **recíproca** — nodos cuyo id ya no es owner global —, y `review` es quien limpia esos. Con la dirección correcta, el invariante vale **en todas partes**, y en [v25](./verificacion_inseguridad_autor_v25.md) está demostrado para toda la máquina.

---

## 5. Dónde queda la cosa

| obligación | estado |
|---|---|
| `Supported` (L6) | la original |
| `Inhabited` | mitad del veredicto, localizada (v16) |
| `UpCertifies` | seed y join saldados (v21) |
| `ReqChain` | condiciones laterales saldadas (v22) |
| **`FilteredChain`** | **el fondo real de la escalera** |
| `ArcImpliesChainOn` | equivalente a `FilteredChain`, con contexto explícito |
| ~~`ArcImpliesChain`~~ | **refutado** (v24) |

Y el invariante que hay que sacar a la luz para seguir: `GownersAreNodes`, con la semilla hecha y `addNode` / `review` / `join` por delante.

---

## 6. Lo que aprendo de esto, y te lo digo porque afecta a cómo leer lo anterior

Llevo ocho reducciones seguidas y esta es la primera que se me va de las manos en la dirección equivocada. El patrón del error es reconocible: **quitar hipótesis parece limpieza y es lo contrario.** Cada vez que un enunciado se ve "más elegante" porque ha perdido contexto de la máquina, hay que sospechar.

Lo bueno es que el propio método lo detectó: intentar demostrarlo fue lo que produjo el contraejemplo en diez minutos.

---

*Claude (Opus 5), 2026-09-09. Corrige v23. `lake build AbsSat` verde, 61 módulos, 0 `sorry`.*
