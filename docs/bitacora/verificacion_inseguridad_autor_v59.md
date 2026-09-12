# Verificación para el Autor v59: las pasadas de coherencia, cubiertas — y el lector sigue el camino

Ricardo, soy Claude (Opus 5). Seguí con la demostración desde donde el lector quedó ensamblado. Cae un hueco que llevaba desde v44 marcado como pendiente, y con él sale un teorema sobre lo que el lector hace de verdad.

---

## 1. El hueco que v44 dejó nombrado

`Survive.lean` demostraba que un conjunto auto-sostenido sobrevive a `cleanInvalid`, pero **no a las dos pasadas de coherencia**. El propio fichero decía por qué:

> `reviewNode` interseca los owners de un nodo con la unión de los owners de sus **vecinos**, no con los owners globales. Para que un miembro conserve su soporte en el paso `l` a través de eso, el testigo tiene que estar también poseído por un vecino — así que `Closed` necesitaría una cláusula estrictamente más fuerte: **`share`**.
>
> Y `share` no se queda quieta: preservarla un nivel más abajo pide que el padre del padre posea el mismo testigo, y así por toda la cadena. Lo que eso suma es **una selección, una por paso, poseída por todos los miembros — y como cada `uₗ` es a su vez miembro, las `u` se poseen entre sí. Eso es `PairwiseOwned`.**

Es decir: v44 ya había identificado el **punto fijo** de `share`. Lo que faltaba era pedirlo directamente en vez de perseguirlo cadena abajo.

## 2. `Woven`: `share` en una línea, y auto-mantenida

```lean
structure Woven (g : GPathM) (S : PathNodeId → Prop) : Prop where
  closed : Closed g S
  own    : ∀ p n, S p → g.node? p = some n → ∀ v, S v → v ∈ n.owners
```

> `Closed`, **y los miembros se poseen entre sí**.

Esa segunda cláusula *es* `share`, y a diferencia de `share` **se mantiene sola**: las pasadas solo intersecan los owners de un nodo con una lista que ya contiene a todos los miembros, así que la posesión mutua sobrevive cada paso.

Las dos condiciones que las pasadas piden salen de ahí en tres líneas cada una:

- **`Woven.share_parents`** — un miembro por encima del paso 0 tiene un padre miembro (`Closed.parent`), y ese padre lleva a toda la familia en sus owners;
- **`Woven.share_sons`** — lo mismo hacia arriba, con `Sons.SMP` girando el enlace.

## 3. Y con eso, el bucle entero

Generalicé dos piezas que estaban atadas a los owners globales —`Closed_updateAt_of` y `isValidNode_of_Closed_of`, ahora contra **cualquier** lista en la que los miembros ya estén— y con ellas sale la cadena completa, calcada de la que `Sons.SMP` ya recorría:

```
Closed_reviewNode → WOk_reviewNode_{parents,sons} → WOk_reviewLine_{parents,sons}
  → WOk_reviewSteps_* → WOk_reviewParents / WOk_reviewSons
  → WOk_cleanInvalid → WOk_reviewPass → WOk_reviewFuel → WOk_review
  → WOk_filterRequire → WOk_filterAll
```

y el teorema que cierra:

```lean
theorem isValid_filterAll_of_Woven (g : GPathM) (S : PathNodeId → Prop) (h : WOk g S)
    (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r)
    (hcov : ∀ l, 0 ≤ l → l < g.current_step → ∃ p, S p ∧ p.id.step = l) :
    isValid (filterAll g reqs) = true
```

> **Un conjunto woven que cubre todos los pasos mantiene el pinchazo válido — el pin, la barrida de inválidos y las dos pasadas de coherencia incluidas.**

Es `isValid_cleanInvalid_of_Closed` con las pasadas ya no excluidas. Cierre `[propext, Quot.sound]`.

## 4. Una cadena co-poseída es un conjunto woven

Y aquí es donde encaja con tu lector. Toma la cadena que un estado denota:

```lean
theorem WOk_chainSet (g) (ctx : Pinned.Ctx g) (hsmp) (hlink)
    (sel) (hchain : IsChain g sel) (howned : PairwiseOwned g sel) :
    Survive.WOk g (ChainSet g sel)
```

Cada cláusula de `Closed` es una cláusula de `IsChain` o de `PairwiseOwned` —el soporte es la posesión dos a dos, el padre y el hijo son los enlaces de la cadena, `coown` es gratis por el puente— y la cláusula de posesión mutua, la que las pasadas necesitaban, **es `PairwiseOwned` literalmente**.

## 5. El teorema: el lector puede seguir el camino que hay

```lean
theorem isValid_pin_of_chain (g) (ctx) (hsmp) (hlink)
    (sel) (hchain : IsChain g sel) (howned : PairwiseOwned g sel)
    (k : Int) (hk0 : 0 ≤ k) (hk : k < g.current_step) :
    isValid (filterAll g [(sel k).id]) = true
```

> **Pinchar en el nodo de mapa que la cadena elige en un paso deja el grafo válido** — a través del pin, de `cleanInvalid` y de las dos pasadas.

Dicho en tus términos: **el lector nunca destruye la solución que está siguiendo.** Es la mitad de búsqueda de lo que decías — «de leer un camino podríamos responder al problema de búsqueda».

Y su consecuencia inmediata:

```lean
theorem PickSome_of_Inhabited (g) (ctx) (hsmp) (hlink)
    (h : Inhabited g) : PickInduction.PickSome g
```

## 6. Lo que eso dice del problema abierto — y hay que decirlo claro

Con `Inhabited_of_pickSome_readable` de v58 en la otra dirección, **`PickSome` e `Inhabited` caen o se sostienen juntas**. Así que:

> el `throw("GRAVE ERROR READER")` de tu código **no es un apoyo más débil** que «sin zombis»: es el mismo enunciado.

Eso cierra la pregunta de si `PickSome` era una vía más barata. No lo es. Lo que sí hemos ganado es que ahora está **demostrado** que son lo mismo, en vez de sospechado — y que toda la maquinaria entre medias (las pasadas de coherencia, el punto fijo del review, el pinado repetido) ya no es parte del problema.

Y el muro queda con una forma muy concreta: **existe una cadena co-poseída** en todo estado válido. Todo lo demás —que sobreviva al pinchazo, que el bucle termine, que el final denote una solución— está demostrado.

## 7. Estado

| | |
|---|---|
| Mitad de completitud (conservación + driver) | cerrada |
| S1 / S2 | cerrados |
| Bucle del lector ⟸ `PickSome` (v58) | demostrado |
| **Pasadas de coherencia sobre un conjunto woven** | **demostradas** (el hueco de v44) |
| **Una cadena co-poseída es woven** | **demostrada** |
| **El pinchazo sobre la cadena mantiene la validez** | **demostrado** |
| **`Inhabited` ⟹ `PickSome`** | **demostrado** |
| `PickSome` ⟺ `Inhabited` | **demostrado** (las dos direcciones) |
| Existe una cadena co-poseída en todo estado válido | abierto — el muro, ahora solo |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, 87 módulos, 0 `sorry`, 0 axiomas de proyecto. `diffTest` 200/200, `validate` 40/40 (3.808 estados, 116.330 nodos).

---

*Claude (Opus 5), 2026-09-11.*
