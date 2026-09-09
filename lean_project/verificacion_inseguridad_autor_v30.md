# Verificación para el Autor v30: `self_owned` cerrado — y `ParentOwns` no hacía falta

Ricardo, soy Claude (Opus 5). Me pediste atacar `SelfOwned` y `ParentOwns` **juntos**, porque en v29 los dejé como mutuamente recursivos. **`SelfOwned` está demostrado, y `ParentOwns` no ha hecho falta.** La recursión mutua era real, pero era la ruta equivocada.

---

## 1. Lo que decía v29, y por qué estaba incompleto

v29 encontró que la ruta directa se muerde la cola:

- bajo `reviewNode`, `n` conserva su propio id en sus owners solo si **algún vecino lo posee**;
- y el vecino lo conserva solo si **`n` se posee a sí mismo**.

Eso es correcto. Lo que faltaba era ver que **no hay que llevar la auto-posesión como invariante en absoluto.**

## 2. El invariante que solo encoge

```lean
def OOS (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ q ∈ n.owners, q.id.step = n.id.id.step → q = n.id
```

> **En su propio paso, los owners de un nodo no contienen nada más que a él.**

Y es cierto **desde el nacimiento**, por cómo escribiste `addNode`: al nodo nuevo le das `owners := gowners ++ [pid]`, y en ese momento **todos** los owners globales están en pasos estrictamente inferiores. Así que en su propio paso el nodo nuevo tiene exactamente `{él mismo}`.

A partir de ahí, todas las operaciones **solo quitan owners**. Un invariante que solo encoge no tiene que pelearse con la pasada de coherencia: se preserva incondicionalmente. Demostrado para toda la máquina — `filterRequire`, `updateAt`, `removeNode`, la cadena de `review`, `addNode`, `join`, `initSeed`.

## 3. Y entonces la auto-posesión es una **consecuencia**, no un invariante

```lean
theorem SelfOwned_of_OOS (h : GPathM) (hv : isValid (review h) = true)
    (hoos : OOS (review h)) ... : Ownership.SelfOwned (review h)
```

El argumento cabe en dos líneas:

1. En un punto fijo válido todo nodo pasa `isValidNode`, que exige **un owner en cada paso** por debajo de `current_step` — incluido el suyo propio.
2. Por `OOS`, ese owner **solo puede ser el nodo mismo**.

Fin. Nunca se entra en la recursión mutua.

```lean
theorem SelfOwned_filterAll (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true) :
    Ownership.SelfOwned (filterAll g reqs)
```

`ParentOwns` se queda en el código, marcado como **la ruta que no hace falta** — porque saber qué ruta no hace falta también es información.

---

## 4. `ChainSound`: cinco de seis

| requisito | estado |
|---|---|
| `IsChain` | **demostrado** (v27) |
| `ChainG`, cláusula `gowners` | **gratis** (v26) |
| `son_link` | **demostrado** (v29) |
| `root_shape` | **demostrado** (v29) |
| `self_owned` | **demostrado** (v30) |
| `PairwiseOwned` | **abierto — la Helly** |

Queda **uno**. Y es el que dije desde v28 que era irreducible: dos nodos pueden ser ambos compatibles con `t` e incompatibles entre sí, y ninguna cantidad de invariantes estructurales lo va a dar. Los cinco que se han cerrado eran, todos, propiedades locales preservadas operación a operación. Ese no lo es.

---

## 5. Una observación sobre tu diseño

Es la cuarta vez en pocos turnos que una pieza de tu código resulta ser exactamente la que hacía falta:

- `okJoin` exige `isValid` de las dos ramas → el caso `join` de `Certifies` (v21);
- `up` devuelve el grafo invalidado sin añadir nodo → `isValid_of_upFiltering` (v21);
- `MachineOk` liga `map_parent` con `current_step` → `NotRoot` y `RootAtZero` (v27, v29);
- `addNode` da al nodo nuevo `gowners ++ [pid]` con todos los gowners por debajo → **`OOS`, y con él `self_owned`** (v30).

No es casualidad. Son decisiones de diseño que mantienen invariantes, y por eso los invariantes salen. Lo digo porque el trabajo de estos días ha consistido en gran parte en encontrar cuáles son.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 68 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
