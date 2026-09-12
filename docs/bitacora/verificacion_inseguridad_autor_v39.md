# Verificación para el Autor v39: El puente es un teorema — y el espejo ya lleva tu arreglo

Ricardo, soy Claude (Opus 5). Cierro lo que quedaba abierto en v38: **la migración del arreglo al espejo está hecha y el puente entre el libro de `owners` y el de `parents` es ahora un teorema sobre los estados de la máquina**, no una conjetura ni una propiedad refutada.

---

## 1. El enunciado, tal como queda demostrado

```lean
def LinksInOwners (h : GPathM) : Prop :=
  ∀ pid d, h.node? pid = some d →
    (∀ p ∈ d.parents, p ∈ d.owners) ∧ (∀ s ∈ d.sons, s ∈ d.owners)

theorem linksInOwners_review (g : GPathM) (hv : isValid (review g) = true) :
    LinksInOwners (review g)

theorem linksInOwners_filterAll (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) : LinksInOwners (filterAll g reqs)
```

> En todo punto fijo válido de `review` — y `filterAll` es uno por construcción — cada padre y cada hijo de un nodo está en su lista de `owners`.

Cierre de axiomas `[propext, Quot.sound]`, fijado con `#guard_msgs`. `AbsSat/GraphPath/Model/Bridge.lean`.

**Un detalle de enunciado que importa.** Lo enuncié sobre `node?`, no sobre `n ∈ h.nodes`. No es cosmética: `node?` devuelve el *primer* nodo con ese id, así que la versión con pertenencia a la lista exigiría además unicidad de ids, que es un invariante aparte y que aquí no hace falta. Y `node?` es exactamente la moneda en la que el resto de los módulos consultan el grafo, así que el teorema encaja donde se usa.

## 2. La ruta — corta porque el arreglo hace el trabajo

Tres pasos, todos ya presentes tras la migración:

1. En un punto fijo válido, cada `cleanStep` es la identidad (`Fuel.review_cleanStep_fixed`).
2. Si el paso es la identidad, el desenlace de dentro no encontró nada que hacer (`Fuel.intersectOrDrop_valid_branch`, que ahora devuelve una terna: actualización, desenlace y validez).
3. Si el desenlace es la identidad sobre ese nodo, sus enlaces ya estaban dentro de sus owners (`Fuel.relinkSelf_eq_self_of_fixed` + `links_of_relinkSelf_eq`).

Es decir: **el puente no se demuestra, se observa.** El arreglo lo establece y el punto fijo lo conserva. Eso es lo que cambia respecto de v36, donde había que demostrarlo contra un ledger que la poda dejaba obsoleto.

## 3. La migración al espejo

`GPathM` tiene ahora `relinkSelf`, `relink`, `unlinkMap` y `unlinkIncompatible`, cableados en `cleanInvalidGo` y en `reviewNode` justo después de la intersección de owners y antes de la comprobación de validez — el mismo orden que en el ejecutable. Los módulos que hubo que reparar, y lo que costó cada uno:

| Módulo | Lema nuevo | Nota |
|---|---|---|
| `Pruned.lean` | `pruned_unlinkIncompatible` | el desenlace es un estrechamiento legítimo |
| `Fuel.lean` | `measure_unlinkIncompatible_le`, `unlinkIncompatible_eq_self`, `relinkSelf_eq_self_of_fixed` | toda F2.c re-cableada |
| `CleanInvalid.lean` | `ChainSound_unlinkIncompatible` | el lema del §4 de v38, ya demostrado |
| `Coherence.lean` | — | re-cableado |
| `GownersNodes.lean` | `GN_unlinkIncompatible` | |
| `Parents.lean` | `PN_unlinkIncompatible` | |
| `Sons.lean` | `SMP_unlinkIncompatible` | el delicado: el reflejo padres/hijos |
| `SelfOwn.lean` | `OOS_unlinkIncompatible` | |

**Un error de diseño que costó rehacer `unlinkMap`.** La primera versión filtraba los enlaces del vecino contra *sus propios* owners (`relinkSelf m`). Eso rompía `Pruned` cuando hay ids repetidos y rompía `SMP`, porque la rama del vecino decide con los owners del nodo podado. La versión correcta filtra los enlaces del objetivo contra `n.owners` dejando `m.owners` intacto: **son los owners del nodo podado los que deciden en los dos lados**, que es justo lo que hace el desenlace simétrico del ejecutable.

`lake build AbsSat` verde, 71 módulos, 0 `sorry`.

## 4. La medición, antes y después, sobre los mismos parámetros

No me fío de comparar campañas de tamaños distintos, así que hice el *antes* guardando la migración y volviendo a medir con las mismas banderas y la misma semilla.

**Campaña de puente** (`lake exe extend --randombridge 60`, 161.839 nodos, 174.7 k enlaces):

| | padres fuera de owners | hijos fuera de owners |
|---|---|---|
| espejo sin migrar | **5** | **2** |
| espejo migrado | **0** | **0** |

**Campaña de v36, idéntica** (`lake exe extend --stale 100 90210 3 8`):

| | nodos con un padre rancio | pares consecutivos en cadenas req-satisfactorias | de ellos, padre no-owner |
|---|---|---|---|
| antes | **277** | 2.563.751 | 0 |
| después | **0** | 2.563.751 | 0 |

Los enlaces rancios que v36 midió **han desaparecido**, y el número de pares de cadena es el mismo: el arreglo no ha quitado cadenas, ha quitado basura estructural.

**Y la campaña de "sin zombis" sigue limpia** (`lake exe validate --random 60 2026 3 5`): 60/60, 5.466 estados válidos, 161.839 nodos comprobados, 5.466 `Inhabited` certificados. El recuento de nodos es idéntico al de antes de la migración, así que el desenlace no está podando de más.

## 5. Lo que esto le compra a la obligación abierta

v36 dejó un aviso sobre `PathExists.exists_isChain`: el descenso elige un padre *arbitrario* en cada paso, y como había enlaces rancios el camino construido podía usar uno. **Ese aviso queda retirado**: con `LinksInOwners`, cualquier padre que el descenso elija es owner del nodo del que baja. No cierra `PairwiseOwned` — la co-posesión pide mucho más que la relación con el predecesor inmediato — pero elimina una fuga concreta que la separaba de la realidad.

Y `ParentId.ParentIsOwner` / `SonIsOwner`, refutados en v36, pasan a ser consecuencias de `linksInOwners_review` sobre los estados que importan. Es la segunda vez en la serie que una refutación se convierte en teorema, y por la misma razón que la primera: **lo que fallaba era un defecto, no una conjetura.**

## 6. Lo que sigue abierto

Sin cambio respecto de v38 en lo matemático:

- **`PairwiseOwned`** — la propiedad de Helly en el vocabulario de la máquina. Reducida a `ReqSatImpliesOwned` (mitad pinzada reducida a `OwnerMatchesPredecessor`; los pares no pinzados siguen sin reducción) y a *«en todo estado válido existe un camino que satisface sus requisitos»*.
- Las dos mediciones que sostienen esas reducciones siguen con 0 violaciones y ahora sobre un espejo que ya no tiene enlaces rancios, así que valen más que antes.

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 71 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
