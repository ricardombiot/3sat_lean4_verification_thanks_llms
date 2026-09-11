# Verificación para el Autor v85: `TriProp` extraído — ya no es hipótesis

Ricardo, soy Claude (Opus 5). Hecho lo que quedaba de v84: `TriProp` ya no entra como hipótesis, es un teorema sobre tu `reviewTri`.

---

## 1. Lo demostrado

```lean
theorem TriProp_reviewTri (g : GPathM) (hv : isValid (reviewTri g) = true) :
    TriProp (reviewTri g)                                  -- [propext, Quot.sound]
```

Sin hipótesis colgando. El camino son cuatro piezas:

| teorema | qué dice |
|---|---|
| `TriProp_of_triClean_fixpoint` | **el corazón**: en un punto fijo de `triClean`, una entrada sobrevivió *porque* se cumplió el test de la pasada — y ese test **es** `TriProp` |
| `triClean_eq_of_measure_ge` | una pasada que no quita nada es la identidad (vía `sum_eq_pointwise` y el filtro que no encoge) |
| `measure_reviewFuel_le` / `measure_review_le` | el review nunca hace crecer la medida — hacía falta y no estaba |
| `TriProp_reviewTriFuel` | el bucle: o recursa con medida estrictamente menor, o para donde la pasada ya no quita nada, y ahí es punto fijo |

El corazón es una sola lectura, y me gustó encontrarla así: **no hay que demostrar que el triángulo consigue la propiedad; hay que darse cuenta de que la propiedad es exactamente su criterio de poda**. Lo que costó fue lo de alrededor — que el bucle llega, y que «no quitó nada» implica «es la identidad».

## 2. Y el teorema del estrechado quedó sin axiomas

Al generalizarlo para que sirva a las dos máquinas —la original y la del triángulo— `pinnedCandidate_selfSupporting` pasó a depender de **ningún axioma**, ni `propext`. Ahora dice, sobre un estado cualquiera `G`:

> si los owners son owners globales, los owners globales llevan los pines, vale `TriProp` y vale la simetría, entonces todo miembro del candidato tiene su soporte dentro del candidato en cada paso.

Las cuatro hipótesis son cosas tuyas: las dos primeras las da la construcción (`gowners_compat_filterAll`, demostrado aquí, descarga la segunda para el filtro original), la tercera es el triángulo de v69 —ahora teorema— y la cuarta el review simétrico de v64.

## 3. Lo que falta para ensamblar P3 del todo

Una cosa, y es transporte: los lemas «los owners son owners globales» y la simetría existen para `review`; para `reviewTri` hay que reprobarlos, que es el mismo argumento porque `triClean` no toca `gowners` ni los enlaces, solo filtra tablas. Es contabilidad del tipo que `Fabric.lean` ya hace, y no queda nada abierto dentro.

Con eso, P3 quedaría cerrada de punta a punta **en la máquina del triángulo**, que es donde tiene que estar, porque el argumento necesita el triángulo.

## 4. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | candidato cubre ✅ (v83); el estrechado no borra ✅ (v84, ahora sin axiomas); **`TriProp` ✅ (hoy)**; falta transportar dos lemas a `reviewTri` |
| **P4** el puente a `PickSome` | formalmente ✅ (v81), medido equivalente a la validez (v82) |
| **P5** cierre con `L7` | libre |

Y sigo apuntando lo mismo que en v84, porque es lo que hace que esto no sea sospechoso: el argumento de P3 se apoya en `owns_required`, que es un teorema **del filtro de cláusula**, y no vale para el pinchazo del lector. P3 es un invariante de la construcción, no un procedimiento de decisión. Esa es la razón por la que se puede demostrar sin que nada se rompa.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto; los treinta y siete teoremas de `FabricAdd.lean` cierran en `[propext, Quot.sound]` o menos — dos de ellos, `Fabric_core` y `pinnedCandidate_selfSupporting`, sin axiomas de ningún tipo.
