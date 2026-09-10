# Verificación para el Autor v40: `PairwiseOwned`, cerrado donde la inducción lo necesita

Ricardo, soy Claude (Opus 5). Ataqué `PairwiseOwned`. El resultado tiene dos mitades y las digo por orden de importancia: **el caso base de la ruta A′ está demostrado** — un estado válido en el que la propagación no ha dejado elección *está habitado*, y con eso `Inhabited_of_pickValid` se queda con **una sola** obligación abierta. La otra mitad es una refutación: la posesión **no es transitiva**, así que la vía obvia que abría el puente de v39 está cerrada.

---

## 1. Primero lo que el puente regalaba, y por qué no bastaba

`linksInOwners_review` (v39) da los pares **adyacentes** de `PairwiseOwned` en las dos direcciones: en una cadena `sel k` es padre de `sel (k+1)` y `sel (k+1)` es hijo de `sel k`, y todo padre y todo hijo es owner. Gratis.

La vía natural era propagar: bajar desde `sel j` por el padre, arrastrando `sel i` con transitividad.

```lean
OwnersTransitive h : q ∈ owners n → r ∈ owners q → r ∈ owners n
```

**Es falso.** `lake exe extend --randomtrans`, 20 instancias:

| forma | tripletas | fallos |
|---|---|---|
| global | 22.521.728 | **2.950.784** |
| bajando (`q` padre de `n`, `r` owner de `q` por debajo) | 420.078 | **15.240** |
| subiendo (`q` hijo de `n`, `r` owner de `q` por encima) | 416.403 | **18.919** |

Ni siquiera restringida a los enlaces que el puente acaba de certificar. La co-posesión no se propaga: queda registrado como `Pinned.OwnersTransitive`, refutado.

## 2. La otra carretera: no propagar la relación, quitar la elección

Si la posesión no viaja, hay que quitar el margen. Y la máquina ya sabe hacerlo — es lo que hace `filterRequire`.

```lean
def PinnedAt (h : GPathM) (k : Int) : Prop :=
  ∀ q ∈ ownersAt h.gowners k, ∀ r ∈ ownersAt h.gowners k, q.id = r.id

def FullyPinned (h : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < h.current_step → PinnedAt h k
```

**Dos clavos fijan un `PathNodeId`:**

1. **El id de mapa.** `filterRequire` deja los `gowners` de ese paso con un solo id de mapa. La review intersecta los owners de cada nodo con los `gowners`, y `SelfOwned` (v30) obliga al propio id del nodo a estar en esa intersección. Luego **todo nodo superviviente en un paso pinzado lleva el id pinzado**.
2. **El `parent_id`.** `PMP` (v34) dice que `parent_id` nombra el id de mapa de los padres, y los padres son nodos del paso de abajo — que también está pinzado. Luego el `parent_id` también está fijado.

```lean
theorem pid_unique (h) (ctx : Ctx h) (hfp : FullyPinned h) (k) … :
    p = p'
```

> **En un estado totalmente pinzado hay como mucho un nodo por paso.** El grafo ha colapsado a un solo camino.

Y entonces `PairwiseOwned` no hay que demostrarlo, sale solo: `isValidNode` garantiza un owner en cada paso, ese owner es un nodo de ese paso (v25/v26), y no hay más que uno — así que **es** la elección de la cadena.

```lean
theorem pairwiseOwned_of_fullyPinned (h) (ctx : Ctx h) (hfp : FullyPinned h)
    (sel) (hchain : IsChain h sel) : PairwiseOwned h sel
```

Cierre `[propext, Quot.sound]`, fijado con `#guard_msgs`. `AbsSat/GraphPath/Model/Pinned.lean`.

## 3. Y esto *es* el caso base de la ruta A′

Esto no lo busqué: apareció al comparar definiciones. El caso base que v19 dejó pendiente en `Inhabited_of_pickValid` era

```lean
hbase : ∀ g, P g → isValid g = true → NoChoice g → Inhabited g
```

y `NoChoice g` es `hasChoice g = false`, que desplegado dice *«en cada paso todos los owners globales coinciden en el id de mapa»*. Es **literalmente `FullyPinned`**, escrito con `Bool`. Los dos sentidos están demostrados (`fullyPinned_of_noChoice`, `noChoice_of_fullyPinned`), y de ahí:

```lean
theorem inhabited_of_noChoice_filterAll (g) (reqs) (hreach) (hv) (hpos)
    (hnc : PickInduction.NoChoice (filterAll g reqs)) : Inhabited (filterAll g reqs)
```

El camino lo pone `exists_isChain` (v27), la co-posesión la pone el pinzado. **`hbase` queda descargado.**

La escalera de la ruta A′ queda así:

```
Inhabited
  ⟸ Inhabited_of_pickValid     PickValid  +  hbase
                                   ↑           ↑
                                ABIERTO    DEMOSTRADO (v40)
```

## 4. La medición: que no sea vacío

Un teorema sobre estados «totalmente pinzados» no vale nada si la máquina nunca llega a uno, y `pid_unique` es una afirmación fuerte — dice que el grafo colapsa a un camino. Así que lo medí (`lake exe extend --nochoice`, dos semillas independientes):

| campaña | estados válidos | de ellos `NoChoice` | con 2+ ids en algún paso | paso más ancho |
|---|---|---|---|---|
| 50 casos, semilla 2026, 3..7 vars | 4.835 | **1.284** (26,6 %) | **0** | **1** |
| 120 casos, semilla 90210, 3..10 vars | 15.362 | **2.685** (17,5 %) | **0** | **1** |

Casi 4.000 estados pinzados reales, y en **todos** el paso más ancho tiene exactamente un id. El teorema predice 1; la máquina da 1.

## 5. Qué queda abierto — sin adornos

- **`PairwiseOwned` en general sigue abierto.** Lo demostrado es en el régimen pinzado. Un estado válido con elección todavía puede, hasta donde sé, llevar una cadena no co-poseída; nada de lo de arriba lo descarta.
- **`PickValid` sigue abierto**, exactamente como lo dejó v20: *ninguna eliminación de la review es el último owner global de su paso*. La ruta A′ ya no tiene dos huecos, tiene uno.
- La ruta por `ChainSound`/`FilteredChain` sigue con `PairwiseOwned` como su única deuda, y esta demostración no la salda salvo en el punto fijo pinzado.

Lo que ha cambiado es la forma del problema. Antes había que demostrar una propiedad de Helly sobre una familia de conjuntos de soporte. Ahora hay que demostrar que **el filtro no invalida**, que es un enunciado sobre una sola eliminación de nodo. No es lo mismo, y es más pequeño.

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 72 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
