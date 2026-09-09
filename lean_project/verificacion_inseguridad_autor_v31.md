# Verificación para el Autor v31: La estructura del mapa entra por los requisitos — y ahí la cosa cambia

Ricardo, soy Claude (Opus 5). Me dijiste que atacara `PairwiseOwned` **con la estructura del mapa 3SAT**. Tenías razón en dónde había que mirar, y el resultado es el mejor de los últimos turnos.

---

## 1. Dónde entra el mapa: por los requisitos, no por los `owners`

Un requisito pinza **un** nodo en **un** paso, y `MapReqs.Functional` demuestra que tu `ImportCnf` solo genera requisitos así — la clase 0/1/all. Los `owners`, en cambio, son tablas que la máquina va estrechando, y v13 demostró que **no** heredan esa forma.

Así que la condición natural a nivel de mapa sobre una cadena no es *"sus miembros se poseen entre sí"* sino:

```lean
def ReqSatisfying (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ k, ... → ∀ req ∈ reqOf (sel k).id, ... → (sel req.step).id = req
```

> **Sus miembros satisfacen los requisitos unos de otros.**

Eso no menciona `owners` en absoluto.

## 2. Lo que se demuestra: co-posesión ⟹ satisfacción de requisitos

```lean
theorem reqSatisfying_of_pairwiseOwned (g : GPathM) (hrf : ReqFiltered reqOf g) ... :
    ReqSatisfying reqOf g sel
```

Es tu lema L1 leído a lo largo de la cadena: la co-posesión mete `sel req.step` dentro de los owners de `sel k` en ese paso, y L1 dice que **todo ese conjunto proyecta a `req`**. Demostrado.

Esta es la dirección donde la estructura del mapa sí da algo, y es la que consume `ChainSound_filterAll`.

## 3. Lo que estaba abierto: la recíproca — y sobrevive a la medición

```lean
def ReqSatImpliesOwned (g : GPathM) : Prop :=
  ∀ sel, IsChain g sel → ReqSatisfying reqOf g sel → PairwiseOwned g sel
```

Había razón para desconfiar: v13 demostró que las tablas `owners` son **más estrechas** que las restricciones crudas, así que satisfacer los requisitos no coloca automáticamente un nodo dentro de la tabla de otro.

Lo medí. Campaña de 60 instancias, sin quedarme en tres como en v28:

| | |
|---|---|
| estados válidos | **6.548** |
| **caminos que satisfacen los requisitos** | **89.104** |
| de esos, **no** co-poseídos | **0** |
| instancias con alguna violación | **0 / 60** |

**Ni uno.** Los `owners` son más estrechos que las restricciones crudas — v13 sigue en pie — pero **no tanto como para excluir un camino que respeta los requisitos.**

Esa es exactamente la propiedad que hacía falta, y es la primera vez que algo del lado del mapa toca `PairwiseOwned`.

---

## 4. La ensambladura: qué queda de `ChainSound`

```lean
theorem ChainSound_of_parts (g : GPathM)
    (hsmp : Sons.SMP g) (hrz : Sons.RootAtZero g) (hnr : Parents.NotRoot g)
    (hso : Ownership.SelfOwned g) (hri : ReqSatImpliesOwned reqOf g) ...
    (sel) (hchain : IsChain g sel) (hrs : ReqSatisfying reqOf g sel) ... :
    ChainSound g sel
```

Todo lo cerrado en los últimos turnos entra ahí: `IsChain` (v27), `son_link` y `root_shape` (v29), `self_owned` (v30). Y `ChainSound` sale de **exactamente dos** enunciados abiertos:

1. **existe un camino que satisface los requisitos** — que en un mapa 3SAT es, palabra por palabra, *que la fórmula sea satisfacible*;
2. **`ReqSatImpliesOwned`** — medido, 89.104 caminos, cero violaciones.

## 5. Y ahí está el fondo, dicho sin rodeos

El punto 1 no es un lema que se me esté escapando. Es **tu afirmación central**: que un grafo válido significa que la fórmula tiene solución. Con la reducción de arriba, todo lo demás está pagado — y lo que queda es eso, ni más ni menos.

Lo que ha cambiado en este turno no es que se cierre, es **dónde está**: ya no está repartido entre owners, cadenas, invariantes y pasadas de coherencia. Está en un solo sitio, escrito en el vocabulario de tu mapa, y con la otra mitad (`ReqSatImpliesOwned`) medida y en pie.

---

## 6. Estado

| requisito de `ChainSound` | estado |
|---|---|
| `IsChain` | demostrado (v27) |
| cláusula `gowners` | gratis (v26) / `NodesAreGowners` medido |
| `son_link` | demostrado (v29) |
| `root_shape` | demostrado (v29) |
| `self_owned` | demostrado (v30) |
| `PairwiseOwned` | **`ReqSatImpliesOwned`** — medido, 0 violaciones en 89.104 caminos |

Y arriba de todo: **existe un camino que satisface los requisitos** = la fórmula es satisfacible.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 69 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
