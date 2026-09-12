# Verificación para el Autor v38: El puente, formalizado — de refutado a cierto por construcción

Ricardo, soy Claude (Opus 5). El puente entre el libro de `owners` y el de `parents` está formalizado. Y ha pasado algo que merece decirse antes que los detalles: **v36 lo refutó, y ahora es cierto por construcción.** No porque haya encontrado una demostración más lista, sino porque lo que fallaba era un bug y lo has arreglado.

---

## 1. El puente, enunciado

```lean
def LinksInOwners (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, (∀ p ∈ n.parents, p ∈ n.owners) ∧ (∀ s ∈ n.sons, s ∈ n.owners)
```

> Todo padre y todo hijo de un nodo es uno de sus owners.

En v36 esto estaba **refutado**: 37 enlaces padre y 71 enlaces hijo rancios por cada ~328.000, y escalando. Quedó registrado como `ParentId.ParentIsOwner` y `ParentId.SonIsOwner`, refutados.

## 2. Lo que el arreglo establece — demostrado

```lean
theorem linksInOwners_relinkSelf (n : PNodeM) :
    (∀ p ∈ (relinkSelf n).parents, p ∈ (relinkSelf n).owners) ∧
    (∀ s ∈ (relinkSelf n).sons, s ∈ (relinkSelf n).owners)

theorem linksInOwners_at (g : GPathM) (id : PathNodeId) (n : PNodeM)
    (hn : g.node? id = some n) (m : PNodeM) (hm : m ∈ (unlinkIncompatible g id).nodes)
    (hmid : m.id = id) :
    (∀ p ∈ m.parents, p ∈ m.owners) ∧ (∀ s ∈ m.sons, s ∈ m.owners)
```

> **La operación establece el puente por construcción**, en el nodo sobre el que actúa.

No hay nada que conjeturar ahí: después de re-enlazar, los padres y los hijos son exactamente los que los owners permiten.

## 3. Y es un estrechamiento legítimo

```lean
theorem pruned_unlinkIncompatible (g : GPathM) (id : PathNodeId) :
    Pruned g (unlinkIncompatible g id)
```

Solo quita enlaces: nunca añade nodos, nunca añade owners, nunca cambia ids ni pasos. Así que **todo lo que `Pruned` da atraviesa la operación**. Eso es lo que hace segura la migración del espejo.

## 4. Por qué la migración va a salir

```lean
theorem chain_link_survives (g : GPathM) (sel : Int → PathNodeId)
    (howned : PairwiseOwned g sel) ... : sel k ∈ n.owners
```

> El enlace padre de una cadena sonora sobrevive al desenlace **precisamente porque la cadena está co-poseída**.

Y `PairwiseOwned` ya es un campo de `ChainSound`. O sea: el desenlace no puede romper una cadena sonora, y la razón es la propia definición de cadena sonora. Ese es el argumento que hay que enhebrar en las cuatro pruebas de preservación.

---

## 5. Lo que NO está demostrado, y el estado exacto de la migración

**No está demostrado que `LinksInOwners` sea invariante de todo estado que la máquina construye.** Para eso hay que cablear la operación dentro de `cleanInvalidGo` y `reviewNode` en el espejo. Lo intenté en esta sesión, llegué hasta aquí, y lo revertí para no dejarte el repo sin compilar:

| pieza de la migración | estado |
|---|---|
| `GPathM` (`relinkSelf`, `unlinkMap`, `unlinkIncompatible`, pasos cableados) | **funciona** |
| `Pruned` (`pruned_unlinkIncompatible` + los dos sitios) | **funciona** |
| `Fuel`: cotas de medida | **funciona** |
| `Fuel`: **F2.c entero** (`unlinkIncompatible_eq_self`, `intersectOrDrop`, `intersectOrDrop_valid_branch`, `relinkSelf_eq_self_of_fixed`) | **funciona** |
| `CleanInvalid`, `Coherence`, `Review`, `AddNode` | **pendiente** |

Lo que falta en esas cuatro es un solo lema, `ChainSound_unlinkIncompatible`, cuyo argumento es exactamente el teorema del §4. No es difícil; es largo, y hay que escribirlo en el idioma de `CleanInvalid.lean`.

Mientras tanto **el espejo poda menos que el ejecutable**. La diferencia es conservadora y `diffTest` valida las dos bandas contra el oráculo (800/800).

---

## 6. Lo que este episodio dice de método

El puente pasó de **refutado** (v36, con 37 testigos que escalaban) a **cierto por construcción** (v38) por un cambio en el algoritmo, no por una demostración mejor.

Eso solo pasa cuando lo que fallaba **no era una conjetura sino un defecto**. Y es la primera vez en toda esta serie: `Extendable`, el clique del soporte, la simetría de posesión, la aciclicidad y `ArcImpliesChain` se refutaron y **siguen refutados**, porque eran conjeturas equivocadas. Este no lo era.

La medición sirvió para las dos cosas: descartar conjeturas falsas y **encontrar un fallo real**.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 71 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
