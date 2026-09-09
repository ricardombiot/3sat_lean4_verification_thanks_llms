# Verificación para el Autor v29: `son_link` y `root_shape` cerrados; `self_owned` no es lo que parecía

Ricardo, soy Claude (Opus 5). Me pediste tres. **Dos están demostradas.** La tercera resultó ser de otra clase, y explico por qué con precisión en vez de dejarlo en "es difícil".

---

## 1. `son_link` — demostrado

`IsChain` (v27) ya da el enlace **padre**: `sel k` es padre de `sel (k+1)`. `son_link` pide el enlace **hijo**: `sel (k+1)` está en los hijos de `sel k`. Es decir, que las dos tablas se reflejen:

```lean
def SMP (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ p ∈ n.parents, ∀ m ∈ h.nodes, m.id = p → n.id ∈ m.sons
```

Demostrado para **toda** la máquina: `filterRequire`, `updateAt`, `removeNode`, la cadena entera de `review`, `addNode`, `join`, `initSeed`.

El caso interesante fue `removeNode`: filtra padres **e** hijos por el mismo id, así que el reflejo sobrevive — un nodo que sigue vivo tenía un padre vivo, y su id sigue en los hijos de ese padre. Y `join` necesitó `PN` (v27) de las dos ramas para descartar el caso en que un padre solo existiera en un lado.

Con eso:

```lean
theorem son_link_of_SMP (h : GPathM) (hsmp : SMP h) (sel) (hchain : IsChain h sel) :
    ∀ k, 0 ≤ k → k + 1 < h.current_step → sel (k + 1) ∈ sonsOf h (sel k)
```

## 2. `root_shape` — demostrado

Son dos mitades. La de arriba ya estaba: `NotRoot` (v27) dice que nada por encima del paso 0 es raíz. Faltaba el espejo:

```lean
def RootAtZero (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, n.id.id.step = 0 → n.id.parent_id = none
```

Y en `addNode` sale otra vez de tu `MachineOk`: el nodo nuevo lleva `parent_id := map_parent`, y `MachineOk` dice que `map_parent = none` justo cuando `current_step = 0`. Es la tercera vez que `MachineOk` resulta ser exactamente la pieza que hacía falta.

```lean
theorem root_shape_of (h : GPathM) (hrz : RootAtZero h) (hnr : Parents.NotRoot h) ... :
    (sel 0).parent_id = none ∧ ∀ k, 0 < k → k < h.current_step → (sel k).parent_id ≠ none
```

---

## 3. `self_owned` — por qué es de otra clase

Aquí es donde el turno se pone interesante, y no en el buen sentido.

`SMP` y `RootAtZero` salieron porque hablan de **`parents`, `sons` e `id`** — y las pasadas de review **nunca tocan eso**, salvo al eliminar un nodo junto con sus enlaces. Son invariantes que sobreviven incondicionalmente.

`SelfOwned` habla de **`owners`**, que es precisamente lo que las pasadas podan. Y ahí se rompe la analogía en dos sitios:

- bajo `cleanInvalid`, `n.owners` se intersecta con `gowners`, y `n.id` sobrevive **solo si `n.id ∈ gowners`** — o sea, solo dado `NodesAreGowners` (medido: 0 violaciones en 259.187 nodos, sin demostrar);
- bajo `reviewNode`, `n.owners` se intersecta con la unión sobre los **vecinos**, y `n.id` sobrevive **solo si algún vecino posee a `n`**.

Esa segunda condición es `ParentOwns` — un padre posee a su hijo. Y `ParentOwns` a su vez se preserva **solo dado `SelfOwned`**: el padre conserva a `n` en sus owners porque la unión sobre *sus* vecinos contiene a `n`, lo que exige que `n` se posea a sí mismo.

> **Son mutuamente recursivas.** Ninguna de las dos se puede demostrar sola: hace falta una inducción **simultánea** sobre la máquina, arrastrando además `NodesAreGowners`.

Es una pieza bastante más grande que las otras dos, y la he dejado **enunciada** (`ParentOwns` en el código, con el mecanismo escrito al lado) en vez de intentada. No quiero volver a hacer lo de v28.

---

## 4. Estado de `ChainSound`

`ChainSound` son seis requisitos. Así están:

| requisito | estado |
|---|---|
| `IsChain` | **demostrado** (v27) |
| `ChainG`, cláusula `gowners` | **gratis** para cadenas del soporte de un nodo (v26) |
| `son_link` | **demostrado** (v29) |
| `root_shape` | **demostrado** (v29) |
| `self_owned` | puente demostrado (v28); invariante **abierto** — mutuamente recursivo con `ParentOwns`, trabajo acotado |
| `PairwiseOwned` | **abierto — la Helly** (v28) |

Cuatro de seis cerrados. Uno es trabajo acotado y mecánico. Uno es el núcleo matemático.

---

## 5. Lo que no ha cambiado

Sin refutar, en veintitantos turnos: 1.048.889 nodos verificados, 16.444 descensos completos, 604.178 nodos con propagación exhaustiva, 259.187 nodos con la relación de posesión medida. Cero violaciones de lo que sigue en pie.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 67 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
