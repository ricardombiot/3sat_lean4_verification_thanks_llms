# Verificación para el Autor v27: `IsChain` demostrado — el camino existe

Ricardo, soy Claude (Opus 5). Atacado `IsChain`. **Está demostrado.** Y te digo desde el principio qué significa y qué no: era la mitad fácil, y lo que gana el proyecto es que ya no está en la lista.

---

## 1. La construcción

```lean
theorem exists_isChain (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true)
    (hpos : 0 < (filterAll g reqs).current_step) :
    ∃ sel, IsChain (filterAll g reqs) sel
```

Es un **descenso**:

1. Coge un nodo del paso más alto. Existe, por `node_at_every_step` (v25).
2. En un punto fijo válido todo nodo pasa `isValidNode` (`review_node_valid`, tuyo).
3. Un nodo por encima del paso 0 **no es raíz**, así que `isValidNode` le exige tener padres.
4. Un padre es un nodo superviviente, y está **exactamente un paso por debajo**.
5. Baja hasta el paso 0.

Los pasos 3 y 4 no se podían dar antes de este turno. Hicieron falta tres invariantes nuevos.

## 2. Los tres invariantes (`Model/Parents.lean`)

| | |
|---|---|
| `PN` | todo padre de un nodo superviviente es un nodo superviviente |
| `PBelow` | un padre está exactamente un paso por debajo |
| `NotRoot` | un nodo por encima del paso 0 no es raíz |

`PBelow` y `NotRoot` salieron **gratis de `Pruned`**: los padres solo encogen y los `id` nunca cambian, así que basta demostrarlos en `initSeed`, `addNode` y `join`.

`PN` no. `Pruned` registra que los padres encogen, no que los **nodos** que nombran sobrevivan. Es cierto —`removeNode` desenlaza el id que elimina— pero hay que demostrarlo operación por operación, como en v25.

Y `NotRoot` en `addNode` sale de tu `MachineOk`: el nodo nuevo tiene `parent_id := map_parent`, y `MachineOk` dice que `map_parent ≠ none` en cuanto `current_step > 0`. Otra pieza de diseño tuya que resulta ser exactamente lo que hacía falta.

## 3. Lo que esto es, sin inflarlo

**`IsChain` nunca fue la parte difícil.** Que exista un camino padre→hijo de arriba abajo es plausible desde el primer día; lo que faltaba era demostrarlo en Lean, y para eso hacía falta la fontanería de arriba.

Lo que gana el proyecto es concreto: **sale de la lista**. `FilteredChain` pedía `ChainSound`, que es `IsChain ∧ PairwiseOwned` más cuatro condiciones. Ahora:

| pieza | estado |
|---|---|
| `IsChain` | **demostrado** (v27) |
| `ChainG`, cláusula `gowners` | gratis para cadenas del soporte de un nodo (v26) |
| `PairwiseOwned` | **abierto — aquí está la Helly** |
| `self_owned`, `son_link`, `root_shape` | abiertos; parecen más invariantes del mismo tipo |

## 4. Y aquí está el matiz que hay que decir

El camino que construyo **no tiene por qué estar co-poseído**. Bajo eligiendo *un* padre cualquiera; nada garantiza que los nodos del camino se posean entre sí.

> Construir **un** camino es fácil. Construir **un camino co-poseído** es el problema.

Así que esto es progreso de fontanería, no de matemáticas. La diferencia con los turnos anteriores es que ahora `PairwiseOwned` está **completamente aislado**: no queda nada mezclado con él que sea cuestión de invariantes de la máquina.

## 5. Lo que sospecho de lo que queda

- `root_shape` parece casi inmediato desde `NotRoot` más la dirección recíproca.
- `son_link` pide un invariante de simetría padre/hijo — mismo idioma, probablemente factible.
- `self_owned` pide que un nodo se posea a sí mismo en el punto fijo; menos claro, porque `intersectOwners` puede quitarlo.
- **`PairwiseOwned` no creo que salga por esta vía.** Ahí está la propiedad de Helly, y ninguna cantidad de invariantes estructurales la va a dar.

No lo he intentado, para no prometer de más.

---

## 6. Estado

| | |
|---|---|
| **`PairwiseOwned`** | **lo que queda de verdad** |
| `IsChain` | demostrado (v27) |
| tres invariantes de forma | demostrados (v27) |
| dominios no vacíos y concretos | demostrado (v26) |
| `GownersAreNodes` | demostrado (v25) |
| `MachineOk`, condiciones laterales | demostrados (v22) |
| `Certifies` seed / join | demostrados (v21) |
| el checker de `Supported` | demostrado (v16) |

Sin refutar: 1.048.889 nodos verificados, 16.444 descensos completos, 0 violaciones.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 65 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
