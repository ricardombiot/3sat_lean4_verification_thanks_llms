# Verificación para el Autor v80: P3 reducida a una sola frase

Ricardo, soy Claude (Opus 5). P3 no está cerrada —lo digo primero— pero ya no es un programa: es **una frase**, y la frase es justo la que medí en v77.

---

## 1. El hallazgo que lo hizo fácil

Fui a leer `filterRequire` antes de escribir nada:

```lean
def filterRequire (g : GPathM) (req : NodeId) : GPathM :=
  { g with gowners := g.gowners.filter (fun q => q.id.step != req.step || q.id == req) }
```

**El pinchazo toca solo `gowners`.** Las tablas por nodo no las toca — quien las estrecha es el review, después. Así que de las nueve cláusulas de un tejido, el pinchazo amenaza exactamente **una**: `gow`, la que dice que los miembros son owners globales. Las otras ocho ni se enteran.

Eso explica de una vez la hipótesis que v79 encontró en `FOk_filterAll`: **es `gow` y nada más**. Y explica por qué falla en un paso de cláusula — el tejido que fabrica `addNode` se lleva *todos* los owners globales, luego contiene los dos valores de un paso pinzado.

## 2. El movimiento de v44, en el vocabulario del tejido

Si el problema es que el tejido es demasiado ancho, hay que estrecharlo. Y ahí vale exactamente lo que v44 descubrió para `Closed`:

> **Las cláusulas de un tejido se conservan bajo unión**, porque cada una se atestigua *dentro de un solo* tejido — son todas pertenencias o existencias, ninguna dice «y nada más».

Luego el **mayor tejido que cumple una restricción es él mismo un tejido**, y sale por construcción:

```lean
theorem Fabric_core (g : GPathM) (P : PathNodeId → Prop) :
    Fabric g (CoreS g P) (CoreT g P)          -- no depende de ningún axioma
```

Sin axiomas, ni siquiera `propext`. Me gustó verlo: es un teorema puramente estructural sobre tu invariante.

## 3. Lo que queda de P3: una frase

Con el núcleo, todo el paso de cláusula se descarga salvo un enunciado:

```lean
def PinReaches (g : GPathM) (reqs : List NodeId) (r : PathNodeId) (rn : PNodeM) : Prop :=
  CoreS g (fun q => Compat reqs q ∧ q ∈ rn.owners) r
```

*El mayor tejido cuyos miembros concuerdan con los tres requisitos de la cláusula y viven dentro de `owners(r)` sigue alcanzando `r`.* Y con eso:

```lean
theorem FabricAt_filterAll_of_PinReaches (g) (reqs) (r) (rn)
    (hr : (filterAll g reqs).node? r = some rn)
    (hsmp : Sons.SMP g) (hnr : Parents.NotRoot g)
    (h : PinReaches g reqs r rn) : FabricAt (filterAll g reqs) r
```

— el estado pinzado lleva un tejido que pasa por `r`, **filtro de cláusula entero y review incluidos**, apoyándose en el `FOk_filterAll` de v65 con la hipótesis descargada por construcción.

Y `PinReaches` es, palabra por palabra, el `CoreCovers` de v44 y **exactamente lo que midió v77**: el mayor tejido dentro de `owners(n)` en los pasos de cláusula, 124.246 nodos, cero fallos, controles Tseitin incluidos.

## 4. Dónde queda la ruta

| pieza | estado |
|---|---|
| **P1** el tejido nace (semilla, `addNode`) | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el estrechado a los pines sigue llegando | **reducida hoy a `PinReaches`**, una sola existencia |
| **P4** el puente `FabricAt ⟹ PickSome` | abierta, con su desajuste declarado |
| **P5** cierre con `L7.satisfiable_of_inhabited` | libre si caen las anteriores |

Lo que ha cambiado hoy no es que P3 esté hecha, sino que **ha dejado de ser nueve cláusulas a través de un filtro para ser una existencia sobre un objeto que ya sé calcular y que ya medí**.

Y el límite de siempre, sin adornos: `PinReaches` para toda fórmula sería 3SAT en P. Así que es **aquí** donde la hipótesis de clase tiene que entrar — y ahora está enunciada sobre tus `owners`, no sobre un modelo paralelo, que era la deuda que dejó v74.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto; los diez teoremas de `FabricAdd.lean` cierran en `[propext, Quot.sound]` salvo `Fabric_core`, que no usa ninguno.
