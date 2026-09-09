# Verificación para el Autor v28: La vía barata a `PairwiseOwned` está cerrada — y es la Helly, en tu vocabulario

Ricardo, soy Claude (Opus 5). Atacado `PairwiseOwned`. **No lo he demostrado, y no creo que salga por donde venía yendo.** Lo que he hecho es medir la relación de posesión, cerrar la vía barata con una refutación, y demostrar exactamente cuánto costaba esa vía. Te lo cuento con los números.

---

## 1. Por qué esta es distinta

Todas las obligaciones que he ido cerrando eran **locales**: una propiedad de un nodo, o de una operación, preservada paso a paso. `GownersAreNodes`, `MachineOk`, `PN`, `PBelow`, `NotRoot` — todas del mismo tipo, todas demostrables por inducción sobre la máquina.

`PairwiseOwned` no lo es. Es una propiedad de una **selección global**: todos los nodos elegidos se poseen entre sí. No hay inducción sobre operaciones que la dé.

Así que antes de intentar demostrar nada, medí la relación.

## 2. Lo que dice `lake exe extend --owners`

Campaña de 80 instancias aleatorias: **7.800 estados válidos, 259.187 nodos.**

| propiedad | violaciones |
|---|---|
| **`nodes ⊆ gowners`** — el id de todo nodo es owner global | **0** |
| **auto-posesión** — todo nodo se posee a sí mismo | **0** |
| **simetría** — si `q` posee a `n`, ¿`n` posee a `q`? | **1.364**, en 19 de 80 instancias |
| **clique del soporte** — los owners de un nodo, ¿se poseen entre sí? | **63.917.242**, en 80 de 80 |

Las dos primeras son invariantes candidatos, y las he dejado enunciadas. Las dos últimas están refutadas.

### Una corrección mía, y la anoto porque es de método

La primera versión de este documento decía que la simetría tenía **cero violaciones**. Lo decía a partir de **cuatro instancias elegidas a mano**. La campaña la refuta.

Cuatro instancias no son una medición, y tenía el arnés de campañas ahí mismo. Es exactamente el error contra el que llevo veinte turnos avisando, cometido por mí.

Visto en retrospectiva el mecanismo es evidente: `reviewNode` intersecta los owners de un nodo contra la **unión sobre sus vecinos**, y esa operación no es simétrica — `q` puede desaparecer de los owners de `n` mientras `n` sigue en los de `q`. Es el mismo mecanismo que v13 identificó.

## 3. Cuánto costaba la vía barata

Lo he demostrado, para que la refutación tenga peso:

```lean
theorem SupportClique_gives_PairwiseOwned (h : GPathM) (t : PNodeM)
    (hclique : SupportClique h t) (sel : Int → PathNodeId)
    (hsel : ∀ k, 0 ≤ k → k < h.current_step → sel k ∈ ownersAt t.owners k) ... :
    PairwiseOwned h sel
```

> Si el soporte de un nodo fuera un clique, **cualquier cadena sacada de ese soporte estaría co-poseída gratis.**

Y v27 ya construye caminos. Las dos juntas habrían cerrado `ChainSound` entero.

No lo hacen. Y el clique no falla por poco: **63,9 millones de violaciones, en las 80 instancias de la campaña.**

## 4. Y eso **es** la Helly, dicho en tu vocabulario

El contenido de la refutación es exactamente este:

> Dos nodos pueden ser **ambos compatibles con `t`** y **incompatibles entre sí**.

Eso es la propiedad de Helly fallando, dicha con `owners` en vez de con conjuntos convexos. Y explica de una vez por qué las rutas anteriores se quedaban cortas — v13 (anchura), v17 (hipergrafo), v18 (`Extendable`): todas intentaban obtener información global de información por pares, y la medición dice que la información por pares **no la contiene**.

## 5. Lo que sí queda como diana demostrable

Las **dos** propiedades que sobreviven a la campaña. Y una de ellas paga directamente:

```lean
theorem self_owned_of_SelfOwned ... : ∀ k, ... → sel k ∈ ownersOf h (sel k)
```

`SelfOwned` — todo nodo se posee a sí mismo — cierra **directamente** una de las tres condiciones que le faltaban a `ChainSound`. El puente está demostrado; falta el invariante.

`NodesAreGowners` es la otra, y es del tipo que sí sé demostrar (mismo idioma que v25 y v27). No la he hecho en este turno.

`OwnersSymmetric` queda **refutada**, y anotada en el código como lo que es: un invariante de aspecto plausible que resulta falso, con el mecanismo escrito al lado.

## 6. Lo que no voy a fingir

No he demostrado `PairwiseOwned`, y después de esta medición **no creo que salga de más invariantes estructurales**. Lo que queda ahí es matemática sobre la red de restricciones que genera tu mapa, no fontanería sobre el grafo.

Dicho de otro modo: he pasado veinte turnos quitándole a la obligación todo lo que era mecánico. Lo que queda es lo que era irreducible desde el principio — y ahora está solo, con nombre, medido, y con la vía barata formalmente descartada.

---

## 7. Estado

| | |
|---|---|
| **`PairwiseOwned`** | **lo que queda; la Helly** |
| ~~`SupportClique`~~ | **refutado** (v28) — con el coste demostrado |
| ~~`OwnersSymmetric`~~ | **refutado** (v28) — 1.364 violaciones en 19/80 |
| `SelfOwned` → `ChainSound.self_owned` | puente demostrado, invariante medido (0 en 259.187 nodos) |
| `NodesAreGowners` | medido (0 en 259.187 nodos), sin demostrar |
| `IsChain` | demostrado (v27) |
| dominios no vacíos, `GownersAreNodes` | demostrados (v25, v26) |
| `MachineOk`, `Certifies` seed/join | demostrados (v21, v22) |
| el checker de `Supported` | demostrado (v16) |

Y lo que no ha cambiado en veinte turnos: **sin refutar.** 1.048.889 nodos verificados, 16.444 descensos completos, 604.178 nodos con propagación exhaustiva. Cero violaciones.

---

*Claude (Opus 5), 2026-09-09. §2 corregida tras la campaña de 80 instancias: la simetría es falsa. `lake build AbsSat` verde, 66 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
