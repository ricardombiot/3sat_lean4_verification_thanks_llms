# Verificación para el Autor v41: `PickValid` — más pequeño, localizado, y con media pieza nueva

Ricardo, soy Claude (Opus 5). Ataqué `PickValid`. **No lo he cerrado**, y lo digo antes de nada. Lo que traigo son tres cosas concretas: la obligación es ahora estrictamente más débil, sé **en qué pasada de la review** vive el riesgo, y hay un teorema estructural nuevo que es exactamente el ingrediente que hace falta — demostrado a medias, con la mitad que falta nombrada con precisión.

---

## 1. La obligación era más grande de lo necesario

`PickValid` pide que **toda** elección permitida, en **todo** paso que aún tenga elección, propague a un grafo válido. Pero leyendo la inducción de v19, esta consume exactamente **una** elección buena por etapa: coge el primer `k` y el primer `q` porque era lo cómodo de escribir, no porque lo necesite.

```lean
def PickSome (g : GPathM) : Prop :=
  hasChoice g = true → ∃ k, 0 ≤ k ∧ k < g.current_step ∧ choiceAt g k = true ∧
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAll g [q.id]) = true

theorem Inhabited_of_pickSome (P) (hPf) (hnd) (hpick : ∀ g, P g → isValid g = true → PickSome g)
    (hbase) (g) (hP) (hv) : Inhabited g
```

La inducción corre igual. El decrecimiento de la medida sigue siendo gratis (`measure_lt_of_choiceAt`: un paso con elección siempre ofrece un owner global rival, sea cual sea la elección). Cierre `[propext, Quot.sound]`.

Es «la máquina nunca necesita retroceder» en su forma más débil. **Y la medición dice que la forma ∀ también aguanta**: `lake exe extend --pickvalid`, 2.794 estados válidos con elección abierta, **63.314** elecciones permitidas, **0** que invaliden. Así que la debilitación no compra un hueco medido — compra una obligación más pequeña que demostrar.

## 2. Dónde vive el riesgo: en la primera pasada, y casi en ninguna

`filterAll g [mid] = review (filterRequire g mid)`, y `review` itera `reviewPass = reviewSons ∘ reviewParents ∘ cleanInvalid`. El pinchazo en sí es inofensivo (`isValid_filterRequire`, v20). ¿Cuál de las tres barre el riesgo?

`lake exe extend --sweep`, 25 instancias, **39.984** elecciones permitidas:

| | |
|---|---|
| `cleanInvalid` sola deja el grafo **inválido** | **0** |
| la review completa lo deja **inválido** | **0** |
| elecciones donde las pasadas de coherencia quitan algo *más* | **67** (0,17 %) |
| nodos extra que quitan en total | **185** |

Es decir: la pasada que **hace** el trabajo del pinzado —`cleanInvalid`, la que intersecta con los owners globales estrechados— nunca invalida, y las dos pasadas de coherencia apenas tocan nada. `PickValid` es, en la práctica, un teorema sobre `cleanInvalid`.

Eso es una diana, no una demostración. Pero es una diana mucho más estrecha que «la review preserva la validez».

## 3. El ingrediente: cada nodo tiene un pasado enhebrado

Para que `cleanInvalid` no pueda vaciar un paso hace falta exhibir, tras el pinchazo, un superviviente en cada paso. Y un nodo sobrevive al pinchazo si posee algo del conjunto pinzado. Así que hace falta un **camino cuyos nodos posean todos un mismo ancla**.

No co-posesión por pares — **un ancla común**. Y eso sí lo paga la arco-consistencia:

> `coherent_parents` dice `d.owners ⊆ ⋃ owners de los padres de d`. Luego si `d` posee `a`, **algún padre de `d` posee `a`**.

Bajando con eso desde el nodo del ancla:

```lean
structure TPart (g) (a) (sel) (lo hi) : Prop where
  chain : PartialChain g sel lo hi
  owns  : ∀ i, lo ≤ i → i ≤ hi → a ∈ ownersOf g (sel i)

theorem threaded_below (g) (ctx : TCtx g) (a) (n) (hn : g.node? a = some n)
    (hself : a ∈ n.owners) … : ∃ sel, TPart g a sel 0 a.id.step
```

> **Todo nodo tiene un pasado enhebrado**: desde el paso 0 hasta su propio paso hay un camino enlazado por padres **cuyos nodos lo poseen todos**.

Cierre `[propext, Quot.sound]`, y ensamblado para los estados de la máquina (`threaded_below_filterAll`, con la auto-posesión de v30 poniendo el ancla en su propio camino).

Esto se coloca **estrictamente entre** v27 y `PairwiseOwned`: v27 construye un camino y no dice nada de posesión; `PairwiseOwned` pide que cada par se posea; esto pide que cada nodo del camino posea **uno** común. A diferencia de `PairwiseOwned`, es un teorema.

## 4. La mitad que falta, dicha con precisión

El teorema cubre el camino **por debajo** del ancla. Por encima falta, y sé exactamente por qué.

El argumento espejo funciona: `coherent_sons` da que si `d` posee `a`, algún **hijo** de `d` tiene un nodo que posee `a`. Pero entrega un nodo **sin paso**. Para convertirlo en «hay un nodo en el paso `j+1` que posee `a`» hace falta el espejo de `Parents.PBelow` para la tabla de hijos:

> **`SAbove`: todo hijo está un paso por encima.**

Y ese invariante no existe, y —a diferencia de `PBelow`— no sale gratis: `Pruned` lleva una cláusula `owners ⊆` y una `parents ⊆`, pero **ninguna de hijos**, así que necesita la inducción operación por operación que necesitó `Sons.SMP`. Eso, y solo eso, separa este módulo del teorema completo (un camino del paso 0 hasta arriba).

Está escrito en `Threaded.lean` donde iría `hop_up`, para que quien siga no tenga que redescubrirlo.

## 5. Y lo que seguiría faltando aun con el camino completo

Honestidad hasta el final: con el camino enhebrado completo, `cleanInvalid` tras el pinchazo se sobrevive —los owners fuera del paso pinzado no cambian, y en el pinzado el ancla está—, pero las **dos pasadas de coherencia** no se siguen de ahí. Ahí `reviewNode` intersecta con la unión de los vecinos, y para que un nodo del camino conserve soporte en un paso `l` cualquiera hace falta que **comparta un owner con su vecino en el camino en ese paso**. El ancla común da eso solo en el paso del ancla.

Es decir: el camino enhebrado cubre la pasada donde está el 100 % del riesgo medido, y no cubre las dos donde está el 0 %. Cuál de las dos frases pesa más, no lo sé.

## 6. Estado

| | |
|---|---|
| Caso base de la ruta A′ | **demostrado** (v40) |
| Obligación de la ruta A′ | `PickSome` (∃), estrictamente más débil que `PickValid` |
| Riesgo medido de esa obligación | **0** en 63.314 elecciones; concentrado en `cleanInvalid`, que nunca invalida |
| Camino enhebrado por debajo del ancla | **demostrado** |
| Camino enhebrado por encima | falta `SAbove` |
| `PairwiseOwned` general | abierto |

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 73 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
