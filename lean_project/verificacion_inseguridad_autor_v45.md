# Verificación para el Autor v45: `CoreCovers` partido en dos — y una mitad es teorema

Ricardo, soy Claude (Opus 5). Ataqué `CoreCovers`. **No lo he demostrado.** Lo que sí he hecho es partirlo, y la parte que se lleva la intuición —«¿hay candidatos en cada paso?»— resulta ser un **teorema**. Lo que queda es la otra mitad, y ahora está mucho más ceñido.

---

## 1. La partición

El núcleo se obtiene **estrechando** un conjunto candidato. Para un pinchazo en el paso `k` al id de mapa `mid`, el candidato es

```lean
def PinSet (g : GPathM) (k : Int) (mid : NodeId) : PathNodeId → Prop :=
  fun p => ∃ n, g.node? p = some n ∧ ∃ u ∈ ownersAt n.owners k, u.id = mid
```

Dos preguntas, entonces: **¿cubre el candidato todos los pasos?** y **¿el estrechamiento conserva la cobertura?**

La primera es teorema:

```lean
theorem pinSet_covers (g) (tctx : Threaded.TCtx g) (q) (nq) (hq) (hself)
    (h1 : 1 ≤ q.id.step) (hqhi) :
    ∀ l en rango, ∃ p, PinSet g q.id.step q.id p ∧ p.id.step = l
```

Sale directo del enhebrado de v42: el nodo pinzado tiene un camino completo cuyos nodos lo poseen todos, así que **cada paso tiene un candidato**. Cierre `[propext, Quot.sound]`.

Eso reorienta el problema. La dificultad no es *si hay algo compatible con la elección* —lo hay, en todos los pasos, demostrado— sino *si la compatibilidad sobrevive a su propia clausura*.

## 2. La cadena completa, de punta a punta

```lean
theorem isValid_cleanInvalid_pin (g) (tctx) (q) (nq) (hq) (hself) (h1) (hqhi)
    (hoos) (hrootz) (hsnn) (hnodegow) (hbelow) (hsmp) (hlink)
    (hsupport : …) (hson : …) :
    isValid (cleanInvalid (filterRequire g q.id)) = true
```

Del pinchazo a la validez, todo demostrado: el enhebrado da la cobertura, `Closed_PinSet` da la clausura, `Core_greatest` la sube al núcleo y `isValid_cleanInvalid_of_Core` cierra. **Las únicas hipótesis que quedan son `hsupport` y `hson`** — el residuo de v43, medido en 0 fallos.

Y dentro de `Closed_PinSet`, tres de las cuatro cláusulas restantes salen solas:

| cláusula | de dónde |
|---|---|
| `gow` | `OOS`: en el paso pinzado el único owner de un nodo es él mismo, así que un candidato *es* el id pinzado y sobrevive a `filterRequire` |
| `node` | por construcción |
| `parent` | `Threaded.hop_down` |
| `coown` | `coown_of_bridge` (v43) |

## 3. Y `support` es gratis en cuatro pasos

Esto es lo que más me gusta de la sesión, porque el ingrediente es tu propio arreglo. `support` pide un owner-candidato en **cada** paso. Cuatro no cuestan nada:

| paso | por qué |
|---|---|
| el **pinzado** | el candidato posee el nodo pinzado por definición, y el pinzado es candidato (se posee a sí mismo) |
| su **propio** paso | `SelfOwned` |
| el de **abajo** | `hop_down` da un padre que es candidato, y **el puente de v39 hace owner a todo padre** |
| el de **arriba** | `hop_up` y el lado de los hijos del puente; `SAbove` pone el paso |

```lean
theorem support_at_pin …   theorem support_at_self …
theorem support_below …    theorem support_above …
```

Todos con cierre `[propext, Quot.sound]`. Sin el arreglo del bug (v37–v39) ninguno de los dos últimos existiría: los padres no eran owners.

**Y por tanto el residuo es `support` a distancia ≥ 2.** Que es exactamente donde la transitividad refutada de v40 lo habría llevado: bajar dos veces da un candidato poseído por el *padre*, no por el nodo.

## 4. Medido

`lake exe extend --closed`, contando **solo** las comprobaciones que siguen siendo residuo:

| campaña | comprobaciones lejanas | fallos | cláusula `son` | fallos |
|---|---|---|---|---|
| 10 casos, semilla 90210, 3..6 vars | 3.473.942 | **0** | 237.503 | **0** |

De los 4.357.895 que v43 contaba, 883.953 —un 20 %— han pasado a ser teoremas. Los 3,47 M restantes siguen sin un solo fallo.

Y la medición del núcleo de v44 sigue en pie: 24.877 pinchazos, 0 pasos vacíos, con el núcleo calculado sin llamar nunca a `isValidNode`.

## 5. Estado

| | |
|---|---|
| El candidato cubre todos los pasos | **demostrado** |
| Cadena pinchazo → `isValid (cleanInvalid …)` | **demostrada** módulo dos hipótesis |
| `gow`, `node`, `parent`, `coown` para el candidato | **demostradas** |
| `support` en el paso pinzado, el propio y los dos vecinos | **demostrado** |
| `support` a distancia ≥ 2 | **abierto** — 0 fallos en 3,47 M |
| `son` (espejo hijos→padres) | hueco estructural — 0 fallos en 237 k |
| `CoreCovers`, `PickValid`, `PairwiseOwned` | abiertos, y son el mismo enunciado |

Lo que ha cambiado: la obligación ya no es «que el núcleo no se vacíe», que era una afirmación sobre un proceso. Es «que un candidato tenga soporte candidato **a distancia dos o más**», que es una afirmación sobre una relación, en un solo régimen, con todo lo demás pagado.

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 74 módulos, 0 `sorry`, cierres `[propext, Quot.sound]` o más finos.*
