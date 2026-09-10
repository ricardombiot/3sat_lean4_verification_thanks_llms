# Verificación para el Autor v43: la supervivencia a `cleanInvalid`, demostrada — y el testigo no es un camino

Ricardo, soy Claude (Opus 5). Ataqué la supervivencia del camino a `cleanInvalid`. El resultado tiene una parte que no esperaba y que cambia cómo hay que mirar el problema: **el testigo no puede ser un camino.** No por falta de técnica — es que un camino que se sostiene a sí mismo *es* `PairwiseOwned`. El objeto correcto es otro, y con él el teorema sale.

---

## 1. Por qué el camino no vale

Sigamos el argumento. `cleanInvalid` vuelve a intersectar los owners de cada nodo con los owners globales **actuales**, y esos encogen según la barrida va eliminando nodos. Así que para que un nodo siga pasando `isValidNode` necesita, en cada paso, un owner **que también sobreviva**. Iterando eso, el testigo tiene que estar cerrado bajo su propio soporte.

Y ahí está el punto: **si insistes en que el testigo sea un camino —un nodo por paso— «cerrado bajo su propio soporte» es exactamente `PairwiseOwned`.** No hay atajo por caminos. Eso explica de una vez por qué v27 (el descenso) y v41 (el enhebrado) no pueden terminar el trabajo solos: no les falta un ingrediente, les sobra la forma.

Pero `isValid` **no pide una cadena**. Pide un owner global en cada paso. El testigo no tiene por qué ser un camino.

## 2. El objeto correcto: un conjunto auto-sostenido

```lean
structure Closed (g : GPathM) (S : PathNodeId → Prop) : Prop where
  gow     : ∀ p, S p → p ∈ g.gowners
  node    : ∀ p, S p → (g.node? p).isSome = true
  support : ∀ p n, g.node? p = some n → S p → ∀ l en rango, ∃ v ∈ n.owners, S v ∧ v.id.step = l
  parent  : ∀ p n, … → p.parent_id ≠ none → ∃ c ∈ n.parents, S c
  son     : ∀ p, S p → p.id.step ≠ g.current_step - 1 →
              ∃ c m, S c ∧ g.node? c = some m ∧ p ∈ m.parents
  coown   : miembros enlazados se poseen mutuamente
```

**El teorema:**

```lean
theorem Closed_cleanInvalidGo (S) : ∀ ids g, Sons.SMP g → Closed g S → Closed (cleanInvalidGo g ids) S

theorem isValid_cleanInvalid_of_Closed (g) (S) (hsmp) (h : Closed g S)
    (hcov : ∀ l en rango, ∃ p, S p ∧ p.id.step = l) : isValid (cleanInvalid g) = true
```

> **La barrida no puede eliminar a un miembro de un conjunto auto-sostenido**, y si el conjunto llega a todos los pasos, la barrida deja el grafo válido.

Cierres `[propext, Quot.sound]`. `AbsSat/GraphPath/Model/Survive.lean`.

El corazón es `isValidNode_of_Closed`: cada cláusula de `isValidNode` la contesta una cláusula de `Closed` — la tabla de soporte con `support`, los padres con `parent`, los hijos con `son` dado la vuelta por `Sons.SMP`. Y la inducción sobre `cleanInvalidGo` es lo que hace el trabajo: en cada una de las tres suboperaciones (intersección de owners, desenlace, eliminación) hay que reestablecer las seis cláusulas.

**Un detalle de diseño que importa.** La cláusula `son` está escrita a través de la tabla de **padres**, no de la de hijos. No es capricho: así `Sons.SMP` la convierte en enlace de hijo cuando hace falta, y el espejo inverso —el que no existe— nunca se usa dentro del teorema.

## 3. Lo que de `Closed` sale gratis

Para el conjunto que el pinchazo define, `S = {n : n posee, en el paso pinzado, un nodo con el id de mapa elegido}` —que es exactamente lo que `cleanInvalid` intenta conservar—:

| cláusula | estado |
|---|---|
| `gow` | gratis (un nodo es owner global; en el paso pinzado `OOS` fuerza que su propio id sea el pinzado) |
| `node` | gratis, por construcción |
| `parent` | gratis (`coherent_parents`: el owner pinzado de un miembro lo posee algún padre, y ese padre es miembro) |
| `coown` | **gratis, demostrado**: `coown_of_bridge` |
| `son` | debido *estructuralmente* (el espejo inverso) |
| `support` | **el residuo** |

`coown_of_bridge` merece una línea: `Sons.SMP` da la vuelta a un enlace de padre y el puente de v39 hace owner tanto al padre como al hijo. Cierre `[propext]` — ni siquiera `Quot.sound`.

## 4. El residuo, dicho sin adornos — y medido

`support` dice: **en cada paso, un miembro posee a un miembro.** Es decir, que la poda tiene un núcleo arco-consistente no vacío. Eso **es** `PickValid`, escrito sin ninguna referencia a cadenas. No lo he demostrado.

Lo que sí he hecho es medirlo, junto con la cláusula `son` (`lake exe extend --closed`, dos semillas):

| campaña | comprobaciones de `support` | fallos | comprobaciones de `son` | fallos |
|---|---|---|---|---|
| 8 casos, semilla 2026, 3..5 vars | 667.682 | **0** | 45.312 | **0** |
| 10 casos, semilla 90210, 3..6 vars | 4.357.895 | **0** | 237.503 | **0** |

Cinco millones de comprobaciones de auto-soporte, cero fallos. Y la cláusula `son` —la que depende del espejo que falta— tampoco falla nunca, lo que dice que ese hueco es de formalización, no de matemáticas.

## 5. Estado

| | |
|---|---|
| Un conjunto auto-sostenido sobrevive a `cleanInvalid` | **demostrado** |
| `isValid` tras la barrida, si el conjunto cubre los pasos | **demostrado** |
| `coown` para miembros enlazados | **demostrado** (`[propext]`) |
| `gow`, `node`, `parent` para el conjunto del pinchazo | gratis (no ensamblados en Lean) |
| `son` | hueco estructural: el espejo hijos→padres |
| `support` | **el residuo** — 0 fallos en 5,0 M de comprobaciones |
| Pasadas de coherencia | fuera de este teorema (v41: 0 invalidaciones medidas) |

Lo que ha cambiado de forma: antes «`PickValid`» era una afirmación sobre la review entera. Ahora es una afirmación sobre **un conjunto**: que el núcleo arco-consistente del pinchazo no se vacía en ningún paso. Sigue sin estar demostrada, pero ya no se disfraza de pregunta sobre caminos.

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 74 módulos, 0 `sorry`, cierres `[propext, Quot.sound]` o más finos.*
