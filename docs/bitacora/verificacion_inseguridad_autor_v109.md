# Verificación para el Autor v109: Horn decidido, la profundidad refutada y la regla condicionada

Ricardo, soy Claude (Opus 5). Este tramo corre en paralelo a la línea de v105-v108 (requires débiles, poda por
pines, frontera y join): parte del plan Horn y no toca esos módulos. Tiene tres partes: se cerró el plan Horn, se midió que la
profundidad de refutación **no** está acotada por una constante, y de ahí salió una regla nueva —la
condicionada— que ya está formalizada y montada en un driver que no pierde soluciones.

Todo está en el build de `AbsSat` (155 módulos), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. La máquina decide las fórmulas Horn

**`horn_decides`** (`HornDecision.lean`): si φ está bien formada y es Horn,

`is_satisfiable (run_pure φ) = true ↔ Satisfiable φ`.

En cinco piezas:

| Pieza | Módulo | Qué demuestra |
|---|---|---|
| 1 | `FixAgreeInv` | un nodo y sus owners nunca fijan una variable a valores distintos |
| 2 | `Cnf/UnitProp` | la propagación unitaria como inductivo; lo derivado es cierto en todo modelo |
| 3 | `UnitPropReview` | **`conflict_invalid`**: un conflicto sobre las cláusulas leídas invalida el filtro |
| 4 | `Cnf/HornModel` | **`Cnf.horn_satisfiable_iff`**: Horn es satisfacible ⟺ no hay conflicto |
| 5 | `HornDecision` | el último avance vacía la línea ante un conflicto |

Sin suponer Horn: **`pureRun_nil_of_conflict`**, un conflicto de propagación unitaria deja la última
línea vacía, para cualquier fórmula bien formada.

El modelo de la pieza 4 se **calcula**: encadenamiento hacia delante iterado `|heads| + 1` veces,
con un conteo que crece estrictamente en cada ronda no fija. Así se evita `Classical.choice`.

## 2. La profundidad de refutación no está acotada

Sobre la familia `altchain` (cadenas de implicaciones con fuentes alternadas entre pins y literales
de un nodo), con `k` variables intermedias:

| Fórmula | k | Profundidad | Pasadas de la regla condicionada |
|---|---|---|---|
| m1 | 1 | 2 | 2 |
| m2 | 2 | 2 | 2 |
| m3 | 3 | 3 | 3 |
| m4 | 4 | 3 | 3 |
| m5 | 5 | 3 | 4 |
| m6 | 6 | 3 | 4 |
| m7 | 7 | ≥ 4 | 5 |

- **La profundidad crece como log₂(k + 2).** El análisis a mano de m5 lo explica: la refutación parte
  la cadena por la mitad y una fila de cláusula fija dos variables de cadena a la vez. La capacidad
  cumple `cap(d) = 2·cap(d−1) + 2`, o sea `2^d − 2`. El salto de 3 a 4 cae entre m6 y m7, medido.
- **Las pasadas crecen como ⌈k/2⌉ + 1**, linealmente: la regla no ramifica, propaga.
- Ninguna cota constante sirve, así que **la profundidad es el objetivo equivocado**; lo acotable es
  el número de pasadas, que está limitado por el número de pasos del mapa.

**Dos errores del código de medición**, corregidos antes de fiarme de nada: `adversary2` contaba como
zombi todo nodo cuya búsqueda agotaba el presupuesto, y `depth` se saltaba esos nodos. Además la
búsqueda de cadenas era exponencial en las variables libres; se reescribió como un problema de
restricciones con poda hacia delante y memorización, y da los mismos resultados en las fórmulas de
control, entre 1,6 y 5 veces más rápido.

## 3. La regla condicionada, medida en `altchain`

Condicionar a un nodo `x`, quedarse en cada paso con los owners globales compatibles con `x`, y
propagar. En `altchain_m1..m7`:

- elimina **exactamente** los nodos sin cadena (13.426, 23.338, 37.373, 53.893, 76.181, 100.933 y
  130.795, coincidiendo al nodo con el recuento independiente);
- ninguno de los supervivientes es de los que el review elimina, y nunca elimina un nodo que el
  review conserve;
- casi todos mueren en la pasada 0.

La variante **sin** condicionar no basta: deja vivos justo los nodos profundos, porque la cadena solo
es imposible *junto con* `x`.

## 4. Las tres piezas formales

| Módulo | Qué demuestra |
|---|---|
| `SacClosure` | `not_chainS_of_sacDead`: lo que la regla mata no está en ninguna cadena. `sacDead_of_unsupported`: la regla **subsume** el cierre de eliminación del review |
| `SacFilter` | `filterAC`, una pasada de consistencia de arco sobre los owners. `ChainSound_filterAC`: toda cadena sana lo atraviesa, **sin hipótesis lateral**. `sacDead_of_removed`: lo que descarta no tenía cadena |
| `ConservationFilter` | la conservación demostrada **una sola vez** para un filtro arbitrario, e instanciada: `pureRunSac_full_state` y `pureRunSac_ne_nil` |

Queda el sándwich: **lo que el review elimina ⊆ lo que la regla mata ⊆ lo que no tiene cadena**.

**Un hallazgo negativo que cambió el plan.** La dirección «`SacDead` ⇒ el review lo elimina» no puede
valer: `ReviewNodes.removed_unsupported` ya caracteriza lo que el review quita como `Unsupported`, y
`Unsupported` cuantifica sobre *todos* los owners de un nodo mientras que la regla lo hace solo sobre
los compatibles con el nodo condicionante. Condicionar es estrictamente más fuerte. Por eso la fuerza
extra hay que **añadirla a la máquina como filtro**, y no deducirla del review.

## 5. La regla condicionada, medida en la máquina

`improves-diff` compara ahora cuatro máquinas: base, débil, débil + pines y débil + condicionada
(`--sac <pasadas>`). Sobre las 4 fórmulas bien formadas de `test/cnf` y 9 aleatorias 6×24:

| Medida | Resultado |
|---|---|
| veredicto frente a base, débil, pines y fuerza bruta | igual en todas |
| última línea (claves, owners globales, nodos) | idéntica |
| el review tras el filtro acaba como el base | sí en todas (`sameSac`) |
| pasadas del review | −0 a −4 % (los pines: −17 a −38 %) |
| lo que elimina el review | −1 a −16 % (los pines: −96 a −100 %) |
| recorte propio del filtro | 301 a 20.718 de medida, pero solo 0 a 2.787 en los envíos donde el review base corre |
| tiempo | +40 a +70 % sobre la base |
| una segunda pasada | casi nada: 16.686 → 16.708 |

Es decir: **correcta y casi idempotente tras una pasada, pero no es una mejora de rendimiento a este
tamaño**. Recorta sobre todo en envíos que el filtro duro ya iba a invalidar. Su valor está en lo que
permite demostrar, no en lo que ahorra; y el punto fijo que la medición de `altchain` necesitaba en
⌈k/2⌉ + 1 pasadas aquí se alcanza en una.

## 6. Qué significa y qué no

- **Demostrado**: la máquina decide Horn; un conflicto de propagación unitaria da UNSAT en cualquier
  fórmula; la regla condicionada es correcta, subsume al review, y la máquina que la incorpora
  conserva todas las soluciones, con cualquier número de pasadas.
- **No demostrado**: el coste; que la regla elimine *todos* los nodos sin cadena fuera de `altchain`.
- **Abierto**: la dirección contraria, línea final no vacía ⇒ satisfacible, igual que en la máquina de
  referencia.
- **De regalo, y ya cobrado**: la conservación se demostró una sola vez para un filtro cualquiera, y
  las otras dos máquinas se rederivaron de ella. El núcleo común vive en `ConservationCore` (273
  líneas); `ConservationImproves` pasó de 601 a 205 líneas y `ConservationPins` de 921 a 480, con los
  mismos enunciados públicos y las mismas guardas de axiomas. La invariante genérica lleva ahora
  también el padre de cada nodo de la cadena (`SelParent`), que es lo que necesita un filtro que
  elimine **nodos** y no solo owners globales: la poda por pines lo requería, y cualquier
  endurecimiento futuro de la regla condicionada lo requerirá igual. Añadir un filtro cuesta una
  instancia, no una copia.

Detalles de Lean anotados por el camino: `omega` con una disyunción en la meta, `List.all_eq_false` y
`by_cases` sobre `Int` arrastran `Classical.choice`; `Bool.and_eq_true` no tiene `.mpr`; y este
proyecto trata el linter de variables sin usar como error.

Build: `lake build AbsSat` verde, 155 módulos, 0 `sorry`, `[propext, Quot.sound]`.
