# Verificación para el Autor v104: la máquina decide las fórmulas Horn

Ricardo, soy Claude (Opus 5). Este es el plan en cinco piezas acordado tras v103: demostrar, sobre `SatMachinePure` tal
como está, que la máquina decide una clase concreta de fórmulas, las Horn (como mucho un literal positivo por cláusula).
Está hecho, sin hipótesis abiertas para esa clase.

Todo está en el build de `AbsSat` (137 módulos), sin `sorry`, en `[propext, Quot.sound]`.

---

## El resultado

**`horn_decides`** (`HornDecision.lean`): si φ está bien formada y es Horn,

`is_satisfiable (run_pure φ) = true ↔ Satisfiable φ`.

Además, sin suponer Horn, **`pureRun_nil_of_conflict`**: si la propagación unitaria sobre las cláusulas llega a un
conflicto, la última línea de la máquina queda vacía y la respuesta es UNSAT (`unsat_of_conflict`).

## Las cinco piezas

| Pieza | Módulo | Qué demuestra |
|---|---|---|
| 1 | `FixAgreeInv.lean` | `FixAgree_reachable`: en todo estado alcanzable, un nodo y cada uno de sus owners nunca fijan una variable a valores distintos |
| 2 | `Cnf/UnitProp.lean` | la propagación unitaria (`Forced`, `Conflict`) como inductivo; lo derivado es cierto en todo modelo (`forced_true`), un modelo no deja conflicto, monotonía |
| 3 | `UnitPropReview.lean` | `forced_unsupported`: todo nodo que fija la negación de un literal derivado queda sin soporte tras el filtro; **`conflict_invalid`**: un conflicto sobre las cláusulas ya leídas y los pins del destino invalida el filtro |
| 4 | `Cnf/HornModel.lean` | **`Cnf.horn_satisfiable_iff`**: una fórmula Horn es satisfacible si y solo si la propagación unitaria no da conflicto |
| 5 | `HornDecision.lean` | el último avance lleva todos los estados al nodo final del mapa con todas las cláusulas leídas; con conflicto, todos los envíos se descartan |

## Cómo encajan

- **SAT ⇒ satisfacible**: si la máquina dice SAT, la última línea no está vacía; por la pieza 5 no hay conflicto; por la
  pieza 4 hay modelo.
- **Satisfacible ⇒ SAT**: ya estaba demostrado (`completeness_pure`).

La pieza 3 es la que habla de la máquina: combina la invariante de la pieza 1 con las filas de cláusula del mapa. Si una
cláusula procesada tiene todos sus literales menos uno refutados, cada fila del mapa que la owner-ea pone a verdadero ese
último literal, y los nodos que lo contradicen pierden soporte en el review.

## Detalles de Lean

- El modelo de la pieza 4 se **calcula**, no se elige: encadenamiento hacia delante desde todo falso, iterado
  `|heads| + 1` veces. Cada ronda que no es punto fijo enciende una variable nueva de una lista finita (`count_strict`),
  así que se llega al punto fijo (`hornModel_closed`). Así se evita `Classical.choice`.
- `omega` con una disyunción en la meta (`b = 0 ∨ b = 1`) introducía `Classical.choice` en `varVal_01`; se separaron los
  casos a mano.

## Qué significa y qué no

- **Demostrado**: para fórmulas Horn, la respuesta rápida de la máquina (hay estados válidos al final) es correcta. Es la
  primera clase de fórmulas para la que `SendExact` deja de ser necesario.
- **No demostrado**: el coste de la ejecución; ni otras clases (2-SAT, o el caso general). Para el caso general sigue
  abierto `SendExact`.

Build: `lake build AbsSat` verde, 137 módulos, 0 `sorry`, `[propext, Quot.sound]`.
