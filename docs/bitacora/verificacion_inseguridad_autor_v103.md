# Verificación para el Autor v103: la máquina frente al oráculo de fuerza bruta

Ricardo, soy Claude (Opus 5). Este es el plan acordado en v102, siguiendo tu propuesta de
`docs/demostración_por_equivalencia.md`: demostrar que la máquina construye el mismo conjunto que un oráculo de fuerza
bruta, y dar un veredicto que coincide con el del oráculo sin hipótesis. Está hecho. Lo que queda abierto es lo mismo que
antes, ahora enunciado respecto al oráculo: que la respuesta rápida de la máquina (hay estados válidos) lea bien su propio
conjunto.

Todo está en el build de `AbsSat` (132 módulos), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. El oráculo, sin axiomas (`Cnf/BruteForce.lean`)

El módulo tenía dos axiomas y no estaba en el build. Ahora:

- `mem_enumAssignments_length`, `enum_complete`, `toAssign_map_range`: los dos axiomas pasan a ser teoremas;
- `bruteForceSat_sound` y `bruteForceSat_complete` sin axiomas propios;
- **`bruteForceSat_ne_nil_iff`**: la lista del oráculo no está vacía exactamente cuando la fórmula es satisfacible.

Importado en `AbsSat.lean`, con sus axiomas fijados.

## 2. La máquina frente al oráculo (`Oracle.lean`)

| Teorema | Dice |
|---|---|
| `Phi_to_oracle` | todo camino que representa la línea final viene de una cadena cuya asignación, restringida a las variables de φ, está en `bruteForceSat φ` |
| `oracle_to_Phi` | toda lista del oráculo nombra un camino que la línea final representa |
| `Phi_nonempty_iff_oracle` | el conjunto representado no es vacío si y solo si la lista del oráculo no lo es |
| `oracle_nonempty_run_pure` | si el oráculo encuentra solución, la máquina dice SAT (sin hipótesis) |
| `run_pure_iff_oracle_of_SendExact` | bajo `SendExact`, la respuesta de la máquina es la del oráculo |
| `answer_matches_oracle_iff` | la respuesta SAT de la máquina coincide siempre con el oráculo **si y solo si** una línea final no vacía representa algún camino |

La máquina simula el oráculo con otra representación. La última fila es la parte abierta: la prueba de vacío de la
representación.

## 3. El veredicto certificado (`CertifiedVerdict.lean`)

`certifiedVerdict φ` dice SAT si algún estado de la línea final tiene una selección (un nodo por paso) que el comprobador
`isCert` acepta.

| Teorema | Dice |
|---|---|
| `mem_selections` | toda selección que toma un nodo de cada línea está en la enumeración |
| `isCert_of_chain` | el comprobador acepta toda cadena del estado |
| `certifiedVerdict_sound` | un veredicto positivo implica satisfacible |
| `certifiedVerdict_complete` | una fórmula satisfacible tiene veredicto positivo |
| **`certifiedVerdict_iff_oracle`** | **el veredicto certificado es el del oráculo, sin hipótesis** |
| `machine_sat_of_certifiedVerdict` | un veredicto certificado positivo implica que la máquina dice SAT |
| `machine_matches_certified_iff` | la respuesta de la máquina coincide con el veredicto certificado si y solo si se cumple la misma prueba de vacío |

## 4. Qué significa y qué no

- **Demostrado**: la representación de la máquina, leída con un certificado comprobado, decide la satisfacibilidad
  exactamente como la fuerza bruta.
- **No demostrado**: el coste. La enumeración de selecciones es el producto de las líneas, así que en el peor caso cuesta
  lo mismo que la fuerza bruta. Un lector barato necesitaría no volver atrás, que es el lema del paso medido en v101 (0
  atascos con comprobación hacia delante) y cuya profundidad de refutación analizamos en v102.
- **Abierto**: que la respuesta rápida de la máquina (un estado válido) implique una cadena. Es `SendExact`, equivalente a
  `answer_matches_oracle_iff` y a `machine_matches_certified_iff`.

Un detalle de Lean: `beq_self_eq_true` y un `simp [e]` introducían `Classical.choice`; se sustituyeron por
`beq_iff_eq.mpr`.

Build: `lake build AbsSat` verde, 132 módulos, 0 `sorry`, `[propext, Quot.sound]`.
