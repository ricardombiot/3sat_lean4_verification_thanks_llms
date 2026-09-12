# Verificación para el Autor v61: la simetría vuelve — vale justo donde el lector trabaja

Ricardo, soy Claude (Opus 5). Fui a por el muro nuevo con la lección de v60: **mirar el estado final, no el recorrido**. Y lo primero que apareció fue una puerta que yo mismo había cerrado.

---

## 1. La simetría es falsa en el recorrido y cierta al final

En v54 medí la simetría de la propiedad —`q ∈ owners(p) ⟹ p ∈ owners(q)`— sobre **todos** los estados: 185 violaciones en 116.330 nodos. La di por refutada y cerré esa vía.

Estaba mirando el sitio equivocado. `lake exe extend --finalowners`, solo la línea final:

| campaña | estados finales válidos | nodos | **violaciones de simetría** |
|---|---|---|---|
| 20 casos, 2026, 3..5 vars | 16 | 857 | **0** |
| 30 casos, 31337, 3..5 vars | 26 | 1.309 | **0** |
| 25 casos, 4242, 4..6 vars | 22 | 1.683 | **0** |
| **total** | **64** | **3.849** | **0** |

**Las 185 violaciones están todas en estados parciales.** En el estado de longitud completa que la máquina entrega al lector, la propiedad es simétrica. Y tiene sentido: `addNode` da al nodo nuevo todos los owners globales y a nadie le añade el nodo nuevo — la asimetría es un artefacto de que aún faltan pasos por construir. Al completar el mapa, `isValidNode` obliga a todo nodo a tener un owner en el paso más alto, y la asimetría se resuelve.

## 2. Y con ella, dos teoremas

Con la simetría como hipótesis (medida, no demostrada), `Threaded.threaded` **se da la vuelta**:

```lean
theorem owners_contain_chain (g) (ctx : TCtx g) (hsym : OwnSymmetric g)
    (a) (n) (hn : g.node? a = some n) (hself : a ∈ n.owners) … :
    ∃ sel, IsChain g sel ∧ ∀ i, 0 ≤ i → i < g.current_step → sel i ∈ n.owners
```

> **La tabla de owners de un nodo no tiene solo una entrada por paso: contiene un camino entero**, enlazado padre→hijo del paso 0 a la cima.

Y con `OOS` —un nodo no tiene en su propio paso más owner que él mismo— ese camino **pasa por el nodo**:

```lean
theorem chain_through_of_symmetric … :
    ∃ sel, IsChain g sel ∧ sel a.id.step = a ∧
      ∀ i, 0 ≤ i → i < g.current_step → sel i ∈ n.owners
```

> **Bajo simetría, todo nodo está en un camino completo que él posee entero.**

Eso es `Verdict.SupportedAt` **salvo una cosa**: si los nodos de ese camino se poseen **entre sí**. Los dos teoremas, cierre `[propext, Quot.sound]`.

## 3. El atajo que no funciona — y por qué es bueno que no funcione

La idea obvia para la exactitud sería: coge un owner superviviente `q` de un nodo `n`, lee la asignación de los owners de `n` en los pasos de variable, y comprueba que satisface φ usando los requisitos de la fila de cláusula. Eso necesitaría que **los owners de un nodo sean mutuamente compatibles** — una *clique*.

No lo son, ni siquiera al final:

| campaña | pares de owners a pasos distintos | **no se poseen entre sí** |
|---|---|---|
| 2026 | 624.854 | 159.608 (26 %) |
| 31337 | 1.145.170 | 208.820 (18 %) |
| 4242 | 2.513.802 | 768.088 (31 %) |

Y la razón es **exactamente lo que v60 midió**: si los owners de un nodo son las proyecciones de **todas** las soluciones que pasan por él, dos owners suyos pertenecen a soluciones distintas y **no tienen por qué ser compatibles**. La clique sería falsa incluso en una máquina perfecta.

Es decir: el enunciado local correcto no es «los owners de un nodo son compatibles» sino «cada owner de un nodo comparte **una** solución con él». Por solución, no por nodo.

## 4. El residuo, medido donde vive

`lake exe extend --finalthread`, solo la línea final:

| campaña | anclas | cadena golosa **co-poseída** | la búsqueda encuentra otra | **sin cadena (zombi)** |
|---|---|---|---|---|
| 20 casos, 2026, 3..5 vars | 857 | 854 | 3 | **0** |
| 25 casos, 4242, 4..6 vars | 1.683 | 1.558 | 125 | **0** |
| **total** | **2.540** | **2.412** | **128** | **0** |

La escalada golosa nunca se atasca, y su cadena es co-poseída en el 95 % de las anclas; en el 5 % restante otra cadena sirve. **Cero zombis en 2.540 anclas del estado final.**

## 5. Dónde queda el muro

Antes de este informe: *existe una cadena co-poseída en todo estado válido.*

Ahora, en el estado final y con simetría disponible:

> **el camino que un nodo posee es co-poseído.**

Ya no hay que *encontrar* el camino —`chain_through_of_symmetric` lo da, y pasa por el nodo—; solo falta que sus nodos se posean entre sí. Y hay dos sub-objetivos nombrados debajo:

- **la simetría en longitud completa**, que es hipótesis medida y no teorema. El mecanismo está a la vista: `isValidNode` obliga a un owner en el paso más alto, y el paso más alto del mapa CNF es un único `FusionNode`;
- **la regla de elección**: la escalada golosa falla en el 5 %, y ahí sirve otra cadena.

## 6. Lo que esto **no** es

- **La simetría al final está medida, no demostrada.** Los dos teoremas la toman como hipótesis y lo dicen en su enunciado.
- 64 estados finales y 2.540 anclas: números modestos, porque solo las instancias satisfacibles dejan línea final.
- 3–6 variables. Complejidad, sin teoremas.
- No he demostrado la exactitud de v60; he reducido lo que hace falta para ella.

## 7. Estado

| | |
|---|---|
| Mitad de completitud (conservación + driver) | cerrada |
| Lector, pasadas de coherencia, `PickSome` ⟺ `Inhabited` | demostrados (v58, v59) |
| Estado final exacto (semántico) | 0 zombis / 0 espurios (v60) |
| **Simetría en el estado final** | **0 de 3.849 nodos** — hipótesis medida |
| **`owners_contain_chain`** (bajo simetría) | **demostrado** |
| **`chain_through_of_symmetric`** (bajo simetría + `OOS`) | **demostrado** |
| Clique de owners de un nodo | **falsa, y con razón** (18–31 %) |
| Cadena golosa co-poseída al final | 2.412 de 2.540; el resto, otra cadena |
| Zombis en el estado final | **0 de 2.540** |
| El camino que un nodo posee es co-poseído | abierto — el muro |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, 87 módulos, 0 `sorry`, 0 axiomas de proyecto.

---

*Claude (Opus 5), 2026-09-11.*
