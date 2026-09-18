# Verificación para el Autor v141: el veredicto, con el invariante de vuelta como hipótesis declarada

Ricardo, soy Claude (Opus 5). Como en v133 hice con `CommonOwner`, este informe fija **una** hipótesis
declarada para el veredicto de la máquina *Improves*. La nueva es mucho más concreta: habla de **una sola
pasada de una sola operación** de tu máquina, en lugar de sus estados en conjunto.

Rama `spaik`, build de `AbsSat` (201 jobs), sin `sorry`, `[propext, Quot.sound]`. Módulo
`AbsSat/GraphPath/Model/DeclaredVerdict.lean`.

---

## 1. El resultado

> **`DeclaredVerdict.verdict_iff`** — para φ bien formada, bajo la hipótesis declarada `GhostsLine φ`:
> **algún estado de lector de la última línea es válido ⟺ φ es satisfacible.**

Sus dos mitades, por separado:

| teorema | enunciado | hipótesis |
|---|---|---|
| `unsat_sound` | ejecución vacía ⟹ φ insatisfacible | **ninguna** |
| (⇐ de `verdict_iff`) | φ satisfacible ⟹ algún estado final válido | **ninguna** |
| `sat_sound` | estado final válido ⟹ φ satisfacible | `GhostsLine` |

## 2. La hipótesis, en una línea

> **`GhostsLine`** — *tras una pasada del review base sobre un estado de la ejecución, fijado, cuyas tablas
> eran exactas, toda compatibilidad que ya no sostiene ningún camino superviviente es asimétrica, o no
> comparte owner en algún paso.*

Dicho con tu vocabulario: **tras limpiar con la tabla global y revisar padres e hijos una vez, toda
incoherencia que queda es de las que tu filtro agresivo detecta** —por su pata de simetría o por su pata
de pertenencia a camino—.

En Lean:

```lean
def GhostsDetectable (B R : GPathM) : Prop :=
  ∀ x v nx nv, B.node? x = some nx → B.node? v = some nv → (x, v en rango) → v ∈ nx.owners →
    x ∉ nv.owners ∨ sharesEveryStep B.current_step nx.owners nv.owners = false ∨ Realizes R x v

def GhostsLine : Prop :=
  ∀ k kv, StateOkF φ k kv → MInv φ kv.2 → TablesSound kv.2 → ∀ ws rq,
    isValid (filterAllAgg (filterWeakAll kv.2 ws) rq) = true →
    GhostsDetectable (review (pinnedW kv.2 ws rq)) (filterAllAgg (filterWeakAll kv.2 ws) rq)
```

## 3. Por qué es el sitio correcto para parar

**Es concreta.** `CommonOwner` (v133) hablaba de las cadenas parciales de un estado cualquiera. Esta
habla de **una pasada** de la operación más estudiada del proyecto (limpieza + padres + hijos), aplicada a
un estado que **era exacto**, y dice exactamente qué deja esa pasada: incoherencias que tu barrido
reconoce.

**Todo lo demás está demostrado alrededor de ella.** La cadena completa, operación por operación de tu
ciclo:

| pieza | contenido | estado |
|---|---|---|
| semilla, UP, unión | conservan las rebanadas (la tabla de cada nodo = nodos de los caminos que pasan por él) | demostrado (v135, v140) |
| fijar + review | conserva las rebanadas **si** vale `GhostsLine` | demostrado (`tablesSound_of_ghosts`, sin razonar sobre el orden del barrido) |
| toda la ejecución | tiene rebanadas por tablas | demostrado bajo `GhostsLine` (`run_slices`) |
| veredicto | estado válido ⟹ su rebanada contiene un camino ⟹ modelo | demostrado (`sat_of_slices`) |

**Está medida sin excepción, y en su forma más exigente.** No solo con los requisitos que la máquina
aplica, sino con **cualquier** fijación de un nodo de mapa sobre **cualquier** estado exacto:

| hecho medido | volumen | excepciones |
|---|---|---|
| entradas fantasma que sobreviven al review completo | 3,02 M (K4, paridad) | **0** |
| fantasmas que llegan al barrido y no son detectables por pares | 4.764 que llegan | **0** |
| fijar cualquier nodo de mapa y revisar da exactamente la unión de los caminos que pasan por él | 21.709 fijaciones (K4, paridad, Tseitin sobre grafos aleatorios) | **0** |
| cada estado de la máquina = unión de los caminos del oráculo | todas las familias, incl. 8.032 estados aleatorios | **0** |

## 4. La historia de la hipótesis

Cada paso cambió la hipótesis por otra más cercana a una operación concreta de tu máquina:

| informe | hipótesis | de qué habla |
|---|---|---|
| v133 | `CommonOwner` | las cadenas parciales de un estado |
| v138 | `ReviewJoin` | el review de una unión |
| v139 | `SupportCover` | los apoyos del review de una unión |
| v140 | `FilterSlices` | fijar + review conserva las rebanadas |
| **v141** | **`GhostsLine`** | **una pasada del review base** |

Una advertencia de precisión: no está demostrado que `GhostsLine` sea **más débil** que `CommonOwner`;
son enunciados distintos, cada uno suficiente para el veredicto. La ventaja de `GhostsLine` es de
naturaleza, no de fuerza: es un hecho sobre una operación, y dice **cuál** de tus mecanismos hace qué.

## 5. Qué significa aceptarla, y qué no

**Lo que es**: un teorema de corrección condicional con la condición aislada en una frase sobre una
pasada de una operación, con todo lo demás demostrado y la condición medida sin excepción.

**Lo que no es**: una demostración de que la respuesta SAT sea siempre correcta. Si `GhostsLine` fallara en
alguna instancia, la respuesta SAT podría ser incorrecta en ella. La respuesta **UNSAT** sí es correcta
siempre, y la respuesta SAT **acompañada de su camino** también (v134): se comprueba en tiempo lineal.

## 6. Cómo se falsaría

Un contraejemplo sería: un estado de la ejecución con tablas exactas, una fijación, y una entrada que,
tras una pasada del review base, **no está en ningún camino superviviente** y sin embargo es **simétrica
y comparte owner en todos los pasos**. La sonda `helly ghosts` busca exactamente eso.

Dónde buscaría, por orden: fórmulas de Tseitin sobre grafos bien conectados de tamaño creciente (la
hipótesis de anchura de v139 predice fallos ahí si los hay); y el lema aislado de v140 §5, sin máquina,
con búsqueda adversarial sobre sistemas de requisitos "y ⇒ r".

## 7. Qué la haría incondicional

Una demostración de `GhostsLine`. Nueve reducciones locales están refutadas por medida (v139, v140), así
que tendría que ser global. Las dos vías que veo:

1. **Reducción** al lema combinatorio independiente de v140 §5 (el review de la unión de todas las
   soluciones de requisitos "y ⇒ r", tras fijar, es exacto), y demostrarlo como resultado sobre sistemas
   de requisitos.
2. **Anchura** (v139 §6): demostrarlo para la clase de fórmulas cuya anchura, respecto a las ventanas de
   dos cláusulas que llevan tus nodos, está acotada. Sería un teorema de corrección para una clase amplia
   y bien definida.
