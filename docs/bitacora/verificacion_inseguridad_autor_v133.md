# Verificación para el Autor v133: el veredicto, con una hipótesis declarada

Ricardo, soy Claude (Opus 5). Este informe cierra la línea: el veredicto de *Improves* queda demostrado
en Lean **en los dos sentidos**, con **una** hipótesis declarada en el sentido SAT. La hipótesis tiene
nombre, enunciado corto, evidencia medida y cinco rutas alternativas refutadas. Escribo también, con
claridad, qué **no** significa aceptarla.

Rama `spaik`, build de `AbsSat` (191 jobs), sin `sorry`, cierre de axiomas `[propext, Quot.sound]` en
todos los teoremas citados.

---

## 1. Los dos teoremas

**Sentido UNSAT, sin hipótesis:**

> `ConservationImproves.pureRunW_ne_nil` — si φ es satisfacible, la ejecución de la máquina **no
> muere**.

Es decir: si la máquina termina sin estados, φ es insatisfacible. El filtro débil y el barrido agresivo
—tus dos últimas mejoras— no pierden soluciones, y eso está demostrado sin condiciones.

**Sentido SAT, con la hipótesis declarada:**

> `NoDeadEndVerdict.sat_of_commonOwner` — para φ bien formada, si `kv` es un estado de la ejecución, su
> estado de lector es válido y en él se cumple **`CommonOwner`**, entonces φ **es satisfacible**.

Es decir: leer un camino garantiza modelo, bajo `CommonOwner`.

## 2. La hipótesis, en una línea

> **`Descent.CommonOwner g`** — los picks de una cadena parcial de `g` tienen un **owner común** en el
> paso inmediatamente inferior.

Nada más. Un estado, un paso, sin cuantificar sobre fijaciones, uniones ni rebanadas.

**Por qué es el sitio correcto para parar.** Tu barrido ya da exactamente eso **par a par**: dos owners
cualesquiera comparten entrada en cada paso (`AggFixpoint.aggOk_reviewAgg`, tu filtro simétrico de
v121). Lo que falta es el salto de pares al conjunto entero de picks, que forman una *clique* de la
relación de compatibilidad. En lenguaje de propagación de restricciones: la máquina mantiene
**2-consistencia** y el descenso necesita **k-consistencia**. Y `CommonOwner` es **equivalente** a que
las tablas de la máquina sean exactas respecto a los caminos —lo que las sondas miden desde v119—, así
que no hay forma de sustituirla por algo más débil sin demostrar la exactitud.

## 3. Lo que sostiene el teorema (todo demostrado)

| pieza | contenido |
|---|---|
| `ReaderAggRun.MInv`, `LineInv_steps` | todo estado de la ejecución cumple los invariantes, línea a línea |
| `AggFixpoint.aggOk_reviewAgg` | un estado revisado es punto fijo del barrido: tablas simétricas y pares consistentes en todos los pasos |
| `AdjacentOwners.owners_below_iff_parents` / `_above_iff_sons` | los owners de los pasos contiguos **son** los padres (y los hijos) |
| `ParentWitness.parents_id_eq` | todo padre de un nodo lleva el nodo de mapa que nombra el ID del propio nodo |
| `ParentWitness.owners_below_unique` | con un solo padre por nodo, el pasado de un nodo es un camino único |
| `RunEnv.runWithin_of_wf` | **invariante de ejecución incondicional**: ninguna tabla lleva nunca, en su paso o por debajo, una entrada ajena a la que nació con el nodo |
| `RunEnv.shared_tables_common_bound` | los dos lados de una unión acotan un nodo compartido con la **misma** cota |
| `NoDeadEnd.topAnchor_of` | el ancla del paso alto **siempre existe** |
| `Descent.extend_of_common_owner` | la extensión de una cadena parcial **es** exactamente un owner común; las otras seis condiciones salen de los invariantes |
| `Descent.extend_anchor`, `extend_pair` | los dos primeros escalones del descenso son gratis |
| `DescentUp.noDeadEnd_addNode` | **un UP mantiene el descenso**: el nodo que crea posee todas las elecciones del estado, así que no restringe nada |
| `DescentJoin.noDeadEnd_join`, `chain_in_left_slice`, `soundFrom_left_of_entries` | el **join** mantiene el descenso; la entrada al ancla es siempre del lado que la tiene; y una cadena de la unión es cadena de un lado en cuanto sus entradas lo son (seis de las siete condiciones demostradas) |
| `DescentFilter.noDeadEnd_filterAllAgg_of_completion` | el filtro mantiene el descenso dada la compleción — reformulación en la moneda de "no se pierde ninguna solución" (su hipótesis es equivalente a la conclusión; no lo cuento como reducción) |
| `Descent.noDeadEnd_of_commonOwner` | y de `CommonOwner` sale `NoDeadEnd` |
| `NoDeadEndVerdict.sat_of_denotS`, `sat_of_noDeadEnd`, `sat_of_commonOwner` | y de ahí el veredicto |

Además, siete reducciones del veredicto SAT por otras vías, todas demostradas y todas **más fuertes**
de lo necesario: `sat_of_pinExact`, `sat_of_someSupported`, `sat_of_someSpcStable`, `sat_of_pairChain`,
`sat_of_noBorrow`, `sat_of_hpv`, `sat_of_joinSplit`.

## 4. La evidencia de la hipótesis

Todas las sondas están en `lean_project/Probes/` y son reproducibles.

| hecho medido | volumen | excepciones |
|---|---|---|
| el descenso nunca se atasca (`NoDeadEnd`, espacio de cadenas **entero**) | 5 familias Tseitin, ~3,4 M extensiones | **0** |
| las cadenas de una unión nunca se mezclan | 6 familias (incl. aleatorias), 5.679 uniones, **1.027.901** cadenas | **0** |
| las fijaciones son exactas | 19,2 M entradas | **0** |
| fijar = construir la rama | 1.725 fijaciones | **0** |
| `PairChain`: ningún par de owners sin cadena | todas las líneas y recorridos del lector | **0** |
| las uniones no prestan elecciones | 2,5 M elecciones | **0** |

## 5. Las rutas refutadas (no volver sobre ellas)

Ocho, todas por medida:

| ruta | medida |
|---|---|
| relación de soporte estática (v119) | 32 nodos de rebanada perdidos |
| cierre de triángulos `SPC` (v122) | contraejemplo en K4 3-colores |
| soporte de doble rebanada (v123) | 2.026 nodos eliminados |
| rebanada del ancla como soporte (v130) | 72 / 15.180; 5.712 / 439.091; 592 / 122.050 |
| transitividad de la pertenencia (v132) | 52.720 / 380.746 |
| transitividad adyacente (v132) | 3.432 / 45.615 |
| "el pick vecino decide el padre" (v132) | 220 / 6.767 |
| rebanada = clique; candidatos anidados (v132) | 182.860 / 1.254.448; 175.024 / 9.073.621 |

Lo que dicen juntas: el owner común **existe siempre**, pero **no** lo determina ningún patrón local ni
monótono sobre las tablas. Es un fenómeno de tipo Helly genuino.

## 6. Qué significa aceptar la hipótesis, y qué no

**Lo que es**: un teorema condicional, con la condición aislada en un enunciado de una línea sobre un
solo estado y un solo paso, con el resto de la cadena demostrado y con la condición medida sin
excepción en seis familias. Es una posición defendible y verificable: cualquiera puede leer
`CommonOwner`, entenderla y comprobar el resto en Lean.

**Lo que no es**: una demostración de que el veredicto SAT sea correcto. Si `CommonOwner` fallara en
alguna instancia —y no he encontrado ninguna— el veredicto SAT podría ser incorrecto en ella. Tampoco
dice nada sobre el coste ni sobre clases de complejidad; es una afirmación de corrección condicional
sobre esta máquina.

## 7. Lo que la haría incondicional

Dos caminos, y la elección es tuya:

1. **Demostrar la exactitud de las tablas**, que es equivalente a `CommonOwner`. Las cinco rutas locales
   están cerradas; lo que queda es un argumento por construcción que use que la tabla de un nodo nace de
   **una** historia (`RunEnv`) y que el review la mantiene coherente paso a paso.
2. **Cambiar el diseño** (v129 §5): marcar la **procedencia** de cada entrada de owners. Con eso la
   exactitud sale por construcción y `CommonOwner` se demuestra, a costa de espacio — el mismo coste que
   separar los padres en el ID (v130 §3).

## 8. Pendiente, fuera de mi alcance

El `push` a `origin` falla con 403 (credenciales `ricautomation`); los commits de esta sesión están en
local sobre `spaik`. Y la URL de `origin` lleva un token personal en claro: conviene revocarlo y
reconfigurar el remoto.
