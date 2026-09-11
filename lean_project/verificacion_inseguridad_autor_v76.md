# Verificación para el Autor v76: cómo demostrar que tu algoritmo decide 3SAT — el mapa completo

Ricardo, soy Claude (Opus 5). Me recuerdas lo que tu algoritmo **es**: no busca *una* solución, construye paso a paso **el conjunto de todos los certificados**, representado en un grafo cuyos nodos llevan tablas `owners` que les dicen con qué nodos son compatibles en cada paso; y los nodos son asignaciones de literales o valores concretos de las cláusulas. Y me pides que analice cómo demostrar que decide bien 3SAT, para una clase o en general, contando con que quizá haya que corregir o mejorar las reglas de filtrado — como ya pasó en v69.

Este informe no trae teoremas nuevos. Trae el mapa, con los precios puestos.

---

## 1. Tu diseño, dicho en dos inclusiones

Si Φ es el conjunto que construyes, tu afirmación de diseño es que Φ **es** el conjunto de soluciones. Eso son dos inclusiones, y el desarrollo entero es infraestructura para una u otra:

| | qué dice | estado |
|---|---|---|
| **⊇** | no pierdes ningún certificado | **demostrado de punta a punta** (v50–v53) |
| **⊆** | no guardas nada que no sea certificado | **abierto** — es «sin zombis», `ClauseStepExact` |

La de arriba es la ley de conservación: `chainSound_along` (para toda asignación que satisface φ, la selección que nombra es cadena sonora en todo estado de su rama) y `pureRun_full_state` (la última línea tiene entrada en el nodo que **cada** asignación nombra). El cuantificador es el que tú decías: no una solución, todas.

La de abajo es todo lo que queda. Y conviene tenerlo presente: **`decides_of_ClauseStepExact` ya está demostrado**, así que en cuanto ⊆ caiga, «tu máquina decide 3SAT» es un corolario, no otro proyecto.

## 2. Qué son `owners`, dicho en el vocabulario clásico

Esto no es traer una teoría de fuera: es tu diseño traducido.

- **Variables** del CSP = los pasos del mapa.
- **Dominio** del paso k = los nodos de ese paso: en el bloque de literales, los valores de una variable; en el bloque de cláusulas, las **filas** (las siete que satisfacen la cláusula). Exactamente lo que dices tú.
- **`owners(n)`** = los nodos compatibles con `n`, por paso. Eso **no es un dominio**: es una tabla de soportes por pares, es decir una estructura de **2-consistencia**. `ZeroOneAll.lean` ya lo dejó dicho en v20: «`owners` no es un dominio: es una tabla por nodo y por paso, exactamente una estructura de 2-consistencia».
- **`review`** = el algoritmo que lleva esa estructura a su punto fijo. `ArcConsistency.review_arcConsistent` lo demuestra sin hipótesis.
- **La pasada del triángulo** (v69) = subir un nivel esa consistencia.

Dicho de una vez: **tu algoritmo es un algoritmo de consistencia local de nivel fijo sobre ese CSP**, con la ventaja —que no es pequeña— de que mantiene la tabla por pares, que es más de lo que mantiene la consistencia de arcos ordinaria. La banda de v75 lo midió: en 5.203 pasos de cláusula tu filtro poda siempre **al menos** tanto como la consistencia de arcos, y no guarda ni una fila espuria.

## 3. El teorema que gobierna todo esto, y las tres consecuencias

El resultado clásico es de Freuder: **consistencia fuerte de nivel k, más anchura inducida < k, da solución sin retroceso**. De ahí salen tres cosas, y las tres responden a tu pregunta:

**(a) Para toda fórmula, ningún nivel fijo basta.** Por eso ⊆ en general **equivale a P = NP** — no es una sospecha mía, está en el registro desde v14 y reafirmado en v67: tu máquina es polinómica, así que «sin zombis para toda φ» pondría 3SAT en P.

**(b) Para una clase de anchura acotada, sí basta.** Ahí hay un teorema de verdad, demostrable, y es el objetivo realista.

**(c) Y esto responde a tu pregunta sobre correcciones y mejoras del filtrado:** subir el nivel del filtro —como hizo el triángulo— **no cierra el caso general; ensancha la clase**. Es trabajo valioso y no es un parche: mueve la frontera. Pero no la borra, y cualquier informe que sugiera lo contrario estaría mintiendo. Cada nivel cuesta un exponente más de tiempo polinómico.

## 4. Dónde está el hueco hoy, medido

Lo que sabemos de la exactitud de las tablas, por niveles:

| nivel | medición | resultado |
|---|---|---|
| pares | v69, tras el triángulo | **0 huecos** en 5,58 M de entradas |
| tríos | v70 | **38** de 905.506 muestreados, **7 genuinos** |
| nodos zombie | v66, v70, v75 | **0** en todo lo medido |
| veredictos | v70, v75 | **0** equivocados |

La lectura honesta: **el nivel actual no hace cierta la exactitud a nivel de tabla — ya falla en tríos** —, pero ningún hueco de tabla se ha convertido nunca en un nodo zombie ni en un veredicto malo, porque la propagación por las filas de cláusula cierra la contradicción unos pasos más allá. Esa distancia entre «la tabla falla» y «la máquina falla» es real y es tu margen, pero no es un teorema: es una medición.

Si quisieras exactitud de tabla como invariante limpio, el paso siguiente sería una pasada de nivel 4 sobre cuádruplas, igual que el triángulo fue la de nivel 3. Sabemos ya que existirán huecos de nivel 5, y así sucesivamente: es la escalera, no un fallo de diseño.

## 5. Las tres rutas, con su precio

**R1 — la clase, sobre tus estructuras.** El objetivo concreto sería:

```lean
theorem decides_on_class (φ : Cnf) (h : AnchuraAcotada φ) :
    Satisfiable φ ↔ ∃ kv ∈ pureRun φ, isValid kv.2 = true
```

y con `decides_of_ClauseStepExact` en la mano, basta demostrar `ClauseStepExact φ` bajo esa hipótesis. **Esta es la ruta que hay que hacer**, y lo que falta para arrancarla es el puente (A) de v75, enunciado sobre `owners` y no sobre mi reductor.

**R2 — subir el nivel del filtro.** Añadir la pasada de cuádruplas, medir que cierra los 7 huecos genuinos de v70, y demostrar la exactitud de tabla a ese nivel. Ensancha la clase de R1. Es el trabajo que tú intuías, y es legítimo; solo hay que contarlo como lo que es.

**R3 — el caso general.** Equivale a P = NP. Aplazado, no descartado, como acordamos. Y la forma no ingenua de acercarse es empírica y está a nuestro alcance: **medir cuánto se puede ensanchar la clase de R1 antes de que la exactitud se rompa**, usando los 2.166 casos donde mi reductor sí guarda filas espurias y tu máquina no, que son justamente el material donde tu algoritmo hace algo más que la consistencia de arcos.

## 6. El primer teorema concreto que propongo

Enunciar (A) **sobre tus estructuras**, no sobre un modelo paralelo:

> Si ninguna solución de lo visto hasta ahora combina la fila `r` de la cláusula `j` con alguna fila superviviente de otra cláusula, entonces `filterAll` + `review` matan `r`.

Medido: **0 excepciones en 5.203 pasos de cláusula** (v75). Y la vía de demostración se ve: dos filas de cláusula solo pueden chocar por las variables que comparten, es decir por los **pasos de literal**; y ahí tienes `L1`/`ReqFiltered` pinzando los owners en el paso requerido, más las dos pasadas de coherencia de padres e hijos. Eso es estrictamente más que un semi-join, que es justo lo que la banda midió.

Con (A) demostrado, más la exactitud del reductor en la clase (lo que v73 dejó abierto), saldría: **dentro de la clase, las filas que tu máquina mantiene vivas son exactamente las que usa alguna solución de lo visto**.

Y digo el alcance exacto, porque de eso iba v74: eso sería exactitud **a nivel de clave**, del sabor de `OwnersExactAt`. Para llegar a `ClauseStepExact` hace falta además subir de clave a **nodo** — que todo nodo del estado, no solo la clave, esté en una cadena sonora. Es un escalón más, y está identificado desde v67.

---

**En una frase:** la mitad de tu afirmación de diseño está demostrada entera; la otra mitad es, por un teorema de 1982 y por tu propia complejidad polinómica, exactamente tan difícil como P vs NP en el caso general y perfectamente demostrable en una clase de anchura acotada — y el trabajo inmediato, concreto y sobre tus propias estructuras, es el puente (A).

Build: `lake build AbsSat` verde, 99 módulos, 0 `sorry`, 0 axiomas de proyecto. Este informe no añade código.
