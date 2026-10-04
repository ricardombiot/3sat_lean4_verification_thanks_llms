# Verificación para el Autor v142: toda respuesta es correcta, y el lector nunca se atasca

Ricardo, soy Claude (Opus 5). Este informe recoge lo hecho tras v141 a partir de tu propuesta: que la
máquina, para responder SAT, **entregue siempre un certificado**. Con eso cambia la forma del resultado, y
a mejor: **ninguna respuesta de la máquina puede ser incorrecta, sin hipótesis**. Lo único que queda
condicionado es que la máquina **siempre responda**, y eso también está formalizado ahora, por inducción
sobre el lector.

Rama `spaik`, build de `AbsSat` (203 jobs), sin `sorry`, `[propext, Quot.sound]`. Commits `c0ed423`,
`67e8c91`, más la sonda `e325ab5`.

---

## 1. Toda respuesta es correcta (demostrado sin hipótesis)

`Answer.lean` define la respuesta de la máquina como una función **computable**:

* **UNSAT** — si ningún estado de lector de la última línea es válido;
* **SAT a** — si tu lector (variable a variable: fija `v = 0`, revisa, y si el grafo queda inválido fija
  `v = 1`) extrae una asignación `a` **y `a` satisface φ al comprobarla**;
* **no sé** — en cualquier otro caso.

| teorema | enunciado | hipótesis |
|---|---|---|
| `answer_unsat_sound` | si responde UNSAT, φ no tiene modelo | **ninguna** |
| `answer_sat_sound` | si responde SAT a, a es modelo de φ | **ninguna** |
| `answer_ne_unsat_of_sat` | a una fórmula satisfacible nunca responde UNSAT | **ninguna** |
| `answer_unsat_of_unsat` | a una fórmula insatisfacible responde UNSAT | `GhostsLine` (v141) |

La hipótesis cambia de papel: ya no protege la **corrección** de las respuestas —eso está demostrado sin
nada—, solo la **completitud**: que la máquina no se quede en "no sé".

La función se ejecuta (modo `helly answer`). Sobre fórmulas del repositorio:

| fórmula | respuesta |
|---|---|
| Tseitin K4 (par) | SAT, certificado comprobado |
| paridad k3 | SAT, certificado comprobado |
| Tseitin prisma (par) | SAT, certificado comprobado |
| Tseitin Petersen | UNSAT |
| Tseitin Möbius, 10 vértices | UNSAT |
| Tseitin sobre grafo 3-regular aleatorio, 8 vértices | SAT, certificado comprobado |

Ninguna vez "no sé".

## 2. El lector nunca se atasca (demostrado bajo dos hipótesis de la misma clase)

`ReaderComplete.lean`, por inducción sobre las variables que fija el lector, con el invariante **el estado
actual del lector es válido y exacto** (sus tablas son rebanadas):

1. **Un estado válido y exacto contiene un camino completo** (`exact_chain`): tiene un owner global, que se
   posee a sí mismo, y su rebanada contiene un camino.
2. **El paso**: ese camino tiene en la variable `v` el valor 0 o el 1 (los nodos de mapa de un paso de
   variable son solo esos dos, `var_node`). Si fijar 0 deja el estado inválido, el camino tenía 1, y fijar 1
   lo conserva (`ChainSound_filterAllAgg`). **El lector nunca se atasca.**
3. **El final**: el camino que queda pasa por todos los valores leídos (en un paso fijado, todo owner
   global lleva el valor fijado, `pin_id`), así que la asignación leída es su decodificación en las
   variables de φ, que es un modelo (`sat_decode`, `sat_congr`). **El certificado pasa la comprobación.**

> **`answer_ne_unknown`** — bajo `GhostsLine` y `ReaderPinExact`, la máquina **nunca** responde "no sé".

La hipótesis nueva, **`ReaderPinExact`**, dice: *fijar un nodo de mapa sobre un estado de lector válido y
exacto, y revisar, lo deja exacto*. Es de la misma naturaleza que `GhostsLine` (fijar y revisar conserva
la exactitud), una para las fijaciones de la ejecución y otra para las del lector, y es exactamente lo que
midió la sonda `pinexact` en v139: **21.709 fijaciones arbitrarias, todas exactas**.

## 3. Cómo queda todo

| afirmación | hipótesis |
|---|---|
| toda respuesta UNSAT es correcta | **ninguna** |
| toda respuesta SAT lleva un modelo comprobado | **ninguna** |
| a una fórmula satisfacible nunca le responde UNSAT | **ninguna** |
| la máquina es la unión de los caminos del oráculo, en la dirección que protege UNSAT | **ninguna** |
| semilla, UP y unión conservan las rebanadas | **ninguna** |
| a una fórmula insatisfacible le responde UNSAT | `GhostsLine` |
| la máquina siempre responde (nunca "no sé") | `GhostsLine` + `ReaderPinExact` |

Y las dos hipótesis dicen lo mismo en dos sitios: **fijar y revisar conserva la exactitud de las tablas**.
Medido sin excepción: 3,02 M entradas fantasma eliminadas (v140), 21.709 fijaciones exactas (v139), y cada
estado de la máquina igual a la unión de los caminos del oráculo en todas las familias (v139).

## 4. La búsqueda adversarial sobre el modelo aislado (detenida)

v140 §5 propuso aislar el filtro en un lema sin máquina: sistemas de requisitos "si en el paso t está y,
en el paso i está r", todas sus soluciones como un estado de tablas exactas, cada fijación posible, y
buscar fantasmas que el review base deje no detectables. Monté una búsqueda por escalada con reinicios
(modo `helly adversarial`) que muta los requisitos para maximizar las fantasmas tras el review base.

Lo que dio antes de detenerla:

* **anchura 2** (dos nodos por paso): el review base es exacto por sí solo, **ninguna** fantasma. Coherente
  con la teoría: en dominios booleanos "y ⇒ r" es 2-SAT, donde la consistencia por pares basta.
* **anchura 3** (8 pasos): aparecen fantasmas tras el review base (hasta 104 en una configuración), todas
  detectables; **ningún contraejemplo**.

Las cuatro búsquedas largas (8×3, 7×4, 9×3, 6×5) se detuvieron a petición tuya antes de terminar, y como
escribían con búfer no dejaron resultados. No hay que sacar conclusiones de ellas.

**Tu objeción, y es correcta**: el modelo aislado simplifica tu algoritmo —deja fuera los requisitos
débiles, la estructura del mapa, los estados por clave, las uniones y la fijación en el momento de crear
cada nodo—. La lógica es asimétrica: si el modelo aislado no da contraejemplos, apoya una **vía de
prueba**; si los da, **no refuta tu máquina**, solo esa vía. Sirve para elegir la prueba, no para juzgar
el diseño.

## 5. Siguiente paso propuesto: búsqueda adversarial sobre fórmulas reales, para buscar ideas

La búsqueda que sí respeta toda la complejidad de tu algoritmo es la misma, pero **sobre fórmulas CNF
reales, ejecutando la máquina completa**: mutar cláusulas de fórmulas pequeñas (añadir, quitar o cambiar
literales) y maximizar las fantasmas que sobreviven a la primera pasada del review base (sondas `ghosts` y
`pinexact`).

Tiene dos usos, y el segundo es el que interesa para la prueba:

1. **Falsación.** Si existe una fórmula en la que tu máquina deja, tras la pasada base, una compatibilidad
   falsa simétrica y con owner común en todos los pasos, la búsqueda tiende a encontrarla. Si no la
   encuentra, la confianza sube, pero una búsqueda **nunca** es una demostración.
2. **Pistas para demostrar `GhostsLine`.** Las fórmulas que la búsqueda empuja hacia el fallo sin llegar a
   él son los **casos extremos** de tu review. Estudiarlos puede revelar la regularidad que hace
   detectables a las fantasmas, por ejemplo:
   * si son asimétricas siempre por el mismo motivo —que el ID con el mapa del padre corte en un sentido y
     no en el otro—;
   * si intervienen los requisitos débiles;
   * si aparecen solo con ciertos patrones de cláusulas que comparten variables.

   Una regularidad así es exactamente la idea que falta. La búsqueda no la da, pero **produce los ejemplos
   que hay que mirar**, en vez de los millones de casos fáciles de las familias al azar.

## 6. Artefactos

* Lean: `Answer.lean` (respuesta computable, corrección sin hipótesis), `ReaderComplete.lean` (el lector
  nunca se atasca), sobre `DeclaredVerdict.lean`, `RoundInvariant.lean`, `SliceInvariant.lean`.
* Sondas (`Probes/Helly.lean`): `answer` (ejecuta la máquina sobre ficheros CNF), `adversarial` (búsqueda
  sobre el modelo aislado).
