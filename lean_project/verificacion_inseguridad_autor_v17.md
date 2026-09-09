# Verificación para el Autor v17: Ruta E cerrada — el mapa no es acíclico, y no podía serlo

Ricardo, soy Claude (Opus 5). Me pediste atacar **E**: usar el teorema de Beeri–Fagin–Maier–Yannakakis en lugar de CCJ. Está atacada, es medible, y la respuesta es **no**. Te cuento qué he construido, qué dice, y por qué el "no" era el único resultado que podía llegar.

---

## 1. Por qué E merecía intentarse

v13 cerró negativamente la ruta CCJ: las restricciones 0/1/all son cerradas por mayoría y dan **anchura estricta 2**, que exige **consistencia de caminos**, y tu máquina mantiene algo más débil (consistencia de arcos por los enlaces padre/hijo, más los owners globales).

E preguntaba si aplica otro teorema clásico que **no pide consistencia de caminos en absoluto**:

> **Beeri–Fagin–Maier–Yannakakis (1983).** Si el hipergrafo de restricciones es **α-acíclico**, la consistencia por pares implica consistencia global.

Si el hipergrafo de tu mapa fuera α-acíclico, la consistencia de arcos decidiría, "sin zombis" saldría gratis, y toda la maquinaria de anchura sobraría. Merecía medirse en vez de discutirse.

---

## 2. El techo que E traía de fábrica

Esto hay que decirlo antes de los números, porque cambia cómo se leen:

> Los CSP α-acíclicos se resuelven en **tiempo polinómico**. Un mapa cuyo hipergrafo fuese α-acíclico pondría 3SAT en P **por un teorema de 1983**.

O sea: E no era un paso hacia tu afirmación, **era tu afirmación entera**. Un "sí" habría sido motivo de sospechar de mi construcción del hipergrafo antes que de celebrar nada.

Y al revés: un "no" **no refuta nada de tu algoritmo**. Solo cierra esta ruta de demostración, y dice de dónde no puede venir la prueba.

---

## 3. Lo que he construido

`AbsSat/GraphMap/Hypergraph.lean` + `lake exe hyper`.

**El CSP, explícito.** Las variables son los **pasos** `0 … step-1`; el dominio del paso `k` son los nodos del mapa en `k`; los `requires` de un nodo son las restricciones. Es exactamente la forma de `IsChain`: una selección de un nodo por paso.

**Dos hipergrafos, y solo uno es el honesto:**

- `scopesByStep` — una arista por paso: `{k} ∪ {pasos que nombran los requisitos de algún nodo de k}`. **Este es el hipergrafo del que habla BFMY**: una restricción es *una* relación, y su ámbito es todo lo que restringe.
- `scopesByNode` — una arista por nodo. Más fina, aristas más pequeñas, más fácil de reducir. **No es una descomposición válida** de las restricciones (el conjunto de requisitos de un nodo es un disyunto de la relación del paso, no una restricción propia), así que solo la calculo como cota optimista: si hasta esta es cíclica, la honesta lo es con seguridad.

**α-aciclicidad decidida por reducción GYO:** quitar repetidamente (1) un vértice que aparece en una sola arista, y (2) una arista contenida en otra. Acíclico ⟺ se reduce a nada. Lo que queda cuando se atasca es el **núcleo cíclico**.

Sin `native_decide` — los tres casos de prueba (camino, triángulo, y el clásico `{a,b,c},{b,c,d}` que es α-acíclico sin que su grafo primal lo sea) están verificados por el kernel con `decide`.

---

## 4. Lo que dice

### Mapas concretos

| instancia | pasos | aristas (por paso) | núcleo cíclico | α-acíclico |
|---|---|---|---|---|
| `sample.cnf` | 10 | 5 | 5 aristas sobre 6 pasos | **no** |
| literal repetido | 14 | 8 | 8 sobre 8 | **no** |
| UNSAT forzado (8 cláusulas / 3 vars) | 16 | 11 | 11 sobre 6 | **no** |
| transición de fase | 40 | 32 | 32 sobre 12 | **no** |
| **cadena implicativa larga** | 27 | 17 | **0** | **sí** |

**La última fila es la que me dice que el probe mide lo correcto.** La cadena implicativa `x₁ → x₂ → … → x₈` tiene un grafo de restricciones que es un **camino**, y un camino es acíclico. El probe dice "sí" exactamente en la instancia cuya estructura es un árbol, y "no" en cuanto hay variables compartidas entre cláusulas. No es un detector roto que siempre diga que no.

### Campañas aleatorias

| rango | α-acíclicos | núcleo mayor | núcleo medio |
|---|---|---|---|
| 3–10 vars, 200 mapas | 16/200 | 66 aristas | 22 |
| 3–4 vars, 100 mapas | 5/100 | 22 aristas | 10 |
| 8–12 vars, 100 mapas | 7/100 | 81 aristas | 37 |

Dos cosas que leo ahí:

1. **No es "casi acíclico".** En la mayoría de los mapas cíclicos el núcleo es **el hipergrafo entero** — GYO no elimina ni una arista. No hay un residuo pequeño y manejable que se pudiera tratar aparte.
2. **El núcleo crece con la instancia** (media 10 → 22 → 37). Los pocos acíclicos son los degenerados, con muy pocas cláusulas.

### Dónde está exactamente el ciclo

Vale la pena verlo, porque es preciso. Dos cláusulas que comparten dos variables **sí** reducen: `{c₁,x₁,x₂,x₃}` y `{c₂,x₁,x₂,x₄}` → se quitan `c₁` y `x₃` (aparecen en una sola arista), queda `{x₁,x₂}` contenido en la otra, fuera. Acíclico.

Con **tres** cláusulas encadenadas sobre variables compartidas queda `{x₁,x₂}, {x₂,x₃}, {x₃,x₁}` — un triángulo, y ahí GYO se para.

Es decir: **el ciclo es la estructura de variables compartidas entre cláusulas.** Justo lo que hace difícil a 3SAT. No es un accidente de tu construcción; ninguna codificación de 3SAT puede evitarlo sin resolver 3SAT.

---

## 5. La conclusión, y por qué es útil

**Ruta E cerrada.** BFMY no aplica. Cualquier demostración de "sin zombis" tiene que venir de **la dinámica de tu máquina** — de cómo poda — y no de la estructura estática del mapa.

Y eso encaja con algo que ya sabíamos y que no habíamos sabido interpretar. `lake exe l6search` construye estados con requisitos **arbitrarios, sin ninguna estructura 3SAT**, y no encontró un solo contraejemplo a "sin zombis" en 1.680 estados. El documento del puente predecía lo contrario: que la prueba tendría que venir de la estructura 3SAT.

Puestas juntas, las dos observaciones apuntan al mismo sitio:

> Si la propiedad se cumple, **no se cumple por cómo está hecho el mapa. Se cumple por cómo la máquina poda.**

Eso descarta E y F (que buscan la respuesta en la estructura) y señala **A** (extensibilidad / *backtrack-free*), que es una propiedad de las pasadas de filtrado. Y A es justamente lo que tu corrección sobre el Reader dejó en evidencia: como el lector no retrocede, lo que necesita es que toda selección parcial consistente se extienda — que es `Extendable`, no `Supported`.

---

## 6. Lo que haría ahora

1. **Ruta G** — el falsador dirigido por SAT: codificar "grafo válido con un zombi" como instancia SAT y dársela a un solver externo. Barato, exhaustivo hasta tamaños decentes, y responde la pregunta que ahora manda: ¿la poda de la máquina fuerza la propiedad por sí sola?
2. Si G sale UNSAT, **ruta A**: `Extendable` como invariante de `upFiltering` y `review`, con la inducción sobre `k` en vez de sobre `Reachable`. Es la única de las siete que apunta a la dinámica.
3. Y `ReadStable` (v16 §2) como el enunciado puente: la corrección del lector y el hueco de L6 son la misma obligación.

---

*Claude (Opus 5), 2026-09-09. Ruta E de las siete alternativas. `lake build AbsSat` verde, 57 módulos, 0 `sorry`, sin `native_decide`.*
