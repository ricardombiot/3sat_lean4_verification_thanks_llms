# Verificación para el Autor v60: tu frase, medida — y por qué la inducción nunca podía funcionar

Ricardo, soy Claude (Opus 5). Tu frase es exactamente la conjetura, así que la he medido **directamente**, sin pasar por el grafo: enumerando todas las asignaciones y preguntando cuáles siguen dentro del estado. El resultado dice más de lo que pedías — y, de paso, explica un fracaso que lleva repitiéndose desde v12.

---

## 1. La medición, sin maquinaria

`lake exe cnfmap --exact`. Para cada estado del recorrido:

- enumero las **2ⁿ** asignaciones y me quedo con las que satisfacen φ;
- digo que una solución está **dentro** del estado si, en cada paso, el nodo de mapa que esa asignación nombra sigue estando entre los owners globales;
- y cuento dos cosas: estados válidos **sin ninguna solución dentro** (zombis de verdad), y nodos de mapa supervivientes que **ninguna solución superviviente usa** (owners espurios).

Ni cadenas, ni `Closed`, ni `PairwiseOwned`. Solo semántica.

## 2. En el estado final, tu frase es cierta — y algo más fuerte

| campaña | estados finales válidos | **sin solución dentro** | nodos de mapa supervivientes | **espurios** |
|---|---|---|---|---|
| 20 casos, 2026, 3..5 vars | 16 | **0** | 688 | **0** |
| 60 casos, 31337, 3..5 vars | 53 | **0** | 2.376 | **0** |
| 50 casos, 4242, 4..6 vars | 46 | **0** | 2.617 | **0** |
| **total** | **115** | **0** | **5.681** | **0** |

La primera columna es tu frase: **ningún estado final válido está vacío de soluciones.**

La segunda es más fuerte y no la habías pedido: **cero espurios**. Los nodos de mapa que sobreviven al final son **exactamente** los que usan las soluciones supervivientes. Es decir, en el estado final

> **Φ no contiene «al menos una» solución: contiene exactamente el conjunto de soluciones**, nodo a nodo, a nivel de mapa.

Eso es lo que llevas diciendo desde el principio, y ahora está medido sin intermediarios.

## 3. Y ahora la parte que importa para la demostración

Repetí la cuenta en los estados **intermedios**, y ahí la exactitud **se cae**:

| | estados | nodos supervivientes | espurios |
|---|---|---|---|
| todos los estados válidos (2026) | 1.352 | 21.593 | 12.266 |
| **solo los que aún contienen solución** (2026) | 688 | 10.239 | **912** (8,9 %) |
| **solo los que aún contienen solución** (31337) | 1.087 | 17.932 | **1.852** (10,3 %) |

Fíjate en la tercera fila: **incluso restringiéndose a estados que todavía contienen una solución, hay owners espurios.** Así que la exactitud **no es un invariante que se pueda arrastrar**: es falsa durante todo el recorrido y solo se vuelve cierta **al completarlo**.

Y eso explica algo que llevaba repitiéndose sin que supiéramos por qué:

> **La propiedad que uno querría inducir sobre la construcción es falsa hasta el último paso.**

Por eso fracasó la ruta de v12, y `Inhabited_of_descent`, y la ruta A, y toda la línea de v54–v57 sobre posesión dos a dos. No eran malas ideas mal ejecutadas: **estaban buscando un invariante que no existe a mitad de camino**. La demostración no puede ser una inducción sobre cómo se construyó el estado; tiene que ser un argumento de **punto fijo** sobre el estado ya terminado.

Eso es una corrección de rumbo, y es la primera vez que el desarrollo tiene una razón *medida* para ella en lugar de una sospecha.

## 4. Qué queda, dicho con esta luz

El objetivo pasa a ser:

> **Exactitud del estado final** — todo owner global superviviente es usado por alguna solución superviviente.

De ahí la conjetura sale sola: si el estado es válido, hay un owner en el paso 0; por exactitud, alguna solución lo usa; esa solución **es** el camino que el lector puede leer.

Y las dos mitades están repartidas así:

- **⊇** (toda solución sobrevive) es la **ley de conservación** — demostrada, v50–v52;
- **⊆** (ningún owner sobra) es el muro, ahora con nombre semántico en lugar de estructural.

Con lo demostrado en v58 y v59, todo lo que hay entre ese enunciado y el veredicto ya está cerrado: el pinchazo sobre una cadena mantiene la validez (pasadas de coherencia incluidas), el bucle del lector termina, el final denota una solución, y `PickSome` ⟺ `Inhabited`.

## 5. Lo que esto **no** es

- **No es una demostración de tu frase.** Son 115 estados finales sin un solo contraejemplo, medidos semánticamente. Fuerte, pero medición.
- La medición es **a nivel de nodo de mapa**, no de `PathNodeId`: dice que el id de mapa sobrevive, no que sobreviva la decoración concreta del camino.
- Solo llega a **3–6 variables**: enumera 2ⁿ asignaciones, así que no escala.
- La mitad UNSAT no aparece aquí porque una instancia insatisfacible da línea final vacía — que es justo lo correcto, y eso sí está demostrado (`pureRun_ne_nil`).

## 6. Estado

| | |
|---|---|
| Mitad de completitud (conservación + driver) | cerrada |
| Bucle del lector, pasadas de coherencia, `PickSome` ⟺ `Inhabited` | demostrados (v58, v59) |
| **Estado final sin solución dentro** | **0 de 115** |
| **Owners espurios en el estado final** | **0 de 5.681** |
| Owners espurios en estados intermedios vivos | **8,9 % – 10,3 %** — la exactitud no es inductiva |
| Exactitud del estado final | abierto — el muro, con nombre semántico |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, 87 módulos, 0 `sorry`, 0 axiomas de proyecto.

---

*Claude (Opus 5), 2026-09-11.*
