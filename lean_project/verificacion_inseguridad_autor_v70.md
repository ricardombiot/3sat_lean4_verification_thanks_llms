# Verificación para el Autor v70: el caso general — lo que se ha podido y lo que no

Ricardo, soy Claude (Opus 5). Te preocupaba mi frase «el triángulo arregla los huecos entre pares, pero puede haberlos entre tríos», y me pediste intentar el caso general. Lo he intentado en serio, por las dos vías: el argumento y la búsqueda del hueco. Primero el resultado, sin rodeos:

- **La preocupación era real a nivel de tablas:** con el triángulo sigue habiendo tríos de nodos compatibles dos a dos que no comparten ninguna solución.
- **Pero no se ha convertido nunca en un error de la máquina:** apuntando cláusulas directamente a esos huecos, **0 nodos zombie y 0 veredictos equivocados**. He encontrado por qué.
- **El caso general no lo he demostrado**, y te explico con precisión qué es lo que habría que demostrar.
- De paso, **demostrada la última pieza de prefijo que faltaba**: la dirección contraria.

---

## 1. El argumento: dónde está exactamente el caso general

Con el triángulo, cada nodo superviviente es compatible **dos a dos** con los tres literales que fija una cláusula, y los pares tienen un owner común en cada paso. El paso de cláusula necesita más: que el nodo y los tres literales estén en **una misma** solución, es decir, compatibilidad **de cuatro a la vez**.

La construcción que muestra que eso no es gratis es la **paridad**. Con `x_a ⊕ x_b ⊕ x_c ⊕ x_p = 0`, cualesquiera **tres** de las cuatro variables pueden tomar las 8 combinaciones, pero fijar tres determina la cuarta. Ninguna comprobación de pares, y ni siquiera de tríos, ve esa restricción.

## 2. La búsqueda: los huecos entre tríos existen

Modo nuevo, `lake exe cnfmap --triples`. En los estados de la máquina con triángulo muestreo tríos de nodos que se poseen mutuamente dos a dos y pregunto si alguna solución de lo visto pasa por los tres.

| tres semillas, 5–6 variables | |
|---|---|
| tríos co-poseídos probados | 905.506 |
| con algún par sin solución común | **0** (el triángulo cierra los pares) |
| **pares bien, pero ninguna solución común** | **38** |
| de ellos, hueco también entre **valores del mapa** | **7** |

31 de los 38 son huecos solo entre **nodos del camino**: cada nodo lleva también el valor de su padre, y otra copia del mismo valor con otro padre sí tiene la solución. Los 7 restantes son huecos genuinos: por ejemplo, x0=0, x2=0, x4=1, compatibles dos a dos y sin ninguna solución de lo visto que los tenga a la vez, en ningún estado.

## 3. El ataque: apuntar cláusulas a esos huecos

Si una cláusula posterior fija dos de los tres valores, el razonamiento de pares dice que el tercer nodo sobrevive: tiene owner compatible con cada uno y pasa el triángulo. Sería un nodo zombie, un contraejemplo. Así que inserté, justo después de cada estado con un hueco genuino, cada cláusula posible (cada terna de variables y cada patrón de signos):

| estado con hueco genuino (semilla, caso, paso) | fórmulas | **nodos zombie** | veredictos equivocados |
|---|---|---|---|
| 2026, caso 10, paso 20 | 160 | **0** | 0 |
| 31337, caso 4, paso 18 | 160 | **0** | 0 |
| 777, caso 10, paso 19 | 160 | **0** | 0 |
| 777, caso 11, paso 16 | 160 | **0** | 0 |
| 777, caso 11, paso 19 | 160 | **0** | 0 |
| **total** | **800** | **0** | **0** |

Y antes, sobre el hueco de tríos en un estado **final** (777, caso 3), 240 inserciones más en cada máquina: 0.

**Ni uno.** La razón no es la que yo esperaba. Primero comprobé si el hueco era de una sola clave y la unión de estados lo rescataba: no, las siete combinaciones **faltan en todas partes**. La razón es que al fijar dos valores la máquina **no se limita a los pares**. Los nodos de cláusula codifican sus tres literales a la vez, así que fijar x0 y x2 elimina las filas de todas las cláusulas incompatibles con ellos, y eso **se propaga de cláusula en cláusula** hasta llegar a x4. En estas fórmulas la contradicción siempre queda a pocos pasos de esa propagación.

Es decir: **los huecos de tríos existen en las tablas, pero el filtro de cláusula los cierra con su propia propagación.** Es lo mismo que vimos en v66, dicho un escalón más arriba: el invariante de **nodo** aguanta donde el de **tabla** falla.

## 4. Lo demostrado en esta sesión: la dirección contraria por prefijo

Faltaba una pieza para enunciar el núcleo sin grafo:

```lean
theorem satUpTo_of_chain (hwf : WF φ) (g) (hmr : MapReachable φ g) (sel)
    (hchain : IsChain g sel) (howned : PairwiseOwned g sel) :
    SatUpTo φ (decode sel) (g.current_step - 1)          -- [propext, Quot.sound]
```

**Toda cadena co-poseída de un estado intermedio se descodifica en una asignación que satisface todas las cláusulas vistas.** Con la conservación por prefijo de v69, en mitad de una ejecución las cadenas de un estado y las soluciones de lo visto son lo mismo, leído de dos formas. La demostración es la de longitud completa, notando que esa hipótesis solo se usaba para saber que los pasos de literal y el de la cláusula quedan por debajo del paso actual.

## 5. Por qué el caso general no es cuestión de más tiempo

Lo que la máquina hace al fijar valores es propagación local a través de las filas de las cláusulas, sea con pares o con el triángulo. Esa propagación tiene un **alcance**: resuelve las contradicciones que se alcanzan en pocos pasos de razonamiento local. Hay familias de fórmulas conocidas (paridad sobre grafos expansores, las fórmulas de Tseitin grandes) en las que la contradicción no se alcanza con **ningún** alcance acotado. Y como la máquina es polinómica, demostrar que su propagación basta **para toda fórmula** es demostrar P = NP.

Te lo digo porque delimita el trabajo, no para quitarle valor. El caso general **no se ha roto** en ninguna prueba: ni pares, ni tríos apuntados, ni Tseitin pequeño. Pero la forma honesta de cerrarlo es una de estas dos:
1. **Una demostración para una clase de fórmulas**, las de alcance acotado en el sentido de arriba. Esto sí es demostrable, y es un teorema de verdad.
2. **Buscar el contraejemplo donde tiene que estar**: paridad sobre expansores de 20 a 40 variables. Hace falta una implementación más rápida de la máquina: la actual, en listas, no terminó Petersen (15 variables) en 8 minutos.

## 6. Lo que queda en firme y lo que no

**Demostrado:** `litVal_of_reqSat_prefix`, `satClause_of_reqSat_prefix`, `satUpTo_of_chain`.

**Medido:**
- con el triángulo, 0 huecos de pares y 38 de tríos (7 genuinos) en 905.506 tríos;
- inserciones apuntadas a los 7 genuinos: 800 fórmulas, 0 zombies y 0 veredictos equivocados.

**No demostrado:** el caso general (`FlipCore`). Queda como teorema para una clase o como búsqueda a mayor escala.

Build: `lake build AbsSat` verde, 96 módulos, 0 `sorry`, 0 axiomas de proyecto.
