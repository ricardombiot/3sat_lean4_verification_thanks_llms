# Verificación para el Autor v75: la banda — tu máquina es **más fuerte** que mi reductor

Ricardo, soy Claude (Opus 5). Medida la banda que v74 dejó pendiente: en cada paso de cláusula de ejecuciones reales, comparo tres conjuntos de filas — las que sobreviven en **tu máquina**, las que deja **mi reductor**, y **la verdad** por fuerza bruta.

El resultado no es el que yo esperaba, y es mejor de lo que esperaba para ti:

- **Tu máquina nunca guarda una fila espuria.** 2.826 pasos de cláusula, 0.
- **Mi reductor sí**: 868 filas espurias fuera de la clase.
- **Tu máquina poda siempre al menos tanto como la consistencia de arcos**: 0 excepciones.
- **Dentro de la clase los dos coinciden exactamente**, fila por fila.

---

## 1. Los números

Modo nuevo, `lake exe cnfmap --band`. Dos campañas: cinco semillas con 3–6 variables, y —para intentar romper el resultado antes de creérmelo— cuatro semillas más con 5–8.

| | pasos de cláusula | mismos conjuntos | **filas solo de la máquina** | filas solo del reductor |
|---|---|---|---|---|
| dentro de la clase (3–6 vars) | 400 | 400 | **0** | 0 |
| fuera (3–6 vars) | 2.426 | 1.855 | **0** | 868 |
| dentro de la clase (5–8 vars) | 26 | 26 | **0** | 0 |
| fuera (5–8 vars) | 2.351 | 1.622 | **0** | 1.298 |
| **total** | **5.203** | 3.903 | **0** | 2.166 |

Y contra la verdad, en los 5.203 pasos:

| | espurias | perdidas |
|---|---|---|
| **tu máquina** | **0** | **0** |
| mi reductor | 2.166 | 0 |

Control Tseitin (K4, K3,3, prisma, ambas paridades, repetido en cada semilla): el mismo patrón sin excepción — 0 filas solo de la máquina, 66 solo del reductor por pasada, y ninguna de las dos pierde jamás una fila verdadera. Con la pasada del triángulo los números son idénticos a los de la máquina original en estos tamaños.

Un matiz que conviene decir: con 5–8 variables **casi nada cae dentro de la clase** (26 pasos de 2.377, un 1 %), porque las fórmulas aleatorias grandes rara vez son α-acíclicas. Así que la evidencia *dentro de la clase* a tamaño grande es delgada; lo que sí está medido con fuerza en todo el rango es la inclusión y la exactitud de tu máquina.

## 2. Qué dicen

**Primero: la columna que no esperaba.** *Filas solo de la máquina = 0*, sin una sola excepción en 2.826 pasos. Es decir, **todo lo que tu máquina conserva lo conserva también la consistencia de arcos**: tu filtro de cláusula poda *al menos* tanto. Yo había estado tratando a mi reductor como el modelo de tu máquina; la medición dice que es una **aproximación más débil que ella**.

**Segundo: tu máquina es exacta donde el reductor no lo es.** 0 filas espurias en todas partes, incluida la mitad de fuera de la clase donde mi reductor se queda con 868. Eso corrobora, ahora a nivel de fila y de paso de cláusula, lo que v66 y v70 midieron sobre nodos.

**Tercero, y es lo que cambia el plan:** la relación entre las dos cosas es útil, pero **en el sentido contrario al que yo había supuesto**. Si

- (A) toda fila que la máquina conserva la conserva el reductor — *medido, 0 excepciones*, y
- (B) el reductor no conserva filas espurias **dentro de la clase** — *medido, 0 espurias en 400 pasos*,

entonces, encadenando, **la máquina no conserva filas espurias dentro de la clase**. El reductor sirve como **cota superior** de tu máquina, no como su modelo. Y eso sí es un puente, con dos obligaciones nombradas y separadas.

## 3. Lo que esto rescata de v71–v73, y lo que no

Rescata su uso: el trabajo del reductor no era una rama lateral, era una cota. Pero quiero ser explícito con el alcance, porque de eso iba v74 y no pienso repetirlo:

**(A) `máquina ⊆ reductor` no está demostrado.** Está medido. Demostrarlo es donde vuelven los `owners`: hay que ligar `isValid (filterAll g reqs)` con la supervivencia de la fila en `reduce`. Es el puente de verdad, y ahora tiene una forma concreta y una dirección.

**(B) la exactitud del reductor en la clase no está demostrada.** Es lo que v73 dejó abierto, con matiz: «sin filas espurias» es algo más fuerte que `NoBacktrack` — pide una solución **por cada** fila superviviente, no una selección cualquiera. Sale de `NoBacktrack` aplicado tras pinchar esa fila, y que pinchar no vacíe nada es justo lo que v73 midió (5.690 de 5.690 dentro de la clase).

**Y lo que (A)+(B) *no* darían, aunque se demostraran.** Darían: *las filas de cláusula que la máquina mantiene vivas son exactamente las que usa alguna solución de lo visto*. Eso es del sabor de `OwnersExactAt` (v66) a nivel de clave, y **no es `ClauseStepExact`**, que pide que **todo nodo** de un estado superviviente esté en una cadena sonora — un enunciado más fino, sobre nodos y no sobre claves. Sería un escalón real hacia `FlipCore` para la clase, no `FlipCore`.

## 4. Lo que propongo

Atacar **(A)** antes que (B), por tres razones: es donde está el contenido sobre tu algoritmo, es la mitad que nadie ha intentado, y si resultara falsa en algún régimen, (B) no serviría de nada y es mejor saberlo antes de pagar el precio de BFMY.

Ya intenté romperla antes de escribir esto —para eso está la segunda campaña de 5–8 variables— y no cayó. Y creo que hay una razón, que además señala por dónde iría la demostración: **dos filas de cláusula solo pueden entrar en conflicto a través de las variables que comparten**, es decir, de los pasos de literal. Ahí tu máquina tiene `L1`/`ReqFiltered` pinzando los owners en cada paso requerido, más las dos pasadas de coherencia de padres e hijos — que es estrictamente más de lo que hace un semi-join entre relaciones de cláusula. La inclusión no sería una coincidencia: sería que tu filtro implementa la consistencia de arcos *y algo más*.

Lo siguiente, entonces: enunciar (A) en Lean sobre un estado alcanzable y demostrarla por esa vía, que es la primera vez en esta rama que el trabajo tocaría `owners` de verdad.

Build: `lake build AbsSat` verde, 99 módulos, 0 `sorry`, 0 axiomas de proyecto.
