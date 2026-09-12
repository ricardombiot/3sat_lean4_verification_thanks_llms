# Verificación para el Autor v68: el filtro de cláusula, en piezas pequeñas

Ricardo, soy Claude (Opus 5). Me pediste partir la demostración del filtro de cláusula en piezas pequeñas y demostrarlas en Lean. Lo he hecho. Todas las piezas que admiten demostración están demostradas. Queda una sola, que he aislado y medido, y te explico por qué no se deja partir más.

Sobre el vértigo, una sola frase: no es miedo. Con todo lo demás demostrado, la pieza que quede lleva dentro toda la dificultad, y lo honesto es decir cuál es y dejarla tan pequeña como sea posible.

---

## 1. La estructura

```
ClauseStepExact                                    (v67: la hipótesis única)
  ⇐ Parte 1: un requisito cada vez                  DEMOSTRADO
      OneReqStep
        ⇐ Parte 2: los casos de un paso
            (a) el nodo está en el paso del requisito    DEMOSTRADO
            (b) la cadena ya lo cumple                   DEMOSTRADO
            (c) el paso ya estaba fijado                 DEMOSTRADO
            (d) hay que cambiar el valor de un literal   ← FlipCore, el núcleo
```

Y todo encadenado, de punta a punta:

```lean
theorem decides_of_FlipCore (φ) (hwf : WF φ) (hzero : 0 < stepCount φ) (hcore : … FlipCore …) :
    Satisfiable φ ↔ ∃ kv ∈ pureRun φ, isValid kv.2 = true          -- [propext, Quot.sound]
```

## 2. Parte 1: un requisito cada vez (demostrada)

Una cláusula impone tres requisitos. Un nodo superviviente empieza con *alguna* cadena (el soporte que ya había antes del filtro). Se añaden los requisitos de uno en uno: de una cadena que pasa por el nodo y cumple algunos, se obtiene otra que cumple uno más. Tras el último, la cadena pasa el filtro (`ChainSound_filterAll`).

```lean
theorem SupportedS_filterAll_of_OneReqStep (g) (reqs) (hsup : SupportedS g)
    (hone : OneReqStep g reqs) : SupportedS (filterAll g reqs)
```

Esto dice algo que no esperaba: **el paso de cláusula de la máquina y la elección del lector son el mismo enunciado**, un requisito cada vez. La cláusula son tres elecciones seguidas.

## 3. Parte 2: los casos de un paso (tres de cuatro, demostrados)

Tenemos una cadena por el superviviente `p` que cumple los requisitos anteriores, y llega el siguiente, `r`:

- **(a)** `p` está en el propio paso de `r`. Entonces `p` **es** `r`: el filtro le dejó un owner con el valor de `r` en ese paso (`owns_required`), y en su propio paso un nodo solo se posee a sí mismo (`OOS`). Toda cadena por `p` cumple `r`. **Demostrado** (`step_case_self`).
- **(b)** la cadena ya lleva el valor de `r` en ese paso. **Demostrado**: no hay nada que hacer.
- **(c)** todos los owners globales de ese paso ya llevan el valor de `r`: el paso estaba fijado antes del filtro. Toda cadena sólida vive en los owners globales, así que lo cumple. **Demostrado** (`step_case_pinned`).
- **(d)** si no, la cadena lleva **el otro valor**: hay que **cambiar un literal**, y la cadena cambiada tiene que existir. Esto es `FlipCore`.

## 4. Cuánto trabajo hace cada caso

Modo nuevo, `lake exe cnfmap --flipcases`. En cada filtro de cláusula de la máquina original, para cada superviviente y cada requisito en orden, clasifica el caso:

| cinco semillas: 9.703 filtros, 593.472 instancias | | |
|---|---|---|
| (c) paso ya fijado | 344.384 | 58,0 % |
| (b) toda cadena ya lo cumple | 75.700 | 12,8 % |
| (a) el nodo está en el paso | 30.786 | 5,2 % |
| **(d) núcleo, y el cambio existe** | **142.602** | **24,0 %** |
| (d) núcleo, **y el cambio NO existe** | **0** | 0 % |

**Los casos demostrados cubren el 76 %.** El núcleo trabaja en una de cada cuatro instancias, y **siempre encuentra el cambio**.

## 5. Por qué el núcleo no se deja partir más

Probé la división natural: el superviviente `p` es owner de un nodo `q` con el valor de `r` (eso lo garantiza el filtro), así que bastaría con que *dos supervivientes que se poseen mutuamente estuvieran en una cadena común que cumpla los requisitos anteriores*.

**Esa pieza es falsa.** Es exactamente la exactitud por pares de las tablas, y las 18 entradas del caso 17 (v66) son pares que se poseen mutuamente sin ninguna cadena común. Partir el núcleo en pares cambiaría un enunciado medido verdadero por uno medido falso.

El núcleo solo es verdadero en su forma existencial: *existe* algún nodo con el valor de `r` en una cadena común con `p`, no necesariamente el `q` que da el filtro. Esa es la forma de tipo Helly que dije en v67, y ya no se reduce a propiedades por pares.

## 6. Qué es el núcleo, dicho en fórmula

En un mapa 3SAT, `FlipCore` dice: *si `p` sobrevive al filtro, entonces las cláusulas vistas hasta ahí, junto con los literales que fija `p` y los requisitos, se satisfacen a la vez*. Eso es una pregunta de satisfacibilidad con un puñado de literales fijados. La máquina la contesta con una comprobación local y polinómica.

La otra dirección (si se satisfacen, `p` sobrevive) es la ley de conservación, y ya está demostrada para las soluciones completas. **Así que el núcleo es exactamente la afirmación de que la comprobación local de la máquina es un oráculo exacto para esas preguntas pequeñas.** Por eso equivale a P = NP, y por eso es donde tiene que caer un contraejemplo, si existe.

**Siguiente pieza demostrable:** la ley de conservación **por prefijo** (toda asignación que satisface las cláusulas vistas está, como cadena, en el estado de su clave). Con ella, `FlipCore` quedaría enunciado en términos de la fórmula, sin grafo. No la he hecho todavía porque exige rehacer media docena de teoremas del driver: la hipótesis de satisfacción completa atraviesa `advance_target`, `isValid_along`, `inhabited_along` y `selOfAssign_son`.

## 7. Lo que queda en firme y lo que no

**Demostrado** (`[propext, Quot.sound]`, 0 `sorry`):
- `SupportedS_filterAll_of_OneReqStep`, `node_of_survivor`;
- `step_case_self`, `step_case_pinned`, `OneReqStep_of_FlipCore`;
- `ClauseStepExact_of_FlipCore`, `decides_of_FlipCore`.

**No demostrado:** `FlipCore`, el caso (d). Medido: 142.602 instancias y 0 fallos.

**Refutado:** la división del núcleo en pares (las 18 entradas del caso 17).

Build: `lake build AbsSat` verde, 93 módulos, 0 `sorry`, 0 axiomas de proyecto.
