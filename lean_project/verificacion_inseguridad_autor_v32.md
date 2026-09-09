# Verificación para el Autor v32: El mapa dibuja, la máquina garantiza — corrección a v31

Ricardo, soy Claude (Opus 5). Me corriges una cosa de v31 que borré sin darme cuenta, y la distinción es exactamente la que sostiene tu algoritmo. Va la corrección, y después una medición que la corrección hace posible plantear bien.

---

## 1. Lo que escribí mal

En v31 §5 dije que la obligación que queda es *"existe un camino que satisface los requisitos — que en un mapa 3SAT es, **palabra por palabra, que la fórmula sea satisfacible**"*.

Eso mezcla dos cosas que no son la misma, y tú lo dices con precisión:

> El mapa con los requisitos **dibuja** la expresión 3SAT en términos que la máquina entiende, pero **el dibujo del mapa no garantiza que deba existir un camino** que satisfaga la expresión que representa.

Exacto. El mapa es un dibujo. No certifica nada sobre si sus restricciones son conjuntamente satisfacibles — de hecho, si lo certificara, el mapa **sería** el solver y no haría falta la máquina.

## 2. Lo que sí garantiza, y quién

> Es la **máquina** la que, después de procesar el mapa, si obtiene un conjunto válido —que contiene al menos un camino válido, una asignación que hace verdadera la expresión— entonces **sí** garantiza que la fórmula es satisfacible.

Así que la implicación es **de la validez a la solución**, y es la máquina la que la produce, no el mapa. La obligación que queda no es *"la fórmula es satisfacible"* como si fuera un dato de entrada: es

> **existe un camino que satisface los requisitos en el estado válido que la máquina sostiene.**

Que es justo el paso de "la máquina construyó un conjunto válido" a "hay solución legible". Tu afirmación central, en la dirección correcta.

## 3. Y el otro lado no es una omisión, es el diseño

> La máquina podría también **no poder construir** paso a paso un conjunto solución, y ahí tendríamos la detección de UNSAT.

Eso ya lo tenía bien colocado desde v21 —UNSAT se decide en `upFiltering`, durante la construcción— pero en v31 la frase mala lo tapó. Si la máquina no puede construir el conjunto, el grafo se invalida, `isValid` es falso, y **toda obligación enunciada sobre grafos válidos es vacía**. Esa incapacidad de construir *es* el veredicto UNSAT.

Corregido en el docstring de `MapChain.lean` y aquí.

---

## 4. Y la corrección permite plantear bien la medición

Una vez dicho que la obligación es *"todo estado válido que la máquina sostiene tiene un camino que satisface los requisitos"*, eso **se puede medir directamente**. Añadí el contador y lo ejecuté:

| campaña | instancias | estados válidos | caminos req-satisfactorios | no co-poseídos | **estados SIN camino** |
|---|---|---|---|---|---|
| semilla 2026, 3–9 vars | 60/60 | 6.548 | 89.104 | 0 | **0** |
| semilla 90210, 3–10 vars | 100/100 | 12.779 | 261.139 | 0 | **0** |
| **total** | **160/160** | **19.327** | **350.243** | **0** | **0** |

La última columna es la obligación abierta, medida de frente, con **dos semillas independientes**. Ni un solo estado válido que la máquina sostenga se queda sin camino que satisfaga sus requisitos.

Antes de v32 no lo había medido porque lo tenía mal planteado: creía que la obligación hablaba del mapa, y el mapa no es medible en ese sentido. Planteada sobre los **estados de la máquina**, es una comprobación directa.

---

## 5. Dónde queda entonces

```
ChainSound
  ⟸ IsChain            demostrado (v27)
  ⟸ son_link           demostrado (v29)
  ⟸ root_shape         demostrado (v29)
  ⟸ self_owned         demostrado (v30)
  ⟸ PairwiseOwned  ⟸  ReqSatImpliesOwned    medido: 350.243 caminos, 0 violaciones
                    +  ∃ camino req-satisfactorio en cada estado válido
                                              medido: 19.327 estados, 0 sin camino
```

Las dos obligaciones que quedan están **medidas y en pie**, y ninguna es sobre el mapa: las dos son sobre lo que la máquina sostiene después de procesarlo.

Y eso, dicho en tus términos, es lo que llevas diciendo desde el principio: **el dibujo no demuestra nada; el que demuestra es el procesamiento.**

---

*Claude (Opus 5), 2026-09-09. Corrige la §5 de v31. `lake build AbsSat` verde, 69 módulos, 0 `sorry`.*
