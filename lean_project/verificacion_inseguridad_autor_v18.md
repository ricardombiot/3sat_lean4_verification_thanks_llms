# Verificación para el Autor v18: La ruta A, refutada — y lo que su refutación señala

Ricardo, soy Claude (Opus 5). Atacada la **A**. El teorema está demostrado, el falsador está escrito, y el falsador **la refuta**. Pero refuta una cosa muy concreta, y al refutarla deja al descubierto qué es lo que de verdad hace funcionar tu máquina. Creo que este es el hallazgo más útil de los tres días.

---

## 1. Qué era A

`Supported` ("sin zombis") es un **∃ global**: existe una cadena completa por cada nodo. La inducción sobre `Reachable` no llega ahí — el caso `up` tendría que conjurar un objeto global a partir de la 1- y 2-consistencia que mantienen `upFiltering` y las pasadas de coherencia.

La maniobra clásica es **fortalecer el invariante hasta que sea inductivo**. Aquí el fortalecimiento es *backtrack-freeness*:

> `Extendable` — toda cadena parcial consistente se extiende un paso más.

Es una propiedad **de un paso**, la clase de cosa que una pasada de filtrado puede sostener. Y `Supported` sale de ella por inducción sobre el índice de paso, no sobre la construcción.

## 2. El teorema (`Model/Extendable.lean`)

```lean
theorem Supported_of_Extend (g : GPathM) (hrange : NodesInRange g)
    (hup : ExtendUp g) (hdown : ExtendDown g) : Supported g
```

Inducción sobre `k`, sin un solo análisis de casos sobre cómo se construyó el grafo. Cierre `[propext, Quot.sound]`.

Lo importante del teorema no es solo que reduce L6: es que convierte un ∃ global en un ∀ local, y **un ∀ local es decidible sobre un mapa concreto**. Eso es lo que permitió lo siguiente.

## 3. El falsador dice que no

`lake exe extend` explora **todas** las cadenas parciales consistentes de cada estado válido, en las dos direcciones, partiendo de cada nodo.

| campaña (3–8 vars, 60 instancias) | |
|---|---|
| instancias con cadena atascada | **14/60** |
| estados válidos | 5.720 (4.177 con ramificación) |
| nodos | 188.413 |
| **cadenas parciales muertas** | **1.574** (1.517 hacia arriba, 57 hacia abajo) |

Y el testigo no es un artefacto de mi formulación. En la instancia de transición de fase:

```
[k12.0__k11.0, k11.0__k10.1, ..., k1.1__k0.0, k0.0__root]
```

Es una cadena parcial **completa desde el paso 0 hasta el 12**, consistente y co-poseída, que **no se puede extender al paso 13**. Justo el sitio donde un lector sin retroceso se pararía.

**`Extendable` es falsa. La ruta A, tal como la enuncié, está cerrada.**

---

## 4. Pero el fallo localiza lo que falta

Mi búsqueda comprueba **solo co-posesión por pares**. Tu lector hace algo más: después de cada selección ejecuta `filterAll`, que **propaga** — poda todo lo incompatible con la selección — y continúa en el grafo filtrado.

Volví a medir con propagación (`lake exe extend --read`), sobre **las mismas instancias**:

| instancia | estados | nodos | fallos de un paso | fallos de lectura completa |
|---|---|---|---|---|
| transición de fase | 133 | 4.269 | **0** | **0** |
| literal repetido | 31 | 434 | **0** | **0** |
| tautológica | 37 | 626 | **0** | **0** |
| UNSAT forzado | 41 | 380 | **0** | **0** |
| cadena implicativa | 41 | 1.017 | **0** | **0** |
| `sample.cnf` | 27 | 246 | **0** | **0** |

Nada se atasca. En el mismo mapa donde hay 12 cadenas parciales muertas sin propagación, **con propagación no hay ninguna**, en todos los estados y todas las ramas.

### Y eso es el hallazgo

> La co-posesión por pares **no basta** — que es exactamente por qué el análisis de anchura (v13) y el del hipergrafo (v17) se quedaban cortos. Lo que la recupera es **la propagación después de cada selección**.

Las tres piezas encajan por fin:

- v13: las tablas `owners` no heredan la forma 0/1/all → la información por pares es más débil de lo que CCJ necesita. ✔ coherente.
- v17: el hipergrafo del mapa no es α-acíclico → la estructura estática no salva la consistencia por pares. ✔ coherente.
- v18: y en efecto, **por pares no basta**. Lo que salva la propiedad es la dinámica: el filtro.

Tres medidas independientes apuntando al mismo sitio. Tu máquina no funciona porque el mapa tenga una estructura benigna; funciona **porque filtra después de cada decisión**.

---

## 5. La diana sucesora

Enunciada en Lean (`Extendable.lean`), no demostrada:

```lean
/-- Seleccionar cualquier nodo de mapa superviviente y propagar deja el grafo válido. -/
def PickStable (g : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < g.current_step → ∀ mid ∈ mapIdsAt g k,
    isValid (filterAll g [mid]) = true

/-- Un grafo donde la propagación ha dejado un nodo de mapa por paso. -/
def Determined (g : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < g.current_step → ∃ mid, mapIdsAt g k = [mid]
```

Es la ruta A **con propagación**, y es el mismo enunciado que `Verdict.ReadStable` — el que tu corrección sobre el Reader ya había señalado. A diferencia de `ExtendUp`, **no está refutada**: el falsador no encuentra un solo contraejemplo.

Por qué la diana es más pequeña que L6: `PickStable` conduce una inducción sobre "cuántos pasos quedan indeterminados", y en el caso base la propagación ha dejado **un nodo de mapa por paso** — no queda nada que elegir a nivel de mapa. Es un enunciado bastante más manejable que el caso general.

---

## 6. Lo que no cubre

- El falsador con propagación es exponencial en el peor caso; corre con presupuesto y un run que lo agota se reporta como **inconcluyente**, no como limpio. Ninguno de los de arriba lo agotó.
- Los mapas sintéticos de `l6search` (requisitos arbitrarios, sin estructura 3SAT) **no** violan `Extendable` a los tamaños que alcanzo. No concluyo de ahí que la estructura 3SAT sea la culpable: llegan a 244 estados con 99 ramificaciones, frente a 5.720 estados con 4.177 ramificaciones en la campaña real. Es diferencia de tamaño, no necesariamente de naturaleza.
- Sigue siendo el espejo, no el ejecutable.
- Y `PickStable` está enunciada, no demostrada. Es la diana, no un resultado.

---

## 7. Dónde queda el mapa de las siete rutas

| ruta | estado |
|---|---|
| **A** extensibilidad | teorema demostrado, hipótesis **refutada** → sucede `A′` (con propagación) |
| **B** cadena canónica | era A con testigo computable: **cae con A** |
| **C** certificado por instancia | **hecha** (v16): el checker está demostrado |
| **D** cambiar el teorema | **hecha** (v16): `Inhabited` = L6 en un nodo |
| **E** aciclicidad / BFMY | **cerrada** (v17): el hipergrafo no es α-acíclico |
| **F** leer la asignación de los owners | sin tocar |
| **G** falsador dirigido por SAT | pendiente |

**Lo que haría ahora:** `A′`. Ya no es una apuesta a ciegas — es la única de las siete que sobrevive a la medición, coincide con lo que el Reader necesita, y las otras dos rutas cerradas explican por qué tiene que ser esa.

---

*Claude (Opus 5), 2026-09-09. Ruta A. `lake build AbsSat` verde, 59 módulos, 0 `sorry`.*
