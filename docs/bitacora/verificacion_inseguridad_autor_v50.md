# Verificación para el Autor v50: la ley de conservación — el veredicto, cerrado por los dos lados

Ricardo, soy Claude (Opus 5). Tenías razón y yo estaba atacando el enunciado equivocado. Este documento cuenta qué cambió y qué se ha demostrado con ello.

---

## 0. El error de estrategia

Llevaba treinta documentos intentando demostrar una **existencia**: *un estado válido lleva una cadena co-poseída*. Eso obliga a **producir** un testigo a partir de un conjunto construido por podas sucesivas, y por eso chocaba siempre contra el mismo muro — `PairwiseOwned`, `PickValid`, `support` a distancia dos, `CoreCovers`, `share`: cinco caras del mismo problema.

Tu frase decía otra cosa:

> *el conjunto válido contiene de forma abstracta **no una solución sino todas las soluciones***

Eso no es una existencia. Es una **ley de conservación**. Y las leyes de conservación no se demuestran exhibiendo testigos: se demuestran por inducción sobre la construcción, que es exactamente como está construida tu máquina.

## 1. La reformulación

En vez de «∃ una cadena», el enunciado es:

```lean
theorem chainSound_along (φ) (hwf : WF φ) (hsat : Sat a φ) (hzero) (g)
    (h : AlongAssign φ a g) :
    ∃ sel, ChainSound g sel ∧ ∀ k en rango, (sel k).id = selOfAssign φ a k
```

> **Para toda asignación que satisface φ, la selección que esa asignación nombra es una cadena sonora en todos los estados que la máquina construye a lo largo de su rama** — y sus ids de mapa son exactamente las elecciones de la asignación.

**Por qué esquiva el muro:** el testigo ya no hay que producirlo. **Viene de fuera**, lo entrega la asignación. La máquina no tiene que *construir* una cadena; solo tiene que **no destruirla**.

Cierre `[propext, Quot.sound]`. `AbsSat/GraphPath/Model/Conservation.lean`.

## 2. Y todos los lemas de no-destrucción ya estaban demostrados

Esto es lo que hace que la ruta sea corta: los cuatro pasos de la inducción existían, escritos para otros fines, sin que nadie los hubiera encadenado en esta dirección.

| paso | lema | módulo |
|---|---|---|
| semilla | `ChainSound_initSeed` | `AddNode.lean` |
| filtro + crecimiento | `ChainSound_upFiltering` | `AddNode.lean` |
| unión | `ChainSound_join_left` / `_right` | `JoinSound.lean` |

Y la hipótesis que pide el paso del filtro —*la selección satisface todos los requisitos*— es **`CnfSel.reqSat_selOfAssign`**, que demostramos hoy mismo al cerrar el eslabón 1. Sin M3 esta inducción no cerraba.

## 3. Lo que sale gratis, y es lo más bonito

`isValid_of_ChainG` dice que un grafo que lleva una cadena dentro de sus owners globales **es válido**. Así que la supervivencia de la cadena **demuestra la validez**:

```lean
theorem isValid_along … : isValid g = true
```

> **La máquina no puede invalidar un estado que todavía contiene una solución.**

La validez deja de ser una obligación aparte y pasa a ser una **consecuencia**. Eso es, creo, exactamente lo que querías decir con que el conjunto válido «contiene todas las soluciones»: mientras quede una, el conjunto no se puede vaciar.

## 4. El veredicto, por los dos lados

```lean
theorem sound_and_complete (φ) (hwf) (hzero) :
    (∀ g, MapReachable φ g → g.current_step = stepCount φ → Inhabited g → Satisfiable φ)
  ∧ (∀ b, Sat b φ → ∀ g, AlongAssign φ b g → Inhabited g ∧ isValid g = true)
```

- **Soundness** (eslabón 4, `L7.sat_of_inhabited`): si la máquina sostiene un estado que denota algo, la fórmula es satisfacible.
- **Completitud** (aquí): si la fórmula es satisfacible, la máquina no puede quedarse sin estado.

Juntas: **que el conjunto de la máquina sea no vacío es exactamente la satisfacibilidad.** Y todo ello **sin demostrar nunca que un estado válido tenga que producir una cadena**.

## 5. Lo que esto NO cierra — sin adornos

- **`AlongAssign` describe una rama.** La máquina real explora todas las ramas y las indexa por nodo de mapa; el estado que sigue a `a` es una de ellas, así que su validez implica que la línea final no está vacía y el veredicto es SAT. Eso es un argumento sobre el driver, **no todavía un teorema sobre `mirrorRun`** — es la siguiente pieza y es contable.
- **No demuestra «sin zombis» (`Supported`).** Un lector que compruebe validez tras cada elección nunca se atasca: por conservación, invalidar significa que no hay solución por ahí. Pero el lector **sin retroceso** sigue necesitando `Supported`, y eso sigue abierto.
- **No dice nada de complejidad.** Sigue sin haber un solo teorema sobre tiempo o tamaño.

## 6. Estado

| | |
|---|---|
| Eslabón 1 (CNF → mapa) | **cerrado** (v49-M2, banda `cnfmap`) |
| Eslabón 2 (mapa → estados) | cerrado desde F5 |
| Eslabón 3, mitad de completitud | **cerrado** (esta ley de conservación) |
| Eslabón 3, «sin zombis» | abierto |
| Eslabón 4 (cadena → asignación) | **cerrado** (`L7.sat_of_inhabited`) |
| Eslabón 5 (ejecutable ↔ espejo) | empírico |
| El driver: de la rama a `mirrorRun` | siguiente pieza |

`lake build AbsSat` verde, **83 módulos**, 0 `sorry`; `diffTest` 150/150, `cnfmap` 60/60, `validate` 40/40 con `Inhabited` certificado en 3.808 estados.

---

*Claude (Opus 5), 2026-09-10. La idea de este documento es del autor; lo mío fue el ensamblaje.*
