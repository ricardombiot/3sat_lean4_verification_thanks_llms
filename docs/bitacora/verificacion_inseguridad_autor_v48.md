# Verificación para el Autor v48: el paso 0 y la barrida de hijos — estudio

Ricardo, me preguntas si es un error de implementación no revisar el paso 0, y cuánto nos facilitaría la demostración hacerlo. He estudiado las dos cosas. **La respuesta corta: es una asimetría sin razón, no es un fallo de corrección, y sí cierra un hueco concreto que ahora mismo está abierto.** No he tocado la máquina — el cambio es tuyo.

---

## 1. De dónde vienen los rangos

El espejo copia al ejecutable y el ejecutable copia a Julia. Los rangos son estos:

```julia
review_owners_parents_sons!:   for step in 1:gpath.current_step-1
review_owners_sons_parents!:   for step in gpath.current_step-2:-1:1
```

**Tres de las cuatro cotas están forzadas:**

| cota | razón |
|---|---|
| padres, inferior = 1 | un nodo del paso 0 **no tiene padres**: la unión sería vacía y la pasada no haría nada |
| padres, superior = `S-1` | es la cima, y la cima **sí tiene padres** |
| hijos, superior = `S-2` | la cima **no tiene hijos**: la pasada no haría nada |
| **hijos, inferior = 1** | **ninguna** — un nodo del paso 0 **sí tiene hijos** |

La cuarta no tiene justificación. Tiene la forma de una cota copiada del bucle de padres sin volver a derivarla para el de hijos.

## 2. ¿Es un fallo de corrección? No

La omisión solo puede dejar los `owners` **más grandes** de lo que deberían. Owners más grandes ⇒ `owners_ok` más fácil ⇒ menos eliminaciones ⇒ `isValid` más fácil de cumplir. Luego:

- **no puede producir un UNSAT falso** — nunca invalida de más;
- podría, en principio, dejar soporte rancio en el paso 0 (un candidato a zombi).

Y medido (`lake exe extend --zerosons`, dos semillas):

| campaña | nodos del paso 0 en estados válidos | perderían owners con la barrida | entradas que quitaría | quedarían inválidos |
|---|---|---|---|---|
| 25 casos, semilla 2026, 3..7 vars | 3.292 | **3** | 15 | **0** |
| 40 casos, semilla 90210, 3..10 vars | 7.333 | **51** | 317 | **0** |

Así que **no es un no-op** —deja soporte que sus hijos no respaldan, en un 0,1–0,7 % de los nodos raíz— pero **nunca invalida un estado**. Es una poda perdida, no un error de veredicto.

## 3. ¿Cuánto facilitaría la demostración? Lo probé

Apliqué el cambio (`reviewSons` sobre `intRange 0 (current_step - 2)`) y reconstruí los 74 módulos. Esto es lo que pasó:

**Rompió exactamente tres anotaciones de rango**, todas mecánicas:

1. `GPathM.reviewSons` — el rango en sí;
2. `Fuel.review_owners_coherent_sons` — la hipótesis `k ∈ intRange 1 …` y una línea de su cuerpo;
3. `ArcConsistency.ArcConsistent.coherent_sons` — el campo de la estructura.

**Y nada más.** Ni una demostración tuvo que reescribirse.

**La razón por la que no rompe nada es la que más me ha sorprendido:** el lado de la preservación **ya estaba demostrado para el paso 0**.

```lean
theorem ChainSound_reviewLine_sons  (g) (k) (hk : 0 ≤ k) …
theorem ChainSound_reviewSteps_sons (ks) (cs) (hks : ∀ k ∈ ks, 0 ≤ k ∧ k + 1 < cs) …
```

Quien escribió esos lemas derivó la condición lateral natural —`0 ≤ k`— y **no coincide con el bucle**. Es decir: ya está demostrado que barrer el paso 0 con los hijos **no puede cortar una cadena sonora**. La justificación de la poda extra ya estaba en el repositorio, esperando.

**Lo que se gana, concretamente:**

- `Threaded.hop_up` pierde la hipótesis `1 ≤ p.id.step`.
- `Survive.support_above` la pierde también.
- **`Survive.son_of_hop_up` la pierde — y eso cierra exactamente el hueco que dejó v47**: la cláusula `Closed.son` para un candidato en el paso 0 con el pinchazo en otro paso. Con el cambio, `Closed_PinSet` necesitaría **una sola** hipótesis, `hsupport`.
- El rodeo `hop_up_zero` + `PMS` en `threaded` se vuelve innecesario (aunque `PMS` está demostrado y vale por sí mismo).
- Y `coherent_parents` / `coherent_sons` pasan a ser simétricos —«todo nodo no-raíz» / «todo nodo no-cima»— lo que quita condiciones laterales asimétricas de todo el desarrollo.

**Lo que NO se gana:** el residuo principal. `support` a distancia ≥ 2 sigue igual — las mismas 3.473.942 comprobaciones lejanas, los mismos 0 fallos. Esto no acerca `CoreCovers`.

## 4. Comportamiento: no cambia veredictos

Con el espejo extendido, `lake exe diffTest` —que compara **ejecutable + espejo + oráculo por fuerza bruta**— pasa **150/150** y **400/400**. Ni un veredicto ni un conjunto de soluciones cambia.

## 5. Aplicado (2026-09-10, decisión del autor)

**El cambio está aplicado a los dos lados**, ejecutable y espejo, en el mismo commit. La copia de Julia queda intacta como registro histórico y los docstrings que decían *«Mirrors Julia's `review_owners_sons_parents!`»* ahora dicen que **divergen deliberadamente**, con el porqué y la referencia a este documento.

**El pago se cobró:** `Closed_PinSet` e `isValid_cleanInvalid_pin` pasan de **dos hipótesis a una**. `son_of_hop_up` ya no tiene salvedad de paso, así que la cláusula `son` deja de ser hipótesis en todos los pasos no-cima, y **lo único que queda debido es `support`**.

**Verificación tras aplicarlo:**

| comprobación | resultado |
|---|---|
| `lake build AbsSat` | verde, 74 módulos, 0 `sorry`, cierres intactos |
| `lake exe diffTest 400 2026` | **400/400** (352 SAT, 48 UNSAT) |
| `lake exe diffTest 300 90210` | **300/300** (255 SAT, 45 UNSAT) |
| `lake exe validate --random 50 2026 3 5` | **50/50** limpias, 4.835 estados, 151.308 nodos, 4.835 `Inhabited` certificados |
| `lake exe extend --zerosons 25 2026 3 5` | **0** nodos con soporte rancio (antes 3), mismos 3.292 nodos raíz y 4.835 estados válidos |

La última línea es la que cierra el círculo: la medición que detectó el problema ahora da cero, y el recuento de estados y de nodos raíz **no ha cambiado** — se podó soporte rancio, no se perdió nada.

Las ediciones, para el registro:

```
GPathM.lean         reviewSons: intRange 1 (current_step-2)  →  intRange 0 (current_step-2)
GraphPath.lean      review_owners_descending! … (current_step - 2) 1  →  … 0
Fuel.lean           review_owners_coherent_sons: intRange 1 …  →  intRange 0 …   (×2)
ArcConsistency.lean coherent_sons: intRange 1 …  →  intRange 0 …
Threaded.lean       hop_up: 1 ≤ p.id.step  →  0 ≤ p.id.step
Survive.lean        support_above, son_of_hop_up: idem
```

(más `Survive.Closed_PinSet` e `isValid_cleanInvalid_pin`, que pierden la hipótesis `hson`.)

## 6. Resumen

| pregunta | respuesta |
|---|---|
| ¿Es un error de implementación? | Una **asimetría sin justificación**, con forma de cota copiada. No es un fallo de corrección. |
| ¿Cuesta algo dejarlo? | Soporte rancio en el 0,1–0,7 % de los nodos raíz. Nunca invalida. |
| ¿Qué gana la demostración? | Cierra el hueco de v47 (`Closed.son` en el paso 0) y hace simétricas las dos cláusulas de arco-consistencia. Tres anotaciones de rango, ninguna demostración reescrita. |
| ¿Es seguro? | El lado de la preservación **ya está demostrado para el paso 0**. `diffTest` 400/400 con el espejo extendido. |
| ¿Acerca `PickValid`? | **No.** El residuo no se mueve. |
| ¿Aplicado? | **Sí**, a ejecutable y espejo. `diffTest` 400/400 y 300/300. |

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 74 módulos, 0 `sorry`. El cambio está aplicado a ejecutable y espejo; la copia de Julia queda como registro histórico.*
