# Verificación para el Autor v11: Me equivoqué en v10 — dónde está de verdad el problema de Helly

Ricardo, soy Claude (Opus 5). Esto corrige el hallazgo central de v10, y la corrección es lo bastante seria como para que v10 no deba leerse solo.

En v10 escribí que tu documento del puente se equivocaba de problema: que L6 no era una cuestión de consistencia global, que el problema de Helly no aparecía por ninguna parte, y que la demostración no necesitaba la estructura del mapa 3SAT.

**La primera mitad de eso es cierta. La segunda es falsa, y lo es porque yo solo había atacado la mitad fácil sin darme cuenta.**

## 1. L6 son dos enunciados, no uno

L6 dice: *todo nodo superviviente está en alguna cadena co-poseída completa*. Al formalizarlo se parte en dos afirmaciones con caracteres opuestos:

| | Enunciado | Estado |
|---|---|---|
| **Preservación** | Una cadena buena **sobrevive** a cada operación | **Demostrado** |
| **Sin zombis** | Todo nodo que sobrevive **tiene** una cadena | **Sin empezar** |

Todo lo que hice entre v10 y hoy —los cuatro lemas de preservación, semilla, `up`, `join`, `review`— es la fila de arriba. Y para la fila de arriba **sí es verdad** que no hace falta la estructura 3SAT: la cadena se hereda, nunca se sintetiza, y por tanto no hay ningún CSP que resolver. Eso lo mantengo.

Lo que hice mal fue reducir L6 entero a la preservación en un módulo temprano (`L6Up.lean`) y no volver a mirar esa reducción hasta tener las cuatro piezas montadas. Cuando las monté, la reducción no cerraba.

## 2. Dónde está el problema de Helly: en la fila de abajo

Un nodo sobrevive a la revisión cuando pasa `is_valid_node`. Y `is_valid_node` es una prueba **puramente local**: que sus owners cubran todos los pasos, que tenga padre, que tenga hijo. Las pasadas de coherencia propagan esa condición entre vecinos — es decir, **consistencia de arcos**.

"Sin zombis" dice, literalmente: *consistencia local ⟹ existe una cadena global*.

**Eso es el problema de Helly.** Palabra por palabra, lo que tu documento del puente predijo:

> *La co-propiedad par a par es una 2-consistencia; que 2-consistencia implique una cadena global no es cierto en general — tiene que salir de la estructura específica del mapa 3SAT.*

No te equivocaste. Me equivoqué yo al declarar el problema ausente cuando lo que pasaba es que aún no había llegado a él.

Y ahora se puede decir algo más preciso que lo que decía el documento: **exactamente una de las dos mitades necesita la estructura 3SAT, y sabemos cuál y por qué.** La preservación es estructural y sale de cómo la máquina construye y poda. Sin-zombis es semántica y no puede salir de la estructura: consistencia de arcos no implica satisfacibilidad, y ninguna cantidad de razonamiento sobre `filter` lo va a arreglar. Tiene que venir del mapa.

## 3. Y esto reparte tu corrección en dos mitades limpias

| Mitad de L6 | Qué te compra |
|---|---|
| Preservación | **Completitud**: si hay solución, no se pierde — la máquina la encuentra |
| Sin zombis | **Soundness**: si la máquina dice válido, hay solución de verdad |

Lo demostrado es la mitad de la completitud. La soundness de los veredictos —que un SAT sea un SAT— descansa entera sobre la mitad que no está.

Dicho crudamente: **he demostrado que tu algoritmo no pierde soluciones. No he demostrado que no invente ninguna.**

## 4. Corrijo también lo que dije del Reader

En v10 sugerí que "el Reader simple nunca se atasca" (tu E4b) podía ser mi resultado de preservación leído en otra dirección. **Al revés.** El Reader se atasca exactamente cuando un nodo sobrevive sin cadena viva — es decir, cuando hay un zombi. Su mensaje `Owners invariant violated` es un **detector de zombis**.

Eso tiene una consecuencia buena: significa que **toda tu evidencia empírica ha estado apuntando a la mitad abierta, no a la cerrada**. Los miles de casos del `diffTest` sin un solo error del Reader, y los 1.680 estados del falsador `l6search` sin contraejemplo, son evidencia de *sin-zombis*. La mitad que sí demostré nunca necesitó evidencia.

No es poca cosa. Es la evidencia dirigida al sitio correcto por accidente de diseño.

## 5. Lo que de v10 sigue en pie

Sin repetirlo entero, porque no ha cambiado:

- **Qué son los `owners`**: coexistencias todavía no descartadas, no evidencia acumulada. Nacen máximos y solo encogen.
- **Las tres invariantes de una cadena**, una por cada mecanismo de poda: ser owner global, poseerse a sí mismo, y el enlace padre/hijo en ambos sentidos.
- **Los rangos `1..cs-1` y `cs-2..1`** de las pasadas de coherencia cargan con la demostración de preservación. Si los tocas, la rompes.
- **La fragilidad real**: `node?` como primera coincidencia sin unicidad de ids, y el estado mutable redundante.

Y añado una lectura nueva de esos rangos, ahora que veo las dos mitades: las pasadas de coherencia hacen **doble trabajo**. Para la preservación están obligadas a **no podar de más** —y los rangos son justo lo que se lo impide—. Para sin-zombis tienen que **podar lo suficiente**. Son tu respuesta al problema de Helly. Si esa respuesta basta es, exactamente, la pregunta abierta.

## 6. Qué haría yo ahora

No intentar sin-zombis de frente todavía. La evidencia dice que es cierto en tus mapas, pero **no tengo ningún mecanismo que explique por qué**, al contrario que con la preservación, donde el mecanismo apareció antes que la prueba.

Endurecería primero el falsador contra esta mitad concretamente: construir grafos donde la consistencia de arcos se sostenga y la cadena global no exista, y ver si la máquina los puede alcanzar. Si aguanta eso, habrá una razón esperando; si se rompe, tendrás el contraejemplo exacto de tu algoritmo — que, como decía tu propio documento, vale igual.

---

*Lo que me llevo de esta corrección: el mecanismo que encontré es real y explica una mitad entera de tu algoritmo. Pero encontrarlo me hizo declarar resuelto un problema que solo había rodeado. Tu instinto sobre dónde estaba la dificultad era mejor que mi lectura de v10 — y la dificultad sigue ahí, ahora localizada con precisión.*
