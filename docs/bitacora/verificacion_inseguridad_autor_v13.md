# Verificación para el Autor v13: La ruta de v12 no cierra — y por qué eso también es información

Ricardo, soy Claude (Opus 5). En v12 te dije que la construcción de tu mapa daba el mecanismo que faltaba, y tracé una ruta de tres pasos. Los tres están hechos. **La ruta no cierra**, y el sitio donde se rompe no es donde yo pensaba.

Esto no es una retractación de v12. Es el resultado de haberlo ejecutado.

## 1. Lo que sí quedó demostrado

| Paso de v12 | Resultado |
|---|---|
| (1) El mapa solo genera restricciones 0/1/all | `MapReqs.lean` — y es **exhaustivo**: `add_require!` se llama en cinco sitios y los cinco están cubiertos |
| (2) El punto fijo de `review` es localmente consistente | `ArcConsistency.lean` — y resultó no ser matemática nueva: **la consistencia local *es* `is_valid_node`** |
| (3) Núcleo matemático | `ZeroOneAll.lean` — **los soportes todo-o-uno tienen la propiedad de Helly**, en `[propext]` |

Y una pieza más, que es la mejor noticia del día:

**`owners_pinned_at_required_step`**: en un paso que uno de sus requisitos nombra, los owners de un nodo proyectan **exactamente** a ese requisito. Nada más sobrevive ahí. Es tu lema L1 leído a nivel de mapa —que es donde vive la red de restricciones— y dice que **el filtro impone exactamente lo que el mapa pide**. El "1" del 0/1/all se cumple en las tablas de tu máquina.

## 2. Dónde se rompe

La otra mitad del 0/1/all sería: en un paso que **ningún** requisito nombra, los owners deberían proyectar a **todos** los nodos de mapa todavía disponibles.

**Es falso.** El falsador lo exhibe: sobre 1.680 estados reporta **164 pares (nodo, paso) en grafos válidos** cuya proyección es un subconjunto propio de dos o más nodos de mapa. Un testigo concreto:

> proyección `{(2,0), (2,1)}` contra un dominio de paso 2 que es `{(2,0), (2,1), (2,2)}`.

Ni singleton, ni todo.

**Y no es un fallo tuyo.** El mecanismo es este: la pasada de coherencia interseca los owners de un nodo contra la **unión** de los de sus vecinos, y la unión de dos singletons es un conjunto de dos elementos. Tus tablas **agregan sobre los vecinos**. Son una aproximación de consistencia de arcos a lo largo de los enlaces padre/hijo, no las filas de la red de restricciones.

## 3. Qué significa

Las restricciones **crudas** que genera tu mapa sí son 0/1/all —eso está demostrado y se mantiene—. Los soportes todo-o-uno sí tienen la propiedad de Helly —eso está demostrado y se mantiene—. Lo que no se sostiene es el paso que los conecta: **las tablas de tu máquina no son esos soportes.**

Así que el hueco no era la inclusión `owners ⊆ soporte` que enuncié ayer. Es más profundo y más preciso:

> Las restricciones 0/1/all son cerradas bajo mayoría, lo que da **anchura estricta 2** — y eso pide **consistencia de caminos**. Tu máquina mantiene algo más débil: consistencia de arcos por los enlaces padre/hijo, más los owners globales.

La pregunta abierta ya no es "¿vale CCJ?". Es: **¿basta esa propagación más débil para este mapa concreto?** CCJ de catálogo no lo responde.

## 4. Por qué esto también es información

Tres cosas que antes no sabíamos y ahora sí:

- **El "1" está demostrado.** Donde el mapa pide algo, tu filtro lo impone exactamente. Eso no era obvio y ya no hay que suponerlo.
- **Sabemos qué le falta a la propagación**, con nombre: la distancia entre arco-consistencia por enlaces y consistencia de caminos. Es una diferencia concreta, no una nebulosa.
- **Sabemos que la brecha es real y no un artefacto de la demostración**, porque hay 164 testigos ejecutables. Si alguien intenta esta ruta otra vez, el falsador se lo dice en segundos.

Y la evidencia empírica sigue diciendo que la conclusión es cierta aunque la ruta no la alcance: ningún error del Reader en miles de instancias de `diffTest`, ningún contraejemplo en 1.680 estados.

## 5. Lo que yo haría ahora, y lo que no

**No** insistiría en CCJ. Está descartado como atajo.

Hay dos caminos, y creo que el segundo es el tuyo:

1. **Reforzar la propagación hasta consistencia de caminos** y demostrar que entonces sí decide. Eso cambia tu algoritmo — probablemente su coste — así que solo tiene sentido si el objetivo es la corrección y no la complejidad.
2. **Demostrar que para *este* mapa la propagación débil basta**, usando estructura que CCJ no ve: los requisitos van hacia atrás, el bloque negativo es una biyección espejo, y cada cláusula tiene exactamente 7 nodos con 3 requisitos cada uno. Es un argumento a medida, más trabajo, pero no cambia tu algoritmo.

La (2) es la que preserva tu apuesta. Y ahora hay una diana precisa a la que apuntar en vez de "demostrar L6".

---

*Lo que me llevo: v12 fue el documento más optimista que te he escrito y la parte central sigue en pie — tu construcción es 0/1/all y ésa es la razón de que el problema de Helly no muerda en las restricciones. Lo que no sobrevive es mi suposición de que las tablas de la máquina heredaban esa forma. La ejecuté, la máquina dijo que no 164 veces, y prefiero traerte eso que una ruta elegante que no llega.*
