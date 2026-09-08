# Verificación para el Autor v10: Lo que las pruebas dicen sobre tu algoritmo

Ricardo, soy Claude (Opus 5). Vuelvo a esta crónica después de v9 con algo distinto de lo que traía entonces. En v9 conté qué axiomas eran falsos y cómo se convirtieron en teoremas. Esto no va de huecos: va de **qué he entendido de tu algoritmo al obligarme a demostrarlo**, y en particular de un sitio donde tu propio documento del puente se equivocaba de problema.

No es un documento de tranquilidad. Hay cosas que salen mejor de lo que esperabas y cosas que salen peor.

## 1. El hallazgo principal: L6 nunca fue un problema de consistencia

`formal_bridge_owners_runpure.md` §5-L6 dice, sobre el lema de "no zombies":

> *La co-propiedad par a par es una 2-consistencia; que 2-consistencia implique una cadena global no es cierto en general — tiene que salir de la estructura específica del mapa 3SAT.*

Eso encuadra L6 como un problema de satisfacción de restricciones: tienes información local (cada par de nodos es compatible) y quieres concluir algo global (existe una cadena entera). Ese salto es falso en general —es el fallo clásico de la consistencia de arcos— y por eso el documento predecía que la demostración necesitaría el bloque de literales, el de cláusulas, los requisitos de alcance 1, todo.

**No hizo falta nada de eso, y la razón es que la pregunta estaba mal planteada.**

L6 no pide *construir* una cadena a partir de los owners. Pide que una cadena que **ya existe** sobreviva. Y en tu máquina las cadenas nunca se sintetizan: se heredan.

- La semilla crea una cadena trivial de un nodo.
- Cada `up` **extiende** la cadena existente con el nodo nuevo — no la reconstruye.
- El `join` **une**, y una cadena de cualquiera de las dos ramas sigue siendo cadena.
- La revisión solo **poda**.

En ningún punto del bucle hay que resolver un CSP. El algoritmo no busca una cadena entre los owners: mantiene un testigo y comprueba que sigue vivo. El problema de Helly aparecería si tuvieras que reconstruir el testigo desde información par a par — y eso tu máquina no lo hace nunca.

Dicho de otro modo: **encuadraste tu propio algoritmo como más difícil de lo que es.** No estabas resolviendo consistencia global; estabas preservando una invariante.

## 2. Qué son realmente los `owners`

Al demostrarlo se ve una cosa que el código no dice en voz alta. Cuando `add_node!` mete un nodo, le da como owners **todos los owners globales** y añade su propio id a los owners de **todos** los nodos, incluido él mismo. Es decir: al nacer, todo el mundo posee a todo el mundo. A partir de ahí los owners **solo se encogen**.

Entonces `owners` no es *evidencia acumulada*. Es **el conjunto de coexistencias todavía no descartadas** — una sobreaproximación que se va afinando.

Eso cambia qué hay que demostrar. La propiedad crítica no es que los owners sean precisos, sino que **la poda nunca descarte una coexistencia real**. Y eso es exactamente lo que dicen los dos lemas centrales que he demostrado (`mem_intersectOwners_of_mem` y `chain_mem_unionOwnersOf`).

Ojo con la asimetría, porque importa: he demostrado que **el filtro no mata cadenas vivas**. No he demostrado que el filtro mate **todas** las muertas. Lo primero sostiene los SAT; lo segundo sostiene los UNSAT, y va por otro camino (el veredicto `isValid` frente a "la denotación es vacía").

## 3. Las tres invariantes no son contabilidad: son tu diseño

Para que la demostración saliera tuve que aislar tres propiedades de una cadena. Ninguna la inventé yo; las tres estaban ya en tu algoritmo, y cada una para una cosa distinta:

| Invariante | Contra qué protege |
|---|---|
| Cada nodo de la cadena es **owner global** | La poda global de `cleanInvalid`. Un owner global sobrevive siempre a la intersección contra `gowners`. |
| Cada nodo de la cadena **se posee a sí mismo** | Que la cadena **se pode a sí misma** en la pasada de coherencia. Sin esto falla el caso en que el vecino testigo es el propio nodo. |
| El enlace **padre/hijo en ambos sentidos** | Aporta el vecino testigo que mete a toda la cadena en la unión de owners de los vecinos. |

Y hay una cuarta que me sorprendió. En tu ejecutable, `make_review_owners!` llama a la pasada de padres con `1 (current_step - 1)` y a la de hijos con `(current_step - 2) 1`. Parecen límites de implementación. **No lo son: son exactamente los rangos donde cada nodo tiene el vecino que lo justifica.** Si la pasada de hijos llegara hasta `current_step - 1`, el nodo de arriba no tendría hijo, no pasaría `is_valid_node`, y se llevaría por delante todas las cadenas.

Subrayo que esto lo comprobé en `GraphPath.lean`, no solo en el espejo: los rangos que cargan con la demostración son los que corren de verdad. Salen en el libro como las Figs. 2.31-2.33. Sospecho que los ajustaste empíricamente hasta que el algoritmo dejó de fallar. Ahora hay una razón formal de por qué son ésos y no otros — y una advertencia: **si alguna vez los tocas, rompes la demostración, no solo un test.**

## 4. Dónde está la fragilidad de verdad

Si me preguntas dónde este sistema es delicado, no te diría L6. Te diría esto:

**`node?` devuelve la primera coincidencia.** En el modelo, "el nodo con este id" y "lo que `node?` devuelve" no son lo mismo salvo que los ids sean únicos. Me ha mordido tres veces en sitios sin relación aparente: al enunciar la forma por nodo de F2.c, al transferir la denotación hacia atrás (hizo falta `NodupIds`), y en los lemas de `cleanInvalidGo`. Donde los ids pueden repetirse, un nodo ensombrecido es un nodo que la propia máquina no puede alcanzar. El modelo puro ya asume ids únicos vía `WellFormedGMap`; el espejo no lo asumía, y ha habido que hacerlo explícito.

**El estado mutable redundante.** Los dos fallos de invalidación muerta que encontramos en el ejecutable —`valid`/`emptySteps` desincronizados, y después el contador `count` que crecía con cada sobrescritura— eran la misma forma: un campo que duplicaba a mano algo ya derivable de una colección. Cada uno hacía que una comprobación de seguridad no pudiera dispararse nunca. En este código, **preferir derivar antes que mantener** no es estilo, es corrección.

## 5. Lo que esto NO dice

Con la misma franqueza:

- **No dice que tu algoritmo sea polinómico.** La complejidad es ortogonal a todo esto. La apuesta real —que `GMap` se puede construir con tamaño polinómico para 3SAT arbitrario— sigue intacta y sin tocar.
- **No dice que L6 esté cerrado.** Falta que `addNode` establezca el tercer campo de la invariante, y eso necesita un hecho estructural que el desarrollo aún no lleva (`map_parent ≠ none` cuando `current_step > 0`).
- **No dice nada sobre el ejecutable.** Todo esto es sobre el espejo puro `GPathM`. El puente entre el espejo y el código que corre sigue siendo **solo empírico**: la banda diferencial de tres vías.
- **No prescinde de todas las hipótesis.** No hace falta la estructura 3SAT, cierto — pero sí las hipótesis de los constructores de `Reachable`: requisitos hacia atrás y distintos por paso. La fase L7 tendrá que descargarlas desde el driver real, y si no puede, este resultado no viaja.

## 6. Una consecuencia que merece que mires

Cada `read_step` del Reader elige un nodo superviviente, llama a `filter!` con un requisito unitario y comprueba la validez. Es decir: **el Reader hace exactamente la operación cuya preservación acabo de demostrar.** Y su mensaje de error dice, literalmente, `Owners invariant violated` — o sea que el "GRAVE ERROR" que temías *es* un contraejemplo de L6, no un problema aparte.

Si eso encaja como parece, "el Reader simple nunca se atasca" —tu E4b— no es un lema nuevo: es este mismo resultado leído en otra dirección.

No lo he formalizado y no lo doy por hecho. Pero si tenía que apostar por dónde el trabajo de estas sesiones se paga otra vez, apostaría ahí.

---

*Lo que me llevo: tu intuición sobre el mecanismo era mejor que tu descripción formal de él. El sistema de identificación `(id, parent_id)` y los rangos de las pasadas de coherencia hacen más trabajo del que el documento del puente les atribuía — tanto, que el obstáculo teórico que temías no llega a aparecer. Eso no salva la conjetura de complejidad. Pero significa que la parte del algoritmo que sí has verificado descansa sobre razones, no sobre suerte.*
