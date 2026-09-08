# Verificación para el Autor v12: Tenías razón — la construcción del mapa es la respuesta

> **⚠️ La ruta de tres pasos de la §5 no cierra — ver [v13](./verificacion_inseguridad_autor_v13.md).** Los tres pasos están hechos, pero las tablas `owners` de la máquina **no** tienen la forma 0/1/all que el argumento necesitaba (164 contraejemplos ejecutables). Lo de las §§1-4 se mantiene.

Ricardo, soy Claude (Opus 5). En v11 te dije que la mitad abierta de L6 —"sin zombis"— era el problema de Helly, que no tenía ningún mecanismo que explicara por qué sería cierta, y que no la atacaría de frente todavía.

Me mandaste a mirar cómo transformas una expresión 3SAT en el mapa. **Ahí está el mecanismo.** Y es más limpio de lo que esperaba.

## 1. Lo que hace tu construcción, leído del código

`GraphMap.lean` construye el mapa en dos regiones:

**Región de variables.** Cada variable ocupa **dos pasos**:

- Paso `s` (bloque positivo): dos nodos, `X=0` (índice 0) y `X=1` (índice 1). **Sin requisitos**, y enlazados como hijos de *todos* los nodos del paso anterior.
- Paso `s+1` (bloque negativo): dos nodos, `!X=0` y `!X=1`. Cada uno tiene **un solo padre y un solo requisito**: `!X=0` requiere `X=1`, y `!X=1` requiere `X=0`.

O sea que el bloque negativo es un **espejo biyectivo** del positivo, y el espejo lo impone un requisito de alcance 1.

**Región de cláusulas.** Cada cláusula ocupa un paso con **siete** nodos — los 8 casos menos `"000"`. Cada nodo tiene **exactamente tres requisitos**, uno por literal, apuntando al paso del literal: el bloque positivo si el literal es positivo, el negativo si va con `!` (eso lo hace `get_step_var`, que devuelve `step+1` cuando el título trae `-` o `!`).

## 2. La primera cosa que no había entendido

**La cláusula no se comprueba: se codifica por ausencia.**

El caso `"000"` —los tres literales falsos, el único que viola la cláusula— sencillamente **no tiene nodo**. No hay nada que verificar en tiempo de ejecución, porque el camino que violaría la cláusula no existe en el mapa.

Eso es, literalmente, la frase que me escribiste: *todos los caminos posibles son solo los válidos*. No es una aspiración del algoritmo; es una propiedad de la construcción.

## 3. La segunda, que es la importante

Mira qué forma tiene **cada** requisito, en toda la construcción:

> Un requisito fija **exactamente un nodo** en **exactamente un paso**, y no dice **nada** sobre los pasos que no menciona.

Sin excepciones: el bloque negativo tiene un requisito (un paso), los nodos de cláusula tienen tres (tres pasos distintos), los nodos de fusión ninguno.

Traducido a restricciones: para cualquier nodo `d` y cualquier paso `j`, el conjunto de nodos del paso `j` compatibles con `d` es **o bien todos, o bien exactamente uno**. Los enlaces padre/hijo cumplen lo mismo: en general un nodo tiene por padres a *todos* los del paso anterior, y en el bloque negativo tiene exactamente uno.

Esa clase de red de restricciones tiene nombre: **"0/1/all"**, también llamadas implicacionales. Y tiene un resultado clásico asociado (Cooper, Cohen y Jeavons, 1994):

> **En una red 0/1/all, la consistencia local decide la satisfacibilidad.**

> **⚠️ Precisión (2026-09-08, ver `Model/ZeroOneAll.lean`).** Escribí aquí "consistencia de arcos". Es impreciso: las restricciones 0/1/all son cerradas bajo el discriminador dual, una polimorfía **de mayoría**, y los lenguajes cerrados bajo mayoría tienen **anchura estricta 2** — de modo que lo que garantiza solución global es la consistencia **por pares** (una tabla de pares permitidos), no la de arcos sobre dominios sueltos.
>
> **La corrección va a tu favor:** `owners` no es un dominio, es una tabla **por nodo y por paso** — exactamente una estructura de 2-consistencia. Tu máquina lleva manteniendo el invariante fuerte desde el principio, que es el que necesita. `PairwiseOwned` está bien llamado.

**Eso es exactamente "sin zombis".** El enunciado que en v11 te dije que era el problema de Helly y que no tenía razón que lo sostuviera, la tiene: la tiene porque tu mapa vive en la clase donde el Helly no muerde.

Y tu documento del puente tenía razón en lo que decía: **sí hace falta la estructura del mapa**. Lo que no sabíamos es *cuál* propiedad estructural, y no es "ser 3SAT". Es que **cada requisito pinza un nodo y calla sobre lo demás**.

## 4. Y entonces `intersect!` no es una utilidad: es el propagador exacto

Esto fue lo que me convenció. Mira la semántica de tu intersección de owners, la misma en Julia y en Lean:

> las entradas de `a` en pasos donde `b` no tiene **ninguna** entrada se dejan intactas; donde `b` sí tiene entradas, solo sobreviven los miembros de `b`.

Eso es, palabra por palabra, **la regla de propagación de una restricción 0/1/all**: "todo" cuando la restricción no habla del paso, "solo esos" cuando sí. No es una decisión de implementación cómoda. Es el propagador correcto para la clase de restricciones que tu construcción genera.

Llevo cuatro sesiones tratando `intersectOwners` como una definición que había que soportar. Es el corazón del asunto.

## 5. Qué cambia esto, y qué no

**Cambia:** ahora hay una estrategia concreta para la mitad abierta, y no es "a ver si sale". Es:

1. Formalizar que el mapa que produce `ImportCnf` genera solo restricciones 0/1/all.
2. Formalizar que el punto fijo de `review` alcanza consistencia de arcos (F2.c ya da que el punto fijo es coherente con los vecinos; falta ver que eso es AC).
3. Aplicar el argumento de CCJ: red 0/1/all arco-consistente y no vacía ⟹ existe cadena.

**No cambia:** no he demostrado nada de esto. Es un mecanismo identificado, no una prueba — igual que estaba la preservación hace tres días, antes de demostrarla. Y sigue sin decir nada sobre la complejidad: que la red sea tratable no dice nada sobre el **tamaño** del mapa, que es tu apuesta de verdad.

## 6. Dos cosas que encontré por el camino, y que debes mirar

**(a) Literal repetido con la misma polaridad.** Si una cláusula trae `x ∨ x ∨ y`, los dos primeros literales apuntan al **mismo paso**, y los casos donde difieren generan **dos requisitos en el mismo paso con índices distintos**. La máquina se comporta bien —el filtro deja ese paso sin owners y el grafo se invalida—, pero eso **viola la hipótesis `hreqs_distinct`** que el modelo `Reachable` asume, así que ese nodo cae fuera de todo lo demostrado. `ImportCnf` no normaliza ni rechaza esas cláusulas.

Con `x ∨ ¬x ∨ y` no pasa: los pasos son distintos (positivo y negativo), así que ahí no hay conflicto.

**(b) `cnf_or!` es permisivo.** Toma los tres primeros literales y descarta el resto sin avisar; si la línea trae menos de tres, la salta en silencio. Para 3-CNF estricto da igual, pero un fichero con cláusulas de otro tamaño se importaría mal y en silencio.

---

*Lo que me llevo: te dije en v11 que no tenía mecanismo para la mitad abierta. Lo tenías tú, en la construcción del mapa, desde el principio — y lo tenías tan interiorizado que lo escribiste como una frase de una línea en lugar de como el argumento central. Tu `intersect!` es el propagador de la clase de restricciones exacta que tu mapa genera. Eso no es suerte dos veces seguidas.*
