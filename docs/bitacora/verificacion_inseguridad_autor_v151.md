# Verificación para el Autor v151: el núcleo en el idioma de la historia

Ricardo, soy Claude (Opus 5). Tras v150 ataqué `PinPairSoundAt` sin medir y después seguí tu indicación:
*el estado se construye uniendo ramas de asignaciones de forma abstracta*. Este informe recoge las dos
cosas y el estado general.

Rama `spaik`, build de `AbsSat` (223 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Commits
`cebe775` y `f03a4b6`. Módulos nuevos: `ClausePins.lean`, `RunHistory.lean`.

---

## 1. Solo las filas de cláusula pueden cortar caminos (`ClausePins`)

Un nodo del mapa tiene tres tipos de requisitos: ninguno; uno, si es un nodo de negación (el valor opuesto
de su propia variable, un paso por debajo); o tres, si es una fila de cláusula (sus tres literales).

* **Negación, demostrado sin hipótesis** (`soundAt_pin_top`). Su requisito cae en el **paso más alto** del
  estado desde el que se envía, y ahí todos los nodos llevan la clave del estado (`TL`). O el requisito es
  la clave, y ningún camino se corta, o no sobrevive nada.
* **Por tanto, las únicas fijaciones que pueden cortar caminos son las de las filas de cláusula**, y actúan
  cuando todas las variables ya están construidas.
* **Un extremo que ya decidía el paso fijado sale gratis** (`clausePin_of_open`). Si antes de fijar x (o q)
  solo poseía el nodo fijado en ese paso, su camino antiguo ya pasa por él.

## 2. El núcleo en el idioma de la historia (`RunHistory`)

Dos hechos sobre la historia ya estaban demostrados:

* todo camino genuino (la rama de una solución parcial) que pasa por el origen y el destino de un envío
  está en el estado enviado (`send_complete`);
* todo camino de un estado es genuino (`genuine_of_chain`).

Juntos permiten reescribir el invariante de la ruta de construcción **sin hablar de fijaciones, requisitos
débiles ni review**:

> **`SentWitness`**: en cada envío de la ejecución, toda entrada x → q del estado enviado (q en un paso de
> literal) está sobre la rama de una **solución parcial** —una asignación que satisface todas las cláusulas
> hasta el destino— que pasa por la clave de origen y por el destino.

Lo demostrado:

| resultado | contenido |
|---|---|
| `soundAt_sent_iff` | `SentWitness` en un envío ⟺ el invariante en el estado enviado (**nada se pierde en la traducción**) |
| `owns_iff_witness` | con el invariante, **x posee a q ⟺ existe una solución parcial por x y q**: las tablas hacia los literales *son* la relación de compatibilidad entre soluciones parciales |
| `sat_of_sentWitness` | el veredicto bajo `SentWitness`, por inducción sobre la ejecución |
| `soundAt_sent_of_clauses` | todo envío que no va a una fila de cláusula sale gratis (sin requisitos; negación en el paso más alto; requisitos débiles) |
| `sat_of_clauseWitness` | **el veredicto bajo `ClauseWitness`**: `SentWitness` solo en los envíos a filas de cláusula |

Es tu frase formalizada: el estado es la unión abstracta de ramas de asignaciones, y **mientras el
invariante se sostenga, esa abstracción no pierde precisión en las entradas hacia los literales**.

## 3. Lo que queda: `ClauseWitness`

En un envío a la fila d de la cláusula j (desde la clave p), sea x → q una entrada que sobrevive a la
fijación de los tres literales de d y al review. Hay que dar **una** asignación que:

* satisfaga las cláusulas 1…j;
* tome los tres valores de la fila d;
* pase por x, por q y por p.

Lo que la historia ya da, por `owns_iff_witness` aplicado al estado de origen: **cada par** de esos objetos
que se poseen tiene su propia solución parcial (x con q, x con cada literal de d, q con cada literal…). El
review, además, da en cada paso un nodo común a cada par, que también respeta las fijaciones.

Falta **pegar las soluciones de cada par en una sola**. Es la misma elección común de v149, ahora en su
forma más concreta: el review, sobre unas tablas que son **exactas** hacia los literales, tiene que decidir
si el prefijo de la fórmula con esos valores fijados tiene solución. Las rutas de lectura, construcción e
historia desembocan en esta misma pregunta. Ningún argumento local ha bastado hasta ahora (las reglas sobre
pocos nodos se descartaron midiendo); la clave de tu diseño es que el review, al recorrer las filas de
todas las cláusulas anteriores como nodos, hace ese pegado.

## 4. Estado general

### Demostrado sin ninguna hipótesis

| resultado | módulo |
|---|---|
| **toda respuesta es correcta** (UNSAT sin modelo; SAT con certificado comprobado) | `Answer` |
| la máquina contiene todas las soluciones, completas y parciales | `ConservationImproves`, `ConservationPrefix` |
| no hay préstamo entre ramas en las uniones | `RunNoBorrow` |
| todo camino es una solución real; cláusulas decididas, propagación unitaria, filas testigo | `LiveSolution` |
| semilla, unión, UP y review conservan "hay caminos" | `RunInhabited` |
| los requisitos débiles no cambian nada | `WeakNoop` |
| **los nodos de negación no cortan caminos; un extremo decidido sale gratis** | `ClausePins` |
| **el invariante ⟺ las entradas se explican por soluciones parciales; tablas = compatibilidad** | `RunHistory` |

### La única dirección que falta

```
veredicto ⇐ ClauseWitness (en los envíos a filas de cláusula, cada entrada superviviente
             se explica por una solución parcial que toma los valores de la fila)
   ├─ envíos sin requisitos, de negación, requisitos débiles   ✔ demostrado
   ├─ extremo que ya decidía el paso fijado                    ✔ demostrado (forma por fijaciones)
   ├─ cada par tiene su solución parcial (tablas exactas)      ✔ demostrado (owns_iff_witness)
   └─ pegar las soluciones de los pares en una                 ✘ abierto — la elección común
```

### Siguiente paso propuesto

Formalizar lo que el review aporta en el paso de la cláusula en términos de asignaciones: para cada
cláusula anterior, una fila viva común a x, q y los literales fijados (la versión con fijaciones de
`entry_witness`). Una advertencia honesta: el enunciado *"si cada cláusula tiene una fila compatible con
todos y cada par tiene su solución, existe una solución común"*, tal cual, no es cierto para fórmulas
arbitrarias (la consistencia local no basta en general). Así que el paso siguiente no es solo ese
enunciado, sino encontrar **qué más aporta la historia de tu máquina** —el orden de los envíos, las
uniones por clave, las filas como nodos— que lo haga cierto aquí.
