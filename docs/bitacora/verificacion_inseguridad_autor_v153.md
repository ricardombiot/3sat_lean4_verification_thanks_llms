# Verificación para el Autor v153: fijar es un requisito que la historia ya aplicó

Ricardo, soy Claude (Opus 5). He seguido tu indicación: fijar un valor es filtrar un requisito del mapa,
es decir, quitar los caminos parciales que pasan por el valor incompatible; los pares o tríos son solo más
requisitos. Este informe lo formaliza con la ejecución restringida que ya teníamos (`BranchRun`, v125).

Rama `spaik`, build de `AbsSat` (225 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Módulo nuevo:
`PinHistory.lean`. Sondas nuevas: `helly pincommute`, `helly pin1`, `helly basejoin`, `helly basewhy`.

---

## 1. La idea

Cuando la ejecución estaba en el paso de una variable, esa variable era la **clave**. La rama de una
fijación (la ejecución que en ese paso solo conserva la clave fijada) **nunca construyó el otro valor**.
Así que los tres valores de una fila de cláusula son tres requisitos que la rama ya aplicó cuando sus
variables eran clave, y la rama sigue siendo una ejecución de tu máquina.

## 2. Lo demostrado

| resultado | contenido |
|---|---|
| `branchLine`, `branchLine_nil` | la línea de la rama de P en el paso m; sin fijaciones es la línea de la máquina |
| `branchLine_inv` | las ramas conservan los invariantes de la máquina |
| `branchLine_emb` | más fijaciones, rama más pequeña: la rama de P ++ R está dentro de la de P, clave a clave |
| **`pinIds_branch`** (sin hipótesis) | en un estado de la rama, todo nodo de un paso fijado **es** el valor fijado |
| `chain_pins` | por tanto, todo camino de la rama toma los valores fijados |
| **`branch_sound`** | bajo `PinCommutes`, todos los estados de todas las ramas conservan el invariante (inducción sobre el paso, para todas las ramas a la vez) |
| `sat_of_pinCommutes` | el veredicto |
| **`pinCommutes_of_one`** | basta **una fijación cada vez**: `PinCommutes1 ⟹ PinCommutes` |
| `sat_of_pinCommutes1` | el veredicto bajo `PinCommutes1` |

La inducción funciona así. En el envío a una fila, una entrada que sobrevive es (por la hipótesis) una
entrada de la rama que además lleva las tres fijaciones de la fila. Por la inducción, esa entrada está
sobre un camino de esa rama. Ese camino está en el estado desde el que se envía y toma los valores
fijados, así que sobrevive a la fijación. Es el pegado que faltaba en v152, hecho por la historia.

## 3. La hipótesis que queda

> **`PinCommutes1`**: en un estado de una rama, con todas las variables construidas, fijar un valor y
> hacer el review da un estado **dentro** del estado con la misma clave de la rama que además lleva esa
> fijación.

Dicho con tus palabras: *aplicar el requisito ahora da lo mismo que haberlo aplicado cuando la variable
era la clave*.

## 4. Medidas

| sonda | qué mide | resultado |
|---|---|---|
| `pincommute` (profundidad 2) | `PinCommutes` en cada envío a fila de cláusula, en la ejecución y en las ramas de un nivel | paridad k3 asc: 1.195.790 entradas, **0 violaciones**; paridad k3 desc: 102.040, **0**; Tseitin K4: 745.413, **0**; ninguna clave ausente |
| `pin1` | una fijación en **todas** las líneas, también en la etapa de variables | paridad k3 desc: 794 fijaciones, **0**; Tseitin K4: 1.776, **0** |

Hay dos sondas más en curso (`pin1` en más familias y `pincommute` en fórmulas aleatorias); sus resultados irán en el siguiente informe.

La conmutación de una fijación se cumple **en todas las líneas**, no solo en la etapa de las cláusulas. Eso
permite demostrarla por inducción sobre la historia, línea a línea.

## 5. Dónde está la dificultad

La inducción línea a línea de `PinCommutes1` tiene tres pasos:

1. **fijar atraviesa un envío** (filtros, review, UP): los filtros conmutan tal cual y el UP distribuye
   (`ReviewJoin.embedded_addNode_join`); falta el review, que se espera demostrable;
2. **fijar atraviesa una unión por clave**: es exactamente `ReviewJoin` (v138), el review de una unión;
3. **caso base**: la fijación cae en el paso justo debajo de la clave, donde los lados de la unión se
   separan por su clave (`SideCover`, v146).

Así que todas las rutas desembocan en el mismo núcleo: **el review de una unión por clave no toma prestado
entre lados**. Lo que cambia con este informe es la forma: ahora es una afirmación sobre **una sola
fijación**, medida sin excepciones en todas las líneas, y todo lo demás está demostrado.

## 6. El caso base de la unión por clave (sondas `basejoin`, `basewhy`)

En una unión por clave, los lados son los envíos desde las claves de la línea anterior. Fijo una de esas
claves y comparo el review de la unión fijada con el envío desde esa clave sola.

| fijación | entradas ajenas antes del review (dos extremos vivos en el lado fijado, entrada solo de otro lado) | tras el review |
|---|---|---|
| **valor de literal** (lo que usa `PinCommutes1`) | **0** (paridad k3 ×2, Tseitin K4) | — |
| clave de fila de cláusula | 834 (48 + 480 + 306) | **todas mueren**; ninguna sobrevive |

* Para fijaciones de literal, el caso base cae en la etapa de variables, y ahí **los lados coinciden en sus
  nodos compartidos**: no hay nada que el review tenga que corregir.
* Para claves de fila, el review sí trabaja: mata la entrada ajena (sus dos extremos siguen vivos). Al
  comprobar contra las tablas finales, cada entrada muerta falla la regla del nodo común en **muchos
  pasos a la vez** (por debajo de la fijación, y en paridad también en el propio paso fijado), y también
  las reglas de padre e hijo. **No hay una regla local única que la mate**: es el punto fijo entero.

Esto sitúa la dificultad de `ReviewJoin`: en la etapa de cláusulas, cuando los lados vienen de filas
distintas, sus tablas difieren en nodos compartidos, y que el review elimine lo que sobra es la misma
afirmación global que `RunPaths` (`PartSplitReal`): *toda entrada de la unión fijada y revisada está
sobre un camino fijado de uno de los lados*. En el repo ya está demostrado
`ReviewJoin ⟸ SupportSplit ⟸ RunPaths`.
