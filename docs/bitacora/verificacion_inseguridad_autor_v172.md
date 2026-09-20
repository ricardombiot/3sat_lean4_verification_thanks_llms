# Verificación para el Autor v172: `ImprovesCima` conserva, y lo que queda cabe en una frase

Ricardo, soy Claude (Opus 5). Este informe sigue a v171 y cubre cuatro commits que cierran la mitad
"no pierde soluciones" del veredicto y reducen la otra mitad a un solo enunciado. Rama `spaik`, módulo
`ImprovesCima.lean`. Build de `AbsSat` (232 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`.

## 0. Resumen

* **`ImprovesCima` no pierde ninguna solución parcial** (`cima_chain_below`). La conservación de la
  máquina con la regla, demostrada. La circularidad que temía —el envío necesita ser válido para
  existir— **no existía**: una cadena hace válido a su propio estado.
* El refactor que preparé en v171 salió sin sorpresas: **catorce teoremas que pedían la ejecución
  cuando solo necesitaban las invariantes**. El módulo salió más corto.
* **Una cadena que vive en un lado mantiene vivo a su estado**, fijaciones y regla incluidas
  (`valid_filterAllCima_of_chain`). Sin envío, sin descenso, sin lado que elegir.
* Y con eso, **lo que queda del veredicto cabe en una línea**: `RulePreservesValidity` — *la regla nunca
  mata un estado vivo*. Demostradas **las dos direcciones**: de ahí sale el veredicto, y el veredicto
  sale de ahí. No es una exigencia más fuerte: es el veredicto dicho sobre el filtro.
* Explorándola, se reduce más: **la parte de "vive en un lado" es gratis** (`noBorrow_union`, demostrado
  hace meses) y la de "respeta las fijaciones" también. Lo único con contenido es **"vivo ⟹ no vacío"**.

## 1. La conservación

> **`cima_chain_below`**: para una asignación que cumple las cláusulas por debajo del paso, la línea de
> la ejecución **con la regla** tiene, en el nodo de la asignación, un estado que lleva su rama parcial
> como cadena sana.

La inducción resultó ser exactamente la que la regla estaba pensada para permitir:

| paso | pieza |
|---|---|
| la rama llega al envío del estado anterior | `keepsBranch_Fsac_below`, `chainSound_up_of_prunedR` |
| **el envío está vivo** | porque una cadena hace vivo a su propio estado (`isValid_of_ChainG`) |
| el envío crece hasta la unión por clave | `full_reach`, `ChainSound_of_grown` |
| **la regla no lo toca** | porque el envío **es** uno de los lados (`ChainSound_reviewCima_of_side`) |

El último renglón es donde la regla se cobra: existe para que una cadena que vive en un lado sobreviva a
la unión, y la cadena de la asignación llega desde un envío, que es un lado.

Antes hizo falta poner el suelo: `advanceCima` ahora tira las claves muertas, sus estados vivos son
estados de máquina (`MInv_reviewCima`) y sus líneas son líneas de la máquina (`LineInv_stepsCima`).

## 2. El refactor

Catorce teoremas arrastraban la línea `branchLine φ P m` por sus firmas. **Solo cuatro la consultaban**,
y solo para sacar `StateOkF` y `MInv` — que es exactamente lo que da `LineInv`. Ahora toman cualquier
línea con sus invariantes.

`topValid_cima` hacía lo mismo con la unión: pedía pertenencia a `pureAdvanceW` y la usaba dos veces,
las dos para invariantes. Ahora las pide directamente, y eso es lo que le permite hablar también de un
estado ya revisado.

Va la quinta vez esta semana que aparece el mismo movimiento:

> **Un teorema pide la ejecución cuando solo necesita las invariantes.**

No es dificultad matemática: es deuda de escribir cada teorema contra la máquina que se tiene delante. Y
pagarla ha sido lo que ha desbloqueado cada paso.

## 3. La cadena basta

> **`valid_filterAllCima_of_chain`**: un estado que lleva una cadena sana de uno de sus lados sobrevive
> a las fijaciones que esa cadena respeta y al review entero con la regla.

La cadena es el soporte (`sup_of_chainSound`), su propio lado contesta a la regla en cada estrechamiento
(`carried_of_side`, `cimaOk_of_chain`), y un soporte con un miembro hace válido al estado
(`valid_of_sup`). Treinta y seis líneas, y ninguna elección.

## 4. Lo que queda, en una línea

```
RulePreservesValidity :
    en una unión por clave, sean cuales sean las fijaciones,
    si el estado sobrevive al review normal, sobrevive al review con la regla
```

Sin familias, sin cimas, sin soportes, sin cadenas.

**Las dos direcciones, demostradas:**

* **`sat_of_rulePreserves`** — de ahí sale el veredicto. La regla mantiene vivo el estado; un estado
  vivo tiene un lado con la cima viva (`side_top_alive_of`); y para ese lado `topValid_cima` da el envío
  fijado. `ValidSideAt` cae y con ella `sat_of_validSideOnly`.
* **`rulePreserves_of_genuine`** — y nada se pierde en la traducción. Una unión con un camino genuino
  por las fijaciones la deja viva la regla, porque ese camino es cadena de la unión (`line_complete`) y
  del lado que su propia cima nombra (`advance_top_node`, `send_complete`).

Así que **no es una exigencia más fuerte que el veredicto: es el veredicto, dicho sobre el filtro**. Eso
no lo hace más fácil, pero lo hace *decible*: el problema abierto cabe ahora en una frase que se
entiende sin conocer el módulo, con certificado en Lean de que es exactamente el problema.

## 5. Y explorándola, se reduce más

Fui a ver en qué se puede partir, y hay dos mitades que **ya están pagadas**:

* **"la cadena vive en un lado" es gratis.** `RunNoBorrow.noBorrow_union` —demostrado hace meses, sin
  hipótesis— dice que *una cadena de la unión fijada de dos estados es cadena de uno de los dos*. No hay
  caminos mezclados. Así que no hay que elegir lado: el lado viene dado.
* **"la cadena respeta las fijaciones" es gratis.** Una cadena de un estado fijado las cumple por
  definición: fijar filtra los dueños globales, y una cadena exige que sus nodos lo sean.

Lo que queda con contenido es una sola cosa:

> **Una unión fijada que sigue viva contiene una cadena.**

Es decir, **vivo ⟹ no vacío**. La forma más clásica y más desnuda del problema de este proyecto, sin
nada de la maquinaria encima.

## 6. Lo que esto deja dicho

| pieza | estado |
|---|---|
| veredicto UNSAT | demostrado, sin hipótesis, desde hace tiempo |
| veredicto SAT **por ejecución** (filtro del triángulo) | demostrado; medido 3.071/3.071 |
| **conservación de `ImprovesCima`** | **demostrada** |
| veredicto SAT sin hipótesis | ⟸ `RulePreservesValidity`, equivalente, abierta |
| y ésta ⟸ | **una unión fijada viva contiene una cadena** |

## 7. Dos correcciones mías

Las dejo escritas porque las dos me costaron tiempo:

* Estimé la fase D de v171 como "riesgo medio-alto" y ya estaba demostrada (`send_complete`). El riesgo
  estaba en mi memoria del repositorio, no en la matemática.
* Te vendí la fase 5 como "ensamblaje" y no lo era: al trazar la inducción entera aparece un choque
  entre lo que la unión necesita (validez **con** regla) y lo que el envío da (validez **sin** regla),
  y cruzarlo pide una cadena. Ambas veces el error fue el mismo: **contar la fase antes de trazarla
  entera**.

## 8. Commits

`9f3f467` (la conservación), `41e5083` (el refactor), `8e813e4` (la cadena basta),
`6227275` (`RulePreservesValidity` y su equivalencia).
