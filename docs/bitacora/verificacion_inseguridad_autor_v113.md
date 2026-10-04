# Verificación para el Autor v113: tu Reader, formalizado — qué está garantizado y qué no

Ricardo, soy Claude (Opus 5). Este informe trata **solo del Reader**: cómo he formalizado tu algoritmo
de lectura, qué queda demostrado, qué está medido y dónde está el límite. El caso de Tseitin sobre
Petersen, en el que la propia máquina se equivoca, va aparte en v114. Aquí solo aparece por lo que
implica para la lectura.

Todo en la rama `spaik`, en el build de `AbsSat`, sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. El algoritmo que se formaliza

`PathReader.read_step!` (Julia, `docs/original_julia/src/graph_path/reader/path_reader.jl`):

1. recorre **de abajo arriba y solo el bloque de literales**: pasos 0, 2, 4…, una variable por paso;
2. toma el primer id disponible (`first(ids)`) y **fija su nodo de mapa**, es decir, el valor de la
   variable;
3. `filter!`: `filterRequire` más review hasta el punto fijo;
4. si el grafo queda inválido, `"GRAVE ERROR READER"`. No hay backtracking.

En Lean (`AbsSat/GraphPath/Model/AuthorReader.lean`) eso es:

- **`readFrom choose n v g`**: el lector como función. En el paso de valor de la variable `v` fija
  `choose g v`, hace `filterAll` y devuelve `none` si el grafo queda inválido. Devuelve la lista de
  nodos fijados.
- **`readAssign`**: la asignación que deletrean esos nodos (índice 1 = verdadero, la misma lectura
  que `CnfChain.decode`).
- **`authorChoice`**: tu regla, el primer nodo que sigue siendo owner global en el paso de valor.
  Julia recorre un conjunto y Lean la lista de nodos, así que "primero" puede no coincidir. Los
  resultados de abajo no dependen de cuál sea el primero, solo de que esté en una cadena.

## 2. Demostrado sin ninguna hipótesis abierta

- **`readFrom_chain`**: un lector que en cada paso fija el nodo que elige una cadena del estado actual
  **nunca encuentra el grafo inválido** y fija exactamente los nodos de esa cadena. Fijar el nodo de
  una cadena la conserva (`ChainSound_filterAll`), y con ella la validez.
- **`chainRead_final`**: en cualquier estado final, esa lectura **da un modelo de φ**.
- **`chainRead_of_satisfiable`**: **para toda φ satisfacible hay un estado final que se lee sin
  backtracking y da un modelo.**

Los fantasmas (selecciones coherentes por parejas que no son solución) no aparecen en ningún
enunciado. El invariante es semántico: *el estado actual contiene una cadena*.

## 3. Demostrado con una hipótesis: tu regla `first(ids)`

- **`ValueOnChain g v`**: el nodo que elige tu regla está en alguna cadena de `g`.
- **`AuthorReadable`**: eso mismo, en cada estado por el que pasa tu lectura.
- **`pin_forces`**: tras fijar un nodo, toda cadena del estado fijado pasa por él.
- **`readFrom_author`** y **`authorRead_final`**: bajo `AuthorReadable`, **tu Reader lee un modelo
  sin backtracking**. Las cadenas de los estados fijados se suben al estado original con
  `ChainSound_of_pruned`, así que una misma cadena respalda todas las fijaciones.

`AuthorReadable` es la **única** hipótesis de tu Reader, y habla de nodos sueltos, no de selecciones.

## 4. Una reducción de esa hipótesis (`ReaderPin.lean`)

- **`unsupported_removed_rctx`**: el review elimina todo nodo sin soporte también en los estados por
  los que pasa el lector. Antes solo estaba demostrado para estados alcanzables.
- **`pin_exact`**: si las entradas de owner hacia el paso fijado están respaldadas por cadenas, todo
  nodo que sobrevive a la fijación está en una cadena.
- **`authorReadable_of_pinsSound`**: `AuthorReadable` se deduce de esa condición en cada paso fijado.

La reducción es correcta, pero **su hipótesis es demasiado fuerte**. En los gadgets de paridad hay 40
entradas que nombran el valor fijado sin ninguna cadena detrás, y aun así ningún nodo sobrevive por
ellas: el review los elimina **en cascada** (nodos sin padres vivos, o sin soporte en otros pasos),
no por falta de soporte en un solo paso. Lo que de verdad sostiene al Reader es que esa cascada
elimina todo nodo que se queda sin cadenas tras una fijación.

## 5. Lo medido

Con `lake exe join-borrow read`: en cada estado visitado se fijan **todos** los valores disponibles
y se cuentan sus cadenas; una violación de `AuthorReadable` es un valor que deja el estado inválido o
sin cadenas.

| familia | lecturas | valores comprobados | violaciones |
|---|---|---|---|
| aleatorias, 6–8 variables (60 fórmulas) | 459 correctas de 459 | 4.540 | 0 |
| aleatorias, 8–10 variables (40) | 315 de 315 | 4.261 | 0 |
| aleatorias, 10–12 variables (20) | 153 de 153 | 2.592 | 0 |
| gadgets de paridad (todas las elecciones posibles) | lecturas = número de modelos | — | 0 |
| Tseitin guardadas: K4, K3,3, prisma, cubo | todas correctas | — | 0 |
| **Tseitin guardadas: Petersen** | **9 de 9 y 4 de 9 atascadas** | — | **sí** |

## 6. El límite: cuando el estado final ya está mal

En Petersen, el estado final que construye la máquina es **válido pero no contiene ninguna cadena**
(v114). Sobre un estado así ninguna regla de lectura puede acertar: no hay solución que leer, y tu
Reader se atasca. No es un fallo del Reader, sino del estado que recibe. Pero significa que
`AuthorReadable` **no vale para todos los estados finales**.

En todos los casos medidos en que el estado final contiene cadenas, tu Reader leyó bien.

## 7. Con qué tranquilidad puedes quedarte

- **Garantizado**: si el estado final contiene alguna solución, **existe** una lectura sin
  backtracking que la encuentra. Y si φ es satisfacible, ese estado existe.
- **Garantizado, añadiendo una línea**: si al terminar se comprueba la asignación contra las
  cláusulas, **tu Reader nunca devuelve una solución falsa**. En Petersen no la devuelve: se atasca.
- **No garantizado**: que `first(ids)` elija siempre un valor con solución. Solo está medido, y falla
  cuando la máquina deja un estado final zombi.

## 8. Lo que queda

1. Enunciar `AuthorReadable` para estados finales **que contienen alguna cadena** y medir si vale en
   todos ellos, Petersen incluido si se consigue un estado final no zombi.
2. Demostrar la exactitud de la cascada tras **una** fijación de valor (la `LossInClosureD` de siempre,
   pero reducida a una fijación y a los estados del lector), con la clausura `DeadClosure` en lugar
   del soporte de un paso.
