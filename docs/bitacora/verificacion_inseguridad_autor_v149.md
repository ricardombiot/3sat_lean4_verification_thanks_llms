# Verificación para el Autor v149: el núcleo dividido — lo local está demostrado, queda la elección común

Ricardo, soy Claude (Opus 5). Este informe recoge lo hecho tras v148: el intento de atacar `LivePinUp` con
la técnica de la historia, la división de la frase del núcleo y tu observación de que, para tu máquina, las
cláusulas con dos o tres literales abiertos son lo mismo. Al final, el estado general actualizado.

Rama `spaik`, build de `AbsSat` (218 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Commits
`3a04b59`, `969da6d`, `efa7be9`, `7025bd2`. Módulo: `LiveSolution.lean`.

---

## 1. Por qué la técnica de `NoBorrow` no cierra `LivePinUp` sola

La técnica de la historia sabe dos cosas, las dos demostradas:

* **un camino que existe es una solución real** (`path_is_solution`, nuevo, sin hipótesis);
* **toda solución real está en el estado de su clave** (completitud, total y por prefijos).

Con eso bastó para `NoBorrow`, porque ahí el camino ya existe y solo hay que situarlo. `LivePinUp` pide lo
contrario: que **exista** un camino a partir de que el estado es válido. Cuando un nodo de variable se
crea, todos los prefijos son viables (aún no se ha visto ninguna cláusula); la pregunta es si sigue en una
solución después de que las cláusulas lo filtren, y eso la historia no lo da.

`livePinUp_of_onPath` deja el núcleo en su forma más limpia:

> **En un estado válido del lector, con el prefijo decidido, todo valor que sobrevive al review forma
> parte de una solución real** (`LiveOnPath`).

## 2. La frase dividida

Sea α la asignación parcial: el prefijo decidido más el valor vivo `a` de la variable `v`. Las cláusulas se
dividen por cuántos literales **abiertos** (variables mayores que `v`) les quedan.

| pieza | enunciado | estado |
|---|---|---|
| **(A) decididas** | toda cláusula con todas sus variables ≤ `v` queda satisfecha por α | **demostrado** (`decided_clause_holds`) |
| **(B1) unitarias** | si α deja una cláusula con un único literal abierto, todo nodo que `a` posee en ese paso lo hace verdadero | **demostrado** (`unit_forced`) |
| **(B2 = B3) resto** | cláusulas con dos o tres literales abiertos | **uniforme**: ver § 3 |

La idea de las pruebas: **una fila que un valor vivo posee lleva los valores del prefijo** (`row_bit`).
En cada paso de un literal, la fila y `a` comparten un nodo (la regla de nodo común del review); ese nodo
lleva el valor decidido, o el de `a`; los requisitos de la fila (`ReqFiltered`) igualan sus bits a esos
valores; y como toda fila que el mapa construye hace verdadero algún literal (índice 1…7), si los literales
decididos son falsos, el abierto queda forzado. **El review ya contiene la consistencia de las cláusulas
decididas y la propagación unitaria.**

## 3. B2 = B3: la cláusula es un nodo fila

Tu observación: en tu mapa, una cláusula es un **nodo fila** cuyos requisitos fijan sus tres literales; B2
y B3 solo difieren en cuántos de esos requisitos caen sobre variables ya decididas. Formalizado de forma
uniforme:

* **`row_bit_prefix`** (sin hipótesis, sin valor vivo): **toda fila viva lleva el prefijo decidido**. La fila
  posee un nodo en el paso de cada literal decidido, y ese nodo solo puede llevar el valor del prefijo.
* **`entry_witness`** (sin hipótesis): **todo par de nodos que se poseen tiene como testigo una fila viva**.
  En el paso de cualquier cláusula comparten una fila que posee a ambos, fija sus valores por sus
  requisitos, lleva el prefijo y hace verdadero algún literal.

(A) y (B1) son casos particulares. **Localmente, las tablas garantizan que todo lo que se posee entre sí es
compatible con alguna solución local de cada cláusula y con el prefijo.**

## 4. Lo que queda: la elección común

Ya estaba demostrado que una camarilla que cubre todos los pasos es un camino (`chain_of_clique`) y que todo
camino es una solución (`path_is_solution`). Falta pasar de *"cada par tiene su fila testigo"* a *"existe
una elección común"*: un nodo por paso —filas incluidas— que se posean todos entre sí y pasen por el valor
vivo. Es la extensión de la camarilla, ya sin distinguir anchuras de cláusula. Aquí fallaron antes las
reglas locales de tres nodos (ternas, Helly-3); la diferencia es que ahora sabemos que **las filas, como
nodos, son las que tienen que encajar**, y que cada fila viva ya es una solución local consistente con el
prefijo.

---

## 5. Estado general de la demostración del veredicto (actualizado)

### Demostrado sin ninguna hipótesis

| resultado | módulo |
|---|---|
| **toda respuesta es correcta** (UNSAT sin modelo; SAT con certificado comprobado) | `Answer` |
| a una fórmula satisfacible nunca le responde UNSAT | `Answer` |
| la máquina contiene todas las soluciones, completas y **parciales** | `ConservationImproves`, `ConservationPrefix` |
| un camino que cumple los requisitos es la rama de su asignación | `ConservationPrefix` |
| **no hay préstamo entre ramas en las uniones de la máquina** | `RunNoBorrow` |
| **todo camino de un estado del lector es una solución real** | `LiveSolution.path_is_solution` |
| un estado válido con un mapa por paso es un camino | `PinExtends.chain_of_ids` |
| lo decidido abajo decide negación, fusión y cláusula | `PinUp.decided_off_var` |
| **un valor vivo nunca rompe una cláusula decidida** | `LiveSolution.decided_clause_holds` |
| **el review contiene la propagación unitaria** | `LiveSolution.unit_forced` |
| **toda fila viva lleva el prefijo; todo par tiene una fila testigo** | `LiveSolution.row_bit_prefix`, `entry_witness` |
| fijar a la vez = en secuencia; un envío = sus pasos; revisar tras cada unión no cambia nada | `SeqPin`, `WeakPairs` |

### La única dirección que falta

*Si la máquina termina con un estado válido, la fórmula es satisfacible* (equivalente: nunca responde "no
sé"). Las cuatro rutas formalizadas (lectura, exactitud, construcción, pares) desembocan en el mismo
núcleo, que hoy está dividido así:

```
LiveOnPath: un valor vivo está en una solución real
│
├─ (A) cláusulas decididas satisfechas                 ✔ demostrado
├─ (B1) propagación unitaria                           ✔ demostrado
├─ filas vivas = soluciones locales con el prefijo     ✔ demostrado (row_bit_prefix)
├─ todo par tiene fila testigo                         ✔ demostrado (entry_witness)
└─ elección común (extensión de la camarilla)          ✘ abierto — el núcleo
```

### Lo medido del núcleo, sin un solo fallo

| hipótesis | casos |
|---|---|
| `LivePinUp` (de abajo arriba, todo candidato vivo) | 5 familias + 240 fórmulas aleatorias |
| `PinExtends` (orden aleatorio) | 27.505 comprobaciones de paso |
| exactitud tras fijar (`PairPinExact`) | 21.709 fijaciones; 10,9 M entradas |
| `EntryPin` | 11.858 entradas (K4, paridad, prisma) |
| `RunPaths` / `SideCover` | 615.911 / 33,2 M entradas |

### Descartado por medición

Empalme de caminos, construcción voraz sin review, regla de ternas a través del valor vivo, Helly-3, la
versión fuerte de `SideCover`, que cada rama explique todas sus entradas. Ninguna regla sobre pocos nodos
basta.

### Caminos que faltan, por coste

1. **`SupportSplit` restringido a la ejecución** (mecánico): para enchufar `NoBorrow` en la ruta de
   construcción.
2. **Los débiles no cambian nada** (mecánico): extender `OwnedCompatible`, `ParentInv`, `LitInv` a Improves.
3. **El núcleo: la elección común**. Propuesta para el siguiente paso: tratar las filas como nodos y
   construir la camarilla **de abajo arriba igual que tu lector**, aprovechando que en el mapa todas las
   variables van antes que todas las cláusulas: cuando el lector llega a las filas, las variables ya están
   decididas y cada fila queda determinada (`decided_off_var`). La pregunta se concentra entonces en las
   variables: que un valor vivo, con el prefijo, deje en cada cláusula al menos una fila viva compatible
   con **todas** las elecciones posteriores.
