# Verificación para el Autor v116: la validez del veredicto de *Improves*, reducida a una sola fijación

Ricardo, soy Claude (Opus 5). En v115 quedó demostrado que la máquina *Improves*, con tu review
agresivo, no pierde soluciones. Faltaba la otra mitad: que si la máquina dice SAT, la fórmula lo sea.
Este tramo reduce esa mitad a **una única obligación sobre una fijación**, apoyándose en tu Reader, y
mide esa obligación.

Todo en la rama `spaik`, en el build de `AbsSat` y sus ejecutables (263 jobs), sin `sorry`, en
`[propext, Quot.sound]`.

---

## 1. La idea: el Reader como demostración

Una demostración directa de "estado final válido ⇒ hay solución" chocaría con Helly: tu barrido
garantiza que dos nodos compatibles tienen un owner común en cada paso, pero no que *m* nodos lo
tengan a la vez.

Tu Reader lo evita. No elige todos los nodos de golpe: **fija uno, hace el review y vuelve a
elegir**. La limpieza tras cada fijación resuelve paso a paso lo que un Helly estático tendría que
garantizar de una vez. Así que la validez se puede enunciar con el Reader y sin hablar de cadenas:

1. **Nadie se atasca**: en cada estado que visita el lector, alguna fijación deja el grafo válido.
2. **El final es correcto**: cuando no queda nada que elegir, el estado denota un camino, y ese
   camino deletrea un modelo de φ.

La pieza 2 ya estaba demostrada para el review base (`Reader.Inhabited_of_pickSome_machine`, de
tramos anteriores). Lo nuevo es llevarla al review agresivo y a la máquina *Improves*.

## 2. Lo demostrado

### `ReaderAgg.lean`: el lector con el review agresivo

- **`reviewAggFuel_form`**: todo resultado de `reviewAgg` es un resultado del review base. Para
  conseguirlo he hecho un ajuste mínimo en `reviewAgg`: cuando el barrido no elimina nada, devuelve el
  punto fijo del review base en lugar de la salida del barrido, que tiene la misma medida. Los
  veredictos no cambian (las aleatorias y los Tseitin de la sonda coinciden con el oráculo).
- **`keeps_aggSweep`**: el barrido solo estrecha tablas y elimina nodos, así que conserva los
  invariantes del lector: owners globales que son nodos, padres que son nodos e ids sin duplicados.
- **`readable_of_readableAgg`**: por lo anterior, un estado fijado con el review agresivo es un
  estado legible del lector base, y todo lo estático del lector base le vale.
- **`Inhabited_of_pickSomeAgg`**: el bucle de lectura con el review agresivo. Un estado válido
  denota un camino en cuanto, **en cada estado que el lector visita desde él** (`ReadFrom`), alguna
  fijación lo deja válido (`PickSomeAgg`). La hipótesis se pide solo en los estados del lector, no en
  todos los estados posibles.

### `ReaderAggRun.lean`: sobre la máquina *Improves*

- **`MInv`**: los invariantes del lector más lo que necesita la decodificación (las tablas de owners
  respetan los requisitos, los requisitos apuntan hacia atrás y los nodos están en el mapa).
- **`MInv_sent`, `MInv_join`, `MInv_initSeed`**: cada operación del driver lo conserva. El filtro
  débil y el review agresivo solo estrechan; `addNode` y `join` usan los lemas existentes.
- **`pureRunW_state`**: todo estado de la línea final de `pureRunW` cumple `MInv`, está en el último
  paso y es válido.
- **`sat_of_denot_final`**: un camino por un estado final deletrea un modelo de φ. Es la
  decodificación de la máquina base, reescrita sobre `MInv` en lugar de `MapReachable`, que los estados
  de *Improves* no cumplen.
- **`sat_of_pickSomeAgg`**: **si la máquina *Improves* deja un estado final, un review agresivo lo
  mantiene válido y el lector encuentra siempre una fijación válida, entonces φ es satisfacible.**

Resultado: **la validez del veredicto SAT de *Improves* queda reducida a `PickSomeAgg` en los estados
del lector.** Con la conservación de v115, la máquina decidiría 3SAT bajo esa única hipótesis.

## 3. Lo medido

`lake exe join-borrow readagg`: ejecuta la máquina *Improves* real, compara el veredicto con el
oráculo de fuerza bruta y, desde cada estado final, lanza el lector de `ReaderAgg` (fijaciones con el
review agresivo, primera fijación válida, cinco órdenes distintos). **Atasco** = ninguna fijación
válida en ningún paso con elección, es decir, `PickSomeAgg` falla.
Con `all`, el lector arranca desde **todos los estados de todas las líneas**, no solo los finales.

| familia | fórmulas | veredictos erróneos | lecturas | atascos | respuestas erróneas |
|---|---|---|---|---|---|
| aleatorias, 6–8 variables (semillas 1001, 7777, 31337) | 60 (55 SAT) | 0 | 275 | **0** | 0 |
| aleatorias, 8–10 variables (semillas 90210, 4242) | 30 (26 SAT) | 0 | 78 | **0** | 0 |
| Tseitin con paridad par (SAT): K4, K3,3, prisma, cubo, Petersen | 5 | 0 | 25 | **0** | 0 |
| 3-coloración de K4 menos una arista (SAT) | 1 | 0 | 5 | **0** | 0 |
| 3-coloración de K4 (UNSAT) y Tseitin K4 impar (UNSAT) | 2 | 0 | — | — | — |
| `all`: Tseitin K4 impar, Tseitin K4 par, gadget `par_k3`, `top_phantom`, K4 con 3 colores | 5 | 0 | 703 | **0** | 0 |
| gadgets de paridad `p2` | 13 | *pendiente* | | | |

Notas:

- Las fórmulas Tseitin pares y las coloraciones las genera `Probes/cnf/gen_readagg.py`. Una Tseitin par
  es la impar con la paridad del primer vértice invertida: misma estructura, pero SAT.
- **La 3-coloración de K4** es el ejemplo clásico en que la consistencia de tríos sobre las variables
  no basta. La máquina *Improves* la decide bien, y el lector no se atasca en ninguno de sus 287
  estados intermedios.
- `invalidPins = 0` en todo lo medido: la primera fijación que prueba el lector siempre ha sido válida.
- Coste: Petersen par tarda unos 430 s (máquina más cinco lecturas); K4 con 3 colores, unos 290 s en
  modo `all`.

## 4. Tu observación sobre el filtro agresivo

Señalaste que tu filtro es más que consistencia de 3: al intersecar las owners de dos nodos
compatibles se pregunta si, en ese paso, **existe un camino parcial común** a los dos.

Es correcto en lo esencial. Los elementos que se intersecan no son valores de variables: son **nodos
de camino**, cada uno con su nodo del mapa, el de su padre y su propia tabla de owners, que es la
huella de los caminos parciales que pasan por él. Formalmente sigue siendo consistencia de caminos,
pero **sobre la estructura de caminos parciales** que construye la máquina, no sobre las variables de
φ. Por eso el contraejemplo de K4 con 3 colores no se traslada, y la medida lo confirma.

El matiz: la comprobación es **por paso**. Garantiza un nodo común en cada paso, pero no que esos
nodos, uno por paso, formen un mismo camino. Que sí lo formen, con el review iterado hasta el punto
fijo, es exactamente `PickSomeAgg`.

## 5. Lo que queda

1. **`AggConsistent`**: tu observación como invariante. Para todo nodo `x`, todo owner válido `w` de
   `x` y todo paso `k`, existe un owner común. Demostrar que el resultado de `reviewAgg` lo cumple:
   cuando el bucle termina, el barrido ya no elimina nada.
2. **La conjetura**: `AggConsistent` más el punto fijo del review ⇒ `PickSomeAgg`. Con ella, la
   validez del veredicto de *Improves* queda cerrada.
3. **Medidas**: completar los gadgets de paridad `p2`, fórmulas mayores y Tseitin de cintura 5–6
   (dodecaedro, Heawood).
