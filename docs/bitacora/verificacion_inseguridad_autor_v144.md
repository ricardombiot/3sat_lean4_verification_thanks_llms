# Verificación para el Autor v144: la manera del lector — el veredicto bajo una sola hipótesis local

Ricardo, soy Claude (Opus 5). Este informe recoge lo hecho tras v143. El resultado principal es que
**el veredicto completo de la máquina depende ya de una sola hipótesis, pequeña y local**, sacada de tu
lector: *en un estado válido del lector, cada paso admite alguna fijación que lo deja válido*. Ya no hacen
falta ni la exactitud de las tablas ni `GhostsLine`.

Rama `spaik`, build de `AbsSat` (208 jobs), sin `sorry`, `[propext, Quot.sound]`. Commits `6ab188d`,
`f9b85db`, `164a9f1`, `afb55cc`, `d4ccd5a`.

---

## 1. El envío, paso a paso (`WeakPairs.lean`)

Un envío filtra con requisitos débiles y fijaciones y después revisa. Demostrado (`full_seq`) que equivale
a hacerlo paso a paso: primero el review, después cada requisito débil con su review y después cada
fijación con su review. Con eso, `GhostsLine` se redujo a dos enunciados de un solo paso y solo sobre
pares (`PairPinExact`, `WeakPairExact`); el nivel de nodos de los dos quedó demostrado.

## 2. Los requisitos débiles no cambian nada (medido)

Tu observación: los débiles fueron una optimización. La sonda `weakcmp` lo confirma: con y sin ellos, las
tablas son **idénticas**.

| familia | envíos válidos iguales | estados de la ejecución iguales |
|---|---|---|
| K4 | 93 / 93 | 108 / 108 |
| paridad | 127 / 127 | 81 / 81 |
| prisma | 165 / 165 | 164 / 164 |
| K3,3 | 145 / 145 | 164 / 164 |

Solo cambian el coste (hasta −16 %), no el resultado. La mitad de la prueba ya existía
(`idContradicts_of_weak_removed`: lo que quitan contradice una fijación del mismo envío). La otra mitad,
`agree_of_fixes`, necesita extender tres invariantes a la máquina Improves. Queda pendiente, pero con §4
deja de ser necesaria.

## 3. Dos vías descartadas por medición

* **El empalme** (`splice`): unir dos caminos por el nodo del medio **no** da siempre un camino (en
  paridad, 23.506 entradas con ninguno de los empalmes probados válido). Pero confirmó `PairPinExact` en
  10,9 M entradas: el review conserva exactamente las que están en un camino real.
* **La construcción voraz sin review** (`Greedy.lean`, `greedy`): elegir nodo a nodo, cada uno poseído
  por todos los anteriores, **se atasca** en algunas ramas (19 entradas en K4, 219 en paridad, 945 en
  prisma de las medidas). Se conserva el lema `chain_of_clique`: un conjunto de nodos que se poseen entre
  sí y cubre todos los pasos **es** un camino.

## 4. La manera del lector (`PinExtends.lean`)

Tu lector no elige nodos: **fija un paso, revisa y sigue**. Con esa idea:

**Demostrado sin hipótesis** (`chain_of_ids`): *un estado revisado y válido en el que cada paso tiene un
solo nodo de mapa es un camino.* El mapa del padre también queda fijado (enlace de padre y `PMP`), así que
en cada paso hay un único nodo, todos se poseen entre sí y forman un camino (`chain_of_clique`).

**La hipótesis, `PinExtends`**: en todo estado válido al que llega el lector desde un estado final, cada
paso admite alguna fijación que lo deja válido.

**Demostrado bajo `PinExtends` sola:**

| teorema | enunciado |
|---|---|
| `chain_of_readFrom` | todo estado válido del lector contiene un camino (fijarlo todo, y aplicar `chain_of_ids`) |
| `verdict_iff_pinExtends` | la máquina tiene un estado final válido ⟺ φ es satisfacible |
| `answer_unsat_px` | a una fórmula insatisfacible responde UNSAT |
| `answer_ne_unknown_px` | nunca responde "no sé": el lector no se atasca y su certificado pasa la comprobación |

**Medido** (`pinext`: recorridos de fijación al azar desde el estado final, comprobando en cada estado
todos los pasos):

| familia | recorridos completos | comprobaciones de paso | fallos |
|---|---|---|---|
| K4 | 5 / 5 | 4.500 | **0** |
| paridad | 5 / 5 | 3.645 | **0** |
| prisma, K3,3, aleatorias | en curso | | |

## 5. Cómo queda todo

| afirmación | hipótesis |
|---|---|
| toda respuesta (UNSAT, o SAT con certificado) es correcta | **ninguna** |
| un estado válido con un mapa por paso es un camino | **ninguna** |
| fijar a la vez = fijar en secuencia; débiles y fijaciones paso a paso | **ninguna** |
| la máquina decide; nunca responde "no sé" | **`PinExtends`** |

`PinExtends` ya no habla de tablas exactas ni de caminos: habla **solo de validez**, un paso cada vez.

## 6. Cómo seguir dividiéndola

Ver la conversación asociada; en resumen, cuatro cortes posibles:

1. **Por clase de paso.** Los pasos con un solo nodo de mapa (fusiones) cumplen `PinExtends` gratis:
   fijar el único nodo no cambia nada. Quedan los pasos de variable y negación (dos valores) y los de
   cláusula (hasta 7 filas).
2. **Por orden.** La prueba solo necesita fijar los pasos en **un** orden, no en cualquiera. Con el orden
   de abajo arriba (0, 1, 2…), que es el mismo en que tu máquina construye, basta: *con los pasos 0…l−1
   fijados y el estado válido, el paso l admite una fijación válida*.
3. **Por elección.** En vez de "alguna fijación", ver qué candidatos fallan y por qué.
4. **Por causa de invalidez.** Si una fijación invalida el estado, algún paso se queda sin owners: separar
   si es el propio paso, uno vecino o uno lejano.
