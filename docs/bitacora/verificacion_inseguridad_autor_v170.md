# Verificación para el Autor v170: la cadena se arrastra, no se reconstruye — y las dos rutas resultan ser una

Ricardo, soy Claude (Opus 5). Este informe sigue a v169 y recoge una etapa que **cambió el camino
principal**. Rama `spaik`, módulo `ImprovesCima.lean`. Build de `AbsSat` (232 jobs), sin `sorry`,
axiomas `[propext, Quot.sound]`.

## 0. Resumen

* Tu observación —"la máquina no computa 3‑SAT, construye el conjunto de soluciones; busquemos
  mecanismos que esquiven la consistencia de tríos"— tenía una consecuencia técnica que yo no había
  visto: **la ruta C ya es la ruta de arrastrar el camino**, y su paso difícil estaba demostrado desde
  v168. El filtro del triángulo no era el camino principal. Era un desvío mío.
* Pedía yo de más en tres sitios distintos, y los tres se han apretado: **por pares** en vez de un lado
  para todo el soporte; **la cadena es su propio certificado**; y **la pasada arrastra las cadenas**,
  así que la obligación pierde el cuantificador sobre estrechamientos.
* **Una cadena es un soporte** (`sup_of_chainSound`) y **una cadena de una familia ya es una cadena de
  su lado** (`chainSound_side_of_famFix`). Ninguna de las dos estaba escrita.
* Resultado: **las dos rutas al veredicto son la misma frase**. De las tres condiciones que pedía el
  descenso, dos salen gratis de una cadena de la familia. Queda una, concreta: las fijaciones.

## 1. El desvío, y por qué lo era

Tras v169 el veredicto colgaba de tu filtro del triángulo, y demostrarlo pedía consistencia de orden
`k` creciente. Tú señalaste que ese no era el objetivo de la máquina. Al levantar el terreno encontré
esto:

> **`ValidWitAt`** (ruta C, desde v165): *un estado de la ejecución que sigue vivo bajo fijaciones tiene
> un camino parcial real hasta su clave, por las fijaciones.*

Eso **es** arrastrar el certificado línea a línea. No reconstruye una cadena a partir de información de
pares: la hereda. Y su paso de la unión —el difícil— ya estaba demostrado **sin hipótesis** para
`ImprovesCima`: es `topValid_cima`, y la regla de la cima existe precisamente para eso.

Lo que faltaba de esa ruta era el paso de fijar, `SendPinAt`, y ahí es donde se ha trabajado.

## 2. Pedía de más, tres veces

### 2.1 Un lado para todo el soporte → por pares

El test de la regla, `cimaOk`, es **existencial sobre las cimas**: cada par puede nombrar la suya. El
"un solo lado para todo el soporte" venía de cómo lo demostré yo (`carriedR_of_side` fija una cima y
tira de ella), no de lo que el descenso necesita.

`carriedR_of_pair` deja que **cada par nombre su lado y su sub‑soporte**. La forma antigua queda como
caso particular, escrito y demostrado, para que conste que era yo pidiendo de más.

### 2.2 El sub‑soporte hay que calcularlo → la cadena ya lo es

Buscando qué sub‑soporte exhibir sin caer en circularidad salió una pieza que este proyecto no tenía:

> **`sup_of_chainSound` — una cadena sana *es* un soporte.**

Y sale de su propia forma, sin calcular nada: la cobertura y la agregación son el nodo de la cadena en
ese paso, el padre y el hijo son sus vecinos, los enlaces son los suyos. Las once cláusulas de `Sup`,
todas de la misma cadena.

Y su compañera, `restTest_of_chain`: **una cadena sana en un lado pasa el test de restricción de su
propia cima**. La cima de la que habla el test no hay que buscarla — es el nodo de la cadena en el
último paso. La cadena es el certificado de su lado.

### 2.3 En cualquier estrechamiento → donde la pasada puede estar

El módulo tenía dos hipótesis gemelas y una estaba floja:

| | cómo pedía la regla |
|---|---|
| `TestC` (cadenas) | en cada estrechamiento **que aún conserva la cadena** |
| `TestR` (soportes) | en cada estrechamiento que conserva el soporte — y nada más |

La pasada conserva las cadenas por sí sola (`ChainSound_prunePair` en cada paso), pero la inducción del
soporte **tiraba esa información**. `TestRC` la conserva: pide la regla solo donde la pasada puede
estar. No es una hipótesis nueva; es dejar de perder lo que ya se sabía.

Enhebrado hasta arriba —`AOk_pruneNodeC`, `AOk_pruneSweepC`, `AOk_reviewCimaFuelC`,
`AOk_filterAllCimaC`—: **soporte y cadenas sobreviven juntos a las fijaciones y al review entero.**

## 3. La obligación, en su tamaño justo

```
SideChainG :  cada par del soporte está sobre una cadena que es
              sana en G, sana en un lado, y compatible con las fijaciones
```

Ni un cuantificador sobre estrechamientos. Compárese con lo que había al empezar la etapa —"un solo
lado que lleve el soporte entero, en cualquier estrechamiento"— y se ve la holgura que se ha quitado.

## 4. Y de las tres condiciones, dos son gratis

`chainSound_transfer` (abstracto): una cadena se traslada a cualquier estado que tenga sus pares, sus
enlaces de padre y sus nodos como dueños globales. Es la versión para cadenas de `sup_transfer`.

Con él, `chainSound_side_of_famFix`: **una cadena de una familia ya es una cadena de su lado.** Los tres
ingredientes estaban repartidos por el repositorio y encajan sin holgura:

| lo que hace falta | de dónde sale |
|---|---|
| sus pares son del lado | `side_of_famFix` |
| sus enlaces son del lado | la tercera componente de lo mismo |
| sus nodos son dueños globales allí | `sent_ownGow` |

Y entonces `cimaChain_of_famChain`: una cadena de la familia sirve al descenso. Sana en `G` porque la
familia es un estrechamiento de `G`; sana en un lado por lo anterior.

## 5. Las dos rutas son una

Esto es lo que más me importa de la etapa:

| ruta | lo que pide |
|---|---|
| directa (`sat_of_famHasChain`) | **la familia contiene una cadena** |
| descenso (ruta C, `SideChainG`) | **la familia contiene una cadena** por cada par, más las fijaciones |

Es la misma frase. Todo el veredicto de `ImprovesCima` descansa sobre ella, y se llega por dos caminos
independientes. Eso no la demuestra — pero explica por qué el muro llevaba años reapareciendo con
nombres distintos (`SpcStable`, `PairChain`, `JoinSplit`, `CommonOwner`, `NoDeadEnd`, `TriOk`): no eran
obstáculos distintos, era el mismo visto desde sitios distintos.

## 6. Lo que queda

**Las fijaciones.** La familia se calcula sobre `G` sin fijar, así que su cadena puede violar un
requisito del hijo. Es el único resto del descenso, y es concreto: no es "consistencia de orden k", es
"la cadena de la familia respeta lo que se ha fijado".

Ahí encaja exactamente la **regla del envío por familias** que propuse en la exploración previa:

> Antes de enviar `G` al hijo `d`, conservar solo lo que lleva alguna familia que siga viva al aplicar
> los requisitos de `d`.

No pierde soluciones (una cadena real que continúa hacia `d` cumple sus requisitos, y su familia
sobrevive porque la cadena está dentro), es polinómica (una familia por cima contra los requisitos de un
hijo), y haría que la condición que falta se cumpliese **por construcción** en vez de tener que
demostrarse a posteriori.

## 7. Nota de método

El guardián de axiomas cazó una fuga de `Classical.choice` en la cláusula de enlaces de
`sup_of_chainSound` —un `omega` en un contexto con una ecuación de pasos— y quedó sustituida por el paso
explícito. Lo anoto porque es justo para lo que están esos guardianes: sin ellos habría entrado sin que
nadie lo viera, y el resultado habría sido más débil de lo que aparenta.

## 8. Commits

`971c4b7` (por pares, y la cadena como soporte), `798ce86` (la cadena, certificado de su lado),
`d9714c9` (la pasada arrastra las cadenas; `SideChainG`), `2f018e4` (dos de las tres condiciones, gratis).
