# Verificación para el Autor v169: tu filtro deja de ser hipótesis y pasa a ser el test que demuestra el veredicto

Ricardo, soy Claude (Opus 5). Este informe sigue a v168 y cierra una etapa que cambia el **estatus** del
problema abierto, no solo su tamaño. Rama `spaik`, módulo `ImprovesCima.lean`. Build de `AbsSat`
(232 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`.

## 0. Resumen

* **Tu filtro del triángulo no puede dispararse en las cuatro primeras elecciones.** Tres salen de la
  consistencia de pares; la cuarta sale de que **la familia es un cono** y su cima no pide nada.
* **El cono ya no es hipótesis**: una familia viva nombra una cima real, y la cima de un lado es única.
  Queda descargado para los lados de la máquina.
* **Y lo principal**: tu filtro es un **cálculo**, no un enunciado. Ahora está en Lean como un `Bool`, y
  de él sale `sat_of_filterCheck`: **si el filtro pasa sobre la unión filtrada, la fórmula es
  satisfacible, sin hipótesis de ninguna clase.** El veredicto SAT queda demostrado **por ejecución**,
  fórmula a fórmula.
* Medido con la propia definición de Lean: **3.071 uniones reales, 3.071 veces `true`, ningún `false`**.

## 1. Dónde estábamos

Tras v168 el veredicto colgaba de una sola cosa, `TriOk`: que al bajar paso a paso dentro de una
familia, eligiendo un nodo por paso, los nodos comunes a todo lo elegido no se agoten. Es exactamente tu
`filter_triangle_nodes!` leído como hipótesis.

## 2. Las cuatro primeras rondas son gratis

Lo primero fue ver hasta dónde llega lo que ya tenemos.

| ronda | por qué no puede dispararse | pieza |
|---|---|---|
| ninguna elegida | el estado está vivo, la línea no está vacía | `commonWith_small` |
| una elegida | su propia cobertura le da compañero en cada paso | `Sup.cov` |
| dos elegidas | se poseen mutuamente, y la revisión agresiva les da dueño común | `Sup.agg` |
| **tres elegidas** | **una de las tres es siempre la cima, y la cima es gratis** | `triOk_of_cone` |

La cuarta ronda merece explicación, porque es el aporte nuevo.

**La familia tiene un solo nodo en su último paso: su propia cima.** Un lado es un envío, y un envío
tiene exactamente un nodo en el paso que acaba de crear (`sent_top`). De ahí salen tres cosas en
cascada:

1. Como arriba solo hay un nodo, **la primera elección es siempre la cima** — no hay otra cosa que
   elegir (`triPicks_cone`).
2. Como es la primera, **está en todas las listas posteriores**.
3. Y como toda la familia cuelga de ella, **se lleva bien con cualquier candidato, gratis**
   (`coneAt_of_topSingle`).

De los tres nodos que deben ponerse de acuerdo en la cuarta ronda, uno no cuesta nada. Quedan dos, y dos
ya los daba la revisión agresiva. **El contenido empieza en la quinta.**

Y hay una lectura más limpia todavía (`commonWith_drop_cone`): **la cima nunca quita un candidato**. En
la ronda `n` el filtro cree intersecar sobre `n` nodos, pero está intersecando sobre `n−1`. Ahí está la
razón exacta de que el umbral caiga en la quinta y no en la cuarta.

## 3. El cono ya no es hipótesis

Para usar el cono hacía falta saber que la cima que produce la regla es la cima **de un lado**, y no hay
que suponerlo:

> Una familia viva conserva al menos una entrada → esa entrada la lleva un lado → **un lado es un
> envío** (`side_is_send`) → y un envío tiene un solo nodo en su paso nuevo (`sent_top`).

Eso es `top_of_famFix`. Con él, `famTopSingle_sides` descarga la parte estructural para los lados
reales de la máquina: el cono es un **teorema**, no una hipótesis.

Las hipótesis de familia (`FamHasChain`, `FamPairwise`, `FamTriOk`, …) pasan a hablar del estado
concreto de la máquina, y la cima se nombra por **pertenecer a la última línea** en vez de por su paso.
Ese cambio pequeño es el que hace el test finito: las cimas candidatas son una lista.

## 4. Tu filtro, ejecutándose

```
triOkB F      -- la bajada: una pasada por paso
famTriOkB     -- eso, para cada cima de la última línea cuya familia esté viva
```

Y encima:

> **`sat_of_filterCheck`** — si `famTriOkB` devuelve `true` sobre la unión filtrada, la fórmula es
> satisfacible. **Sin ninguna hipótesis**: ni sobre los lados, ni sobre las tablas, ni sobre nada.

Esto es lo que cambia el estatus. Hasta ahora teníamos "el veredicto es correcto **si** se cumple X".
Ahora tenemos: **cada ejecución en la que el filtro no salta lleva su propia demostración**. No es una
conjetura respaldada por medidas; son teoremas, uno por ejecución.

También está `sat_of_filterCheckCone`: el mismo veredicto **saltándose las cuatro primeras rondas** de
cada bajada, porque el cono ya las paga. Ahí es donde el trabajo de la sección 2 se convierte en ahorro
de cómputo.

## 5. Lo medido

Dos medidas distintas, con permiso tuyo, y las dos sobre la **unión fijada ordinaria**, que es el objeto
más duro que el que menciona el teorema (la familia es mayor y menos coherente que con la regla ya
aplicada).

**La bajada, con tablas rápidas** (sonda `trifam`, fórmulas aleatorias):

| tanda | familias | bajadas | intersección vacía |
|---|---|---|---|
| semillas 1–3 | 2.802 | 35.208 | **0** |
| semillas 11–15 | 69.173 | 1.111.706 | **0** |
| **total** | **71.975** | **1.146.914** | **0** |

**La definición de Lean, ejecutándose tal cual** (sonda `bcheck`, sin reimplementar nada):

| semilla | uniones reales | `famTriOkB` = `true` | `false` |
|---|---|---|---|
| 1 | 686 | 686 | **0** |
| 2 | 623 | 623 | **0** |
| 3 | 679 | 679 | **0** |
| 4 | 523 | 523 | **0** |
| 5 | 560 | 560 | **0** |

Esta segunda medida importa por una razón concreta: un test que siempre devolviera `false` haría el
teorema cierto e inútil. **3.071 de 3.071** dice que no lo es.

## 6. Lo que queda, dicho sin adornos

Me preguntaste si el problema no era la consistencia de tríos sino que después vendrían cuartetos,
quintetos, etc. **Tienes razón, y conviene dejarlo escrito.**

En la ronda `n` hay que poner de acuerdo a `n−1` nodos, y `n` corre hasta el número de pasos. Eso es
**consistencia global**. La revisión agresiva da consistencia de pares, y entre pares y global no hay
escalera que suba sola — si la hubiera, esto no sería difícil. Además, es **el mismo muro que este
proyecto ya bautizó** en su día (`CommonOwner` / `NoDeadEnd`): hemos vuelto a él por un camino mucho más
corto, pero es el mismo.

Lo que cambia es **dónde queda la pregunta**:

| antes | ahora |
|---|---|
| "demuestra la consistencia de orden `k`" | "¿puede la bajada codiciosa atascarse teniendo salida?" |
| enunciado abierto sobre la máquina | pregunta sobre el comportamiento de un algoritmo |
| veredicto condicional | **veredicto demostrado en cada ejecución que pasa el test** |

Porque el filtro es polinómico y la máquina lo ejecuta, no hace falta demostrar la consistencia de orden
`k` a priori. Basta con que el test no se equivoque, y equivocarse aquí significa una cosa muy concreta:
que la bajada elija mal y se quede sin salida **teniendo** salida. Sobre eso es sobre lo que hablan los
1,1 millones de bajadas.

## 7. Dos callejones que cerré por el camino

Los dejo escritos para que no parezcan posibilidades abiertas:

* **La cláusula `par` del soporte no da más que el cono.** Da un padre del último elegido relacionado
  con él y con **uno** que elijas; con la cima, tres. Mismo umbral, por vía independiente. Que dos
  mecanismos distintos se paren en el mismo sitio sugiere que el cuatro es la frontera de lo local, no
  un límite de mi técnica.
* **No se puede pedir menos que todos los pares.** Miré si una cadena podría construirse solo con
  eslabones consecutivos: no. `ChainG` exige `PairwiseOwned` entero, y con razón — un camino real sí
  tiene todos sus nodos poseyéndose entre sí.
* **El descenso por el lado, que propuse yo, no funciona.** Los pares de la familia viven *dentro* del
  lado, no al revés; bajar no devuelve el testigo que hace falta. Lo que pagó fue el cono.

## 8. Commits

`0c2481d` (las tres primeras elecciones), `f8a3b64` (la sonda de la bajada), `c7f1711` (el cono paga la
cuarta), `f50b07d` (la fontanería y la cima que no pide nada), `ad80cfd` (el filtro como test y el
veredicto por ejecución).
