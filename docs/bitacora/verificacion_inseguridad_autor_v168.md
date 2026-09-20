# Verificación para el Autor v168: el veredicto, colgado de tu filtro del triángulo

Ricardo, soy Claude (Opus 5). Este informe sigue a v167 y cubre una etapa que cambió el mapa. Rama
`spaik`, módulo `ImprovesCima.lean`. Build de `AbsSat` (232 jobs), sin `sorry`, axiomas
`[propext, Quot.sound]`.

## 0. Resumen

* **Desaparece la inducción por líneas.** Encontré que ya teníamos demostrado, sin hipótesis, que **una
  cadena sana dentro de un estado de la máquina es un camino real** (`genuine_of_chain`). Con eso el
  veredicto sale directo del último estado: nada de bajar línea a línea, nada de soportes viajando.
* **El veredicto de `ImprovesCima` depende hoy de una sola cosa**, y es **tu filtro del triángulo**:
  que la intersección de los dueños de lo ya elegido no se vacíe dentro de una familia.
* Por el camino corregí un error mío: el triángulo **no** sirve como regla de borrado de pares, ni
  siquiera dentro de la familia. Tu versión no borra pares — comprueba una intersección — y **esa sí**
  es la pieza que faltaba.

## 1. La cadena del veredicto, hoy

Todo lo de abajo está demostrado, sin hipótesis:

| paso | pieza |
|---|---|
| el filtro no dispara en la familia | **`TriOk`** — lo único abierto |
| ⟹ un nodo por paso, poseyéndose dos a dos | `pairwise_triSel`, `triSel_spec` |
| ⟹ cadena enlazada | `isChain_of_pairwise` |
| ⟹ cadena sana | `chainSound_of_pairwise` |
| ⟹ cadena del estado de la máquina | `ChainSound_of_pruned` |
| ⟹ camino real, es decir un modelo | `genuine_of_chain` |
| ⟹ **veredicto de `ImprovesCima`** | `sat_of_famTriOk` |

Y antes de eso, para que exista la familia:

| paso | pieza |
|---|---|
| el estado filtrado tiene una relación viva | `sup_filterAllCima` |
| la regla le da una cima buena, y su familia está viva | `cimaOk_filterAllCima` |
| la familia es un estado de la especie de la máquina | `reviewCimaFuel_form`, `adj_famFix` |

## 2. Lo que cayó en esta etapa

* **El paso de la unión** (`topValid_cima`): con la cima de un lado viva, el envío fijado de ese lado
  sigue vivo. Es `TopValidAt` de la ruta C para la máquina nueva, sin hipótesis. Con tres piezas:
  * `reviewCimaFuel_form` — todo resultado del review nuevo es el review agresivo de un estrechamiento,
    así que la unión filtrada tiene adyacencia y soporte propio;
  * `cert_top_of_top` — si un extremo es la cima de un lado, la regla solo puede certificar esa cima;
  * `sup_of_famSide` — la familia es soporte del envío del lado.
* **La regla para un soporte, arreglada** (`carriedR_of_side`): la hipótesis pedía la cima buena en
  *cualquier* estrechamiento, lo cual es imposible. Ahora la pide solo donde el soporte sigue en pie,
  igual que hace la versión para cadenas. Con ese paréntesis, se descarga sola.
* **La familia es un cono** (`cone_of_famFix`): todo nodo suyo posee la cima y es poseído por ella.
* **De una cadena solo queda la posesión** (`chainSound_of_pairwise`, `isChain_of_pairwise`): los
  enlaces, los dueños globales, la auto-posesión y la raíz salen de los invariantes del estado.

## 3. Tu filtro, en el modelo

`filter_triangle_nodes!` no borra pares: **intersecta los dueños de los nodos pedidos y marca el estado
inválido si la intersección se vacía**. Eso es sano por construcción — un camino real está siempre en
esa intersección — y es justo lo que hacía falta. En el modelo:

* `commonWith F L l` — los nodos del paso `l` que poseen a todo lo elegido y son poseídos por ello;
* `triPicks F n` — la elección de arriba abajo, tomando en cada ronda el primero que esa intersección
  permite;
* `TriOk F` — **el filtro no dispara**: la intersección nunca se vacía;
* `triSel F k` — el nodo elegido en el paso `k`.

**Demostrado**: los elegidos son un nodo por paso y se poseen todos entre sí.

## 4. Tu pregunta: aplicarlo en el `up`

Es sano y conviene, y **no rompe las familias**. Tres razones:

1. **El filtro nunca borra pares; solo invalida un estado.** Un estado invalidado desaparece, no queda
   deformado. Todo lo demostrado habla de un estado dado, así que sigue valiendo.
2. **No pierde soluciones.** Si la intersección se vacía, no hay ningún camino real que cumpla todos los
   requisitos: ese envío no llevaba nada que nos importe.
3. **Empuja en la buena dirección.** Cuantos más estados incoherentes mueran en el `up`, más cerca está
   la máquina de cumplir `TriOk`.

El matiz: aplicarlo en el `up` **no demuestra `TriOk`**. En el `up` compruebas la intersección de los
requisitos del nodo nuevo; `TriOk` pide que la intersección no se vacíe para **cualquier** bajada de
elecciones, paso a paso. Es la misma prueba, hecha en otro sitio y para otro conjunto. Por eso la puse
dentro del cómputo de la familia: ahí es donde la necesita la cadena.

## 5. Un error mío, corregido

En el mensaje anterior te dije que dentro de la familia el triángulo sí servía para borrar pares. Es
falso: si x, y, z se poseen dos a dos y no tienen nodo común, borrar (x, y) puede matar un camino que
pase por x e y; no se sabe cuál de los tres pares sobra. Lo retiro. Tu versión — comprobar la
intersección, no borrar — no tiene ese problema.

## 6. Lo que falta

1. **`TriOk` dentro de una familia**: que tu filtro no dispare mientras se baja eligiendo. Es lo único
   abierto, y es una propiedad que la máquina **computa**, no una hipótesis abstracta.
2. Si quieres, **medirlo** antes de atacarlo: una sonda que ejecute la bajada de elecciones dentro de
   cada familia y cuente cuántas veces se vacía la intersección. No la he lanzado; espero tu palabra.
3. **Enlazar la ejecución**: los estados de `runCima` cumplen los invariantes que piden los teoremas
   (`MInv`, paso actual, última línea) por `Keeps` desde `Improves`; queda escribirlo.

## 7. Lo que esto significa, y lo que no

* Lo que quedaría demostrado es el veredicto de **`ImprovesCima`**, la máquina con la regla de la cima y
  tu filtro. De `Improves` seguimos teniendo lo de siempre.
* Nada de esto acota la generalidad: los enunciados son para toda fórmula y todo estado; la familia se
  elige por estado, no se fija de antemano.
* El coste sigue siendo polinómico: la regla cuesta una revisión por lado en cada unión, y el filtro es
  una intersección por elección.

Commits: `b16a79d`, `362fc82`, `6fad510`, `45c7957`, `3da19b5`, `2b3b6cf`, `2b392a5`, `36d3acd`.
