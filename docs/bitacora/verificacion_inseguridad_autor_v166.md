# Verificación para el Autor v166: `ImprovesCima`, la máquina con la regla de la cima

Ricardo, soy Claude (Opus 5). Este informe explica la máquina nueva, por qué nace de `Improves` y qué
falta para que su veredicto quede demostrado. Rama `spaik`, módulo `ImprovesCima.lean`. Build de
`AbsSat` (232 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`.

## 1. De dónde viene

Tras v165, el veredicto de `Improves` depende de una sola cosa: que la validez no se tome prestada en
una unión. Eso quedó reducido, paso a paso y sin hipótesis nuevas, a que **los testigos que da el review
estén en la tabla del lado que nombra la cadena del par** (`ChainClosureAt`).

Lo medimos mucho y nunca falla:

| sonda | qué comprueba | comprobaciones | fallos |
|---|---|---|---|
| `chainside2` | toda cadena de dueños comunes acaba en un lado que lleva el par | 13,4 M pares | 0 |
| `history` | el par está en la tabla de cada línea que nombra la cadena | 45,1 M niveles | 0 |
| `chainfam` | las cinco reglas de cierre de la familia que nombra una cima | 2,8 M pares | 0 |
| `ownsupport` | el soporte propio de cada lado con la cima viva | 52.506 lados | 0 |

Pero nada en el review actual lo **obliga**. Por eso la máquina nueva.

## 2. La idea de `ImprovesCima`

Es `Improves` con una pasada más dentro del review, que se ejecuta en la unión por clave, donde los
lados que la formaron aún están a mano:

> **Regla de la cima.** Se conserva una relación a → b solo si, para **toda** cima t que alcance una
> cadena de dueños comunes de a y b, el lado de t lleva a → b en su propia tabla, en ambos sentidos.

Tres detalles del diseño:

* **Los IDs nombran el lado.** Un nodo es (nodo del mapa, nodo padre), así que la cima de un lado,
  `⟨p, clave⟩`, solo existe en ese lado. La cadena, leída por sus IDs, dice de qué lado habla.
* **La cadena se lee por los padres**, no por los hijos: un review solo puede quitar padres, así que la
  regla se comporta bien cuando el estado mengua.
* **Se mira la tabla del lado**, no la de la unión. Esa es la información que la unión pierde al fundir,
  y la única forma de recuperarla es mirarla cuando todavía está.

El coste es polinómico: por cada par, por cada cima alcanzada y por cada paso, un recorrido de nodos y
enlaces. Es más cara que la revisión agresiva, del orden de lo que ya ejecuta la sonda `chainfam`.

## 3. Lo demostrado

* **`keeps_cimaSweep`**: la pasada solo quita (`Keeps`, es decir, `Pruned` más las condiciones que el
  review necesita).
* **`ChainSound_cimaSweep`**: **no pierde soluciones.** Si una cadena real tiene sus pares llevados por
  los lados de las cimas que alcanza, la pasada nunca la separa: los pares de la cadena no entran nunca
  en la rama que borra, y lo que se borra fuera de ella no la toca.

## 4. Lo que falta, y por qué basta

Queda una sola pieza del núcleo:

> **`KeepsSupports`**: un soporte cuyos pares llevan los lados de las cimas que alcanza sobrevive a la
> pasada.

Con ella se enchufa `AOk_filterAllAgg` (un soporte sobrevive a fijar y revisar), y entonces la cadena ya
demostrada se cierra sola:

| pieza | estado |
|---|---|
| `ChainClosureAt` ⇒ `TopValidAt` | demostrado (v165) |
| `TopValidAt` ⇒ `ValidSideAt` | demostrado |
| `ValidSideAt` ⇒ invariante de validez hereditaria ⇒ veredicto | demostrado |
| la regla obliga a `ChainClosureAt` | con `KeepsSupports` |

Es decir: demostrando `KeepsSupports` (y rehaciendo, con la plantilla del review agresivo, el punto fijo
y la conservación a nivel de máquina), **el veredicto de `ImprovesCima` queda demostrado**, sin
hipótesis y sin necesidad de que las tablas sean exactas.

## 5. Lo que esto significa, y lo que no

* Lo que quedaría demostrado es el veredicto de **`ImprovesCima`**, la máquina con la regla. De
  `Improves` seguiríamos teniendo lo de siempre: no pierde soluciones, su veredicto leído con
  certificado nunca es erróneo, y las medidas, que no fallan nunca, pero no una demostración.
* La regla no cambia ningún resultado en lo medido: en esas familias nunca borra nada, porque la
  condición ya se cumplía.
* Hay que pagar dos cosas: la máquina conserva los lados de la última unión, y el review deja de ser
  función de un solo estado.

## 6. Plan

1. **`KeepsSupports`**, la pieza que falta del núcleo.
2. **Punto fijo** de la pasada dentro del review, con la plantilla de `AggFixpoint`.
3. **Conservación a nivel de máquina**: que la máquina completa con la regla siga sin perder soluciones,
   apoyándose en `ChainSound_cimaSweep` y en la completitud de las ramas.
4. **Enchufar la ruta C** y cerrar `sat_of_chainClosure` para `ImprovesCima`.

Commits de esta etapa: `5b9da34` (la familia que nombra la cima), `ca35928` (`tops_unique`),
`2414927` (`ImprovesCima`).
