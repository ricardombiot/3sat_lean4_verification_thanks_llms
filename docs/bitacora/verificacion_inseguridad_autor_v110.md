# Verificación para el Autor v110: una sola prueba de conservación para tres filtros

Ricardo, soy Claude (Opus 5). Este tramo no añade ningún resultado nuevo sobre la máquina: es
estructural. La ley de conservación —«la máquina no pierde soluciones»— estaba demostrada tres veces,
una por filtro, y ahora está demostrada una sola vez, con los tres filtros como instancias. El
criterio que me diste fue dejarla preparada para filtros que **eliminen nodos**, y eso es lo que
marca el diseño.

Todo en el build de `AbsSat` (156 módulos), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. De dónde venía

`ConservationImproves` probaba que la máquina con el filtro débil conserva las soluciones, y
`ConservationPins` repetía el mismo argumento para la poda por pines. Al añadir el filtro condicionado
(v109) escribí una tercera versión, ya genérica. Tres copias de la misma contabilidad: unas 670 líneas
cada una, de las cuales casi todo era el trasiego del driver —líneas, claves, plegados— y no el
argumento matemático.

## 2. Lo hecho, en tres pasos

Cada paso se compiló antes de pasar al siguiente.

- **C1.** Bajar a un módulo nuevo, `ConservationCore`, la parte que no depende del filtro: `ShapeOk` y
  sus lemas, el paso `up` sobre un recorte cualquiera, y los dos lemas del filtro débil que todas las
  instancias usan. Eso invierte la dependencia: la prueba genérica ya no importa a una de sus propias
  instancias.
- **C2.** Reforzar la invariante genérica para que lleve, además del identificador de cada nodo de la
  cadena, **quién es su padre** (`SelParent`), con `mapParent_alongF` alimentando el paso `up`.
- **C3.** Convertir la poda por pines en una instancia más: `Fpin` es el filtro débil seguido de la
  poda, sus dos hipótesis salen de `pruned_pinPrune` y de `ChainSound_pinPrune` con
  `not_idContradicts_sel`, y el driver coincide con el genérico paso a paso (`run_eqP`).

| Módulo | Antes | Ahora |
|---|---|---|
| `ConservationCore` (nuevo) | — | 273 |
| `ConservationFilter` (la prueba genérica) | 699 | 729 |
| `ConservationImproves` | 601 | 205 |
| `ConservationPins` | 921 | 480 |

## 3. Las dos claves técnicas

- **`filterACn 0` es la identidad**, así que `Fsac φ 0` *es* el filtro débil: el mismo término, no uno
  igual. El paso de envío coincide por `rfl`, y la ejecución completa con una inducción de dos líneas
  (`run_eq`). Por eso `ConservationImproves` se derrumbó sin resistencia.
- **El padre es lo que pedía un filtro que elimina nodos.** Un filtro que solo reescribe owners
  globales no puede romper una cadena; uno que borra nodos, sí, salvo que se sepa que la cadena de una
  solución nunca contradice sus propios pines. Y eso solo se demuestra sabiendo también de quién
  desciende cada nodo. Los filtros que no lo necesitan se limitan a arrastrar el dato.

## 4. Qué no cambió

Los once enunciados públicos de los dos módulos conservan su forma exacta y sus cierres de axiomas,
fijados con guardas que fallarían el build si cambiaran. Ningún módulo externo tuvo que tocarse:
`ConservationPins` y `ReviewWorkImproves` no usaban ningún nombre de la contabilidad, y
`PureProofsImproves` solo usaba `pureRunW_ne_nil`.

Añadir un filtro nuevo cuesta ahora una instancia con dos hipótesis, en vez de una copia de 670
líneas.

## 5. Lo que queda pendiente: el camino 1

Sigue abierto lo mismo que antes de este tramo: **última línea no vacía ⇒ satisfacible**. Con el filtro
condicionado puesto, el enunciado natural pasa a ser *si en ese estado todo nodo sin cadena muere por
la regla, entonces un nodo que sobrevive tiene cadena*, y de ahí `L7` decodifica la asignación. Es
decir, la hipótesis abierta se convierte en «la regla es **completa** en este estado».

- **Medido cierto** en `altchain` y en el corpus; **falso en general**: ninguna regla local de tamaño
  fijo refuta fórmulas que exigen anchura de resolución creciente. Solo caben resultados por clase,
  como pasó con Horn.
- **El obstáculo concreto, y es el primer trabajo a hacer:** la red sobre la que propaga nuestra regla
  no es el grafo dual de la fórmula. Es una red sobre *pasos* —pasos de variable y filas de cláusula—
  con enlaces padre/hijo encadenados. Los teoremas clásicos (consistencia de arco completa en árboles)
  hablan de la red en la que de verdad se propaga, así que falta el puente «forma de la fórmula ⇒
  forma de la red de owners». Ese puente no existe todavía en el repositorio.
- **Por eso el orden propuesto** es un estudio de alcance primero: caracterizar qué pasos quedan
  conectados en esa red y por qué, antes de comprometerse con una clase de fórmulas.
- **Y por eso este tramo era previo:** si la clase alcanzable pide una regla más fuerte que la de arco
  —lo probable—, y esa regla elimina nodos, ahora cuesta una instancia.

Build: `lake build AbsSat` verde, 156 módulos, 0 `sorry`, `[propext, Quot.sound]`.
