# Verificación para el Autor v187: Helly de un paso, relativo al mapa, y una propuesta para el mapa

Ricardo, soy Claude (Opus 5.5). Este informe sigue al v186, que dejó `PairHelly` reducido a
`SegThroughPin`: todo tramo que sobrevive a `cleanPair` tras un pin se extiende a una cadena completa
del estado del lector que pasa por el nodo pinchado. Aquí se mide la forma más pequeña de atacarlo
—alargar el tramo **un paso cada vez**— usando lo que tú señalaste: el Helly que necesitamos es
**relativo**, y la representación (ventanas de tres nodos del mapa, cláusulas de siete filas sin la
000) es lo que hay que aprovechar. Al final, en una sección aparte, una propuesta de cambio del mapa
para que las piezas encajen: está pensada para que la analices con calma.

Rama `pair-mode`. Sonda `lake exe row-degree onestep random 12 4 <semillas>`
(`lean_project/Probes/RowDegree.lean`, commit `a80fc32` y siguientes).

---

## 1. Qué se mide

Tras `cleanPair` de cada pin del lector (el pin débil, `filterWeak`, como en la escalera), para cada
tramo `S` del estado resultante `C` y cada extremo:

* **hacia arriba**: los candidatos a alargar el tramo son los hijos vivos del extremo superior `t`
  (paso `h`). Un hijo de `t` es la ventana `(d, t.id, t.parent)`: **los candidatos solo se distinguen
  por `d`**, el nodo del mapa del paso `h+1`;
* **hacia abajo**: los padres vivos del extremo inferior `b` que encajan con su ventana; solo se
  distinguen por la componente más antigua, el nodo del mapa del paso `l-3`.

Para cada miembro `u` del tramo, `B_u` = los candidatos que están en su tabla. Alargar el tramo un paso
es encontrar un candidato en todos los `B_u`: un **Helly de un paso**, sobre un dominio de nodos del
mapa.

## 2. Resultados

Semillas 1 y 7, 86 pines, 60.734 extensiones (todos los tramos de `C`, arriba y abajo):

| | medido |
|---|---|
| extensiones imposibles (ningún candidato común) | **0** |
| `B_u` que no se cortan dos a dos | **0** |
| fallos de Helly (dos a dos sí, todos no) | **0** |
| tamaño del dominio | **1 en el 88 %** (53.749); 2 en 6.326; 3–7 en 659 |
| por tipo de paso del componente que varía | cláusula 27.339, negación 14.022, variable 13.665, fusión 5.708 |
| pasos de cláusula: algún `B_u` que no es una **caja** | **0** |
| cajas cuya intersección cae solo en la fila 000 | **0** |

Una caja es un conjunto de filas de la cláusula descrito por los literales que fija: «todas las filas
con `l1 = 0`», «todas las filas con `l2 = 1, l3 = 0`»…, dentro de los candidatos vivos.

**Lectura.** Casi siempre el paso está **forzado** (un solo candidato). Con dos candidatos, Helly es un
lema trivial: subconjuntos de `{0, 1}` que se cortan dos a dos tienen un elemento común (si alguno es
`{0}`, todos contienen el 0; si alguno es `{1}`, el 1; si no, todos son `{0,1}`). Los únicos casos con
contenido son pasos de cláusula con 3 o más candidatos (un 1 %), y ahí los `B_u` son siempre cajas. Las
cajas cumplen Helly en el cubo entero; en el cubo sin la 000 **la única manera de fallar** es que entre
todos fijen los tres literales a falso —el obstáculo clásico, el que tú señalabas—, y no aparece nunca.

## 3. Por qué los `B_u` se cortan dos a dos

Es la pieza que hace falta en cualquier camino. Primera hipótesis: las entradas de un miembro en el
paso siguiente son todas hijos de `t`, y entonces la regla de parejas daría el corte directamente.

**Es falsa**: de 480.574 miembros revisados, 82.240 (un 17 %) tienen en ese paso alguna entrada que no es candidata, en 21.462 de las 60.734 extensiones. Un ejemplo: el miembro `0/0` tiene en el paso 7 las entradas `7/0<6/1<5/0` y
`7/0<6/1<5/1`, que no son hijas del extremo `6/0<5/0<…`; el único candidato es `7/1<6/0<5/0`.

Pero **ninguna pareja** tiene todas sus entradas comunes de ese paso fuera de los candidatos (0 en
todas las semillas). Y hay una razón exacta para mirarlo así: las entradas de `t` en el paso `h+1` son
sus hijos (I1-hijos, ya en `PStateG`), así que

> `B_u ∩ B_v` = las entradas del paso `h+1` comunes a `u`, `v` **y** `t`.

**Que los `B_u` se corten dos a dos es un Helly de tres —`u`, `v` y el extremo `t`— en un solo paso.**
Es el «triángulo con el extremo». Medido sin fallos aquí, y coherente con los 5,3 millones de tríos
del v185.

## 4. El mapa de la prueba de un paso

Con lo medido, `SegThroughPin` saldría de:

1. **Alargar paso a paso** hasta una cadena completa de `C`. Esa cadena es completa en el estado del
   lector (al subir por una poda solo se gana, `fullChain_before`), y en el paso pinchado solo puede
   estar el nodo pinchado. Es mecánico.
2. **En cada paso, Helly sobre los candidatos**:
   * dominio de 1 o 2: el lema de dos elementos, un teorema;
   * paso de cláusula con más candidatos: que los `B_u` son cajas, y que las cajas nunca se juntan solo
     en la 000.
3. **El triángulo con el extremo**: que `u`, `v` y `t` compartan una entrada en el paso siguiente.

Las piezas 2 (cláusulas) y 3 son las que tienen contenido. De la 2 hay un argumento a mano: el tramo es
también un tramo del estado del lector, que cumple `SegExact`. Allí se extiende a una cadena completa,
cuya fila de cláusula es compatible con todos los miembros y no es la 000. Falta ver que las cajas en
`C` no pierden esa fila por culpa del pin.

## 5. Propuesta: binarizar las cláusulas con una ventana prohibida

*Para analizar con calma; no está implementada.*

### La idea

La pieza 2 existe solo porque un paso de cláusula tiene 7 nodos del mapa. Si **todo paso tuviera como
mucho 2**, el Helly de un paso sería el lema de dos elementos **en cualquier estado**, sin depender de
las tablas. Solo quedaría el triángulo con el extremo (pieza 3).

### Por qué no basta con partir la cláusula en tres pasos

Lo natural sería codificar la cláusula `j` con tres pasos binarios, uno por literal (`L1_j`, `L2_j`,
`L3_j`), cada nodo con su bit y requiriendo el nodo del literal con ese valor. Pero la cláusula es una
**disyunción** (no los tres falsos), y los requisitos del mapa son **conjuntivos**: un nodo requiere
*todos* los nodos de su lista. Ningún nodo de `L3` puede decir «si soy 0, entonces `L1` o `L2` es 1».
Por eso hoy la cláusula enumera sus 7 filas: es la forma de meter la disyunción en un paso. Las
alternativas conjuntivas (Tseitin con variables auxiliares) necesitan igualmente pasos de 3 o 4
nodos.

### Cómo hacerlo: la ventana hace la disyunción

Con ventanas de tres nodos del mapa, **los tres pasos de una cláusula caben exactamente en una
ventana**: el nodo del paso `L3_j` es la ventana `(b3, b2, b1)`. La disyunción se expresa prohibiendo
una sola ventana: **`(0, 0, 0)` no se crea**.

* **Mapa**: la cláusula `j` pasa de un paso con 7 filas a tres pasos con 2 nodos cada uno. El nodo
  `Lp_j = b` requiere el nodo del literal `lp` con valor `b`, como hoy cada fila requiere sus tres
  literales. Además, el mapa declara la ventana prohibida `(L1_j, L2_j, L3_j) = (0, 0, 0)`.
* **UP**: al crear los nodos de la fila `L3_j` desde las ventanas de la fila anterior, no se crea el que
  cierra la ventana prohibida. Es un filtro local en `create_node_from_parents!` / `addNode`, sobre
  datos que el nodo nuevo ya tiene (su propia ventana).
* **Pasos**: `2n + 3m + 2` en lugar de `2n + m + 2`. Los nodos por paso no crecen: en `L3_j` hay como
  mucho 7 ventanas vivas, las mismas 7 filas de hoy, pero repartidas en tres pasos de dos nodos del mapa.

### Qué gana la prueba

* **El Helly de un paso pasa a ser un teorema general**: todo dominio de candidatos tiene como mucho 2
  elementos. Desaparecen las cajas, el hueco 000 y el 1 % de casos difíciles.
* La disyunción deja de estar en las tablas y pasa a estar en **la existencia de nodos**: una ventana
  prohibida no existe. Una cadena completa nunca puede pasar por ella, y eso es un hecho de forma, no de
  exactitud.
* Tus «9 valores por nodo» se vuelven exactos: una ventana de un paso `L3_j` fija los tres literales de
  la cláusula `j`, y nada más.

### Qué cuesta

* **Julia**: `add_gate_case!` (la cláusula en tres pasos) y el filtro de ventana prohibida en UP.
* **Lean, el mapa**: `CnfMap` (`reqOfCnf`, `mapNodes`, `stepCount`) y todo lo que decodifica una
  cadena como asignación (`Functional`, `Backward`, la correspondencia con las soluciones). Son pruebas
  del mapa, no del review; se rehacen, pero con la misma estructura.
* **Lean, UP**: `addNode` con el filtro, y los invariantes de UP (`Fabric_addNode`, `ShapeOk`, las
  filas nuevas). El review, la limpieza, la regla de parejas y la escalera no dependen del mapa.
* **Riesgo de coste**: más pasos con los mismos nodos por paso. El trabajo de las pasadas crece con el
  número de pasos; habría que medirlo.
* **Riesgo de semántica**: comprobar, con la comparación diferencial de siempre (veredictos, estados
  equivalentes, soluciones contra el exhaustivo), que el mapa binarizado decide lo mismo.

### Qué no resuelve

El **triángulo con el extremo** (pieza 3): que dos miembros y el extremo compartan una entrada en el
paso siguiente. Con dominio 2 tiene una forma muy concreta —no puede pasar que un miembro solo admita
el hijo `d = 0` y otro solo el `d = 1`—, pero sigue siendo una afirmación sobre las tablas. Es, con
diferencia, la pieza más pequeña de todas las que han aparecido.

### Alternativa sin tocar el mapa

Demostrar la pieza 2 tal como está: los `B_u` de un paso de cláusula son cajas (por la estructura de
ventanas) y nunca se juntan solo en la 000 (por `SegExact` del estado del lector). Es más trabajo de
prueba y menos de máquina. La binarización cambia la máquina para que la prueba sea corta.

## 6. Una frase

Alargar un tramo un paso casi nunca es una elección —en el 88 % de los casos hay un solo candidato—, y
cuando lo es, las piezas encajan como cajas que nunca se juntan en el hueco. Lo que queda de verdad es
un triángulo: dos miembros y el extremo, en el paso siguiente.
