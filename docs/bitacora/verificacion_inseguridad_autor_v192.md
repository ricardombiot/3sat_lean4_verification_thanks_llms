# Verificación para el Autor v192: qué gana la prueba Lean con el mapa binario

Ricardo, soy Claude (Opus 5.5). La rama `improves_bin` ya tiene el mapa `bin` en Julia (Fases A, B y C
de `docs/plans/bin-map.md`): cada cláusula ocupa tres pasos de dos nodos, con una ventana prohibida
`(0,0,0)` al final. Este informe es **teórico**. Recorre, pieza a pieza, qué cambia en la prueba Lean
si el mapa pasa a ser binario. No hay mediciones nuevas ni código nuevo.

Cada afirmación lleva su estado: **demostrado** (hay teorema en Lean), **deducido** (se sigue de lo
demostrado o de la forma del mapa, sin escribir aún) o **por comprobar** (hipótesis razonable, sin
argumento completo).

**La conclusión, por adelantado.** Con el mapa binario, alargar un tramo un paso deja de tener
hipótesis sobre la forma del paso. Toda la pieza de las cajas desaparece. La escalera
`OneStep → SegGood/PairHelly` queda con **una sola hipótesis sobre las tablas: el triángulo con el
extremo (`TriTop`)**. El fallo de la semilla 11 no desaparece (v191 §6.1), pero queda localizado en
esa pieza y en su forma más pequeña.

---

## 1. Punto de partida: qué pide hoy alargar un paso

En `AbsSat/GraphPath/Model/OneStep.lean` (v187), alargar un tramo un paso se reduce a dos hipótesis:

```lean
theorem oneStepUp_of (C : GPathM) (hsym : OwnSymmetric C) (hT : TriTop C) (hS : SmallOrHellyUp C) :
    OneStepUp C
theorem pairHelly_of_triTop (C : GPathM) (hsym : OwnSymmetric C) (hT : TriTop C)
    (hU : SmallOrHellyUp C) (hD : SmallOrHellyDown C) : PairHelly C
```

* **`SmallOrHelly…`**: o el paso tiene **como mucho dos candidatos**, y entonces basta `helly_two`
  (demostrado), o algún candidato lo poseen todos los miembros.
* **`TriTop`**: cada dos miembros del tramo comparten un candidato. Es el «triángulo con el extremo».

En el mapa clásico, la segunda rama de `SmallOrHelly` hace falta en los pasos de cláusula, que tienen
hasta 7 filas. Para ellos está la **pieza 3, por cajas**: `helly_box`, `rowBit`, `BoxHellyUp` y
`extUp_of_boxes` (demostrados, **solo hacia arriba**). Pero su hipótesis `BoxHellyUp` es existencial
(`W`), porque las cajas «literales» fallan en 30 de 463 casos de la semilla 7. Y exige que ningún corte
caiga en el hueco 000. La versión hacia abajo no está escrita.

## 2. Ventaja 1: `SmallOrHelly` deja de ser hipótesis

**Deducido.** Un candidato hacia arriba (`IsCandUp C sel hi r`) es un nodo vivo del paso `hi + 1` que
tiene al extremo `sel hi` entre sus padres. Su `PathNodeId` es una ventana `(gparent, parent, id)`:

* `gparent` y `parent` son los ids de mapa de `sel hi`, así que están fijados por el extremo;
* solo varía `id`, un nodo del mapa en el paso `hi + 1`.

En el mapa bin, **todo paso tiene como mucho 2 nodos de mapa** (1 en las fusiones, 2 en variables y en
cada `L1_j`, `L2_j`, `L3_j`). Luego hay como mucho 2 candidatos. Hacia abajo es simétrico: el candidato
es un padre del extremo inferior, y solo varía su `gparent`, que está en el paso `lo - 2`, que también
tiene como mucho 2 nodos.

Así que `SmallOrHellyUp C` y `SmallOrHellyDown C` salen **siempre por la primera rama**. Hay que
escribir un lema de forma, del tipo:

```lean
theorem candUp_le_two (hshape : ShapeOk C) (hbin : BinMap C.map) … :
    ∃ a b, ∀ r, IsCandUp C sel hi r → r = a ∨ r = b
```

Depende del mapa y de `ShapeOk` (la forma de los ids que ya lleva UP), **no de las tablas**. Es un
hecho de forma, válido en cualquier estado.

Consecuencia:

```lean
-- previsto
theorem oneStepUp_of_bin (hsym : OwnSymmetric C) (hT : TriTop C) : OneStepUp C
theorem pairHelly_of_triTop_bin (hsym : OwnSymmetric C) (hT : TriTop C) : PairHelly C
```

## 3. Ventaja 2: desaparece la pieza de las cajas

**Deducido.** Con como mucho 2 candidatos por paso, no hace falta la rama de Helly. Sobran:

* `helly_box`, `rowBit`, `BoxHellyUp`, `extUp_of_boxes`;
* la versión **hacia abajo** de las cajas, que ni siquiera estaba escrita;
* la `W` existencial y los 30 casos de cajas no literales;
* el hueco 000 como caso de la prueba, y el 1 % de pasos difíciles del v187.

Es la parte con más contenido de la prueba de un paso, y la menos cerrada. En el mapa bin **no hay nada
que cerrar**.

## 4. Ventaja 3: el fallo de la semilla 11 queda localizado en `TriTop`

**Deducido, sin medir.** El v191 §6.1 muestra que el trío muerto de la semilla 11 sigue ahí con el mapa
bin: el hueco pasa a las ventanas de `L2`. Por tanto, en ese estado, `SegGood` sigue fallando.

Pero en el mapa bin la cadena es `TriTop ⟹ OneStep ⟹ SegGood`, sin más hipótesis (§2). Si `SegGood`
falla, **tiene que fallar `TriTop`**, en algún tramo y algún paso concretos.

Eso es una ventaja para la prueba, no solo un diagnóstico:

* En el clásico, el fallo podía estar en tres sitios: `SmallOrHelly` (cajas), `TriTop` o el invariante
  de partida. En el bin solo queda uno.
* Con dominio 2, `TriTop` tiene su forma mínima: **no puede ocurrir que un miembro solo admita el
  candidato `d = 0` y otro solo el `d = 1`**. Es una afirmación sobre dos miembros y dos valores.
* Lo previsto del v191 (llevar `PairExact`, o `PrefixSegGood`, en lugar de `SegGood`) se aplica igual.
  Lo que cambia es que la pieza que hay que restringir a prefijos, o a parejas con el pin, es una sola.

**Por comprobar**: medir `TriTop` en el mapa bin para la semilla 11, fórmula #1, y ver que el fallo
aparece ahí y en qué tramos.

## 5. Ventaja 4: la disyunción pasa a ser la inexistencia de un nodo

**Deducido.** En el mapa bin:

* Cada nodo `Lp_j = b` tiene **un solo require**: `⟨step(lp), b⟩`. No hay filas con tres requires ni
  requires negados en las cláusulas.
* La disyunción de la cláusula está en que la ventana `(L1_j, L2_j, L3_j) = (0,0,0)` **no se crea**
  en UP. Una cadena completa no puede pasar por ella: es un hecho de forma, igual que hoy lo es que una
  fila exista.
* La ventana de un nodo de `L3_j` fija **exactamente** los tres literales de la cláusula `j`, y nada más.
  Tus «9 valores por nodo» quedan exactos.

Para la prueba del mapa (`AbsSat/GraphMap/CnfMap.lean`, `MapReqs.lean`: `Functional`, `Backward`),
decodificar una cadena como asignación debería ser más uniforme. Cada paso de cláusula aporta un bit
de un literal con un require simple, y la condición de cláusula es una sola ventana ausente. Hoy es una
enumeración de 7 filas con `rowBit`.

**Por comprobar**: que la prueba de «cadena completa ⟺ solución» del mapa bin no queda más larga por
tener `3m` pasos de cláusula en lugar de `m`. La estructura es más regular, pero hay más pasos.

## 6. Ventaja 5: encaje con la propuesta B del v191 (`PairExact`)

**Por comprobar.** La pieza que el v191 dejó abierta es conservar `PairExact` en el pin: si `(x, w)`
sobrevive a `cleanPair X`, hay una cadena sana de `X` por `x`, `w` **y el pin**.

Si esa cadena se construye alargando paso a paso, cada paso es, en el mapa bin, una elección entre dos
candidatos. El argumento tendría entonces la forma de `TriTop` con el pin como tercer miembro fijo. Es
la misma pieza de §4, y no una nueva. No está demostrado que la conservación se pueda hacer así. Se
señala porque las dos líneas abiertas convergen en la misma afirmación de dominio 2.

## 7. La estructura simétrica

**Especulativo.** El mapa bin es `[fusión][variables][fusión][cláusulas][fusión]`: empieza y acaba en
fusión, y todo paso intermedio tiene 2 nodos. En el clásico, «hacia arriba» y «hacia abajo» tienen
formas distintas cerca de las cláusulas (7 filas arriba, 7 abuelos abajo). En el bin, el lema de
§2 es el mismo en las dos direcciones.

Queda abierto si se puede ir más lejos: obtener las piezas `Down` de las `Up` reflejando el mapa. No hay
argumento para eso todavía. Con prefijos (v190 §5), la dirección `Down` podría no hacer falta en
ningún caso.

## 8. Lo que no gana, y lo que cuesta

* **No arregla el trío de la semilla 11** (v191 §6.1). Las tablas siguen siendo de parejas. Lo que hace
  el bin es aislar el fallo (§4), no quitarlo.
* **Lean, el mapa**: rehacer `CnfMap` (`reqOfCnf`, `mapNodes`, `stepCount = 2n + 3m + 3`) y la
  decodificación de cadenas (`Functional`, `Backward`). Son pruebas del mapa, con la misma estructura.
* **Lean, UP**: `addNode` con el filtro de ventana prohibida, y los invariantes `Fabric_addNode` y
  `ShapeOk` con ese filtro. El filtro solo quita nodos, así que los invariantes de «subconjunto» deberían
  pasar sin cambios de fondo.
* **No cambian**: el review, la limpieza, la regla de parejas, `AggInactive`, las reducciones y la
  escalera del lector. No dependen del mapa.
* **Coste de ejecución**: de `m` a `3m` pasos de cláusula. La Fase C estima ~7x en `v8_c10` y ~25x en
  `v4_c20`. Queda por medir en la Fase D.

## 9. Resumen

| ventaja | pieza Lean | estado |
|---|---|---|
| `SmallOrHelly` gratis (≤ 2 candidatos) | lema nuevo `candUp_le_two`/`candDown_le_two` + `helly_two` | deducido |
| sin cajas ni hueco 000 | sobran `helly_box`, `BoxHellyUp`, `rowBit`, `extUp_of_boxes`, y las cajas `Down` que faltaban | deducido |
| escalera con una hipótesis de tablas | `pairHelly_of_triTop` solo con `TriTop` | deducido |
| fallo de la semilla 11 localizado en `TriTop` | — | deducido, por medir |
| disyunción = ventana ausente, un require por nodo | `CnfMap`, `Functional`, `Backward` | deducido |
| `PairExact` en el pin con la forma de `TriTop` | propuesta B del v191 | por comprobar |
| reflejo `Up`/`Down` por simetría | piezas `Down` | especulativo |
| coste | rehacer mapa y UP en Lean; `3m` pasos | conocido |

## 10. Lo previsto, en orden

1. **Espejo Lean del mapa bin**: `CnfMap` con `L1/L2/L3`, ventana prohibida y `stepCount`. Primero la
   definición y la correspondencia «cadena completa ⟺ solución».
2. **UP con filtro**: `addNode` y los invariantes `ShapeOk` y `Fabric_addNode`.
3. **Lema de forma** `candUp_le_two` / `candDown_le_two`.
4. **Escalera sin `SmallOrHelly`**: `oneStepUp_of_bin`, `pairHelly_of_triTop_bin`.
5. **Medir `TriTop` en el mapa bin** (semillas 1, 7 y 11, sin muestreo en instancias pequeñas) para ver
   dónde falla y si se mantiene en prefijos o para parejas con el pin.

Los pasos 1 a 4 no dependen de ninguna medición. El 5 es el que decide la ruta.

## 11. Una frase

El mapa binario no borra el trío muerto, pero deja la prueba de un paso sin cajas ni huecos: lo único
que queda sobre las tablas es que dos miembros no se contradigan en una elección entre dos.