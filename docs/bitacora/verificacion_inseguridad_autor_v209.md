# Verificación para el Autor v209: la vía B hasta el final, y todo lo que falta, en el join

Ricardo, este informe sigue al v208 en la misma sesión (29-sept-2026, rama `reader-stuck`). El v208 proponía la
vía B: la estrella de una cima. Aquí cuento cómo la recorrí entera: qué quedó **demostrado**, qué dicen los datos y
dónde queda exactamente lo que falta.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar):
  * `StarNodes` + `TopNbr` ⟹ `NodeColour`;
  * la estrella de una cima se sostiene **por inducción a lo largo de la línea**. La base y el UP están demostrados
    sin hipótesis, incluido el paso delicado, subir la estrella del padre por la fila nueva;
  * el join se reduce a una vuelta explícita de la regla de trío en el lado de la cima.
* **El veredicto del lector** (`readerVerdict_iff_of_trioSide`) depende ahora de dos hipótesis, **las dos en el
  join**:
  * `TrioSideAt`: una vuelta de trío en el lado de la cima es cerrada;
  * `SideEdgesAt`, la del v208.
* **Medido:** el review de una estrella llega **siempre** a una sola vuelta de trío explícita, en 26 258 de 26 258
  estrellas, tanto en la unión como en el lado. Y las etiquetas por fila no cambian nada de esto.

---

## 1. Los "fallos" que no lo eran

En el v208, la vía B tenía dos anomalías:
* la regla de parejas fallaba dentro de la estrella en torno al 4 % de los núcleos;
* existían los tríos muertos de `clause_mix*`.

Me preguntaste si activar las etiquetas por fila (`ROW_TAGS=on`) los eliminaba. Lo medí sobre las instancias con
fallos (`27b0e6c`): salen **exactamente los mismos números**. La regla de la etiqueta no corta nada en estos estados.

Tu pregunta siguiente fue la buena: si todas sus aristas son correctas, ¿por qué se llaman fallos? **No son fallos de
la máquina.**
* Restringir a la estrella y revisar conserva **todos** los nodos (`fx_f = 0` en todas partes).
* El review solo quita **aristas** sobrantes.
* El "4 %" decía que la estrella, escrita a mano tal cual, no es una estructura cerrada. Era un atajo de mi prueba,
  no un defecto del estado.
* Lo mismo vale para los tríos muertos: rompen un lema auxiliar (`OneSideSupport`), no el veredicto.

Así que no hace falta ninguna regla nueva. Lo que había que cambiar era la prueba: tomar la estructura como el **punto
fijo del review** dentro de la estrella, no como la estrella literal.

## 2. El punto fijo es una sola vuelta de trío (`StarTrio.lean`, `c457d94`)

Medí qué aristas deja el review dentro de la estrella $S(t)$ de una cima $t$ (`probe_star_fixpoint.jl`), comparando
con varios candidatos explícitos:

| candidato (aristas entre nodos de $S(t)$) | coincide con el punto fijo |
|---|---|
| todas las de $V$ | 24 743 / 26 258 |
| las que forman triángulo con $t$ | 24 743 / 26 258 |
| **una vuelta de trío**: en cada paso, un testigo común que $t$ también posee | **26 258 / 26 258** |

Son 88 instancias; 5 347 estrellas vienen de estructuras al azar y 20 911 de núcleos fijados. Nunca se pierde un nodo.
La cascada del review, dentro de la estrella, **no tiene profundidad**: una vuelta basta.

En Lean:

> `trioRel u R t x w` := `R x w`, los dos en la estrella, y en cada paso un testigo común `r` con `R r t`.
>
> **`TrioStar u`**: para toda estructura cerrada y toda cima, `trioRel` es una estructura cerrada.

**`starNodes_of_trioStar`**: `TrioStar ⟹ StarNodes`. Todo nodo $z$ de la estrella entra, porque los testigos de su
pareja con $t$ los posee $t$, así que están en la estrella.

## 3. La estrella por inducción a lo largo de la línea (`StarUp.lean`, `StarLine.lean`, `c457d94`, `d1562e4`)

`TrioStar` en un solo estado es un Helly de segundo orden, y no sale de las reglas de parejas. La idea fue **no
demostrarla dentro de un estado, sino heredarla**: un paso antes, el padre $p$ de la cima $t$ era cima.

**El invariante (`StarInv`).** Para toda estructura cerrada $(V,R)$, toda cima $t$ y todo $z$ con $R\,z\,t$, hay una
estructura cerrada $(W,R')$ que cumple:
* $z, t \in W \subseteq V$;
* todo $W$ está relacionado con $t$ por $R'$;
* en el paso de $t$, en $W$ solo está $t$.

`StarInv ⟹ StarNodes`.

**Base** (`starInv_initSeed`): la semilla tiene un solo vivo.

**UP (`starInv_up`), demostrado sin hipótesis:**
1. *Bajar.* $V$ pasa del estado final al de antes del review (`secStruct_of_sub`). Luego, sin la fila nueva, al
   estado filtrado (`secStruct_addNode_down`). Y de ahí al estado anterior al filtro.
2. *El padre.* El testigo de la pareja $z$–$t$ en el paso de arriba es un vivo $p$ que $t$ posee. Una arista de un
   nodo nuevo hacia el paso de arriba viene de uno de sus padres, y las cimas no se poseen entre sí (`TopsApart`).
   Luego $p$ **es un padre de $t$** (`rowParent_of_adj`).
3. *Hipótesis de inducción* en $p$: da $W_0$ cerrada en la estrella de $p$ que contiene a $z$ (o a $p$, si $z = t$).
4. *El filtro.* $W_0$ pasa el filtro porque sus nodos son vivos del estado filtrado, así que concuerdan con los
   requisitos (`pinned_filterAll_list`).
5. *Subir* (`secStruct_addNode_star`). $W_0 \cup \{t\}$ es cerrada tras la fila:
   * $t$ hereda los vecinos de su padre, así que posee todo $W_0$;
   * los testigos de las parejas nuevas son los de $W_0$, y en el paso nuevo el testigo es $t$;
   * $p$ gana a $t$ como hijo, que es el hijo que la estructura pide en el paso de $p$.

   Después, el review la conserva (`secStruct_review`).

**Join (`starInv_join`).** Bajo **`StarJoinDown`**: para una cima $t$ de la unión y un $z$ de su estrella, hay una
estructura cerrada **de un solo lado**, dentro de $V$, que contiene y relaciona a $z$ y $t$. Con eso se aplica la
hipótesis de inducción del lado y se levanta a la unión (`secStruct_join_left/right`, ya demostrados).

Medido (`probe_join_down.jl`, 88 instancias): restringir el lado de la cima a su estrella y revisar conserva **todos**
los nodos: 1 403 067 nodos de estrella, 0 fallos.

## 4. El join, reducido a una vuelta de trío en el lado (`StarSide.lean`, `a71b6a7`)

Repetí la medida del §2 dentro del lado $L$ de la cima (`probe_join_star_fix.jl`):

| candidato en $L$ | coincide |
|---|---|
| aristas de $L$ | 23 862 / 26 258 |
| aristas de $L$ que también son de $V$ | 24 751 / 26 258 |
| vuelta de trío con aristas de $L$ | 26 139 / 26 258 |
| **vuelta de trío con aristas de $L$ y de $V$** | **26 258 / 26 258** |

En Lean:

> `sideRel L R x w := R x w ∧ L.Adj x w`.
>
> **`TrioSideAt u L`**: la estructura $\{x \in V \mid \text{sideRel } L\,R\,x\,t\}$ con `trioRel L (sideRel L R) t`
> es cerrada en $L$.

**`starJoinDown_of_trioSide`**: con `TopsApart` en los dos lados, `TrioSideAt` en los dos da `StarJoinDown`. El
testigo de $z$ en la cima, dentro de la estructura, solo puede ser $t$.

**`readerVerdict_iff_of_trioSide`**: el veredicto del lector es la satisfacibilidad bajo `TrioSideAt` y
`SideEdgesAt` en los joins. `#print axioms` da solo `propext`, `Classical.choice` y `Quot.sound`.

## 5. Dónde está exactamente lo que falta

| pieza | estado |
|---|---|
| base, filtro, review, fila nueva (UP) de la estrella | **demostrado** |
| `StarNodes` ⟹ `NodeColour` ⟹ `NodeSplitIn` ⟹ `NodeIn` | **demostrado** (con `SideEdgesAt`) |
| `CliqueSplit`, completitud, `SepAt`, dos colores por join | **demostrado** (v207–v208) |
| levantar una estructura de un lado a la unión | **demostrado** |
| **`TrioSideAt`**: la vuelta de trío en el lado es cerrada | hipótesis; medido 26 258 / 0 |
| **`SideEdgesAt`**: la unión fijada en un color usa aristas de ese lado | hipótesis; medido 7,18 M / 0 |

Las dos hipótesis dicen, en el fondo, lo mismo: **una estructura de la unión se puede bajar a un solo lado**.

`TrioSideAt` pide un Helly de segundo orden: si $x, w, t$ tienen un testigo común $r$, las parejas $x$–$r$ y $w$–$r$
también tienen testigos comunes con $t$. Lo que ha cambiado respecto al v208:
* antes hacía falta en **cada estado** de la máquina; ahora solo en el join;
* es una sola vuelta explícita, sin cascada.

**Por qué no sale todavía.** Con solo las reglas de parejas no se deduce. Y la hipótesis de inducción del lado no
ayuda directamente: habla de estructuras cerradas de $e$, y $V$ restringida a $e$ no lo es.

## 6. Siguiente paso propuesto

Usar lo único que sabemos del join y que no es local: la **completitud** (`steps_has_sel`, `carried_arrival`,
`CliqueSplit`). La conjetura concreta es:

> para $x, w$ en la estrella de $t$ con una arista del lado, **el testigo $r$ se puede elegir en una camarilla del lado
> que pasa por $x$ y por $t$**.

Si fuera así, esa camarilla daría los testigos de $x$–$r$ con $t$ en todos los pasos, que es justo lo que pide
`TrioSideAt`. Es medible en Julia antes de intentarlo en Lean. Si falla, la alternativa es la vía D del v208, acotar
la clase: `TrioSideAt` es una comprobación local de una vuelta y se puede comprobar por instancia.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `StarTrio`, `StarUp`, `StarLine`, `StarSide`.
En `StarNodes`, el paso del join queda extraído como `joinStep_T`.

**Julia (`julia/improves_bingo/test_3sat/`):**
* sondas: `probe_star_fixpoint`, `probe_join_down`, `probe_join_star_fix`;
* con `ROW_TAGS=on`: `probe_topstar_union_tags_bin` y `probe_onesided_tags_bin` en `output_probes`.

**Commits:** de `27b0e6c` a `60aa13a` en la rama `reader-stuck`.
