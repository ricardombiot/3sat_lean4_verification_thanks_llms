# Verificación para el Autor v211: el cono de antepasados, el hueco de una llegada y el acuerdo entre ramas

Ricardo, este informe sigue al v210 en la misma sesión (29-sept-2026, rama `reader-stuck`). El v210 terminaba con el
veredicto bajo tres hipótesis: B1, `CrossAt` y `ArrivalGap`. Aquí cuento cómo `CrossAt` desapareció. Primero lo
sustituí por un argumento sobre los antepasados de la cima (el cono). Después eso resultó innecesario: la estrella de
la cima cabe entera en **una sola llegada**, la que trajo a sus padres. Al final, lo que queda por demostrar tiene una
sola forma, que llamo el **acuerdo entre ramas**.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar):
  * el caso "repartido" de StarOneSide (`starOneSide_split`), sin hipótesis;
  * el join con un proveedor abstracto por lado (`HypsOne`, `readerVerdict_iff_of_one`);
  * la infraestructura del cono de antepasados (`ConeAnc.lean`):
    * las entradas de la línea son árboles de llegadas;
    * TopsApart en todas las entradas de todos los niveles;
    * la monotonía del paso libre;
    * el descenso hasta la transición;
  * `ArrivalGap` ⇐ `ArrHole`, y `ConeGap` de una sola llegada ⇐ `ArrHole` (`ConeHole.lean`);
  * **StarOneSide ⇐ `ArrHole` + `AbsHole`** por la llegada de los padres (`StarHole.lean`).
* **El veredicto** (`readerVerdict_iff_of_holes`) depende ahora de **tres hipótesis**:
  * **B1**: `StarNodes` de la unión, igual que antes;
  * **ArrHole** y **AbsHole**: cada una habla de **una sola llegada** y de las aristas del nivel de su remitente, sin
    contexto. No hablan de estructuras cerradas ni de uniones.
* **Medido:** `ArrHole` 23 571/23 571 y `AbsHole` 3 908/3 908, en 6 instancias (clause_mix incluida) sin ninguna
  condición añadida. B1 igual que antes.
* **Lo que no he conseguido:** demostrar `ArrHole`. Sé con precisión de qué está hecho (§8). Lo que falta es el mismo
  tipo de problema que B1: que dos ramas se pongan de acuerdo en un paso.

---

## 1. El caso repartido y el proveedor por lado (`OneSideHist.lean`, `SenderLink.lean`, `97bcbd7`)

Partí de tu sonda sobre la herencia del paso libre (`probe_top_inherit.jl`). Las parejas ausentes de la estrella de
$t$ se reparten en dos casos:
* **bajo un mismo padre**: el paso libre se hereda entero de la estrella del padre;
* **repartidas** (ningún padre tiene a los dos): el paso de los padres queda libre.

El caso repartido se demuestra sin hipótesis (**`starOneSide_split`**). En ese paso la estrella de $t$ solo contiene
padres de $t$, y ninguno vive en la otra llegada: los padres tienen el id del remitente $kv_A$, y los vivos de la otra
llegada en ese paso tienen el de $kv_B$ (`parents_not_in_other`).

Con eso **`CrossAt1`** (`CrossAt` solo para parejas bajo un mismo padre) basta. También generalicé el join de
`SenderLink` a un proveedor abstracto de StarOneSide por lado (**`HypsOne`**), para no repetir la conexión con la
línea cada vez que cambiara la hipótesis.

## 2. `CrossAt1` no es inductivo (`probe_cross1_step.jl`, `530e310`)

Intenté la inducción de `CrossAt1` bajando un nivel, a la entrada $A_c$ del paso anterior:

| caso | peso | resultado |
|---|---|---|
| quitada (la pareja estaba en $A_c$) | ~90 % | la cubre `ArrivalGap` |
| ausente, sin cima común en $A_c$ | 99 | el paso de las cimas de $A_c$ queda libre arriba, 100 % |
| ausente, con cima común | 225 | el paso libre del subgrupo **no siempre** se hereda |

El tercer caso falla por una razón concreta. Los padres de $t$ comparten remitente, pero sus propios padres pueden
estar en **subgrupos distintos** de $A_c$, uno por cada remitente del nivel de abajo. Los testigos que tapan el paso
cuelgan del otro subgrupo. Tomando la estrella de todos los subgrupos con hijo vivo sí se hereda (100 %), pero esa
estrella ya abarca dos entradas un nivel más abajo. El invariante natural no era una entrada: era el **cono de
antepasados** de $t$.

## 3. El cono de antepasados (`ConeAnc.lean`, `f1d9414`)

En bin los antepasados salen de los propios ids. Como `shiftPid p d = ⟨d, some p.id, p.parent_id⟩`, $p$ es padre de
$q$ exactamente cuando $q.\mathit{parent} = p.\mathit{id}$ y $q.\mathit{gparent} = p.\mathit{parent}$ (`Par`). La
entrada de $p$ es la de clave $p.\mathit{id}$. Así se definen, sin guardar historia:
* `AncL φ t k p`: antepasados vivos de $t$ en el nivel $k$;
* `ConeAt φ k t`: vecinos de esos antepasados en sus entradas;
* `EdgeL φ k`: aristas de todas las entradas del nivel $k$;
* `FreeL φ k t y w`: hay un paso sin testigo común en el cono con esas aristas.

Demostrado sin hipótesis:
* **`steps_tree`**: toda entrada del nivel $n+1$ es un árbol de llegadas del nivel $n$ (antes solo lo sabía por dentro
  la inducción de la línea).
* **`line_topsApart`**: TopsApart en todas las entradas de todos los niveles.
* **Monotonía** (`cone_down`, `edge_down`, `freeL_mono`): el cono de un nivel cabe en el de abajo y las aristas viejas
  bajan, así que un paso libre sube hasta arriba.
* **Nacimiento sin antepasado común** (`freeL_of_noCommon`): en el paso de las cimas, el cono solo tiene antepasados.
* **`freeL_descent`**: se baja hasta la transición más alta de un nivel **Q** (antepasado común con la arista) a
  niveles **P** (comunes sin la arista). Allí o no hay común, o hace falta **`ConeGap`**.

La sonda `probe_cone.jl` confirmó cada pieza:
* la monotonía falla 0 veces;
* ninguna pareja se queda en P en todos los niveles;
* en la transición N el paso es libre el 100 %;
* en la transición Q el nivel de encima tiene paso libre el 100 %.

*Una corrección:* mi primera versión de `ConeGap` era más fuerte de lo que había medido. Pedía la conclusión en
cualquier transición, no solo en la más alta, y no exigía que la pareja fuera arista del nivel. La ajusté antes del
commit.

## 4. `ConeGap` por dentro: el hueco de la llegada que quitó la arista (`ConeHole.lean`, `545ec72`–`0c203bb`)

Qué pasa en la transición (`probe_conegap.jl`):
* **todo** antepasado común del nivel $k+1$ vive en una llegada $X$ cuyo remitente $S$ tenía la arista: la quitó $X$;
* los testigos del nivel $k$ en el paso del hueco **nunca viven en $X$**. $X$ los mató, y aunque siguen vivos en
  otras entradas, al subir salen del cono;
* el hueco **no** cae en pasos requeridos por la cláusula (0 de 5 364).

De ahí la hipótesis local **`ArrHole`**: si una llegada quita una arista de su remitente y conserva a los dos nodos,
hay un paso en el que ningún vivo de la llegada es vecino común, **con las aristas de las dos entradas del nivel del
remitente**. Vale sin contexto (`probe_arrhole.jl`).

Demostrado:
* **`arrivalGap_of_arrHole`**: `ArrivalGap` sale de `ArrHole`.
* **`tree_incl`**: si una cima de una llegada vive en un árbol, las aristas de la llegada son del árbol.
* **`freeL_one`**: si todos los antepasados del nivel $k+1$ están en una sola llegada, `ArrHole` da `ConeGap`. Los
  antepasados del nivel $k$ son cimas de $S$, que tiene la arista; $X$ la quitó (por `tree_incl`); y el cono del nivel
  $k+1$ cabe en los vivos de $X$.

## 5. El caso de dos llegadas (`68deb29`)

Queda el ~4 % de transiciones con antepasados en dos llegadas. Al ampliar a 6 instancias el caso resultó
heterogéneo:
* a veces **las dos** llegadas quitan la arista (68 casos en `set5830`);
* a veces los antepasados caen en **dos entradas distintas** (6 casos en `v6`);
* el paso más alto del hueco no es universal (626/732 en `set5830`).

*Otra corrección:* con las tres primeras instancias te dije que la llegada que no quita "nunca tiene vivos a $y$ y $w$
a la vez". En `v6_c26_i1` sí los tiene, 2 veces.

Lo que valió siempre (1 008/1 008) fue subir hasta el primer nivel con una sola llegada, y eso llevó al paso siguiente.

## 6. La llegada de los padres (`StarHole.lean`, `c28f45d`)

Este es el resultado principal del informe. Arriba del todo, los padres de $t$ comparten remitente, así que viven en
**una sola llegada** $Y$ dentro de $kv_A$, que viene de un remitente $E$ del nivel $n-1$. De ahí:
* la estrella de $t$ en la unión cabe en los vivos de $Y$;
* las aristas de la unión entre viejos bajan al nivel $n-1$.

Basta entonces un paso en el que ningún vivo de $Y$ sea vecino común de $y$ y $w$ con las aristas del nivel $n-1$:
* si $E$ tenía la arista, $Y$ la quitó, y el paso lo da **`ArrHole`**;
* si no (ausente: tampoco en $kv_A$, pero sí en la otra entrada del nivel $n$), lo da **`AbsHole`**, medido 3 908/3 908
  sin contexto.

**`readerVerdict_iff_of_holes`**: veredicto bajo **B1 + `ArrHole` + `AbsHole`**. `CrossAt`, `CrossAt1`, `ConeGap` y el
caso de dos llegadas dejan de hacer falta. El cono de §3 queda demostrado y disponible, pero la cadena ya no lo usa.

Un detalle de la prueba (`absent_of_holes`): los nodos $y$ y $w$ no pueden ser cimas de $kv_A$, porque una cima de
$kv_A$ no vive en la llegada de $kv_B$ (claves distintas). Eso los deja por debajo del nivel de $E$.

*Un matiz:* la variante de `AbsHole` con la arista en la otra entrada del **mismo** nivel de $E$ falla 4 veces en
`clause_mix` (los tríos muertos). La que uso, con la arista en el nivel **siguiente**, no falla.

## 7. B1 por el lado: una equivalencia, no una reducción (`probe_sidekeep.jl`, `2980c3b`)

Medí si restringir una estructura cerrada de la unión al lado de la cima y revisar conserva la estrella y las aristas
$z$–$t$: 0 fallos en 3 319 casos. Pero esa construcción da exactamente `StarJoinDown`, y al revés también, porque la
revisión da la mayor subestructura cerrada. Es la misma hipótesis que `SideSubIn` del v207 y `UnionTopClique`. No
avanza.

Lo que sí queda claro: como B2 ya sale de los huecos, **B1 es todo el contenido de tipo Helly que queda en el join**.

## 8. `ArrHole` por dentro (`77f39bc`, `f68b688`, `1ea407d`)

Intenté demostrar `ArrHole` desde la revisión. Datos sobre 7 262 parejas de 5 instancias:

* **La arista la quita siempre la regla de parejas** (7 262/7 262); nunca el corte por soporte ni la purga.
* **La vía por contradicción no sirve tal cual.** El plan era: sin hueco, $X$ más la arista sería una estructura
  cerrada, la revisión la conservaría (`secStruct_review`, `closedState_review`) y $X$ tendría la arista. Pero una
  estructura cerrada también exige **apoyo**: un padre de $y$ que sea vecino de $w$. En la llegada final el apoyo falla
  **siempre** (7 262/7 262), así que la contradicción solo da "hueco o fallo de apoyo".
* **La cadena de padres** de $y$ llega siempre a un antepasado que sí es vecino de $w$. Aun así:
  * la pareja frontera tampoco tiene apoyo completo (falla el lado de los hijos o el otro sentido);
  * en ~34 % de los casos su arista ni siquiera estaba en el remitente: el hueco viene de niveles anteriores.
* **Dentro de la llegada, el acuerdo no es el problema.** Si todos los padres de $y$ tienen hueco con $w$ en un paso
  por debajo de $y$, $y$ también (100 %); además $y$ tiene unos 14 pasos de hueco propio.
* **El problema es la otra entrada del nivel.** Los pasos que **dispararon** la regla de parejas están dentro del hueco
  del remitente, y al menos uno nunca lo tapa la otra entrada (7 262/7 262). No siempre todos: en 79 casos alguno queda
  tapado.
* **No es un hueco de valor.** Nunca hay un paso en el que $y$ y $w$ tengan vecinos de valores opuestos en todo el
  nivel (0 de 7 262). El hueco es de **camino**, no semántico.

## 9. Dónde estamos

| hipótesis | qué dice | datos | qué se sabe |
|---|---|---|---|
| **B1** | restringir una estructura de la unión a la estrella de una cima no pierde nodos | 26 258 / 0 | es el Helly de la unión; equivale a `StarJoinDown` |
| **ArrHole** | una llegada que quita una arista deja un hueco, contando las aristas de las dos entradas del nivel | 23 571 / 0, sin contexto | lo quita la regla de parejas; el paso que la disparó sobrevive en al menos un caso siempre |
| **AbsHole** | lo mismo para una pareja ausente en el remitente y presente en la otra entrada del nivel siguiente | 3 908 / 0, sin contexto | medido, sin mecanismo |

Las tres trabas tienen la misma forma. Dos ramas (los dos lados del join, o el remitente y la otra entrada del nivel)
tienen que ponerse de acuerdo en un paso, y el acuerdo es sobre **caminos**, no sobre valores. En bin cada nivel tiene
solo dos entradas, así que "la otra rama" es siempre concreta: el otro valor de la variable.

**Siguiente paso propuesto.** Atacar el acuerdo entre ramas como un único problema, empezando por el caso más pequeño:
los 79 pares en los que la otra entrada tapa algún paso del hueco. Si en ellos se ve por qué nunca los tapa todos,
el mismo argumento debería servir para B1.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `ConeAnc`, `ConeHole`, `StarHole`. Cambios en
`OneSideHist` y `SenderLink`.

**Julia (`julia/improves_bingo/test_3sat/`), sondas nuevas:** `probe_cross1_step`, `probe_cone`, `probe_conegap`,
`probe_arrhole`, `probe_sidekeep`. Todas sobre 4–6 instancias. `probes_lib.jl` imprime ahora la traza de un error con
`PROBE_DEBUG=1`.

**Commits:** de `639a7f9` a `1ea407d` en la rama `reader-stuck`.
