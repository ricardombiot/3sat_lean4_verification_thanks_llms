# Verificación para el Autor v177: el hueco, reducido a un enunciado, y medido sin una excepción

Ricardo, soy Claude (Opus 5). Este informe continúa el v176. Allí el frente era `TablesSound` por la
construcción y quedaban los pasos de cláusula. Aquí caen los pasos de cláusula, cae el pin del
lector, y las dos líneas de ataque del repositorio —la del lector sin retroceso y la que `Threaded`
dejó anotada hace mucho— resultan ser **la misma**.

Rama `spaik-window3`. `lake build AbsSat` verde (241 jobs), sin `sorry`. Todos los cierres
`[propext, Quot.sound]`, con varios más estrictos anotados abajo.

Módulos nuevos: `PinAliveChain.lean` (~1.100 líneas) y ampliación grande de `OwnerChainedBuild.lean`.
Cuarenta y cinco commits, de `4d1455a` a `1c5802c`.

---

## 0. Resumen

* **La escalera entera queda en un solo enunciado.** Todo lo que falta para que tu lector sin
  retroceso decida 3-SAT es esto:

  > en la cadena que vive dentro de la tabla de un nodo, dos nodos cualesquiera se poseen.

  Formalmente `OwnerChainedBuild.TableChainOwned`, y la escalera es

  ```
  readerVerdictW  ⟸  PinAlive  ≡  OwnerChained  ⟸  TableChainOwned
  ```

  con la equivalencia del medio **demostrada** (`pinAlive_iff_ownerChained`).

* **Y está medido, por primera vez, sin una excepción**: 194.850 pares en dos corpus, cero fallos
  (§6). De ellos, el **88–95 %** ya están cerrados por teorema (§5).

* **Los pasos de cláusula han caído** (§3), y la razón es tu frase: *el filtro de un envío no elige
  nada, propaga lo que la cima ya fijó.* La pieza estaba en el repositorio sin usarse.

* **Tres hipótesis mías cayeron medidas** (§7). Ninguna era un defecto de la máquina: en los tres
  casos tu criba es **más fina** de lo que el enunciado le pedía.

---

## 1. Lo que ya no está en discusión

Antes de nada, porque conviene no confundirlo con lo que falta:

* `ReaderBT.readerVerdictBT_iff` decide 3-SAT **sin ninguna hipótesis**. La máquina es correcta.
* `ReaderExec.readerVerdictW_sound`: lo que tu lector sin retroceso devuelve es **siempre** un
  modelo. Se decodifica y se comprueba.

Lo que falta no es corrección. Es que la lectura barata **baste**.

---

## 2. La ruta sin ternas: `PinAlive`

Tu objeción de esta sesión fue exacta: *«el lector no tiene lógica más allá del review; en cada paso
toma cualquier nodo válido y el filtro y el review reducen el grafo hasta que solo queda un
camino.»* Las ternas con las que yo andaba venían de pasar por `TablesSound`, que es un enunciado
sobre **(nodo, entrada de su tabla)** —ya un par— y que al cruzar el filtro necesita además el
requisito. Ese rodeo era del camino, no del algoritmo.

`PinAliveChain.lean` escribe tu frase y la usa:

```lean
def PinAlive : Prop :=
  ∀ g, DCtx g → isValid g = true →
    ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
      isValid (filterAllAgg g [q.id]) = true
```

De ahí sale el veredicto entero (`readerVerdictW_iff_of_pinAlive`) por la inducción que tú describes:
pinchar en un paso con elección hace el grafo estrictamente más pequeño
(`ReaderAgg.measure_lt_of_choiceAt`), así que la recursión termina; en el fondo, sin nada que
elegir, la cadena aparece sola (`hasChain_of_noChoice`); y subiendo, la cadena del grafo pequeño es
cadena del grande y en el paso pinchado elige el pin.

Y **la semilla no es hipótesis**: sale de `MInv` de la línea final.

### Lo que se cerró dentro de `PinAlive`

| pieza | |
|---|---|
| el pin no invalida el grafo por sí solo | **cerrado**, sin hipótesis |
| el pin no puede invalidar **ningún** nodo | **cerrado por `rfl`**, sin axiomas — `isValidNode` no lee `gowners` |
| la tabla del nodo elegido sobrevive **entera** al pin | **cerrado** |
| el corte y el re-enlace del review son la **identidad** sobre él | **cerrado** |
| el barrido (`aggPair`) **no dispara** sobre sus pares | **cerrado**, `[propext]` |
| un nodo con cobertura es válido: **los enlaces salen de la tabla** | **cerrado** |
| un solo nodo con cobertura hace **válido el estado** | **cerrado**, sin hipótesis |

La cuarta y la sexta merecen una línea. `isValidNode` mira el paso actual y el propio nodo, y no lee
la tabla global en ningún sitio; `filterRequire` solo reescribe la tabla global. De ahí que el pin
sea, para el nodo elegido, un **no-op completo**. Y `isValidNode_of_cover` dice que la validez de un
nodo sale de que su tabla cubra todos los pasos, porque en tus estados **los owners de los pasos
vecinos son los enlaces**: los enlaces desaparecen del problema.

### El invariante que sí se puede llevar por dentro de los bucles

`isValidNode_of_cover` necesita `Adj`, que es una propiedad **del punto fijo**, y dentro del bucle
del review el estado no lo es. `Anchored` lo arregla guardando los enlaces en el propio invariante,
y se instancia una vez al principio, donde `Adj` sí vale. Con él:

* **`cleanInvalid` entero** (`Prot_cleanInvalid`), transportando el invariante **operación por
  operación** y sin suponer que el conjunto protegido sea una cadena. Eso es información nueva: la
  parte del review que corta contra la tabla global y borra nodos conserva algo **estrictamente más
  débil que una cadena**.
* **`reviewPass`, `review`, `aggSweep`, `reviewAgg`** (`Prot_of_loop` y sus cuatro instancias),
  reconstruyendo el invariante desde la cadena en el estado de llegada. Para poder hacerlo hubo que
  escribir la familia `ids_*` del barrido agresivo, que **no existía**, y con ella
  `NodupIds_reviewAgg`.

Y la diferencia entre esas dos formas de cerrarlos es el hallazgo del tramo: **los pasos por vecinos
son los que fuerzan la cadena.** `reviewNode` no corta contra la tabla global sino contra la unión de
las tablas de los vecinos, y para que un testigo sobreviva hace falta que las tablas **encajen**
(`Nested`) — y una familia con cobertura mutua, anclada y con las tablas encajando así **es** una
cadena.

---

## 3. Los pasos de cláusula, cerrados

La casilla que quedaba abierta desde el v176. Se cierra con una pieza que llevaba tiempo en el
repositorio sin usarse en esta línea: `MapChain.reqSatisfying_of_pairwiseOwned`.

```lean
theorem ownerChained_filterAllAgg_of_reqSatisfying (P : GPathM) (reqOf : NodeId → List NodeId)
    (d : NodeId) (htop : TopSingleId P d) … (ho : OwnerChained P) :
    OwnerChained (filterAllAgg P (reqOf d))
```

Para **cualquier** `d`, los tres requisitos de una cláusula incluidos. Tres frases:

1. la **cima** del estado lleva un solo id de mapa, el del envío (`TopSingleId`), así que toda cadena
   del estado elige `d` allí — en la cima no hay elección;
2. **una cadena satisface los requisitos de todo nodo que elige**: la posesión por pares mete
   `sel(req.step)` en la tabla de `sel(k)`, y `ReqFiltered` dice que esa tabla, en el paso del
   requisito, **solo contiene el requisito**;
3. luego la cadena satisface `reqOf d`, y `ChainSound_filterAllAgg` la pasa al otro lado entera.

Dicho en tus términos: **el filtro de un envío no elige nada, propaga lo que la cima ya fijó.** Los
tres requisitos de una cláusula son *consecuencia* del nodo de cláusula al que se envía; cualquier
camino que llegue a ese nodo los cumple ya. No hacía falta ninguna terna porque no había nada que
dirigir.

Subsume `ownerChained_filterAllAgg_var` y `_top`: cubre **todos** los filtros de envío.

---

## 4. El pin del lector, y la unificación

El pin del lector no es de esa forma —`mid` no es requisito de ningún nodo que la cadena elija—, así
que hubo que atacarlo aparte. Dos reducciones, la segunda decisiva.

**Primera** (`pinPairChained_of_tablesSound`): el pin del lector sale de `TablesSound` del estado que
se pincha. La clave es no pedirle a la cadena que pase por el pin, sino **elegir el testigo del pin
dentro de la tabla del superviviente**: si `q` sobrevive, su tabla lleva el requisito
(`reqs_in_owners`, que no necesita nada del punto fijo), esa entrada estaba ya allí antes del pin
porque las tablas solo encogen, y `TablesSound` convierte el par en una cadena que pasa por los dos.

**Segunda** (`ownerChained_of_tableChainOwned`): y mejor todavía, porque no pide cadena por un
**par** sino solo por el nodo. `Threaded` ya demuestra que **la tabla de todo nodo vivo contiene una
cadena entera** —enlazada de padre a hijo, del paso 0 a la cima, y que pasa por el propio nodo—. Lo
único que esa cadena no trae demostrado es que sus nodos **se posean entre sí**, y el docstring de
`Threaded` lo dejó escrito hace mucho: *«That is now the whole of the residue.»*

Con eso, el hueco del lector **es** el residuo de `Threaded`. No son dos frentes.

Y una de las dos hipótesis que `Threaded` dejaba abiertas **se paga sola**: la simetría de tablas la
da `AggOk` (`ownSymmetric_of_reviewed`, cierre `[propext]`) — uno de los dos tests que tu barrido
agresivo aplica a cada par de owners.

---

## 5. Lo que ya está demostrado de `TableChainOwned`

**Los pares contiguos, en las dos direcciones** (`pairwiseOwned_of_distant`):

* hacia arriba, `IsChain` dice que `sel i` es **padre** de `sel (i+1)` y `Bridge.LinksInOwners` dice
  que los padres están en la tabla;
* hacia abajo, la simetría de tablas lo devuelve.

**Y los pares a cualquier distancia donde la tabla anfitriona no ofrece elección**
(`mem_owners_of_singleAt`), y ahí `AggOk` lo paga entero:

1. `sel j` está en la tabla de `a`, así que `AggOk` da `sharesEveryStep` entre las dos tablas;
2. `sel j` es válido, luego su tabla **tiene** entrada en el paso `i`, y el cruce obliga a que
   **algún** owner de `a` en `i` esté también en la de `sel j`;
3. y si en `i` solo hay uno, **ese alguno es `sel i`**.

Es el mecanismo que cerró el 90,4 % de los pines en `realizes_pin_of_singleId`, una planta más
arriba: allí la unicidad estaba en el paso del pin, aquí en el paso del par. Y usa el **segundo**
test de tu barrido, `sharesEveryStep`, que llevaba toda la sesión sin pagar nada.

### Cuánto cubre

Sonda `row-degree tcsingle`, sobre las mismas cadenas que mide `tablechain`:

| corpus | pares | cerrados por teorema | residuo |
|---|---|---|---|
| `dos_de_tres.cnf` | 11.388 | **10.848 (95,2 %)** | 540 |
| 3 aleatorias, 4+ vars | 183.462 | **161.582 (88,0 %)** | 21.880 |

---

## 6. La medida del enunciado que queda

Es la primera vez que `TableChainOwned` se mide directamente, y sale limpio. Sonda
`row-degree tablechain`: construye la cadena —descenso ávido por enlaces de padre sin salir de la
tabla de `a`— y comprueba todos sus pares.

| corpus | tablas | el descenso llega al paso 0 | pares | fallos |
|---|---|---|---|---|
| `dos_de_tres.cnf` | 73 | **73 (100 %)** | 11.388 | **0** |
| 3 aleatorias, 4+ vars | 347 | **347 (100 %)** | 183.462 | **0** |

**194.850 pares y ni una excepción**, y el descenso no se atasca nunca — la construcción de
`Threaded` funciona en el 100 % de las tablas.

Y no es trivial, porque la versión fácil **es falsa**: la tabla de un nodo **no** es una clique
(sonda `row-degree clique`: 1.236 de 15.496 pares no se poseen, 7,9 %, y 216 de los fallos entre
pasos contiguos). El enunciado depende de que la cadena esté **enlazada por padres**, que es
exactamente lo que tu review mantiene con `coherent_parents`.

---

## 7. Las tres hipótesis mías que cayeron

Y esto va aquí porque es el patrón de la sesión, no una nota al pie.

| hipótesis | medida | qué resultó |
|---|---|---|
| `AncOwned` (todos los ancestros son owners) | **falsa**, 22,8 % de las fusiones | tras un `doJoin` la relación *padre* sobreaproxima mientras la tabla se queda exacta |
| `PairChained` (dos entradas vivas cualesquiera en una cadena) | **contradictoria** en el mismo paso | dos entradas de un paso con ids distintos son alternativas |
| `HopDown` (lo que un padre posee, lo posee el hijo) | **falsa**, 16/484 y 16/6.100 | el **barrido agresivo** quita al hijo entradas que el padre conserva |

En los tres casos el fallo **no es un defecto de la máquina**: es que yo le pedía más de lo que hace
falta. El tercero es el más instructivo — la tabla del hijo acaba siendo **más pequeña, es decir más
exacta**, que la unión de las de sus padres. La inclusión falla en la dirección buena, y eso dice por
dónde no ir: no hay que empujar owners hacia abajo desde los padres, hay que construir la cadena
**dentro** de la tabla del hijo. Que es lo que hace `Threaded`.

---

## 8. Lo que falta, en una frase

> En la cadena que vive dentro de la tabla de un nodo, dos nodos **a distancia ≥ 2** se poseen,
> **cuando la tabla anfitriona ofrece dos valores en el paso de uno de ellos.**

Eso es el 4,8 % / 12,0 % de los pares. Todo lo demás de la escalera está cerrado, y el enunciado es
geométrico, local, y medido sin una sola excepción en 194.850 casos.

---

## 9. Sondas nuevas de esta sesión

Todas en `lean_project/Probes/RowDegree.lean`:

* `hopdown`, `hopdown2` — la regla del `up` como invariante del estado. **Niegan** la hipótesis.
* `clique` — ¿es la tabla de un nodo una clique bajo la posesión? **No** (7,9 %).
* `tablechain` — `TableChainOwned` sobre la cadena enlazada por padres dentro de la tabla.
  **Se cumple**, 194.850 pares, 0 fallos.
* `tcsingle` — cuánto de eso cubre `mem_owners_of_singleAt`. **88–95 %**.
