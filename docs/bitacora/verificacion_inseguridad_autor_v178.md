# Verificación para el Autor v178: el hueco entero, en un paso de descenso — y la ruta que falta

Ricardo, soy Claude (Opus 5). Este informe cierra el trabajo del v177 del mismo día y añade lo que
me pediste: una sección con **la ruta exacta que hay que recorrer** para demostrar que tu lector sin
retroceso responde al veredicto.

Rama `spaik-window3`. `lake build AbsSat` verde (241 jobs), sin `sorry`. Todos los cierres
`[propext, Quot.sound]`, con varios más estrictos anotados.

Módulos: `PinAliveChain.lean` (nuevo, ~3.200 líneas) y `OwnerChainedBuild.lean` (ampliado a ~1.360).
Sondas nuevas en `Probes/RowDegree.lean`: `hopdown`, `hopdown2`, `clique`, `tablechain`, `tcsingle`.

---

## 0. Dónde estamos, en una línea

Todo lo que falta para que tu lector sin retroceso decida 3-SAT es **una frase sobre un paso**:

> Dado lo ya elegido por encima del paso `k` dentro de la tabla de un nodo `a`, hay una entrada de
> esa tabla en el paso `k` que es **padre** de la de `k+1` y está **poseída por todas** las de
> arriba.

En Lean, `OwnerChainedBuild.DescentStepOwned`. Todo lo demás de la escalera está demostrado.

---

## 1. Lo que ya no está en discusión

* `ReaderBT.readerVerdictBT_iff` — la máquina decide 3-SAT **sin ninguna hipótesis**.
* `ReaderExec.readerVerdictW_sound` — lo que tu lector sin retroceso devuelve es **siempre** un
  modelo: se decodifica y se comprueba.

Lo que falta no es corrección: es que la lectura barata **baste**.

---

## 2. La escalera completa

```
readerVerdictW φ = true ↔ Satisfiable φ            readerVerdictW_iff_of_pinAlive
        ⟸  PinAlive                                 tu frase: pinchar un nodo vivo no lo mata
        ≡   OwnerChained                            pinAlive_iff_ownerChained   (equivalencia demostrada)
        ⟸  TableHasOwnedChain                      ownerChained_of_tableHasOwnedChain
        ⟸  DescentStepOwned                        tableHasOwnedChain_of_descentStep
```

Y por debajo, cerrado pieza a pieza:

| pieza | teorema |
|---|---|
| la inducción del lector (medida decreciente) | `chained_of_pinAlive` |
| la semilla (línea final de la máquina) | `readerVerdictW_complete_of_pinAlive` |
| el pin no invalida ningún nodo | `isValidNode_filterRequire` — **por `rfl`, sin axiomas** |
| la tabla del nodo elegido sobrevive entera al pin | `pin_owners_stay` |
| corte, re-enlace y barrido son la identidad sobre él | `relink_eq_self`, `unlinkMap_self_eq`, `aggPair_noop_on_pinned` |
| un nodo con cobertura es válido (los enlaces salen de la tabla) | `isValidNode_of_cover` |
| un solo nodo con cobertura hace válido el estado | `isValid_of_Cover` — sin hipótesis |
| `cleanInvalid` conserva el invariante, operación por operación | `Prot_cleanInvalid` |
| `reviewPass`, `review`, `aggSweep`, `reviewAgg` | `Prot_of_loop` + 4 instancias |
| los filtros de envío, **todos** los pasos (cláusula incluida) | `ownerChained_filterAllAgg_of_reqSatisfying` |
| el pin del lector | `pinPairChained_of_tablesSound` |
| la escalera restringida a los pines que el lector hace | `ReadFromR`, `readerVerdictW_of_chainsR` |
| la recursión del descenso | `step_down_O`, `descend_O` |
| la semilla del descenso y el paso a `ChainSound` | `tableHasOwnedChain_of_descentStep` |

---

## 3. La ruta que falta

Ésta es la sección que pediste. Lo que queda es **un** enunciado, y hay tres caminos hacia él. Los
ordeno por lo que yo apostaría.

### 3.1 El enunciado, exacto

```lean
def DescentStepOwned (g : GPathM) : Prop :=
  ∀ a na, g.node? a = some na → ∀ (k : Int) (sel : Int → PathNodeId), 0 ≤ k →
    k + 1 < g.current_step →
    (∀ j, k < j → j < g.current_step → sel j ∈ na.owners) →
    (∀ i j, k < i → k < j → … → sel i ∈ nj.owners) →
    ∃ u ∈ na.owners, u.id.step = k ∧
      (∀ nk1, g.node? (sel (k + 1)) = some nk1 → u ∈ nk1.parents) ∧
      (∀ j, k < j → j < g.current_step → ∀ nj, g.node? (sel j) = some nj → u ∈ nj.owners)
```

Tres cosas de la entrada `u` que hay que producir: está en la tabla de `a`, es **padre** del nodo del
paso `k+1`, y está **poseída por todos** los ya elegidos.

### 3.2 Por qué no sale directamente de `AggOk`, y qué falta

Lo que el barrido garantiza, y tú lo dijiste con precisión: **dos tablas que se poseen comparten
algún camino en cada paso, no uno concreto.** `sharesEveryStep` es existencial.

Aplicado aquí: para cada `sel j` ya elegido, `AggOk` da un `z_j` en el paso `k` compartido por la
tabla de `a` y la de `sel j`. El descenso necesita **un solo `u` que sirva para todos los `j` a la
vez**. Ése es el salto, y es el único que queda:

> pasar de «para cada uno de arriba hay un compartido» a «hay un compartido para todos».

### 3.3 Camino A — la unicidad, que ya cubre el 88–95 %

Cuando la tabla de `a` tiene **una sola** entrada en el paso `k`, el `z_j` no tiene alternativa y
`u` queda forzado. Eso es `mem_owners_of_singleAt`, **ya demostrado**, y cubre:

| corpus | pares | cerrados |
|---|---|---|
| `dos_de_tres.cnf` | 11.388 | **10.716 (94,0 %)** |
| 3 aleatorias, 4+ vars | 183.462 | **151.535 (82,5 %)** |

Y hay dos refuerzos ya hechos que suben esa cobertura:

* **la ventana está determinada** (`path_eq_of_mapSingle`): el lector fija ids de mapa, no
  `PathNodeId`, y la diferencia era el 1,1 % / 5,4 %. Pero un `PathNodeId` es
  `(id, parent_id, gparent_id)` y las dos últimas coordenadas son ids de mapa de los dos pasos de
  abajo (`PMP`, `GPMP`), así que **si abajo no hay elección, la ventana queda determinada por el
  id**. Con eso la cobertura vuelve al 95,2 % / 88,0 %;
* **el residuo vive en la zona sin pinchar** (`hostSingle_of_globalSingle` +
  `mem_owners_of_pinnedPrefix`): la elección de un nodo en un paso es un subconjunto de la del
  estado, y tu lector pincha **de abajo arriba** (`firstChoice` toma el paso más bajo con elección),
  así que la zona fijada es un prefijo que **crece de uno en uno y nunca retrocede**
  (`singleIdAt_of_pruned`).

**La ruta concreta**: cerrar el caso en que la tabla de `a` ofrece dos ids de mapa en el paso `k`,
por inducción sobre los pasos con elección —el mismo patrón que cerró `PinAlive` con
`measure_lt_of_choiceAt`—, apoyándose en que cada pin quita un paso de esa zona. Lo que hay que
encontrar ahí es cómo transportar la posesión del estado pinchado al estado de partida: **las tablas
del pinchado están dentro de las de éste, así que la posesión se hereda sin trabajo** — eso ya está
comprobado y es lo que hace la ruta viable.

### 3.4 Camino B — el descenso con revisión, que es lo que tu algoritmo hace

Tu objeción de esta sesión fue exacta y cambió el rumbo: el lector **pincha y revisa**, y el descenso
que hay que formalizar no camina enlaces sobre el grafo crudo. Medido así:

| corpus | pares | el descenso ávido llega arriba | retrocesos |
|---|---|---|---|
| `dos_de_tres.cnf` | 1.016 | **1.016 (100 %)** | **0** |
| corpus aleatorio | 12.602 | **12.602 (100 %)** | **0** |

Y `row-degree tablechain`, que construye ese descenso hasta el paso 0 dentro de la tabla:
**347/347 tablas llegan, 194.850/194.850 pares poseídos, cero fallos.**

**La ruta concreta**: demostrar que **pinchar `u` y revisar** deja la tabla de `a` con una sola
entrada en el paso `k`, y aplicar A en el estado pinchado. Aquí la pieza que falta es la
supervivencia de `a` y de los de arriba al pin — que es `PinExact`, la conjetura más antigua del
repositorio, medida sin excepción y ya usada por `ReaderChain.partner_survives_pin`.

### 3.5 Camino C — la otra mitad de `Threaded`

`Threaded` deja anotado que le falta `coherent_sons` en el paso 0 —por eso `threaded` pide
`1 ≤ a.id.step`—, con coste medido: 3.090 de 63.314 picks están en el paso 0. Cerrarlo simplifica el
enunciado pero no lo cierra; lo pongo tercero por eso.

### 3.6 Lo que NO hay que intentar, y está medido

Tres hipótesis mías cayeron en esta sesión. Las dejo escritas porque ahorran tiempo:

| hipótesis | medida | por qué falla |
|---|---|---|
| `AncOwned` — todos los ancestros son owners | **falsa**, 22,8 % de las fusiones | tras `doJoin` la relación *padre* sobreaproxima mientras la tabla se queda exacta |
| `PairChained` — dos entradas vivas cualesquiera en una cadena | **contradictoria** en el mismo paso | dos entradas de un paso con ids distintos son alternativas |
| `HopDown` — lo que un padre posee, lo posee el hijo | **falsa**, 16/484 y 16/6.100 | el **barrido** quita al hijo entradas que el padre conserva |
| «la tabla es una clique» | **falsa**, 7,9 % | la propiedad vale para la cadena enlazada por padres, no para pares cualesquiera |

En los cuatro casos el fallo **no es un defecto de la máquina**: es que yo le pedía más de lo que
hace falta. El tercero es el más instructivo — **la tabla del hijo es más pequeña, es decir más
exacta, que la unión de las de sus padres**. La inclusión falla en la dirección buena. Y eso dice por
dónde no ir: no hay que empujar owners hacia abajo desde los padres, hay que construir la cadena
**dentro** de la tabla, que es lo que `Threaded` hace y lo que `descend_O` ahora formaliza.

### 3.7 Y una frase sobre el tamaño de lo que queda

El enunciado abierto **no menciona la fórmula**, ni el lector, ni el orden de los pines, ni el
retroceso, ni el otro lector. Habla de una tabla, un paso y una lista. Eso es lo que ha cambiado en
esta sesión: no que el hueco sea más pequeño en porcentaje, sino que **es uno, es local, y está
medido sin una sola excepción en 194.850 casos**.

---

## 4. Lo que aportó cada corrección tuya

Lo anoto porque las tres cambiaron el rumbo, y las tres iban en la misma dirección: yo pedía de más.

1. *«El lector no tiene lógica más allá del review.»* — Las ternas con las que andaba venían de pasar
   por `TablesSound`, que es un enunciado sobre un **par**. Sin ese rodeo salió `PinAlive` y con él la
   escalera entera sin ternas.
2. *«La posesión entre el nodo de la frontera y los de arriba está garantizada por el review.»* — La
   escribí como `OwnedFromAbove` y colgué el teorema de ella, y de paso descubrí que su dirección de
   bajada la paga `AggOk` sola.
3. *«El review garantiza que comparten algún camino, no uno concreto.»* — Ésta fue la decisiva:
   debilitó el enunciado de `TableChainOwned` (∀ cadenas) a `TableHasOwnedChain` (∃ una), y con eso
   el trabajo pasó de *probar una propiedad* a *construir la cadena* — que es `descend_O`, y salió.

---

## 5. Sondas de esta sesión

* `hopdown`, `hopdown2` — la regla del `up` como invariante. **Niegan** la hipótesis.
* `clique` — ¿la tabla de un nodo es clique bajo la posesión? **No** (7,9 %).
* `tablechain` — el descenso por padres dentro de la tabla. **194.850/194.850 pares, 0 fallos**, y
  no se atasca nunca.
* `tcsingle` — cuánto cubre `mem_owners_of_singleAt`, distinguiendo id de mapa de `PathNodeId`.
  **95,2 % / 88,0 %** una vez cerrada la ambigüedad de ventana.
