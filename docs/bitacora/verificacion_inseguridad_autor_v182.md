# Verificación para el Autor v182: `cleanInvalid` en dos fases, adoptado — y la propuesta de un review simétrico

Ricardo, soy Claude (Opus 5.5). El v181 terminaba con una propuesta (§6): separar `cleanInvalid` en
dos fases. Este informe cuenta cómo se llevó a cabo, en Julia y en Lean, qué ganó la prueba, qué
enseñaron las mediciones de después, y termina con una segunda propuesta en la misma línea: **hacer
simétrico el review**, tomando la idea (no el modelo) de `SymReview`.

Rama `clean-two-phase` (sale de `spaik-window3` en `fcb91fa`). `lake build AbsSat` verde (261 jobs),
sin `sorry`, sin `Classical.choice`. 20 commits desde el v181 (`b62d259`).

---

## 0. Dónde estamos, en una línea

```lean
def reviewPass (g : GPathM) : GPathM :=
  reviewSons (reviewParents (cleanInvalid₂ g))
```

La máquina de Lean ya limpia en dos fases, y la escalera sigue en pie sobre ella:
`readerVerdictW_iff_of_readerSegGood` depende solo de `propext` y `Quot.sound`, y de ningún lema del
`cleanInvalid` secuencial.

## 1. La actualización de `cleanInvalid`

### 1.1 Qué hace ahora

Antes, cada nodo se cortaba con la global **tal como estaba en ese momento**, uno detrás de otro. El
resultado dependía del orden y dejaba en las tablas ids de nodos eliminados más tarde.

Ahora son dos fases:

1. **Purga, hasta el punto fijo**: eliminar los nodos cuya tabla, cortada con la global actual, no
   sería válida; repetir mientras se elimine alguno. Ninguna tabla se toca todavía.
2. **Un solo corte**: cortar la tabla de todos los supervivientes con la global final.

### 1.2 Julia (`julia/improves`)

* `clean_invalid_nodes_two_phase!` detrás del interruptor `GraphPath.CLEAN_MODE`; desde `fcb91fa` es
  el modo **por defecto**. El secuencial sigue disponible.
* `PathDocumentOwners.is_valid_intersect(a, b)` (`f9729e0`): responde lo mismo que copiar la tabla,
  cortarla y mirar su validez, **sin copiar**: basta un id común por paso, y se para en el primer paso
  sin ninguno. Comprobado nodo a nodo contra copia + `intersect!`: 52.476 nodos, 0 diferencias.
* Test de postcondiciones (`test_clean_invalid_two_phase.jl`, en `runtests`): 126 estados pinchados,
  506 comprobaciones. Tras la versión de dos fases: ninguna tabla guarda ids fuera de la global, toda
  la global son nodos, todos los nodos son válidos, y aplicarla otra vez no cambia nada. La secuencial
  deja ids fuera de la global en los 126.
* Comparación diferencial: `test_window` (22 instancias), mismos veredictos y mismas vueltas del
  review, **+1,3 %** de tiempo; en `test_3sat`, mismos veredictos, estados finales y vueltas en todo lo
  recorrido.

### 1.3 Lean

**Las definiciones** están en `GPathM.lean`, junto a `reviewPass`: `cutNode`, `purgeStep`,
`purgeRound`, `purgeFuel`, `cutAll`, `cleanInvalid₂`. Un detalle salió al hacer el cambio: el corte de
un nodo conserva un enlace `x — y` cuando **los dos extremos se admiten**, y los dos se leen por
`node?`, igual que hace la barrida secuencial. Así la condición es simétrica en los dos ids, y la
tabla de padres y la de hijos siguen siendo espejo **sin** pedir que los ids no se repitan.

**Lo demostrado para `cleanInvalid₂`**, cada lema en el fichero de la propiedad que protege:

| propiedad | lema | fichero |
|---|---|---|
| solo estrecha | `pruned_cleanInvalid₂` | `Pruned` |
| la medida no crece; punto fijo | `measure_cleanInvalid₂_le`, `cleanInvalid₂_eq_self` | `Fuel` |
| ids, global = nodos, padres = nodos | `ids_`, `GN_`, `PN_cleanInvalid₂` | `NodeIds`, `GownersNodes`, `Parents` |
| enlaces espejo, sin `NodupIds` | `SMP_`, `PMS_`, `SN_`, `SAbove_cleanInvalid₂` | `Sons` |
| **no se pierde ninguna solución** | `ChainSound_cleanInvalid₂` | `CleanInvalid` |
| conjuntos soportados, tejidos, tramas | `AOk_`, `WOk_`, `FOk_cleanInvalid₂` | `AnchoredSurvive`, `Survive`, `Fabric` |
| contexto del lector | `RCtx_cleanInvalid₂` | `CleanTwoPhase` |
| **sin ids muertos** en las tablas | `owners_live_cleanInvalid₂` | `CleanTwoPhase` |
| **todos los nodos válidos** | `isValidNode_cleanInvalid₂` | `CleanTwoPhase` |

Las dos últimas filas son lo que el secuencial no tenía.

**El cambio de `reviewPass`** (`a88f2de`). Cada `X_reviewPass` se volvió a demostrar con su
`X_cleanInvalid₂`. En el punto fijo del review las propiedades de cada nodo salen ahora directas de la
postcondición: todo nodo es válido y es su propio corte (`review_cut_fixed`). El `cleanInvalid`
secuencial y sus lemas se conservan en el repositorio.

Para saber qué lemas consumía de verdad la escalera, se escribió `Probes/DepsClosure.lean`
(`#deps T "patrón"`), que recorre el cierre de dependencias de un teorema, prueba incluida. La
escalera usaba 14 hechos de `reviewPass`; hoy todos sus lemas de limpieza son los de dos fases.

**Que la máquina no cambia**: la sonda `clean2` compara el review con una copia del secuencial. En las
semillas 1 y 7: 12.944 envíos y 86 pines, **0 estados finales distintos**, antes y después del ajuste
de `cutNode`.

### 1.4 Lo que ganó la prueba: las pasadas sin versiones «vivas»

El v179–v181 tuvo que escribir las pasadas con invariantes **vivos** (`SegGoodL`, `I1L`, `I1sL`),
porque las tablas guardaban ids muertos. `PassPlain.lean` (`b072536`) lo quita del enunciado:

* `OwnLive`: todo owner en un paso dentro de rango es un nodo. Sale de `cleanInvalid₂`
  (`ownLive_cleanInvalid₂`) y lo conservan las dos pasadas, porque no eliminan nodos;
* con `OwnLive`, lo vivo **es** lo simple: `segGood_iff`, `i1_iff`, `i1s_iff`;
* `PStateG`, el estado de la pasada con `SegGood`, `I1`, `I1s` simples: `pstateG_reviewParents`,
  `pstateG_reviewSons`, `pstateG_reviewPass`.

Las pasadas hablan ya del **mismo `SegGood` que la escalera** (`ReaderSegGood`).

## 2. Lo que enseñaron las mediciones de después

### 2.1 `SegGood` vuelta a vuelta (`roundseg`)

En cada vuelta del review agresivo de cada envío y cada pin (semillas 1 y 7, 12 millones de casos
tramo × paso):

* **tras cada vuelta, `SegGood` vale**: 0 tramos sin entrada común;
* toda entrada común de después ya lo era antes (las tablas solo encogen), y **siempre sobrevive
  alguna** (0 fallos);
* pero **no todas**: una entrada común que sigue viva puede dejar de ser común (330 y 459 casos),
  nunca en `cleanInvalid₂`, siempre en las pasadas.

### 2.2 Tu postulado: una entrada solo sale si pierde un nodo común

Tu corrección fue la buena: aunque un nodo siga vivo, puede dejar de ser compatible con otro porque
pierden un nodo común. Medido, excluyendo el propio paso de `r` (con él era una tautología, por `OOS`):
**375 de 375** entradas vivas que salieron de una tabla del tramo habían perdido un nodo común con
algún nodo del tramo en otro paso; 0 salieron siendo compatibles.

`CompatLoss.lean` (`e8664a6`, `6e96c4c`) formaliza el mecanismo local:

* `lost_parents_nosym` / `lost_sons_nosym` (sin hipótesis): si el corte de `x` con la unión de sus
  padres (hijos) le quita `r`, **ningún nodo que `x` conserva en el paso de sus padres (hijos) tiene a
  `r`**;
* `lost_parents` / `sep_of_drop_parents` (y los de hijos): **con simetría de la posesión** antes del
  corte, `x` y `r` no comparten nada en ese paso al salir;
* `Sep.of_pruned`: esa separación dura el resto de la vuelta;
* `owners_other_reviewNode`: `reviewNode x` solo toca la tabla de `x`, así que una tabla solo pierde
  entradas en el paso de su propio nodo.

### 2.3 Dónde se atasca: la simetría a mitad de pasada (`midsym`)

La simetría (`r` tiene a `q` ⇔ `q` tiene a `r`) está demostrada al final del review agresivo, pero **a
mitad de pasada se rompe**: 930 y 440 estados con pares vivos asimétricos (semillas 1 y 7). Pasa
porque el corte escribe «ninguna solución pasa por `x` y `r`» **en un solo lado**: `x` pierde a `r`,
pero `r` sigue teniendo a `x`.

De los 566 eventos de corte, tu postulado vale en todos; la simetría solo decide **dónde**:

* en 401 la separación está en el paso de los vecinos, como dice `lost_parents`;
* en 165 la simetría estaba rota, y la separación aparece **más lejos**: a distancia 2 (44), 3 (21),
  4 (17), 5 o más (12). Baja por la cadena de cortes.

Esa versión recursiva no tiene una prueba sencilla: cada vecino se separa de `r` en un paso distinto.

### 2.4 El lector `ReaderMinOwner`

Tu diseño de lector (restringir al nodo con menos owners y elegir cualquiera) se midió (`minnode`,
`minreader`): restringir a su tabla **nunca invalida** el grafo y casi siempre deja el camino resuelto;
las elecciones que quedan son todas válidas (186 de 186). Pero la tabla del mínimo no es un bloque
compatible cuando hay que elegir (es la unión de varios caminos parciales), así que su corrección
descansa en la misma obligación que el lector actual. Es una mejora de eficiencia, no un atajo de
prueba.

## 3. Propuesta: un review simétrico

### 3.1 La idea

Cuando el review quita `r` de la tabla de `x`, lo que afirma es *ninguna solución pasa a la vez por `x`
y por `r`*. Esa frase es simétrica, pero la máquina solo la escribe en la tabla de `x`. La propuesta:
**cada vez que se borra un owner, borrarlo también en la otra tabla**. Si `x` pierde a `r` y `r` sigue
vivo, `r` pierde a `x`.

La idea viene de `SymReview.lean`. Aquel módulo no representaba bien el review de la máquina, así que
**no se reutiliza**: se toma solo la idea y se aplica sobre la máquina actual.

**No pierde soluciones**: si una cadena solución pasara por `x` y `r`, `r` estaría en la tabla de `x`
(ley de conservación), así que no se habría quitado. El espejo solo borra pares que ninguna solución
usa.

### 3.2 Dónde entra, en Julia

| dónde | qué borra | espejo |
|---|---|---|
| `review_owners_parents_sons!`, `review_owners_sons_parents!` (`intersect!` con la unión de vecinos) | entradas de `x` que ningún vecino tiene | **sí**: aquí nace la asimetría medida |
| `clean_invalid_nodes_two_phase!`, fase 2 | ids que ya no están en la global | **sí**, si el nodo sigue vivo |
| `agressive_consistence_filter!`, rama «inconsistent» | el par `x`–`w` | ya es simétrica |
| la misma, rama «asymmetric» | `w` de `x` cuando `w` no tiene a `x` | con el cambio, no debería dispararse nunca |
| `filter_require!` | solo la global | no toca tablas |
| UP (`graph_path_up.jl`) | la tabla del nodo nuevo | a medir si deja tablas simétricas |

La pieza nueva sería `PathDocumentOwners.intersect_removed!(a, b)`, el mismo corte pero devolviendo los
ids que quita, y `mirror_remove!(gpath, x, removed)`, que borra a `x` de la tabla de cada uno que siga
vivo y marca `review_owners = true`. Detrás de un interruptor, como `CLEAN_MODE`.

### 3.3 Qué gana la formalización

1. **La simetría pasa a ser un invariante de cada paso** (`OwnSymmetric_reviewNode`), no solo del punto
   fijo. Es fácil de demostrar: cada corte escribe los dos lados.
2. **`lost_parents` y `lost_sons` valen en todo corte.** Tu postulado se cumple siempre **en el paso de
   los vecinos**, y S1′ para la vuelta entera se ensambla con piezas ya demostradas (`Sep.of_pruned`,
   `owners_other_reviewNode`), sin la recursión del §2.3.
3. **Desaparecen las hipótesis de las pasadas.** Las dos pasadas enteras están demostradas con una
   única hipótesis cada una: que la simetría local se conserve nodo a nodo (`LocSymStable`,
   `LocSymStableS`). La simetría local (`LocSym`: si una entrada `r` está en la tabla de todos los
   nodos de un tramo, el tramo está en la tabla de `r`) **se sigue en una línea de la simetría global**.
   Con el review simétrico, `pstateG_reviewPass` quedaría **sin hipótesis**.
4. **Una rama muerta menos.** La rama «asymmetric» del filtro agresivo solo existe para reparar
   asimetrías; si ninguna aparece, en la prueba del barrido agresivo esa rama se descarta.

### 3.4 Cómo verificarlo antes de adoptarlo

El mismo camino que con `cleanInvalid₂`:

1. **En el modelo de Lean, medir primero**: una sonda como `clean2` que compare, en `dos_de_tres` y las
   semillas 1 y 7, el review actual con el simétrico: veredictos, estados finales, vueltas, asimetrías
   a mitad de pasada (deberían ser 0) y si UP deja tablas simétricas. **No está garantizado** que los
   estados coincidan: el espejo borra más y puede cambiar estados intermedios del lector. Si los
   veredictos coinciden y los estados no, lo decides tú.
2. **Julia** detrás del interruptor: test de simetría tras cada review, comparación diferencial en
   `test_window` y `test_3sat` (veredictos, vueltas, tiempo).
3. **Lean**: el espejo en `GPathM` junto a `cutNode` y `reviewNode`; volver a demostrar los
   `X_reviewPass` (el espejo solo quita entradas de tablas, así que `Pruned`, la medida, `SMP` y `PMS`
   salen casi directos); `OwnSymmetric_reviewPass`; y S1′ para la vuelta.

### 3.5 Qué no arregla

La parte **colectiva**: que alguna entrada común siga siendo compatible con **todo** el tramo a la vez,
no solo con cada nodo por separado. Es lo que, según tú, garantiza UP por cómo construye los caminos, y
lo que la medición confirma (tras cada vuelta, `SegGood` vale en el 100 % de los casos). El review
simétrico deja S1′ demostrable y quita las hipótesis de las pasadas; el punto de fondo sigue siendo ese.

## 4. Lo que falta

1. El review simétrico (§3), empezando por la medición en el modelo.
2. El ejecutable Lean (`GraphPath.lean`) sigue limpiando en secuencial: pasarlo a dos fases y rehacer
   el espejo con el modelo y con Julia.
3. La parte colectiva: alguna entrada común compatible con todo el tramo sobrevive cada vuelta.
4. El barrido agresivo y el ensamblaje en `reviewAgg` y `ReaderSegGood`.

## 5. Una frase sobre el tamaño de lo que queda

El `cleanInvalid` en dos fases quitó el ruido de los ids muertos, y con él las versiones vivas; el
review simétrico quitaría el de las asimetrías, y con él las hipótesis de las pasadas. Lo que quedaría
es solo la pregunta que siempre estuvo debajo: por qué, entre las entradas comunes de un tramo, **una**
sobrevive siempre compatible con todos.
