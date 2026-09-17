# Verificación para el Autor v122: con los extremos cubiertos, el soporte es consistencia de pares en la rebanada

Ricardo, soy Claude (Opus 5). Con tu barrido simétrico en todos los pasos (v121), la obligación que
quedaba se concreta mucho. Este tramo demuestra que las tablas coinciden con la adyacencia de los
caminos del mapa, mide que el soporte de una rebanada se alcanza en **una sola ronda**, y reduce la
validez del veredicto a una única propiedad estática: la **estabilidad de la consistencia de pares
dentro de la rebanada** (`SpcStable`).

Todo en la rama `spaik`, en el build de `AbsSat` (242 jobs con la sonda), sin `sorry`, en
`[propext, Quot.sound]`.

Corrección a v121: en Julia los rangos empiezan en 1, así que tu barrido ya recorría todos los pasos.
Mi comentario sobre el paso 0 era un error; está corregido en v121.

---

## 1. Las tablas son la adyacencia de los caminos (`AdjacentOwners.lean`)

La máquina construye caminos parciales del mapa: un nodo es una arista (su `parent_id` es el nodo del
mapa anterior, `PMP`). En los estados del lector:

- **`owners_below_iff_parents`**: los owners de un nodo en el paso de **abajo** son **exactamente** sus
  padres;
- **`owners_above_iff_sons`**: los owners en el paso de **arriba** son **exactamente** sus hijos;
- **`reader_adjacent_owners`**: los dos hechos, en todo estado que visita el lector desde un estado
  final de la máquina.

La prueba usa la coherencia del review con padres e hijos, que un nodo solo es owner de sí mismo en su
propio paso (`OOS`), que los enlaces son owners, y que un hijo lista a su padre (`PMS`).

## 2. El soporte se alcanza en una ronda (`helly rounds`, condiciones nuevas)

La sonda de rondas aplica ahora las condiciones de `Sup` del barrido nuevo: pares en todos los pasos
y simetría.

| familia | fijaciones | rondas | pares eliminados en la ronda 0 | por padres o hijos | en la ronda 1 | nodos perdidos |
|---|---|---|---|---|---|---|
| Tseitin K4 par | 88 | 1 | 18.272 (todos por pares) | **0** | **0** | **0** |
| `par_k3_direct_asc_fresh` | 73 | 1 | 3.818 (todos por pares) | **0** | **0** | **0** |

Con el barrido antiguo, los pasos extremos necesitaban hasta 8 rondas más (v120). Ahora no: **el mayor
soporte es exactamente `SPC`**. Es decir, `v` es owner de `x`, los dos están en la rebanada, y en cada
paso tienen un owner común que también está en la rebanada.

## 3. La reducción (`SpcSupport.lean`)

- **`Spc g mid x v`**: consistencia de pares dentro de la rebanada de `mid`.
- **`SpcStable g mid`**: todo par `Spc` tiene, en cada paso, un testigo común que es `Spc` con los dos
  extremos.
- **`supported_of_spcStable`** (**demostrado**): en un estado del lector, si `Spc` es estable, la
  rebanada tiene soporte. Cada condición de `Sup` sale así:
  - pares: la estabilidad misma;
  - simetría: las tablas son simétricas (`AggOk`, v121);
  - padres e hijos: el testigo estable en el paso vecino es owner allí, luego es padre o hijo
    (sección 1);
  - cobertura: un miembro y su portador de `mid` son `Spc`, porque todo owner común de los dos es
    owner del portador y por tanto está en la rebanada. La estabilidad sobre ese par da un owner `Spc`
    en cada paso.
- **`sat_of_someSpcStable`** (**demostrado**): el veredicto SAT de *Improves* es correcto si en cada
  estado del lector con elección hay alguna fijación cuya rebanada tiene `Spc` estable.

## 4. Medido: la estabilidad se cumple, pero no con cualquier testigo (`helly hered`, todos los pasos)

| familia | pares `Spc` | testigos | testigos que no sirven | casillas sin ningún testigo que sirva |
|---|---|---|---|---|
| Tseitin K4 par | 189.520 | 6.401.984 | 410.304 | **0** |
| `par_k3_direct_asc_fresh` | 448.833 | 19.907.161 | 197.198 | **0** |

## 5. La cadena, tal como queda

```
estado final de pureRunW                           MInv (+ SMP, PMS, SN)         demostrado
  estados del lector: resultados de reviewAgg      AggOk: simetría y pares       demostrado (v121)
  las tablas son la adyacencia de los caminos      owners_below/above_iff        demostrado (v122)
  en cada estado con elección, alguna fijación     SpcStable                     medido, abierto
  con Spc estable
    ⇒ la rebanada tiene soporte                    supported_of_spcStable        demostrado (v122)
    ⇒ la fijación es exacta y válida ⇒ PickSomeAgg                               demostrado
    ⇒ el lector acaba en un camino ⇒ modelo de φ                                 demostrado (v116)
```

## 6. Lo que queda, y por qué es el núcleo

`SpcStable` es la única pieza abierta. Hay que decir con claridad lo que implica:

- **No se sigue solo de la consistencia local.** Un estado abstracto con cuatro pasos de tres valores y
  compatibilidad "valores distintos" (K4 con 3 colores) cumple la simetría, la consistencia de pares y
  la coherencia, y en él una fijación vacía su rebanada. Para demostrar `SpcStable` hay que usar que
  las tablas vienen de **caminos del mapa construidos paso a paso**, no solo sus propiedades locales.
  La sección 1 es el primer hecho de ese tipo.
- **Se cumple si toda relación de owners está realizada por una cadena.** Si cada par `x`, `q` de owners
  está en una cadena completa de la tabla (`ChainSound`), entonces la fijación de `q` conserva esa
  cadena (`ChainSound_filterAllAgg`) y con ella a `x`. Esa propiedad es la versión por pares de
  "estado válido ⇒ hay una cadena", la pregunta de fondo de toda la serie.

Siguiente paso propuesto: medir directamente si cada par de owners de los estados del lector está en
una cadena completa (búsqueda de cadenas en la tabla). Si se cumple, es el invariante por caminos que
falta, y habría que demostrarlo por inducción sobre la construcción de la máquina.
