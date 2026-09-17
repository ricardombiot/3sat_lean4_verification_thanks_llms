# Verificación para el Autor v123: cada par de owners está en un camino

Ricardo, soy Claude (Opus 5). En v122 la validez del veredicto quedó en `SpcStable`, y señalé que
saldría de un invariante de caminos: que cada par de owners esté en una cadena completa. Tu aportación
fue precisamente esa: tras cada UP, el filtro y el review con todas sus fases dejan el `gpath` bien
construido, con cada nodo formando parte de al menos un camino; la coherencia se encarga de eliminar
lo que no lo esté.

Este tramo mide ese invariante en su forma por pares, demuestra lo que da al lector, y demuestra que
el crecimiento de la máquina lo conserva. Tu argumento queda como un único lema abierto.

Todo en la rama `spaik`, en el build de `AbsSat` (243 jobs con la sonda), sin `sorry`, en
`[propext, Quot.sound]`.

---

## 1. Medido: ningún par de owners sin cadena (`helly chains`)

La sonda busca, para cada nodo y cada par de owners (`x`, `w`), una **cadena completa de la tabla**: un
nodo por paso, owners entre sí dos a dos, que pase por los dos. Recorre los estados base de **todas las
líneas** de la máquina y, desde cada uno, **paseos del lector** con fijaciones al azar (3 paseos de
hasta 6 fijaciones).

| familia | estados | nodos | nodos sin cadena | pares de owners | pares sin cadena | búsquedas truncadas |
|---|---|---|---|---|---|---|
| Tseitin K4 par | 756 | 15.854 | **0** | 158.978 | **0** | 0 |
| `par_k3_direct_asc_fresh` | 1.166 | 34.403 | **0** | 498.423 | **0** | 0 |

Las aleatorias (semilla 1001) y los coloreados (K4 con 3 colores, insatisfacible, y K4 menos una
arista) siguen en marcha. Los añadiré cuando terminen.

## 2. Lo demostrado (`PairChain.lean`)

- **`PairChain g`**: todo par de owners de un nodo está en una cadena completa de la tabla
  (`ChainSound`). Con `w = x` contiene "todo nodo está en una cadena" (L6, `SupportedS`).
- **`pinExact_of_pairChain`**: `PairChain` hace **exacta** toda fijación. Un nodo de la rebanada y su
  portador están en una cadena; esa cadena respeta la fijación, así que sobrevive a la fijación y a
  todo el review agresivo (`ChainSound_filterAllAgg`, el resultado de "no se pierde ninguna
  solución"), y el nodo con ella.
- **`sat_of_pairChain`**: si `PairChain` se cumple en los estados del lector, el veredicto SAT de
  *Improves* es correcto.
- **`pairChain_join`**: el `join` conserva `PairChain`. Un owner de un nodo unido viene de uno de los
  dos lados, donde una cadena lo lleva, y las cadenas de cada lado lo son de la unión.
- **`pairChain_addNode`**: **UP conserva `PairChain`**. El nodo nuevo es owner de todos y todos son
  owners suyos, y toda cadena se extiende por él (`ChainSound_addNode`).
- **`FilterKeepsPairChain`**: tu afirmación, como **lema abierto**. Una fijación seguida del review
  agresivo completo conserva `PairChain` siempre que deje el estado válido.
- **`sat_of_pairChain_base`**: con ese lema y `PairChain` en el estado base, el veredicto es correcto.

## 3. La cadena, tal como queda

```
initSeed, UP, join conservan PairChain                             demostrado (v123)
filtro + review agresivo conservan PairChain   FilterKeepsPairChain   medido, abierto
  ⇒ PairChain en el estado base y en todos los estados del lector
  ⇒ toda fijación es exacta                      pinExact_of_pairChain  demostrado (v123)
  ⇒ PickSomeAgg ⇒ el lector acaba en un camino ⇒ modelo de φ          demostrado
```

## 4. Dónde está el trabajo que queda

`FilterKeepsPairChain` es el paso que el programa L6 nunca cerró en su forma por nodos: el review sin
fijaciones conserva "todo nodo en una cadena" (`SupportedS_review`), pero con una fijación una cadena
que pasa por un nodo puede no respetarla, y entonces no sobrevive.

Lo que hay que demostrar, concretamente: si `x` y `w` sobreviven como par a la fijación de `a`,
entonces el estado **anterior** tenía una cadena que pasa **a la vez** por `x`, `w` y un portador de
`a`. Esa cadena respeta la fijación y sobrevive. Por v122, los pares supervivientes son exactamente los
`Spc` de la rebanada de `a` (una ronda), y `PairChain` antes del filtro da cadenas por los tres pares
(`x,w`), (`x,a`) y (`w,a`), pero no una que pase por los tres.

Ese salto de pares a tríos es el que la coherencia tiene que garantizar. No se sigue solo de la
consistencia local: el estado abstracto K4 con 3 colores (v122) es coherente y consistente por pares,
y no tiene ninguna cadena. Por eso la prueba debe usar `PairChain` en el estado anterior, que es la
historia de la construcción, y no solo las propiedades locales del estado filtrado. La adyacencia
exacta (v122: owners en pasos vecinos = enlaces) es la herramienta natural para pegar cadenas paso a
paso.
