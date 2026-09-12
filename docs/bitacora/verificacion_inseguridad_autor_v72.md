# Verificación para el Autor v72: el reductor, formalizado — y sobre las filas de tu propio mapa

Ricardo, soy Claude (Opus 5). Me pediste seguir con la primera de las tres piezas que v71 dejó nombradas: **el reductor de semi-joins en el modelo puro**. Está hecho, en un módulo nuevo, y con más de lo que esperaba: no solo las definiciones, sino la conservación, la terminación y la arco-consistencia, todas demostradas y sin hipótesis.

Lo importante en una frase: **la mitad del argumento clásico que no necesita aciclicidad ya no es una analogía con tu máquina, es un teorema del modelo puro, escrito sobre la codificación de filas del propio mapa.**

---

## 1. La decisión de diseño que hace que esto valga

Podría haber inventado una representación cómoda para las relaciones. No lo he hecho: **las filas de este módulo son las de `CnfMap`** — los índices `1..7`, con `b1`/`b2`/`b3` leyendo qué literal nombra verdadero cada bit. La fila `0`, la de los tres literales falsos, es la única que el mapa no construye, y es exactamente la fila de una asignación que incumple la cláusula (`mem_allRows_of_bits`).

Eso importa para la tercera pieza. Cuando haya que cruzar de vuelta a una cadena del grafo, no habrá que traducir entre dos codificaciones: la fila que el reductor conserva **es** el índice del nodo de cláusula que la máquina mantiene vivo.

Y de paso apareció un detalle que el modelo tenía que decir y no decía: `WF` pide pasos distintos, no variables distintas, así que `x ∨ ¬x ∨ y` es una cláusula legítima y algunas de sus siete filas fijan la misma variable dos veces de forma contradictoria. `rowOk` las descarta. No es cosmético: sin eso, «fila» y «asignación parcial» no serían lo mismo.

## 2. Lo demostrado (`AbsSat/GraphMap/CnfReducer.lean`)

**La fila de una asignación se lee de vuelta como la asignación.** `b1_bits`/`b2_bits`/`b3_bits` (ocho casos concretos que comprueba el kernel), `varOfLit_bitOf`, y de ahí `mem_rowPairs_rowOfAssign`: *todo par que la fila de una solución fija es el valor que esa solución le da a esa variable*. De ahí sale gratis lo que hace falta después: **dos filas de solución nunca se contradicen** (`pairsAgree_rowOfAssign`), porque las dos solo saben informar de la misma asignación.

**Conservación — el reductor nunca tira una fila que una solución usa.**

```lean
theorem Carries_sweep (a : Assign) (rels : Rels) (h : Carries a rels) : Carries a (sweep rels)
theorem rowOfAssign_mem_reduce (a : Assign) (C : List Clause) (h : ∀ c ∈ C, SatClause a c) :
    ∀ cr ∈ reduce (initRels C), rowOfAssign a cr.1 ∈ cr.2     -- [propext, Quot.sound]
```

Tiene la forma de todas las leyes de conservación de este desarrollo, y me gustó verla salir así: el testigo viene de fuera y la maquinaria solo tiene prohibido destruirlo. El paso clave no necesita **nada** de la fórmula — la pareja que una fila de solución necesita en otra relación es la fila que **la misma** solución usa allí.

Corolario, `reduce_ne_nil_of_sat`: **un prefijo satisfacible nunca deja una relación vacía.** Dicho al revés, que es como se usará: una relación vacía es una prueba de insatisfacibilidad, nunca un artefacto del reductor.

**Terminación — y esto no es burocracia.** `totalRows_sweepWith_lt`: una pasada que cambia algo quita al menos una fila. Con eso, `sweep_reduceGo` y `sweep_reduce`: **la reducción alcanza el punto fijo**. Sin este teorema, el de abajo se quedaría apoyado en una hipótesis que nadie descarga, que es justo el tipo de hueco que este proyecto no se permite.

**Arco-consistencia, sin condiciones.**

```lean
theorem arcConsistent_reduce (rels : Rels) :
    ∀ cr ∈ reduce rels, ∀ r ∈ cr.2, ∀ q ∈ reduce rels,
      ∃ w ∈ q.2, pairsAgree (rowPairs cr.1 r) (rowPairs q.1 w) = true   -- [propext, Quot.sound]
```

Toda fila superviviente tiene pareja en todas partes. Es la premisa que pide Beeri–Fagin–Maier–Yannakakis, y es el mismo enunciado que `ArcConsistency.review_arcConsistent` ya demuestra de las tablas de owners de tu máquina — ahora también del lado de las fórmulas, y con el mismo apoyo incondicional.

`reduce_sound` junta las dos mitades en un enunciado.

Un apunte de higiene, porque costó encontrarlo: `beq_self_eq_true` arrastra `Classical.choice` al cierre para este tipo compuesto. `reduceGo` usa igualdad decidible (`=`) en vez de `==`, y con eso todos los cierres quedan en `[propext, Quot.sound]`.

## 3. Medido: la banda corre el reductor **del modelo**, no otro

Modo nuevo, `lake exe cnfmap --reducer`. No es una segunda implementación: llama a `CnfReducer.reduce`, el que los teoremas describen. Para cada prefijo de cada fórmula compara con fuerza bruta.

| cinco semillas, 1.000 fórmulas, 3–7 variables | prefijos | UNSAT | **vació un prefijo SAT** | UNSAT no detectado |
|---|---|---|---|---|
| **dentro de la clase** | 2.310 | 39 | **0** | **0** |
| fuera | 14.039 | 688 | **0** | 9 |

Dos lecturas, y las dos valen:

**La primera columna en negrita es la banda del teorema.** `reduce_ne_nil_of_sat` dice que no puede pasar; la medición dice que no pasa, en 16.349 prefijos. Eso no añade confianza al teorema —está demostrado— sino a que **las definiciones dicen lo que los teoremas creen que dicen**, que es lo que una banda comprueba en este proyecto.

**La última columna es el enunciado de la pieza siguiente.** Dentro de la clase, los 39 prefijos insatisfacibles fueron detectados por una relación vacía, los 39. Fuera, 9 de 688 se escapan. Y el control es el mejor posible:

| control Tseitin | prefijos | UNSAT no detectado |
|---|---|---|
| K4 / K3,3 / prisma, paridad **impar** (UNSAT) | 17 / 25 / 25 | **1 cada una** |
| las mismas, paridad par (SAT) | 17 / 25 / 25 | 0 |

El prefijo que se escapa en cada fórmula impar es **la fórmula entera**: la consistencia de arcos no ve la contradicción de paridad. Es exactamente el fallo clásico, reproducido en tres familias, y es la razón por la que la pieza 2 necesita la aciclicidad y no puede salir gratis.

## 4. Dónde queda esto

De las tres piezas que v71 dejó nombradas, la primera está cerrada. Las otras dos siguen abiertas y no han cambiado de forma:

2. **El no-retroceso bajo `BoundedScope`**: dentro de la clase, una relación vacía equivale a insatisfacible — o, en la forma que hace falta, tras el reductor la elección golosa no se atasca. La medición de arriba ya dice cuál es el enunciado y que aguanta; la inducción desciende sobre `gyoIter_eq_nil_of_BoundedScope`, que v71 dejó demostrado.
3. **El puente de vuelta**: de la asignación reparada a una cadena sonora de *ese* estado que pase por *ese* nodo.

Y sobre el caso general, que dijiste que quedara aplazado y no descartado: esta pieza no lo toca, pero tampoco lo estorba. La conservación y la arco-consistencia valen para **toda** fórmula — no piden aciclicidad en ningún sitio. Lo único que la clase tendrá que pagar es la pieza 2.

Build: `lake build AbsSat` verde, **98 módulos**, 0 `sorry`, 0 axiomas de proyecto.
