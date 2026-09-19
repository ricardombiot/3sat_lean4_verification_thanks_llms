# Verificación para el Autor v152: lo que aporta el review en la fila de cláusula

Ricardo, soy Claude (Opus 5). Seguí el paso que propuse en v151: escribir, en términos de asignaciones,
qué aporta el review cuando se envía a una fila de cláusula. Aquí van el resultado y lo que queda.

Rama `spaik`, build de `AbsSat` (224 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Módulo nuevo:
`ClauseReview.lean`.

---

## 1. El núcleo sin la fila: `ClauseGlue`

En un envío desde la clave p (paso m) a la fila d de la cláusula j (paso m+1), la máquina fija los tres
valores de los literales de d y hace el review. Llamo **F** a ese estado (`pinnedAt`); el estado enviado es
F con d encima.

> **`ClauseGlue`**: toda entrada x → q de F (con q en un paso de literal) se explica por **una** solución
> parcial (cláusulas por debajo de m+1) que pasa por p, x y q y **toma los tres valores de d**.

La fila d ya no aparece como nodo: solo cuentan sus tres valores.

| resultado | contenido |
|---|---|
| `extend_genuine` | una solución parcial con los valores de la fila satisface su cláusula (el mapa no construye la fila toda falsa) y su rama pasa por d |
| `clauseWitness_of_glue` | `ClauseGlue ⟹ ClauseWitness` (incluido el nodo nuevo de arriba, que posee exactamente los nodos de F) |
| `sat_of_clauseGlue` | **el veredicto bajo `ClauseGlue`** |

## 2. Lo que aporta el review, sin hipótesis: `clause_review`

En el mismo envío, sobre F:

1. **Fijaciones**: en los pasos de los literales de d, F solo tiene los valores fijados.
2. **Pares**: todo nodo de F tiene una entrada hacia cada valor fijado, y toda entrada con un extremo en un
   paso de literal se explica por una solución parcial que pasa por p (`Explained`,
   `explained_of_realizes`).
3. **Triángulos**: toda entrada tiene, **en cada paso** por debajo de la clave, un nodo que posee a sus dos
   extremos y es poseído por ambos.

Dicho con asignaciones: el review cierra la relación "compatibles por pares" entre soluciones parciales
bajo triángulos (consistencia de caminos), y las fijaciones de d están dentro de esa relación. Esta es la
versión con fijaciones de `entry_witness`, ahora sobre el estado del envío y no solo sobre el del lector:
en cada cláusula anterior hay una fila viva común a x, q y a cada literal fijado.

## 3. Lo que queda: el pegado

```
veredicto ⇐ ClauseGlue ⇐ ?
   ├─ pares explicados por soluciones parciales    ✔ clause_review (2)
   ├─ triángulos en todos los pasos                ✔ clause_review (3)
   ├─ fijaciones dentro de la relación             ✔ clause_review (1)
   └─ de pares y triángulos, una sola solución     ✘ abierto
```

Tal cual, el último paso no basta: la consistencia de caminos no implica una solución común para CNF
arbitrarias. Lo que el review da es local; el pegado tiene que venir de la historia.

## 4. La propiedad de la historia que propongo

Las tres fijaciones de d caen en pasos de literal, es decir, en variables. Cuando la ejecución estaba en ese
paso, **esa variable era la clave**: fijar su valor entonces es fijar el paso más alto, y eso ya está
demostrado gratis (`soundAt_pin_top`). Así que el pegado sale si **fijar conmuta con la historia**: fijar
un valor en el estado de ahora es lo mismo que haber seguido solo la parte de la ejecución con esa clave.
En esa sub-ejecución todo lo demostrado (conservación, `SoundAt`, `owns_iff_witness`) se aplica igual, y
en su estado las entradas vuelven a explicarse por soluciones parciales, que ya toman el valor fijado.

Tus sondas ya lo midieron en dos formas: v124 (fijar el estado final = ejecutar la máquina sobre la rama
de esa fijación; 1.725 fijaciones con tablas idénticas) y v138 (envío y review distribuyen sobre la unión;
0 diferencias en ~90k casos). En Lean está `OraclePath.sat_of_oracle`, el veredicto bajo `SendDistrib` y
`ReviewDistrib`. El paso siguiente es enlazar las dos líneas: demostrar `ClauseGlue` a partir de la
conmutación, fijando una variable cada vez (`SeqPin` ya reduce varias fijaciones a una tras otra), y
después atacar la conmutación en su forma más pequeña: una fijación a través de una unión por clave.
