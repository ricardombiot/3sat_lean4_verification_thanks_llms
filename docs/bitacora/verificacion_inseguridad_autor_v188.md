# Verificación para el Autor v188: `PairHelly` paso a paso, y el testigo que sobrevive

Ricardo, soy Claude (Opus 5.5). Este informe sigue al v187, que midió el Helly de un paso y propuso
binarizar las cláusulas. Aquí se cuenta qué se ha formalizado desde entonces (las cuatro piezas del
v187), dónde se paró cada una y por qué, y un giro: **la historia del lector da el testigo sin Helly**,
y lo que queda es por qué sobrevive.

Rama `pair-mode`. Módulo `lean_project/AbsSat/GraphPath/Model/OneStep.lean`; sondas `onestep` y
`tri3x` en `Probes/RowDegree.lean`. `lake build AbsSat` verde (272 jobs), sin `sorry`, axiomas
`propext` y `Quot.sound`. Commits `a60a4fc` … `595721b`.

---

## 1. Las piezas 1 y 2: demostradas

* **Pieza 1** (`segGood_of_oneStep`, `pairHelly_of_oneStep`): si todo tramo se alarga un paso en cada
  dirección, repitiendo se cubren todos los pasos y vale `SegGood`, luego `PairHelly`. Directo, sin
  pasar por `SegThroughPin`.
* **Pieza 2** (`helly_two`, `extUp_of_two`, `extDown_of_two`): con uno o dos candidatos, Helly es un
  lema de dos elementos. Enunciado sin lógica clásica (hubo que cambiar un lema de listas de la
  biblioteca que metía `Classical.choice` por una inducción).

## 2. La pieza 3 (cláusulas con 3+ candidatos): reducida, y una corrección

* **Demostrado**: `helly_box` (cajas que se cortan dos a dos: cada literal es un Helly de dos valores;
  con un candidato vivo en la intersección, es común a todos) y `extUp_of_boxes`.
* **Demostrado, en general**: `req_shared`. Si `u` posee a `r`, la tabla de `u` contiene cada nodo que
  `r` requiere. Sale de `ReqFiltered` (invariante de la máquina) y de la regla de parejas. Es la mitad
  «⊆» de las cajas.
* **Corregido por la medición**: la caja leída de la tabla literal a literal **no** es `B_u`. En 30 de
  463 casos (semilla 7) es mayor: la tabla admite `x1 = 0` pero el miembro no posee la fila `001`, por
  una exclusión exacta a través de otras variables. Lo que sí vale siempre es que `B_u` es una caja con
  sus propias coordenadas; la hipótesis que queda (`BoxHellyUp`) lo dice de forma existencial.

## 3. La pieza 4 (el triángulo con el extremo): reducida a un trío

* **Demostrado**: cuando el extremo es uno de la pareja (`triTopUp_of_inner`, `triTopDown_of_inner`).
  La regla da una entrada común en el paso contiguo, y las entradas del extremo allí son sus hijos
  (I1-hijos) o, abajo, los padres del extremo inferior (I1).
* **Reducido** (`triTop_of_tri3`): las parejas de miembros interiores, a **`Tri3` en el paso contiguo
  al extremo**. Tres nodos que se poseen mutuamente, uno el extremo, comparten entrada en el paso de al
  lado. Medido tras `cleanPair`: 5,34 millones de tríos, sin fallos (con una muestra de 40 nodos y 12
  vecinos por estado).

**Por qué no se puede cerrar localmente.** La regla de parejas es consistencia de caminos: cada
pareja tiene un tercero compatible en cada paso. `Tri3` es el nivel siguiente, un cuarto para cada
trío. En 3-SAT uno no implica el otro. Y con tablas de parejas la máquina no puede guardar ni filtrar
una incompatibilidad de tres, porque ninguna pareja es la culpable. Estas piezas tienen que venir de
**la historia** del estado, no de un estado solo.

## 4. El giro: el testigo viene de la historia

Mediciones (`tri3x`, semillas 1 y 7, 33.403 tramos tras `cleanPair`):

| | medido |
|---|---|
| tramos sin testigo en el estado del lector `g` | 0 |
| tramos en que el pin mata **todos** los testigos de `g` | **0** |
| tramos en que la regla le quita un testigo vivo a un miembro | 58, siempre con otro que queda |
| con dos hijos vivos: un miembro admite solo uno | 47 % |
| … la exclusión ya estaba en `g` | 99,5 % |
| … dos miembros con un solo hijo cada uno, distintos | **0** (de 48.578) |

El **testigo** de un tramo es un hijo de su extremo que todos los miembros poseen. En `g` existe
siempre, y eso **está demostrado sin Helly**:

* `witUp_of_segExact`, `witDown_of_segExact`: el tramo es tramo de `g` (`seg_before`); con `SegExact`
  se extiende a una cadena completa, y su nodo del paso siguiente (o anterior) es el testigo;
* `witUp_of_segGood`: lo mismo con solo `SegGood`, que es lo que la escalera da. La entrada común del
  paso siguiente está en la tabla del extremo, luego es un hijo suyo.

Lo que queda es que **alguno de esos testigos sobreviva** en `C` (vivo, enlazado, en la tabla de todos
los miembros): `SurvivesUp` / `SurvivesDown`. Con eso:

```lean
theorem readerVerdictW_iff_of_survives (hStart …)
    (hPin : … → SurvivesUp g C ∧ SurvivesDown g C ∧ CleanRest X ∧ LaterValid X) … :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ
```

(`C = cleanPair X`, `X` el estado pinchado de `g`). **Sin cajas, sin hueco, sin `Tri3`.** La simetría
de `C`, que la extensión necesita, sale del punto fijo del review agresivo de `g`.

Una advertencia honesta: pedir que el testigo sea de `g` hace la hipótesis más fuerte, no más débil,
que decir «el tramo se alarga». Su valor es que ya no es un Helly de muchas tablas, sino una pregunta de
supervivencia sobre nodos concretos.

## 5. Qué testigo sobrevive

La última medición separa **exactamente** a los testigos que sobreviven a la purga de los que mueren:

> **Criterio**: la tabla del testigo en `g` contiene, en el paso del pin, un nodo pinchado que sigue vivo
> y que todos los miembros poseen en `C`.

| | semilla 1 | semilla 7 |
|---|---|---|
| testigos de `g` | 17.315 | 18.644 |
| cumplen el criterio | 16.629 | 18.135 |
| … mueren en la purga | **0** | **0** |
| los que mueren (todos sin el criterio) | 686 | 509 |
| tramos sin ningún testigo con el criterio | **0** | **0** |
| tramos donde fallan todos los que lo cumplen | **0** | **0** |

Así que la supervivencia se parte en tres afirmaciones, cada una más pequeña:

* **(W1) Existe** un testigo con el criterio. Es una afirmación de intersección —un nodo pinchado común
  a los miembros y al testigo—, pero sobre un solo paso, el del pin.
* **(W2) El criterio salva de la purga.** Aquí hay una prueba a la vista: si en `g` cada pareja de una
  tabla está en una cadena completa común (**exactitud de las tablas por parejas**), el testigo `r` y el
  nodo pinchado `p` que posee están en una cadena. Esa cadena pasa por el pin, así que es sana tras el
  pin (`chainSound_filterWeak`) y tras `cleanPair` (`ChainSound_cleanPair`), y `r` sobrevive. Queda
  medir y demostrar esa exactitud por parejas en los estados del lector.
* **(W3) La regla no se lo quita a todos**: 62 testigos con el criterio perdidos por la regla, y nunca
  todos los de un tramo.

## 6. Qué queda, en orden

1. **Medir la exactitud de las tablas por parejas** en los estados del lector (cada entrada de una tabla
   está en una cadena completa con su dueño). Si sale sin fallos, (W2) se demuestra con lo que ya hay.
2. **(W1) y (W3)**, las dos partes que siguen teniendo sabor a intersección, ahora en el paso del pin y
   con un nodo concreto.
3. Pendientes de antes: la regla en el ejecutable IO, la velocidad del modelo para que `diffTest`
   vuelva a pasar, y la adopción en Julia (`PAIR_MODE = :on`).

## 7. Una frase

Pedirle a las tablas que resuelvan un Helly era pedirles información de tríos que no guardan. La
historia sí la guarda: el estado del lector ya tiene, para cada tramo, un testigo. Y el que sobrevive al
pin es justo el que comparte con el tramo un nodo pinchado.
