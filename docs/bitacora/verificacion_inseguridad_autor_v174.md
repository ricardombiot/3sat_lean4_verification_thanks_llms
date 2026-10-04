# Verificación para el Autor v174: la máquina decide sin hipótesis abiertas, y el hueco restante cabe en una frase sobre tres nodos

Ricardo, soy Claude (Opus 5). Esta sesión fue larga y cambió de forma dos veces, las dos por
objeciones tuyas. El informe intenta ser honesto con lo que salió bien, con lo que salió mal, y con
lo que resultó ser un error de encuadre mío que tú detectaste antes que yo.

Rama `spaik-window3`. `lake build AbsSat` verde (236 jobs), `lake exe runTests` verde, sin `sorry`.
Cierres `[propext, Quot.sound]`, con dos excepciones más estrictas anotadas abajo.

---

## 0. Resumen

* **Lo grande**: `ReaderBT.readerVerdictBT_iff φ hwf : readerVerdictBT φ = true ↔ Satisfiable φ`.
  **La máquina decide 3-SAT sin ninguna hipótesis abierta.** Salió de no tirar una cadena que la
  conservación ya construía.
* **El error de encuadre, tuyo el diagnóstico**: exigir que un lector que *nunca* retrocede acierte
  siempre es exigir que no haya fantasmas, o sea el objetivo entero. La máquina revisa después de
  cada pin precisamente porque no sabe la cadena de antemano.
* **Cinco hipótesis medidas falsas o colapsadas** en una sesión, y al final se vio que no era mala
  suerte: todas hablaban de **tres** cosas. Las que se cumplen hablan de una o dos.
* **Dos medidas al 100%** que ordenan todo: `SupportedG` (todo nodo está en una cadena) y
  `TablesSound` (toda entrada de tabla es realizable). 42.652 nodos y 825.612 entradas, cero
  excepciones.
* **El hueco restante, aislado**: `SupportedRun.TriplePin`, una frase sobre tres nodos de un solo
  estado sin pinchar. Con ella cae toda la escalera hasta el veredicto sin retroceso.

---

## 1. El resultado: la máquina decide

### 1.1 Lo que pasó

Llevaba la sesión entera atacando «el lector no se atasca» como si fuera una propiedad de las
tablas. Tú lo cortaste:

> *el algoritmo necesita aplicar review paso a paso para poder leer la cadena; si la supiera desde
> el principio no tendría que hacerlo... la demostración está exigiendo demasiado a un algoritmo que
> en la práctica es correcto... creo que el enfoque es incorrecto*

Es exactamente el diagnóstico. Un lector sin retroceso acierta siempre **si y solo si** no hay
fantasmas en su trayectoria — `Reader.PickSome_of_Inhabited` y su recíproco lo dicen desde v?. O
sea: pedirle que no se equivoque nunca es pedirle que supiera la respuesta.

### 1.2 Y la prueba estaba escrita, tirada

`ConservationFilter.chainSound_alongF` **ya construía la cadena `ChainSound`** sobre una fórmula
satisfacible. `inhabitedM_alongF` la proyectaba a `Inhabited` —dos de sus cuatro campos— y
`pureRunF_full_state` devolvía solo eso. Bastó no tirarla:

* `ConservationFilter.pureRunF_full_chain` / `ConservationImproves.pureRunW_full_chain`

Con la cadena en la mano, un lector que **puede deshacer un pin** es completo sin hipótesis:

* `ReaderBT.pin_of_chain` — el pin que la cadena elige deja el estado válido y conserva la cadena
  (`ChainSound_filterAllAgg`);
* `ReaderBT.readBT_complete` — y entonces el lector termina siempre que hay camino. Que otros pines
  lleven a estados sin camino da igual: el retroceso los deshace;
* **`ReaderBT.readerVerdictBT_iff`** — el veredicto, en las dos direcciones, sin hipótesis.

### 1.3 El retroceso no cambia el algoritmo, lo cubre

Objetaste, y con razón, que el lector no necesita retroceso. Está demostrado que no se paga cuando
no hace falta:

* `readBT_isSome_of_readLoop` / `readerVerdictBT_of_readerVerdictW` — si el lector sin retroceso
  termina, el de retroceso también: prueba los mismos pines en el mismo orden y solo sigue donde el
  otro se rendía.

Y medido, no hace falta nunca: sonda `row-degree traj`, 100% de los estados llegan al paso 0, media
1,00 owners comunes por paso, cero atascos en todos los barridos.

**Lo que esto mueve de sitio**: la obligación pasó de la *corrección* al *coste*. Que el retroceso
no dispare nunca es `ProgressAgg`, medido sin excepción. La construcción del grafo sigue siendo
polinómica.

---

## 2. El patrón: dos y tres

### 2.1 Cinco hipótesis caídas

| hipótesis | destino |
|---|---|
| `ParentMeet` | medida falsa (375 fallos, todos espurios) |
| `PairMeet` + `TwoParents` | medidas falsas a 5+ variables (6 contraejemplos, in-degree 4) |
| `DecidedAbove` | medida falsa (solo 1/3 de los estados) |
| `TableDownClosed` | **colapsa a `SingleParents`** (`singleParent_of_tableDownClosed`) |
| `AllParentsOwn` | medida falsa, y el review no la restablece |

### 2.2 Y dos medidas al 100%

* **`SupportedG`** — todo nodo de todo estado está en una cadena. Sonda `row-degree sup-all`:
  42.652 nodos, 2.296 estados, 36 fórmulas más los tres ficheros. Cero fantasmas, cero indecisos.
* **`TablesSound`** — toda entrada `(nodo, owner)` es realizable por una cadena que pase por los
  dos. Sonda `row-degree soundat`: **825.612 entradas, cero fantasmas.**

### 2.3 La lectura, que es el hallazgo conceptual

Esto parecía contradecir la no-transitividad de la posesión, que **remedí con la ventana actual** a
petición tuya y sigue fallando (19,9% / 17,0% / 5,5% / 9,2% / 11,4%; la medida vieja daba 13,8%).
No la contradice:

* **una entrada es un PAR** `(x, w)` — y todo par es realizable: 100%
* **la transitividad es un TRÍO** — y ahí falla

> **La máquina es exacta en 2-consistencia e inexacta de 3 en adelante.**

Y eso explica las cinco caídas de golpe. `ParentMeet`, `PairMeet`, `DecidedAbove`,
`TableDownClosed`, `AllParentsOwn` hablan todas de compatibilidad entre **tres** cosas: un nodo y
dos de sus owners, o un nodo, un owner y un padre. Las que se cumplen hablan de **una o dos**. No
era mala suerte cinco veces: era la frontera.

Corroborado por teorema: `Descent.path_consistent_witness` demuestra que la criba alcanza
consistencia de caminos **completa** —testigo simétrico en todo paso para todo par—, que es el techo
de lo que unas tablas por pares pueden sostener. **No hay tercera pata que añadir a `aggPair`.**

---

## 3. Lo que sí quedó demostrado por el camino

### 3.1 La ventana lleva el pin dos niveles

* `Descent.pid_of_three_pins` (cierre **`[propext]` solo**) — un pin fija el **id de mapa** de un
  paso; con los **tres** pasos de la ventana pinchados, `PMP` lee el segundo componente del padre y
  `GPMP` el tercero del abuelo: el `PathNodeId` queda escrito.
* `Descent.owner_two_above_via_son` — `cohS` lleva la determinación un nivel más.
* `Descent.decided_in_pinned_zone` / `extend_below_pinned` — dentro de la zona pinchada **y un paso
  por debajo** la tabla está decidida, y el descenso baja **dos pasos** por debajo de la zona **sin
  hipótesis ninguna**.
* `Descent.commonOwner_of_mapPinned` — con la corrida pinchada, `CommonOwner` entero.

**En una frase: un pin fija un nivel y la ventana lo lleva dos más abajo.** Ese es el rendimiento del
tercer componente dicho como teorema, y explica la medida del lector de arriba abajo (§3.2).

### 3.2 El lector de arriba abajo

`ReaderTop.lean`: el mismo lector pinchando el **último** paso con elección. `readerVerdictWTop_sound`
sin hipótesis — el orden de los pines no entra en la corrección.

| seed | orden | pines | zona pinchada |
|---|---|---:|---:|
| 2026 | abajo→arriba | 18 | 42,2% |
| 2026 | **arriba→abajo** | **9** | **56,4%** |
| 7 | abajo→arriba | 14 | 50,0% |
| 7 | **arriba→abajo** | **8** | **62,1%** |
| 11 | abajo→arriba | 21 | 37,2% |
| 11 | **arriba→abajo** | **11** | **52,1%** |

**La mitad de pines y una zona más profunda**, mismo veredicto. Cada pin cubre tres niveles, no uno.

### 3.3 `up` conserva, `doJoin` es quien rompe

* `Descent.gained_of_parent` — el `up` **conserva** `AllParentsOwn`: la herencia de `rowOwners` es
  uniforme **hacia arriba** y solo por rama **hacia abajo**.
* `Descent.supportedS_reviewAgg` — la **revisión** conserva que todo nodo esté en una cadena, en tres
  líneas (`ChainSound_reviewAgg` no rompe ninguna cadena sana).
* Y `doJoin` explorado con sonda: une **sin revisar**, el review llega en el envío siguiente; fusiona
  nodos con listas de padres distintas en el 10,8–11,5% de los casos.

### 3.4 El filtro sí afecta, y la revisión lo arregla

Tu intuición era que limpiar los requisitos de mapa no debía afectar. Medido en tres fotos de cada
envío (contando solo los que sobreviven; la primera versión de la sonda contaba también los
inválidos y daba cifras espurias del 56–83%):

| corpus | antes | tras `filterRequire`, **sin revisar** | tras `reviewAgg` |
|---|---:|---:|---:|
| simple_test | 0 | 105/370 (28,3%) | **0/265** |
| test_sat_medium | 0 | 228/975 (23,3%) | **0/747** |
| test_unsat | 0 | 105/471 (22,2%) | **0/366** |
| seed 2026 | 0 | 5.059/19.852 (25,4%) | **0/14.793** |
| seed 11 | 0 | 6.405/24.303 (26,3%) | **0/17.898** |

**El filtro rompe una cuarta parte de los nodos; la revisión los quita todos.** 0 fallos en 10.572
envíos. El reparto de trabajo no era el que parecía: la revisión no es un adorno detrás del filtro,
es la mitad que restablece la propiedad.

---

## 4. El hueco, aislado

`SupportedRun.lean` conecta el invariante de entradas con el de nodos y deja escrito lo que falta.

* `supportedS_of_soundAt` — el invariante de **entradas** implica el de **nodos** en dos líneas. Así
  que los 42.652 nodos al 100% son consecuencia de las 825.612 entradas al 100%, no un hecho aparte.
* `supportedS_pin_of_soundAt` — con un pin en un paso literal, `RunSteps.realizes_pin` da
  `SupportedS` del estado pinchado.

Y la reducción:

```lean
def TriplePin : Prop :=
  ∀ g, ReadableAgg g → isValid g = true → SoundAt (LitStep φ) g →
    ∀ r, LitStep φ r.step → isValid (filterAllAgg g [r]) = true →
      ∀ x q, Realizes g x q → q.id.step ≠ r.step →
        ((filterAllAgg g [r]).node? x).isSome = true →   -- `x` sobrevive al pin
        ((filterAllAgg g [r]).node? q).isSome = true →   -- `q` también
        ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel q.id.step = q ∧ (sel r.step).id = r
```

*Si hay cadena por `x` y por `q`, y el pin `r` deja el estado válido, hay cadena por los tres.*

`pinPair_of_triplePin` la conecta, y detrás cae todo lo que ya está en el repo:

```
TriplePin → PinPairSoundAt → PinStepSoundAt → SendPinSoundAt → FilterSoundAt
          → invariante de la corrida → SupportedS → Inhabited
          → el lector no se atasca → el veredicto SIN retroceso
```

### 4.1 Lo que ya está cerrado de `TriplePin`

* `chain_through_req` — `ReqFiltered` dice que todo owner de un nodo en el paso de uno de sus
  requisitos **es** ese requisito; los picks de una cadena son owners unos de otros. Luego **si el
  pin es un requisito del nodo, la cadena ya pasa por él**, sin reencaminar nada. (Cierre
  `[propext, Quot.sound]`.)
* `triplePin_of_req` — el caso en que el pin es requisito de `x` **o** de `q`. Cubre la pareja
  cruzada `2v ↔ 2v+1` del bloque de literales y todo nodo de cláusula con el pin entre sus literales.

### 4.2 Lo que queda, y la única dirección viable

Queda el caso en que **ni `x` ni `q` requieren `r`**: dos variables que el mapa no enlaza
directamente.

Y hay un resultado negativo que cierra la vía obvia: **`ChainMerge` es falso** (v145). De «hay
cadena por `x` y `q`» más «hay cadena por `x` y `r`» **no** se sigue «hay cadena por los tres» — el
contraejemplo es una fórmula donde `v1` puede ser cierta, `v2` puede ser cierta, y no a la vez. Así
que empalmar no vale, y toda versión de la frase que no use la supervivencia al review es falsa.

Por eso apreté `TriplePin` para que solo lo pida de nodos que **sobreviven al pin**. Y de ahí salió
lo último de la sesión:

* **`shared_pin_witness`** — si `x` y `q` sobreviven y `q` sigue en la tabla de `x`, la criba del
  estado pinchado los obliga a compartir un owner en **todos** los pasos, y en el paso del pin ese
  owner común **lleva el pin**.

O sea: la frase abierta ya no es «tres nodos compatibles dos a dos». Es «`x`, `q` y **un mismo
tercero** `z` que los dos poseen y que es el valor pinchado». **Un testigo, no dos.** Es la forma más
débil a la que ha bajado y la primera que de verdad usa que el review dejó vivos a los dos — que es
justo lo que `ChainMerge` no sabe.

---

## 5. Errores míos en esta sesión, anotados

1. **Encuadre del lector sin retroceso.** Lo atacaba como propiedad de las tablas durante horas. El
   diagnóstico fue tuyo.
2. **Dije que `up` y `doJoin` conservan `TableDownClosed` «por construcción».** Falso: al intentar
   escribirlo salió `singleParent_of_tableDownClosed`, el colapso.
3. **Primera versión de la sonda del filtro**: contaba envíos inválidos y daba 56–83% de fantasmas.
   Cifra espuria; con el filtro puesto son 22–28% y la revisión los quita todos.
4. **`AllParentsOwn` presentada como «estrictamente más débil»** antes de medirla. No lo era.

---

## 6. Inventario, al cierre

**Cerrado sin hipótesis**: conservación (`pureRunW_ne_nil`), las tres respuestas (`answer_*_sound`),
el veredicto para `SingleParents`, que el lector nunca se equivoca cuando termina
(`readerVerdictW_sound`, `readerVerdictWTop_sound`), y **el veredicto completo con retroceso**
(`readerVerdictBT_iff`).

**Medido sin excepción**: `SupportedG` (42.652 nodos), `TablesSound` (825.612 entradas), que el
retroceso no hace falta nunca, que el descenso siempre baja al paso 0.

**Abierto**: `TriplePin`, caso de variables distintas, con testigo compartido. Y la cota de coste del
lector sin retroceso, que es la misma frase.

### 6.1 Addendum: el ataque montado, y un callejón cerrado con ejemplo

`triple_data_of_survival` junta `shared_pin_witness` con `SoundAt` y entrega lo que la frase abierta
consume: el testigo `z` que es el valor pinchado, y **cadena para las tres parejas** `(x,q)`,
`(x,z)`, `(q,z)` en el estado de antes del pin. Todo demostrado, sin hipótesis nueva.

Y con eso delante se ve que **el pegado puro es falso**, así que conviene no intentarlo:

> Sea `φ` con soluciones exactamente `{110, 101, 011}`. Tómese `x` el nodo que fija el bit 1, `q` el
> que fija el bit 2, `z` el que fija el bit 3. Las tres parejas tienen cadena —`110` lleva `x` y
> `q`, `101` lleva `x` y `z`, `011` lleva `q` y `z`— y la terna necesitaría `111`, que no es
> solución.

Es el mismo tipo de contraejemplo que mató a `ChainMerge`, un piso más arriba: no basta con que las
tres parejas sean realizables.

**Y esa es la lectura que me llevo, que corrige el plan de ayer.** En ese mismo ejemplo, tras fijar
el bit 3 la criba del estado pinchado compara `x` y `q` y **no comparten owner en el paso del bit
1**, así que `aggPair` borra el par y la obligación ni se plantea. O sea:

> `PinPairSoundAt` **no es un teorema de pegado de cadenas**. Es un teorema sobre **qué sobrevive al
> punto fijo de la criba en el estado pinchado**.

Los tres `Realizes` son datos de entrada; el trabajo está en `AggOk (filterAllAgg g [r])`, que
`shared_pin_witness` ya empieza a usar y que ningún intento de esta sesión —ni de las anteriores—
tocaba. Ahí es donde yo miraría mañana, y ya no en el pegado.
