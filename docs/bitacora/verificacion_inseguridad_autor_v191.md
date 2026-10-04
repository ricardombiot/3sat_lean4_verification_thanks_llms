# Verificación para el Autor v191: por qué falla la semilla 11, y qué se puede cambiar en construcción, revisión y lectura

Ricardo, soy Claude (Opus 5.5). El v190 encontró que en la semilla 11, fórmula #1, el estado inicial
del lector incumple `SegGood`, aunque el lector acierta. Aquí se disecciona ese fallo hasta su causa y
se desarrollan las propuestas de mejora en cada capa de la máquina: construcción, revisión y lectura.

**Adelanto la conclusión, porque corrige lo que dije en el chat.** Allí propuse una «regla del hueco»
en la revisión. Al desarrollarla, **resulta incorrecta**: cada una de las tres parejas implicadas está
en una solución real, así que ninguna regla correcta sobre tablas de parejas puede quitarlas. El fallo
no es un defecto de la revisión. Es un límite de la representación: las tablas guardan parejas, y aquí
lo que está muerto es un trío. La propuesta que sale reforzada es la de la **lectura**. Y aparece una
forma más limpia que la del v190: llevar por la inducción **la exactitud por parejas**, que es
justo lo que las tablas pueden guardar, en lugar de un invariante de tramos.

Rama `pair-mode`. Sonda `segdetail` en `lean_project/Probes/RowDegree.lean`. Fórmula en
`Probes/cnf/seed11_1_segexact_start.cnf`. El análisis del §1 está hecho a mano sobre la salida de
`segdetail`, para el primer tramo; los demás tramos listados tienen la misma forma, pero **no** se ha
medido que los 18 de la semilla respondan a la misma causa.

---

## 1. Anatomía del fallo

### 1.1 La fórmula y sus pasos

```
p cnf 6 8
6 -5 2 0      c1   paso 13
6 -1 5 0      c2   paso 14
-6 -2 -1 0    c3   paso 15
-5 -2 -3 0    c4   paso 16
2 4 6 0       c5   paso 17   ← la culpable
2 5 -1 0      c6   paso 18
5 3 -1 0      c7   paso 19
-3 1 -4 0     c8   paso 20
```

La codificación (`CnfMap`): la variable `v` (desde 0) vive en el paso `2v` (`v=0`, `v=1`), su
negación en `2v+1` (`!v=i`, que requiere `v = 1-i`); el paso 12 es la fusión; las cláusulas van del
13 al 20, cada una con 7 filas `r = 4b₁+2b₂+b₃` (falta la `000`); la fusión final en el 21. Cada nodo
del camino es una **ventana** de tres ids del mapa: el suyo, el de su padre y el de su abuelo.

En DIMACS: x2 vive en los pasos 2–3, x3 en 4–5, x4 en 6–7, x5 en 8–9 y x6 en 10–11.

### 1.2 El tramo

`segdetail` da, en el estado inicial del lector (paso 22, 181 nodos), el tramo:

```
4/0<3/1<2/0, 5/1<4/0<3/1, 6/0<5/1<4/0, 7/1<6/0<5/1,
8/0<7/1<6/0, 9/1<8/0<7/1, 10/0<9/1<8/0, 11/1<10/0<9/1
```

sin entrada común en los pasos 13 a 20. Leído como asignación:

* x3 = x4 = x5 = x6 = 0 (los nodos `4/0`, `6/0`, `8/0`, `10/0`);
* y además **x2 = 0**, que no está en ningún paso del tramo, sino en la **ventana** de sus primeros
  miembros: `3/1` es `!x2=1`, es decir x2 = 0.

### 1.3 La cláusula que lo mata

La cláusula c5 = `x2 ∨ x4 ∨ x6` tiene sus tres literales falsos. **Ninguna solución contiene el
tramo**: el fallo de `SegGood` es genuino, no un error de la máquina. Lo que falla es que la máquina
lo sigue representando como un tramo vivo.

Y **nadie lo ve entero**. Cada literal falso lo conoce un grupo distinto de miembros:

| literal falso | lo conocen | por qué |
|---|---|---|
| x2 = 0 | miembros de los pasos 3, 4, 5 | x2 está en su ventana |
| x4 = 0 | miembros de los pasos 6 a 9 | x4 es su nodo o está en su ventana |
| x6 = 0 | miembros de los pasos 10 a 12 | x6 es su nodo o está en su ventana |

Una ventana abarca tres pasos, es decir, una variable y media. Ningún miembro ve dos de esos literales
a la vez.

### 1.4 El hueco 000, repartido entre tres nodos

En el paso 17, las filas de c5 compatibles con cada literal falso son:

| miembro | condición | filas `(b₁b₂b₃)` = (x2, x4, x6) |
|---|---|---|
| A (sabe x2 = 0) | b₁ = 0 | 1 (001), 2 (010), 3 (011) |
| B (sabe x4 = 0) | b₂ = 0 | 1 (001), 4 (100), 5 (101) |
| C (sabe x6 = 0) | b₃ = 0 | 2 (010), 4 (100), 6 (110) |

Son **tres caras del cubo** {0,1}³. Se cortan dos a dos (A∩B = {1}, A∩C = {2}, B∩C = {4}), y las tres
juntas solo se cortarían en la 000, que es la fila que falta. Es exactamente el caso que `helly_box`
excluye: cajas que se cortan dos a dos tienen un punto común en el cubo, pero ese punto puede ser el
hueco.

### 1.5 El resto es arrastre

`segdetail` informa del primer paso sin entrada común, el 13 (c1 = `x6 ∨ ¬x5 ∨ x2`), no el 17. Pero es
el mismo hueco proyectado:

* el miembro A (x2 = 0) solo admite filas con b₃ = 0: {6, 2, 4};
* el miembro de x6 (x6 = 0) solo admite b₁ = 0: {3, 2};
* el miembro `8/0<7/1<6/0` (x5 = 0 y, por su ventana, x4 = 0) admite {3, 7, 6}: le falta la fila 2
  (x6 = 0, x2 = 0), porque con su x4 = 0 violaría c5. Este miembro **sí** ve dos de los tres
  literales, y la máquina ya había aprovechado esa información.

La intersección de las tres es vacía. Todo tramo que contiene un trío con el hueco de c5 falla en
todos los pasos de cláusula, porque ninguna cadena completa puede pasar por él.

## 2. Por qué ninguna regla correcta sobre parejas lo arregla

Una regla de la revisión solo puede **quitar nodos** o **quitar entradas de tablas**. Para ser
correcta (no perder soluciones, que es lo que demuestran `ChainSound_*`), solo puede quitar una
pareja `(u, v)` si ninguna solución pasa por `u` y `v` a la vez. Comprobado a mano, cada pareja del
trío está en una solución real:

| pareja | solución (x1..x6) | comprobación |
|---|---|---|
| A (x2 = 0, x3 = 0) y B (x3 = 0, x4 = 0) | 0 0 0 0 0 1 | c5 por x6; c2 por x6; las demás, sí |
| A (x2 = 0) y C (x5 = 0, x6 = 0) | 0 0 0 1 0 0 | c5 por x4; c2 por ¬x1 |
| B (x4 = 0) y C (x5 = 0, x6 = 0) | 0 1 0 0 0 0 | c5 por x2; c3 por ¬x1 |

Así que:

* **Ninguna pareja es la culpable** (ya lo intuía el v188). Una regla que quite `v` de la tabla de `u`
  porque existe un tercero `w` perdería una de esas tres soluciones.
* **Ningún nodo es el culpable**: los tres están en soluciones.
* **Lo único muerto es el trío**, y las tablas no tienen dónde guardar un trío.

**Corrección de lo dicho en el chat.** La «regla del hueco» que propuse (si tres nodos que se poseen
falsean cada uno un literal distinto de una cláusula, se quitan unos a otros de sus tablas) **no es
correcta**: quitaría, por ejemplo, la pareja A–B, que está en la solución `0 0 0 0 0 1`. Queda
descartada. La prueba de que es incorrecta es la tabla de arriba.

Consecuencia más fuerte: **con tablas de parejas, `SegGood` no se puede alcanzar en general con
ninguna revisión correcta.** Basta un estado que contenga este trío, y la máquina lo construye.

## 3. Por qué los prefijos nunca fallan

Esto se deduce sin medir:

1. Las entradas comunes de un tramo son la intersección de las tablas de sus miembros. Si un tramo
   contiene a otro, sus entradas comunes son un subconjunto de las del otro.
2. Por tanto, si un prefijo (un tramo que empieza en el paso 0) contuviera un tramo que falla, el
   prefijo también fallaría.
3. La medición del v190 dio **0 prefijos que fallan** (semilla 11: 18 tramos que fallan, 0 prefijos).
4. Luego **ningún tramo que falla se prolonga hacia abajo hasta el paso 0**.

Los tramos que fallan son **restos sin soporte inferior**: tríos muertos que siguen escritos en las
tablas porque la revisión solo ve parejas, pero que ninguna cadena desde el paso 0 puede recorrer. La
máquina los ha matado «por abajo»: las cadenas que los contendrían ya no existen.

Una observación que refuerza la lectura: el trío solo es visible como tramo cuando x2 queda **fuera**
del tramo, en una ventana (tramos que empiezan en los pasos 3 a 5). Eso encaja con que empiecen en los
pasos 3, 4 o 5, pero no se ha medido que sea la única forma.

## 4. Propuestas en la lectura

Aquí está la mejora con más peso, y no toca la máquina.

### 4.1 Lo que el lector necesita de verdad

La escalera termina en `ReaderChain.OwnerChained g`:

```lean
def OwnerChained (g : GPathM) : Prop :=
  ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
    ∃ sel, ChainSound g sel ∧ (sel q.id.step).id = q.id
```

Es decir: todo nodo de la global está en alguna cadena sana. `SegGood` era un medio para construirla
(`TopGoodUp.ownerChained_of_segGood`: bajar desde `q` hasta el paso 0 y subir hasta la cima,
alargando tramos). Ese medio pide que **todo** tramo se alargue, y el §2 muestra que no puede ser.

### 4.2 Propuesta A: `PrefixSegGood` (la del v190)

```lean
def PrefixSegGood (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (hi : Int), 0 ≤ hi → hi ≤ g.current_step - 1 →
    Extendable.PartialChain g sel 0 hi →
    (∀ i j, 0 ≤ i → 0 ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∀ i, hi < i → i ≤ g.current_step - 1 → ∃ r, r.id.step = i ∧
      ∀ j, 0 ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners
```

Es `SegGood` con `lo = 0` y solo hacia arriba.

* **A favor**: medido sin fallos (§3), y la dirección `Down` desaparece de toda la escalera.
* **El obstáculo**: `OwnerChained` pide una cadena por **cualquier** `q`, y hoy se construye bajando
  desde `q`, lo que usa tramos que no empiezan en 0. Con prefijos habría que **tener ya** un prefijo
  que acabe en `q` y subir desde él. Ese prefijo existe si `q` está en alguna cadena sana… que es lo
  que se quiere demostrar. La circularidad se rompe con la historia: tras un pin, los nodos que
  sobreviven estaban en una cadena de `g`, que es un prefijo que acaba en ellos (esto es el
  razonamiento de (W2)). Hay que escribirlo, y no es inmediato.

### 4.3 Propuesta B: llevar `PairExact` por la inducción (nueva)

La escalera ya tiene una definición que dice justo lo que necesita el lector, y que las tablas sí
pueden guardar:

```lean
def PairExact (g : GPathM) : Prop :=
  ∀ x nx w, g.node? x = some nx → w ∈ nx.owners → (g.node? w).isSome = true →
    ∃ sel, ChainSound g sel ∧ Fabric.Passes g sel x ∧ Fabric.Passes g sel w
```

Toda entrada viva de una tabla está en una cadena sana junto con su dueño.

* **`PairExact` implica `OwnerChained`** casi directamente: todo nodo de la global se posee a sí mismo
  (autoposesión, `SelfOwn`), así que basta tomar `w = x`. Esto debería salir con piezas ya demostradas.
* **Es de parejas**, que es lo que las tablas guardan. No pide nada sobre tríos, así que el fallo del
  §1 no le afecta: A–B, A–C y B–C están, cada una, en una cadena (las tres soluciones del §2).
* **Medido**: 0 fallos en todos los pines de las semillas 1, 7 y 11 (198.666 parejas con muestreo), y
  0 de 6.742 **sin muestreo** en el estado exacto donde `SegGood` y `TriExact` fallan.
* **Reescribe la escalera**: `ReaderPairExact` (`PairExact` en todo estado que el lector visita)
  ⟹ `OwnerChained` en cada estado ⟹ `readerVerdictW φ = true ↔ Satisfiable φ`, con la misma
  estructura que `readerVerdictW_iff_of_readerSegGood`.

**Lo que queda, dicho con honestidad.** La pieza dura se desplaza a **conservar `PairExact` en cada
pin**: si `(x, w)` sobrevive a `cleanPair X`, hay una cadena sana de `X` por `x`, `w` **y el pin**.
Eso es una afirmación de tres elementos (dos nodos y el pin), del mismo tipo que `TriExact`, que falla
para tríos arbitrarios. La diferencia, que hay que medir y luego demostrar, es que aquí el tercero es
siempre **el nodo pinchado**, que el lector elige por su historia, y que la revisión ya ha filtrado
todas las entradas contra él (`filterWeak` + `cleanPair`). Es la misma forma que (W2), que ya está
demostrado en un sentido.

**Recomendación**: B antes que A. B no depende de la forma de los tramos, usa una definición que ya
existe, y su hipótesis está medida sin fallos donde A y `SegGood` fallan.

## 5. Propuestas en la revisión

### 5.1 Qué no se puede hacer

Por el §2, ninguna regla correcta que actúe sobre nodos o sobre parejas puede hacer que el tramo del
§1 tenga una entrada común. Quedan descartadas:

* la «regla del hueco» del chat (incorrecta);
* cualquier regla de tríos que termine quitando parejas;
* reforzar la regla de parejas: ya da consistencia de caminos, y el trío es del nivel siguiente.

### 5.2 Qué sí puede aportar la revisión

La revisión no puede arreglar `SegGood`, pero puede **hacer más fácil de demostrar la conservación
de `PairExact`**, que es la pieza que queda en la propuesta B:

* **Filtrado contra el pin en dos sentidos.** Tras un pin, la regla de parejas compara cada pareja
  con la tabla del otro. Una variante («pareja con el pin») exigiría, además, que para cada pareja
  `(x, w)` exista en cada paso una entrada común de `x`, `w` **y del nodo pinchado `q`**. Es una regla
  de tríos, pero con un elemento fijo: el coste es el de la regla de parejas, no el de tríos
  arbitrarios. Es correcta: toda solución que sobrevive al pin pasa por `q`, así que una pareja
  en una solución tiene esa entrada común. Y ataca exactamente la afirmación que la propuesta B
  necesita.
* Antes de implementarla conviene **medir si hace falta**: si `PairExact` se conserva ya en todos los
  pines (0 fallos hasta ahora), la regla sería redundante y solo facilitaría la prueba. Si la medición
  sin muestreo encuentra una pareja superviviente sin cadena por el pin, esa regla sería la reparación.

## 6. Propuestas en la construcción

Aquí están las únicas opciones que harían desaparecer el trío del §1, porque cambian lo que un nodo
puede ver.

### 6.1 Binarizar las cláusulas (v187 §5): no basta

La propuesta del v187 parte cada cláusula en tres pasos binarios con una ventana prohibida `000`.
Aplicada a c5, el paso intermedio `L2` tiene como entradas las ventanas `(b₂, b₁)`:

* A (x2 = 0) admite las de b₁ = 0: `(0,0)` y `(1,0)`;
* B (x4 = 0) admite las de b₂ = 0: `(0,0)` y `(0,1)`;
* C (x6 = 0) necesita b₃ = 0, y como `000` no existe, admite las que no son `(0,0)`: `(0,1)`, `(1,0)` y
  `(1,1)`.

Se cortan dos a dos y no las tres: **el hueco se muda a las ventanas**. La binarización hace trivial
el Helly de un paso para **elegir hijo** (dominio de 2 nodos del mapa), que era su objetivo en el v187,
pero no hace que las tablas guarden tríos. No arregla este fallo.

### 6.2 Reordenar las variables: reduce, no elimina

El trío aparece porque los tres literales quedan en ventanas distintas. Un orden de variables que
junte las de cada cláusula reduce los casos. Pero una ventana ve como mucho dos variables, y una
cláusula tiene tres: siempre puede quedar un literal fuera. Sirve como mejora de coste y de
frecuencia, no como garantía.

### 6.3 Acarreo del estado de las cláusulas: sí lo elimina, con un coste

La única forma de convertir la restricción de tres en restricciones de dos es que **un nodo lleve
consigo la parte ya decidida de la cláusula**:

* Cada nodo del bloque de variables lleva, además de su valor, un bit por cada cláusula **abierta** en
  ese paso (con un literal ya visto y otro aún por ver): «esta cláusula ya está satisfecha por un
  literal anterior».
* El bit se actualiza de un paso al siguiente mirando solo la ventana: es una restricción entre un
  nodo y su padre. En el paso de la cláusula basta mirar el bit acarreado, y otra vez es una
  restricción de dos.
* En el ejemplo, el nodo de x6 llevaría «c5 aún no satisfecha» exactamente cuando x2 = x4 = 0, así
  que C ya no sería compatible con A y B a la vez: el trío pasa a ser una pareja, y la regla de
  parejas la quita.

**El coste es exponencial en el número de cláusulas abiertas a la vez** (el ancho de corte del orden
de variables): 2^(cláusulas abiertas) índices por paso. En esta fórmula de 6 variables, con el orden
natural, las 8 cláusulas están abiertas entre x3 y x4, así que no ganaría nada. Es una vía para
**acotar una clase** (fórmulas con ancho de corte acotado, con un buen orden), en la que `SegGood`
valdría por construcción. No es una vía para el caso general.

## 7. Resumen de las propuestas

| capa | propuesta | ¿arregla `SegGood`? | ¿sirve para la escalera? | coste |
|---|---|---|---|---|
| lectura | **B: `PairExact` como invariante** | no hace falta | **sí**: medida sin fallos donde las otras fallan | prueba: conservar `PairExact` en el pin |
| lectura | A: `PrefixSegGood` | no hace falta | sí, si se rompe la circularidad del §4.2 | prueba: prefijo que acaba en cada nodo |
| revisión | regla del hueco (chat) | — | **no: incorrecta** | — |
| revisión | pareja con el pin | no | facilita conservar `PairExact` | como la regla de parejas |
| construcción | binarizar (v187) | no | Helly de elegir hijo | mapa y UP |
| construcción | reordenar variables | reduce | no garantiza | heurística |
| construcción | acarreo de cláusulas | sí | sí, en una clase | exponencial en el ancho de corte |

## 8. Lo previsto, en orden

1. **Demostrar `PairExact g → OwnerChained g`** con `SelfOwn` y escribir la escalera
   `readerVerdictW_iff_of_readerPairExact`. Debería ser corto.
2. **Medir la conservación de `PairExact` en cada pin sin muestreo** en instancias pequeñas, con al
   menos cuatro semillas (1, 3, 7, 11, 13): para cada pareja superviviente de `cleanPair X`, ¿hay una
   cadena sana de `X` que pasa por las dos y por el pin?
3. Según la medida: si es 0, intentar la prueba por la historia, siguiendo el camino de (W2). Si no,
   implementar en la sonda la regla «pareja con el pin» y volver a medir.
4. Dejar `PrefixSegGood` como alternativa, y el acarreo de cláusulas como línea aparte para acotar una
   clase.

## 9. Una frase

El fallo de la semilla 11 es un trío muerto hecho de tres parejas vivas: las tablas no pueden
borrarlo, y el lector no lo necesita. Lo que conviene llevar por la inducción es lo que las tablas sí
guardan, las parejas en una cadena, y demostrar que el pin las conserva.
