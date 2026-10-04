# Verificación para el Autor v190: una tercera semilla, y el invariante que hay que debilitar

Ricardo, soy Claude (Opus 5.5). Este informe sigue al v189, que dejó la escalera del lector con
hipótesis por pin medidas sin fallos. Aquí se midió lo que el v189 dejaba previsto (si la exactitud
por parejas y por tríos se conserva al pinchar, y `WitPinDown`), **ampliando la muestra a una tercera
semilla (11)**. La ampliación ha encontrado algo importante. **El invariante sobre el que se apoyan
todas las escaleras es falso en una fórmula concreta, aunque el lector acierta en ella.** Y señala
cuál es el invariante más débil que sí se mantiene.

Lo cuento primero, porque cambia lo que sigue.

Rama `pair-mode`. Sondas en `lean_project/Probes/RowDegree.lean` (modos `exactpins`, `tri3x`,
`roundexact`, `verdict`, `segdetail`, `triexactfile`, `prefix`). Fórmula guardada en
`Probes/cnf/seed11_1_segexact_start.cnf`. Commits `ef16e37` y `53e2be6`.

---

## 1. El hallazgo: `hStart` y `SegGood` fallan en la semilla 11, fórmula #1

La fórmula (6 variables, 8 cláusulas, **satisfacible**):

```
p cnf 6 8
6 -5 2 0
6 -1 5 0
-6 -2 -1 0
-5 -2 -3 0
2 4 6 0
2 5 -1 0
5 3 -1 0
-3 1 -4 0
```

* **El lector acierta**: veredicto `true`, igual que la fuerza bruta. En las 36 fórmulas de las
  semillas 1, 7 y 11, el lector acierta siempre.
* Pero en el **primer estado del lector** (la línea final revisada, `filterAllAgg kv.2 []`) hay
  **tramos sin cadena completa** (6) y el estado **incumple `SegGood`**.
* Un ejemplo: el tramo de los pasos 4 a 11 (`4/0<3/1<2/0 … 11/1<10/0<9/1`) no tiene entrada común en
  ningún paso del 13 al 20. En el paso 13 (la primera cláusula), las tablas de sus miembros se cortan
  **dos a dos** pero no las tres a la vez; por ejemplo `{6, 2, 4}`, `{3, 7, 6}` y `{3, 2}` (filas de la
  cláusula). Es un fallo de Helly genuino, en un estado de la máquina.
* En la semilla 11 completa: tras la primera vuelta del pin y tras `cleanPair` quedan **6 tramos sin
  cadena** (en las semillas 1 y 7 eran 0), y en los estados del lector, 12. **`RoundExact` y la forma
  fuerte de `PairHelly` también fallan aquí.**

**Qué significa.** `hStart` (SegExact en la línea final revisada, medido sin fallos en el v183 con las
semillas 1 y 7) es **falso en general**. `SegGood` **no es un invariante** de los estados del lector.
Todas las escaleras de los v184–v189 (`…_of_roundExact`, `…_of_pairHelly`, `…_of_survives`,
`…_of_kept`, `…_of_keptOwn`, `…_of_witPin`) son teoremas correctos, pero **una de sus hipótesis falla
en esta fórmula**. Su conclusión, que el lector decide bien, sigue siendo cierta aquí: la estaban
demostrando con un invariante demasiado fuerte.

Lo demostrado sobre la máquina no cambia: la regla, su corrección, los invariantes, `AggInactive`, las
reducciones. Lo que cambia es **qué invariante del lector** hay que llevar por la inducción.

## 2. La exactitud por parejas sí, por tríos no

Medición del v189 ampliada (`exactpins`, todos los pines, semillas 1, 7 y 11; con muestreo: 40 nodos
para parejas; 25 nodos, 12 y 6 vecinos para tríos):

| | estados | medidos | sin cadena común |
|---|---|---|---|
| `PairExact` (parejas) | 185 | 198.666 | 0 |
| `TriExact` (tríos) | 185 | 317.788 | 0 |

Pero **sin muestreo**, en el estado inicial de la fórmula #1 de la semilla 11 (`triexactfile`):

| | medidos | sin cadena común |
|---|---|---|
| parejas | 6.742 | **0** |
| tríos | 26.413 | **87** |

Así que **la exactitud por parejas se mantiene y la de tríos no**. Es exactamente la limitación de
tablas de parejas: guardan bien la compatibilidad de dos nodos, y no pueden guardar la de tres. La
escalera `…_of_witPin`, que usa `TriExact`, tiene una hipótesis falsa en esa fórmula. La muestra de 25
nodos no la había visto.

## 3. `WitPin` y la supervivencia: igual

`tri3x`, tres semillas:

* **`WitPinDown`**: 0 tramos sin testigo pinchado (65.981 tramos con paso anterior).
* **`WitPinUp`**: 0 en las semillas 1 y 7; **1** en la semilla 11. Es el tramo 5..12 del estado
  anterior, que ya no tenía testigo ni siquiera en `g`: la misma raíz del §1.
* El criterio local (testigo con nodo pinchado compartido) sigue separando **exactamente** a los
  testigos que sobreviven de los que mueren: 70.988 lo cumplen, **ninguno** muere.

## 4. El invariante que sí se mantiene: los prefijos

Los tramos que fallan empiezan en los pasos 3, 4 o 5, nunca en el 0. Medido en todos los estados del
lector, siguiendo todos los pines (`prefix`):

| | estados del lector | tramos | sin entrada común en algún paso | de ellos, **empiezan en el paso 0** |
|---|---|---|---|---|
| semilla 11 | 113 | 28.287 | 18 | **0** |
| semilla 1 | 72 | 15.818 | 0 | 0 |

El lector construye su cadena **desde el paso 0**: cada pin se añade a un prefijo. Lo que el lector
necesita no es `SegGood` para *todo* tramo, sino para los tramos que puede estar construyendo. En esos,
la medición no encuentra ningún fallo.

## 5. Qué cambia en la escalera

La estructura se mantiene: alargar tramos paso a paso, testigos de la historia, supervivencia,
`link_cleanPair`, (W2). Lo que hay que cambiar es el invariante de la inducción:

* **De `SegGood` a `PrefixSegGood`**: todo tramo **que empieza en el paso 0** tiene entrada común en
  cada paso por encima de él. Es más débil, y medido sin fallos.
* **Alargar paso a paso con prefijos**: un prefijo solo se alarga hacia arriba, así que solo hace falta
  la dirección `Up` (`OneStepUp`, `SurvivesUp`, `KeptOwnUp`, `WitPinUp`). Las piezas `Down`
  desaparecen.
* **`hStart`** pasa a ser `PrefixSegGood` de la línea final revisada.
* **`TriExact`** fuera: falla. Queda por ver si, restringida a tríos que se usan con prefijos, se
  mantiene, o si la pieza `KeptOwnUp` se puede cerrar con solo `PairExact` para prefijos.

## 6. Lo previsto, en orden

1. **Medir las hipótesis restringidas a prefijos**: `PrefixSegExact` tras cada pin y en el punto fijo;
   `WitPinUp` y `KeptOwnUp` para prefijos; `TriExact` para los tríos (miembro de un prefijo, testigo,
   nodo pinchado). Con más semillas (3, 5, 11, 13…).
2. **Comprobar que la escalera del lector funciona con prefijos**: que `TopGoodLadder` (la escalera
   por `SegGood`) puede reescribirse con `PrefixSegGood`, es decir, que el lector solo consulta tramos
   que empiezan en el paso 0.
3. **Formalizar las versiones de prefijo** de `pairHelly_of_oneStep` (solo hacia arriba) y de la
   escalera.
4. Pendientes de máquina, como en el v189.

**Una nota sobre las muestras.** Dos semillas ocultaron un fallo que la tercera enseñó, y una muestra de
25 nodos ocultó otro que la búsqueda completa encontró. A partir de aquí conviene medir cada hipótesis
nueva con más semillas y, en instancias pequeñas, sin muestreo.

## 7. Una frase

El lector acierta en la fórmula donde el invariante falla, porque nunca mira los tramos que fallan:
los construye desde el paso 0, y ahí las tablas de parejas siguen siendo suficientes.
