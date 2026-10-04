# Verificación para el Autor v159: el cambio de valor, desde los lados

Ricardo, soy Claude (Opus 5). He atacado `FlipSat` (v158) con lo que la inducción conjunta ya sabe en cada
línea. Rama `spaik`, build de `AbsSat` (228 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`.

## 1. La reducción

> **`SideKeep`**: en la etapa de cláusulas, toda entrada de una unión por clave fijada (un valor de
> literal) y revisada la conserva también **el envío fijado y revisado de uno de sus lados**.

`flipSat_of_sideKeep` y `sat_of_sideKeep`: el veredicto bajo `SideKeep` sola.

La prueba usa solo lo ya demostrado:

1. la entrada está en el envío fijado de un lado;
2. ese envío fijado cabe en el envío de la rama que lleva la fijación (`pin_send`, con la conmutación en
   esa línea, que la inducción conjunta ya ha establecido);
3. la unión de esa rama es exacta, así que la entrada está sobre uno de sus caminos;
4. todos los caminos de esa rama toman el valor fijado (`pinIds_branch`): el camino **no necesita
   ningún cambio de valor**, y cumple las cláusulas porque es genuino.

La inducción conjunta (`joint`) se ha generalizado para que la hipótesis de cada línea pueda usar la
conmutación y la exactitud de esa misma línea.

## 2. Lo que queda, en su forma más simple

`SideKeep` ya no habla de asignaciones, de caminos ni de cambios de valor. Habla solo del review:

> el review de la unión fijada **no conserva nada que no conserve el review fijado de alguno de sus
> lados**.

Es la forma por entradas de "nada se toma prestado entre lados". Para los caminos ya está demostrado
(`RunNoBorrow`); `SideKeep` es lo mismo para las entradas de las tablas, en las uniones por clave que
hace la máquina, con una fijación de literal. Se midió en v154 (`pinjoin`: 0 entradas fuera en todas las
uniones medidas).
