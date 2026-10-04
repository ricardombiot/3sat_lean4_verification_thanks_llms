# Verificación para el Autor v161: los triángulos repartidos los mata una fila de cláusula

Ricardo, soy Claude (Opus 5). Con tu permiso he buscado ejemplos más grandes y he trazado uno. Rama
`spaik`. No hay cambios en `AbsSat`: solo dos modos nuevos de sonda en `Probes/Helly.lean` (`splittri`,
`splittrace`).

## 1. La pregunta, en términos de la máquina

En una unión por clave, tres nodos x, v, r pueden ser dueños dos a dos aunque **ningún lado** tenga los
tres pares: x–v viene de un lado, x–r de otro y v–r de un tercero. Lo llamo *triángulo repartido*. La
pregunta era qué mecanismo lo elimina cuando el siguiente UP fija r.

## 2. Existen, y el review los mata al fijar

Fórmulas aleatorias, 10 por semilla (`splittri random 10 nvMin seeds`):

| vars | semillas | triángulos | repartidos | x→v sobrevive al fijar | sobrevive sin lado | muertos en una fila |
|---|---|---|---|---|---|---|
| 3+ | 1–6 | 5,5 M | 3212 | 532 | **0** | 2680 / 2680 |
| 4+ | 1–3 | 11,0 M | 10694 | 2132 | **0** | 8562 / 8562 |

Cuando x→v sobrevive, es porque algún lado ya lo conservaba al fijar. Fijar es por nodo del mapa, así que
otro nodo del camino con el mismo nodo del mapa que r sirve de apoyo.

Cuando muere, lo hace **siempre de forma directa en una fila de cláusula**: hay un paso de cláusula en el
que todas las filas comunes a x y v excluyen el valor fijado. Al fijar, esas filas pierden su único dueño
en el paso de r, `cleanInvalid` las quita, y x y v se quedan sin dueño común en ese paso. En ningún caso
hizo falta una cascada.

## 3. La traza (`splittrace 1 1 19 19 0 3 0 2 1 0 0 - - 5 0 4 1`)

Fórmula de 4 variables y 10 cláusulas. La tercera es (¬x1 ∨ x0 ∨ ¬x2), en el paso 11. La clave es `19.0`,
la fusión final, con cuatro lados.

* x = `3.0<2.1` (x1 = 1), v = `0.0` (x0 = 0), r = `5.0` (x2 = 1).
* En la unión, las filas comunes a x y v en el paso 11 son `11.1<10.6` y `11.1<10.7`. La fila 1 = 001
  dice ¬x1 falso, x0 falso y ¬x2 cierto, es decir, **exige x2 = 0**.
* Al fijar x2 = 1, esas filas mueren. Tras el review, x solo conserva x0 = 1 y v solo conserva x1 = 0, y
  no comparten dueño en ningún paso. Basta el review base; el agresivo no añade nada aquí.

Es tu mecanismo: la fila de una cláusula fija tres variables a la vez, y la combinación x0 = 0, x1 = 1,
x2 = 1 es justo la fila que el mapa omite.

## 4. Lo que sugiere para formalizar

`SideKeepFar` se reduciría a dos hechos:

1. **(fila)** si una entrada ancha x→v no está en ningún camino que tome r, hay un paso de cláusula donde
   toda fila común a x y v excluye el valor de r;
2. **(muerte directa)** en ese caso, fijar r y hacer el review quita x→v.

El punto 2 es mecánico (pin, `cleanInvalid`, nodo común). El punto 1 es el que falta: que la
incompatibilidad de un triángulo repartido la presencie una sola fila. Las medidas no dan excepciones, y
sospecho que viene de que cada nodo de la unión es una arista del mapa y de cómo las filas heredan dueños
de sus lados.
