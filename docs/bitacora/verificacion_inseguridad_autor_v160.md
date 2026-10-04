# Verificación para el Autor v160: solo quedan las incoherencias anchas

Ricardo, soy Claude (Opus 5). Dos cosas tras tus últimos mensajes. Rama `spaik`, build de `AbsSat` (228
jobs), sin `sorry`, axiomas `[propext, Quot.sound]`.

## 1. La unión sin revisar no tiene incoherencias (`union_review_keeps`)

He revisado paso a paso `do_join!` (unión de líneas, nodos y propietarios): el modelo en Lean hace lo
mismo. Y dentro de la inducción conjunta, toda entrada de una unión está sobre un camino real de un lado,
así que **revisar justo después de unir no quitaría nada**. No hay hueco en unir sin revisar: las
incoherencias las crean los valores que fija el siguiente UP, y las limpia su review.

## 2. Las incoherencias que no son anchas salen gratis (`sideKeep_of_far`)

Sea x → v una entrada de la unión tras fijar r (variable u). Un nodo **fija** u si todo camino que pasa
por él da a u el mismo valor: el literal de u o su negación (tus nodos separados para cada literal y su
negación), una fila de una cláusula con u (tus filas con los tres valores), o un nodo cuyo padre lo hace.

Si x o v fija u, la entrada no toma nada prestado:

* el review da a ese extremo un nodo común con r (regla del nodo común);
* la unión es exacta: hay un camino por ese extremo y por r;
* como el extremo fija u, **todo** camino por él toma el valor de r, en particular el de la entrada;
* ese camino está en el envío fijado de un lado.

## 3. Lo que queda

> **`SideKeepFar`**: las entradas **anchas** —ninguno de sus dos extremos fija la variable fijada— de una
> unión fijada las conserva también el envío fijado de algún lado.

`sat_of_sideKeepFar`: el veredicto bajo esta sola hipótesis (enunciada de forma constructiva: puede usar
las entradas no anchas, ya demostradas).

Es tu frase de que las incoherencias más anchas se detectan por simetría y por coherencia entre nodos
compatibles con el review agresivo: para una entrada ancha el review da, en el paso de u, el valor fijado
común a x y a v, y en cada cláusula de u una fila común a x, a v y al valor fijado. Falta demostrar que eso
basta para un camino común.
