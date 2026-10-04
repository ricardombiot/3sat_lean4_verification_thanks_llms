# Verificación para el Autor v162: la muerte directa, demostrada; queda la fila testigo

Ricardo, soy Claude (Opus 5). Rama `spaik`, módulo nuevo `PinDeath.lean`. Build de `AbsSat` (229 jobs),
sin `sorry`, axiomas `[propext, Quot.sound]`.

## 1. La muerte directa (`pinned_common`, `direct_death`)

Es la mitad mecánica de lo que vimos en v161. Sin hipótesis:

* **`pinned_common`**: si una relación x → v sobrevive a fijar r y al review agresivo, entonces **en cada
  paso** hay un nodo z común a x y v que es dueño de un nodo de r (el nodo del mapa fijado). Todo eso ya
  estaba en la unión antes de fijar. Viene de dos reglas del review: el nodo común en cada paso
  (`sharesEveryStep`) y la cobertura del paso de r, donde tras fijar solo queda r.
* **`direct_death`**: leído al revés, si en algún paso todo nodo común a x y v excluye r, fijar r y hacer
  el review quitan x → v. Es lo que la sonda vio en todos los casos, en una fila de cláusula.

## 2. El veredicto, reducido a la fila testigo (`sat_of_rowWitness`)

> **`RowWitnessAt`**: sea x → v una relación de una unión por clave, y r un valor de literal tal que en
> cada paso algún nodo común a x y v es dueño de un nodo de r. Entonces algún camino real de la unión
> pasa por x, v y r.

Cuando la fila testigo hace falta, la inducción conjunta ya ha dado la exactitud: toda relación de la
unión está en un camino de un lado.

La novedad es que **la hipótesis ya no habla de fijar ni del review posterior**. Habla solo de la unión
tal como la deja `do_join!`: sus nodos (aristas del mapa) y sus dueños. `sideKeep_of_row` hace el resto
con `pinned_common` y `side_of_path`, y lleva a `SideKeepAt` y al veredicto.

## 3. Lo que falta: la fila testigo misma

Tenemos caminos por pares: uno por x y v, otro por x y z, otro por v y z, y otro por z y r, con un z
en cada paso. Hay que pasar a **un solo** camino por x, v y r. Probé las vías locales y no bastan:

* un nodo común en la cima es la cima de un lado, y solo dice que x, v y r están en ese lado, no que
  estén en un mismo camino;
* un nodo común en el paso de r es el propio r, y da de nuevo tres pares;
* cambiar u en el camino de x → v rompe las cláusulas de u en sus otras variables, que la fila común
  fija para los caminos de z, no para el de x → v.

Las medidas de v161 dicen que la máquina no falla aquí: 0 casos sin lado en 13.906 triángulos
repartidos. Lo que falta es el argumento de por qué las filas comunes, paso a paso, bastan para dar
un camino entero.
