# Verificación para el Autor v158: el veredicto bajo un único cambio de valor

Ricardo, soy Claude (Opus 5). He quitado de la hipótesis todo lo que eran pares: ahora los lleva la
historia. Rama `spaik`, build de `AbsSat` (228 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`.
Commit `b344334`. Módulo nuevo: `PinClause.lean`.

## 1. La hipótesis que queda

> **`FlipSat`**: en la etapa de cláusulas, para cada entrada x → v de una unión por clave fijada por un
> valor de literal r (variable u), **alguna asignación cuya rama pasa por x, por v, por la clave y por las
> fijaciones de la rama sigue cumpliendo todas las cláusulas por debajo de la cima cuando u toma el valor
> de r**.

`sat_of_flipSat`: el veredicto bajo `FlipSat` sola. Solo cuentan las cláusulas que contienen u
(`satBelow_glue`, v157).

## 2. Cómo se quitan los pares: la inducción conjunta

Por inducción sobre la línea, para todas las ramas a la vez, se llevan dos hechos:

| hecho | cómo se mantiene |
|---|---|
| **toda rama es exacta hacia todos los pasos** (`LineSoundL Full`) | los envíos gratuitos valen ya para cualquier conjunto de pasos (`soundAt_sent_ofL`, `soundAt_weak_sendL`, `soundAt_pin_topL`); el envío a una fila de cláusula, porque sus tres fijaciones conmutan con la historia en esa línea (`pc3_at`) y la rama que las lleva es exacta (`send_sound_full`, `adv_sound_full`) |
| **fijar un valor conmuta con la historia** (`PC1At`) | fijar la clave es gratis (`top_case`); si no, un avance (`advance_at`), con `PinJoin` en esa línea: en la etapa de variables por `pinJoinVar` (v156), en la de cláusulas por los caminos de la unión exacta (`flipAt_of_sat`) más `FlipSat` |

## 3. Lo que ya está demostrado sin hipótesis, en resumen

* las ramas no pierden caminos (v156);
* la etapa de variables entera (v156);
* fijar atraviesa un envío (v154);
* el pegado de caminos conserva todos los nodos, filas incluidas (v157);
* la exactitud de todas las ramas en todas las líneas, dada la conmutación en la línea anterior (esta
  entrega).

## 4. Qué pide `FlipSat`, en tus términos

Entre los caminos de la unión que pasan por x y por v, uno cuyas cláusulas con la variable u se cumplan
**sin depender del valor contrario al fijado**. Si u no tiene cláusulas por debajo, o el camino ya toma
el valor de r, es inmediato. En otro caso, para cada una de esas cláusulas el review da una fila con el
valor de r común a x, a v y a r. `FlipSat` pide que el camino elija esas filas a la vez.
