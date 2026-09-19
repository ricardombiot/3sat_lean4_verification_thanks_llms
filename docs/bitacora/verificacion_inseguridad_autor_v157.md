# Verificación para el Autor v157: la etapa de cláusulas, reducida a un solo cambio de valor

Ricardo, soy Claude (Opus 5). He atacado `PinJoinClause` simplificándolo hasta dejar a la vista lo único
que no es un par. Rama `spaik`, build de `AbsSat` (227 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`.
Todo en `PinVar.lean`.

## 1. La cadena

```
veredicto ⇐ PinJoinClause ⇐ ClausePath ⇐ FlipAt
```

| resultado | contenido |
|---|---|
| `side_of_path`, `pinJoinAt_of_paths` | si cada entrada de la unión fijada está sobre la rama de una asignación que toma el valor fijado (`PathAt`), `PinJoin` se cumple en esa línea. Vale en **cualquier** etapa: es la segunda mitad de la prueba de la etapa de variables, sacada fuera |
| `sat_of_clausePath` | el veredicto bajo `ClausePath` (`PathAt` en la etapa de cláusulas) |
| **`glue_row`, `glue_agree_all`, `glue_canon`** (sin hipótesis) | el pegado funciona **en todos los pasos**, filas incluidas: si dos asignaciones eligen la misma fila, coinciden en sus tres variables, y la asignación pegada elige esa misma fila |
| `pathAt_of_flip`, `sat_of_clauseFlip` | `ClausePath` se reduce a `FlipAt` |
| `satBelow_glue` | solo pueden romperse las cláusulas que **contienen la variable fijada** |
| `glue_same` | si el camino ya toma el valor fijado, no hay nada que cambiar |

## 2. Lo que queda: `FlipAt`

Para cada entrada x → v de una unión fijada por un literal r (variable u):

1. un camino de la unión por x y v (b₁), uno por x y r (b₂), uno por v y r (b₃) — **pares**;
2. y la única condición que no es de pares: **b₁ con u puesto al valor de r sigue cumpliendo todas las
   cláusulas por debajo de la cima** — y, por `satBelow_glue`, solo cuentan las cláusulas que contienen u.

Con eso, la asignación pegada pasa por x, por v, por r, por la clave y por las fijaciones de la rama, y el
resto ya está demostrado.

## 3. Dónde está la dificultad, en tus términos

* Si u no está en ninguna cláusula por debajo de la cima, el cambio de valor es gratis.
* Si el camino de x ↔ v ya pasa por una fila de una cláusula de u que toma el valor de r, también
  (`glue_same`): la fila fija u.
* Lo difícil es el caso intermedio: las cláusulas de u que el camino de x ↔ v cumple **solo** gracias al
  valor contrario de u. Hay que elegir otro camino por x y v cuya fila en esas cláusulas ya tome el valor
  de r. El review da, para cada una de esas cláusulas, una fila así común a x, a v y a r (nodo común en el
  paso de la cláusula). Lo que falta es elegirlas **todas a la vez** en un mismo camino: las filas como
  nodos, pegadas entre sí.

Es el mismo núcleo de siempre, pero ahora localizado: solo las cláusulas de la variable fijada, y solo sus
filas.
