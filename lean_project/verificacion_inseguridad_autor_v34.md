# Verificación para el Autor v34: `parent_id` no era decoración — una cadena está determinada por sus ids de mapa

Ricardo, soy Claude (Opus 5). Atacada la condición local sobre `parent_id`. El resultado es más fuerte de lo que esperaba y **deshace el "factor dos"** de v33.

---

## 1. `parent_id` no es decoración

`addNode` construye `⟨d, g.map_parent⟩`, donde `map_parent` es **el nodo de mapa que visitó el último `up` en esa rama**. Y los `parents` del nodo nuevo son exactamente la línea anterior de esa misma rama. Esas dos cosas están ligadas por construcción, y de ahí salen dos invariantes:

| | |
|---|---|
| **`TL`** | la línea de arriba de un estado lleva el nodo de mapa que nombra `map_parent` |
| **`PMP`** | todo padre de un nodo lleva el id de mapa que nombra el `parent_id` del nodo |

Demostrados para toda la máquina — `initSeed`, `addNode`, `join` y toda la cadena de poda.

## 2. La condición local

```lean
theorem parentId_coherent (h : GPathM) (hpmp : PMP h) (sel) (hchain : IsChain h sel) ... :
    (sel (k + 1)).parent_id = some (sel k).id
```

> **El nodo que la cadena elige en el paso `k+1` registra el id de mapa que eligió en el paso `k`.**

Es el enlace padre de `IsChain`, leído sobre los ids en vez de sobre las listas.

## 3. Y lo que fuerza

```lean
theorem chain_eq_of_mapIds_eq (h : GPathM) (hpmp : PMP h) (sel sel') ...
    (hids : ∀ k, ... → (sel k).id = (sel' k).id) : ... sel k = sel' k
```

> **Una cadena está determinada por su secuencia de ids de mapa.**

En el paso 0 por `root_shape` (v29): el nodo es raíz, `parent_id = none`. En cada paso siguiente, `parent_id` queda fijado por el id de mapa del paso anterior. Dos cadenas que coinciden en todos los ids de mapa **son la misma cadena**.

---

## 4. Qué le hace esto a v33

v33 dejó el hueco así: *"en un paso pinzado el conjunto de owners tiene a lo sumo dos `PathNodeId`, y falta que la cadena elija el que está ahí"*. Con 1,65 millones de pares medidos y ancho máximo 2.

**Ya no hay elección.** El `PathNodeId` que la cadena elige en un paso pinzado está **determinado**:

- su id de mapa es el que nombra el requisito (`ReqSatisfying`),
- su `parent_id` es el id de mapa del paso de abajo (`parentId_coherent`).

No es "uno de dos". Es uno solo, fijado por la cadena misma.

Lo que sigue faltando es únicamente esto:

> **que ese `PathNodeId` determinado esté en la lista de owners.**

Que es una pregunta de pertenencia sobre un elemento concreto, no una búsqueda. Y explica el "factor dos" medido: los dos owners de un paso pinzado corresponden a **dos ids de mapa distintos en el paso de abajo**, y la cadena, al haber elegido ya uno de ellos, selecciona cuál le toca.

---

## 5. Estado

```
ChainSound
  ⟸ IsChain, son_link, root_shape, self_owned    demostrados
  ⟸ PairwiseOwned
       ⟸ id de mapa correcto                     demostrado (v33)
       ⟸ parent_id determinado por la cadena     demostrado (v34)
       + que el path-node determinado esté en la lista de owners
  + ∃ camino req-satisfactorio en cada estado válido    medido, 0 sin camino
```

De la co-posesión quedan **dos piezas demostradas y una de pertenencia**. Del resto, tu afirmación central, sola.

---

## 6. La quinta vez

Vuelve a pasar lo mismo que en v30: la pieza que faltaba estaba en una decisión de diseño tuya.

`parent_id` podría haber sido un campo informativo. No lo es: al ligarlo a `map_parent` y hacer que los padres de un nodo sean la línea anterior de la misma rama, hiciste que **el `PathNodeId` codifique un paso de historia**. Eso es lo que hace que una cadena esté determinada por sus ids de mapa — y por tanto lo que quita la elección del hueco.

v14 ya había dicho que `PathNodeId` guarda un nivel de historia. Lo que no habíamos visto es para qué sirve.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 70 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
