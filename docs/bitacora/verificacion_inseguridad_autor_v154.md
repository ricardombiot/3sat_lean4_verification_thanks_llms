# Verificación para el Autor v154: fijar atraviesa un envío; queda la unión por clave

Ricardo, soy Claude (Opus 5). He atacado `PinCommutes1` (v153) por inducción sobre las líneas. El caso
base y el paso por un envío quedan demostrados sin hipótesis. Queda una sola afirmación, sobre la unión
por clave.

Rama `spaik`, build de `AbsSat` (226 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Commit
`2ceb3bb`. Módulo nuevo: `PinSend.lean`; ampliado: `PinHistory.lean`. Sonda nueva: `helly pinjoin`.

---

## 1. La cadena del veredicto

```
veredicto ⇐ PinCommutes1 ⇐ PinAdvance ⇐ PinJoin
               (v153)        (inducción     (pin_send demostrado;
                              sobre líneas)   queda la unión)
```

## 2. `PinCommutes1` es un paso de la máquina (`PinHistory`)

> **`PinAdvance`**: si cada estado fijado de una línea cabe dentro del estado con la misma clave de otra
> línea, lo mismo pasa tras avanzar las dos líneas un paso.

| resultado | contenido |
|---|---|
| **`topPin_key`** (sin hipótesis) | fijar el paso más alto de un estado válido es fijar su clave |
| `mem_branch_top` | la rama de P ++ [r], en el paso de r, conserva el estado con clave r |
| **`pinCommutes_all`** | bajo `PinAdvance`, fijar un valor conmuta con la historia **en todas las líneas**, por inducción |
| `pinCommutes1_of_advance`, `sat_of_pinAdvance` | `PinCommutes1` y el veredicto |

**El caso base desaparece**: cuando la fijación cae en el paso de la clave, es la clave misma, y la rama
conserva ese estado tal cual. Es tu observación de que fijar la clave es gratis.

## 3. Fijar atraviesa un envío (`PinSend`, sin hipótesis)

| resultado | contenido |
|---|---|
| `sup_transfer` | un soporte se transporta a lo largo de un `Embedded` |
| `sup_weak` | un soporte cuyos miembros cumplen los requisitos débiles sobrevive a su filtro (como dijiste, los débiles no cambian nada: aquí cuestan un lema) |
| `sup_below_addNode` | por debajo del nodo nuevo de un UP, un soporte del estado subido es un soporte del estado anterior |
| **`pin_send`** | si el origen fijado cabe en `B`, el envío fijado cabe en el envío de `B`, que es válido |
| `pinned_source_valid` | un envío fijado válido tiene su origen fijado válido |

La idea de `pin_send`: la parte del envío fijado que queda por debajo de su cima es un soporte. Sobrevive
en el estado de origen, atraviesa la fijación hasta `B`, atraviesa el filtro débil y los requisitos del
destino, y el review la conserva. La cima es el nodo nuevo, idéntico en los dos lados porque la clave es
la misma.

## 4. Lo que queda: `PinJoin`

> **`PinJoin`**: en una unión por clave de la máquina, si la unión fijada (un valor de literal) y
> revisada es válida, algún lado fijado lo es, y la unión fijada cabe dentro de cualquier estado con esa
> clave que contenga todos los lados fijados válidos.

`pinAdvance_of_join` demuestra que basta con esto, y `sat_of_pinJoin` da el veredicto.

Es la forma más pequeña del núcleo que aparece desde v138 (`ReviewJoin`): **una sola fijación de
literal, en las uniones que hace la máquina**. Ya no aparecen ni los envíos, ni varias fijaciones, ni la
historia.

## 5. Medidas

| sonda | qué mide | resultado |
|---|---|---|
| `pinjoin` | la forma canónica de `PinJoin` en cada unión de la ejecución y cada literal por debajo | paridad k3 desc: 386 fijaciones; Tseitin K4: 492; paridad k3 asc: 990. **0 nodos y 0 entradas fuera; siempre queda un lado válido**. Aleatorias (3 semillas × 20 fórmulas, 4–6 variables): 2.540 uniones, 35.370 fijaciones, **0** |
| `pin1` (v153, completada) | una fijación contra la rama, en todas las líneas | además de v153: paridad k3 asc 1.956, paridad k5 3.642, Tseitin prisma 4.446, Tseitin K3,3 4.446: **0** |

## 6. Cómo atacar `PinJoin`

Ya está demostrado `ReviewJoin ⟸ SupportSplit ⟸ RunPaths` (`PartSplitReal`): basta con que cada entrada
de la unión revisada esté sobre un camino fijado de un lado. `PinJoin` es el caso de una fijación de
literal. La diferencia con los intentos anteriores es que ahora, dentro de la inducción conjunta de
v153, **los lados de la unión son exactos hacia los literales** (`SoundAt`), y
`JoinSide.sideCover_of_sound` ya da la mitad de cobertura a partir de lados exactos. El paso siguiente
es llevar la inducción conjunta hasta `PinJoin`, usando esa exactitud de los lados.

## 7. Adenda: el review hace trabajo global en `PinJoin`

Medí cuántas entradas de la unión, **entre nodos que sobreviven**, no están en la unión de los lados
fijados y revisados: paridad k3 desc **320**, Tseitin K4 **10.464**. El review de la unión las elimina
todas (0 fuera al final). A diferencia del caso base con literales (0 entradas ajenas), aquí no hay atajo
estructural: que el review de la unión no conserve nada que los lados no conserven es, otra vez, la
afirmación de pegado (`RunPaths` / `SurvivorsRealized` en su forma de una fijación).
