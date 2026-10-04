# Verificación para el Autor v181: las pasadas de coherencia, formalizadas — y dónde se detiene la prueba a pasada entera

Ricardo, soy Claude (Opus 5.5). Este informe sigue al v180. El v180 cerraba la escalera con una
hipótesis honesta (`ReaderTopGood`) y proponía demostrarla **a pasada entera**: pieza a pieza del
review. Aquí está lo que se consiguió —las dos pasadas de coherencia (padres e hijos) formalizadas
enteras—, lo que la medición enseñó sobre `cleanInvalid`, y una propuesta de cambio en la máquina
(§6) que simplifica la prueba.

Rama `spaik-window3`. `lake build AbsSat` verde (258 jobs), sin `sorry`, sin `Classical.choice`.
11 commits desde `0ac8526` (el del v180). Módulos nuevos: `PassCtx.lean`, `PassSons.lean`; ampliado
`TopGoodLadder.lean`.

---

## 0. Dónde estamos, en una línea

```lean
theorem readerVerdictW_iff_of_readerSegGood (h : ReaderSegGood) (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ
```

La misma escalera del v180, pero **sin anfitrión**: `ReaderSegGood` dice que en todo estado válido
que el lector visita, todo tramo (enlazado por padres, poseído por pares) tiene, en cada paso fuera
de él, una entrada común a todos sus nodos. La cadena por cada entrada sale bajando y subiendo desde
ella (`TopGoodUp.ownerChained_of_segGood`). Medida sin fallos en todas las clases de estado.

## 1. Las dos pasadas de coherencia, enteras

```lean
theorem pstate_reviewParents (hLS : LocSymStable) (g : GPathM) (h : PState g) :
    PState (reviewParents g)
theorem pstate_reviewSons (hLS : LocSymStableS) (g : GPathM) (h : PState g) :
    PState (reviewSons g)
```

`PState` es lo que un estado de la pasada lleva: `SegGoodL` (la versión de `SegGood` con entrada
común **viva**), `I1L`/`I1sL` (los owners vivos un paso por debajo/encima son padres/hijos), padres
e hijos vivos, autoposesión, simetría local, ids sin repetir, `NotRoot`, `RootAtZero`, pasos en rango.
Cada `reviewNode` de cada pasada lo conserva:

* **No elimina el nodo que procesa** (`kept_reviewNode_parents`, `kept_reviewNode_sons`). Es el truco
  de alargar la cadena del v180, ya en Lean: un padre vivo `u` de `x` en su tabla alarga el tramo
  `[x]` a `[u, x]` (en la pasada de hijos, un hijo `s` lo alarga a `[x, s]`), y las entradas comunes
  de ese tramo están en la tabla de `u`, así que sobreviven al corte con la unión de padres. `x`
  conserva una entrada en cada paso, un padre y un hijo: sigue siendo válido.
* **Conserva `SegGoodL`** (`segGoodL_reviewNode_parents/sons`): la prueba del v179 reescrita con las
  hipótesis vivas.
* **Conserva `I1L` e `I1sL`**: un vecino vivo que tiene a `x` en su tabla queda en la nueva tabla de
  `x`, así que el desenlace no lo toca (vía la simetría local en `[y]` y en `[x, y]`).
* **Conserva padres vivos, hijos vivos y autoposesión** (`pLive_reviewNode`, `sLive_reviewNode`,
  `selfL_reviewNode`), sin hipótesis: `reviewNode x` solo puede eliminar a `x`, y cuando lo hace lo
  desenlaza de todos.

La única hipótesis de cada pasada es que **la simetría local se conserva nodo a nodo**
(`LocSymStable`, `LocSymStableS`), medida sin fallos entre nodos vivos.

## 2. Una corrección al v179: las hipótesis tenían que ser «vivas»

El lema del v179 pedía que *toda* entrada de la tabla un paso por debajo fuera padre, **incluidos
ids ya muertos**. La máquina no lo cumple (`passhyp`, semilla 1): falla en 4.533 de 53.646 estados
de la pasada de padres, porque un nodo eliminado sale de las listas de padres pero no de las tablas.
Solo para entradas vivas: 0 fallos. Por eso todo el §1 está en versión viva, y hubo que medir que
`SegGood` tiene siempre una entrada común **viva**: 0 casos con solo entradas muertas en 227 millones.

Y un dato que simplificó mucho: **las pasadas de padres e hijos no eliminan ningún nodo** en la
máquina (0 de 53.646 y 53.101, semilla 1). El §1 lo demuestra.

## 3. Dónde se detiene: `cleanInvalid`

Encadenar las pasadas exige que `PState` valga al empezar la pasada de padres, es decir, a la salida
de `cleanInvalid`. Medido (`cleanpass`, semilla 1):

| | entrada de `cleanInvalid` | salida |
|---|---|---|
| envíos (línea filtrada) | `SegGood` falla en 504 casos | 0 fallos: `cleanInvalid` lo arregla |
| pines del lector | 0 fallos | **204 tramos sin entrada común, 322 con solo entradas muertas** (de 252.753) |

Y esos tramos **mueren todos en la misma vuelta** (`doomed`): 74 de 74 (semilla 1), 12 de 12
(semilla 7), en las pasadas de padres e hijos que siguen. Ninguno sobrevive al review.

Es tu cascada, exactamente —*un nodo sin compatibilidad se vuelve inválido, se elimina, sus vecinos
quedan huérfanos y caen*—, pero **cruza pasadas**. `SegGoodL` no es un invariante de cada pasada:
`cleanInvalid` deja tramos condenados que la coherencia remata después. Lo verdadero es «los tramos
que sobreviven a la vuelta tenían entrada común viva», y usarlo en los lemas de las pasadas es
circular (para saber que `[x]` sobrevive hay que saber que `x` sobrevive). Ahí está la frontera.

## 4. Mediciones que confirmaron lo del v180

| sonda (semilla 1) | medida | resultado |
|---|---|---|
| `pairline` | tablas exactas en la línea y en los envíos paso a paso | 0 de 1.538.505 y 0 de 27.989.806 |
| `triplestep` | ternas que sobreviven a un filtro de un paso, con cadena en el estado de antes | 0 de 39.288.791 |
| `passhyp` | hipótesis vivas en las pasadas de padres e hijos | 0 fallos; 0 nodos eliminados |
| `cleanpass` / `doomed` | §3 | los tramos condenados mueren en la misma vuelta |

## 5. Lo que falta

1. **La vuelta completa mata a los condenados** —los que deja `cleanInvalid` y los que traía la
   entrada—: es la completitud del review dentro de una vuelta. La parte difícil de verdad.
2. La **estabilidad de la simetría local** (`LocSymStable`, `LocSymStableS`).
3. El **barrido agresivo**, pareja a pareja.
4. El **ensamblaje** en `reviewPass`, `review`, `reviewAgg` y `ReaderSegGood`.

## 6. Propuesta para la máquina Improves: `cleanInvalid` en dos fases

### El problema

Hoy `clean_invalid_nodes!` (Julia, `graph_path_filter.jl`) y su espejo `cleanInvalid` (Lean) recorren
los nodos **uno a uno**: cortan la tabla del nodo con la tabla global *tal como está en ese momento*
y, si queda inválido, lo eliminan de la global. Consecuencias:

* **depende del orden**: un nodo procesado antes de una eliminación conserva en su tabla el id
  eliminado; uno procesado después, no;
* **deja ids muertos en las tablas** hasta la vuelta siguiente (`midinv`: unos 19.000 estados
  intermedios; `cleanpass`: los 322 tramos con «solo entradas muertas»);
* obliga a la prueba a llevar versiones «vivas» de todas las propiedades (§2), y hace que
  `cleanInvalid` sea demostrable solo a pasada entera, no nodo a nodo.

### La propuesta

Separar las dos cosas que hace:

1. **Fase de eliminación, hasta estabilizar**: repetir *eliminar de la global los nodos cuya tabla,
   cortada con la global actual, no es válida* hasta que la global no cambie.
2. **Fase de corte, a la vez**: cortar la tabla de **todos** los nodos supervivientes con esa global
   final, y re-enlazar.

En Julia, esquemáticamente:

```julia
function clean_invalid_nodes!(gpath :: GPath)
    # fase 1: eliminar hasta estabilizar, sin tocar las tablas todavía
    changed = true
    while changed && gpath.is_valid
        changed = false
        for node in all_nodes(gpath)
            owners_now = PathDocumentOwners.intersect(node.owners, gpath.owners)  # copia
            if !is_valid_with_owners(gpath, node, owners_now)
                remove_node_owner!(gpath, node.id); clean_links!(gpath, node)
                changed = true
            end
        end
    end
    # fase 2: un solo corte, con la global final
    for node in all_nodes(gpath)
        PathDocumentOwners.intersect!(node.owners, gpath.owners)
    end
end
```

(`is_valid_with_owners` es `is_valid_node` evaluado con una tabla dada, sin modificar el nodo.)

### Qué gana la formalización

* **Las tablas solo contienen nodos vivos** tras cada `cleanInvalid`: las versiones «vivas»
  (`I1L`, `SegGoodL`…) dejarían de hacer falta, y la hipótesis del v179 debería volver a cumplirse tal
  como estaba (a medir).
* **`cleanInvalid` deja de depender del orden**: su resultado es «global final + un corte», y su
  lema es una intersección, no una inducción sobre el orden de los nodos.
* Desaparecen los 322 casos de «solo entradas muertas».

### Qué no arregla

Los 204 tramos **sin ninguna** entrada común no los crea `cleanInvalid`: nacen de lo que el filtro
quita, y los eliminan las pasadas de coherencia. La completitud de la vuelta (§5.1) sigue siendo el
punto abierto. El cambio **simplifica** la prueba; no la **desbloquea**.

### Cómo verificarlo antes de adoptarlo

1. **Mismos resultados finales**: comparar, en `dos_de_tres.cnf` y las semillas 1 y 7, el estado final
   de cada `reviewAgg` (validez, tabla global, nodos con sus tablas, como en `seqsend`) y el veredicto
   del lector, con el `cleanInvalid` actual y con el de dos fases. No está garantizado que coincidan
   (no está demostrado que el review llegue al mismo punto fijo con otro orden de las reglas); la
   sonda lo diría.
2. **Coste**: contar las vueltas del review con cada versión; la fase 1 puede repetir recorridos,
   pero cada repetición elimina al menos un nodo.
3. **En Lean**: `cleanInvalid₂` nuevo junto al actual, con `Pruned`, `Keeps` y los invariantes de
   forma (`RCtx`, `SMP`, `PMS`, `SN`) demostrados para él; luego cambiar `reviewPass` y comprobar que
   `lake build AbsSat` sigue verde.

Si las dos primeras mediciones coinciden, el cambio no altera la máquina y deja la prueba más limpia.

## 7. Una frase sobre el tamaño de lo que queda

El v180 decía que faltaba una idea para `cleanInvalid`. Ahora sabemos con precisión cuál: la cascada
de eliminaciones **cruza pasadas** —`cleanInvalid` condena, la coherencia remata—, y la prueba tiene
que capturar la vuelta entera. Las dos pasadas de coherencia ya están demostradas por su cuenta, y el
`cleanInvalid` en dos fases quitaría el ruido de los ids muertos para que lo que quede sea solo esa
idea.
