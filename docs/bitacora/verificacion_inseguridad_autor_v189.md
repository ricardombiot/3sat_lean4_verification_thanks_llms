# Verificación para el Autor v189: la escalera del lector, lo realizado y lo previsto

Ricardo, soy Claude (Opus 5.5). Este informe no trae una medición nueva, sino el **mapa de la escalera**
tal como queda en la rama `pair-mode` después de los v185–v188: qué está demostrado, qué hipótesis
quedan, cómo se ordenan entre sí y qué está previsto. Al final, la lista de lo pendiente.

Rama `pair-mode`. `lake build AbsSat` verde (272 jobs), sin `sorry`, todos los teoremas citados con los
axiomas `propext` y `Quot.sound`. Módulos principales: `GPathM.lean` (la regla), `Pruned.lean`,
`CleanInvalid.lean`, `PairHelly.lean`, `OneStep.lean`. Último commit de prueba: `1468c80`.

---

## 1. La escalera en una figura

```
readerVerdictW φ = true ↔ Satisfiable φ
  ⇐ SegGood en todo estado del lector                    (TopGoodLadder, demostrado)
    ⇐ en cada pin: SegGood llega al punto fijo           (segGood_pinReview, PinDoomed)
        ⇐ PinFirstRound   ⇐ PairHelly + CleanRest         (pinFirstRound_of_pairHelly)
        ⇐ LaterValid                                      (hipótesis, medida)
        ⇐ AggInactive     — TEOREMA con la regla          (aggInactive_of_revOk)
    PairHelly (cleanPair X)
      ⇐ todo tramo se alarga un paso arriba y abajo       (pairHelly_of_oneStep)
        ⇐ un testigo de g sobrevive (Survives)            (oneStepUp_of_survives)
          ⇐ PairExact g + KeptOwn                         (survivesUp_of_keptOwn)
            vivo:      (W2)  survives_of_pinned_owner
            enlazado:        link_cleanPair
            simétrico, en la global: OwnSymmetric_cleanPair, nodesGow_cleanPair
          ⇐ SegThroughPin                                 (keptOwnUp_of_segThroughPin)
```

`X` es el estado pinchado de cada pin (`filterWeak g (paso de q, [q])`), `g` el estado del lector y
`C = cleanPair X` el estado tras la limpieza con la regla de parejas.

## 2. Lo realizado

### 2.1 La regla de parejas, en la máquina y en el modelo (v185–v186)

* **Julia** (`graph_path_filter_pair.jl`, `PAIR_MODE`): 80 instancias con mismos veredictos, estados,
  soluciones y vueltas; la rama «inconsistente» del agresivo baja a 0; +6 % de tiempo.
* **Lean, el modelo**: `reviewPass = reviewSons ∘ reviewParents ∘ cleanPair`.
  * **Correcta**, no pierde soluciones: `ChainSound_pairSweep`, `ChainSound_cleanPair`.
  * **Invariantes**: todos llevados a `cleanPair`. `Fabric` ganó una cláusula nueva (`agg`).
  * **Simetría**: `OwnSymmetric_cleanPair`.
  * **Punto fijo**: `pairFixed_cleanPair`, es decir, tras `cleanPair` la regla ya no quita nada.
* **`AggInactive` es un teorema**: en el punto fijo del review, el barrido agresivo es la identidad.
* Una versión rápida del test de pareja, con la igualdad demostrada (`@[csimp] pairShares_eq_fast`).

### 2.2 `PairHelly` paso a paso (v187–v188)

* **Alargar paso a paso** (`segGood_of_oneStep`): si todo tramo se alarga un paso en cada dirección,
  vale `SegGood`.
* **Helly de dos elementos** (`helly_two`, `extUp_of_two`): con uno o dos candidatos, un teorema.
* **Helly por cajas** (`helly_box`, `extUp_of_boxes`) y la mitad «⊆» de las cajas (`req_shared`).
* **El triángulo con el extremo**: demostrado cuando el extremo es de la pareja
  (`triTopUp_of_inner`); reducido a `Tri3` en el paso contiguo para las parejas interiores
  (`triTop_of_tri3`).

### 2.3 Por la historia (v188 y esta tanda)

* **El testigo existe** en el estado del lector, sin Helly (`witUp_of_segExact`, `witUp_of_segGood`).
* **(W2), el testigo con un nodo pinchado sobrevive a la purga** (`survives_of_pinned_owner`), dada la
  exactitud por parejas de `g`.
* **El enlace padre–hijo sobrevive a `cleanPair`** (`link_cleanPair`), si los dos extremos se poseen
  mutuamente y están en la global. La prueba sigue la computación: la purga no toca enlaces entre vivos,
  la regla no toca enlaces, y el corte conserva los admitidos.
* **`SegThroughPin` implica `KeptOwn`** (`keptOwnUp_of_segThroughPin`, `keptOwnDown_…`): el orden de
  las hipótesis.

## 3. Las escaleras disponibles

Todas demostradas, todas con `hStart` (la línea final revisada no tiene tramos sin cadena), y con estas
hipótesis por pin:

| teorema | hipótesis por pin |
|---|---|
| `readerVerdictW_iff_of_roundExact` | `RoundExact` (la primera vuelta deja todo tramo en una cadena) |
| `readerVerdictW_iff_of_pairHelly` | `PairHelly (cleanPair X)`, `CleanRest X`, `LaterValid X` |
| `readerVerdictW_iff_of_survives` | `SurvivesUp/Down g C`, `CleanRest`, `LaterValid` |
| `readerVerdictW_iff_of_kept` | `PairExact g`, `KeptUp/Down` (con enlace), `CleanRest`, `LaterValid` |
| **`readerVerdictW_iff_of_keptOwn`** | **`PairExact g`, `KeptOwnUp/Down`, `CleanRest`, `LaterValid`** |

La última es la más fina. Todo lo que no está en esa lista está demostrado.

## 4. Las hipótesis que quedan, ordenadas

| hipótesis | qué dice | medido | se deduce de |
|---|---|---|---|
| `hStart` | la línea final revisada no tiene tramos sin cadena | 0 fallos (v183) | — |
| `PairExact g` | cada entrada de una tabla del lector está en una cadena sana con su dueño | 50.517 parejas, 0 fallos | — |
| `KeptOwnUp/Down` | un testigo de `g` que posee un nodo pinchado sigue en la tabla de todo miembro tras `cleanPair` | todo tramo tiene alguno; 0 tramos sin ninguno | `SegThroughPin` |
| `CleanRest` | tras `cleanPair`: I1, I1-hijos, padres/hijos vivos, autoposesión | 0 fallos | — |
| `LaterValid` | las vueltas siguientes que progresan empiezan listas | ninguna progresa | — |

Y las formas alternativas, todas medidas sin fallos:

* `SegThroughPin` ⟹ `KeptOwn` (demostrado). Dice: todo tramo que sobrevive a `cleanPair` tras un pin
  se extiende a una cadena del lector que pasa por el pin.
* `TriTop` + `SmallOrHelly` ⟹ `PairHelly` (demostrado), con `Tri3` ⟹ `TriTop` (demostrado).
* `BoxHellyUp` ⟹ el paso grande de las cláusulas (demostrado).

**El núcleo** en su forma más local es `KeptOwn`: la limpieza y la regla no quitan ese testigo de la
tabla de ningún miembro. Es de tipo intersección (el testigo tiene que quedar en todas las tablas a la
vez), pero ahora es un nodo concreto que ya estaba en todas las tablas antes del pin.

## 5. Lo previsto

### 5.1 En la prueba

1. **`KeptOwn` por la regla.** Lo que puede quitar el testigo de la tabla de un miembro es el corte
   contra la global o la regla de parejas. El corte no puede, porque el testigo sigue vivo y está en la
   global; se puede demostrar como el enlace. Queda la regla: que nunca separe a un miembro de ese
   testigo, es decir, que compartan entrada en cada paso durante todo `cleanPair`. Plan: medir en qué
   ronda de `pairFuel` se pierden los 62 testigos que la regla quita (v188), y si los que se conservan
   comparten con el miembro un camino por el pin en cada paso (lo que daría la entrada común).
2. **`PairExact` como invariante del lector.** Hoy es hipótesis sobre cada estado del lector. Si se
   conserva de un estado del lector al siguiente, pasaría a formar parte de la inducción de la escalera,
   como `SegGood`.
3. **`CleanRest`**: cinco piezas de forma (I1, I1-hijos, padres e hijos vivos, autoposesión) tras
   `cleanPair`. La limpieza establece parte de ellas; es trabajo mecánico.
4. **`LaterValid`**: ninguna vuelta siguiente progresa en la medición. Si se demuestra que tras la
   primera vuelta del pin el estado es punto fijo, desaparece.

### 5.2 En la máquina

5. **La regla en el ejecutable IO** (`GraphPath.lean`), en dos fases como en Julia, y las comparaciones
   diferenciales (`exec-diff`, `diffTest`).
6. **La velocidad del modelo**: `pairSweep` es de orden N³ con listas. Indexar nodos y tablas una vez
   por barrido, con la igualdad demostrada como en `pairSharesFast`, para que `diffTest` vuelva a pasar
   su tercera banda.
7. **Adoptar la regla en Julia** (`PAIR_MODE = :on` por defecto).

### 5.3 Una propuesta abierta

8. **Binarizar las cláusulas con una ventana prohibida** (v187, §5): haría trivial el Helly de un paso
   en cualquier estado. Hoy no hace falta para la escalera por la historia, pero sigue siendo la forma
   de convertir las piezas 3 y 4 en teoremas sin hipótesis.

## 6. Una frase

La escalera ya no pide que las tablas resuelvan un Helly. Pide que, tras cada pin, la limpieza deje en
las tablas del tramo un nodo que ya estaba en todas ellas: el testigo que el propio lector había
garantizado.
