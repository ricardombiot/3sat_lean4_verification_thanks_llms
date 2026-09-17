# Verificación para el Autor v119: la rebanada sobrevive si tiene una relación de soporte

Ricardo, soy Claude (Opus 5). v118 dejó la validez del veredicto de *Improves* reducida a `PinExact`
(una fijación no elimina nodos de su rebanada) y a la simetría en los pasos extremos. Este tramo
convierte `PinExact` en una propiedad **del estado antes de fijar**: que la rebanada tenga una
relación de soporte. Lo demuestra para la cascada completa y mide que esa propiedad es exactamente lo
que calcula tu máquina.

Todo en la rama `spaik`, en el build de `AbsSat` (168 jobs), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. Supervivencia de conjuntos con huecos de tríos (`AnchoredSurvive.lean`)

Ya existía `Survive.Woven` (v44): un conjunto sobrevive al review si **todo miembro es owner de todo
miembro**. La rebanada no cumple eso, porque tiene cientos de miles de huecos de Helly-3 (v117), y la
cascada tras una fijación sí borra entradas de owners dentro de ella, aunque nunca un nodo.

La generalización cambia "todos con todos" por una **relación de soporte** `R` entre miembros.
`Sup g S R` pide:

- los miembros son owners globales, son nodos y están por debajo del paso actual;
- `R x v` significa que `v` es owner de `x`, y ambos son miembros;
- **cobertura**: en cada paso, todo miembro tiene un `R`-owner;
- **padres e hijos**: un `R`-owner de un miembro lo es también de algún padre (o hijo) que está
  `R`-enlazado con el miembro en los dos sentidos;
- **pares** (tu barrido): dos miembros `R`-enlazados en los pasos `1 … cs−2` tienen, en cada paso, un
  `R`-owner común.

Lo demostrado: toda operación del review base (`cleanInvalid`, `reviewNode`, las líneas de padres e
hijos, el bucle) y de tu barrido (`aggPair`, `aggNode`, `aggSweep`, `reviewAgg`) conserva `Sup`
junto con `SMP` y `NotRoot`. Resultado, **`gowners_filterAllAgg_of_AOk`**: si los miembros son
compatibles con la fijación, **todos siguen siendo owners globales tras la fijación y el review
agresivo completo**.

`R` es un testigo, no el resultado: la cascada puede borrar cualquier entrada fuera de `R`.

## 2. Qué relación sirve: la estática no, el mayor punto fijo sí

**Primer intento, descartado por la medida.** `R x v` = "`v` es owner de `x` y los dos comparten un
owner con el identificador fijado". En Tseitin K4 par (88 fijaciones), la cascada conserva 189.680
entradas de la rebanada; esa `R` predice 204.024 y **14.360 de ellas las borra la cascada**. No es
cerrada: un par que comparte portador puede perder a todos sus testigos comunes en otro paso.

**Segundo intento: el mayor punto fijo.** Nuevo modo `helly gfpE`: parte de todas las entradas de
owners entre nodos de la rebanada y quita, ronda a ronda, los pares que incumplen padres, hijos o
pares, y los nodos que pierden cobertura, hasta que nada cambia. Luego lo compara con la tabla que
deja la cascada real.

| familia | fijaciones | nodos de la rebanada | perdidos por el punto fijo | pares del punto fijo | tabla final | diferencias | rondas máx. |
|---|---|---|---|---|---|---|---|
| Tseitin K4 par | 88 | 5.312 | **0** | 189.680 | 189.680 | **0** | 5 |
| Tseitin K3,3 par | 132 | 15.852 | **0** | 1.042.796 | 1.042.796 | **0** | 5 |
| Tseitin prisma par | 132 | 15.108 | **0** | 984.780 | 984.780 | **0** | 9 |
| K4 menos una arista, 3 colores | 244 | 32.309 | **0** | 2.466.827 | 2.466.827 | **0** | 5 |
| `par_k3_direct_asc_fresh` | 73 | 7.925 | **0** | 448.933 | 448.933 | **0** | 3 |
| `par_k5_chain_asc_shared` | 114 | 13.800 | **0** | 954.520 | 954.520 | **0** | 5 |
| aleatorias, 6–8 variables (semilla 1001, 20 fórmulas) | 1.318 | 84.801 | **0** | 3.859.201 | 3.859.201 | **0** | 6 |
| aleatorias, 7–9 variables (semilla 7777, 20 fórmulas) | 1.703 | 165.229 | **0** | 9.237.902 | 9.237.902 | **0** | 12 |
| **total** | **3.804** | **340.336** | **0** | **19.184.639** | **19.184.639** | **0** | |

**El mayor punto fijo de las condiciones de `Sup` coincide entrada a entrada con la tabla que deja la
cascada.** Es decir, `Sup` describe con exactitud lo que hace tu review tras una fijación, y la
cascada es el cálculo de ese punto fijo.

Una variante que exige además un portador común (`helly gfp`) tampoco pierde nodos, pero se deja
fuera algunos pares de los pasos extremos que la cascada conserva (32 en K4 par, 339 en las
aleatorias). Por eso el enunciado final no exige portador: en el paso fijado, la condición de pares ya
obliga a que el owner común sea un portador.

## 3. Lo formalizado (`SliceSupport.lean`)

- **`Slice g mid`**: owners globales cuyo nodo tiene un owner con identificador `mid`.
- **`Supported g mid`**: existe `R` con `Sup g (Slice g mid) R`.
- **`slice_pinned`**: la rebanada es compatible con la fijación. Por `OOS`, un miembro en el paso
  fijado es su propio owner allí, así que lleva `mid`.
- **`pinExact_of_supported`** (**demostrado**): `Supported g mid` implica `PinExact g mid`.
- **`smp_readFrom`**: todo estado que visita el lector conserva `SMP`. Para eso `MInv` lleva ahora el
  campo `smp`: el crecimiento lo conservaba (`SMP_addNode`, `SMP_join`, `SMP_initSeed`) y la revisión
  agresiva también (`SMP_filterAllAgg`, que sale gratis de `AOk` con el conjunto vacío).
- **`sat_of_supported_boundary`** (**demostrado**): **si en los estados del lector toda rebanada
  tiene soporte y se cumple la simetría en los pasos extremos, el veredicto SAT de *Improves* es
  correcto.**

## 4. La cadena, tal como queda

```
estado final de pureRunW                           MInv (ahora con SMP)         demostrado
  todo estado del lector es resultado de reviewAgg AggOk, simetría interior     demostrado (v118)
  simetría en los pasos 0 y cs−1                   BoundarySym                  medida, abierta
  la rebanada de cada fijación tiene soporte       Supported                    medida, abierta
    ⇒ la rebanada sobrevive a la cascada           PinExact                     demostrado (v119)
    ⇒ toda fijación es válida ⇒ PickSomeAgg                                     demostrado
    ⇒ el lector acaba en un camino ⇒ modelo de φ                                demostrado (v116)
```

Lo que cambia respecto a v118: la obligación ya no menciona la cascada. `Supported` es una propiedad
estática del estado antes de fijar: existe un testigo `R` con cinco condiciones locales.

## 5. Lo que queda

1. **`Supported`: que el mayor punto fijo cubra la rebanada.** Es el contenido real que queda, porque
   el punto fijo *es* la cascada. Lo que da la estructura: `AggOk` y la simetría ya dan la cobertura
   de la primera ronda (el owner común de `x` y del nodo fijado está en la rebanada). Falta entender
   por qué las rondas siguientes, que borran pares, nunca vacían un paso de un nodo. Las rondas son
   pocas (de 3 a 12), y eso merece una sonda: qué pares caen en cada ronda y por qué condición.
2. **El recíproco** (`PinExact` ⇒ `Supported`, con `R` igual a la tabla final): la medida lo respalda.
   Demostrarlo requiere lemas de punto fijo del review base para padres e hijos, análogos a
   `aggOk_of_noProgress`. Haría de `Supported` una caracterización exacta de `PinExact`.
3. **`BoundarySym`**, sin cambios desde v118.
