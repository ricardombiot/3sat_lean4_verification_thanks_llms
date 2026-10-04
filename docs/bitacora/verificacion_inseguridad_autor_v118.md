# Verificación para el Autor v118: lo que garantiza tu review agresivo cuando para

Ricardo, soy Claude (Opus 5). v117 dejó la validez del veredicto de *Improves* reducida a dos cosas en
los estados que visita el lector: que las tablas de owners sean **simétricas** y `PinExact` (una
fijación no elimina nodos de su rebanada). Este tramo demuestra la mayor parte de la simetría, a
partir de la regla de parada de tu review, y amplía las medidas de `PinExact`.

Todo en la rama `spaik`, en el build de `AbsSat` (166 jobs), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. La regla de parada, convertida en propiedad (`AggFixpoint.lean`)

`reviewAgg` se detiene cuando el barrido ya no baja la medida. Lo demostrado:

- **Cada paso del barrido o no cambia nada o baja estrictamente la medida** (`aggPair_eqOrLt`,
  `aggNode_eqOrLt`). Un par que falla tu test, siendo `w` owner de `x`, siempre se borra, y borrarlo
  baja la medida (`measure_aggPair_lt`).
- **`aggOk_of_noProgress`**: si el barrido no baja la medida de un estado válido, **todo par de owners
  en los pasos que recorre** (`1 … current_step − 2`), con los dos nodos válidos, supera tu test: en
  cada paso donde `w` tiene owners, `x` tiene uno que `w` también tiene.
- **`aggOk_reviewAgg`**: por tanto, **todo resultado válido de `reviewAgg` cumple esa propiedad**
  (`AggOk`). Es `AggConsistent`, la formulación de tu observación en v116, ya demostrada en los pasos
  interiores.
- **`ownSym_of_aggOk`**: y **las tablas de owners son simétricas en esos pasos**. Las owners de un
  nodo en su propio paso son solo él mismo, así que tu test en el paso de `x` obliga a que `x` esté en
  la tabla de `w`.

La simetría la da tu barrido y no el review base, que por sí solo no la conserva: cuando falta una
dirección, tu test lo detecta y borra la relación en los dos sentidos.

**Un ajuste técnico en `aggPair`**: la condición incluye ahora `nx.owners.contains w`. En la máquina
no cambia nada, porque el barrido solo llama a `aggPair` con owners actuales de `x`, pero hace
explícito que un par que se dispara siempre borra algo. Los `#guard` de veredicto siguen pasando.

## 2. Solo quedan los pasos extremos (`PinExactBoundary.lean`)

- **`BoundarySym`**: simetría para los pares con un extremo en el paso `0` o en el último paso.
- **`ownSymmetric_of_boundary`**: `AggOk` más `BoundarySym` dan la simetría completa.
- **`readFrom_form`**: todo estado que visita el lector es un resultado del review agresivo, así que
  `AggOk` se aplica a todos.
- **`sat_of_pinExact_boundary`**: **si en los estados del lector se cumplen `PinExact` y la simetría
  en los pasos extremos, el veredicto SAT de *Improves* es correcto.**

Los pasos `0` y `current_step − 1` quedan fuera porque tu barrido (`cs−2 … 1`) no los recorre. Hay
dos caminos para cerrarlos:

- demostrar la simetría en esos pasos por otra vía (propiedades del nodo raíz y del último nodo
  añadido);
- o ampliar el barrido a todos los pasos. Sigue siendo sólido por la misma prueba de conservación, y
  en lo medido no cambiaría nada porque no hay asimetrías. Pero sería un cambio a tu filtro, y esa
  decisión es tuya.

## 3. `PinExact`, medida ampliada

`helly pins`: toda fijación en todo paso con elección, en los estados finales de *Improves*.

| familia | estados | fijaciones | inválidas | nodos de la rebanada | eliminados de la rebanada | conservados fuera |
|---|---|---|---|---|---|---|
| aleatorias, 6–8 variables (semillas 1001, 7777; 40 fórmulas) | 37 | 2.776 | **0** | 180.516 | **0** | **0** |
| Tseitin K3,3 par | 1 | 132 | **0** | 15.852 | **0** | **0** |
| Tseitin prisma par | 1 | 132 | **0** | 15.108 | **0** | **0** |
| Tseitin cubo par | 1 | 176 | **0** | 31.904 | **0** | **0** |
| (v117) Tseitin K4 par, K4 impar y `par_k3` | 162 | 2.638 | **0** | 60.414 | **0** | **0** |

En total, 5.854 fijaciones y 303.794 nodos de rebanada: **ni una excepción**. Los huecos de tríos
dentro de la rebanada siguen apareciendo por cientos de miles (1,26 millones en el cubo) sin que caiga
un solo nodo.

Pendientes de volcar: `helly pins all` sobre `top_phantom`, Tseitin K4 par, `par_k5` y K4 menos una
arista, y los gadgets `p2` de `readagg`.

## 4. La cadena, tal como queda

```
estado final de pureRunW                           MInv                         demostrado
  todo estado del lector es un resultado de        AggOk                        demostrado (v118)
  reviewAgg
    ⇒ simetría de owners en pasos interiores                                    demostrado (v118)
  simetría en los pasos 0 y cs−1                   BoundarySym                  medida, abierta
  la fijación no elimina nodos de su rebanada      PinExact                     medida, abierta
  lo que sobrevive a la fijación está en la                                     demostrado (v117)
  rebanada
    ⇒ toda fijación es válida ⇒ PickSomeAgg                                     demostrado
    ⇒ el lector acaba en un camino ⇒ modelo de φ                                demostrado (v116)
```

## 5. Lo que queda

1. **`PinExact`**, la mitad "la rebanada no pierde nodos". Con `AggOk` y la simetría ya demostradas,
   la cobertura inicial está: para `x` en la rebanada y un paso `j`, el owner común de `x` y del nodo
   fijado está en la rebanada. El núcleo técnico es seguir la cascada: demostrar que el conjunto
   rebanada es estable para cada operación del review y del barrido, igual que `ChainSound` lo es
   para una cadena, pero para un conjunto de nodos.
2. **`BoundarySym`**: por la vía de las propiedades del nodo raíz y del último, o ampliando el
   barrido si lo decides.
