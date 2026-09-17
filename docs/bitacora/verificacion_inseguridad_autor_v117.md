# Verificación para el Autor v117: una fijación elimina exactamente su rebanada

Ricardo, soy Claude (Opus 5). En v116 la validez del veredicto de *Improves* quedó reducida a una
obligación: en cada estado que visita tu lector, **alguna** fijación deja el grafo válido
(`PickSomeAgg`). Este tramo mide qué hace **de verdad** una fijación en esos estados, encuentra una
regularidad muy limpia y empieza a formalizarla.

Todo en la rama `spaik`, en el build de `AbsSat` (164 jobs), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. De dónde partimos: Helly estático no funciona

Mi primera idea era un argumento estático: tomar como testigo los nodos compatibles con el nodo
fijado y demostrar que no pierden la cobertura. Para eso hacía falta que las tablas de owners
cumplieran Helly-3: si tres nodos son compatibles dos a dos, tienen un owner común en cada paso.

La sonda `helly` (nuevo ejecutable, `Probes/Helly.lean`) lo mide en los estados finales de *Improves*
tras el review agresivo:

| estado | pares co-owned | violaciones de pares | tríos | huecos de Helly-3 |
|---|---|---|---|---|
| Tseitin K4 par, final | 2.932 | **0** | 34.168 | **27.800** |
| K4 menos una arista, 3 colores, final | 17.779 | **0** | 424.016 | **204.632** |
| Tseitin K4 impar, todas las líneas | 33.468 | **0** | 228.449 | 0 |

- **Violaciones de pares = 0**: tu `AggConsistent` se cumple en todo lo medido. Dos nodos
  compatibles tienen siempre un owner común en cada paso.
- **Huecos de Helly-3 abundantes**: el argumento estático es falso.

Tu anotación lo anticipaba: no hace falta que todo lo compatible sea compatible con el nodo fijado,
porque el lector, al fijar y limpiar, se asegura de que quede al menos un camino. Así que hay que
mirar lo que hace la limpieza, no una propiedad estática.

## 2. Lo que hace la fijación: exactamente su rebanada

`helly pins`: en cada estado se prueba **toda** fijación, por identificador del mapa y en **todo**
paso con elección, seguida del review agresivo. Llamo **rebanada** de un identificador `mid` a los
nodos que tienen algún owner con ese identificador.

| estados | fijaciones | inválidas | nodos de la rebanada | eliminados de la rebanada | conservados fuera | entradas de owners | asimétricas |
|---|---|---|---|---|---|---|---|
| Tseitin K4 par, final | 88 | **0** | 5.312 | **0** | **0** | 5.980 | **0** |
| Tseitin K4 impar, todas las líneas (97) | 1.800 | **0** | 41.416 | **0** | **0** | 69.830 | **0** |
| gadget `par_k3`, todas las líneas (64) | 750 | **0** | 13.686 | **0** | **0** | 25.056 | **0** |

Tres regularidades, sin una sola excepción:

1. **Toda fijación es válida**, no solo alguna.
2. **La cascada elimina exactamente lo que queda fuera de la rebanada**: ni se lleva un nodo de la
   rebanada ni deja uno de fuera.
3. **Las tablas de owners son simétricas**: si `q` es owner de `n`, `n` es owner de `q`.

La rebanada sigue teniendo huecos de tríos (87.936 en Tseitin K4 par) y aun así no pierde ningún
nodo. El motivo: el barrido agresivo borra **relaciones de owner entre pares**, no nodos. Un nodo solo
cae si se queda sin cobertura en algún paso, y eso no pasa.

Pendientes de volcar: aleatorias de 6–8 variables, Tseitin K3,3, prisma y cubo, y el modo de todas
las líneas sobre `top_phantom`, Tseitin K4 par, `par_k5` y K4 menos una arista. También los gadgets
`p2` de la sonda `readagg` de v116.

## 3. Lo formalizado (`PinExact.lean`)

- **`InSlice n mid`**: `n` tiene un owner con identificador `mid`.
- **`PinExact g mid`**: todo nodo de la rebanada sigue siendo owner global tras la fijación.
  **Es la conjetura que la medida respalda; no está demostrada.**
- **`pruned_filterAll_filterAllAgg`**: el review agresivo empieza por el review base, así que su
  resultado es un recorte del de `filterAll`. Con esto, todo lo demostrado sobre fijaciones del
  review base se aplica también aquí.
- **`inSlice_of_survives`** (**demostrado**): **lo que sobrevive a una fijación válida está en la
  rebanada**. Es la mitad "elimina todo lo de fuera".
- **`isValid_pin_of_pinExact`** (**demostrado**): con owners simétricos, `PinExact` hace válida la
  fijación. El nodo fijado es válido, así que tiene un owner en cada paso; por simetría, ese owner lo
  tiene a él y está en la rebanada; por `PinExact` sigue vivo, y ningún paso se vacía.
- **`pickSomeAgg_of_pinExact`** (**demostrado**): `PinExact` en los pasos con elección da
  `PickSomeAgg`.
- **`sat_of_pinExact`** (**demostrado**): con la reducción de v116, **si en los estados que visita el
  lector se cumplen `PinExact` y la simetría de owners, el veredicto SAT de *Improves* es correcto.**

## 4. La cadena completa, tal como queda

```
estado final de pureRunW (MInv: demostrado)
  + un review agresivo lo deja válido
  + en cada estado del lector: simetría de owners        ← medida, sin demostrar
                               PinExact                  ← medida, mitad demostrada
  ⇒ PickSomeAgg                                          (demostrado)
  ⇒ el lector termina en un camino                       (demostrado, v116)
  ⇒ el camino es un modelo de φ                          (demostrado, v116)
```

Y en la otra dirección, v115: si φ es satisfacible, la máquina lo detecta (demostrado).

## 5. Lo que queda

1. **Simetría de owners en los estados del lector.** El review base no la conserva en general (por
   eso existen las variantes `SymReview`), pero en los puntos fijos del review agresivo no aparece
   ninguna asimetría. Hay que ver qué parte del bucle la restaura: probablemente tu barrido, que borra
   las relaciones **en los dos sentidos**.
2. **La mitad abierta de `PinExact`: la rebanada no pierde nodos.** El argumento que propongo, por
   punto fijo:
   - cobertura: para `x` en la rebanada y un paso `j`, `AggConsistent` sobre el par (`x`, `p'`) da un
     owner común `r`, y por simetría `r` está en la rebanada;
   - el núcleo técnico: el barrido puede quitar la relación (`x`, `r`), y hay que demostrar que
     siempre queda otro `r` en la rebanada. Eso exige describir la cascada como el mayor conjunto
     estable que contiene a la rebanada.
3. **`AggConsistent` en el resultado de `reviewAgg`**: cuando el bucle termina, el barrido ya no
   elimina nada. Ojo: el barrido solo recorre los pasos `1 … current_step − 2`, así que los pasos
   extremos requieren un argumento aparte o un ajuste del enunciado.
4. **Medidas**: volcar las ejecuciones en curso y ampliar `helly pins` a Petersen par y a fórmulas
   aleatorias mayores.
