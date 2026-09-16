# Verificación para el Autor v115: tu filtro de consistencia agresiva, dentro del review de *Improves*

Ricardo, soy Claude (Opus 5). Encontraste en Julia que `agressive_consistence_filter!` resuelve el
contraejemplo de Petersen (v114). Este tramo lo integra en el review de la máquina *Improves*, con la
prueba de que no pierde soluciones, y mide el resultado con la máquina real.

Todo en la rama `spaik`, en el build de `AbsSat` y sus ejecutables (284 jobs), sin `sorry`, en
`[propext, Quot.sound]`.

---

## 1. Qué hace tu filtro

`graph_path_filter.jl`, `agressive_consistence_filter!`:

- recorre los pasos de `current_step − 2` a `1` y, en cada uno, sus nodos `x`;
- para cada owner válido `w` de `x` en esos mismos pasos, interseca las owners de ambos;
- si en algún paso `w` tiene owners y ninguna es owner de `x`, **no hay camino que contenga a los
  dos**: `w` deja de ser owner de `x` y `x` deja de serlo de `w`;
- al terminar con `x`, lo elimina si ha quedado inválido;
- los cambios se ven al instante en las comprobaciones siguientes.

Es consistencia de caminos sobre las tablas de owners: un par solo sobrevive si en cada paso hay un
tercer nodo compatible con los dos. Por eso ve lo que el review base no ve. En Petersen el fallo era
un trío de pines compatibles dos a dos pero no los tres a la vez, y este filtro comprueba pares
**con un tercero en cada paso**.

## 2. Cómo queda integrado

`AbsSat/GraphPath/Model/AggressiveReview.lean`:

- **`aggSweep`**: traducción fiel del filtro sobre `GPathM`, con el mismo orden de recorrido, los
  mismos pasos y los cambios aplicados sobre la marcha. Como en Julia, borrar una relación de owner no
  toca padres ni hijos; los enlaces que quedan incoherentes los limpia la ronda siguiente del review.
- **`reviewAgg`**: el review base hasta su punto fijo, un barrido, y se repite mientras el barrido
  elimine algo. Es tu idea de meterlo dentro del bucle del review.
- **`filterAllAgg`**: pines y review agresivo.

La máquina *Improves* (`PureDriverImproves.upFilteringWeak`) usa ahora `filterAllAgg` en lugar del
review base. `SatMachinePure` no se toca: sigue siendo la referencia.

## 3. Lo demostrado

- **`pruned_reviewAgg`**: el review agresivo solo elimina.
- **`ChainSound_reviewAgg`**: **no pierde ninguna solución**. Dos nodos de una misma cadena comparten,
  en cada paso, el nodo de esa cadena, así que la intersección nunca queda vacía y el barrido nunca los
  separa. Y los nodos de una cadena siguen siendo válidos, así que nunca se eliminan.

Para que la máquina herede la ley de conservación sin reescribirla, el marco genérico de v109–v110 se
ha parametrizado por el review:

- **`ReviewOk R`**: los dos requisitos de un review (es un recorte y conserva cadenas), con instancias
  para el review base y para el agresivo;
- **`ConservationFilter`**: la ley de conservación, probada una sola vez para cualquier filtro previo
  y **cualquier review** con `ReviewOk`;
- **instancias**: *Improves* con el review agresivo, y la máquina de pines y SAC con el review base.

Resultado: **la máquina *Improves* con el review agresivo no pierde soluciones**
(`pureRunW_full_state`, `pureRunW_ne_nil`), demostrado como antes.

## 4. Lo medido con la máquina real

`lake exe improves-diff`, que ejecuta la máquina *Improves* y la compara con la máquina base, las
variantes y el oráculo de fuerza bruta.

| fórmula | base | *Improves* | oráculo | tiempo base → *Improves* |
|---|---|---|---|---|
| 20 aleatorias (6 variables, 24 cláusulas) | correctas | **correctas, misma línea final** | — | ×2,7 |
| Tseitin K4 | UNSAT | **UNSAT** | UNSAT | 97 ms → 288 ms |
| Tseitin K3,3 | UNSAT | **UNSAT** | UNSAT | 1,3 s → 5,3 s |
| Tseitin prisma | UNSAT | **UNSAT** | UNSAT | 1,0 s → 5,3 s |
| Tseitin cubo | UNSAT | **UNSAT** | UNSAT | 6,7 s → 41 s |
| **Tseitin Petersen** | **SAT (erróneo)** | **UNSAT (correcto)** | UNSAT | 32 s → 234 s |

Con la sonda (`lake exe join-borrow agg`), las dos renumeraciones de Petersen que también fallaban dan
UNSAT con el review agresivo (unos 220 s cada una, frente a unos 30 s).

**Cómo leer `improves-diff` en Petersen.** Marca `MISMATCH` porque su criterio es que todas las
variantes coincidan con la máquina base, y ahora *Improves* discrepa de ella. Pero la que se equivoca
es la base: *Improves* coincide con el oráculo.

**Una limitación de la herramienta.** Las cifras de carga de la columna de *Improves* (pasadas y
eliminaciones del review) las recalcula `ImprovesLoad` repitiendo el **review base**, así que no
describen el review agresivo. Los veredictos, las líneas finales y los tiempos sí son los de la máquina
real. Habría que actualizar `ImprovesLoad` para medir la carga del nuevo review.

## 5. El coste

Entre 3 y 7 veces más lento en lo medido, y el factor crece con el tamaño. Encaja con lo esperado: una
pasada del barrido revisa cada par nodo–owner y, para cada uno, todos los pasos, lo que la hace del
orden de S⁴ con la implementación directa sobre listas. Agrupando las owners de cada nodo por paso
bajaría a unos S³ sin cambiar el resultado.

## 6. Qué queda abierto

- **La otra mitad de la validez**: que un estado final válido contenga siempre una solución. La
  conservación ya está demostrada; esta no. Lo que cambia es que la máquina sobre la que hay que
  atacarla es ahora la de este review, y Petersen ya no es un contraejemplo.
- **Hasta dónde llega**: el filtro razona sobre tríos (un par y un tercero en cada paso). Tseitin sobre
  grafos con ciclos más largos puede esconder restricciones que involucren más variables a la vez.
  Medir el dodecaedro (cintura 5, 20 vértices) y el grafo de Heawood (cintura 6) dirá si aguanta.
- **La herramienta**: actualizar `ImprovesLoad` para medir la carga real del review agresivo.
