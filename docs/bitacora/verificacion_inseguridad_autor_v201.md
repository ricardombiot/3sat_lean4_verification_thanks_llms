# Verificación para el Autor v201: todo lo vivo está en una camarilla, el veredicto del lector bajo tres hipótesis medidas, y una propuesta de cambio en el review

Ricardo, este informe cuenta lo que se hizo desde el v200 en `lean/improves_bingo` y `julia/improves_bingo`.
Empezó buscando reglas para `NoDeadEnd` y acabó en tu frase: **el review de cada paso limpia los nodos incoherentes
y deja únicamente las camarillas válidas.** Esa frase es ahora un invariante con nombre (`KernelExact`), y la cadena
entera hasta el veredicto del lector está demostrada en Lean bajo tres hipótesis, las tres medidas sin fallos. La
§5 propone un cambio pequeño en el review, en Lean y en Julia a la vez, que convierte una de las tres en teorema.

**La conclusión, por adelantado.**
* **Hay un teorema de veredicto con tres hipótesis con nombre.** `readerVerdict_iff_of_hyps`
  (`ReaderFinal.lean`, sin `sorry`, solo los axiomas estándar): el lector dice SAT exactamente cuando la fórmula es
  satisfacible, bajo
  * `closed`: los estados del lector están cerrados por las reglas;
  * `union`: en cada join, el núcleo de la unión es la unión de los núcleos;
  * `skip`: el UP que salta una ventana prohibida conserva el invariante.
* **Las tres están medidas sin fallos** con el mapa bin (el del modelo Lean), en las 88 instancias del corpus (§3).
* **El invariante es `KernelExact`**: el núcleo de cualquier pin está hecho de camarillas. Lo conservan la selección
  (por la confluencia del núcleo, sin hipótesis), el UP sin ventana saltada, y el join bajo `union`.
* **La propuesta de §5** hace que el review solo salga cuando una vuelta completa con todas las reglas no cambia
  nada. Medida en Julia: **no cambia ningún veredicto, ninguna solución ni ningún estado** en 176 ejecuciones
  (88 instancias × 2 mapas), y cuesta entre un 2 % y un 5 % de tiempo. Con ella, `closed` pasa a ser teorema.
* **Lo que queda de fondo** es `union` (y `skip`, que parece de la misma naturaleza que `closed`).

---

## 1. El recorrido

| paso | commit | qué |
|---|---|---|
| reglas 2 y 3 del v199 | `66c1970` | la regla de tríos (versión sólida) y `SecPair` como reglas del review **no cortan nada**; la regla de tríos de §4.4 de la escalera perdía soluciones (corregido) |
| `SecPair` | `4a5e549`, `cc475c1` | enunciado en Lean, espejo en Julia; la camarilla de una solución es una sección |
| la sección es el pin | `3b74bfa` | 17 158 / 17 158: la sección de `b` es exactamente lo que deja el pin de `b` |
| `PinEqSec`, `PairClosed` | `0e93257`, `aacffe3`, `79540f1` | mitad fácil demostrada; `review_exits_clean`: el combustible del review basta |
| `SecStruct` | `0dca35e`, `ba5c226` | el review conserva toda estructura cerrada por parejas, enlaces y apoyo |
| inducción por el lector | `f7236ca`, `c914f1f` | el paso local (`SecMeet`) es **falso**: al fijar, cambia la sección que cubre cada arista |
| pins cualesquiera | `dac7c2d`, `0637201` | `SecPair` vale en todo estado fijado y en cada paso de la máquina |
| la selección rompe, el review restaura | `c133244` | tu intuición, medida: `SecPair` falla en el 66 % tras la selección y en 0 tras el review; el UP y el join la conservan solos |
| `EdgeClique` | `9f91703`, `d55cbaf`, `623fba3`, `c264b14` | todo lo vivo está en una camarilla; da `NoDeadEnd` directamente; el join y el UP lo conservan |
| mapa bin | `2707c45` | con el mapa bin, el UP con ventana saltada rompe `EdgeClique` y su review lo restaura |
| el núcleo | `2f8249b`, `b4db3e7` | el review como núcleo, confluencia de los pins, `KernelExact` |
| la cadena | `3c79ec6`, `7f678da`, `82166a5`, `a8b25a1` | contabilidad, el UP, el join, y `readerVerdict_iff_of_hyps` |

`lean/improves_bingo` tiene ahora 6 882 líneas en `Model/`, sin `sorry`.

### Una advertencia sobre el mapa

Las sondas en Julia corrieron primero con el **mapa clásico** (`GraphMap.load_import!`), y el modelo Lean usa el
**mapa bin** (con ventanas prohibidas). Las medidas que respaldan las tres hipótesis y la propuesta se repitieron con
el mapa bin (`PROBE_MAP=bin`). La diferencia importa en un punto: con el mapa bin, la fila nueva puede saltar una
ventana, y entonces el UP necesita su review (es la hipótesis `skip`).

## 2. La idea: el review como núcleo

Tres piezas, todas demostradas:

* **Estructuras cerradas** (`SecStruct g V R`). Un conjunto de nodos `V` y una relación `R`, cerrados por las reglas
  del review:
  * **parejas**: cada pareja tiene, en cada paso, un testigo relacionado con las dos;
  * **enlaces**: cada nodo tiene padre e hijo enlazados dentro;
  * **apoyo**: en cada pareja `(x, w)`, un padre de `x` relacionado con `x` lo está con `w`, y lo mismo con los
    hijos.

  `secStruct_review`: el review las conserva todas. Una camarilla llevada es el caso de un solo camino.
* **El núcleo** (`Kernel.lean`). Si el estado que deja un pin está cerrado (`ClosedState`), sus aristas son
  exactamente las parejas de las estructuras cerradas del estado original que concuerdan con el pin
  (`pinEdge_iff_kernel`). De ahí sale la **confluencia**: fijar `b₁` y luego `b₂` es fijar los dos a la vez
  (`pin_confluent`, `kernel_pin_list_iff`).
* **`KernelExact g`**: toda pareja del núcleo de `g` fijado en cualquier `P` está en una camarilla de `g` que pasa
  por `P`. Es tu frase en forma operativa.
  * La selección lo conserva **sin hipótesis**: fijar `B` y luego `P` es fijar `B ++ P` (`kernelExact_filterAll`).
  * Junto con el cierre, da `EdgeClique` (todo lo vivo en una camarilla), de ahí `NoZombie` y el veredicto.

Por operación de la máquina:

| operación | `KernelExact` | dónde |
|---|---|---|
| selección (filtro por requisitos con su review) | demostrado, sin hipótesis | `kernelExact_filterAll` |
| UP sin ventana saltada | demostrado | `kernelExact_addNode` (`KernelUp.lean`) |
| UP con ventana saltada | hipótesis `skip` | medida |
| join | demostrado bajo `union` | `kernelExact_doJoin` (`KernelJoin.lean`) |
| lector | hereda de la selección; con `closed`, `EdgeClique` | `ReaderFinal.lean` |

La contabilidad (las posesiones unen vivos, un documento por id, los enlaces van al paso de al lado, todo por debajo
de la cima) está demostrada a lo largo de la máquina con un combinador genérico (`RevPrims`, `Bookkeeping.lean`).

## 3. Las tres hipótesis, medidas

Todas con el mapa bin, en las 88 instancias (sin `tseitin_petersen_H`; `simple_v3_c2` falla en la máquina también
sin cambios).

| hipótesis | qué dice | sonda | medida |
|---|---|---|---|
| `closed` | los estados del lector están cerrados por las reglas | `probe_secinpin.jl` y otras | las pasadas de padres e hijos **nunca cortan nada** |
| `union` | el núcleo de la unión es la unión de los núcleos | `probe_kernelunion.jl` | 7 311 joins, 29 244 comparaciones, **0 diferencias** en los dos sentidos |
| `skip` | el UP con ventana saltada conserva `KernelExact` | `probe_kernelexact_up.jl` | 18 704 estados, 33 894 pins al azar, **0 fallos** |

Además, la confluencia se midió directamente (`probe_pinexact.jl`): 30 309 comparaciones, 0 diferencias. Y
`KernelExact` sobre la línea (23 297 estados fijados): 0 fallos.

## 4. Lo que no funcionó

* **La regla de tríos de §4.4 de la escalera pierde soluciones.** El trío sin entrada común solo dice que ninguna
  solución pasa por los **tres**, y eso no permite cortar ninguna de sus aristas. La forma sólida (cuantificar `x`
  por paso) no corta nada. Corregido en la escalera.
* **La inducción a lo largo del lector no es local.** Al fijar `b`, la sección que cubre una arista cambia a otro
  nodo del mapa: `SecMeet` falla en 21 044 casos, y sus variantes (`SecMeetAlive`, «toda ancla cubre») también. Por
  eso la inducción pasó a la máquina, y al núcleo.

## 5. Propuesta de cambio: la comprobación final del review

### El problema

`closed` pide tres cierres del estado que deja el review. Dos salen del mecanismo: parejas y enlaces, porque la
última vuelta no cambió nada. El tercero, el **apoyo**, no:

* las pasadas de padres y de hijos solo corren con `dirty` (Julia: `review_owners`), en Lean y en Julia por igual;
* la pasada de hijos va de abajo arriba y puede cortar una arista en un paso bajo, dejando sin apoyo por padres a un
  nodo de un paso superior;
* si la vuelta siguiente no cambia nada en la purga, las parejas ni los enlaces, `dirty` sigue apagado, la pasada de
  padres no se repite y el review sale.

Que eso no ocurra es un hecho medido, no una garantía.

### El cambio

**Al salir, una vuelta forzada de las pasadas de padres e hijos** (y de la poda de enlaces). Si cambian algo, el
review sigue; si no, sale. Así el review solo sale cuando una vuelta completa con todas las reglas no cambia nada, y
los tres cierres quedan garantizados.

* Julia: `GraphPath.FINAL_CHECK` (`src/graph_path/graph_path_filter.jl`, `final_coherence_check!`), **apagado por
  defecto** hasta que decidas.
* Lean: el mismo cambio en `review` (una vuelta final sin la condición de `dirty` para las dos pasadas). Con él,
  `closed` se demuestra con el argumento de salida limpia que ya tienen `review_exits_clean` y
  `pairClosed_review'`, y sale de `Hyps`.

### Medida (`julia/improves_bingo/test_3sat/probe_final_check.jl`)

Cada instancia con `FINAL_CHECK` apagado y encendido, con los dos mapas, máquina y lector completos:

| | mapa clásico | mapa bin |
|---|---|---|
| instancias | 88 | 88 |
| veredictos distintos | 0 | 0 |
| veredictos contra el exhaustivo | 0 errores | 0 errores |
| soluciones del lector distintas | 0 | 0 |
| soluciones del lector = exhaustivo (y comprobador de cláusulas) | 88 / 88 | 88 / 88 |
| estados finales distintos (vivos, aristas, nodos, enlaces) | 0 | 0 |
| vueltas de review | 26 310 → 26 310 | 30 922 → 30 922 |
| comprobaciones finales / que cambiaron algo | 12 837 / **0** | 15 461 / **0** |
| tiempo (máquina + lector) | 38,6 s → 39,5 s (+2,3 %) | 251,1 s → 264,1 s (+5,2 %) |

**No se pierde ninguna solución**: con la comprobación final, las soluciones del lector son exactamente las del
exhaustivo en todas las instancias, y la máquina queda idéntica estado a estado. En el corpus el cambio no hace nada
salvo comprobar; su valor es que lo que era un hecho medido pasa a ser una garantía demostrable.

**Recomendación:** adoptarlo en los dos lados (encender `FINAL_CHECK` por defecto en Julia y cambiar `review` en
Lean), y demostrar `closed`.

## 6. El plan

1. **Si adoptas §5:** el cambio en Lean y Julia, y `closed` como teorema. Quedarían `union` y `skip`.
2. **`skip`**: el UP con ventana saltada es «restringir y revisar», como la selección. Con el núcleo, debería
   reducirse a la confluencia: la ventana saltada restringe la cima a los nodos con hijo.
3. **`union`**, el lema de fondo. En cada join, cada lado trae, en el paso anterior a la cima, nodos de un nodo del
   mapa que el otro lado no tiene, y esos nodos nunca se poseen entre lados. Una estructura cerrada de la unión solo
   puede mezclar los lados a través de nodos compartidos de pasos más bajos; ahí es donde hay que mirar.
4. La tabla de sincronía Julia ↔ Lean está en `docs/plans/lean_bingo.md`.
