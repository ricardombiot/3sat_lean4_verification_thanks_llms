# Verificación para el Autor v63: la barrida queda demostrada, y la simetría resulta ser cosa de los extremos

Ricardo, soy Claude (Opus 5). v62 dejó la localización de la simetría en tres cuartos de teorema y un argumento. Este informe cierra ese cuarto — y, al medir su alcance, encuentra algo que cambia cómo hay que leer todo el asunto.

Dos resultados, uno demostrado y otro medido. El medido es el que importa.

---

## 1. `cleanInvalid` no puede romper la simetría — ahora es teorema

El tercer punto de v62 era un argumento. Ya no.

La barrida hace tres cosas por nodo: intersecar su tabla de owners con los owners **globales**, desenlazar lo que eso deje incompatible, y tirar el nodo si sale inválido. Las dos últimas dejan la tabla de todo superviviente **intacta**, así que transportan la simetría gratis. Solo la intersección quita algo de una tabla — y quita únicamente ids que **no son owners globales**.

De modo que toda la cuestión es si un id que las tablas pierden puede seguir siendo un nodo. Si todo nodo es owner global, no puede:

```lean
theorem OwnSymmetric_cleanInvalid (g : GPathM)
    (hng : Ownership.NodesAreGowners g)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (cleanInvalid g)
```

Cierre `[propext, Quot.sound]`, cero axiomas de proyecto, cero `sorry`. Por el camino quedan también demostrados `NG_cleanInvalid` (la barrida conserva `NodesAreGowners`), las tres inversiones de `node?` para `updateAt` / `unlinkIncompatible` / `removeNode`, y `OwnSymmetric_of_ownersEq`, el lema que dice que cualquier estrechamiento que no toque las tablas transporta la simetría.

**La hipótesis es honesta y está nombrada**: `Ownership.NodesAreGowners`, medida en 0 violaciones sobre 259.187 nodos, y rota por exactamente una operación — `filterRequire`, que es el pinchazo del propio lector. Lo que el teorema no cubre es la recuperación: que la barrida, recibiendo el estado roto que deja un pinchazo, elimine todos los nodos que el pinchazo degradó. Demostré la mitad provable de ese argumento:

```lean
theorem not_gowner_invalid (g g' : GPathM) (hoos : SelfOwn.OOS g) …
    (hout : id ∉ g.gowners)
    (hstep : hasStepEntry g.gowners id.id.step = true) … :
    isValidNode g' (relink (intersectOwners d.owners g.gowners) d) = false
```

Un nodo que ya no es owner global pierde la auto-posesión al intersecar, se queda sin ningún owner en su propio paso, falla `owners_ok` y la barrida lo tira. Lo que falta es el *cuándo*: la barrida solo llega a ese nodo en su turno, y los owners globales encogen mientras tanto, así que `hstep` no lo arrastra nadie. Eso es contabilidad, y la dejo dicha como tal.

## 2. Así que medí la recuperación en vez de suponerla

Modo nuevo, `lake exe extend --gowscope`. Sobre cada estado final válido: pinchar como pincharía el lector, y mirar `NodesAreGowners` y la simetría en cada etapa.

Cinco semillas, 4..6 variables, 76 estados finales válidos, 5.864 nodos, 64 pinchazos:

| etapa | nodos que no son owner global | **violaciones de simetría** |
|---|---|---|
| estado final, antes del pinchazo | **0** | 0 (v62: 0 en 11.009) |
| justo después de `filterRequire` | **64** (uno por pinchazo) | — |
| después de `cleanInvalid` | **0** | **0** |
| después de `+ reviewParents` | — | **236** |
| después del punto fijo del review | **0** | **51** |
| **al final de la lectura completa** | — | **0** |

Léelo de arriba abajo, porque cuenta una historia entera.

## 3. Lo que dice esa tabla

**La recuperación ocurre, y ocurre exactamente donde el argumento decía.** El pinchazo degrada 64 nodos; `cleanInvalid` se lleva **los 64**, y deja la simetría en **0**. El hueco entre mi teorema y la barrida tal y como el lector la ejecuta es un argumento de conteo que los números dicen que es cierto.

**La coherencia sí la rompe, y ahora se le ha visto hacerlo.** `reviewParents`, una sola pasada, introduce **236** violaciones donde no había ninguna. Es el cuarto punto de v62, la única operación sin contrapartida simétrica, pillada en el acto.

**El review no siempre la repara.** Al punto fijo quedan 51 (0, 0, 6, 45, 0 por semilla). No es ruido: en dos semillas de cinco el estado que el lector se lleva al siguiente paso es asimétrico.

**Y al final de la lectura vuelve a ser 0.** Las 64 lecturas completas terminan con simetría perfecta.

## 4. Lo que eso cambia

La simetría **no se pierde y se recupera por casualidad: está en los dos extremos y no en el medio.**

- Vale en el estado de longitud completa que la máquina le entrega al lector.
- Vale en el estado final de la lectura, cuando ya no queda nada que elegir.
- **No vale entre uno y otro.**

Es exactamente la forma que v60 encontró para la exactitud: una propiedad de los estados sin elección pendiente, no un invariante que la máquina arrastre entre ellos. Dos propiedades distintas, el mismo diagnóstico — y creo que eso ya no es coincidencia, sino la estructura del problema.

**Consecuencia práctica para la ruta de v61.** `chain_through_of_symmetric` —todo nodo está en un camino completo que posee entero— sigue disponible donde lo puse, sobre el estado que la máquina entrega. Pero **no se puede arrastrar a lo largo de una lectura**: en el paso siguiente la hipótesis puede ser falsa. Si el plan era inducir sobre los pasos de lectura usando simetría en cada uno, ese plan no funciona tal cual. Lo digo ahora y no cuando hubiera costado tres informes descubrirlo.

## 5. Lo que queda en firme

- `OwnSymmetric_cleanInvalid`, `NG_cleanInvalid`, `not_gowner_invalid`, más las inversiones y `OwnSymmetric_of_ownersEq` — demostrados, `[propext, Quot.sound]`.
- Con v62: **tres de las cuatro operaciones no pueden romper la simetría** (dos sin hipótesis, una con `NodesAreGowners`), y la cuarta se ha medido rompiéndola.
- La localización de v62 ya no es tres cuartos de teorema y un argumento: es teorema, con una hipótesis nombrada y su alcance medido.
- Modo `--gowscope` nuevo, cinco semillas.

## 6. Lo que sigue abierto

- **La simetría en longitud completa**, sin hipótesis, sigue sin demostrar. Pero ahora sabe uno qué forma tiene: es un enunciado sobre estados sin elección pendiente.
- **La recuperación** (`cleanInvalid` elimina todo nodo degradado antes de acabar la barrida): medida en 64/64, no demostrada.
- **El muro**: la exactitud del estado final — todo owner global superviviente lo usa alguna solución superviviente. ⊇ es la ley de conservación, demostrada; ⊆ sigue abierto.
- **Complejidad**: cero teoremas, como siempre.

Build: `lake build AbsSat` verde, 87 módulos, 0 `sorry`, 0 axiomas de proyecto.
