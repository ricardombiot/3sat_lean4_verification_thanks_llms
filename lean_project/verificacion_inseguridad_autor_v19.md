# Verificación para el Autor v19: A′ — una obligación en vez de dos, y la terminación sale gratis

Ricardo, soy Claude (Opus 5). Atacada la **A′**: la ruta A con propagación, que es la que sobrevivió a la medición de v18. Esta vez el resultado no es una refutación.

---

## 1. De dónde viene A′

v18 dejó dos cosas:

- `Extendable` (co-posesión por pares, sin propagar) es **falsa** — 1.574 cadenas parciales muertas.
- Con propagación (`filterAll` tras cada selección, que es lo que hace tu Reader) **no se atasca nada**.

Así que la inducción tiene que ir conducida por la propagación. Eso es A′:

> Elige un nodo de mapa que los owners globales aún permitan, en un paso donde todavía discrepan; propaga; aterriza en un grafo válido **estrictamente más pequeño**. Repite hasta que no quede nada que elegir. Si un grafo sin elección denota algo, el de partida también.

---

## 2. La sorpresa buena: la terminación no hay que suponerla

Cuando planteé el esqueleto pensaba que tendría que asumir dos cosas: que el paso mantiene la validez, y que la medida baja. La segunda **resultó ser demostrable**, y por una razón que estaba delante todo el rato:

```lean
def measure (g : GPathM) : Nat :=
  g.gowners.length + (g.nodes.map PNodeM.weight).sum
```

Tu medida **cuenta los `gowners`**. Y `filterRequire` tira exactamente los owners globales del paso que nombran otro nodo de mapa. Así que:

```lean
theorem measure_filterAll_lt (g : GPathM) (mid : NodeId) (r : PathNodeId)
    (hr : r ∈ g.gowners) (hstep : r.id.step = mid.step) (hne : r.id ≠ mid) :
    measure (filterAll g [mid]) < measure g
```

es un **teorema**, no una hipótesis. Un paso donde los owners todavía discrepan hace bajar la medida, sin más. La terminación del descenso es gratis.

Esto, por cierto, es mérito de tu diseño: si `measure` contase solo los nodos, esto no saldría.

---

## 3. El teorema (`Model/PickInduction.lean`)

```lean
theorem Inhabited_of_pickValid
    (P : GPathM → Prop)
    (hPf : ∀ g mid, P g → isValid g = true → P (filterAll g [mid]))
    (hnd : ∀ g, P g → NodupIds g)
    (hpick : ∀ g, P g → isValid g = true → PickValid g)
    (hbase : ∀ g, P g → isValid g = true → NoChoice g → Inhabited g)
    (g : GPathM) (hP : P g) (hv : isValid g = true) : Inhabited g
```

`Inhabited` — la mitad de L6 que consume el veredicto SAT/UNSAT — sale de **una obligación y un caso base**:

| | |
|---|---|
| `PickValid` | seleccionar un nodo de mapa permitido y propagar deja el grafo válido |
| `NoChoice → Inhabited` | un grafo cuyos owners globales coinciden en **un nodo de mapa por paso** denota algo |

`PickValid` es exactamente la forma de un paso de `ReadStable` — lo que tu Reader necesita, y lo que la corrección que me hiciste ya había señalado. El caso base es un enunciado de otro orden que L6: ahí **no queda nada que elegir a nivel de mapa**.

Y la vuelta atrás es gratis: filtrar solo poda, así que una cadena del grafo filtrado es una cadena del original (`denot_filterAll_subset`, la dirección de estrechamiento de L2, ya demostrada).

Compara con A:

| | obligaciones | estado |
|---|---|---|
| **A** | `ExtendUp` + `ExtendDown` | una de ellas **refutada** |
| **A′** | `PickValid` + caso base | ninguna refutada; terminación **demostrada** |

---

## 4. El probe mide las dos obligaciones a la vez

`lake exe extend --descend` **ejecuta el descenso de verdad**, el mismo que el teorema razona: mientras quede elección, coge el primer owner global de un paso donde discrepen, propaga, repite.

- Si un pick rompe la validez → violación de `PickValid`.
- Si el descenso termina → comprueba que el endpoint sin elección lleva una cadena **certificada con la ruta C** (`Certificate.isCert`, es decir un teorema, no "la búsqueda dijo que sí").

| familia | estados | descensos completados | violaciones de `PickValid` | endpoints con cadena verificada |
|---|---|---|---|---|
| transición de fase | 133 | 133 | **0** | **133 / 133** |
| cláusula tautológica | 37 | 37 | **0** | **37 / 37** |
| UNSAT forzado | 41 | 41 | **0** | **41 / 41** |
| literal repetido | 31 | 31 | **0** | **31 / 31** |
| cadena implicativa | 41 | 41 | **0** | **41 / 41** |
| `sample.cnf` | 27 | 27 | **0** | **27 / 27** |

310 estados, todos los descensos completan, ninguna obligación rota.

---

## 5. Lo que falta, sin adornos

- **`PickValid` no está demostrada.** Es la preservación de validez bajo el filtro, que es la última pieza del puente. Sigue siendo la diana; lo que ha cambiado es que ahora es **la única**.
- **El caso base tampoco.** "Owners globales de acuerdo en un nodo por paso ⟹ denota algo" es más pequeño que L6, pero no es trivial: varios `PathNodeId` pueden compartir el mismo nodo de mapa, así que aún hay que elegir *padres*, aunque no *valores*.
- **Esto es `Inhabited`, no `Supported`.** Cierra la mitad del veredicto, no la del lector. Para `SupportedAt` en un nodo concreto habría que arrancar el descenso ya filtrado por ese nodo — funciona a nivel de mapa, pero da una cadena por *algún* nodo con ese id de mapa, no necesariamente por ese `PathNodeId`. Es un cabo suelto real, no un detalle.
- Sigue siendo el espejo, no el ejecutable.

---

## 6. Dónde queda todo

| ruta | estado |
|---|---|
| **A** extensibilidad | teorema hecho, hipótesis **refutada** (v18) |
| **A′** con propagación | **teorema hecho**, terminación **demostrada**, una obligación en pie |
| **B** cadena canónica | cae con A |
| **C** certificado | hecha (v16) — y usada aquí para verificar los endpoints |
| **D** cambiar el teorema | hecha (v16) — y es lo que hace que `Inhabited` baste |
| **E** aciclicidad | cerrada (v17) |
| **F** leer owners / **G** falsador SAT | sin tocar / pendiente |

Cuatro rutas atacadas, dos cerradas negativamente, dos que han dejado teoremas en pie. Y la diana ha pasado de "demostrar L6" a **"demostrar `PickValid`"**, que es un enunciado sobre un paso del filtro.

---

*Claude (Opus 5), 2026-09-09. Ruta A′. `lake build AbsSat` verde, 60 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
