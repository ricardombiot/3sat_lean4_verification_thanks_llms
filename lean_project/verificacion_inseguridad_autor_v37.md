# Verificación para el Autor v37: El bug corregido en el ejecutable — y el espejo, pendiente

Ricardo, soy Claude (Opus 5). Tenías razón: es un bug real. **Está corregido en el ejecutable y validado.** El espejo no, y te digo exactamente por qué y qué queda.

---

## 1. El bug, y tu semántica

> La poda de owners siempre debe desenlazar a los padres incompatibles, y si el nodo se queda sin padres se invalida y se elimina, porque sabríamos que nunca podría formar parte de una cadena solución.

Exacto, y es lo que faltaba. `remove_node_owner!` desenlaza cuando un nodo **se elimina**, pero las intersecciones de `clean_invalid_nodes!` y `review_owners_line!` solo encogían `owners`: los `parents` y `sons` se quedaban con vecinos que la propagación ya había descartado.

**Medido antes del arreglo:** 37 enlaces padre y 71 enlaces hijo rancios por cada ~328.000, y **escalando** con el tamaño de la campaña (36 → 277 nodos afectados). No era ruido.

## 2. La corrección

`GraphPath.lean`, nueva función `unlink_incompatible!`, llamada en los dos sitios donde se podan owners:

- por cada padre que ya no es owner: se desenlaza **en los dos sentidos** (el padre también pierde a este hijo);
- ídem por cada hijo;
- y a continuación `remove_if_invalid_node!` hace el resto: un nodo no raíz sin padres falla `is_valid_node` y se elimina — que es justo lo que pediste.

El desenlace es simétrico a propósito: si solo se quitara de un lado, las tablas `parents` y `sons` dejarían de reflejarse entre sí, que es un invariante que sí está demostrado (`Sons.SMP`, v29).

## 3. Validación

`lake exe diffTest`: **300/300 de acuerdo con el oráculo de fuerza bruta** (264 SAT, 36 UNSAT), veredictos **y conjuntos completos de soluciones** sin cambio.

Eso es exactamente como debe verse un arreglo correcto de este tipo: **no cambia ninguna respuesta**, porque solo poda cosas que ya eran inservibles. Si hubiera cambiado un veredicto o una solución, el arreglo estaría mal.

---

## 4. Lo que NO he hecho, y por qué

**El espejo (`GPathM.lean`) sigue sin el arreglo.** Lo intenté, y llegué a este punto:

| pieza | estado |
|---|---|
| `unlinkIncompatible` en el espejo | escrita |
| `Pruned` (`pruned_unlinkIncompatible` y los dos sitios) | reparado |
| las cotas de medida en `Fuel` | reparadas |
| **F2.c** (`intersectOrDrop_eq_self`) | **falta** — necesita un lema nuevo: *"desenlazar es la identidad en el punto fijo"* |
| **`CleanInvalid`, `Coherence`, `Review`, `AddNode`** | **ni empezado** — las pruebas de preservación de `ChainSound` |

Lo revertí para no dejarte el repositorio sin compilar. La parte gorda es la última: ahora el enlace padre de una cadena sobrevive al desenlace **porque la cadena está co-poseída**, y ese es un argumento nuevo que hay que meter en cada una de esas pruebas. No es difícil conceptualmente; es largo.

### La consecuencia, dicha claramente

Hasta que migre el espejo, **el espejo y el ejecutable difieren**: el espejo poda menos. Es una diferencia conocida y conservadora, y `diffTest` sigue pasando porque compara cada banda contra el oráculo por separado. Pero los lemas del puente hablan del espejo, así que hablan de una máquina que ya no es exactamente la tuya.

Y una nota práctica: **mi arnés de medición mide el espejo**, así que seguirá reportando enlaces rancios hasta que lo migre. No es que el arreglo no funcione; es que no lo está midiendo.

---

## 5. Una cosa que el episodio dice a favor del espejo

El bug estaba en tu ejecutable **y el espejo lo reprodujo fielmente**. Por eso se pudo encontrar midiendo el espejo. Es la primera vez que la fidelidad del espejo paga en la dirección útil: no ha servido solo para demostrar cosas, ha servido para **encontrar un fallo real en el código de verdad**.

---

## 6. Lo siguiente

1. Migrar el espejo (`GPathM`, `Pruned`, `Fuel` F2.c, y las cuatro pruebas de `ChainSound`).
2. Re-medir con el arnés para confirmar que los enlaces rancios desaparecen.
3. Re-correr `validate` y las campañas, que ahora hablarán de la máquina corregida.

---

*Claude (Opus 5), 2026-09-09. Bug reportado por el autor. `lake build AbsSat` verde, 70 módulos, 0 `sorry`. `diffTest` 300/300.*
