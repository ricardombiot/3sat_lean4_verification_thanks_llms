# Verificación para el Autor v64: el review simétrico — y tu lectura, medida al pie de la letra

Ricardo, soy Claude (Opus 5). Me pediste explorar el review simétrico, recordando cómo pensaste la lectura: elegir un nodo es asumir elegidos todos sus owners, que son exactamente los nodos con los que es compatible, y después limpiar, que sigue siendo necesario. Lo he construido así, las dos cosas juntas. Hay dos teoremas nuevos y una medida que creo que te va a gustar.

---

## 1. Qué es el review simétrico

Cuando el review quita `q` de `owners(p)`, lo que afirma es *ninguna solución pasa a la vez por `p` y por `q`*. Esa frase es simétrica, pero la máquina solo la apuntaba en un lado. El paso nuevo, `symmetrize`, apunta el otro: cuando la tabla de un nodo encoge, todo nodo que ya no está en ella pierde a ese nodo de la suya.

Va detrás de **cada** intersección que encoge una tabla, tanto en las pasadas de coherencia como en la barrida de inválidos, y justo antes del `unlinkIncompatible` que ya existía. Ese desenlace, además, quita exactamente los enlaces que el paso espejo deja obsoletos.

Y la lectura es la tuya: `pinOwners g r` deja como owners globales `gowners ∩ owners(r)`, **en todos los pasos a la vez** y no solo en el de `r`. Después, el review simétrico hace la limpieza. La limpieza sigue siendo imprescindible, como decías: es la que interseca cada tabla con lo seleccionado.

## 2. Lo demostrado (todo `[propext, Quot.sound]`, 0 `sorry`)

**La simetría ya es un invariante de la lectura, sin ninguna hipótesis.**

```lean
theorem OwnSymmetric_symmetrize_updateAt … (h : OwnSymmetric g) :
    OwnSymmetric (symmetrize (updateAt g id f) id)     -- f solo encoge la tabla

theorem OwnSymmetric_read (rs : List PathNodeId) :
    ∀ g, OwnSymmetric g → OwnSymmetric (rs.foldl readStepSym g)
```

No necesita `NodesAreGowners`, ni validez, ni longitud completa. Compáralo con v63: allí el review original rompía la simetría en la primera pasada (236 violaciones) y a veces no la recuperaba. Ahora **no puede romperse**. Así que el teorema de v61 (todo nodo está en un camino completo que posee entero) queda disponible **en cada paso de la lectura**, no solo en sus extremos.

**Y no pierde ninguna solución.**

```lean
theorem ChainSound_symmetrize   : ChainSound g sel → ChainSound (symmetrize g id) sel
theorem ChainSound_reviewSym    : ChainSound g sel → ChainSound (reviewSym g) sel
theorem ChainSound_readStepSym  : ChainSound g sel → (sel pasa por r) →
                                  ChainSound (readStepSym g r) sel
```

El argumento del paso espejo cabe en una línea: si una solución pasa por `id` y por `m`, entonces `m ∈ owners(id)` por `PairwiseOwned`, así que el espejo nunca toca una entrada de una solución. Y el pinchazo por owners conserva toda solución que pase por el nodo elegido, porque esa solución cabe entera dentro de `owners(r)`.

## 3. Lo medido

**Frente a la máquina original** (`--symreview`, 100 fórmulas de 3 a 6 variables en cinco semillas, fuerza bruta como oráculo):

| | original | simétrica |
|---|---|---|
| veredictos (SAT) | 86 | 86, idénticos |
| soluciones perdidas | 0 | **0** |
| veredictos zombie | 0 | 0 |
| **violaciones de simetría a lo largo de la ejecución** | **132** | **0** |
| fallos de `PickValid` (5.260 elecciones, todas) | 0 | 0 |
| lecturas terminadas y certificadas con `satB` | 86/86 | 86/86 |

Un detalle que no esperaba: la máquina simétrica tampoco rompe la simetría en los `join` ni en `addNode`. Eso no lo he demostrado; lo he medido.

**Tu semántica, al pie de la letra** (`--pinexact`, tres semillas, 6.244 elecciones):

> **Elegir `r` conserva exactamente `owners(r)`.** De 195.167 nodos compatibles con el nodo elegido, **ninguno** muere al elegirlo; y **ningún** superviviente queda fuera de `owners(r)`.

Es decir: sobre la máquina simétrica, **los owners de un nodo son exactamente los nodos que siguen vivos cuando lo eliges**. Es lo que describiste, y los números dicen que la máquina lo hace.

**Consistencia de caminos** (`--triangle`): para todo par que se posee mutuamente, ¿existe en cada paso un nodo que posean los dos? En todos los estados de longitud completa (finales y a lo largo de las lecturas), **0 huecos en unos 197.000 pares**. En estados intermedios de longitud parcial, 9 huecos en más de un millón, y en las dos máquinas por igual. Comprobé que la medida detecta huecos con un grafo hecho a mano: da 3 de 3.

**¿Es `owners(r)` autosuficiente?** (`--selfsupport`): dentro de `owners(r)`, todo nodo conserva un padre y un hijo (0 fallos en 145.969). Pero entre el 1 y el 2 % de las entradas de las tablas no están respaldadas por un enlace así. Luego, tras elegir, **las tablas encogen algo, aunque ningún nodo muera**.

## 4. Lo que eso cambia

Antes, el muro («no hay zombies») tenía una forma difusa. Ahora tiene una frase concreta, medida a 0, y es tu propia definición:

> **en un estado de longitud completa del review simétrico, elegir un nodo no mata a ninguno de sus owners.**

Si eso se demuestra, la lectura nunca se atasca. Y con lo que ya está demostrado (simetría en cada paso, conservación de soluciones, `inhabited_of_noChoice`, `sat_of_inhabited`) la cadena se cierra hasta un certificado 3SAT.

Hay tres piezas del camino y en qué estado están:

- **Que ningún owner se quede sin entrada en algún paso** es el triángulo: 0.
- **Que ninguno se quede sin padre o hijo compatible** es la condición (b): 0.
- **Que ninguno quede incoherente** es la condición (c): falla si se exige tabla intacta, pero no hace falta intacta, solo **no vacía**.

Así que la demostración tiene que ser un argumento de **punto fijo con tablas que encogen**: dentro de `owners(r)` existe una subtabla para cada nodo que el review ya no puede tocar. Es la estructura de `Survive.lean` (`Woven`), pero generalizada de cadenas co-poseídas a conjuntos «owners de un nodo». Esa es la próxima pieza.

Hay una salvedad honesta: el triángulo es 3-consistencia, y la 3-consistencia sola no garantiza consistencia global. Cada paso de lectura necesita un nivel más. Lo que hace diferente este caso es que tras cada elección el review vuelve a un punto fijo de longitud completa, y ahí el triángulo se vuelve a medir a 0. Si eso es un teorema o una casualidad de los tamaños pequeños, lo dirá la demostración, o las campañas grandes (Tseitin, órdenes de variables).

## 5. Lo que queda en firme y lo que no

**Demostrado:** simetría como invariante de la lectura; conservación de soluciones del review simétrico y del pinchazo por owners.

**Medido a 0:** mismos veredictos que el original; 0 soluciones perdidas; 0 asimetrías en la máquina simétrica, `join` incluido; `PickValid`; «elegir `r` conserva exactamente `owners(r)`»; el triángulo a longitud completa; la condición (b).

**No demostrado:**
- Que elegir un nodo no mate a ninguno de sus owners. Es el muro, ahora con forma.
- Que `join` y `addNode` conserven la simetría en la máquina simétrica: medido, no demostrado.
- Complejidad: cero teoremas.

**Cambia tu algoritmo.** El review simétrico y el pinchazo por owners son variantes que viven al lado del original (`SymReview.lean`); no he tocado ni la máquina original, ni el ejecutable, ni Julia. Adoptarlos es decisión tuya.

Build: `lake build AbsSat` verde, 89 módulos, 0 `sorry`, 0 axiomas de proyecto.
