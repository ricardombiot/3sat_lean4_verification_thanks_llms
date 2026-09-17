# Verificación para el Autor v130: el ID fija el testigo, y los varios padres son el precio de la abstracción

Ricardo, soy Claude (Opus 5). Me pediste atacar la condición de padres con el testigo fijo del nodo alto
y formalizar por diseño, señalando que el ID va construyendo una cadena de padres. Tenías razón en el
mecanismo, y lo he demostrado. Pero al medirlo he **refutado** la ruta que estaba construyendo, y creo
que la refutación dice algo importante sobre tu diseño. Lo escribo tal cual.

Rama `spaik`, build de `AbsSat` (185 jobs), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. Demostrado: el identificador fija el testigo (`ParentWitness.lean`)

Un `PathNodeId` es un nodo de mapa **más el nodo de mapa de su padre**, así que el ID ya trae un eslabón
de su cadena. La invariante `PMP` lo convierte en un hecho de estado:

- **`parents_id_eq`**: todo padre de un nodo lleva el nodo de mapa que nombra el ID del propio nodo. Es
  decir, **todos los padres de un nodo coinciden en su nodo de mapa**.
- **`parents_differ_below`**: dos padres distintos solo pueden diferir en *su* padre, un paso más abajo.
- **`par_witness_triple`**: y de ahí el paso que faltaba desde v122. La condición `par` pide un padre de
  `x` enlazado con `x` y con otro miembro `v`; al restringir la relación a una rebanada hace falta que
  ese padre también esté enlazado con el ancla `z` —un testigo para un **trío**—. Pero el testigo que la
  consistencia de pares da para `v` y el que da para `z` son **los dos** padres de `x`, luego nombran el
  mismo nodo de mapa; **si el nodo tiene un solo padre son el mismo nodo** y la consistencia de pares
  entrega el trío.

El hueco nunca fue *qué nodo de mapa*: el ID lo fija. Está un nivel más abajo.

## 2. Refutado, con medida: la rebanada del ancla no es un soporte

La sonda `helly triples` comprueba exactamente lo que `par` necesita, en los nodos con **varios** padres
(lo que el teorema deja abierto): para cada nodo `x`, cada nodo alto `z` que posee, y cada owner `v` de
`x` **que también posee `z`** (es decir, dentro de la rebanada del ancla), ¿hay algún padre de `x` que
posea a la vez `v` y `z`?

| familia | estados | nodos | con varios padres | comprobaciones | **sin trío** |
|---|---|---|---|---|---|
| Tseitin K4 par | 108 | 3.500 | 442 | 15.180 | **72** |
| Tseitin cubo par | 220 | 20.838 | 4.276 | 439.091 | **5.712** |
| Tseitin K3,3 par | 164 | 10.468 | 1.800 | 122.050 | **592** |

Y **fijar el ancla no lo arregla**: `helly triplesPin` repite la medida sobre el estado con el nodo de
mapa del ancla fijado y da cifras **idénticas**, porque todos los nodos altos de un estado comparten el
mismo nodo de mapa (la clave); solo difieren en el padre. El lenguaje de fijaciones habla de nodos de
mapa, así que **no puede separar los dos**: la fijación es una no-operación.

Conclusión: **la rebanada de un nodo, con la relación de owners entera, no es un soporte**. En esos 72
casos un padre de `x` es compatible con `v` y otro con `z`, pero ninguno con los dos.

## 3. Lo que eso dice de tu diseño

Los nodos con varios padres no son un defecto: son el mecanismo. Si el ID llevara la cadena completa de
su padre en vez del último nodo de mapa, cada nodo tendría **un solo** padre, y por el teorema de la
sección 1 el trío se cerraría **por diseño, en todos los nodos**. Pero entonces el ID sería un camino, y
eso es exactamente la explosión espacial que tu abstracción evita.

Así que el salto de pares a tríos es **el precio de la abstracción**, no un hueco de la demostración. Y
de ahí se sigue qué forma tiene que tener la prueba: el soporte no puede ser la relación de owners sobre
una rebanada, porque eso exige un testigo común; tiene que permitir que **el testigo varíe por par**.
Eso es precisamente `ChainSound` / `PairChain` de v123 —cada par de owners sobre una cadena completa,
cada uno con la suya— medido con **0 excepciones** en todas las líneas y recorridos del lector.

## 4. Lo que queda

1. **La obligación abierta vuelve a ser `FilterKeepsPairChain`** (v123): el filtro y el review dejan cada
   par de owners sobre una cadena completa. Es la forma correcta del soporte a la vista de la sección 3,
   y la única de las tres rutas que la medida no ha tocado.
2. **No insistir** en rutas con testigo común: rebanada del ancla (esta sección 2), cierre de triángulos
   `SPC` (v122) y soporte estático (v119) están refutadas por medida.
3. La vía de diseño de v129 §5 (marcar la procedencia de las entradas) sigue siendo tuya, con el coste
   ahora mejor entendido: es el mismo coste que separar los padres en el ID.
