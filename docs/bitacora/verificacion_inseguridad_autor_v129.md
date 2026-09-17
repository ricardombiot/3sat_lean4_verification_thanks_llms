# Verificación para el Autor v129: un solo obstáculo, en tres disfraces

Ricardo, soy Claude (Opus 5). Este tramo intenta cerrar `JoinSplit`, la única condición que quedaba tras la
inducción sobre la construcción (v128), y encuentra que se reduce al mismo obstáculo que ya apareció en
v122 y v123. Lo escribo como síntesis, porque creo que es el resultado más útil de la sesión: **en toda la
cadena queda un único hueco matemático**.

Todo en la rama `spaik`, build de `AbsSat` limpio, sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. Una medida que resulta trivial

Medí si, tras el review de una unión, quedan entradas de owners ajenas a los dos lados. En Tseitin K4 par:
32 uniones, 896 restricciones, 769.386 entradas, **0 ajenas**, con 9.857 nodos compartidos entre los dos
lados.

Pero eso **no prueba nada**: el review solo borra, y las entradas de la unión son exactamente la unión de
las entradas de los lados. La medida era trivialmente cierta. Lo digo porque el dato podría parecer un
avance y no lo es.

## 2. Dónde se rompe `JoinSplit`, exactamente

Sea `J` la unión de dos envíos a `d`, con lados `g₁` (clave `k₁`) y `g₂` (clave `k₂`), y sea `B = Fw J C` el
estado revisado bajo restricciones. Sea `q` un owner global de `B`. Sus nodos del paso de origen llevan
`k₁` o `k₂`.

- **Reparto de nodos**: `q` posee un nodo `z` de clave `k₁`; por simetría, `z` posee a `q`; y los owners de
  `z` en la unión son los de `g₁` porque `z` no existe en `g₂`. Así que `q` **es nodo del lado 1**. Esto
  sale.
- **Cobertura**: en cada paso, la consistencia de pares entre `q` y `z` da un owner común, que a su vez
  posee `z` y por tanto está en la rebanada de `k₁`. Esto sale.
- **Padres**: aquí se rompe. Hace falta **un** padre que esté enlazado a la vez con el owner y con el nodo
  de `k₁`: un testigo para un trío, no para pares. Es exactamente `SpcStable` de v122.

## 3. Un solo obstáculo, tres formas

| forma | informe | enunciado |
|---|---|---|
| `SpcStable` | v122 | todo par consistente dentro de la rebanada tiene, en cada paso, un testigo consistente con sus dos extremos |
| conservación de `PairChain` | v123 | el filtro y el review dejan cada par de owners en una cadena completa |
| `JoinSplit` | v128 | la unión restringida reparte sus elecciones entre sus dos lados |

Las tres piden lo mismo: que el punto fijo del review sobre las tablas de un **subconjunto** (la rebanada,
la cadena, un lado del `join`) coincida con el punto fijo sobre las tablas completas. Es la exactitud de las
fijaciones, medida sin excepción en v119, v124 y v128 (19,2 M entradas, 1.725 fijaciones y 2,5 M owners
comprobados), y nunca derivable de la consistencia local: hace falta pasar de pares a tríos.

## 4. Demostrado: la mitad de nodos de `JoinSplit` (`JoinProvenance.lean`)

La parte que **sí** sale la he formalizado, para que el hueco quede aislado en Lean y no solo en prosa:

- `join_node?_only_right` (en `Join.lean`): si un lado no tiene un nodo, el registro de la unión para
  ese nodo es **exactamente** el del otro lado; la fusión no añade nada.
- `node_left_of_not_gowner`, `node_right_of_not_gowner`: en cualquier estrechamiento de la unión, un
  nodo que posee una elección que un lado **no tiene entre sus owners globales** es nodo del otro lado.
- `slice_one_side`: por tanto, la rebanada de una elección exclusiva de un lado tiene **todos** sus
  nodos en ese lado.

Es el mismo hecho que `no_chain_across_sides` daba para las cadenas parciales: **una elección de la
unión no puede mezclar nodos de los dos lados**.

### El criterio: el lado se lee del paso alto

Medí el caso que el lema anterior no cubre —elecciones que **ya tenían los dos lados**— y el resultado
da un criterio, no solo una estadística. En Tseitin K4 par, 32 uniones, 896 restricciones, 27.670
elecciones que sobreviven:

| clasificación por el nodo alto que posee | elecciones |
|---|---|
| nodo alto exclusivo de **un solo** lado | 24.637 |
| nodos altos exclusivos de **los dos** lados | 3.033 |
| ningún nodo alto exclusivo | **0** |

Y el dato que lo convierte en criterio: esos 3.033 son **exactamente** las elecciones que sobreviven en
los dos lados restringidos. Ni una más. Es decir: **una elección sobrevive en el lado *i* si y solo si
posee un nodo alto exclusivo del lado *i***, y nunca se queda sin lado.

Eso está demostrado como reparto de nodos, y para el 100% de los casos:

- `slice_of_exclusive_top`: la rebanada de un nodo que un lado **no tiene** está entera en el otro
  lado. Aplicado a un nodo del paso alto —y cada uno pertenece a un solo lado, porque un envío añade
  un nodo y el `join` conserva los dos— da el lado de cualquier elección: toda elección que sobrevive
  posee algún nodo alto (su registro es válido, así que tiene owner en cada paso) y, por la simetría
  del barrido, pertenece a la rebanada de ese nodo.
- `slice_side_of_tops`: si **todos** los nodos altos que posee una elección son de un lado, su propia
  rebanada está entera en ese lado. Aquí el barrido simétrico hace el trabajo: obliga a cada miembro
  de la rebanada a compartir owner con la elección en *todos* los pasos, el alto incluido.

Lo que queda de `JoinSplit`, con el lado ya elegido y sus nodos ya situados, son las **entradas** de
owners: el soporte de la rebanada vive en las tablas de la unión, y hay que llevarlo a las tablas del
lado. Ahí vuelve a hacer falta el testigo de trío de la sección 3 —para la condición de padres, un
padre común a la elección, a su owner y al nodo alto— y por eso el obstáculo sigue siendo uno solo.

## 5. Una opción de diseño, tu decisión

Tu explicación del `join` sugiere una salida por diseño, no por demostración. Si cada entrada de owners
llevara su **procedencia** (de qué historia viene), el `join` uniría entradas etiquetadas y el review
borraría las cruzadas por construcción: un par sostenido solo por la historia de `k₂` no sobreviviría al
restringir a `k₁`, y `JoinSplit` saldría inmediata, igual que la simetría salió inmediata con tu filtro de
v121.

El coste es espacio: cada entrada llevaría la marca de su origen. La pregunta, que es tuya, es si eso rompe
la abstracción que evita la explosión espacial o si basta con una marca por paso (el identificador del nodo
del mapa de origen), que es mucho más barata.

## 6. Lo que queda

1. **El obstáculo único**: pasar de pares a tríos en el punto fijo del review. En cualquiera de sus tres
   formas; la del `join` es la más local.
2. **Confirmar el criterio** en más familias (las aleatorias están en marcha).
3. **O la vía de diseño** de la sección 5, si decides que el coste es aceptable.
