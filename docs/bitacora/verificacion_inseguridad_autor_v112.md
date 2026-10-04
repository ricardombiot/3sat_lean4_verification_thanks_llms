# Verificación para el Autor v112: corrección de v111 — tu Reader no lee por arriba

Ricardo, soy Claude (Opus 5). Este informe corrige v111. Allí llevé la obligación de la solidez al
estado final con `FinalReadable` (ningún fantasma anclado arriba) y di a entender que un lector sin
backtracking se atasca donde hay fantasmas. Las dos cosas necesitan corrección: `FinalReadable` es
falsa en general, y el lector que fallaba **no era el tuyo**. Tu Reader lee todos los casos que
construí, por cualquier camino de elecciones. Al final propongo cómo formalizarlo tal como lo
diseñaste.

---

## 1. Qué se corrige de v111

- **"0 fantasmas en el tope de los estados finales"** solo valía para las fórmulas aleatorias que
  medí. No es una propiedad general (sección 2).
- **`FinalReadable` como obligación**: es falsa para fórmulas concretas, así que
  `run_pure_decides_of_FinalReadable` es un resultado condicional correcto pero vacío para ellas. El
  docstring de `FinalReadable.lean` ya lo dice.
- **"El lector sin backtracking se atasca"**: se refería al lector de mi sonda, que baja desde el tope
  por las filas de cláusula eligiendo candidatos compatibles por parejas y sin filtrar ni hacer review.
  Ese no es `PathReader`.

Sigue siendo válido de v111: la equivalencia `noDeadEnd_iff_noTopPhantom`, `topAnchor_valid` (todo
estado válido de la máquina tiene pick en el tope) y la refutación de `FilterNoDeadEnd` con
`Probes/cnf/top_phantom_s31337_4.cnf`.

## 2. Los fantasmas sí llegan al estado final

Antes de intentar demostrar `FinalReadable` intenté romperla con una construcción, no con búsqueda
aleatoria, siguiendo la forma del fantasma de v111 (conflicto abajo, filas compatibles arriba):

- **abajo**, las primeras cláusulas: una cadena de XOR que impone `x₁ ⊕ … ⊕ x_k = 0`;
- **arriba**, las últimas: una cláusula `(xᵢ ∨ p ∨ q)` por variable, cuyas filas pueden fijar `xᵢ = 1`.

Con `k` impar, todos los `xᵢ = 1` no tienen modelo, pero cualquier par sí (comprobado por fuerza
bruta). Los gadgets están en `lean_project/Probes/cnf/p2/`.

En `par_k5_chain_asc_shared.cnf` (9 variables, 17 cláusulas) el estado final tiene **48 cadenas
completas, exactamente los 48 modelos**, y aun así **48 callejones en el tope**: 5 picks en caminos
consistentes, 20 de 20 pares ideales y 4 candidatos bloqueados cada uno por un pick distinto. Helly
puro, en el estado final. Con `k = 7` igual. Con la paridad de 3 variables en una sola cláusula no,
porque ahí la máquina la ve por parejas.

## 3. Lo que hace tu Reader

`docs/original_julia/src/graph_path/reader/path_reader.jl`, `read_step!`:

1. lee **de abajo arriba y solo el bloque de literales**: pasos 0, 2, 4…, una variable por paso;
2. toma el primer id del paso y **fija su nodo de mapa**, es decir, el valor de la variable;
3. `filter!`: `filterRequire` más review hasta el punto fijo;
4. si el grafo queda inválido, `"GRAVE ERROR READER"`. No hay backtracking.

La sonda lo reproduce con `lake exe join-borrow read <cnf>`, y además recorre **todas** las
elecciones posibles, no solo la primera. Traza del contraejemplo de la sección 2:

| variable | valores disponibles | fija | válido | nodos | cadenas completas |
|---|---|---|---|---|---|
| x1 | 0, 1 | 0 | sí | 153 | 24 |
| x2 | 0, 1 | 0 | sí | 119 | 12 |
| x3 | 0, 1 | 0 | sí | 76 | 6 |
| x4 | 0, 1 | 0 | sí | 55 | 3 |
| **x5** | **solo 0** | 0 | sí | 55 | 3 |
| x6, x7 | solo 0 | 0 | sí | 55 | 3 |
| x8 | 0, 1 | 0 | sí | 37 | 1 |
| x9 | solo 1 | 1 | sí | 37 | 1: un modelo |

Con todas las elecciones, en los seis gadgets: **lecturas correctas = número de modelos** (12, 12,
48, 48, 192, 192), 0 atascos, 0 respuestas erróneas, y ninguna fijación deja un estado válido sin
cadenas.

## 4. Por qué los fantasmas del medio no le afectan

Cada fijación con review deja **exactamente** los modelos compatibles con lo fijado: las cadenas se
reducen a la mitad en cada paso. La fila de x5 lo muestra: tras fijar x1…x4, el review ya ha borrado
el valor de x5 que rompería la paridad. Fijar reduce un dominio a un solo valor, y con dominios de un
solo valor la información por parejas se vuelve global.

Un fantasma es una **selección** de nodos vivos anclada arriba: filas de cláusulas altas elegidas sin
haber fijado las variables de abajo. Tu Reader nunca selecciona así. Solo fija **nodos sueltos** (un
valor cada vez), en la misma dirección en que la máquina construye, y cada fijación se propaga antes
de la siguiente. Lo único que necesita es que **cada valor que queda disponible pertenezca a alguna
cadena**. Esa es una propiedad de nodos, no de selecciones, y Helly no la toca.

## 5. Cómo formalizarlo con el Reader original

La idea es que el invariante del lector sea **semántico** —el estado actual contiene alguna cadena—
y no estructural. Así los fantasmas no aparecen en ningún enunciado.

**F0 — El lector como función.** `readFrom G k` itera sobre los pasos de valor
`k = 0, 2, …, litBlock φ − 2`: toma el primer valor disponible, calcula `filterAll G [nodo de valor]`,
falla si no es válido y devuelve la asignación leída. Es una traducción directa de `read_step!`.

**F1 — Un lector que elige bien siempre acierta.** Demostrable ya, sin hipótesis abiertas:

- si `G` contiene una cadena `c` y se fija el valor que `c` da a la variable siguiente, el estado
  sigue siendo válido y sigue conteniendo `c` (`denotS_filterAll_of`, `isValid_of_denotS`; es la
  misma idea que `Reader.isValid_pin_of_chain`);
- con todas las variables fijadas y el estado habitado, la asignación leída es la de una cadena, y las
  cadenas son modelos (`satisfiable_iff_Phi_nonempty`), así que es un modelo;
- y si φ es satisfacible, el estado final está habitado (`pureRun_full_state`).

Resultado: **para toda φ satisfacible, un lector que fija el valor de alguna cadena lee un modelo sin
backtracking.** Sin fantasmas, sin Helly, sin hipótesis.

**F2 — La elección del autor (`first(ids)`).** Para que el primer valor disponible sea bueno basta
con **`ValuesOnChains`**: en cada estado que visita el lector, todo valor disponible en el paso
siguiente está en alguna cadena. Entonces `first(ids)` es un valor de cadena y se aplica F1. Esta es
la única obligación abierta del lector. Es exactitud de nodos (ningún valor zombi) en una familia
concreta de estados, y lo medido hoy la cumple en su forma fuerte: ninguna fijación deja un estado
válido sin cadenas.

**F3 — Relación con el veredicto.** Si φ es insatisfacible, la línea final está vacía y el lector no
se ejecuta, así que F1 y F2 solo hablan de fórmulas satisfacibles. Lo que F2 no evita: si la máquina
dijera SAT para una φ insatisfacible, el estado final sería válido pero sin cadenas y ningún valor
estaría en una cadena. Por eso `ValuesOnChains` sobre **todo** estado final válido implica también la
solidez del veredicto (es la misma equivalencia que ya registra `Reader.PickSome_of_Inhabited`). Se
pueden separar las dos cosas: F1 más F2 restringido a φ satisfacible dan el lector sin tocar el
veredicto.

## 6. Qué haría a continuación

1. **Medir `ValuesOnChains` a escala** con `join-borrow read` sobre fórmulas aleatorias y sobre el
   escalador adversario, contando valores disponibles fuera de toda cadena. Es barato y es la
   obligación exacta.
2. **Formalizar F0 y F1**, que no dependen de nada abierto y dejan escrito que el lector acierta si
   elige bien.
3. Enunciar **F2** y dejarla como la única hipótesis del lector del autor.
