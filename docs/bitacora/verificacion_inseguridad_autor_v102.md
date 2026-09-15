# Verificación para el Autor v102: tablas ideales, grupos conflictivos y la profundidad de la refutación

Ricardo, soy Claude (Opus 5). v101 dejó `LossInClosureD` abierto y separado en dos piezas: (I) un camino enlazado con
asignación consistente es una cadena, y (II) el núcleo combinatorio. En este tramo he medido las dos, hemos discutido
contigo la validación de la máquina frente a un oráculo y tu regla `review_agressive_consistence!`, y he caracterizado
los casos difíciles de `LossInClosureD`: bifurcaciones que se refutan con una búsqueda local de profundidad acotada. La
pregunta final, si esa profundidad está acotada en general, queda abierta; este informe cuenta qué la mantiene baja y
qué explicación sencilla no funciona.

No hay código nuevo en el repositorio: todo es medición (ejecutables compilados en el scratchpad, Lean 4.33.1) y
análisis. El build de `AbsSat` sigue verde (129 módulos).

---

## 1. La caracterización completa

Paseos aleatorios desde el paso 0 que, en cada paso, eligen un hijo enlazado cuyos valores fijados no contradicen lo ya
fijado; al llegar arriba se comprueba si todos los nodos se poseen mutuamente.

| Estado | Caminos consistentes que son cadena | Que no lo son |
|---|---|---|
| `g` guardado | 359.025 | 0 |
| `P` fijado, todos los owners globales | 293.970 | 0 |
| `P` fijado, parte viva de `Dead` | 372.300 | 0 |

(17 fórmulas: `far2`–`far4`, contraejemplos, adversarias, `entries_e`, semillas 1001, 7777, 31337, 90210.) Con
FixAgree, **las cadenas son exactamente los caminos enlazados con asignación de literales consistente**.

En la parte viva, elegir solo por consistencia sí se queda sin salida en las fórmulas adversarias (1.920 paseos, de 20 a
390 por fórmula; ninguno en `far2`–`far4` ni en tres de las cuatro semillas): hace falta la comprobación hacia delante de
v101.

## 2. Tablas ideales

Para cada estado guardado se enumeran todos los caminos enlazados consistentes sobre sus nodos y enlaces (tope 20.000
caminos, nunca alcanzado) y los owners se sustituyen por las parejas que comparten alguno; luego se fijan los pins y se
recalcula `Dead`.

| Medida | Resultado |
|---|---|
| estados reconstruidos | 12.045 |
| nodos vivos del `P` ideal en un camino consistente por los pins | **391.259 de 391.259** |
| construcción con comprobación hacia delante (muestra) | 124.468 sin atasco |
| nodos vivo/muerto distintos entre ideal y máquina | **0** |
| entradas ideales ausentes de la máquina | **0** |
| entradas de la máquina fuera de todo camino consistente | 8.146 (adversarias y `far`), 0 (aleatorias) |

Los owners de la máquina son la tabla ideal (las proyecciones binarias exactas del conjunto de soluciones) más entradas
obsoletas que no cambian qué nodos mueren. El núcleo (II) no depende de cómo la máquina construyó los owners; sí quedan
de la historia el conjunto de nodos y los enlaces.

## 3. La regla `review_agressive_consistence!`

Tu regla quita `w` de `owners(x)` (y `x` de `owners(w)`) si `owners(x) ∩ owners(w)` queda vacía en algún paso, dentro del
bucle del review hasta el punto fijo.

- Es la regla de soporte por parejas de v100 con simetría. Es correcta: el nodo de una cadena en cada paso está en las
  dos tablas.
- **No cambia qué nodos sobreviven**: es correcta y el review actual no deja zombis en lo medido, así que los dos acaban
  con los mismos nodos; y como `Dead` es monótona en las entradas y las tablas ideales dan el mismo estado vivo/muerto,
  su punto fijo (entre la máquina y la ideal) también.
- **Lo que daría**: simetría por construcción (si `w ∈ owners(x)` y `x ∉ owners(w)`, en el paso de `x` la intersección es
  `{x} ∩ owners(w) = ∅`) y soporte por parejas como invariante de todo estado revisado, lo que quitaría la hipótesis de
  `Threaded.chain_through_of_symmetric`. Los bucles actuales omiten los pasos 0 y superior.
- **Lo que no da**: el núcleo necesita un nodo común a toda una selección, no a cada pareja; los grupos de posesión
  mutua sin cadena de v101 superan la regla por construcción.

## 4. Validación frente a un oráculo

Revisamos `docs/demostración_por_equivalencia.md`. Lo demostrado:

| Pieza | Teorema |
|---|---|
| SAT ⇒ la máquina no se vacía (inválido ⇒ UNSAT) | `PureProofs.completeness_pure`, `Conservation.chainSound_along` |
| lo representado son soluciones | `PartialPaths.Phi_sound`, `SubsetSemantics.denotS_sound` |
| representado no vacío ⇔ satisfacible, sin hipótesis | `PartialPaths.satisfiable_iff_Phi_nonempty` |
| el comprobador certifica cadenas | `Certificate.isCert_sound` |
| decisión | `run_pure_decides_of_SendExact` (bajo `SendExact`) |

**La máquina ya construye el conjunto de todas las soluciones**; la igualdad con la fuerza bruta es empaquetar esas
piezas. Lo abierto es la prueba de vacío: la máquina dice SAT si queda un estado *válido*, y un grafo válido podría no
representar ninguna cadena (un zombi). `SendExact` / `LossInClosureD` dicen que eso no pasa.

Sobre el documento: `BruteForce.lean` usa dos axiomas (`enum_complete_ax`, `toAssign_eq_ax`) y no está en el build;
`Set` no existe sin Mathlib; `decode sel = a` debe restringirse a las variables de φ (varias cadenas decodifican la misma
asignación si hay filas parciales). Plan acordado: demostrar los axiomas e incluirlo en el build, enunciar la igualdad con
la restricción, y emitir el veredicto con una cadena certificada por `isCert` (demostrado sin hipótesis; la eficiencia
queda como el lema del paso).

## 5. Grupos conflictivos

Nodo `x` sin cadena por los pins que forma con una variante de cada pin un grupo de posesión mutua en `g` (v101).
Buscando cadenas con cada subconjunto de pins:

| Perfil (mejor paso) | Nodos |
|---|---|
| **bifurcación**: cada alternativa de `x` en el paso queda sin cadena con **un** pin, y no con el mismo | **1.032** |
| todas las alternativas bloqueadas por el mismo pin (posesiones obsoletas) | 24 |

**Regla T** (local, polinómica y correcta): matar `x` si hay un paso donde, para cada alternativa `a`, algún pin no tiene
ninguna variante en posesión mutua con `x` y con `a`.

| Nodos | Mata la regla T (una pasada) |
|---|---|
| en una cadena por los pins | **0 de 258.368** |
| sin cadena, fuera de grupo | **95.397 de 95.397** |
| sin cadena, en grupo conflictivo | 945 de 1.056 |

Iterada hasta su punto fijo (≤ 3 rondas) quedan 31 (`outsideR_a` 6, `outsideR_b` 19, `outsideR_c` 6). Ampliada a
parejas de pins no añade nada.

## 6. Refutación local de profundidad acotada

La profundidad `d + 1` refuta una selección `S` si hay un paso donde, para cada alternativa compatible con `S`, algún pin
tiene todas sus variantes compatibles refutadas a profundidad `d` (o ninguna). Es correcta por construcción: una cadena
aporta en cada nivel una alternativa y variantes compatibles.

| Fórmula | Grupos | Profundidad 1 | Profundidad ≤ 2 | Nodos con cadena refutados (muestra) |
|---|---|---|---|---|
| `outsideR_a` / `outsideR_b` / `outsideR_c` | 52 / 19 / 222 | 46 / 0 / 216 | **52 / 19 / 222** | 0 de 2.086 |
| `entries_d` / `entries_e` | 5 / 197 | 5 / 163 | **5 / 197** | 0 de 1.185 |
| `adv_seed3` / `adv_seed4` / `adv_seed8` | 42 / 139 / 380 | 42 / 114 / 359 | **42 / 139 / 380** | 0 de 1.749 |

Todos los nodos sin cadena medidos caen con profundidad ≤ 2, sin necesitar el review.

## 7. Búsqueda adversaria de profundidad

8 escaladores × 120 iteraciones (≈ 960 fórmulas de hasta 11 variables y 11 cláusulas), maximizando nodos no refutados
hasta profundidad 3 y después la profundidad necesaria.

| Resultado | |
|---|---|
| profundidad máxima encontrada | **2** |
| nodos sin cadena no refutados hasta profundidad 3 | 0 |
| récord de nodos con profundidad 2 | 112 (desde `adv_seed8`) |

## 8. Análisis en papel: qué mantiene baja la profundidad

**Modelo.** Una cadena equivale a una asignación que satisface las cláusulas procesadas (la negación queda determinada por
el valor; cada fila de cláusula es una asignación completa de sus tres variables). Un nodo de camino fija las variables de
dos pasos consecutivos. Los owners son, en lo medido, las proyecciones binarias exactas. La refutación de profundidad `d`
es un árbol de casos de altura `d` sobre nodos, cuyas hojas se cierran por una pareja sin solución común o un paso sin
candidatos compatibles.

**Técnicas de la máquina que comprimen la profundidad:**

1. **Identificadores de dos pasos**: toda interacción entre pasos consecutivos cabe en un nodo; por eso los casos difíciles
   necesitan cláusulas correlacionadas no consecutivas.
2. **Filas de cláusula completas**: cualquier conflicto dentro de una cláusula se ve por parejas tras ramificar en su paso.
3. **Owners como compatibilidad global**: implicaciones, constantes y saltos forzados a cualquier distancia ya están en
   las tablas.
4. **Revisión iterada**: propaga por el orden de pasos.
5. **Tres pins por filtro**.
6. **Estados separados por clave**: la clave fija las variables de la última cláusula y los `join` solo unen estados con
   la misma clave; un conflicto sobre esas variables se ve en la validez del envío.

**Qué haría crecer la profundidad**: un conflicto que combine varios pins sin que ninguna cláusula ni ningún nodo los
relacione, y tal que en cada nivel todo paso conserve un nodo compatible por parejas con la selección. Las paridades son el
caso clásico (se sabe que la consistencia local de ancho acotado no resuelve sistemas lineales módulo 2: Feder–Vardi 1998;
Atserias, Bulatov y Dawar 2009; y que las proyecciones binarias exactas no bastan para encontrar soluciones en redes
generales: Gottlob 2012). Nuestra refutación usa tablas globales y nuestras instancias tienen estructura propia, así que
ninguno se aplica directamente.

**Por qué no hay cota evidente**: cada nivel suele incorporar un pin, lo que sugiere profundidad ≤ 3; pero con los tres
pins ya en la selección el último nivel solo cierra si algún paso queda sin candidato compatible con toda la selección, que
es de nuevo el caso de tipo Helly.

## 9. Fórmulas de paridad construidas a mano

| Familia | Construcción | Profundidad | `R` máx. | Zombis |
|---|---|---|---|---|
| `parity_m2`, `m3` | paridad de `y` forzados por parejas de pins en una misma cláusula | 1 | ≤ 1 | 0 |
| `mparity_H0`, `H1` | `a ⊕ b ⊕ c ⊕ w = 1` por una cadena XOR, sin cláusulas con dos pins, separadores y relleno | 1 | 0 | 0 |
| **`mparityT_H0`** (13 var., 26 cl.) | lo anterior con dos cláusulas de relleno antes del destino | **2** (490 nodos) | 2 | 0 |
| **`mparityT_H1`** (16 var., 41 cl.) | ídem con un salto XOR con constante | **2** (833 nodos) | 2 | 0 |

- En `parity_m*` dos pins comparten cláusula: se ve por parejas (técnica 2).
- En `mparity_H*` la paridad era la última cláusula antes del destino: la clave de cada estado fijaba `w` y el conflicto
  lo resolvió la validez del envío (técnica 6).
- Con relleno final, la paridad produce muchos más nodos de profundidad 2 que la búsqueda adversaria, pero no profundidad
  3. El salto con constante no sube la profundidad (técnica 3).

## 10. La conjetura por número de pins, refutada

Sea `s` el menor número de pins que deja a `x` sin cadena. La conjetura «profundidad ≤ max(1, s − 1)» daría profundidad
≤ 2 por haber 3 pins.

| `s` | Profundidad 1 | Profundidad 2 |
|---|---|---|
| 1 | todos | 0 |
| 2 | la mayoría | **52** (`outsideR_b` 19, `depth_seed23` 20, `adv_seed8` 7, `outsideR_a` 6) |
| 3 | 30 (`far2` 18, `far4` 6, `outsideR_a` 6) | 630 |

Hay nodos que chocan con solo dos pins y necesitan dos niveles: el segundo nivel viene de una bifurcación intermedia no
ligada a un pin. **La profundidad no depende solo de cuántos pins intervienen.** Tampoco hay, en nada de lo medido, un
nodo de profundidad 3.

## 11. Estado

| Pieza | Estado |
|---|---|
| cadenas = caminos enlazados con asignación consistente | medido sin excepciones (1,03 M caminos) |
| owners = tabla ideal + obsoletas inocuas | medido (12.045 estados) |
| (II) sobre tablas ideales | medido (391.259 nodos) |
| grupos conflictivos = bifurcaciones bloqueadas por pins distintos | medido (1.032 de 1.056; el resto, posesiones obsoletas) |
| regla T correcta; refutación de profundidad ≤ 2 completa en lo medido | medido |
| profundidad acotada | abierto: sin prueba ni contraejemplo; la explicación por número de pins es falsa |
| validación | completitud y conjunto representado demostrados; veredicto por validez abierto (`SendExact`) |
| `LossInClosureD`, `JoinCovered` | abiertos |

Siguiente, según lo acordado: quitar los axiomas de `BruteForce.lean` e incluirlo en el build, demostrar la igualdad del
conjunto representado con la fuerza bruta, y el veredicto certificado. Quedan como líneas de investigación analizar a mano
un nodo de profundidad 2 con `s = 2` y formalizar la refutación con su teorema de corrección.

Build: `lake build AbsSat` verde, 129 módulos, 0 `sorry`, Lean 4.33.1.

## Anexo: cómo se midió

Ejecutables compilados en el scratchpad con el toolchain 4.33.1 explícito, sin tocar el repositorio.

- **Caracterización:** 30 paseos por estado guardado y 20 por envío (todos los owners y parte viva), eligiendo al azar
  entre hijos enlazados consistentes; comprobación de posesión mutua de todas las parejas.
- **Tablas ideales:** enumeración de caminos enlazados consistentes sobre los nodos y enlaces de cada estado guardado,
  owners como coocurrencia; `Dead` y búsqueda de cadena en el estado fijado.
- **Grupos conflictivos:** búsqueda de una variante por pin en posesión mutua con `x`; perfil con búsqueda de cadena por
  `x` y la alternativa en el estado filtrado por cada subconjunto de pins.
- **Regla T y refutación:** con las tablas de owners de `g`; muestra de nodos con cadena para comprobar corrección.
- **Búsqueda de profundidad:** escaladores con semilla; puntuación por nodos no refutados hasta profundidad 3, profundidad
  máxima y recuentos.
- **Paridad:** DIMACS generados (XOR de tres variables con cuatro cláusulas; constante forzada con cuatro cláusulas;
  variables separadoras entre pins; cláusulas de relleno entre grupos y antes del destino).
- **Conjetura por pins:** menor subconjunto de pins sin cadena por `x` frente a la menor profundidad que la refuta.
