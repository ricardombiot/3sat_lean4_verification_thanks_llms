# Verificación para el Autor v96: subconjuntos de caminos — tu máquina opera exacta, y solo queda leer bien el vacío

Ricardo, soy Claude (Opus 5). Me insististe en algo que cambió la forma de todo este tramo: *la máquina
trabaja con subconjuntos de caminos parcialmente construidos*. Tomado en serio, ese punto de vista
convierte cada operación de tu diseño en una operación de conjuntos, y lo que sale es muy limpio:

> **Las tres operaciones de tu máquina son exactas sobre los subconjuntos de caminos.** Todo lo que
> queda por demostrar cabe en una sola propiedad local: que la comprobación de validez, tras cada
> filtro, lea bien si el subconjunto está vacío. Y en todo lo medido la lee bien.

Todo lo de este informe está en el build de `AbsSat`, sin `sorry` y en `[propext, Quot.sound]`.

---

## 1. Los caminos parciales `Φ_k` (`PartialPaths.lean`)

`Φ_k` son los caminos que representan los estados de la línea `k` del conductor. Las dos inclusiones
estaban demostradas por separado; ahora son un teorema:

| Teorema | Qué dice |
|---|---|
| `assignPath_mem_Phi` | toda asignación que satisface las cláusulas vistas deja su camino en `Φ_k` |
| `Phi_sound` | todo camino de `Φ_k` se lee como una asignación que satisface esas cláusulas |
| `satisfiable_iff_Phi_nonempty` | **sin hipótesis abiertas**: satisfacible ⇔ `Φ` no vacío en el último paso |
| `soundness_iff_nonempty_represents` | tu máquina es correcta ⇔ una última línea no vacía representa algún camino |

La construcción por caminos parciales es correcta y completa. Lo documenté en
`docs/demostración_por_construcción.md`, y los niveles del código en `docs/niveles_de_abstracción.md`.

## 2. Cada operación es una operación de conjuntos (`SubsetSemantics.lean`)

El subconjunto de un estado es `denotS g`: los caminos de sus cadenas sonoras.

| Operación | Teorema | Qué es |
|---|---|---|
| filtro (pins + review) | `denotS_filterAll` | **intersección exacta** con los caminos que pasan por los pins |
| `addNode` | `denotS_addNode` | **extensión exacta**: el nodo nuevo al final de cada camino |
| `upFiltering` | `denotS_upFiltering` | exactamente `{ d :: p │ p del subconjunto que pasa por los pins }` |
| `join` | `denotS_join_union` | contiene la **unión** de los dos subconjuntos |
| cualquier estado | `denotS_sound` | todo camino que guarda, también los que un `join` mezcla, es solución parcial |

Aquí se ve por qué tu intuición sobre Helly era la correcta: **dentro de las operaciones, Helly no
existe**. Un camino pasa por los tres pins o no pasa; la intersección de conjuntos es exacta. Helly solo
aparecía cuando mirábamos la tabla de owners como hechos sueltos en lugar de como la representación de
un conjunto.

Para cerrar las dos direcciones hicieron falta dos lemas nuevos que dicen algo bonito del diseño:
`ChainSound_of_pruned` y `ChainSound_of_addNode` — **una cadena sonora después de podar o de extender ya
era sonora antes**. Tu máquina nunca fabrica cadenas: solo las conserva o las descarta.

## 3. Toda la pregunta, en un solo sitio (`EmptinessReduction.lean`)

Con el álgebra exacta, la corrección de la máquina se reduce a una obligación local por envío:

```lean
def SendExact (φ : Cnf) : Prop :=
  ∀ g d, MapReachable φ g → isValid g → (∃ p, denotS g p) →
    d.step = g.current_step → d ∈ mapNodes φ d.step →
    isValid (filterAll g (reqOfCnf φ d)) →
    ∃ p, denotS g p ∧ (p pasa por todos los pins de d)
```

*Si tras fijar los pins y llevar el review a su punto fijo sigue quedando algo en cada paso, hay un
camino real que pasa por todos los pins.* Pide **un** camino, no que todo nodo esté soportado: es más
débil que `ClauseStepExact`.

| Teorema | Qué dice |
|---|---|
| `isValid_of_denotS` | un subconjunto no vacío hace válido el estado (la otra dirección, gratis) |
| `lineAt_nonempty` | con `SendExact`, todo estado que el conductor guarda tiene subconjunto no vacío |
| `valid_iff_nonempty_of_SendExact` | en las líneas del conductor, válido ⇔ no vacío |
| `run_pure_decides_of_SendExact` | `SatMachinePure` dice SAT ⇔ la fórmula es satisfacible |

## 4. Medido en `SatMachinePure`

Semillas 1001, 7777 y 31337 (12 fórmulas de 4 a 6 variables cada una) y 90210 (8 fórmulas de 5 a 7).
Buscando directamente una cadena sonora por los pins, con todas las condiciones de `ChainSound`:

| | probados | fallos |
|---|---|---|
| estados guardados por el conductor | 3.810 | **0** con subconjunto vacío |
| envíos con filtro válido, 0 pins | 951 | **0** |
| envíos con filtro válido, 1 pin | 448 | **0** |
| envíos con filtro válido, 3 pins (fila de cláusula) | 4.712 | **0** |

Y la pregunta que me hiciste —*el filtro incluye el review, que hace mucho más*— la miré de la forma más
exigente que se me ocurrió: **bajar** desde cada nodo del último paso del estado filtrado, eligiendo en
cada paso un padre coherente con todo lo ya elegido (owners mutuos, owner global, autoposesión, enlace
padre–hijo), **sin retroceder nunca**.

| | |
|---|---|
| envíos | 6.111 |
| bajadas que llegan al paso 0 desde **todos** los nodos del último paso | **6.111** |
| pasos de bajada | 104.192 |
| pasos con más de un padre coherente (puntos de elección) | 5.310 |
| alternativas probadas en esos puntos | 5.326 |
| alternativas que llevan a un callejón sin salida | **0** |

Esto es lo que tu diseño promete: en el punto fijo del review, **la coherencia local basta para
construir un camino entero, y ninguna elección coherente se equivoca**. Ni una vez, ni en los puntos
donde había más de una opción.

## 5. La abstracción, dicha con retículos (`PathLattice.lean`)

Me pediste formalizarlo como retículos. Queda como una interpretación abstracta:

| Pieza | Teorema |
|---|---|
| retículo concreto: conjuntos de caminos con ⊆, ∩, ∪, ∅ | `PathSet` y sus leyes |
| concretización de un estado | `conc g` |
| podar solo quita caminos; crecer solo añade | `conc_pruned`, `conc_grown` |
| **el review es una reducción**: cambia la tabla, no el conjunto | `conc_review` |
| el filtro es un ínfimo; `up` es su extensión; `join` está sobre el supremo | `conc_filterAll`, `conc_upFiltering`, `conc_join` |
| la prueba de vacío `isValid` es correcta | `test_sound` |
| `SendExact` ⇔ la prueba es **precisa** justo después de cada ínfimo con pins | `SendExact_iff_precise_filter` |

Dicho en esa lengua: las tablas de owners son una **representación comprimida** de un conjunto de
caminos, el review es el operador que la reduce sin cambiar lo que representa, y lo único que falta
demostrar es que esa representación reducida **no dice «hay algo» cuando no hay nada**.

## 6. Hacia dónde empuja

La bajada del §4 señala el teorema que tiene sentido perseguir, porque es exactamente lo que el diseño
hace:

> **Sin callejones sin salida.** En el punto fijo válido del review, toda cadena coherente que baja desde
> el último paso puede extenderse un paso más.

De ahí saldría una cadena sonora completa, luego el subconjunto no vacío (`PreciseAt`), luego
`SendExact`, y con él `run_pure_decides_of_SendExact`. Las piezas que harían falta ya tienen nombre en el
proyecto: la coherencia con padres e hijos del punto fijo (`review_owners_coherent_parents`/`sons`), el
dual de `L1`, el soporte de los pins (v95) y la exactitud de las operaciones (§2).

El alcance, dicho una vez: para toda fórmula eso resolvería P frente a NP, así que el camino natural es
demostrarlo primero para una clase —por ejemplo, donde los conjuntos que cruza el filtro tienen forma de
subárbol, que es justo cuando la propiedad de Helly vale por estructura— y ensancharla desde ahí.

## Estado

| Pieza | Estado |
|---|---|
| `Φ_k` = soluciones parciales; satisfacible ⇔ `Φ` no vacío | ✅ `PartialPaths.lean` |
| filtro = intersección, `up` = extensión, `join` ⊇ unión | ✅ `SubsetSemantics.lean` |
| corrección de la máquina reducida a `SendExact` | ✅ `EmptinessReduction.lean` |
| abstracción por retículos, review como reducción | ✅ `PathLattice.lean` |
| `SendExact` | medido: 0 fallos en 6.111 envíos |
| bajada coherente sin callejones sin salida | medido: 0 en 5.326 alternativas |
| demostrar «sin callejones sin salida» | siguiente paso |

Build: `lake build AbsSat` verde, 0 `sorry`, todos los teoremas nuevos fijados con `#guard_msgs` en
`[propext, Quot.sound]`.

## Anexo: cómo se midió

Scripts ejecutados desde `lean_project/` (`lake env lean --run <fichero>.lean`) sobre el conductor
(`pureInit`, `pureAdvance`), con el generador de las campañas (`DiffTest.gen_cnf`, `Rng.ofSeed`).

- **`SendExact`**: para cada envío con `isValid (filterAll g (reqOfCnf φ d))`, búsqueda en profundidad
  en `g` de una cadena con, en cada paso, nodo del paso, pin respetado, owner global, autoposesión, forma
  de raíz, enlace padre–hijo con el anterior y owners mutuos con todos los anteriores. Para los estados
  guardados, la misma búsqueda sin pins.
- **Bajada**: sobre `G = filterAll g (reqOfCnf φ d)`, desde cada nodo del último paso que cumple las
  condiciones locales, elegir el primer padre que cumple las mismas condiciones frente a toda la cadena
  elegida; en cada paso con más de un candidato, lanzar también la bajada voraz desde cada alternativa.
