# Verificación para el Autor v97: sin callejones sin salida — de la extensión de cadenas a lo que borra el review

Ricardo, soy Claude (Opus 5). Este informe recoge el tramo en que fuimos a por «sin callejones sin
salida» sobre la máquina actual. Resumido: el enunciado está en Lean y es exactamente lo que
`SendExact` necesita. Lo que falta demostrar se ha ido estrechando hasta una propiedad del estado
recién pineado. Y las mediciones han mostrado con precisión qué hace el review con las cadenas que
no tienen continuación.

Todo lo de Lean está en el build de `AbsSat` (119 módulos), sin `sorry`, en `[propext, Quot.sound]`,
y usa solo las definiciones actuales de la máquina. Las mediciones son sobre `SatMachinePure`,
semillas 1001, 7777, 31337 y 90210 (44 fórmulas de 4 a 7 variables), salvo donde se indica.

---

## 1. El enunciado (`NoDeadEnd.lean`)

| Pieza | Qué dice |
|---|---|
| `SoundFrom g sel lo` | los nodos elegidos entre el paso `lo` y el último cumplen las condiciones de `ChainSound` en ese tramo |
| `NoDeadEnd g` | toda cadena así con `lo > 0` se extiende con un nodo en `lo − 1` |
| `TopAnchor g` | hay un nodo en el último paso que cumple esas condiciones él solo |
| `chainSound_iff_soundFrom_zero` | una cadena que llega al paso 0 es exactamente una cadena `ChainSound` |
| `nonempty_of_noDeadEnd` | `TopAnchor` y `NoDeadEnd` dan un subconjunto de caminos no vacío |
| **`topAnchor_filterAll`** | **tras un filtro válido de un estado alcanzable, el ancla siempre existe** |
| `SendExact_of_FilterNoDeadEnd` | `NoDeadEnd` en cada filtro del conductor implica `SendExact` |

Medición exhaustiva, sobre todas las cadenas y no solo las voraces: **0 callejones en 172.557 cadenas
parciales** de 6.111 envíos, sin cortes por presupuesto. Desde cualquier paso, en la semilla 1001:
0 en 334.077 cadenas de los estados filtrados y 0 en 335.917 de los estados que guarda el conductor.

## 2. Owners es coherencia global, no local

Me corregiste: *owners habla de coherencia global*. Las mediciones lo confirman (semilla 1001):

| Hecho local del punto fijo | Fallos |
|---|---|
| simetría de owners | 33 de 569.904 |
| herencia de owners de padre a hijo | 5.429 de 254.043 |
| un padre que posea a todos los owners de arriba | 493 de 26.787 |
| nodo sin padre mutuo | 0 |
| espejo padres/hijos | 0 |

Ningún hecho local basta. Lo que no falla nunca es la cadena.

## 3. La inducción: `addNode` y `join` (`DescentInvariant.lean`, `JoinDescent.lean`)

Para la inducción sobre la construcción, la propiedad se enuncia desde cualquier paso (`DescendAll`).

- **`descendAll_addNode`** (demostrado): `addNode` conserva `DescendAll`, porque el nodo nuevo es owner de
  todos y posee a todos los owners globales.
- **`descendAll_join`** (demostrado bajo `JoinCovered`): el `join` la conserva si cada cadena del estado
  unido es cadena de un lado o se extiende.
- **`no_chain_across_sides`** (demostrado bajo `OwnersAreNodes`): ninguna cadena del `join` mezcla nodos
  exclusivos de los dos lados.

Lo que el `join` tiene de propio lo mostró la medición: **cadenas mezcladas**, 36 de 267.630, que no son
cadena de ningún lado y que se extienden todas. La traza de una (fórmula 11, clave `(17,2)`) lo explica:

| Estado que entra en el `join` | nodo 2 | nodo 6 | nodos 10 y 11 |
|---|---|---|---|
| desde `(16,7)` | no | sí | sí, poseen al 6 |
| desde `(16,6)` | sí | no | sí, poseen al 2 |
| desde `(16,3)` | sí, 2 y 6 se poseen | sí | no |

**`join` compone caminos nuevos**: cada pareja de la cadena la aporta un estado distinto, y ninguno
contenía los tres nodos. Por `denotS_sound`, esos caminos son soluciones parciales reales.

Otras tres mediciones delimitaron qué no se puede usar:

| Hipótesis | Resultado |
|---|---|
| los nodos de un solo lado poseen a todos los compartidos | falla: 17.619 de 106.758 |
| el ownership entre dos nodos es el mismo en todos los estados | falla: 188 de 97.510 en un mismo `join`, 2.283 de 251.184 en una línea |
| dos nodos que se poseen están en un camino completo del estado | casi: 30 excepciones en 526.954 parejas |

Las 30 excepciones están todas en cadenas que bajan hasta el paso 0 y se atascan subiendo, en un paso de
cláusula. Hacia abajo, los owners siempre fueron exactos.

## 4. El filtro, en términos de subconjuntos (`FilterDescent.lean`)

En vez de seguir la inducción por el `join`, fui al filtro en la forma que usa `SendExact`:

> **`noDeadEnd_filterAll_iff`**: `NoDeadEnd (filterAll g reqs) ↔ PinnedCompletion g reqs`

`PinnedCompletion`: toda cadena desde el último paso que sobrevive al filtro es la parte de arriba de
un camino completo de `g` que pasa por los pins. Con `SendExact_of_pinnedCompletion`:

```
PinnedCompletion  ⟺  NoDeadEnd (filtro)  ⟹  SendExact  ⟹  run_pure_decides
```

Lo abierto es una sola propiedad: lo que el review tiene que garantizar.

## 5. Cómo lo garantiza el review: medido

Sobre los estados justo después de fijar los pins (`P`) y antes del review, busqué las cadenas
condenadas (sin camino completo por los pins) y seguí el review etapa a etapa:

| | |
|---|---|
| envíos | 20.544 |
| cadenas condenadas de frontera | 9.240 |
| **eliminadas en la primera `cleanInvalid`, borrando el nodo de más abajo** | **9.127** |
| eliminadas por las pasadas de padres o de hijos, o en pasadas posteriores | 0 |
| intactas al final | 113, todas en estados finales inválidos que se descartan |

| Por qué se borra ese nodo | |
|---|---|
| sin owner en un paso con pin | 4.506 |
| sin owner en un paso sin pin, porque sus owners cayeron antes en el mismo barrido | 4.612 |
| sin padres | 9 |

Es una **cascada dentro de `cleanInvalid`**: los pins eliminan nodos, `removeNode` los saca de los owners
globales, y los nodos que se quedan sin owners en algún paso caen detrás, en la misma pasada.

## 6. El cierre de eliminación `R` (`RemovalClosure.lean`, `ReviewNodes.lean`)

`R` es esa cascada como punto fijo: un nodo está en `R` si en algún paso todos sus owners globales
están en `R`, o si todos sus padres están en `R`.

| Medido | |
|---|---|
| nodo de más abajo de cada cadena condenada, en `R` | 9.240 de 9.240 |
| nodos que borra el review = nodos de `R` (estados finales válidos) | 41.501 = 41.501 |
| mayor `Fabric` dentro de `P ∖ R` que conserva todo `P ∖ R` | 6.111 de 6.111 |
| estados guardados con un `Fabric` sobre todos sus nodos | 3.774 de 3.774 |

| Demostrado | |
|---|---|
| `unsupported_off_chain`, `pinned_chain_off_unsupported` | ningún nodo de un camino completo por los pins está en `R` |
| `unsupported_removed` | el review borra todo `R` |
| `removed_unsupported` (bajo `FabricOutside`) | todo lo que borra el review está en `R` |
| `survives_iff` (bajo `FabricOutside`) | un nodo sobrevive al filtro **si y solo si** no está en `R` |

La conservación del `Fabric` en el review (`Fabric.FOk_review`) ya estaba en el proyecto y es sobre el
review actual; la comprobé antes de usarla.

## 7. Estado

| Pieza | Estado |
|---|---|
| enunciado, ancla, reducción a `SendExact` | ✅ demostrado |
| `addNode` conserva `DescendAll` | ✅ demostrado |
| `join`, salvo cadenas mezcladas (`JoinCovered`) | ✅ demostrado; `JoinCovered` abierto |
| `NoDeadEnd (filtro) ⟺ PinnedCompletion` | ✅ demostrado |
| el review borra `R`; no toca los caminos por los pins | ✅ demostrado |
| el review solo borra `R` | ✅ bajo `FabricOutside`; medido 6.111 de 6.111 |
| `FabricOutside` | abierto |
| núcleo: un nodo fuera de `R`, bajo una cadena con camino completo por los pins, conserva uno | abierto |

Los dos puntos abiertos son ahora propiedades del estado recién pineado `P` y de `R`, sin dinámica del
review. El siguiente paso previsto es `FabricOutside`: medir si el `Fabric` que cubre el estado guardado,
restringido a `P ∖ R`, sigue siendo un `Fabric`.

Build: `lake build AbsSat` verde, 119 módulos, 0 `sorry`, todos los teoremas nuevos fijados con
`#guard_msgs` en `[propext, Quot.sound]`.

## Anexo: cómo se midió

Scripts en el scratchpad, sobre el conductor (`pureInit`, `pureAdvance`) y el generador de las
campañas (`DiffTest.gen_cnf`, `Rng.ofSeed`). Las mediciones pesadas se compilaron a ejecutable sin
tocar el repositorio: `lake env lean --root=<dir> -c`, los objetos C de `.lake/build/ir/AbsSat`
compilados con `leanc -c`, y enlazado con `leanc`. Pasar de interpretado a compilado bajó una medición
de unos 25 minutos a 80 segundos.

- **Cadenas condenadas:** búsqueda exhaustiva hacia abajo en `P`. Una cadena es de frontera si no tiene
  continuación y sí la tiene sin su nodo de más abajo. El review se repite etapa a etapa y se anota la
  primera etapa en que deja de ser cadena.
- **`R`:** punto fijo sobre las dos reglas, independiente del orden de los nodos, comparado con los nodos
  del estado final.
- **`Fabric`:** mayor tabla simétrica dentro de los owners mutuos de `P ∖ R`, quitando en cada vuelta
  entradas sin padre ni hijo que las respalden y miembros sin entrada en algún paso, hasta el punto fijo.
