# Verificación para el Autor v101: `LossInClosure` refutado, la clausura sobre entradas y lo que sostiene el paso

Ricardo, soy Claude (Opus 5). En v100 quedaba lanzar la búsqueda adversaria (2d) sobre las
configuraciones de pins. La búsqueda no encontró una ronda 3 de `R`, pero sí algo más importante: **`LossInClosure`,
tal como estaba formalizado, es falso**. La máquina no falla; lo que falla es la clausura `Unsupported`, que solo sigue
nodos enteros. Este informe cuenta el contraejemplo, la clausura que lo corrige (demostrada en Lean) y lo que las
mediciones dicen sobre el núcleo que queda abierto, `LossInClosureD`.

Todo lo de Lean está en el build de `AbsSat` (129 módulos), sin `sorry`, en `[propext, Quot.sound]`, sobre las
definiciones actuales. Las mediciones son sobre `SatMachinePure`, con ejecutables compilados en el scratchpad.

---

## 1. La búsqueda adversaria

Escaladores que mutan fórmulas (cambiar un literal, su signo, reemplazar, insertar, borrar o mover una cláusula) y
aceptan la mutación si no empeora la puntuación. La puntuación ordena: nodos borrados por el review fuera de `R`,
ronda máxima de `R`, nodos de ronda ≥ 2 en un mismo envío, nodos de ronda ≥ 2 y de ronda ≥ 1. En cada récord se
comprueba además que el estado filtrado no tenga zombis.

| Tanda | Escaladores | Evaluaciones | Ronda máx. de `R` | Borrados fuera de `R` | Zombis |
|---|---|---|---|---|---|
| 1 (7–9 variables, ≤ 8 cláusulas) | 8 × 400 | ≈ 3.200 | 2 | 0 | 0 |
| 2 (9–10 variables, ≤ 10 cláusulas) | 8 × 150–300 | ≈ 1.850 | 2 | **en 4 de 8** (8, 10, 12, 19) | 0 en los 64 récords |

La ronda máxima de `R` no pasó de 2. El récord de nodos de ronda ≥ 2 en un envío fue 9 (36 en total en la fórmula).

## 2. El contraejemplo

```
p cnf 9 9
9 -3 -8 0
7 -8 4 0
3 8 -1 0
-2 -6 8 0
3 -1 -5 0
2 -4 3 0
-6 5 1 0
3 8 2 0
-6 -9 7 0
```

En el envío de la clave `(23,2)` a `(24,6)`, con pins `x2 = 1, x4 = 0, x3 = 0`:

- el estado de entrada tiene 79 nodos, **todos en una cadena completa** (`NoZombie g`);
- el nodo `(12,0)` (valor `x7 = 0`, padre `x6 = 1`) no está en ninguna cadena completa por los pins y **no es
  `Unsupported`**: en el estado fijado tiene owners vivos en todos los pasos, un padre y un hijo;
- el review lo borra en la primera pasada de `reviewSons`.

Como `(12,0)` no está en ninguna cadena y no está en la clausura, `NoZombieOutside` falla: `LossInClosure (reqOfCnf φ)`
es falso para esta fórmula. En total el review borra 6 nodos fuera de `R` en ella; las otras fórmulas de la tanda 2
llegan a 19. No es un error de la máquina (el review los borra y no quedan zombis), sino de la clausura: el review
también borra **entradas** de owners (las intersecciones con los owners de padres e hijos) y **enlaces** padre-hijo cuya
entrada desaparece, y esas bajas se propagan dentro de la misma pasada. El nodo cae porque las entradas de su hijo
desaparecen antes, no porque su propia revisión lo deje sin owners. Añadir a `Unsupported` una regla «sin hijos»
simétrica de `noParent` no lo arregla.

## 3. La clausura sobre nodos, entradas y enlaces

Una clausura por punto fijo que mata entradas además de nodos:

- una entrada `(x, q)` muere si `q` no está en los owners de `x`, no es owner global, está muerto, o si ningún padre
  (ningún hijo) de `x` con enlace vivo la conserva;
- un enlace `x–p` está roto si `p` está muerto o muere cualquiera de las dos entradas `(x, p)`, `(p, x)`;
- un nodo muere si en algún paso no le queda ninguna entrada viva, o si todos sus enlaces a padres (a hijos) están rotos.

| Versión | Nodos: review vs clausura | Entradas: review vs clausura |
|---|---|---|
| sin la regla de enlaces | exacta | el review borra más (148 a 784 entradas por fórmula en 3 fórmulas) |
| **con enlaces** | **exacta** | **exacta** |

Con enlaces coincide con el review nodo a nodo y entrada a entrada en los tres contraejemplos, en `far2`, en dos
fórmulas adversarias más y en las semillas aleatorias 1001 y 7777 (y a nivel de nodos, además, en `far3`, `far4` y el
resto de fórmulas adversarias).

## 4. `DeadClosure.lean`

`Dead P : Item → Prop`, con `Item` = nodo, entrada, enlace o *soporte* (`carry x p q`: el vecino `p` no conserva `q`
para `x`; separarlo evita disyunciones anidadas en el inductivo). Reglas: `absent`, `gowner`, `owner`, `parentGap`,
`sonGap`, `linkNode`, `linkFwd`, `linkBack`, `carryLink`, `carryEntry`, `noSupport`, `noParent`, `noSon`.

- **`dead_of_unsupported`** — la clausura antigua está dentro de la nueva.
- **`dead_off_chain`** — nada de lo que recorre una cadena `ChainSound` (nodo, entrada, enlace o soporte) está muerto.
- **`dead_gone`** — **el review elimina todo lo muerto**: tras un `filterAll` válido, un nodo muerto no es un nodo, y
  los nodos conservados no llevan entradas, enlaces ni soportes muertos. La prueba usa el contexto de punto fijo del
  review (`Threaded.TCtx`: validez, coherencia con padres e hijos, enlaces dentro de los owners, `SN`, `PMS`), `SMP` y
  `Pruned`.
- **`survives_iff_chainS`** — bajo `NoZombieOutsideD` (todo nodo del estado fijado está muerto o en una cadena
  completa), un nodo sobrevive al filtro si y solo si está en una cadena completa.
- **`LossInClosureD`**, implicado por el antiguo (`lossInClosureD_of_lossInClosure`), y la inducción rehecha bajo él:
  `noZombie_filterAll`, **`noZombie_reachable`**, `filter_keeps_chains`.

La regla `absent` se añadió después (`1365b91`): sin ella el `Dead` formal era más débil que lo medido. El docstring de
`NoZombies.lean` dice ahora que `LossInClosure` es falso en general.

**Aviso, como con `IdClosure` en v100:** como `Dead` coincide exactamente con lo que borra el review,
`NoZombieOutsideD` equivale a «el review no deja zombis». Lo que se gana es una forma inductiva sin orden, no una
obligación más débil.

Aparte: `lean-toolchain` apuntaba a `stable`, que hoy resolvió a Lean 4.34.0 y dejaba inservibles los artefactos de
4.33.1. Queda fijado a `v4.33.1` (`121dafa`).

## 5. Rondas y pasos de eliminación

En `far2` la ronda 2 es una cadena de implicaciones leída a través de los ids: el nodo de ronda 2 cae porque su único
owner vivo en un paso de pin cae en ronda 1, y ese cae porque el suyo en otro paso de pin cae en ronda 0. Si los pasos
que justifican cada eliminación fueran siempre pasos de pin y distintos a lo largo de la cadena, con 3 pins la ronda
sería ≤ 2. **No es así**: en fórmulas adversarias hay eliminaciones cuyo paso no es de pin, repartidas entre varios
pins (`adv_seed4`: 114 en ronda 1 y 25 en ronda 2; `adv_seed8`: 359 y 21). No hay una cota evidente de 2 rondas; en
las semillas aleatorias 1001 y 7777 todo cae en ronda 0.

## 6. Hacia `LossInClosureD`

### 6.1 Las parejas de owners no bastan

Si un nodo `x` sin cadena por los pins forma con una variante de cada pin un grupo de posesión mutua en `g`, ninguna
propiedad por parejas de `g` puede explicar su eliminación.

| Fórmula | Nodos sin cadena en un grupo mutuo con los pins |
|---|---|
| `far2`, `far3`, `far4`, semillas 1001, 7777, 31337 | 0 |
| `entries_d` / `outsideR_b` / `adv_seed3` / `outsideR_a` | 5 / 19 / 42 / 52 |
| `adv_seed4` / `entries_e` / `outsideR_c` / `adv_seed8` | 139 / 197 / 222 / 380 |

El nodo del contraejemplo está entre ellos. El review los elimina usando la estructura de pasos.

### 6.2 Construir la cadena desde lo vivo

Para cada nodo vivo (no muerto) se construye una cadena paso a paso, primero hacia abajo por padres y luego hacia arriba
por hijos, eligiendo un nodo vivo, enlazado y con entradas vivas en ambos sentidos con todo lo ya elegido.

| Regla de elección | `far4` | `outsideR_a` | `outsideR_c` | `adv_seed8` |
|---|---|---|---|---|
| primer candidato | 30 | 75 | 257 | 317 |
| preferir una cadena de `g` por `x` | 18 | 0 | 104 | 167 |
| preferir más entradas vivas | 30 | 43 | 12 | 17 |
| pins primero | 30 | 75 | 257 | 317 |
| **con comprobación hacia delante** | **0** | **0** | **0** | **0** |

(Nodos vivos atascados, todos con cadena. En `far2`, `entries_e` y la semilla 1001 ninguna regla se atasca.)

**Comprobación hacia delante:** un candidato se acepta solo si cada paso aún sin elegir conserva algún nodo vivo
compatible con todo lo elegido. Sin muestreo, sobre **406.929 nodos vivos** de 17 fórmulas distintas y con dos órdenes
de candidatos, no se atascó nunca; y todo nodo vivo cumple por sí solo la propiedad hacia delante.

### 6.3 La forma general

Con elecciones al azar entre los candidatos admisibles:

| Forma | Recorridos | Atascos |
|---|---|---|
| contigua (ampliar por abajo o por arriba, al azar) | 1.173.777 | 0 |
| cualquier orden (un paso libre cualquiera, enlazado con sus vecinos) | 782.518 | 0 |

`LossInClosureD` quedaría así en dos lemas: **arranque** (un nodo vivo cumple la propiedad hacia delante) y **paso**
(una selección compatible con la propiedad hacia delante se amplía conservándola).

## 7. El paso, en papel

- **Sale:** la propiedad hacia delante da en el paso `a−1` un nodo vivo `z` compatible con la selección; por
  `parentGap` algún padre de `s_a` conserva `z`, y como los owners de un nodo en su propio paso son solo él mismo, ese
  padre es `z`. Hay, pues, un candidato compatible. También sale que una entrada viva se sostiene en una sucesión de
  hijos enlazados hasta su owner, y que los ids fuerzan la coherencia entre pasos vecinos.
- **No sale:** conservar la propiedad hacia delante tras elegir. Cada testigo de un paso libre lo conserva algún padre,
  pero no necesariamente el mismo para todos ni uno compatible con toda la selección. Es la condición de tipo Helly en
  forma local, y las reglas de `Dead` solo dan un portador por entrada.

## 8. Perturbación: el paso no es estructural

Quitando parejas simétricas de owners al azar (nunca en el propio paso) y recalculando la clausura, sobre 1 de cada 4
nodos vivos:

| Perturbación (1 %) | Paso atascado con cadena | Nodo vivo sin cadena |
|---|---|---|
| parejas sin cadena común por los pins | 0 (no cambia los nodos vivos) | 0 |
| parejas con cadena común | `far2` 8, `far3` 38, `outsideR_a` 16, `outsideR_c` 30, `adv_seed8` 29, `entries_e` 26, semillas 20 y 34 | 0 a 12 por fórmula |
| cualquier pareja | idéntico a la fila anterior | idéntico |

El paso depende de las tablas de owners de los estados alcanzables, no solo de las reglas y los ids. Quitar parejas que
la semántica permite rompe el paso y hasta `LossInClosureD`.

## 9. Cierre semántico por empalme

Dos cadenas por un mismo nodo `y`, empalmadas en el paso de `y` (tramo inferior de una, superior de la otra):

| Estado | Empalmes válidos | Inválidos | Inválidos con asignación combinada inconsistente |
|---|---|---|---|
| guardado `g` | 27.828 | 19.130 | 19.130 |
| fijado `P` | 17.574 | 14.894 | 14.894 |

En las 17 fórmulas, **un empalme es cadena exactamente cuando la asignación de literales combinada es consistente**
(la dirección válido ⇒ consistente se apoya en FixAgree, medido y no demostrado). Las cadenas se comportan como caminos
enlazados del mapa con asignación consistente, y los owners no añaden restricciones propias al empalmar. Esto explica
la sensibilidad a la perturbación, pero no demuestra el paso: con esta caracterización, el paso dice que la clausura
local basta para decidir si una asignación parcial fijada por los pins se completa a lo largo del mapa. Es la misma
cuestión de tipo Helly en términos de asignaciones, confirmada aquí en fórmulas pequeñas.

## 10. Estado

| Pieza | Estado |
|---|---|
| `LossInClosure` (sobre `Unsupported`) | ❌ refutado (tres fórmulas de la tanda 2) |
| `Dead`: fuera de las cadenas y eliminado por el review | ✅ demostrado (`dead_off_chain`, `dead_gone`) |
| sin zombis y el filtro conserva exactamente los caminos por los pins | ✅ bajo `LossInClosureD` |
| clausura por punto fijo = review (nodos y entradas) | medido, exacto |
| construcción con comprobación hacia delante | medida, 0 atascos (406.929 nodos; forma general, 1,96 M recorridos) |
| paso en papel | parcial: el candidato existe; conservar la propiedad hacia delante, abierto |
| paso bajo perturbación | falla: depende de las tablas alcanzables |
| cierre semántico por empalme | medido sin excepciones |
| `LossInClosureD`, `PinnedCompletion`, `JoinCovered` | abiertos |

La cadena:

```
LossInClosureD (abierto)  ⟹  sin zombis  ⟹  el filtro conserva exactamente los caminos por los pins
LossInClosure (refutado)  ⟹  LossInClosureD
```

Siguiente, a elegir: medir la caracterización completa (un camino enlazado de nodos vivos es cadena si y solo si su
asignación es consistente), que separaría la parte de los owners de la parte combinatoria; o la infraestructura de Lean
para el paso (clausura booleana equivalente a `Dead`, para obtener testigos sin `Classical`).

Build: `lake build AbsSat` verde, 129 módulos, 0 `sorry`, `[propext, Quot.sound]`, Lean 4.33.1.

## Anexo: cómo se midió

Ejecutables compilados en el scratchpad (`lake env lean --root=<dir> -c`, objetos C de `AbsSat`, enlazado con
`leanc -O3`, toolchain 4.33.1 explícito), sin tocar el repositorio.

- **Búsqueda adversaria:** escaladores con semilla, aceptando mutaciones que no empeoran (y 1 de cada 25 que sí);
  `R` por rondas con tablas hash; zombis comprobados con búsqueda de cadena en cada récord.
- **Contraejemplo:** reproducción del review etapa a etapa (`cleanInvalid`, `reviewParents`, `reviewSons`) y de la
  pasada de hijos línea a línea.
- **Clausura sobre entradas:** punto fijo con conjuntos de nodos y entradas muertos, comparado con el estado filtrado.
- **Grupos de owners:** para cada nodo sin cadena, búsqueda de una variante por pin en posesión mutua con él y entre sí.
- **Construcción de cadenas:** sobre la parte viva; comprobación hacia delante en cada elección; forma general con
  elecciones al azar (3 recorridos contiguos y 2 en cualquier orden por nodo).
- **Perturbación:** eliminación simétrica por hash con semilla, con y sin cadena común (búsqueda de cadena por la pareja
  en el estado fijado, con caché).
- **Empalme:** hasta 6 cadenas al azar por nodo muestreado (1 de cada 5 en `g`, 1 de cada 10 nodos conservados en `P`);
  validez por posesión mutua de las parejas cruzadas; consistencia de la unión de lo que fijan los ids.
