# Verificación para el Autor v100: una regla de review contra los owners obsoletos, medida antes de 2d

Ricardo, soy Claude (Opus 5). Tras v99 quedaba abierto `IdClosureSeparator`. En este tramo pasaron
cuatro cosas: revisé los dos commits de Gemini, corregí el alcance de lo que v99 presentó como
reducción, exploré la vía 2c (generalizar `Agree`) y, a raíz de lo que 2c mostró, probé la regla que
sugeriste: limpiar en el review los owners obsoletos. Este informe es sobre todo sobre esa regla.

Resumen: la regla es correcta (nunca quita un nodo con camino), deja los owners exactos por parejas y no
cambia ninguna decisión de la máquina, pero **no reduce las rondas de `R`**, que es lo que hace difícil
`LossInClosure`. No la recomiendo como cambio de la máquina.

Nada de lo medido aquí toca el repositorio: la regla vive en ejecutables compilados en el scratchpad. El
build de `AbsSat` sigue verde (128 módulos), sin `sorry`.

---

## 1. Antes: los commits de Gemini y una corrección a v99

- `f6d58f4` (niveles del cierre por ids) y `51ca29d` (owners con ruptura) llevan ahora tu identidad de
  investigador. De `IdClosureLevels.lean` se conserva `IdClosureAt` con sus lemas de monotonía y de
  enlace con `IdClosure`; se quitaron un duplicado y un lema redundante, y se fijaron los axiomas. Se
  eliminó `BreakOwners.lean`, que solo envolvía un constructor (`ee42acd`).
- **Corrección a v99.** La regla de paso de `IdClosure` acepta un conjunto vacío de owners globales,
  igual que `Unsupported.noSupport`. Por eso el cierre por la regla de no soporte (`UnsupportedNS`) está
  dentro del cierre por ids (`idClosure_of_unsupportedNS`), que a su vez está dentro de `R`. Como todo `R`
  medido usa solo esa regla, **`IdClosureSeparator` es `LossInClosure` dicho de otra forma**
  (`idClosureSeparator_of_nsSeparator`), no una obligación más débil. v99 lo presentaba como reducción;
  lo que sí aportan los ids es el contenido de los separadores no vacíos, de profundidad ≤ 2 en lo medido.

## 2. La vía 2c: `FixAgree`

`Agree` (v99) dice que los owners de un nodo llevan, en los pasos de literal de una variable fijada por su
id, el valor fijado. La generalización natural:

> **`FixAgree`**: lo que fija el id de un nodo (nodo de mapa propio y del padre) y lo que fija el id de
> cada uno de sus owners coinciden en toda variable común, en cualquier paso.

| Conjunto | Pares comprobados | Fallos |
|---|---|---|
| `near`, `far`, `near2`, `far2`, `far3`, `far4` | 1.268.218 | 0 |
| aleatorias (semillas 1, 2, 3; estados guardados y filtrados) | 3.928.688 | 0 |

Se puede demostrar como `LitInv`. Con `FixAgree`, un owner `q` de `x` en el paso `j` es una «forma» del
mapa (nodo y padre) compatible con lo que fija `x`. De ahí sale un **separador de mapa**: un paso `j` en
el que toda forma compatible con `x` contradice un pin. Cubre la mayoría de nodos sin camino, pero no
todos:

| Fórmula | Sin camino, separador de mapa | Separador de owners, no de mapa | Solo nivel 2 |
|---|---|---|---|
| `near` | 920 | 20 | 0 |
| `far` | 1.430 | 36 | 0 |
| `near2` | 2.614 | 18 | 0 |
| `far2` | 4.506 | 0 | 18 |
| `far3` | 9.899 | 324 | 12 |
| `far4` | 13.125 | 1.016 | 6 |
| aleatorias 1 / 2 / 3 | 17.795 / 14.098 / 17.281 | 40 / 46 / 69 | 0 |

Lo que falta depende de qué owners quedan en `x`, no del mapa. Y el estado pineado (antes del review)
tiene **owners obsoletos**: entradas de `owners(n)` que no comparten camino con `n`, en nodos con camino y
sin él. Por eso un argumento estático de consistencia por parejas sobre ese estado no funciona, y de ahí
la pregunta de si el review debería limpiarlos.

## 3. La regla sugerida

### 3.1 Definición

Tras cada review, sobre una instantánea del estado, se quita la entrada `w` de `owners(n)` (con `w` en
otro paso que `n`) si:

1. `w` no es un nodo, o
2. **simetría**: `n ∉ owners(w)`, o
3. **soporte por parejas**: hay un paso `k'` (distinto del de `n` y del de `w`) sin ningún owner vivo `q`
   de `n` en `k'` con `w ∈ owners(q)` y `n ∈ owners(q)`.

Después se re-enlaza cada nodo con sus owners nuevos y se repite review + regla hasta que la medida no
baja. Coste polinómico: por entrada, pasos × owners por paso.

**Por qué es correcta.** Si `n` y `w` están en una cadena completa `c`, los caminos completos forman un
`Fabric` (`Fabric_chains`): `w` posee a `n`, y el nodo de `c` en `k'` posee a ambos y es global. Ninguna
entrada entre nodos de una misma cadena se quita, así que no se pierde ningún camino completo.

### 3.2 Qué limpia

Entradas obsoletas (estados 1–3) en los estados guardados de entrada y tras el review actual:

| Fórmula | Entrada: obsoletas / total | Tras review: no simétricas | Tras review: sin soporte | Total tras review |
|---|---|---|---|---|
| `near` | 0 / 70.352 | 0 | 0 | 104.538 |
| `far2` | 99 / 91.379 | 315 | 0 | 175.627 |
| `far3` | 768 / 310.210 | 1.368 | 408 | 614.480 |
| `far4` | 846 / 633.172 | 1.278 | 540 | 1.259.722 |
| aleatorias 1 / 2 | 0 / 978.752 · 0 / 806.942 | 0 | 0 | 974.092 · 811.716 |

Entre un 0,1 % y un 0,2 %, y solo en las fórmulas con cláusulas correlacionadas no consecutivas. En las
aleatorias el review actual ya deja los owners sin entradas obsoletas.

### 3.3 Qué no cambia

- **Nodos**: la regla no quita ningún nodo en ningún envío (tampoco uno con camino), y la validez de cada
  envío es la misma con y sin regla.
- **Conductor**: con la regla dentro de `filterAll` en toda la ejecución, las líneas coinciden paso a paso
  en claves, número de nodos y número de owners globales (22, 22, 30 y 38 pasos en `near2`, `far2`,
  `far3`, `far4`), y las entradas de los estados guardados quedan sin obsoletas.

### 3.4 Qué consigue: owners exactos por parejas

Con la regla, en `near` y `far2`, **toda** entrada de owners (104.538 y 175.312) comparte un camino
completo con su nodo, y también todas las ternas de owners mutuos muestreadas (30.985 y 47.485, una de
cada 40). Sin la regla, `far2`–`far4` sí tienen entradas sin camino común.

### 3.5 Lo que no consigue: las rondas de `R`

`R` es el cierre de eliminación del estado pineado; su ronda ≥ 1 es lo que ni S1 en un nivel ni el
separador de mapa explican. Mismo conductor, con y sin regla:

| Fórmula | Envíos válidos (ronda máx. 0 / 1 / 2) | Nodos de `R` en ronda ≥ 1 | Borrados por el review fuera de `R` |
|---|---|---|---|
| `near2` sin / con regla | 169 / 12 / 0 · 169 / 12 / 0 | 66 · 66 | 0 · 0 |
| `far2` sin / con regla | 230 / 6 / 6 · 230 / 6 / 6 | 90 · 90 | 0 · 0 |
| `far3` sin / con regla | 361 / 4 / 4 · 361 / 4 / 4 | 220 · 220 | 0 · 0 |
| `far4` sin / con regla | 440 / 2 / 2 · 440 / 2 / 2 | 194 · 194 | 0 · 0 |

Idénticas. Los nodos que necesitan una segunda ronda no dependen de owners obsoletos.

## 4. Por qué una regla por parejas no llega

En `far2`, el nodo `x = (10,0)` (`f = 0`) con los pins `a = b = c = 1` conserva, en cada paso de pin,
algún owner global que no contradice el pin (el perfil por pasos de §2 lo muestra: en los pasos de pin
queda al menos un owner no contradictorio). Lo que no existe es un camino por `x` que pase **a la vez**
por los tres pins: exigiría `u = 1` y rompería `B`. Es una configuración de tipo Helly: cada restricción
por separado deja sitio, el conjunto no. Que la regla, que deja los owners exactos por parejas, no mueva
ninguna ronda (§3.5) es la medida de que el problema no está en las parejas. La tabla de owners solo guarda parejas; tras fijar los
pins, detectarlo es buscar un camino por `x` y todos los pins, que es exactamente lo que el review consigue
con su segunda ronda de eliminación.

Una regla que eliminara esos nodos en la ronda 0 tendría que mirar conjuntos de `x` más los tres pins, no
parejas.

## 5. Valoración

| | |
|---|---|
| Correcta respecto a los caminos | sí (argumento de §3.1; 0 nodos con camino perdidos) |
| Cambia las decisiones | no (mismas líneas, misma validez) |
| Limpia owners obsoletos | sí, 0,1–0,2 % en `far2`–`far4`; 0 en aleatorias |
| Simplifica `LossInClosure` | **no**: mismas rondas de `R` |
| Coste de incorporarla a la máquina | revisar todo lo que habla de `review`: `Fuel`, `FOk_review`, `ParentInv`, `LitInv`, `idDies`, soundness/completeness y la banda diferencial con el ejecutable |

**Recomendación:** no incorporarla a `SatMachinePure`. La exactitud por parejas **no es invariante de la
máquina actual** (falla en `far2`–`far4`), así que tampoco puede usarse como hipótesis gratuita; y aunque
lo fuera, no toca el núcleo. Lo que sí queda de este tramo: `FixAgree` (demostrable) y el separador de
mapa como parte sintáctica de los separadores.

## 6. Siguiente: 2d

El residuo está en las configuraciones de pins consistentes por parejas e inconsistentes en conjunto. La
búsqueda adversaria debería apuntar ahí:

- **Objetivos**, de más a menos grave: un nodo sin camino fuera de `R` (`LossInClosure` falso); ronda de
  `R` ≥ 3; separador de profundidad ≥ 3; muchos nodos sin separador de mapa.
- **Generadores**: la familia `far-k` generalizada (cadenas de implicaciones con rellenos entre medias, de
  distinta longitud y ramificación); fórmulas intercaladas aleatorias; mutación local guiada por la ronda
  máxima de `R` partiendo de `far4`.
- Todo sobre `SatMachinePure` sin la regla.

## 7. Estado

| Pieza | Estado |
|---|---|
| `ParentInv`, `LitInv`, S2 (`idDies`) | ✅ demostrados |
| cierre por ids ⊆ `R`; cierre por no soporte ⊆ cierre por ids | ✅ demostrados |
| `IdClosureSeparator` | equivalente a `LossInClosure` por la regla de no soporte; abierto |
| `FixAgree` | medido, 0 fallos en 5.196.906 pares; no demostrado |
| regla de owners obsoletos | medida: correcta, no cambia decisiones ni rondas; no incorporada |
| `LossInClosure`, `PinnedCompletion`, `JoinCovered` | abiertos |

Build: `lake build AbsSat` verde, 128 módulos, 0 `sorry`.

## Anexo: cómo se midió

Ejecutables compilados en el scratchpad (`lake env lean --root=<dir> -c`, objetos C de `AbsSat`, enlazado
con `leanc -O3`), sin tocar el repositorio.

- **`FixAgree`:** en cada estado guardado válido y en cada `filterAll` válido, para cada entrada `(n, w)`
  cuyos ids fijan alguna variable común, comprobación de que no fijan valores distintos.
- **Separador de mapa:** formas de un paso = nodos de mapa del paso con un padre de mapa que los tenga como
  hijo (solo el nodo en el paso 0); fijaciones de la forma frente a las de `x` y a los pins.
- **Regla:** estados 1–3 de §3.1 con tablas hash de owners; `review` + regla iterados con 60 unidades de
  combustible; pérdida de nodos comparada con `onChain` en el estado revisado sin regla.
- **Exactitud:** búsqueda de un camino completo forzado por `n` y `w` (y por ternas), con presupuesto de
  50.000 expansiones, nunca agotado.
- **Rondas de `R`:** conductor duplicado (`advanceR`) con `filterAll` o con review + regla; `R` por rondas
  sobre el estado pineado de cada envío válido.
- **Fórmulas:** `near`, `near2`, `far`, `far2`, `far3`, `far4` escritas a mano (v99); aleatorias de
  `DiffTest.gen_cnf`, 40 casos de 3 a 5 variables por semilla.
