# Demostración por construcción: caminos parciales `Φ_k`

## Síntesis

La idea es leer la máquina como una construcción paso a paso de **caminos parciales** por el mapa: `Φ_k`
son los caminos construidos hasta el paso `k`, y `Φ` en el último paso es el conjunto completo de
caminos.

Esa lectura **ya está demostrada, en las dos direcciones y sin hipótesis abiertas**
(`AbsSat/GraphPath/Model/PartialPaths.lean`):

> `Φ_k` son exactamente las soluciones de las cláusulas vistas hasta el paso `k`, y la fórmula es
> satisfacible si y solo si `Φ` no está vacío en el último paso.

Lo que **no** resuelve es la pregunta de la máquina. La máquina no calcula `Φ`: responde si la última
línea tiene estados. El problema abierto es exactamente este:

> **¿una última línea no vacía representa siempre algún camino completo?**

Para toda fórmula eso equivale a P = NP (v70, v76); el objetivo realista es demostrarlo para una clase.

Los niveles citados aquí son los de `docs/niveles_de_abstracción.md`.

---

## 1. Qué es `Φ_k` en el código

Una línea del conductor (nivel 3) es una lista de estados, uno por clave. Cada estado (nivel 2)
**representa** los caminos de sus cadenas con owners mutuos (lectura semántica, `Denot.lean`):

```lean
def denot (g : GPathM) (p : List NodeId) : Prop :=
  ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ p = pathOf sel g
```

`Φ_k` es la unión de lo que representan los estados de la línea `k`:

```lean
def lineAt (φ : Cnf) (k : Nat) : PureLine := pureSteps φ k (pureInit φ)

def Phi (line : PureLine) (p : List NodeId) : Prop := ∃ kv ∈ line, denot kv.2 p
```

El camino que nombra una asignación hasta el paso `n` es `assignPath φ a n`.

**Importante:** `Φ_k` no es un objeto que la máquina construya. La máquina guarda **estados fusionados**
con tablas de owners, de tamaño polinómico; `Φ_k` es lo que esos estados representan, y puede ser
exponencial.

## 2. Las dos inclusiones

### Toda solución parcial está en `Φ_k`

```lean
theorem assignPath_mem_Phi (φ) (hwf : WF φ) (k : Nat) (hk : (k : Int) < stepCount φ)
    (a : Assign) (hs : SatUpTo φ a k) :
    Phi (lineAt φ k) (assignPath φ a ((k : Int) + 1))               -- [propext, Quot.sound]
```

Sale de la conservación por prefijo (`pureSteps_carries_prefix`, `PrefixConservation.lean`): una
asignación que satisface las cláusulas vistas deja su rama en la línea como cadena sonora, y una cadena
sonora es una cadena con owners mutuos.

Consecuencia: **un camino parcial correcto nunca se pierde**. En particular, en el bloque de cláusulas
nunca es refutado por la propagación unitaria, porque su envío es válido y
`invalid_filterAll_of_UPConflict` diría lo contrario (se sigue directamente; no está enunciado aparte).

### Todo camino de `Φ_k` es una solución parcial

```lean
theorem Phi_sound (φ) (hwf : WF φ) (k : Int) (line) (hl : LineOk φ k line) (p) (hp : Phi line p) :
    ∃ kv ∈ line, ∃ sel, IsChain kv.2 sel ∧ PairwiseOwned kv.2 sel ∧ p = pathOf sel kv.2 ∧
      SatUpTo φ (decode sel) k                                       -- [propext, Quot.sound]
```

Sale de la decodificación por prefijo (`satUpTo_of_chain`, `PrefixDecode.lean`): toda cadena con owners
mutuos de un estado se lee como una asignación que satisface las cláusulas que ese estado ha visto. Las
líneas del conductor cumplen `LineOk` (`lineAt_ok`).

## 3. El último paso

```lean
theorem satisfiable_iff_Phi_nonempty (φ) (hwf : WF φ) :
    Satisfiable φ ↔ ∃ p, Phi (pureRun φ) p                           -- [propext, Quot.sound]
```

Sin `ClauseStepExact`, sin hipótesis de clase. **La construcción por caminos es correcta y completa.**

## 4. Dónde queda el hueco, dicho con exactitud

La máquina responde `is_satisfiable (run_pure φ)`, que es `pureRun φ ≠ []`
(`is_satisfiable_run_pure_iff`). Y:

```lean
theorem soundness_iff_nonempty_represents (φ) (hwf : WF φ) :
    (pureRun φ ≠ [] → Satisfiable φ) ↔ (pureRun φ ≠ [] → ∃ p, Phi (pureRun φ) p)
```

*La máquina es correcta si y solo si una última línea no vacía representa siempre algún camino completo.*
No es una reformulación cómoda: es una equivalencia demostrada.

Por estado, eso es **«válido ⇒ representa algún camino»**, es decir `isValid g ⇒ Inhabited g`
(`Inhabited g := ∃ p, denot g p`). Un estado válido que no representa ningún camino sería un **zombi**:
sus tablas tienen algo en cada paso, pero ninguna cadena las atraviesa enteras.

## 5. Por qué construir por caminos no cierra el hueco

La idea de partida era que, siguiendo **un** camino, no hay hueco de tipo Helly: un camino es por
definición una sola cadena. Eso es cierto **para caminos**, y es exactamente por lo que las dos inclusiones
del §2 salen.

Pero la máquina no sigue caminos:

- `sendTo` **fusiona** en un solo estado todas las ramas que llegan a la misma clave (nivel 3);
- dentro de un estado, `owns_required` garantiza un owner para **cada** requisito por separado, no una
  cadena con todos a la vez;
- lo que la máquina comprueba es `isValid` sobre las tablas fusionadas, no la existencia de un camino.

Seguir los caminos uno a uno es enumerar asignaciones. La máquina es polinómica precisamente porque no lo
hace, y por eso la pregunta «¿las tablas fusionadas todavía contienen un camino?» no sale gratis.

## 6. Cómo se conecta con lo demás

| Pieza | Qué aporta a «válido ⇒ representa un camino» |
|---|---|
| `ClauseStepExact` (`NodeInvariant.lean`) | **suficiente**: el filtro de cláusula conserva `SupportedS`; con ello todo nodo está en una cadena sonora y el estado está habitado (`Decision.lean`) |
| `FlipCore` (`ClauseFilter.lean`) | la única pieza de `ClauseStepExact` sin demostrar |
| `invalid_filterAll_of_UPConflict` (v94) | los estados que la propagación unitaria refuta no llegan a la línea: condición necesaria, no suficiente |
| `pureAdvance_drops_key_conflict` (v95) | las filas que contradicen la clave de un estado no se extienden |
| `pinned_support` (v95) | un valor que no convive con los pins en la tabla de owners desaparece |

Las tres últimas explican **qué zombis evita** la máquina. Ninguna garantiza que no quede ninguno.

## 7. Qué objetivo tiene sentido

Para una clase `C` de fórmulas, cualquiera de estos enunciados, en orden de fuerza:

```lean
-- exacto (equivale a la corrección de la máquina en C)
∀ φ ∈ C, pureRun φ ≠ [] → ∃ p, Phi (pureRun φ) p

-- suficiente, por pasos
∀ φ ∈ C, ClauseStepExact φ
```

El segundo tiene la ventaja de ser **local** (un filtro de cláusula cada vez) y ya está conectado con toda
la máquina (`run_pure_decides`). El primero es el que realmente se necesita y deja abierta la posibilidad
de demostrarlo sin pasar por `ClauseStepExact`.

## Resumen

| | Estado |
|---|---|
| `Φ_k` = soluciones de las cláusulas vistas | ✅ `assignPath_mem_Phi`, `Phi_sound` |
| satisfacible ⇔ `Φ` no vacío en el último paso | ✅ `satisfiable_iff_Phi_nonempty` |
| corrección de la máquina ⇔ última línea no vacía representa un camino | ✅ `soundness_iff_nonempty_represents` |
| una última línea no vacía representa un camino | **abierto** (para toda fórmula, P = NP) |
