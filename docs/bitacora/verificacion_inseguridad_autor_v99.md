# Verificación para el Autor v99: S2 demostrado, S1 refutado en un nivel y reformulado sin profundidad

Ricardo, soy Claude (Opus 5). En v98 la inducción «sin zombis» dependía de `LossInClosure`, y las
mediciones apuntaban a un lema sobre lo que codifican los ids. En este tramo ese lema se partió en dos:
S2 está demostrado en Lean; S1, en su forma de un nivel, es falso, y lo he reformulado sin profundidad
fija. Esa reformulación se cumple en todo lo medido.

Todo lo de Lean está en el build de `AbsSat` (127 módulos), sin `sorry`, en `[propext, Quot.sound]`,
sobre las definiciones actuales. Las mediciones son sobre `SatMachinePure`, con ejecutables compilados.

---

## 1. La reducción por ids (`IdSeparator.lean`)

El id de un nodo es su nodo de mapa más el de su padre, y un nodo de mapa fija valores de variables: uno
de valor, su variable; uno de negación, la del valor que requiere; una fila de cláusula, las de sus
literales. `IdContradicts φ reqs w`: algún valor que fija el id de `w` contradice un pin.

- **S1** (`IdSeparator`): todo nodo del estado pineado está en un camino completo, o tiene un paso en el
  que todos sus owners globales tienen un id que contradice un pin.
- **S2** (`IdDies`): todo owner global cuyo id contradice un pin está en `R`.
- `noZombieOutside_of_separator`, `lossInClosure_of_idSeparator`: con S1 y S2, `LossInClosure`.

Medido (semillas 1001, 7777, 31337, 90210, filtros de cláusula válidos): S1, 41.501 de 41.501 nodos sin
camino con separador y 0 de 97.548 con camino; S2, 39.655 de 39.655 eliminados en la ronda 0.

## 2. S2 demostrado

### 2.1 Dos invariantes nuevas

Antes de probar S2 medí qué hacía falta (9.885 estados guardados y filtrados, 0 fallos):

| Invariante | Comprobaciones |
|---|---|
| P1: owners en el paso anterior tienen el id del padre | 215.324 |
| P2: owners en los pasos de los requisitos del padre son esos requisitos | 265.951 |
| P3: owners en el otro paso de una variable fijada llevan el mismo valor | 679.824 |

Las tres están ahora demostradas para todo estado alcanzable:

- **`ParentOwners.ParentInv_reachable`** — `po` (P1), `ps` (el padre está un paso por debajo), `kp` (los
  owners globales de un estado con clave `p` cumplen los requisitos de `p`), `pr` (P2) y `rp` (un
  requisito propio en el paso del padre es el padre). Sale de `addNode`: los owners globales del nodo
  nuevo tienen la clave en el paso de arriba (`TopKey`) y los requisitos fijados por el filtro previo.
- **`LitOwners.LitInv_reachable`** (P3, sin depender del mapa) — para un literal fijado por el nodo de
  mapa propio o del padre, `own`: un owner que requiere algo en ese paso requiere ese literal; `twin`: un
  owner en el paso del requisito del literal es ese requisito. Sale de los hechos de punto fijo del
  filtro anterior (`ReqFiltered`, `OwnedCompatible`, `GN`, validez de nodos, owners dentro de los owners
  globales).

### 2.2 La prueba (`IdDiesProof.lean`)

El núcleo es `Agree n v b`: los owners de `n` en el paso de valor `2v` tienen índice `b`, y en el de
negación `2v + 1`, índice `1 − b`. Si el id de `n` fija `v = b`, `n` cumple `Agree`:

| Origen del literal | Paso del literal | Otro paso de la variable |
|---|---|---|
| requisito del nodo propio o del padre | `ReqFiltered` / `pr` | `LitInv` |
| nodo de valor propio | `OOS` | `OwnedCompatible` |
| nodo de valor del padre | `po` | `OOS` + `rp` |

Un pin de la misma variable con el otro valor exige un índice que `Agree` excluye. Los owners globales
del estado pineado en el paso del pin son el pin mismo, así que el nodo no tiene ninguno ahí y cae por
`Unsupported.noSupport`.

- **`idDies`**: S2 para todo estado alcanzable de una fórmula bien formada y todo envío con
  `d.step = g.current_step`. La distinción de requisitos por paso sale de `reqOfCnf_functional`.
- `LossInClosure` y la reducción llevan ahora esa hipótesis sobre `d`: sin ella S2 sería falso, porque
  un pin por encima del paso actual no elimina nada. El conductor la cumple siempre.

## 3. S1 en un nivel es falso

El contraejemplo (`a, b, u, c, f` son las variables 1, 2, 3, 4 y 6):

```
p cnf 8 5
-1 -2 3 0     A:  a ∧ b → u
7 8 5 0       relleno
-3 -4 6 0     B:  u ∧ c → f
-7 8 5 0      relleno
1 2 4 0       D:  a ∨ b ∨ c
```

Al fijar `a = b = c = 1`, el nodo de valor `f = 0` no está en ningún camino por los pins (exigiría `u = 1`
y rompería `B`), pero no tiene separador por ids: `A` y `B` no son consecutivas, así que ningún id fija a
la vez sus variables, y la clave del estado (una fila del último relleno) no las toca.

| Fórmula | Nodos sin camino | Sin separador de un nivel | Fuera de `R` | Ronda máx. de `R` |
|---|---|---|---|---|
| `near2` (`A` y `B` consecutivas) | 2.632 | 0 | 0 | 1 |
| `far2` | 4.524 | **18** | 0 | **2** |
| `far3` (cadena más larga, separada) | 10.235 | **12** | 0 | 2 |
| `far4` (aún más larga) | 14.147 | **6** | 0 | 2 |

`R` sigue eliminando todo lo que no tiene camino, pero necesita una ronda 2, que en las fórmulas
aleatorias no había aparecido.

## 4. S1 sin profundidad fija (`IdClosureSep.lean`)

Medí S1 en dos niveles (un paso donde cada owner contradice un pin o tiene él mismo un separador por
ids), y después busqué profundidad 3 con fórmulas aleatorias de cláusulas intercaladas entre rellenos de
variables nuevas:

| Fórmulas | Nodos sin camino | Nivel 1 | Nivel 2 | Nivel ≥ 3 | Sin separador | Fuera de `R` |
|---|---|---|---|---|---|---|
| aleatorias (4 semillas) | 41.501 | 41.501 | 0 | 0 | 0 | 0 |
| `far2` / `far3` / `far4` | 28.906 | 28.870 | 36 | 0 | 0 | 0 |
| **intercaladas (30)** | **457.928** | **457.886** | **42** | **0** | **0** | **0** |

Ningún nodo en un camino por los pins tiene separador de ningún nivel. En lugar de fijar dos niveles, lo
formalicé sin profundidad:

- **`IdClosure`**: el cierre por ids. Base: el id contradice un pin. Paso: un paso en que todos los owners
  globales están en el cierre.
- **`idClosure_unsupported`**: todo owner global del cierre por ids está en `R` (inducción con `idDies`
  como base).
- **`IdClosureSeparator`**: todo nodo está en un camino por los pins o tiene un paso con todos sus
  owners globales en el cierre. `idClosureSeparator_of_idSeparator`: el S1 de un nivel es su primer nivel.
- **`noZombie_of_idClosureSeparator`**: sin zombis en todo estado alcanzable válido, solo con
  `IdClosureSeparator`.

## 5. Estado

| Pieza | Estado |
|---|---|
| `ParentInv`, `LitInv` | ✅ demostrados |
| **S2 (`idDies`)** | ✅ **demostrado** |
| S1 en un nivel | ❌ refutado (`far2`) |
| cierre por ids ⊆ `R` | ✅ demostrado |
| **`IdClosureSeparator`** | medido, profundidad ≤ 2 en 528.335 nodos sin camino; abierto |
| sin zombis y el filtro conserva exactamente los caminos por los pins | ✅ bajo `IdClosureSeparator` |
| `PinnedCompletion`, `JoinCovered` | abiertos |

La cadena:

```
IdClosureSeparator (abierto)  +  idDies (demostrado)
      ⟹  LossInClosure  ⟹  sin zombis  ⟹  el filtro conserva exactamente los caminos por los pins
```

Build: `lake build AbsSat` verde, 127 módulos, 0 `sorry`, `[propext, Quot.sound]`.

## Anexo: cómo se midió

Ejecutables compilados en el scratchpad (`lake env lean --root=<dir> -c`, objetos C de `AbsSat` con
`leanc -c`, enlazado con `leanc`), sin tocar el repositorio.

- **S1 y S2:** para cada filtro de cláusula válido, separador por ids de cada nodo (todos los owners
  globales de un paso con id contradictorio) y ronda de `R` de cada owner contradictorio.
- **P1–P3:** comprobación directa en todos los estados guardados y filtrados.
- **Contraejemplos:** ficheros DIMACS escritos a mano (`near2`, `far2`, `far3`, `far4`) leídos por el
  conductor.
- **Niveles:** conjuntos de nodos con separador de nivel `≤ i`, `i = 1..5`, calculados en cascada.
- **Fórmulas intercaladas:** 4 a 6 variables base con `nb` a `2·nb` cláusulas aleatorias; en cada hueco,
  0 o 1 cláusula sobre 4 variables nuevas con un literal positivo (satisfacibles por construcción).
