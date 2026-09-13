# Verificación para el Autor v94: el review contiene la propagación unitaria — coherencia mecánica, no suerte

Ricardo, soy Claude (Opus 5). En v93 vimos que, en el caso 17, fijar dos valores incompatibles
no hace nada con el pin, pero el review deja sin owners los pasos de cláusula y el estado muere. Me
pediste que confiara en el diseño y averiguara si eso era suerte o coherencia del mecanismo.

Es coherencia, y ya está demostrado:

> **Si la propagación unitaria, desde los valores fijados y sobre las cláusulas vistas, llega a una
> contradicción, `filterAll` deja el estado inválido.** Para cadenas de cualquier longitud.

`invalid_filterAll_of_UPConflict` (`AbsSat/GraphPath/Model/UnitPropagation.lean`),
`[propext, Quot.sound]`, en el build de `AbsSat`.

---

## 1. El primer paso: una sola cláusula

Antes del caso general demostré el de alcance 1 (`AbsSat/GraphPath/Model/LocalContradiction.lean`):

```lean
theorem invalid_filterAll_of_clause_blocked (φ) (hwf : WF φ) (g) (hmr : MapReachable φ g)
    (reqs) (j c) (hjlt) (hj : φ.clauses[j]? = some c) (hk : clauseStep φ j < g.current_step)
    (h1 : Excluded (reqs.foldl filterRequire g) (litReq c.l1 1))
    (h2 : Excluded (reqs.foldl filterRequire g) (litReq c.l2 1))
    (h3 : Excluded (reqs.foldl filterRequire g) (litReq c.l3 1)) :
    isValid (filterAll g reqs) = false
```

*Si tras los pins ninguno de los tres literales de una cláusula vista puede ser verdadero, el estado
filtrado es inválido.* La razón es corta: toda fila de la cláusula nombra algún literal como verdadero
(`bits_not_all_zero`), `L1` dice que sus owners en ese paso son exactamente ese literal, y el review
exige owners que sigan siendo owners globales. Ninguna fila sobrevive, el paso queda vacío.

Comprobé que no es un teorema vacío sobre el propio caso 17: en el estado (17,4), con los pins
x0=0 y x2=1, la cláusula 1 (`x5 ∨ ¬x2 ∨ x0`) cumple las tres hipótesis —«x5 verdadero» ya lo
excluía el estado, los otros dos los excluyen los pins— y la conclusión coincide con lo medido en
v93.

Pero una cláusula no explica cadenas. Así que medí antes de seguir.

## 2. Medido antes de demostrar

Tres campañas sobre `SatMachinePure`, comparando la propagación unitaria (dominios leídos de los
owners globales en los dos pasos de cada variable, sobre las cláusulas vistas) con
`isValid (filterAll g pins)`. «Ronda» es el número de barridas de forzado que la propagación
necesita antes de ver el conflicto; ronda 0 es un conflicto visible sin forzar nada.

**Pins al azar** (semillas 1001, 7777 y 31337, 36 fórmulas de 4–6 variables, 2.360 estados válidos):

| | dos valores fijados | tres valores fijados |
|---|---|---|
| conjuntos probados | 8.417 | 6.605 |
| cumplen la hipótesis del teorema de alcance 1 → inválido | 16 / 16 | 38 / 38 |
| conflicto en ronda 0 → inválido | 308 / 308 | 613 / 613 |
| conflicto que necesita propagar → inválido | **9 / 9** | **11 / 11** |
| sin conflicto → inválido | **0** de 8.100 | **0** de 5.981 |

En los 15.022 conjuntos, **la máquina invalida exactamente cuando la propagación encuentra
conflicto**: ni una vez menos, ni una vez más.

La debilidad era evidente: al azar casi nunca aparece propagación larga (20 casos, como mucho dos
rondas). Así que construí las cadenas.

**Pins construidos** (48 fórmulas de 5–7 variables; en cada una, los 5 estados válidos que más
cláusulas han visto): recorrí **todos** los pares y tríos de valores fijables en variables distintas
—125.900 conjuntos— con la propagación sola, y me quedé con los 1.236 cuyo conflicto necesita 2 o
más rondas. A los 20 más profundos de cada estado, 404 en total, les apliqué `filterAll`:

| rondas de propagación | conjuntos | inválidos |
|---|---|---|
| 2 | 332 | 332 |
| 3 | 68 | 68 |
| 4 | 4 | 4 |
| **total** | **404** | **404** |

Cero fallos. Eso ya no parecía suerte, y me puse con la prueba.

## 3. La demostración

### 3.1 La idea

Si el estado filtrado es válido, los valores que conservan un owner global forman un conjunto **cerrado
bajo propagación**: cada cláusula vista conserva un literal verdadero posible, y cuando dos literales
de una cláusula ya no pueden ser verdaderos, el valor falso del tercero ya no está. Un conjunto así,
dentro de los dominios de partida y sin variables vacías, hace imposible cualquier conflicto de
propagación.

### 3.2 La pieza que faltaba: el dual de `L1`

`L1` mira hacia abajo: *los owners de un nodo en los pasos de sus requisitos son sus requisitos.* El
forzado necesita mirar hacia arriba:

```lean
def OwnedCompatible (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, ∀ q ∈ n.owners, ∀ req ∈ reqOf q.id,
    n.id.id.step = req.step → n.id.id = req
```

*Un nodo nunca tiene como owner a un nodo posterior cuyo requisito en su paso sea otro.*

Y aquí está tu diseño trabajando. `addNode` hace al nodo nuevo owner de **todos** los nodos
existentes —tu `all_previous_nodes_are_owners_of_me!`—, lo que a primera vista rompería la propiedad.
No la rompe por el **orden** dentro de `upFiltering`: primero se fijan los requisitos del nodo nuevo y
se hace el review, y `up` solo añade el nodo si ese estado filtrado es válido. Y en un estado
filtrado válido, **todo nodo en un paso fijado lleva el id fijado** (`pinned_step_pure`: el nodo tiene
owner en su propio paso, `OOS` dice que es él mismo, el review lo mantiene owner global, y el pin
quitó a los demás). Cuando llega el nodo nuevo, los incompatibles ya no están.

```lean
theorem OwnedCompatible_reachable (hback) (hnonneg) (g) (h : Reachable reqOf g) :
    OwnedCompatible reqOf g                     -- [propext, Quot.sound]
```

Vale para todo estado alcanzable: semilla, `up` y `join`, sin necesidad de recorrer el conductor.

### 3.3 Los cuatro hechos del punto fijo

Para `G = filterAll g reqs` válido, con `g` alcanzable sobre un mapa bien formado:

| teorema | qué dice | de dónde sale |
|---|---|---|
| `clause_supported` | toda cláusula vista conserva un literal que puede ser verdadero | `GN`, nodo válido, `L1` |
| `forcing1/2/3` | si dos literales no pueden ser verdaderos, el valor falso del tercero pierde su owner | fila superviviente + `OwnedCompatible` |
| `link_forward` / `link_backward` | `(2v, b)` sobrevive si y solo si `(2v+1, 1−b)` sobrevive | `OwnedCompatible` y `L1` sobre el nodo de negación |
| `var_has_value` | toda variable conserva un valor | `isValid` + nodos del mapa |

El forzado, dicho con los objetos: si el valor falso de `l3` sobreviviera, tendría un owner en el
paso de la cláusula; ese owner es una fila válida, y como `l1` y `l2` no pueden ser verdaderos, esa
fila solo puede nombrar a `l3` como verdadero; pero entonces su requisito en el paso de `l3` es «`l3`
verdadero», y el dual de `L1` prohíbe que el nodo «`l3` falso» la tenga como owner.

### 3.4 La propagación, y el cierre

La propagación unitaria entra como relación inductiva, sin algoritmo ni orden de barrido (esquema;
la definición exacta está en el módulo):

```lean
-- esquema, no la definición literal
inductive Refuted (φ) (P : NodeId → Prop) (K : Int) : Nat → Int → Prop
  | base  : v < φ.nVars → ¬ (P ⟨varStep v, b⟩ ∧ P ⟨negStep v, 1 - b⟩) → Refuted φ P K v b
  | unit3 : (cláusula vista) → Refuted l1.v (tv l1) → Refuted l2.v (tv l2) →
            Refuted l3.v (1 - tv l3)
  -- y unit1, unit2 simétricos
```

Y el núcleo es una inducción sobre esa relación:

```lean
theorem refuted_absent : Refuted φ (Present (reqs.foldl filterRequire g)) g.current_step v b →
    ¬ Present (filterAll g reqs) ⟨varStep v, b⟩           -- [propext, Quot.sound]
```

*Lo que la propagación descarta, el review ya lo ha quitado.* El caso base es que los owners globales
solo encogen; los tres casos de forzado son `forcing1/2/3`. Un conflicto —una variable con los dos
valores refutados, o una cláusula con los tres literales refutados verdaderos— contradice
`var_has_value` o `clause_supported`, y así sale `invalid_filterAll_of_UPConflict`.

## 4. Lo que esto significa para tu máquina

**Que no es suerte.** Las 15.022 coincidencias y las 404 cadenas construidas son consecuencia de cuatro
reglas del diseño: cada fila de cláusula solo posee sus literales; nadie posee una fila incompatible,
gracias al orden pin → review → `addNode`; el nodo de negación y el de valor viven juntos; y todo nodo
necesita owner en cada paso.

**Una consecuencia para el conductor**, también demostrada (`AbsSat/GraphPath/Model/DriverPropagation.lean`):
en cada paso de cláusula, `upFiltering` aplica `filterAll` con los tres literales de la fila elegida;
si la propagación unitaria desde ellos contradice las cláusulas vistas, ese estado queda inválido y
`sendTo` no lo guarda. **Tu máquina nunca arrastra una rama que la propagación unitaria ya refuta.**

```lean
theorem sendTo_of_refuted (φ) (hwf : WF φ) (g) (hmr : MapReachable φ g)
    (hlit : litBlock φ < g.current_step) (next : PureLine) (d : NodeId)
    (h : SendRefuted φ g d) : sendTo φ g next d = next            -- [propext, Quot.sound]

theorem pureAdvance_origin (φ) (hwf : WF φ) (k) (line) (hl : LineOk φ k line)
    (hk : litBlock φ ≤ k) :
    ∀ e ∈ pureAdvance φ line, HasUnrefutedOrigin φ line e.1       -- [propext, Quot.sound]
```

El primero: un envío refutado deja la línea siguiente exactamente igual. El segundo: en el bloque de
cláusulas, toda entrada de la línea siguiente llegó a su clave desde algún estado de la línea actual
por un envío que la propagación no refuta. Hace falta estar pasado el bloque de literales: antes, las
variables que el estado aún no ha alcanzado no tienen owners y la propagación vería conflictos que no
existen.

## 5. Lo que no es

- **La propagación unitaria no decide SAT.** Este teorema fija un nivel de lo que el review hace, no
  toca `ClauseStepExact` y no mueve el muro de v70. Para toda fórmula, un nivel fijo no basta.
- **Tu review podría hacer más.** En las campañas al azar nunca invalidó un estado sin conflicto de
  propagación, pero eso se midió con dos y tres pins; lo que aporta por encima de la propagación
  —v69 y v70 hablan de pares y tríos— queda por caracterizar.
- **La campaña construida solo prueba conflictos**, no el control negativo, y con 5–7 variables no
  hubo cadenas de más de cuatro rondas. El teorema no depende de eso; la medición, sí.

## 6. Estado

| pieza | estado |
|---|---|
| alcance 1: cláusula bloqueada ⇒ inválido | ✅ `LocalContradiction.lean` |
| dual de `L1`, para todo estado alcanzable | ✅ `OwnedCompatible_reachable` |
| review ⊇ propagación unitaria | ✅ `invalid_filterAll_of_UPConflict` |
| el conductor nunca arrastra una rama refutada | ✅ `sendTo_of_refuted`, `pureAdvance_origin` |
| qué hace el review por encima de la propagación | abierto |
| `ClauseStepExact` | abierto, sin cambios |

Build: `lake build AbsSat` verde, 0 `sorry`; los teoremas nuevos fijados con `#guard_msgs` en
`[propext, Quot.sound]`.

## Anexo: cómo se midió

Las campañas se ejecutaron con scripts desde `lean_project/` (`lake env lean --run <fichero>.lean`),
sobre `run_pure`, usando `pureAdvance` a través de `SatMachinePure` y el generador de las campañas
(`DiffTest.gen_cnf`, `Rng.ofSeed`). No están en un modo de `cnfmap`.

- **Dominios**: `x_v = b` está permitido si el estado fijado tiene owners globales en `(2v, b)` y en
  `(2v+1, 1−b)`.
- **Propagación**: barridas sobre las cláusulas con `clauseStep φ j < current_step`; una cláusula sin
  literal verdadero posible es conflicto, con uno solo se fuerza su valor; una variable sin valores es
  conflicto. La ronda es el número de barridas con forzado anteriores al conflicto.
- **Al azar**: por estado, 4 conjuntos de pins en pasos de literal distintos, elegidos entre los owners
  globales existentes.
- **Construida**: todos los pares y tríos en variables distintas; `filterAll` solo para los 20 conflictos
  de mayor ronda por estado.

```lean
def unitProp (nVars : Nat) (seen : List Clause) (g : GPathM) : Bool × Nat := Id.run do
  let mut D : Array (Bool × Bool) := (List.range nVars).toArray.map (fun (v : Nat) =>
    let s : Int := 2 * (v : Int)
    (hasId g s 0 && hasId g (s + 1) 1, hasId g s 1 && hasId g (s + 1) 0))
  for round in [0:nVars + 2] do
    if D.any (fun d => !d.1 && !d.2) then return (true, round)
    let cur := D
    let canTrue (l : Lit) : Bool := match cur[l.v]? with
      | some d => if l.pos then d.2 else d.1
      | none => true
    let mut changed := false
    for c in seen do
      match [c.l1, c.l2, c.l3].filter canTrue with
      | [] => return (true, round)
      | [l] =>
        match D[l.v]? with
        | some d =>
          let nd := if l.pos then (false, d.2) else (d.1, false)
          if nd != d then
            D := D.set! l.v nd
            changed := true
        | none => pure ()
      | _ => pure ()
    if !changed then return (false, round)
  return (false, nVars + 2)
```

donde `hasId g s i` pregunta si algún owner global de `g` tiene id `(s, i)`.
