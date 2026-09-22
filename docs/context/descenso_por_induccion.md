# Nacimiento + preservación: el planteamiento

> Qué es esto: el ángulo (0) de [extend_triple.md](extend_triple.md), explorado a fondo.
> **La conclusión principal llegó leyendo, no pensando: la inducción ya está construida.**
> Este documento dice qué hay, qué falta, y en qué orden lo haría.

---

## 0. El giro

Empecé a escribir un planteamiento desde cero para «demostrar `CommonOwner` por inducción
sobre cómo la máquina construye el estado». Cuatro módulos existen ya con ese nombre y ese
plan — `DescentUp`, `DescentJoin`, `DescentFilter`, `DescentInvariant` — y atacan
directamente `NoDeadEnd`, sin pasar por `CommonOwner`.

Así que **hay dos rutas al mismo objetivo**, y conviene no confundirlas:

| | ataca | cómo |
|---|---|---|
| `Descent.lean` | `NoDeadEnd` vía `CommonOwner` | propiedad **estática** de las tablas de un estado |
| `Descent{Up,Join,Filter,Invariant}` | `NoDeadEnd` directamente | **inducción** sobre las operaciones de la máquina |

`commonOwner_of_singleParents` (esta sesión) es de la primera. La segunda tiene **más trabajo
hecho** y no pasa por Helly en ningún momento.

> Aviso de higiene: los docstrings de `DescentUp` y `DescentInvariant` describen la máquina de
> **ventana 2** («el nodo que un `up` crea posee todos los owners globales — su tabla es
> exactamente `gowners` al nacer»). Eso es falso con la fila. Pero **los teoremas sí
> sobrevivieron al puerto**: `noDeadEnd_addNode` maneja la fila explícitamente
> (`hzrow : sel g.current_step ∈ newRowIds g d`, `node_addNode_cases`) y sigue cerrando en
> `[propext, Quot.sound]`. Hay que arreglar los docstrings, no las pruebas.

---

## 1. Lo que hay, caso por caso

La máquina construye estados con cuatro operaciones. Para cada una existe ya el paso de la
inducción:

| caso | teorema | estado |
|---|---|---|
| semilla | `DescentUp.noDeadEnd_initSeed` | ✅ **probado**, trivial (`current_step = 1`) |
| `up` | `DescentUp.noDeadEnd_addNode` | ✅ **probado**, sin axiomas, ventana incluida |
| `join` | `DescentJoin.noDeadEnd_join` | ✅ probado **dado `JoinCoveredF`** |
| filtro | `DescentFilter.noDeadEnd_filterAllAgg_of_completion` | ✅ probado **dado `ReqCompletion`** |
| **ensamblaje** | — | ❌ **no existe** |

Los dos filtros que el driver aplica antes del review son gratis y ni siquiera hacen falta
como casos aparte: `filterWeak` y `filterRequire` tocan **solo `gowners`**
(`{ g with gowners := g.gowners.filter … }`), así que no mueven ni nodos ni tablas, y un
testigo del descenso sigue siéndolo.

---

## 2. Lo que falta, en orden de coste

### (a) El ensamblaje — ✅ **HECHO** (`DescentRun.lean`)

Escrito en `AbsSat/GraphPath/Model/DescentRun.lean`, cuatro teoremas, todos en
`[propext, Quot.sound]` bajo `#guard_msgs`, build entero verde (232 jobs):

| teorema | dice |
|---|---|
| `noDeadEnd_sent` | un envío conserva el descenso: filtro (`ReqCompletion`) y luego fila (`noDeadEnd_addNode`) |
| `noDeadEnd_advance` | un avance de línea lo conserva, incluidas las fusiones (`JoinCoveredF`) |
| `noDeadEnd_run` | toda la corrida |
| `sat_of_reqCompletion` | **el veredicto** |

Las hipótesis que pedía `noDeadEnd_addNode` —`Pinned.Ctx`, `NodupIds`, `MachineOk`, `below`,
`isValid`— salen todas de `MInv` vía `ReadableAgg`, como se esperaba. Sin sorpresas ahí.

**Dos cosas que el ensamblaje hizo visibles, y ninguna se veía desde fuera.**

1. **El descenso no se propaga a lo largo de la corrida.** `noDeadEnd_advance` no lee nunca la
   línea anterior: `advance_inv` arranca la línea nueva desde `[]`, y cada estado enviado saca
   su descenso de **su propio** filtro, no del estado del que vino. La inducción sobre la
   corrida lo es solo de nombre; el contenido es por envío.
2. **Y el veredicto necesita solo la completación.** Un estado del lector se lee tras un
   `filterAllAgg` más, así que `noDeadEnd_filterAllAgg_of_completion` se le aplica directamente:
   `sat_of_reqCompletion` toma `ReqAll` y **no** `JoinAll`. El join y el `up` son lo que haría
   falta para *demostrar* la completación por inducción, no para usarla.

Eso reordena (b) y (c): **`JoinCoveredF` deja de estar en el camino crítico del veredicto** y
pasa a ser instrumental para (b). Si (b) se demostrara por otra vía, (c) no haría falta.

### (b) `ReqCompletion` — el contenido de verdad

```lean
def ReqCompletion (g : GPathM) (reqs : List NodeId) : Prop :=
  ∀ sel lo, 0 < lo → lo ≤ (filterAllAgg g reqs).current_step - 1 →
    SoundFrom (filterAllAgg g reqs) sel lo →
    ∃ sel', ChainSound g sel' ∧
      (∀ k, lo ≤ k → k < g.current_step → sel' k = sel k) ∧
      (∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel' req.step).id = req)
```

*Toda cadena parcial del estado filtrado se completa, **dentro del estado sin filtrar**, a una
cadena entera que cumple los requisitos del filtro.*

**La reducción que vi explorándolo, y que creo que es la pieza que falta.** En una inducción,
`NoDeadEnd g` es la **hipótesis inductiva**. Con ella:

1. una cadena parcial de `filterAllAgg g reqs` es una cadena parcial de `g`
   (el filtrado es un `Pruned` del original: tablas y padres contenidos);
2. `NoDeadEnd g` la baja hasta el paso 0, dando `sel'` con `ChainSound g sel'`;
3. queda solo la tercera cláusula: que `sel'` **pase por los pines**.

Y esa tercera se parte en dos mitades por el paso:

* **pines en pasos ≥ `lo`**: gratis. Ahí los picks ya están en el estado filtrado, y
  `PairChain.node_id_of_pin` dice que **todo nodo de un paso pinchado lleva el nodo de mapa
  pinchado**. No hay nada que elegir.
* **pines en pasos < `lo`**: el residuo. La extensión hacia abajo tiene que poder **dirigirse**
  por los nodos pinchados.

> **`ReqCompletion` ⟸ `NoDeadEnd g` + «el descenso puede dirigirse por los pines».**

Eso es mucho más pequeño que el enunciado original, y es *exactamente* la frase del autor que
`DescentFilter` cita: *«la extensión elegida no puede morir a la poda, porque el review exige
que exista al menos un camino válido»*. La mitad para cadenas **completas** ya es teorema
(`AggressiveReview.ChainSound_filterAllAgg`, el no-se-pierde-ninguna-solución).

### (c) `JoinCoveredF` — el residuo conocido

```lean
def JoinCoveredF (g₁ g₂ : GPathM) : Prop :=
  ∀ sel lo, … → SoundFrom (join g₁ g₂) sel lo →
    SoundFrom g₁ sel lo ∨ SoundFrom g₂ sel lo ∨ ∃ c, SoundFrom (join g₁ g₂) (upd sel (lo-1) c) (lo-1)
```

Ya está reducido dos veces y **ya está medido**:

* `DescentJoin.noDeadEnd_join_of_entries` lo deriva de `EntriesOnOneSide` — *las entradas de
  una cadena del join viven todas en un lado*;
* `DescentJoin.picks_left_of_exclusive_anchor` demuestra que **los nodos** de una cadena del
  join viven todos en un lado (vía `JoinProvenance.slice_of_exclusive_top`), así que lo único
  que puede mezclarse son **entradas de owner** en los nodos que los dos lados comparten;
* `JoinDescent.SideCovered` es el residuo fino, y la sonda `lake exe join-borrow` lo mide.

**Es el caso mejor entendido de los tres**, y el único con sonda propia ya escrita.

---

## 3. Cómo lo plantearía

**Fase 1 — el esqueleto.** ✅ Hecho, y con dos hallazgos que cambian las fases siguientes
(§2(a)): el descenso es por envío, no por corrida, y el veredicto cuelga de **una sola**
hipótesis, `ReqCompletion`.

**Fase 2 — explorada, y corregida.** Ver [reqcompletion.md](reqcompletion.md). Resultado
negativo y demostrado: `ReqCompletion g reqs` ⟺ `NoDeadEnd (filterAllAgg g reqs)`
(`DescentRun.reqCompletion_of_noDeadEnd`), así que **no es una reducción, es el objetivo
reescrito**. El paso que la inducción necesita de verdad es
*(★) `NoDeadEnd g` ⟹ `NoDeadEnd (filterAllAgg g reqs)`* — «la revisión no crea callejones».
Y ahí la ventana sí regala algo cuantificable: los pines de `lo-1` y `lo-2` se cumplen solos por
`PMP`/`GPMP`, o sea **`w-1` pasos de dirección gratis**.

**Fase 3 — `JoinCoveredF`, solo si (b) lo pide.** Con la fase 1 hecha sabemos que no está en
el camino crítico del veredicto: solo haría falta para demostrar `ReqCompletion` por inducción
sobre la construcción. Si la fase 2 encuentra otra vía, esta fase desaparece.

### Lo que NO haría

* **No tocar los docstrings de `DescentUp`/`DescentInvariant` antes de la fase 1.** Están
  obsoletos (describen ventana 2) pero los teoremas son correctos; arreglarlos ahora es ruido
  que no cambia el estado.
* **No abandonar `commonOwner_of_singleParents`.** Es de la otra ruta y sigue siendo el único
  resultado con una clase cerrada sin hipótesis. Si la fase 1 revelara que los casos no
  encajan, es el plan B.
* **No empezar por `ReqCompletion` sin el ensamblaje.** Es la pieza más grande, y sin el
  esqueleto no hay forma de saber si la hipótesis inductiva que necesita es la que la
  inducción realmente le da.

---

## 4. Lo que aprendí por el camino, y que estaba mal en mi nota anterior

En [extend_triple.md](extend_triple.md) §3bis escribí que `CommonOwner` *«nace trivialmente
cierta»* porque `A_k = {c ∈ parents(x) : c ∈ owners(sel k)}` es creciente por
`mem_rowOwners_iff`. **Está dicho de más.** La inclusión
`owners(n) ⊇ owners(padre) ∩ gowners` vale **en el instante en que `n` se crea**, con las
tablas de entonces. Los reviews posteriores encogen ambos lados y la monotonía no se conserva
sola. La intuición —*el problema no está en el nacimiento sino en las eliminaciones*— era
correcta; la formulación, no.

Y el ángulo que salía de ella resultó estar ya construido, que es mejor noticia que la
intuición.
