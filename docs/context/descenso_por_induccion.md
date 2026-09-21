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

### (a) El ensamblaje — mecánico, y es lo que yo haría primero

**No existe ningún teorema que componga los cuatro casos.** Nadie fuera de los propios
módulos `Descent*` los usa: el grep de `noDeadEnd_addNode`, `noDeadEnd_join` y
`noDeadEnd_filterAllAgg_of_completion` fuera de ahí sale vacío.

Lo que falta es una inducción sobre `Reachable` (o sobre el driver) que dé

```lean
theorem noDeadEnd_run (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hJ : ∀ …, JoinCoveredF …) (hR : ∀ …, ReqCompletion …) :
    NoDeadEnd (filterAllAgg kv.2 [])
```

y con `NoDeadEndVerdict.sat_of_noDeadEnd` detrás, **el veredicto con exactamente dos
hipótesis con nombre**. Es trabajo de fontanería —descargar las hipótesis de
`noDeadEnd_addNode` (`Pinned.Ctx`, `NodupIds`, `MachineOk`, `below`, `isValid`) desde `MInv`,
que ya las tiene todas— pero es lo que convierte cuatro lemas sueltos en una ruta.

**Por qué primero:** hasta que exista, no se sabe si los cuatro casos encajan de verdad, y
cualquier trabajo sobre (b) o (c) es a ciegas. Y si no encajan, mejor saberlo ahora.

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

**Fase 1 — el esqueleto (días, no semanas).** Escribir `noDeadEnd_run`. Descargar las
hipótesis de `noDeadEnd_addNode` desde `MInv`/`StateOkF`, que ya las contienen todas. Dejar
`JoinCoveredF` y `ReqCompletion` como hipótesis del teorema. Resultado: un `sat_of_*` con dos
hipótesis con nombre, y la certeza de que los cuatro casos encajan.

**Fase 2 — `ReqCompletion` desde la hipótesis inductiva.** Probar la reducción del §2(b):
`NoDeadEnd g` + pines-en-pasos-≥-`lo`-gratis, dejando como residuo solo *«el descenso puede
dirigirse por los pines por debajo de `lo`»*. Aunque el residuo quede abierto, el enunciado
que queda es **mucho más pequeño** y dice algo que se puede medir con una sonda.

**Fase 3 — elegir entre el residuo de (b) y el de (c).** Con las dos fases anteriores hechas,
las dos hipótesis restantes están al mismo nivel de granularidad y se puede comparar por
esfuerzo en vez de por corazonada. Hoy no se puede.

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
