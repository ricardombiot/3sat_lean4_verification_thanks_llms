# Plan de formalización: espejo puro `GPathM` + Lema L1

**Objetivo:** construir el espejo puro (sin `IO.Ref`) del grafo con Owners y demostrar el
primer lema del puente — **L1, soundness local de requisitos** — tal como se define en
[`lean_project/formal_bridge_owners_runpure.md`](../../lean_project/formal_bridge_owners_runpure.md)
(§5-L1 y §6.1). Este plan cubre las etapas 0 y 1 del puente y deja enunciada (sin
demostrar) la denotación que usarán L2–L8.

**Estado previo del que parte** (2026-07-04):
- Filtro de Owners del ejecutable corregido y `do_join!` cableado (commit `7092d75`).
- Reader portado + arnés `diffTest`: 5.210 casos aleatorios, 0 desacuerdos (commit `1b70d2e`).
- Modelo puro E2 (`run_pure`) demostrado sin axiomas bajo `WellFormedGMap`.

---

## 0. Principios de diseño (decisiones cerradas antes de escribir código)

1. **Solo `List`, nada de `Finset` ni `Std.HashMap` en el modelo.** El proyecto depende
   únicamente de std4 (no hay Mathlib, luego no hay `Finset`), y el modelo puro
   existente (`PureSatMachine`) ya razona con `List` + pertenencia. Los duplicados en
   listas son inofensivos para razonamiento por `∈`.
2. **Owners como lista plana.** Un `PathNodeId` ya contiene su paso (`id.step`), así que
   no hace falta la tabla `paso → conjunto`: los owners de un nodo son
   `List PathNodeId`, y "owners en el paso k" es `filter (·.id.step == k)`. Elimina una
   capa de estructura anidada y todas las lemas de coherencia tabla/contenido.
3. **La validez es un predicado derivado, no un flag almacenado.** En el ejecutable,
   `valid`/`emptySteps` son estado mutable que hay que mantener coherente (origen del
   bug arreglado el 2026-07-04). En el espejo, `isValid g` se *calcula*: todo paso
   `0 ≤ k < current_step` tiene algún owner global. Cero lemas de coherencia de flags.
4. **El espejo es la especificación, no una transcripción bit a bit.** Debe coincidir
   con el ejecutable en los resultados observables del filtro (qué nodos/owners
   sobreviven, validez), no en la representación interna. La equivalencia se valida
   empíricamente con el arnés (§4), y a medio plazo el ejecutable se puede reconstruir
   como el espejo envuelto en un `IO.Ref` (§6.1 del doc del puente), eliminando el
   teorema de refinamiento.
5. **Todo total, sin `partial` en lo que se demuestra.** La única recursión no
   estructural es la revisión de owners; se modela con *fuel* explícito (§2.3) y un
   lema de suficiencia de fuel. `partial def` queda prohibido en `Model/` (bloquea
   `unfold`/inducción).
6. **Cero axiomas, cero `sorry`, `warningAsError` en verde** — mismo estándar que
   `SatMachine/Model/`.

---

## 1. Estructura de ficheros

```
lean_project/AbsSat/GraphPath/Model/
  GPathM.lean            -- F1: estructuras + operaciones puras
  Fuel.lean              -- F2: revisión con fuel + lema de punto fijo
  Reachable.lean         -- F3: estados alcanzables por la máquina
  Denot.lean             -- F4: IsChain / PairwiseOwned / denot (solo definiciones)
  OwnersInvariants.lean  -- F5: invariante ReqFiltered + preservación + L1
  MirrorTest.lean        -- F6: validación diferencial espejo ↔ ejecutable
```

`AbsSat.lean` importa `OwnersInvariants` (y por transitividad todo lo demás) para que
las pruebas se comprueben en el build por defecto, igual que Soundness/Completeness.

---

## 2. Fase F1 — `GPathM.lean`: estructuras y operaciones

### 2.1 Estructuras

```lean
structure PNodeM where
  id      : PathNodeId
  title   : String                 -- solo para el Reader; irrelevante en pruebas
  parents : List PathNodeId
  sons    : List PathNodeId
  owners  : List PathNodeId        -- plana; paso = owner.id.step
  deriving Repr, BEq

structure GPathM where
  nodes        : List PNodeM       -- todas las líneas, plana; paso = node.id.id.step
  gowners      : List PathNodeId   -- owners globales, plana
  current_step : Nat
  map_parent   : Option NodeId
  deriving Repr
```

Vistas derivadas (definiciones, no campos):

```lean
def GPathM.line (g : GPathM) (k : Nat) : List PNodeM
def GPathM.ownersAt (owners : List PathNodeId) (k : Nat) : List PathNodeId
def GPathM.node? (g : GPathM) (id : PathNodeId) : Option PNodeM
def GPathM.isValid (g : GPathM) : Bool     -- ∀ k < current_step, ownersAt ≠ []
```

### 2.2 Operaciones (espejo de las del ejecutable ya corregido)

| Espejo | Ejecutable (GraphPath.lean) | Notas |
|---|---|---|
| `initSeed node title` | `GPath.new` + primer `do_up!` | |
| `filterRequire g req` | `filter_require!` | poda `gowners` en `req.step` |
| `cleanInvalid g` | `clean_invalid_nodes!` | un solo barrido (fold sobre `nodes`): intersecar owners de nodo con `gowners`, eliminar nodos no válidos (reglas 1–4 de `is_valid_node`), limpiar enlaces |
| `reviewParents g` / `reviewSons g` | `review_owners_parents_sons!` / `review_owners_sons_parents!` | un barrido ascendente / descendente |
| `reviewStep g` | una pasada de `make_review_owners!` | `cleanInvalid` + coherencia; devuelve `(g', changed : Bool)` |
| `upFiltering g reqs d title` | `do_up_filtering!` | usa `review` con fuel (F2) |
| `join g₁ g₂` | `do_join!` | unión de nodos (fusionando los de mismo id), unión de `gowners` |

Detalle importante para las pruebas: **las operaciones de poda solo eliminan elementos
de listas** (nodos, owners, enlaces) — nunca añaden. Formular cada op de poda como un
`filter`/`filterMap` hace que la monotonía (§5, P2) salga por lemas genéricos de
`List.filter` en lugar de análisis por casos.

**Hecho (DoD F1):** compila; `#eval`-tests reproducen a mano el ejemplo del libro
(Fig. 1.15: filtrar `X=1, Y=0, Z=0` sobre el PathSet de 3 variables) y el fixture
`test_sat_medium.cnf` a nivel de una sola cadena de UPs.

## 3. Fase F2 — `Fuel.lean`: la revisión termina

```lean
def measure (g : GPathM) : Nat :=
  g.nodes.length + (g.nodes.map (·.owners.length)).sum + g.gowners.length

def review (g : GPathM) : GPathM := reviewFuel (measure g + 1) g

def reviewFuel : Nat → GPathM → GPathM
  | 0, g => g
  | fuel+1, g =>
      let (g', changed) := reviewStep g
      if changed then reviewFuel fuel g' else g'
```

Lemas:
- **F2.a (decrecimiento):** `changed = true → measure g' < measure g`
  (consecuencia directa de "las pasadas solo podan": cada `reviewStep` con cambio
  elimina al menos un elemento).
- **F2.b (suficiencia):** con fuel `measure g + 1` se alcanza el punto fijo:
  `reviewStep (review g) = (review g, false)`.
- **F2.c (caracterización del punto fijo):** tras `review`, todo nodo superviviente
  pasa `is_valid_node` y sus owners están contenidos en la unión de los de sus padres
  y en la de sus hijos (la postcondición que L6 explotará más adelante).

**Hecho (DoD F2):** F2.a–F2.c demostrados sin `sorry`; `review` es `def` total.

## 4. Fase F6 (en paralelo desde F1) — `MirrorTest.lean`: el espejo no miente

Antes de demostrar nada sobre el espejo, comprobar que computa lo mismo que el
ejecutable. Reutilizar la infraestructura de `DiffTest`:

- Una función `runMirrorMachine : PureGMap → …` que ejecuta el bucle de la máquina
  (init/up_filtering/join por timeline) **sobre `GPathM`**, y un lector exponencial puro
  (~30 líneas: es `filterRequire` + `review` con requisito unitario).
- Extender `diffTest` a comparación a tres bandas: `ExhaustiveSolver` vs máquina IO vs
  máquina espejo, comparando veredicto y conjuntos de soluciones.
- Tanda de aceptación: ≥ 2.000 casos, 0 desacuerdos, mismas semillas registradas.

Esto convierte "el espejo refleja el ejecutable" de esperanza en evidencia, sin pagar
un teorema de refinamiento IO ↔ puro que no aporta nada al puente.

**Hecho (DoD F6):** tres bandas en verde con ≥ 2.000 casos y dos semillas.

## 5. Fase F3 — `Reachable.lean`: estados alcanzables

L1 no es cierto para un `GPathM` arbitrario — solo para los que la máquina construye.
Se formaliza con un inductivo parametrizado por el mapa (que aporta `requiresOf`):

```lean
def requiresOf (gmap : PureGMap) (id : NodeId) : List NodeId  -- de PureNode.requirements

inductive Reachable (gmap : PureGMap) : GPathM → Prop where
  | seed  : ∀ n ∈ capa 0, Reachable gmap (initSeed n …)
  | up    : Reachable gmap g → d ∈ capa (g.current_step) →
            Reachable gmap (upFiltering g (requiresOf gmap d.id) d.id …)
  | join  : Reachable gmap g₁ → Reachable gmap g₂ → okJoin g₁ g₂ →
            Reachable gmap (join g₁ g₂)
```

donde `okJoin` captura las precondiciones de `is_valid_join` (mismo `current_step`,
mismo `map_parent`). Lemas básicos de sanidad estructural, todos por inducción sobre
`Reachable`:

- **P1 (pasos honestos):** todo nodo/owner de `g` tiene paso `< g.current_step`.
- **P2 (monotonía de poda):** si `g ⟶ g'` por cualquier op que no sea `up`/`join`,
  entonces nodos, owners y enlaces de `g'` ⊆ los de `g`.
- **P3 (procedencia):** todo `PathNodeId` presente proyecta a un nodo del mapa de su
  capa (el análogo de `path_confined_to` del modelo E2, que el puente reutilizará).

**Hecho (DoD F3):** `Reachable` + P1–P3 sin `sorry`.

## 6. Fase F4 — `Denot.lean`: la denotación (solo definiciones)

Las definiciones del §3 del doc del puente, para poder *enunciar* el corolario de L1
(demostrarlas en general es L2–L7, fuera de alcance aquí):

```lean
def IsChain (g : GPathM) (sel : Nat → PathNodeId) : Prop := …
def PairwiseOwned (g : GPathM) (sel : Nat → PathNodeId) : Prop :=
  ∀ i j, i < g.current_step → j < g.current_step → i ≠ j →
    sel i ∈ GPathM.ownersAt (nodeOwners g (sel j)) i
def pathOf (sel : Nat → PathNodeId) (S : Nat) : PurePath := …  -- orden de fold_choices
```

**Hecho (DoD F4):** definiciones compilan y un `#eval`-test con `Decidable` ad hoc las
ejercita sobre el ejemplo del libro.

## 7. Fase F5 — `OwnersInvariants.lean`: el Lema L1

### 7.1 El invariante inductivo

> **ReqFiltered:** para todo nodo `d` del grafo y todo `req ∈ requiresOf gmap d.id.id`,
> los owners de `d` en el paso `req.step` solo apuntan al nodo requerido:
>
> ```lean
> def ReqFiltered (gmap : PureGMap) (g : GPathM) : Prop :=
>   ∀ d ∈ g.nodes, ∀ req ∈ requiresOf gmap d.id.id,
>     ∀ q ∈ d.owners, q.id.step = req.step → q.id = req
> ```

### 7.2 Cadena de preservación (el orden de ataque)

| Lema | Enunciado | Por qué sale |
|---|---|---|
| L1.a | `ReqFiltered` tras `initSeed` | vacuo (sin requisitos en capa 0) o directo |
| L1.b | poda preserva `ReqFiltered` | por P2: los owners de `g'` ⊆ owners de `g`; una propiedad ∀-sobre-owners sobrevive a cualquier `filter` |
| L1.c | `upFiltering` establece `ReqFiltered` para el nodo nuevo | el nodo nuevo hereda `gowners` *después* de `filterRequire` por cada `req`: en `req.step` solo queda el requerido; para los nodos viejos, L1.b |
| L1.d | `join` preserva `ReqFiltered` | **el corazón de L1**: `join` fusiona owners solo entre nodos con el *mismo* `PathNodeId`; por `Reachable`, ambos operandos contienen ese id solo si ambos pasaron `upFiltering` con los *mismos* `requiresOf` (mismo id de mapa ⟹ mismos requisitos, usando `WellFormedGMap.unique_ids`); la unión de dos listas que cumplen la propiedad la cumple |
| **L1** | `Reachable gmap g → ReqFiltered gmap g` | inducción sobre `Reachable` con L1.a–L1.d |

Nota técnica sobre L1.d: necesita el lema auxiliar *"mismo `PathNodeId` alcanzable ⟹
mismo historial de filtrado de requisitos"*. No hace falta rastrear historiales: basta
que `requiresOf` sea función del id de mapa (determinista) y que ambos operandos
cumplan ya `ReqFiltered` — la preservación es puramente algebraica
(`∈ unión ⟹ ∈ alguno`). El párrafo del historial es motivación, no parte de la prueba.

### 7.3 El corolario a nivel de cadena (la conexión con el puente)

> **L1-cor:** si `Reachable gmap g`, `IsChain g sel`, `PairwiseOwned g sel`, entonces
> para todo `j < g.current_step` y todo `req ∈ requiresOf gmap (sel j).id`:
> `(sel req.step).id = req` — y por tanto `pathOf sel` satisface
> `satisfies_requirements` en cada prefijo (enunciado exactamente en los términos de
> `ChoicesValid` del modelo E2).

Demostración: `PairwiseOwned` da `sel req.step ∈ owners (sel j)` en ese paso; `ReqFiltered`
(por L1) fuerza `(sel req.step).id = req`. El empalme con `ChoicesValid` es un
desplegado de definiciones más P3.

**Este corolario es la mitad "soundness" del puente en miniatura**: deja demostrado que
ninguna cadena co-poseída puede violar un requisito. Lo que L2–L7 añadirán después es
que las cadenas co-poseídas son exactamente lo que la máquina representa y el Reader
enumera.

**Hecho (DoD F5):** L1 y L1-cor sin `sorry` ni axiomas; `#print axioms` limpio.

---

## 8. Orden de trabajo, tamaños y riesgos

Orden: **F1 → F6(smoke) → F2 → F3 → F4 → F5 → F6(aceptación)**.
F6 arranca en cuanto F1 compila: si el espejo divergiera del ejecutable, mejor saberlo
antes de demostrar nada sobre él.

| Fase | Tamaño | Riesgo principal | Mitigación |
|---|---|---|---|
| F1 | M | desviarse semánticamente del ejecutable al "simplificar" | F6 smoke temprano; revisar contra `GraphPath.lean` corregido, no contra Julia |
| F2 | M | formular `reviewStep` de modo que el decrecimiento no sea evidente | diseñar cada pasada como `filter` explícito (P2 gratis) |
| F3 | S | precondiciones de `okJoin` incompletas | copiarlas de `is_valid_join` y del uso real en `ColTimelineStep.impact!` |
| F4 | S | — | — |
| F5 | M/L | L1.d: tentación de rastrear historiales | quedarse en el argumento algebraico de §7.2 |
| F6 | S/M | duplicar el bucle de máquina (IO y puro) y que diverjan | factorizar el driver de timeline sobre una interfaz común si se puede sin fricción; si no, aceptar la duplicación con el diff de 3 bandas como red |

Dependencias externas: ninguna nueva (solo std4). Convención de calidad: la de
`SatMachine/Model/` (docstrings con la intención, teoremas nombrados por contenido,
nada de `native_decide`).

## 9. Qué NO está en alcance (para no deslizarse)

- L2–L8 del puente (filtro↔denotación, join↔unión, L6/Helly, Reader). F4 solo *define*.
- Teorema de refinamiento IO ↔ espejo (sustituido por F6 + plan §6.1 del puente).
- E1 (CNF ↔ GMap) — independiente; puede avanzar en paralelo si hay energía.
- Cualquier afirmación de complejidad.

---
*Plan escrito por Claude (Fable 5) el 2026-07-04, como continuación de
`formal_bridge_owners_runpure.md` tras cerrar el arnés diferencial (5.210 casos, 0
desacuerdos).*
