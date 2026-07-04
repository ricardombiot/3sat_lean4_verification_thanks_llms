# Brain FRA — Plan de Ataque: 4 `sorry` en `OwnersInvariants.lean`

**Fecha:** 2026-07-04
**Contexto:** Fase F5 del plan [`espejo_gpathm_lema_L1.md`](./espejo_gpathm_lema_L1.md)
**Estado previo:** F1, F2(a+b), F3, F4, F6 completados (0 `sorry`). F5 con estructura compilable y 4 `sorry` restantes.

---

## 0. Resumen Ejecutivo

El archivo `OwnersInvariants.lean` define el invariante `ReqFiltered` y demuestra L1
(`Reachable → ReqFiltered`) por inducción sobre `Reachable`. Los casos `seed`,
`filterRequire` y `filterAll` están demostrados. Quedan 4 bloques con `sorry`:

| # | Teorema | Dificultad | Dependencias |
|---|---------|-----------|-------------|
| S1 | `review_preserves_ReqFiltered` | Alta | Cadena `cleanInvalid → reviewNode → reviewSteps → reviewPass → reviewFuel → review` |
| S2 | `upFiltering_ReqFiltered` | Alta | `filterAll_preserves_ReqFiltered` + estructura de `addNode` |
| S3 | `join_preserves_ReqFiltered` | Media | Estructura de `mergeNode` |
| S4 | `L1_cor` | Media | Cableado `IsChain`/`PairwiseOwned`/`ReqFiltered` |

---

## 1. K-Logic: Axiomas Formales Extraídos

### A₁: Definición del invariante

```
ReqFiltered(g) := ∀ d ∈ g.nodes, ∀ req ∈ reqOf(d.id.id), ∀ q ∈ d.owners,
                    q.id.step = req.step → q.id = req
```

Es una propiedad `∀ x ∈ list, P(x)` — sobrevive a cualquier filtrado de la lista.

### A₂: Monotonía estructural (OwnersSubset)

```
OwnersSubset(g, g') := ∀ d ∈ g'.nodes, ∃ d' ∈ g.nodes,
                         d'.id = d.id ∧ (∀ q ∈ d.owners, q ∈ d'.owners)
```

### A₃: Puente lógico-estructural

```
A₃: OwnersSubset(g, g') → (ReqFiltered(g) → ReqFiltered(g'))
```

**Demostrado** (4 líneas, `OwnersSubset_preserves_ReqFiltered`). Es el desacople clave: el
razonamiento sobre la estructura del grafo (estrechamiento/eliminación) se separa del
invariante lógico.

### A₄: Operaciones de estrechamiento

Toda operación de revisión (`cleanInvalid`, `reviewNode`, `reviewPass`, `review`) solo:
- Reemplaza `owners` de un nodo por `intersectOwners old_owners keepers` (filtro → subconjunto)
- Elimina nodos (`removeNode`)

Ambas satisfacen `OwnersSubset`.

### A₅: Limpieza de gowners por filtro

```
filterRequire_cleans_gowner: ∀ req ∈ reqs, ∀ q ∈ (filterAll g reqs).gowners,
                              q.id.step = req.step → q.id = req
```

**Demostrado.** Garantiza que el nuevo nodo en `upFiltering` herede owners limpios.

### A₆: Requisitos estrictamente hacia atrás

El constructor `Reachable.up` incluye `hreqs_back: ∀ req ∈ reqOf d, req.step < d.step`.
Transitivamente (inducción sobre `Reachable`), todo requisito de cualquier nodo apunta a un
paso estrictamente anterior. Esto garantiza que `pid` (añadido a owners viejos en `addNode`,
con `pid.id.step = g.current_step`) nunca coincide con ningún `req.step` de nodo viejo.

### A₇: Merge de owners en join

```
mergeNode(a, b).owners = a.owners ++ (b.owners \ a.owners)
```

Cada `q` en la unión pertenece a `a.owners` o a `b.owners`. Si ambos satisfacen
`ReqFiltered`, la unión también.

---

## 2. Derivation Validation: Corrección de la Estrategia

### Soundness check de `OwnersSubset`

- **Premisas existentes:** `OwnersSubset_preserves_ReqFiltered` ya demostrado (4 líneas).
- **A demostrar:** `OwnersSubset g (op g)` para cada operación `op` en la cadena de review.
- **Conclusión:** `ReqFiltered g → ReqFiltered (op g)` por A₃. ✓

No hay razonamiento circular: cada operación se analiza estructuralmente (solo estrecha o
elimina), y el invariante se preserva vía A₃.

### Soundness check de `upFiltering`

- El grafo resultante tiene nodos de dos tipos: viejos (de `filterAll g reqs`) y el nuevo.
- **Nodo nuevo:** owners = `(filterAll g reqs).gowners`. Por A₅, los gowners están limpios
  para cada `req ∈ reqOf d`. Por A₄, `filterAll` solo estrecha → la limpieza se preserva.
- **Nodos viejos:** owners extendidos con `pid`. Por A₆, `pid.id.step` no coincide con
  ningún `req.step` de nodo viejo → el invariante se preserva. ✓

### Soundness check de `join`

- `join` mergea nodos por `PathNodeId`. Cada nodo resultante tiene `owners = a.owners ∪ b.owners`.
- Por A₇, cada `q` está en uno de los dos operandos. Ambos satisfacen `ReqFiltered` por IH.
- La unión preserva porque el invariante es `∀ q ∈ owners, ...`. ✓

### Soundness check de `L1_cor`

- `PairwiseOwned` da `sel(req.step) ∈ ownersOf(sel j)` en el paso `req.step`.
- `ReqFiltered` (vía L1) fuerza que ese owner tenga `id = req`.
- Caso `req.step = j`: por A₆, `req.step < (sel j).id.id.step = j`, contradicción. ✓

---

## 3. Bias Correction

### Sesgo detectado: Optimism bias

**Señal:** "las pruebas de inducción sobre folds serán sencillas porque el invariante es
monótono."

**Realidad:** Las pruebas requieren manejar detalles sintácticos de Lean: `let` bindings en
`addNode`, lambdas en `removeNode`, `==` vs `=` en `updateAtGo`, y la dirección de
`List.mem_map.mp` (que da `f a = x`, no `x = f a`).

**Corrección:** El plan incluye mitigaciones específicas para cada punto conflictivo:
- Usar `by_cases h_eq : x.id = id` en lugar de depender de `simp` con `==`
- Usar `calc` con pasos explícitos para `rw` en lambdas
- Usar `dsimp` para reducción de `with` updates
- Smoke build después de cada 2-3 lemas

### Sesgo detectado: Anchoring

**Señal:** Intentos previos anclados en `unfold` + `simp` como táctica principal.

**Corrección:** El plan usa el patrón de `Fuel.lean`: `induction ... generalizing g with`,
`by_cases`, `subst`, `simp` — un patrón probado en el mismo codebase.

---

## 4. Plan de Ataque: 12 Pasos

### Paso 1 — `removeNode_OwnersSubset` (~10 líneas)

**Depende de:** nada.
**Patrón:** `List.mem_map.mp` + `calc` para igualdad de campos.

```lean
private theorem removeNode_OwnersSubset (g : GPathM) (id : PathNodeId) :
    OwnersSubset g (GPathM.removeNode g id) := by
  intro d hd
  dsimp [GPathM.removeNode] at hd
  rcases List.mem_map.mp hd with ⟨d_orig, hd_orig_mem, hd_eq⟩
  -- hd_eq : (fun n => {n with parents:=..., sons:=...}) d_orig = d
  have hd_orig_mem' := (List.mem_filter.mp hd_orig_mem).left
  refine ⟨d_orig, hd_orig_mem', ?_, ?_⟩
  · -- d_orig.id = d.id (lambda preserva .id)
    calc
      d_orig.id = ((fun n => { n with parents := n.parents.filter (· != id),
        sons := n.sons.filter (· != id) }) d_orig).id := rfl
      _ = d.id := by rw [hd_eq]
  · -- q ∈ d.owners → q ∈ d_orig.owners (lambda preserva .owners)
    intro q hq
    have h_ow_eq : d.owners = d_orig.owners :=
      calc
        d.owners = ((fun n => { n with parents := n.parents.filter (· != id),
          sons := n.sons.filter (· != id) }) d_orig).owners := by rw [hd_eq.symm]
        _ = d_orig.owners := rfl
    rw [h_ow_eq] at hq; exact hq
```

**Riesgo:** `rfl` en el último paso del `calc` para `.owners` puede fallar si el kernel no
reduce la lambda con `with`. **Mitigación:** Si falla, usar `simpa` o `dsimp`:

```lean
    _ = d_orig.owners := by
      dsimp
      rfl
```

---

### Paso 2 — `updateAtGo_OwnersSubset` (~15 líneas)

**Depende de:** nada.
**Patrón:** `induction g.nodes generalizing d` + `by_cases h_eq : x.id = id`. Este es el
patrón exacto de `measure_updateAtGo_le` en `Fuel.lean`.

```lean
private theorem updateAtGo_OwnersSubset (g : GPathM) (id : PathNodeId)
    (keepers : List PathNodeId) :
    OwnersSubset g {g with nodes := GPathM.updateAtGo id
      (fun n => { n with owners := intersectOwners n.owners keepers }) g.nodes} := by
  intro d hd
  induction g.nodes generalizing d with
  | nil => simp at hd
  | cons x xs ih =>
    unfold GPathM.updateAtGo at hd
    by_cases h_eq : x.id = id
    · simp [h_eq] at hd
      rcases hd with (rfl | hd')
      · -- d = {x with owners := intersectOwners x.owners keepers}
        refine ⟨x, by simp, ?_, ?_⟩
        · rfl
        · intro q hq
          -- intersectOwners x.owners keepers ⊆ x.owners
          simp [GPathM.intersectOwners] at hq
          exact hq.1
      · -- d viene de la cola
        rcases ih hd' with ⟨d', hd', h_id, h_sub⟩
        exact ⟨d', List.mem_cons_of_mem _ hd', h_id, h_sub⟩
    · simp [h_eq] at hd
      rcases hd with (rfl | hd')
      · exact ⟨x, by simp, rfl, λ q hq => hq⟩
      · rcases ih hd' with ⟨d', hd', h_id, h_sub⟩
        exact ⟨d', List.mem_cons_of_mem _ hd', h_id, h_sub⟩
```

**Punto crítico:** `by_cases h_eq : x.id = id` usa `=` (Prop) en lugar de `==` (Bool).
Esto evita los problemas con `simp` y `BEq` que plagaron los intentos anteriores.

---

### Paso 3 — `cleanInvalidGo_OwnersSubset` (~12 líneas)

**Depende de:** P1, P2, `trans_OwnersSubset`.
**Patrón:** `induction ids generalizing g`.

```lean
private theorem trans_OwnersSubset (hAB : OwnersSubset a b) (hBC : OwnersSubset b c) :
    OwnersSubset a c := by
  intro d hd
  rcases hBC d hd with ⟨d', hd', h_id, h_sub⟩
  rcases hAB d' hd' with ⟨d'', hd'', h_id', h_sub'⟩
  refine ⟨d'', hd'', ?_, ?_⟩
  · rw [← h_id, h_id']
  · intro q hq; apply h_sub'; apply h_sub; exact hq

private theorem cleanInvalidGo_OwnersSubset (ids : List PathNodeId) (g : GPathM) :
    OwnersSubset g (GPathM.cleanInvalidGo g ids) := by
  induction ids generalizing g with
  | nil => simp [OwnersSubset, GPathM.cleanInvalidGo]
  | cons id rest ih =>
    simp [GPathM.cleanInvalidGo]
    split
    · exact ih g
    · next d hd =>
      let g1 := {g with nodes := GPathM.updateAtGo id
        (fun n => { n with owners := intersectOwners n.owners g.gowners }) g.nodes}
      have h_g1 : OwnersSubset g g1 := updateAtGo_OwnersSubset g id g.gowners
      split
      · -- nodo válido: estrechar → continuar
        exact trans_OwnersSubset h_g1 (ih g1)
      · -- nodo eliminado: estrechar → eliminar → continuar
        have h_rem : OwnersSubset g1 (GPathM.removeNode g1 id) :=
          removeNode_OwnersSubset g1 id
        exact trans_OwnersSubset (trans_OwnersSubset h_g1 h_rem)
          (ih (GPathM.removeNode g1 id))
```

---

### Pasos 4-8 — Cadena `reviewNode → ... → review`

**Patrón común:** `induction ... generalizing g` para cada fold, componiendo con
`trans_OwnersSubset`. La estructura es repetitiva y sigue el molde de `Fuel.lean`.

```lean
-- P4: reviewNode_OwnersSubset
private theorem reviewNode_OwnersSubset (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) : OwnersSubset g (GPathM.reviewNode g nb id) := by
  simp [GPathM.reviewNode]
  split
  · -- node? devuelve none → identidad
    simp [OwnersSubset]
  · next d hd =>
    split
    · -- isValidNode: estrechar con unionOwnersOf, luego keep o remove
      let keepers := GPathM.unionOwnersOf g (nb d)
      let g1 := {g with nodes := GPathM.updateAtGo id
        (fun n => { n with owners := intersectOwners n.owners keepers }) g.nodes}
      have h_g1 : OwnersSubset g g1 := updateAtGo_OwnersSubset g id keepers
      split
      · exact h_g1
      · exact trans_OwnersSubset h_g1 (removeNode_OwnersSubset g1 id)
    · -- !isValidNode: eliminar directamente
      exact removeNode_OwnersSubset g id

-- P5: reviewLine_OwnersSubset
private theorem reviewLine_OwnersSubset (g : GPathM) (nb : PNodeM → List PathNodeId)
    (k : Int) : OwnersSubset g (GPathM.reviewLine g nb k) := by
  dsimp [GPathM.reviewLine]
  induction ((g.line k).map (·.id)) generalizing g with
  | nil => simp [OwnersSubset]
  | cons id tail ih =>
    simp
    -- foldl step: reviewNode, que preserva OwnersSubset
    have h_step : OwnersSubset g (GPathM.reviewNode g nb id) :=
      reviewNode_OwnersSubset g nb id
    exact trans_OwnersSubset h_step (ih _)

-- P6: reviewSteps_OwnersSubset
private theorem reviewSteps_OwnersSubset (g : GPathM) (nb : PNodeM → List PathNodeId)
    (ks : List Int) : OwnersSubset g (GPathM.reviewSteps g nb ks) := by
  induction ks generalizing g with
  | nil => simp [OwnersSubset, GPathM.reviewSteps]
  | cons k ks ih =>
    simp [GPathM.reviewSteps]
    split
    · have h_line : OwnersSubset g (GPathM.reviewLine g nb k) :=
        reviewLine_OwnersSubset g nb k
      exact trans_OwnersSubset h_line (ih _)
    · simp [OwnersSubset]

-- P7: reviewPass_OwnersSubset
private theorem reviewPass_OwnersSubset (g : GPathM) :
    OwnersSubset g (GPathM.reviewPass g) := by
  dsimp [GPathM.reviewPass]
  have h_cl := cleanInvalidGo_OwnersSubset (g.nodes.map (·.id)) g
  have h_par := reviewSteps_OwnersSubset (GPathM.cleanInvalid g) (·.parents)
    (intRange 1 (g.current_step - 1))
  have h_son := reviewSteps_OwnersSubset (GPathM.reviewParents (GPathM.cleanInvalid g))
    (·.sons) ((intRange 1 (g.current_step - 2)).reverse)
  exact trans_OwnersSubset (trans_OwnersSubset h_cl h_par) h_son

-- P8: reviewFuel_OwnersSubset
private theorem reviewFuel_OwnersSubset (fuel : Nat) (g : GPathM) :
    OwnersSubset g (GPathM.reviewFuel fuel g) := by
  induction fuel generalizing g with
  | zero => simp [OwnersSubset, GPathM.reviewFuel]
  | succ fuel ih =>
    simp [GPathM.reviewFuel]
    split
    · split
      · have h_pass := reviewPass_OwnersSubset g
        exact trans_OwnersSubset h_pass (ih _)
      · simp [OwnersSubset]
    · simp [OwnersSubset]

-- review_OwnersSubset
private theorem review_OwnersSubset (g : GPathM) :
    OwnersSubset g (GPathM.review g) := by
  dsimp [GPathM.review]
  exact reviewFuel_OwnersSubset (GPathM.measure g + 1) g
```

**Estimación combinada P4-P8:** ~60 líneas.

---

### Paso 9 — `review_preserves_ReqFiltered` (2 líneas)

```lean
private theorem review_preserves_ReqFiltered (h : ReqFiltered reqOf g) :
    ReqFiltered reqOf (GPathM.review g) :=
  OwnersSubset_preserves_ReqFiltered reqOf h (review_OwnersSubset g)
```

---

### Paso 10 — `upFiltering_ReqFiltered` (~30 líneas)

**Depende de:** P9, `filterRequire_cleans_gowner`, `pid_safe` (nuevo).

#### Sub-lema A: `filtered_gowners_ReqFiltered`

```lean
-- Los gowners después de filterAll son limpios para cada req
private theorem filtered_gowners_ReqFiltered (g : GPathM) (reqs : List NodeId)
    (d : NodeId) (hreqs_sub : ∀ req, req ∈ reqs → req ∈ reqOf d)
    (hdistinct : ∀ r₁ r₂, r₁ ∈ reqs → r₂ ∈ reqs → r₁.step = r₂.step → r₁ = r₂) :
    ∀ req ∈ reqs, ∀ q ∈ (GPathM.filterAll g reqs).gowners,
      q.id.step = req.step → q.id = req := by
  -- Por inducción sobre reqs. Cada filterRequire limpia su step. La review solo quita.
  -- Usar filterRequire_cleans_gowner para el paso base y trans_OwnersSubset para review.
  ...
```

#### Sub-lema B: `pid_safe` (requiere P1 de Reachable)

```lean
-- pid añadido en addNode no viola ReqFiltered para nodos viejos
theorem pid_safe (h_reach : Reachable reqOf g) (n : PNodeM) (hn : n ∈ g.nodes)
    (pid : PathNodeId) (hpid_step : pid.id.step = g.current_step)
    (req : NodeId) (hreq : req ∈ reqOf n.id.id) : pid.id.step ≠ req.step := by
  -- Por inducción sobre Reachable, todos los reqs de n tienen req.step < n.id.id.step
  -- y n.id.id.step < g.current_step = pid.id.step (por P1)
  -- Luego req.step < pid.id.step → req.step ≠ pid.id.step
  ...
```

El lema `pid_safe` necesita `steps_below_current` (P1 de `Reachable.lean`) que aún no está
demostrado. **Ajuste táctico:** En lugar de probar P1 completo, se puede probar una versión
más débil directamente sobre `Reachable`:

```lean
theorem reqs_back_trans (h : Reachable reqOf g) :
    ∀ n ∈ g.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step := by
  induction h with
  | seed d title hstep hreqs_back =>
    rcases hstep with rfl
    intro n hn; simp at hn; subst hn
    exact hreqs_back
  | up g d title hstep hreqs_back hreqs_distinct h_reach ih =>
    rcases hstep with rfl
    -- upFiltering = addNode (filterAll g reqs) d title
    -- expandir addNode para ver los nodos resultantes
    -- Nodo nuevo: hreqs_back da la propiedad
    -- Nodos viejos: ih + filterAll solo estrecha → preservado
    ...
  | join g₁ g₂ hok h_reach₁ h_reach₂ ih₁ ih₂ =>
    -- join = merge de nodos por id; ambos lados preservan
    ...
```

**Estimación `reqs_back_trans`:** ~20 líneas adicionales.

#### Cuerpo principal de `upFiltering_ReqFiltered`

```lean
theorem upFiltering_ReqFiltered (h : ReqFiltered reqOf g)
    (d : NodeId) (title : String) (hstep : d.step = g.current_step)
    (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step)
    (hreqs_distinct : ∀ r₁ r₂, r₁ ∈ reqOf d → r₂ ∈ reqOf d → r₁.step = r₂.step → r₁ = r₂) :
    ReqFiltered reqOf (GPathM.upFiltering g (reqOf d) d title) := by
  dsimp [GPathM.upFiltering, GPathM.up]
  let g' := GPathM.filterAll g (reqOf d)
  have h_g' : ReqFiltered reqOf g' := filterAll_preserves_ReqFiltered reqOf h (reqOf d)
  split
  · -- isValid g': expandir addNode
    dsimp [GPathM.addNode]
    -- Grafo resultante: nodes = viejos_nodos_extendidos ++ [nuevo_nodo]
    -- nuevo_nodo.owners = g'.gowners
    -- viejos_nodos tienen owners extendidos con pid
    intro n hn req hreq q hq hstep_q
    -- Analizar si n es el nuevo nodo o uno viejo
    -- Caso A: n está en viejos_nodos_extendidos
    --   Sus owners = old_owners ++ [pid]
    --   Si q ∈ old_owners: por h_g'
    --   Si q = pid: pid.id.step = g.current_step ≠ req.step (por reqs_back_trans)
    -- Caso B: n es el nuevo nodo
    --   Sus owners = g'.gowners
    --   Por filtered_gowners_ReqFiltered, q.id = req
    ...
  · -- not valid: resultado es g'
    exact h_g'
```

---

### Paso 11 — `join_preserves_ReqFiltered` (~20 líneas)

#### Sub-lema: `mergeNode_owners_subset`

```lean
private theorem mergeNode_owners_subset (a b : PNodeM) (q : PathNodeId)
    (hq : q ∈ (GPathM.mergeNode a b).owners) : q ∈ a.owners ∨ q ∈ b.owners := by
  simp [GPathM.mergeNode] at hq
  -- hq : q ∈ a.owners ++ b.owners.filter (λ q => !a.owners.contains q)
  rcases List.mem_append.mp hq with (hq' | hq')
  · exact Or.inl hq'
  · have hq'' := (List.mem_filter.mp hq').left
    exact Or.inr hq''
```

#### Cuerpo principal

```lean
theorem join_preserves_ReqFiltered (h₁ : ReqFiltered reqOf g₁)
    (h₂ : ReqFiltered reqOf g₂) (hok : GPathM.okJoin g₁ g₂) :
    ReqFiltered reqOf (GPathM.join g₁ g₂) := by
  dsimp [ReqFiltered, GPathM.join]
  intro n hn req hreq q hq hstep
  simp at hn
  rcases hn with (hn | hn)
  · -- n en parte mergeada de g₁.nodes
    rcases List.mem_map.mp hn with ⟨n₁, hn₁, hn_eq⟩
    -- n = mergeNode n₁ (g₂.node? n₁.id).getD n₁
    have h_merge_ow : q ∈ n₁.owners ∨ q ∈ ((GPathM.node? g₂ n₁.id).elim n₁ id).owners := by
      -- de mergeNode_owners_subset con n₁ y (node? g₂ n₁.id |>.getD n₁)
      ...
    rcases h_merge_ow with (hq₁ | hq₂)
    · exact h₁ n₁ hn₁ req hreq q hq₁ hstep
    · -- q viene de g₂; aplicar h₂ al nodo correspondiente
      ...
  · -- n ∈ g₂.nodes, no en g₁
    exact h₂ n hn req hreq q hq hstep
```

---

### Paso 12 — `L1_cor` (~25 líneas)

```lean
theorem L1_cor (h_reach : Reachable reqOf g)
    (h_chain : IsChain g sel) (h_owned : PairwiseOwned g sel)
    (j : Int) (hj_lo : 0 ≤ j) (hj_hi : j < g.current_step)
    (req : NodeId) (hreq : req ∈ reqOf (sel j).id)
    (h_req_step_pos : 0 ≤ req.step) (h_req_step_lt : req.step < g.current_step) :
    (sel req.step).id = req := by
  rcases h_chain with ⟨h_chain_node, h_chain_link⟩
  have h_inv : ReqFiltered reqOf g := L1 reqOf h_reach
  by_cases hij : req.step = j
  · subst hij
    -- req.step = j: req apunta al mismo paso que el nodo
    -- Pero reqs_back_trans dice req.step < (sel j).id.id.step = j (por P1/h_chain)
    -- Contradicción
    have h_node_step : (sel j).id.id.step = j := by
      -- De h_chain_node: (g.node? (sel j)).isSome
      -- Y por reqs_back_trans + el hecho de que sel j está en g.nodes
      ...
    have h_back : req.step < (sel j).id.id.step := ...
    rw [h_node_step] at h_back
    omega
  · -- req.step ≠ j: PairwiseOwned da el owner, ReqFiltered fuerza id = req
    have h_owner : sel req.step ∈ ownersAt (ownersOf g (sel j)) req.step :=
      h_owned (req.step) j h_req_step_pos hj_lo h_req_step_lt hj_hi hij
    -- h_owner: sel req.step está en los owners de sel j en el paso req.step
    -- Expandir ownersAt/ownersOf
    simp [ownersAt, ownersOf, GPathM.node?] at h_owner
    -- h_owner da: sel req.step ∈ owners_list ∧ (sel req.step).id.step = req.step
    -- Aplicar h_inv al nodo sel j (si existe en g.nodes)
    ...
```

---

## 5. Orden de Trabajo y Estimaciones

| # | Tarea | Líneas | Tiempo est. | Depende de |
|---|-------|--------|-------------|-----------|
| P1 | `removeNode_OwnersSubset` | 10 | 15 min | — |
| P2 | `updateAtGo_OwnersSubset` | 15 | 20 min | — |
| P3a | `trans_OwnersSubset` | 5 | 5 min | — |
| P3b | `cleanInvalidGo_OwnersSubset` | 12 | 10 min | P1, P2, P3a |
| P4 | `reviewNode_OwnersSubset` | 10 | 10 min | P1, P2 |
| P5 | `reviewLine_OwnersSubset` | 8 | 5 min | P4 |
| P6 | `reviewSteps_OwnersSubset` | 8 | 5 min | P5 |
| P7 | `reviewPass_OwnersSubset` | 6 | 5 min | P3b, P6 |
| P8 | `reviewFuel_OwnersSubset` | 8 | 5 min | P7 |
| P9 | `review_preserves_ReqFiltered` | 2 | 2 min | P8 |
| — | *(hito: S1 resuelto)* | — | — | — |
| P10a | `reqs_back_trans` (P1 débil) | 20 | 25 min | — |
| P10b | `filtered_gowners_ReqFiltered` | 15 | 15 min | P9 |
| P10c | `upFiltering_ReqFiltered` | 30 | 30 min | P10a, P10b |
| — | *(hito: S2 resuelto)* | — | — | — |
| P11a | `mergeNode_owners_subset` | 5 | 5 min | — |
| P11b | `join_preserves_ReqFiltered` | 20 | 20 min | P11a |
| — | *(hito: S3 resuelto)* | — | — | — |
| P12 | `L1_cor` | 25 | 25 min | P10c, P11b, P10a |

| **Total** | | **~200 líneas** | **~3.5 horas** | |

---

## 6. Riesgos y Mitigaciones

| Riesgo | Prob. | Impacto | Mitigación |
|--------|-------|---------|-----------|
| `rfl` no reduce lambda en `removeNode` | Media | Bajo | Usar `dsimp` + `rfl` o `simpa` |
| `by_cases h_eq : x.id = id` usa `=` sobre `PathNodeId` con `DecidableEq` | Baja | Medio | `PathNodeId` ya tiene `DecidableEq` |
| `intRange` produce lista vacía para `current_step ≤ 1` | Baja | Bajo | Ya manejado en definiciones |
| `reqs_back_trans` requiere expandir `addNode` (misma complejidad que P10c) | Media | Alto | Usar `OwnersSubset` para `filterAll` + razonamiento directo sobre `addNode` |
| `List.mem_map.mp` devuelve `f a = x` (dirección inversa) | Baja | Bajo | Usar `.symm` cuando sea necesario |

---

## 7. Qué NO está en alcance

- P3 de `Reachable.lean` (procedencia) — diferido a L7 según el plan original.
- `GPathM` no tiene `DecidableEq` — no necesario (las pruebas son sobre `List` membership, no sobre igualdad de grafos).
- `Fuel.lean` F2.c — diferido, solo lo consume L6.
- `steps_below_current` (P1 completo de `Reachable.lean`) — solo se necesita una versión débil (`reqs_back_trans`), no el teorema completo.

---

*Plan escrito por Claude (Fable 5 +  DeepSeek Pro V4 + Brain FRA v3.0) el 2026-07-04, como refinamiento del
análisis formal de los 4 `sorry` en `OwnersInvariants.lean`.*
