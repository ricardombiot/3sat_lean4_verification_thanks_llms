# Brain FRA — Plan de Ataque: 4 `sorry` en `OwnersInvariants.lean`

**Fecha:** 2026-07-04 (v2 — incorpora decisiones autonomas de Brain FRA)
**Contexto:** Fase F5 del plan [`espejo_gpathm_lema_L1.md`](./espejo_gpathm_lema_L1.md)
**Estado previo:** F1, F2(a+b), F3, F4, F6 completados (0 `sorry`). F5 con 4 `sorry`.

---

## 0. Resumen Ejecutivo

| # | Teorema | Dificultad | Estrategia |
|---|---------|-----------|-----------|
| S1 | `review_preserves_ReqFiltered` | Alta | Cadena `OwnersSubset` (9 lemas) |
| S2 | `upFiltering_ReqFiltered` | Alta | Cambio de firma + `reqs_back_trans` + `pid_safe` |
| S3 | `join_preserves_ReqFiltered` | Media | `List.mem_map.mp` + case-split `node?` |
| S4 | `L1_cor` | Media | `node?_mem` + `PairwiseOwned` a `ReqFiltered` |

### Decisiones de diseno (Brain FRA autonomo, Δconf > 0.15 en las 3)

| Decision | Resultado | Confianza |
|----------|-----------|-----------|
| Q1: Anadir `h_reach` a `upFiltering_ReqFiltered`? | **SI** | 0.88 |
| Q2: `reqs_back_trans` en `Reachable.lean`? | **SI** (propiedades del tipo con su tipo) | 0.71 |
| Q3: `steps_below_current` necesario? | **SI** (evita duplicacion en 2 consumidores) | 0.80 |

---

## 1. K-Logic: Axiomas Formales

### A1: Definicion del invariante

```
ReqFiltered(g) := ∀ d ∈ g.nodes, ∀ req ∈ reqOf(d.id.id), ∀ q ∈ d.owners,
                    q.id.step = req.step → q.id = req
```

### A2: Monotonia estructural (OwnersSubset)

```
OwnersSubset(g, g') := ∀ d ∈ g'.nodes, ∃ d' ∈ g.nodes,
                         d'.id = d.id ∧ (∀ q ∈ d.owners, q ∈ d'.owners)
```

### A3: Puente logico-estructural

```
A3: OwnersSubset(g, g') → (ReqFiltered(g) → ReqFiltered(g'))
```

**Demostrado** (4 lineas). Desacopla razonamiento estructural del invariante logico.

### A4: Reachable → backward-step property (NUEVO)

```
A4:  steps_below_current(h_reach) := ∀ n ∈ g.nodes, n.id.id.step < g.current_step
A4': reqs_back_trans(h_reach)     := ∀ n ∈ g.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step
```

Estos lemas viven en `Reachable.lean`. Necesarios para `pid_safe`.

### A5: pid anadido en addNode no viola ReqFiltered

`pid.id.step = g.current_step`. Por A4 y A4': `req.step < n.id.id.step < g.current_step = pid.id.step`
para todo nodo viejo `n`. Luego `pid.id.step ≠ req.step` → la condicion del invariante nunca se
dispara.

### A6: gowners tras filterAll estan limpios

`filterRequire` expulsa de `gowners` a cualquier `q` con `q.id.step = req.step ∧ q.id ≠ req`. Por
induccion sobre `reqs`, los `gowners` resultantes satisfacen:
`∀ req ∈ reqs, ∀ q ∈ gowners, q.id.step = req.step → q.id = req`.

### A7: Merge de owners preserva ReqFiltered

`mergeNode(a,b).owners = a.owners ++ (b.owners \ a.owners)`. Cada `q` pertenece a `a` o a `b`.
Ambos satisfacen `ReqFiltered` → la union preserva. `mergeNode_owners_subset` ya demostrado.

---

## 2. Derivation Validation

### Soundness de S1 (cadena OwnersSubset)

```
removeNode_OwnersSubset → updateAtGo_OwnersSubset → trans_OwnersSubset
  → cleanInvalidGo_OwnersSubset → reviewNode_OwnersSubset
  → reviewLine_OwnersSubset → reviewSteps_OwnersSubset
  → reviewPass_OwnersSubset → reviewFuel_OwnersSubset
  → review_OwnersSubset → review_preserves_ReqFiltered (2 lineas)
```

- `removeNode`: filtra lista, recorta parents/sons con `filter`. Lambda no toca `.id` ni
  `.owners`. ✓
- `updateAtGo`: induccion sobre `List PNodeM` (no sobre `g.nodes`). `by_cases h_eq : x.id = id`
  (Prop, disponible con `DecidableEq`). Si `h_eq`, `intersectOwners ⊆ original`. Si `¬h_eq`,
  pasa intacto. ✓
- Resto: folds/inductions componiendo con `trans_OwnersSubset`. ✓

**Validacion cruzada con `Fuel.lean`:** El patron `split` sobre `updateAtGo` funciona
(linea 80-93). La diferencia con el intento fallido: en `Fuel.lean` se opera sobre sums, no
sobre membresia (`hd : d ∈ ...`). Para membresia usamos `by_cases` Prop. ✓

### Soundness de S2 (upFiltering)

**Cambio de firma:** `upFiltering_ReqFiltered` ahora recibe `h_reach : Reachable reqOf g`.

```
Caso isValid g':
  addNode (filterAll g reqs) d title =
    let pid := { id := d, parent_id := ... }
    -- 1. Nodo nuevo: owners = g'.gowners
    --    Por filtered_gowners_ReqFiltered → limpio para reqOf d
    -- 2. Nodos viejos: owners = old_owners ++ [pid]
    --    Caso q ∈ old_owners: h_g' (filterAll preserva ReqFiltered)
    --    Caso q = pid: pid.id.step = d.step = g.current_step
    --      Por reqs_back_trans h_reach: req.step < n.id.id.step < g.current_step
    --      Luego pid.id.step ≠ req.step → invariante vacuously true
```

Sin circularidad: `Reachable → ReqFiltered` es exactamente `L1`. ✓

### Soundness de S3 (join)

```
join g1 g2 =
  nodes = map (merge con g2.node?) g1.nodes ++ filter (no en g1) g2.nodes

Caso n ∈ map g1.nodes:
  List.mem_map.mp → ∃ n1, n1 ∈ g1.nodes, mergeFn n1 = n
  Case-split node? g2 n1.id:
    none   → n = n1 → h1 n1 ...
    some m → n = mergeNode n1 m
      mergeNode_owners_subset → q ∈ n1.owners ∨ q ∈ m.owners
      h1 para n1, h2 para m (m ∈ g2.nodes por find?_mem)

Caso n ∈ filter g2.nodes:
  h2 directamente
```

### Soundness de S4 (L1_cor)

```
h_chain: IsChain g sel → (g.node? (sel j)).isSome
h_owned: PairwiseOwned g sel → sel(req.step) ∈ ownersOf(sel j) en paso req.step
h_inv := L1 reqOf h_reach : ReqFiltered reqOf g

Caso req.step = j:
  reqs_back_trans → req.step < (sel j).id.id.step = j (por IsChain)
  Contradiccion con req.step = j → omega

Caso req.step ≠ j:
  Expandir ownersAt/ownersOf → sel(req.step) ∈ n.owners para algun n ∈ g.nodes
  (sel(req.step)).id.step = req.step (por ownersAt)
  h_inv n hn req hreq (sel req.step) ... → (sel req.step).id = req ✓
```

---

## 3. Bias Correction

| Sesgo | Senal | Correccion |
|-------|-------|-----------|
| **Optimism** | "`by_cases` resuelve todo" | P2 se prueba primero. Smoke build tras cada paso. |
| **Anchoring** | Intentos con `simp` + `List.mem_map` en `join` | Usar `List.mem_map.mp` + case-split `node?`. |
| **Sunk cost** | "Ya tenemos L1 sin `h_reach`" | `_h_reach` ya existe, solo se descarta. Cambio: 1 linea. |
| **Recency** | "Pongamos `reqs_back_trans` en OwnersInvariants" | Va en `Reachable.lean` — propiedades del tipo con su tipo. |

---

## 4. Plan de Ataque: 15 Pasos

### FASE 0: Infraestructura en `Reachable.lean` (NUEVO)

| # | Tarea | Archivo | Lineas | Depende |
|---|-------|---------|--------|---------|
| P0a | `steps_below_current`: `∀ n ∈ g.nodes, n.id.id.step < g.current_step` | `Reachable.lean` | ~12 | — |
| P0b | `reqs_back_trans`: `∀ n ∈ g.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step` | `Reachable.lean` | ~25 | P0a |

```lean
-- P0a
theorem steps_below_current (h : Reachable reqOf g) :
    ∀ n ∈ g.nodes, n.id.id.step < g.current_step := by
  induction h with
  | seed d title hstep hreqs_back =>
    intro n hn; simp [GPathM.initSeed, GPathM.up, GPathM.addNode, GPathM.empty] at hn
    simp at hn; subst hn; simp [hstep]
  | up g d title hstep hreqs_back hreqs_distinct h_reach ih =>
    rcases hstep with rfl
    -- upFiltering g (reqOf d) d title = up (filterAll g (reqOf d)) d title
    -- = addNode (filterAll g (reqOf d)) d title
    -- Nodos viejos: de filterAll, que preserva nodes ⊆ g.nodes → ih + narrowing
    -- Nodo nuevo: d.step = g.current_step (paso actual antes del UP)
    ...
  | join g1 g2 hok h_reach1 h_reach2 ih1 ih2 =>
    -- join mergea nodos; cada uno viene de g1 o g2 → ih1 o ih2
    ...

-- P0b
theorem reqs_back_trans (h : Reachable reqOf g) :
    ∀ n ∈ g.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step := by
  induction h with
  | seed d title hstep hreqs_back =>
    intro n hn; simp [GPathM.initSeed, GPathM.up, GPathM.addNode, GPathM.empty] at hn
    simp at hn; subst hn; rw [hstep]; exact hreqs_back
  | up g d title hstep hreqs_back hreqs_distinct h_reach ih =>
    rcases hstep with rfl
    -- Caso nodo nuevo: hreqs_back da req.step < d.step = n.id.id.step ✓
    -- Caso nodo viejo: ih (tras filterAll, que preserva id.id y reqOf) ✓
    ...
  | join g1 g2 hok h_reach1 h_reach2 ih1 ih2 =>
    -- Cada nodo en join viene de g1 o g2 → ih1 o ih2 ✓
    ...
```

---

### FASE 1: Cadena `OwnersSubset` (resuelve S1)

| # | Tarea | Archivo | Lineas |
|---|-------|---------|--------|
| P1 | `removeNode_OwnersSubset` | `OwnersInvariants.lean` | ~10 |
| P2 | `updateAtGo_OwnersSubset` (con `by_cases h_eq : x.id = id` Prop) | `OwnersInvariants.lean` | ~15 |
| P3a | `trans_OwnersSubset` | `OwnersInvariants.lean` | ~5 |
| P3b | `cleanInvalidGo_OwnersSubset` | `OwnersInvariants.lean` | ~12 |
| P4 | `reviewNode_OwnersSubset` | `OwnersInvariants.lean` | ~10 |
| P5 | `reviewLine_OwnersSubset` | `OwnersInvariants.lean` | ~8 |
| P6 | `reviewSteps_OwnersSubset` | `OwnersInvariants.lean` | ~8 |
| P7 | `reviewPass_OwnersSubset` | `OwnersInvariants.lean` | ~6 |
| P8 | `reviewFuel_OwnersSubset` | `OwnersInvariants.lean` | ~8 |
| P9 | `review_preserves_ReqFiltered` (= 2 lineas) | `OwnersInvariants.lean` | ~2 |

#### P1

```lean
private theorem removeNode_OwnersSubset (g : GPathM) (id : PathNodeId) :
    OwnersSubset g (removeNode g id) := by
  intro d hd
  dsimp [removeNode] at hd
  rcases List.mem_map.mp hd with ⟨d_orig, hd_orig_mem, hd_eq⟩
  have hd_orig_mem' := (List.mem_filter.mp hd_orig_mem).left
  refine ⟨d_orig, hd_orig_mem', ?_, ?_⟩
  · calc
      d_orig.id = ((fun n => { n with parents := n.parents.filter (· != id),
        sons := n.sons.filter (· != id) }) d_orig).id := rfl
      _ = d.id := by rw [hd_eq]
  · intro q hq
    have h_ow : d.owners = d_orig.owners := by
      calc
        d.owners = ((fun n => { n with parents := n.parents.filter (· != id),
          sons := n.sons.filter (· != id) }) d_orig).owners := by rw [hd_eq.symm]
        _ = d_orig.owners := by dsimp
    rw [h_ow] at hq; exact hq
```

#### P2 — PUNTO CRITICO

```lean
private theorem updateAtGo_OwnersSubset (g : GPathM) (id : PathNodeId)
    (f : PNodeM → PNodeM) (h_narrow : ∀ n q, q ∈ (f n).owners → q ∈ n.owners) :
    OwnersSubset g {g with nodes := updateAtGo id f g.nodes} := by
  intro d hd
  dsimp at hd
  induction g.nodes generalizing d with
  | nil => simp at hd
  | cons x xs ih =>
    unfold updateAtGo at hd
    by_cases h_eq : x.id = id
    · simp [h_eq] at hd
      rcases hd with (rfl | hd')
      · refine ⟨x, by simp, rfl, h_narrow x⟩
      · rcases ih hd' with ⟨d', hd', h_id, h_sub⟩
        exact ⟨d', List.mem_cons_of_mem _ hd', h_id, h_sub⟩
    · simp [h_eq] at hd
      rcases hd with (rfl | hd')
      · exact ⟨x, by simp, rfl, λ _ h => h⟩
      · rcases ih hd' with ⟨d', hd', h_id, h_sub⟩
        exact ⟨d', List.mem_cons_of_mem _ hd', h_id, h_sub⟩
```

**Nota:** `simp [h_eq]` con `h_eq : x.id = id` (Prop) funciona porque `simp` usa `=` para
reescribir. El `split`/`match` sobre Bool `(x.id == id)` era lo que fallaba.

#### P3a

```lean
private theorem trans_OwnersSubset (hAB : OwnersSubset a b) (hBC : OwnersSubset b c) :
    OwnersSubset a c := by
  intro d hd
  rcases hBC d hd with ⟨d', hd', h_id, h_sub⟩
  rcases hAB d' hd' with ⟨d'', hd'', h_id', h_sub'⟩
  refine ⟨d'', hd'', ?_, ?_⟩
  · rw [← h_id, h_id']
  · intro q hq; apply h_sub'; apply h_sub; exact hq
```

#### P3b

```lean
private theorem cleanInvalidGo_OwnersSubset (ids : List PathNodeId) (g : GPathM) :
    OwnersSubset g (cleanInvalidGo g ids) := by
  induction ids generalizing g with
  | nil => simp [OwnersSubset, cleanInvalidGo]
  | cons id rest ih =>
    simp [cleanInvalidGo]
    split
    · exact ih g
    · next d hd =>
      let f := fun n => { n with owners := intersectOwners n.owners g.gowners }
      have h_narrow : ∀ n q, q ∈ (f n).owners → q ∈ n.owners := by
        intro n q hq; simp [f, intersectOwners] at hq; exact hq.1
      let g1 := {g with nodes := updateAtGo id f g.nodes}
      have h_g1 : OwnersSubset g g1 := updateAtGo_OwnersSubset g id f h_narrow
      split
      · exact trans_OwnersSubset h_g1 (ih g1)
      · have h_rem : OwnersSubset g1 (removeNode g1 id) := removeNode_OwnersSubset g1 id
        exact trans_OwnersSubset (trans_OwnersSubset h_g1 h_rem) (ih (removeNode g1 id))
```

#### P4

```lean
private theorem reviewNode_OwnersSubset (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) : OwnersSubset g (reviewNode g nb id) := by
  simp [reviewNode]
  split
  · simp [OwnersSubset]
  · next d hd =>
    split
    · let f := fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) }
      have h_narrow : ∀ n q, q ∈ (f n).owners → q ∈ n.owners := by
        intro n q hq; simp [f, intersectOwners] at hq; exact hq.1
      let g1 := {g with nodes := updateAtGo id f g.nodes}
      have h_g1 := updateAtGo_OwnersSubset g id f h_narrow
      split
      · exact h_g1
      · exact trans_OwnersSubset h_g1 (removeNode_OwnersSubset g1 id)
    · exact removeNode_OwnersSubset g id
```

#### P5-P8 — Folds (patron de `Fuel.lean`)

```lean
private theorem reviewLine_OwnersSubset (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int) :
    OwnersSubset g (reviewLine g nb k) := by
  dsimp [reviewLine]
  induction ((g.line k).map (·.id)) generalizing g with
  | nil => simp [OwnersSubset]
  | cons id tail ih =>
    simp
    have h_step := reviewNode_OwnersSubset g nb id
    exact trans_OwnersSubset h_step (ih _)

private theorem reviewSteps_OwnersSubset (g : GPathM) (nb : PNodeM → List PathNodeId)
    (ks : List Int) : OwnersSubset g (reviewSteps g nb ks) := by
  induction ks generalizing g with
  | nil => simp [OwnersSubset, reviewSteps]
  | cons k ks ih =>
    simp [reviewSteps]
    split
    · have h_line := reviewLine_OwnersSubset g nb k
      exact trans_OwnersSubset h_line (ih _)
    · simp [OwnersSubset]

private theorem reviewPass_OwnersSubset (g : GPathM) : OwnersSubset g (reviewPass g) := by
  dsimp [reviewPass]
  have h_cl := cleanInvalidGo_OwnersSubset (g.nodes.map (·.id)) g
  have h_par := reviewSteps_OwnersSubset (cleanInvalid g) (·.parents)
    (intRange 1 (g.current_step - 1))
  have h_son := reviewSteps_OwnersSubset (reviewParents (cleanInvalid g)) (·.sons)
    ((intRange 1 (g.current_step - 2)).reverse)
  exact trans_OwnersSubset (trans_OwnersSubset h_cl h_par) h_son

private theorem reviewFuel_OwnersSubset (fuel : Nat) (g : GPathM) :
    OwnersSubset g (reviewFuel fuel g) := by
  induction fuel generalizing g with
  | zero => simp [OwnersSubset, reviewFuel]
  | succ fuel ih =>
    simp [reviewFuel]
    split
    · split
      · have h_pass := reviewPass_OwnersSubset g
        exact trans_OwnersSubset h_pass (ih _)
      · simp [OwnersSubset]
    · simp [OwnersSubset]

private theorem review_OwnersSubset (g : GPathM) : OwnersSubset g (review g) := by
  dsimp [review]; exact reviewFuel_OwnersSubset (measure g + 1) g
```

#### P9 — 2 lineas

```lean
private theorem review_preserves_ReqFiltered (h : ReqFiltered reqOf g) :
    ReqFiltered reqOf (GPathM.review g) :=
  OwnersSubset_preserves_ReqFiltered reqOf h (review_OwnersSubset g)
```

---

### FASE 2: `upFiltering` (resuelve S2)

| # | Tarea | Archivo | Lineas |
|---|-------|---------|--------|
| P10a | Cambiar firma de `upFiltering_ReqFiltered` (+ `h_reach`) | `OwnersInvariants.lean` | ~1 |
| P10b | `pid_safe` (usa P0b) | `OwnersInvariants.lean` | ~10 |
| P10c | `filtered_gowners_ReqFiltered` (usa P9) | `OwnersInvariants.lean` | ~15 |
| P10d | Cuerpo de `upFiltering_ReqFiltered` | `OwnersInvariants.lean` | ~30 |
| — | Actualizar `L1.up`: pasar `h_reach` en vez de `_h_reach` | `OwnersInvariants.lean` | ~1 |

#### P10b

```lean
theorem pid_safe (h_reach : Reachable reqOf g) (n : PNodeM) (hn : n ∈ g.nodes)
    (pid : PathNodeId) (hpid_step : pid.id.step = g.current_step) :
    ∀ req ∈ reqOf n.id.id, pid.id.step ≠ req.step := by
  have h_back := reqs_back_trans reqOf h_reach n hn
  have h_below := steps_below_current reqOf h_reach n hn
  intro req hreq
  have hlt1 := h_back req hreq   -- req.step < n.id.id.step
  have hlt2 := h_below            -- n.id.id.step < g.current_step
  rw [hpid_step]
  omega
```

#### P10c

```lean
theorem filtered_gowners_ReqFiltered (h : ReqFiltered reqOf g) (reqs : List NodeId)
    (hdistinct : ∀ r1 r2, r1 ∈ reqs → r2 ∈ reqs → r1.step = r2.step → r1 = r2) :
    ∀ req ∈ reqs, ∀ q ∈ (filterAll g reqs).gowners, q.id.step = req.step → q.id = req := by
  intro req hreq q hq hstep
  induction reqs generalizing g with
  | nil => simp [filterAll] at hq; exact absurd hq (by simp)
  | cons r rs ih =>
    -- filterRequire g r borra de gowners los q con q.id.step = r.step ∧ q.id ≠ r
    -- Luego foldl continua, y review estrecha
    ...
```

#### P10d — FIRMA NUEVA

```lean
theorem upFiltering_ReqFiltered (h : ReqFiltered reqOf g) (h_reach : Reachable reqOf g)
    (d : NodeId) (title : String) (hstep : d.step = g.current_step)
    (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step)
    (hreqs_distinct : ∀ r1 r2, r1 ∈ reqOf d → r2 ∈ reqOf d → r1.step = r2.step → r1 = r2) :
    ReqFiltered reqOf (GPathM.upFiltering g (reqOf d) d title) := by
  dsimp [GPathM.upFiltering, GPathM.up]
  let g' := GPathM.filterAll g (reqOf d)
  have h_g' : ReqFiltered reqOf g' := filterAll_preserves_ReqFiltered reqOf h (reqOf d)
  split
  · -- isValid g' → expandir addNode
    dsimp [GPathM.addNode]
    intro n hn req hreq q hq hstep_q
    -- n puede ser el nuevo nodo o uno viejo
    -- Caso 1: n es newNode → hq: q ∈ g'.gowners → filtered_gowners_ReqFiltered
    -- Caso 2: n es nodo viejo con owners = old_owners ++ [pid]
    --   Caso 2a: q ∈ old_owners → h_g'
    --   Caso 2b: q = pid → pid_safe → vacuously true
    ...
  · exact h_g'

-- Actualizar L1.up:
--   | up g d title hstep hreqs_back hreqs_distinct h_reach ih =>
--     exact upFiltering_ReqFiltered reqOf ih h_reach d title hstep hreqs_back hreqs_distinct
```

---

### FASE 3: `join` (resuelve S3)

| # | Tarea | Archivo | Lineas |
|---|-------|---------|--------|
| P11a | `node?_mem` lemma | `OwnersInvariants.lean` | ~5 |
| P11b | `join_preserves_ReqFiltered` | `OwnersInvariants.lean` | ~20 |

#### P11a

```lean
theorem node?_mem (g : GPathM) (pid : PathNodeId) (h : (g.node? pid).isSome) :
    (g.node? pid).get h ∈ g.nodes := by
  dsimp [node?] at h ⊢
  induction g.nodes with
  | nil => simp at h
  | cons x xs ih =>
    simp [List.find?] at h ⊢
    split at h <;> simp at h ⊢
    · injection h with h; subst h; exact List.mem_cons_self _ _
    · exact List.mem_cons_of_mem _ (ih h)
```

#### P11b

```lean
theorem join_preserves_ReqFiltered (h1 : ReqFiltered reqOf g1)
    (h2 : ReqFiltered reqOf g2) (hok : GPathM.okJoin g1 g2) :
    ReqFiltered reqOf (GPathM.join g1 g2) := by
  dsimp [ReqFiltered, GPathM.join]
  intro n hn req hreq q hq hstep
  simp at hn
  rcases hn with (hn_map | hn_filter)
  · rcases List.mem_map.mp hn_map with ⟨n1, hn1, hn_eq⟩
    match hg2 : GPathM.node? g2 n1.id with
    | none =>
      have : (match GPathM.node? g2 n1.id with | some m => mergeNode n1 m | none => n1) = n1 :=
        by simp [hg2]
      rw [this] at hn_eq; subst hn_eq
      exact h1 n1 hn1 req hreq q hq hstep
    | some m =>
      have : (match GPathM.node? g2 n1.id with | some m' => mergeNode n1 m' | none => n1) = mergeNode n1 m :=
        by simp [hg2]
      rw [this] at hn_eq; subst hn_eq
      rcases mergeNode_owners_subset n1 m q hq with (hq1 | hq2)
      · exact h1 n1 hn1 req hreq q hq1 hstep
      · have hm : m ∈ g2.nodes := by
          have h_some : (GPathM.node? g2 n1.id).isSome := by rw [hg2]; exact rfl
          exact node?_mem g2 n1.id h_some
        exact h2 m hm req hreq q hq2 hstep
  · simp at hn_filter
    rcases hn_filter with ⟨hn_mem, _⟩
    exact h2 n hn_mem req hreq q hq hstep
```

---

### FASE 4: `L1_cor` (resuelve S4)

| # | Tarea | Archivo | Lineas |
|---|-------|---------|--------|
| P12 | `L1_cor` | `OwnersInvariants.lean` | ~22 |

#### P12

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
    -- req.step = j: contradiction with reqs_back_trans
    ...
    omega
  · -- req.step ≠ j: PairwiseOwned gives owner, ReqFiltered forces identity
    have h_owner : sel req.step ∈ ownersAt (ownersOf g (sel j)) req.step :=
      h_owned (req.step) j h_req_step_pos hj_lo h_req_step_lt hj_hi hij
    -- Expand ownersAt, ownersOf
    ...
```

**Sub-lemas necesarios:**
- `ownersAt_step` — `q ∈ ownersAt owners k → q.id.step = k`
- `ownersOf_mem` — `q ∈ ownersOf g pid → q ∈ (g.node? pid).get _ |>.owners`

---

## 5. Orden de Trabajo

| # | Tarea | Archivo | Lineas | Tiempo |
|---|-------|---------|--------|--------|
| P0a | `steps_below_current` | `Reachable.lean` | 12 | 20 min |
| P0b | `reqs_back_trans` | `Reachable.lean` | 25 | 30 min |
| P1 | `removeNode_OwnersSubset` | `OwnersInvariants.lean` | 10 | 10 min |
| P2 | `updateAtGo_OwnersSubset` | `OwnersInvariants.lean` | 15 | 20 min |
| P3a | `trans_OwnersSubset` | `OwnersInvariants.lean` | 5 | 5 min |
| P3b | `cleanInvalidGo_OwnersSubset` | `OwnersInvariants.lean` | 12 | 10 min |
| P4 | `reviewNode_OwnersSubset` | `OwnersInvariants.lean` | 10 | 10 min |
| P5 | `reviewLine_OwnersSubset` | `OwnersInvariants.lean` | 8 | 5 min |
| P6 | `reviewSteps_OwnersSubset` | `OwnersInvariants.lean` | 8 | 5 min |
| P7 | `reviewPass_OwnersSubset` | `OwnersInvariants.lean` | 6 | 5 min |
| P8 | `reviewFuel_OwnersSubset` | `OwnersInvariants.lean` | 8 | 5 min |
| P9 | `review_preserves_ReqFiltered` | `OwnersInvariants.lean` | 2 | 2 min |
| — | Hito S1 resuelto | | | |
| P10a | Cambiar firma `upFiltering_ReqFiltered` | `OwnersInvariants.lean` | 1 | 1 min |
| P10b | `pid_safe` | `OwnersInvariants.lean` | 10 | 10 min |
| P10c | `filtered_gowners_ReqFiltered` | `OwnersInvariants.lean` | 15 | 20 min |
| P10d | Cuerpo `upFiltering_ReqFiltered` | `OwnersInvariants.lean` | 30 | 35 min |
| — | Hito S2 resuelto | | | |
| P11a | `node?_mem` | `OwnersInvariants.lean` | 5 | 5 min |
| P11b | `join_preserves_ReqFiltered` | `OwnersInvariants.lean` | 20 | 20 min |
| — | Hito S3 resuelto | | | |
| P12 | `L1_cor` | `OwnersInvariants.lean` | 22 | 30 min |
| — | TODO resuelto — 0 sorry | | | |

| **Total** | | **~224 lineas** | **~4.5 horas** |

---

## 6. Riesgos y Mitigaciones

| Riesgo | Prob. | Impacto | Mitigacion |
|--------|-------|---------|-----------|
| `by_cases h_eq : x.id = id` no reduce con `simp` en P2 | Baja | Alto | Usar `rw [h_eq]` en el `if` explicitamente |
| `List.mem_map.mp` no existe en Std4 | Baja | Alto | Induccion inline con `cases` |
| `reqs_back_trans` (P0b) requiere expandir `addNode` en el caso `up` | Media | Medio | `filterAll` estrecha → `ih` aplica a nodos viejos. Nodo nuevo: `hreqs_back` directo |
| `L1_cor` requiere `ownersAt_step` y `ownersOf_mem` no previstos | Baja | Bajo | Ambos son `simp` + `List.mem_filter` (3-5 lineas cada uno) |
| `filtered_gowners_ReqFiltered` (P10c) induccion compleja | Media | Medio | Separar en: `filterRequire_gowners` + `filterAll_gowners` + `review` no anade gowners |

---

## 7. Que NO esta en alcance

- P3 de `Reachable.lean` (procedencia) — diferido a L7
- `GPathM` `DecidableEq` — no necesario (pruebas sobre `List` membership)
- `Fuel.lean` F2.c — diferido, solo L6 lo consume
- `steps_below_current` completo con `current_step` recursivo — solo version debil

---

## 8. Cambios de Diseno Respecto al Plan Original

| Cambio | Razon | Confianza |
|--------|-------|-----------|
| `upFiltering_ReqFiltered` recibe `h_reach : Reachable reqOf g` | `pid_safe` necesita `reqs_back_trans` (no disponible en `ReqFiltered`) | 0.88 |
| `reqs_back_trans` y `steps_below_current` en `Reachable.lean` | Propiedades del tipo con su tipo; reusables por L7 | 0.71 / 0.80 |
| `join_preserves_ReqFiltered` usa `List.mem_map.mp` + case-split `node?` | Evita el `getD` y los problemas de `List.Mem` constructor names | 0.85 |
| `L1.up` pasa `h_reach` en vez de `_h_reach` | 1 linea de cambio; sin impacto en clientes | 0.95 |

---

*Plan v2 actualizado por Brain FRA v3.0 (DeepSeek Pro V4 + Claude) el 2026-07-04,
incorporando 3 decisiones autonomas de diseno y refinamiento de estrategias para `join` y `L1_cor`.*
