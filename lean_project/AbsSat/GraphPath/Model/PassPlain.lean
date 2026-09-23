-- lean_project/AbsSat/GraphPath/Model/PassPlain.lean
import AbsSat.GraphPath.Model.PassSons
import AbsSat.GraphPath.Model.CleanTwoPhase

/-!
# Las pasadas de coherencia, sin versiones «vivas»

`PassCtx` y `PassSons` demuestran las pasadas de padres e hijos con invariantes **vivos** (`SegGoodL`,
`I1L`, `I1sL`): con el `cleanInvalid` secuencial las tablas guardaban ids de nodos ya eliminados, y
las propiedades tenían que decir «entrada común *viva*», «owner *vivo* un paso por debajo»…

Con `cleanInvalid₂` (v181 §6) las tablas no guardan ids muertos (`owners_live_cleanInvalid₂`). Aquí:

* `OwnLive`: todo owner de una tabla, en un paso dentro de rango, es un nodo;
* con `OwnLive`, las versiones vivas **son** las simples: `segGood_iff`, `i1_iff`, `i1s_iff`;
* `OwnLive` sale de `cleanInvalid₂` (`ownLive_cleanInvalid₂`) y lo conservan las dos pasadas
  (`ownLive_reviewNode_parents/sons`), porque ninguna de las dos elimina nodos;
* `PStateG`, el estado de la pasada con `SegGood`, `I1`, `I1s` simples, y
  `pstateG_reviewParents`, `pstateG_reviewSons`: las dos pasadas enteras lo conservan.

Las pruebas nodo a nodo siguen siendo las de `PassCtx`/`PassSons`; lo que cambia es el enunciado, que
habla ya del mismo `SegGood` que la escalera (`TopGoodLadder.ReaderSegGood`).
-/

namespace AbsSat.GraphPath.Model.PassPlain

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PassCtx
open AbsSat.GraphPath.Model.PassSons
open AbsSat.GraphPath.Model.TopGoodUp (SegGood)

/-- **Tablas vivas**: un owner en un paso dentro de rango es un nodo. -/
def OwnLive (g : GPathM) : Prop :=
  ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, 0 ≤ w.id.step → w.id.step ≤ g.current_step - 1 →
    (g.node? w).isSome

/-- **Un paso por debajo, los owners son padres.** -/
def I1 (g : GPathM) : Prop :=
  ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, 0 ≤ w.id.step → w.id.step ≤ g.current_step - 1 →
    w.id.step + 1 = y.id.step → w ∈ ny.parents

/-- **Un paso por encima, los owners son hijos.** -/
def I1s (g : GPathM) : Prop :=
  ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, 0 ≤ w.id.step → w.id.step ≤ g.current_step - 1 →
    w.id.step = y.id.step + 1 → w ∈ ny.sons

-- ============================================================
-- Con tablas vivas, lo vivo es lo simple
-- ============================================================

theorem segGood_iff (g : GPathM) (hol : OwnLive g) : SegGood g ↔ SegGoodL g := by
  constructor
  · intro h sel lo hi hlo hlh hhi hpc hpo i hi0 hic hout
    obtain ⟨r, hrs, hr⟩ := h sel lo hi hlo hlh hhi hpc hpo i hi0 hic hout
    obtain ⟨nlo, hnlo⟩ := Option.isSome_iff_exists.mp (hpc.1 lo (Int.le_refl _) hlh).1
    have hlive := hol (sel lo) nlo hnlo r (hr lo (Int.le_refl _) hlh nlo hnlo)
      (by rw [hrs]; exact hi0) (by rw [hrs]; exact hic)
    exact ⟨r, hrs, hlive, hr⟩
  · intro h sel lo hi hlo hlh hhi hpc hpo i hi0 hic hout
    obtain ⟨r, hrs, _, hr⟩ := h sel lo hi hlo hlh hhi hpc hpo i hi0 hic hout
    exact ⟨r, hrs, hr⟩

/-- A node's step is in range (`SNN`, `below`). -/
theorem node_step_range (g : GPathM) (hsnn : SelfOwn.SNN g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (w : PathNodeId) (nw : PNodeM)
    (hnw : g.node? w = some nw) : 0 ≤ w.id.step ∧ w.id.step ≤ g.current_step - 1 := by
  have hmem : nw ∈ g.nodes := List.mem_of_find?_eq_some hnw
  have hid : nw.id = w := node?_id_eq g w nw hnw
  have h0 := hsnn nw hmem
  have h1 := hbelow nw hmem
  rw [hid] at h0 h1
  exact ⟨h0, by omega⟩

theorem i1_iff (g : GPathM) (hol : OwnLive g) (hsnn : SelfOwn.SNN g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) : I1 g ↔ I1L g := by
  constructor
  · intro h y ny hy w hw hlive hst
    obtain ⟨nw, hnw⟩ := Option.isSome_iff_exists.mp hlive
    obtain ⟨h0, hc⟩ := node_step_range g hsnn hbelow w nw hnw
    exact h y ny hy w hw h0 hc hst
  · intro h y ny hy w hw h0 hc hst
    exact h y ny hy w hw (hol y ny hy w hw h0 hc) hst

theorem i1s_iff (g : GPathM) (hol : OwnLive g) (hsnn : SelfOwn.SNN g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) : I1s g ↔ I1sL g := by
  constructor
  · intro h y ny hy w hw hlive hst
    obtain ⟨nw, hnw⟩ := Option.isSome_iff_exists.mp hlive
    obtain ⟨h0, hc⟩ := node_step_range g hsnn hbelow w nw hnw
    exact h y ny hy w hw h0 hc hst
  · intro h y ny hy w hw h0 hc hst
    exact h y ny hy w hw (hol y ny hy w hw h0 hc) hst

-- ============================================================
-- Tablas vivas: de dónde salen y quién las conserva
-- ============================================================

/-- **`cleanInvalid₂` deja las tablas vivas** (si el grafo queda válido y la global eran nodos). -/
theorem ownLive_cleanInvalid₂ (g : GPathM) (hgn : GownersNodes.GN g)
    (hv : isValid (cleanInvalid₂ g) = true) : OwnLive (cleanInvalid₂ g) := by
  intro y ny hy w hw h0 hc
  have hmem : ny ∈ (cleanInvalid₂ g).nodes := List.mem_of_find?_eq_some hy
  have hs := hasStepEntry_of_isValid _ hv w.id.step h0 (by omega)
  have hg := CleanTwoPhase.owners_in_gowners_cleanInvalid₂ g ny hmem w hw hs
  exact (GownersNodes.hasNode_iff _ w).mp (GownersNodes.GN_cleanInvalid₂ g hgn w hg)

/-- Common shape: a `reviewNode` that keeps everything alive keeps the tables alive. -/
theorem ownLive_of_live (g : GPathM) (nb : PNodeM → List PathNodeId) (x : PathNodeId)
    (hnd : NodupIds g) (hol : OwnLive g)
    (hlive : ∀ r, (g.node? r).isSome → ((reviewNode g nb x).node? r).isSome) :
    OwnLive (reviewNode g nb x) := by
  have hpr := pruned_reviewNode nb x g
  intro y ny hy w hw h0 hc
  have hmem : ny ∈ (reviewNode g nb x).nodes := List.mem_of_find?_eq_some hy
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived ny hmem
  have hyid : ny.id = y := node?_id_eq _ y ny hy
  have hgn : g.node? y = some n := by
    rw [← hyid, hid]; exact node?_of_mem hnd n hn
  rw [hpr.step_eq] at hc
  exact hlive w (hol y n hgn w (hown w hw) h0 hc)

theorem ownLive_reviewNode_parents (g : GPathM) (h : PState g) (hol : OwnLive g) (x : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1) :
    OwnLive (reviewNode g (·.parents) x) :=
  ownLive_of_live g _ x h.nd hol
    (live_reviewNode_parents g h.sgl h.i1 h.i1s h.self h.lsym h.nr x hx1 hxc)

theorem ownLive_reviewNode_sons (g : GPathM) (h : PState g) (hol : OwnLive g) (x : PathNodeId)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2) :
    OwnLive (reviewNode g (·.sons) x) :=
  ownLive_of_live g _ x h.nd hol
    (live_reviewNode_sons g h.sgl h.i1 h.i1s h.self h.lsymU h.rootz x hx0 hxl)

-- ============================================================
-- El estado de la pasada, en su versión simple
-- ============================================================

/-- **Lo que un estado de las pasadas lleva, sin versiones vivas**: `SegGood`, `I1`, `I1s` simples y
las tablas vivas, más el resto de `PState`. -/
structure PStateG (g : GPathM) : Prop where
  nd : NodupIds g
  sg : SegGood g
  i1 : I1 g
  i1s : I1s g
  ol : OwnLive g
  plive : PLive g
  slive : SLive g
  self : SelfL g
  lsym : SegReview.LocSym g
  lsymU : SegReview.LocSymUp g
  nr : Parents.NotRoot g
  below : ∀ n ∈ g.nodes, n.id.id.step < g.current_step
  oos : SelfOwn.OOS g
  snn : SelfOwn.SNN g
  rootz : Sons.RootAtZero g

theorem PStateG.toP {g : GPathM} (h : PStateG g) : PState g where
  nd := h.nd
  sgl := (segGood_iff g h.ol).mp h.sg
  i1 := (i1_iff g h.ol h.snn h.below).mp h.i1
  i1s := (i1s_iff g h.ol h.snn h.below).mp h.i1s
  plive := h.plive
  slive := h.slive
  self := h.self
  lsym := h.lsym
  lsymU := h.lsymU
  nr := h.nr
  below := h.below
  oos := h.oos
  snn := h.snn
  rootz := h.rootz

theorem PStateG.ofP {g : GPathM} (h : PState g) (hol : OwnLive g) : PStateG g where
  nd := h.nd
  sg := (segGood_iff g hol).mpr h.sgl
  i1 := (i1_iff g hol h.snn h.below).mpr h.i1
  i1s := (i1s_iff g hol h.snn h.below).mpr h.i1s
  ol := hol
  plive := h.plive
  slive := h.slive
  self := h.self
  lsym := h.lsym
  lsymU := h.lsymU
  nr := h.nr
  below := h.below
  oos := h.oos
  snn := h.snn
  rootz := h.rootz

theorem pstateG_reviewNode (hLS : LocSymStable) (g : GPathM) (h : PStateG g) (x : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1) :
    PStateG (reviewNode g (·.parents) x) :=
  PStateG.ofP (pstate_reviewNode hLS g h.toP x hx1 hxc)
    (ownLive_reviewNode_parents g h.toP h.ol x hx1 hxc)

theorem pstateG_reviewNode_sons (hLS : LocSymStableS) (g : GPathM) (h : PStateG g) (x : PathNodeId)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2) :
    PStateG (reviewNode g (·.sons) x) :=
  PStateG.ofP (pstate_reviewNode_sons hLS g h.toP x hx0 hxl)
    (ownLive_reviewNode_sons g h.toP h.ol x hx0 hxl)

theorem pstateG_reviewSteps (hLS : LocSymStable) (c : Int) :
    ∀ (ks : List Int) (g : GPathM), PStateG g → g.current_step - 1 = c →
      (∀ k ∈ ks, 1 ≤ k ∧ k ≤ c) → PStateG (reviewSteps g (·.parents) ks) := by
  have hfold : ∀ (k : Int), 1 ≤ k → ∀ (L : List PathNodeId) (g : GPathM), PStateG g →
      k ≤ g.current_step - 1 → (∀ id ∈ L, id.id.step = k) →
      PStateG (L.foldl (fun g id => reviewNode g (·.parents) id) g) := by
    intro k hk1 L
    induction L with
    | nil => intro g h _ _; exact h
    | cons x xs ih =>
      intro g h hkc hL
      have hxs := hL x List.mem_cons_self
      have hstep := (pruned_reviewNode (·.parents) x g).step_eq
      exact ih _ (pstateG_reviewNode hLS g h x (by omega) (by omega)) (by rw [hstep]; exact hkc)
        (fun id hid => hL id (List.mem_cons_of_mem _ hid))
  intro ks
  induction ks with
  | nil => intro g h _ _; exact h
  | cons k ks ih =>
    intro g h hc hks
    unfold reviewSteps
    split
    · have hk := hks k List.mem_cons_self
      have hstep := (pruned_reviewLine (·.parents) k g).step_eq
      refine ih _ ?_ (by rw [hstep]; exact hc) (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      refine hfold k hk.1 _ g h (by omega) (fun id hid => ?_)
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hid
      exact eq_of_beq (List.mem_filter.mp hn).2
    · exact h

theorem pstateG_reviewSteps_sons (hLS : LocSymStableS) (c : Int) :
    ∀ (ks : List Int) (g : GPathM), PStateG g → g.current_step - 2 = c →
      (∀ k ∈ ks, 0 ≤ k ∧ k ≤ c) → PStateG (reviewSteps g (·.sons) ks) := by
  have hfold : ∀ (k : Int), 0 ≤ k → ∀ (L : List PathNodeId) (g : GPathM), PStateG g →
      k ≤ g.current_step - 2 → (∀ id ∈ L, id.id.step = k) →
      PStateG (L.foldl (fun g id => reviewNode g (·.sons) id) g) := by
    intro k hk0 L
    induction L with
    | nil => intro g h _ _; exact h
    | cons x xs ih =>
      intro g h hkc hL
      have hxs := hL x List.mem_cons_self
      have hstep := (pruned_reviewNode (·.sons) x g).step_eq
      exact ih _ (pstateG_reviewNode_sons hLS g h x (by omega) (by omega)) (by rw [hstep]; exact hkc)
        (fun id hid => hL id (List.mem_cons_of_mem _ hid))
  intro ks
  induction ks with
  | nil => intro g h _ _; exact h
  | cons k ks ih =>
    intro g h hc hks
    unfold reviewSteps
    split
    · have hk := hks k List.mem_cons_self
      have hstep := (pruned_reviewLine (·.sons) k g).step_eq
      refine ih _ ?_ (by rw [hstep]; exact hc) (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      refine hfold k hk.1 _ g h (by omega) (fun id hid => ?_)
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hid
      exact eq_of_beq (List.mem_filter.mp hn).2
    · exact h

/-- **La pasada de padres entera conserva `PStateG`**: `SegGood` simple y tablas vivas. -/
theorem pstateG_reviewParents (hLS : LocSymStable) (g : GPathM) (h : PStateG g) :
    PStateG (reviewParents g) :=
  pstateG_reviewSteps hLS (g.current_step - 1) _ g h rfl
    (fun _ hk => ⟨mem_intRange_lower hk, mem_intRange_upper hk⟩)

/-- **La pasada de hijos entera conserva `PStateG`.** -/
theorem pstateG_reviewSons (hLS : LocSymStableS) (g : GPathM) (h : PStateG g) :
    PStateG (reviewSons g) :=
  pstateG_reviewSteps_sons hLS (g.current_step - 2) _ g h rfl
    (fun _ hk => ⟨mem_intRange_lower (List.mem_reverse.mp hk),
      mem_intRange_upper (List.mem_reverse.mp hk)⟩)

/-- **Una vuelta del review, a partir de la salida de `cleanInvalid₂`**: si allí vale `PStateG`, las
dos pasadas lo conservan y la vuelta entera (`reviewPass`) lo deja. Lo que falta para encadenar las
vueltas es establecer `PStateG` a la salida de `cleanInvalid₂`; las tablas vivas ya salen de ella
(`ownLive_cleanInvalid₂`). -/
theorem pstateG_reviewPass (hLS : LocSymStable) (hLSs : LocSymStableS) (g : GPathM)
    (h : PStateG (cleanInvalid₂ g)) : PStateG (reviewPass g) :=
  pstateG_reviewSons hLSs _ (pstateG_reviewParents hLS _ h)

/-- info: 'AbsSat.GraphPath.Model.PassPlain.pstateG_reviewPass' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms pstateG_reviewPass

/-- info: 'AbsSat.GraphPath.Model.PassPlain.ownLive_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ownLive_cleanInvalid₂

end AbsSat.GraphPath.Model.PassPlain
