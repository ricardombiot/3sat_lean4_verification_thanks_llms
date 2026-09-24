-- lean_project/AbsSat/GraphPath/Model/SymInvariant.lean
import AbsSat.GraphPath.Model.CompatLoss
import AbsSat.GraphPath.Model.CleanTwoPhase

/-!
# La simetría de la posesión, invariante del review simétrico (plan `review_simetrico.md`, B3)

Con el espejo (`GPathM.mirrorDrop`, Julia `SYM_MODE = :on`) cada corte se escribe en las dos tablas:
cuando `x` deja fuera a `w`, `w` deja fuera a `x`. La simetría entre nodos vivos
(`Threaded.OwnSymmetric`) deja entonces de ser una propiedad de los estados finales y pasa a ser un
**invariante** de todo el review:

* `OwnSymmetric_reviewNode`: un paso de una pasada la conserva (con `NodupIds`), sin más;
* `OwnSymmetric_cleanInvalid₂`: la purga no toca tablas, y en su punto fijo cada nodo vivo está en su
  propio corte (`OOS`), así que el corte global no lo quita de ninguna tabla;
* el barrido agresivo la conserva: con simetría, su rama «asimétrica» no se dispara
  (`aggPair_asym_never`) y la «inconsistente» quita las dos direcciones;
* y con ello `reviewPass`, `review`, `reviewAgg` y `filterAllAgg`, siempre que el resultado sea
  válido (si no lo es, la máquina lo descarta).
-/

namespace AbsSat.GraphPath.Model.SymInvariant

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Threaded (OwnSymmetric)
open AbsSat.GraphPath.Model.AggressiveReview

-- ============================================================
-- Un paso de una pasada
-- ============================================================

/-- **`reviewNode` conserva la simetría** (review simétrico). Si `x` corta a `q`, el espejo le quita
`x` a `q`; si `q` conserva a `x`, es que el corte de `x` conservó a `q`; y las demás entradas no se
mueven. -/
theorem OwnSymmetric_reviewNode (g : GPathM) (hnd : NodupIds g) (nb : PNodeM → List PathNodeId)
    (x : PathNodeId) (h : OwnSymmetric g) : OwnSymmetric (reviewNode g nb x) := by
  intro p n' q m' hp hq hqn
  obtain ⟨np, hnp, hp1, hp2⟩ := SegReview.reviewNode_owners g hnd nb x p n' hp
  obtain ⟨nq, hnq, hq1, hq2⟩ := SegReview.reviewNode_owners g hnd nb x q m' hq
  if hpx : p = x then
    subst hpx
    rw [hp2 rfl] at hqn
    have hqp : q ∈ np.owners := (List.mem_filter.mp hqn).1
    if hqx : q = p then
      subst hqx
      obtain rfl : n' = m' := Option.some.inj (hp.symm.trans hq)
      rw [hp2 rfl]; exact hqn
    else
      obtain ⟨_, _, hmk, _⟩ := hq1 hqx
      rw [hmk (fun dx hdx _ => by rw [hnp] at hdx; cases hdx; exact hqn)]
      exact h p np q nq hnp hnq hqp
  else
    obtain ⟨hsub, _, _, _⟩ := hp1 hpx
    have hqp : q ∈ np.owners := hsub q hqn
    have hpq : p ∈ nq.owners := h p np q nq hnp hnq hqp
    if hqx : q = x then
      subst hqx
      rw [hq2 rfl]
      obtain ⟨_, _, _, hback⟩ := hp1 hpx
      exact hback hqn (by rw [hq]; rfl) nq hnq hpq
    else
      obtain ⟨_, hkeep, _, _⟩ := hq1 hqx
      exact hkeep p hpq hpx

/-- info: 'AbsSat.GraphPath.Model.SymInvariant.OwnSymmetric_reviewNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_reviewNode

-- ============================================================
-- Las pasadas
-- ============================================================

/-- Lo que las pasadas arrastran: ids sin repetir y simetría. -/
def SymOk (g : GPathM) : Prop := NodupIds g ∧ OwnSymmetric g

theorem symOk_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (x : PathNodeId)
    (h : SymOk g) : SymOk (reviewNode g nb x) :=
  ⟨List.Nodup.sublist (NodeIds.ids_reviewNode g nb x) h.1, OwnSymmetric_reviewNode g h.1 nb x h.2⟩

theorem symOk_reviewLine (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int) (h : SymOk g) :
    SymOk (reviewLine g nb k) := by
  unfold reviewLine
  have main : ∀ (L : List PathNodeId) (g : GPathM), SymOk g →
      SymOk (L.foldl (fun g id => reviewNode g nb id) g) := by
    intro L
    induction L with
    | nil => intro g h; exact h
    | cons x xs ih => intro g h; exact ih _ (symOk_reviewNode g nb x h)
  exact main _ g h

theorem symOk_reviewSteps (nb : PNodeM → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathM), SymOk g → SymOk (reviewSteps g nb ks) := by
  intro ks
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    unfold reviewSteps
    split
    · exact ih _ (symOk_reviewLine g nb k h)
    · exact h

theorem symOk_reviewParents (g : GPathM) (h : SymOk g) : SymOk (reviewParents g) :=
  symOk_reviewSteps _ _ g h

theorem symOk_reviewSons (g : GPathM) (h : SymOk g) : SymOk (reviewSons g) :=
  symOk_reviewSteps _ _ g h

-- ============================================================
-- `cleanInvalid₂`
-- ============================================================

/-- Lo que la limpieza necesita además: la forma de las tablas en el propio paso (`OOS`), pasos no
negativos y por debajo del actual. Todo se conserva al estrechar. -/
structure ShapeOk (g : GPathM) : Prop where
  oos : SelfOwn.OOS g
  snn : SelfOwn.SNN g
  below : ∀ n ∈ g.nodes, n.id.id.step < g.current_step

theorem ShapeOk.of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : ShapeOk g) : ShapeOk g' :=
  ⟨SelfOwn.OOS_of_pruned hpr h.oos, SelfOwn.SNN_of_pruned hpr h.snn,
    Certifies.nodes_below_of_pruned hpr h.below⟩

/-- **En el punto fijo de la purga, cada nodo vivo está en su propio corte**: su corte es válido,
tiene entrada en su propio paso, y por `OOS` esa entrada es él mismo. -/
theorem self_in_cut (g : GPathM) (hsh : ShapeOk g) (hst : CleanTwoPhase.Stable g)
    (p : PathNodeId) (np : PNodeM) (hnp : g.node? p = some np) :
    (!hasStepEntry g.gowners p.id.step || g.gowners.contains p) = true := by
  have hm := List.mem_of_find?_eq_some hnp
  have hpid : np.id = p := node?_id_eq g p np hnp
  have hok := owners_ok_of_isValidNode _ _ (hst np hm)
  have hk := List.all_eq_true.mp hok p.id.step
    (mem_intRange (by rw [← hpid]; exact hsh.snn np hm)
      (by have := hsh.below np hm; rw [hpid] at this; omega))
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hk
  have hq' : q ∈ intersectOwners np.owners g.gowners := hq
  have hqn : q ∈ np.owners := (List.mem_filter.mp hq').1
  have hqeq : q = np.id := hsh.oos np hm q hqn (by rw [eq_of_beq hqs, hpid])
  rw [hqeq, hpid] at hq'
  exact (List.mem_filter.mp hq').2

/-- **`cleanInvalid₂` conserva la simetría**, si el resultado es válido. -/
theorem OwnSymmetric_cleanInvalid₂ (g : GPathM) (hnd : NodupIds g) (hsh : ShapeOk g)
    (h : OwnSymmetric g) (hv : isValid (cleanInvalid₂ g) = true) :
    OwnSymmetric (cleanInvalid₂ g) := by
  have hsym0 : OwnSymmetric (purgeFuel (g.nodes.length + 1) g) :=
    purgeFuel_inv OwnSymmetric
      (fun g id h => Reader.OwnSymmetric_of_ownersEq _ _ (Reader.ownersEq_removeNode g id) h) _ g h
  have hst := CleanTwoPhase.stable_purgeFuel _ g hnd (Nat.lt_succ_self _) hv
  have hsh0 := hsh.of_pruned (pruned_purgeFuel (g.nodes.length + 1) g)
  intro p n' q m' hp hq hqn
  show p ∈ m'.owners
  have hp' : (cutAll (purgeFuel (g.nodes.length + 1) g)).node? p = some n' := hp
  have hq' : (cutAll (purgeFuel (g.nodes.length + 1) g)).node? q = some m' := hq
  rw [node?_cutAll] at hp' hq'
  cases hnp : (purgeFuel (g.nodes.length + 1) g).node? p with
  | none => rw [hnp] at hp'; exact absurd hp' (by simp)
  | some np =>
    cases hnq : (purgeFuel (g.nodes.length + 1) g).node? q with
    | none => rw [hnq] at hq'; exact absurd hq' (by simp)
    | some nq =>
      rw [hnp] at hp'
      rw [hnq] at hq'
      obtain rfl := Option.some.inj hp'
      obtain rfl := Option.some.inj hq'
      have hqp : q ∈ np.owners := (List.mem_filter.mp hqn).1
      have hpq : p ∈ nq.owners := hsym0 p np q nq hnp hnq hqp
      exact List.mem_filter.mpr ⟨hpq, self_in_cut _ hsh0 hst p np hnp⟩

/-- info: 'AbsSat.GraphPath.Model.SymInvariant.OwnSymmetric_cleanInvalid₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_cleanInvalid₂

-- ============================================================
-- Una vuelta y el review base
-- ============================================================

/-- Lo que el review arrastra para la simetría. -/
structure RevOk (g : GPathM) : Prop where
  nd : NodupIds g
  sh : ShapeOk g
  sym : OwnSymmetric g

/-- **Una vuelta conserva la simetría**, si su resultado es válido. -/
theorem OwnSymmetric_reviewPass (g : GPathM) (h : RevOk g) (hv : isValid (reviewPass g) = true) :
    OwnSymmetric (reviewPass g) := by
  have hpr : Pruned (cleanInvalid₂ g) (reviewPass g) :=
    Pruned.trans (pruned_reviewParents _) (pruned_reviewSons _)
  have hv' : isValid (cleanInvalid₂ g) = true := Certifies.isValid_of_pruned hpr hv
  have hc : SymOk (cleanInvalid₂ g) :=
    ⟨CleanTwoPhase.nodupIds_cleanInvalid₂ g h.nd, OwnSymmetric_cleanInvalid₂ g h.nd h.sh h.sym hv'⟩
  exact (symOk_reviewSons _ (symOk_reviewParents _ hc)).2

theorem RevOk_reviewPass (g : GPathM) (h : RevOk g) (hv : isValid (reviewPass g) = true) :
    RevOk (reviewPass g) :=
  ⟨PinAliveChain.NodupIds_reviewPass g h.nd, h.sh.of_pruned (pruned_reviewPass g),
    OwnSymmetric_reviewPass g h hv⟩

theorem OwnSymmetric_reviewFuel : ∀ (fuel : Nat) (g : GPathM), RevOk g →
    isValid (reviewFuel fuel g) = true → OwnSymmetric (reviewFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h _; exact h.sym
  | succ n ih =>
    intro g h hv
    simp only [reviewFuel] at hv ⊢
    split
    · next hg =>
      rw [if_pos hg] at hv
      split
      · next hlt =>
        rw [if_pos hlt] at hv
        have hv' : isValid (reviewPass g) = true :=
          Certifies.isValid_of_pruned (pruned_reviewFuel n _) hv
        exact ih _ (RevOk_reviewPass g h hv') hv
      · next hlt =>
        rw [if_neg hlt] at hv
        exact OwnSymmetric_reviewPass g h hv
    · exact h.sym

/-- **El review base conserva la simetría**, si su resultado es válido. -/
theorem OwnSymmetric_review (g : GPathM) (h : RevOk g) (hv : isValid (review g) = true) :
    OwnSymmetric (review g) :=
  OwnSymmetric_reviewFuel _ g h hv

theorem RevOk_review (g : GPathM) (h : RevOk g) (hv : isValid (review g) = true) : RevOk (review g) :=
  ⟨PinAliveChain.NodupIds_review g h.nd, h.sh.of_pruned (pruned_review g), OwnSymmetric_review g h hv⟩

-- ============================================================
-- El barrido agresivo
-- ============================================================

/-- Una tabla comparte todos sus pasos consigo misma. -/
theorem sharesEveryStep_self (cs : Int) (o : List PathNodeId) : sharesEveryStep cs o o = true := by
  unfold sharesEveryStep
  refine List.all_eq_true.mpr (fun k _ => ?_)
  cases hk : hasStepEntry o k with
  | false => rfl
  | true =>
    obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hk
    have : (ownersAt o k).any (fun r => o.contains r) = true :=
      List.any_eq_true.mpr ⟨q, List.mem_filter.mpr ⟨hq, hqs⟩, List.elem_eq_true_of_mem hq⟩
    rw [this]; rfl

/-- **Con simetría, la rama «asimétrica» del barrido no se dispara nunca.** -/
theorem aggPair_asym_never (g : GPathM) (h : OwnSymmetric g) (x w : PathNodeId) (nx nw : PNodeM)
    (hx : g.node? x = some nx) (hw : g.node? w = some nw) :
    (nx.owners.contains w && isValidNode g nw && !nw.owners.contains x) = false := by
  cases hc : nx.owners.contains w with
  | false => rfl
  | true =>
    have hxw : x ∈ nw.owners := h x nx w nw hx hw (List.contains_iff_mem.mp hc)
    rw [List.contains_iff_mem.mpr hxw]
    simp

/-- Cortar una tabla con su propia `dropList` quita exactamente `w`. -/
theorem mem_intersect_dropList (os : List PathNodeId) (w q : PathNodeId) :
    q ∈ intersectOwners os (dropList os w) ↔ q ∈ os ∧ q ≠ w := by
  constructor
  · intro hq
    obtain ⟨hqo, hp⟩ := List.mem_filter.mp hq
    refine ⟨hqo, fun hqw => ?_⟩
    subst hqw
    have hse : hasStepEntry (dropList os q) q.id.step = true :=
      List.any_eq_true.mpr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), beq_iff_eq.mpr rfl⟩
    have hnc : (dropList os q).contains q = false := by
      cases hc : (dropList os q).contains q with
      | false => rfl
      | true =>
        exfalso
        rcases List.mem_append.mp (List.contains_iff_mem.mp hc) with h1 | h1
        · have := (List.mem_filter.mp h1).2
          simp at this
        · have he := List.mem_singleton.mp h1
          have hidx := congrArg (fun r : PathNodeId => r.id.index) he
          simp only at hidx
          omega
    rw [hse, hnc] at hp
    simp at hp
  · intro ⟨hqo, hqw⟩
    exact mem_intersectOwners_of_mem _ _ q hqo (mem_dropList os w q hqo hqw)

/-- **El par inconsistente**: quita las dos direcciones, así que la simetría se conserva. -/
theorem OwnSymmetric_dropOwnerPair (g : GPathM) (h : OwnSymmetric g) (x w : PathNodeId)
    (nx nw : PNodeM) (hx : g.node? x = some nx) (hw : g.node? w = some nw) (hxw : x ≠ w) :
    OwnSymmetric (dropOwnerPair g x w nx.owners nw.owners) := by
  -- the owners of a node after the drop
  have after : ∀ p n', (dropOwnerPair g x w nx.owners nw.owners).node? p = some n' →
      ∃ n, g.node? p = some n ∧
        ∀ q, q ∈ n'.owners ↔ q ∈ n.owners ∧ ¬(p = x ∧ q = w) ∧ ¬(p = w ∧ q = x) := by
    intro p n' hp
    obtain ⟨m1, hm1, he2⟩ := Reader.updateAt_node?_inv _ w (uniMap (dropList nw.owners x))
      (uniMap_id _) p n' hp
    obtain ⟨n, hn, he1⟩ := Reader.updateAt_node?_inv g x (uniMap (dropList nx.owners w))
      (uniMap_id _) p m1 hm1
    have hnid : n.id = p := node?_id_eq g p n hn
    have hm1id : m1.id = n.id := by
      rw [he1]; cases n.id == x <;> rfl
    refine ⟨n, hn, fun q => ?_⟩
    cases hbx : (n.id == x) with
    | true =>
      have hpx : p = x := by rw [← hnid]; exact eq_of_beq hbx
      have hnx : n = nx := by rw [hpx] at hn; exact Option.some.inj (hn.symm.trans hx)
      have he1' : m1 = uniMap (dropList nx.owners w) n := by rw [he1, hbx]
      have hbw : (m1.id == w) = false := by
        rw [he1', uniMap_id, hnid, hpx]; exact beq_eq_false_iff_ne.mpr hxw
      have he2' : n' = m1 := by rw [he2, hbw]
      rw [he2', he1']
      show q ∈ intersectOwners n.owners (dropList nx.owners w) ↔ _
      rw [hnx, mem_intersect_dropList]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨h1, fun ⟨_, h⟩ => h2 h, fun ⟨h, _⟩ => hxw (hpx.symm.trans h)⟩
      · intro ⟨h1, h2, _⟩; exact ⟨h1, fun h => h2 ⟨hpx, h⟩⟩
    | false =>
      have he1' : m1 = n := by rw [he1, hbx]
      have hpx : p ≠ x := fun he => by rw [hnid, he] at hbx; simp at hbx
      cases hbw : (n.id == w) with
      | true =>
        have hpw : p = w := by rw [← hnid]; exact eq_of_beq hbw
        have hnw : n = nw := by rw [hpw] at hn; exact Option.some.inj (hn.symm.trans hw)
        have he2' : n' = uniMap (dropList nw.owners x) n := by rw [he2, he1', hbw]
        rw [he2']
        show q ∈ intersectOwners n.owners (dropList nw.owners x) ↔ _
        rw [hnw, mem_intersect_dropList]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨h1, fun ⟨h, _⟩ => hpx h, fun ⟨_, h⟩ => h2 h⟩
        · intro ⟨h1, _, h3⟩; exact ⟨h1, fun h => h3 ⟨hpw, h⟩⟩
      | false =>
        have he2' : n' = n := by rw [he2, he1', hbw]
        have hpw : p ≠ w := fun he => by rw [hnid, he] at hbw; simp at hbw
        rw [he2']
        exact ⟨fun h1 => ⟨h1, fun ⟨h, _⟩ => hpx h, fun ⟨h, _⟩ => hpw h⟩, fun ⟨h1, _⟩ => h1⟩
  intro p n' q m' hp hq hqn
  obtain ⟨np, hnp, hpa⟩ := after p n' hp
  obtain ⟨nq, hnq, hqa⟩ := after q m' hq
  obtain ⟨hqo, h1, h2⟩ := (hpa q).mp hqn
  exact (hqa p).mpr ⟨h p np q nq hnp hnq hqo, fun ⟨a, b⟩ => h2 ⟨b, a⟩, fun ⟨a, b⟩ => h1 ⟨b, a⟩⟩

theorem OwnSymmetric_aggPair (g : GPathM) (h : OwnSymmetric g) (x w : PathNodeId) :
    OwnSymmetric (aggPair g x w) := by
  unfold aggPair
  cases hx : g.node? x with
  | none => exact h
  | some nx =>
    cases hw : g.node? w with
    | none => exact h
    | some nw =>
      simp only
      rw [if_neg (by rw [aggPair_asym_never g h x w nx nw hx hw]; exact Bool.false_ne_true)]
      split
      · next hfire =>
        have hxw : x ≠ w := by
          intro he
          subst he
          have hn : nw = nx := Option.some.inj (hw.symm.trans hx)
          subst hn
          rw [sharesEveryStep_self] at hfire
          simp at hfire
        exact OwnSymmetric_dropOwnerPair g h x w nx nw hx hw hxw
      · exact h

private theorem sym_foldl {β : Type} (f : GPathM → β → GPathM)
    (hf : ∀ g b, OwnSymmetric g → OwnSymmetric (f g b)) :
    ∀ (l : List β) (g : GPathM), OwnSymmetric g → OwnSymmetric (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons b rest ih => intro g h; exact ih _ (hf g b h)

theorem OwnSymmetric_removeNode (g : GPathM) (id : PathNodeId) (h : OwnSymmetric g) :
    OwnSymmetric (removeNode g id) :=
  Reader.OwnSymmetric_of_ownersEq _ _ (Reader.ownersEq_removeNode g id) h

theorem OwnSymmetric_aggNode (g : GPathM) (h : OwnSymmetric g) (x : PathNodeId) :
    OwnSymmetric (aggNode g x) := by
  unfold aggNode
  split
  · exact h
  · have h₁ : ∀ g₁ : GPathM, OwnSymmetric g₁ → OwnSymmetric
        (match g₁.node? x with
          | none => g₁
          | some n₁ => if isValidNode g₁ n₁ then g₁ else removeNode g₁ x) := by
      intro g₁ hg₁
      split
      · exact hg₁
      · split
        · exact hg₁
        · exact OwnSymmetric_removeNode _ _ hg₁
    apply h₁
    split
    · exact sym_foldl _ (fun g kw hg => sym_foldl _ (fun g w hg => OwnSymmetric_aggPair g hg x w) _ g hg)
        _ g h
    · exact h

/-- **El barrido agresivo conserva la simetría.** -/
theorem OwnSymmetric_aggSweep (g : GPathM) (h : OwnSymmetric g) : OwnSymmetric (aggSweep g) := by
  unfold aggSweep
  split
  · exact sym_foldl _ (fun g k hg => sym_foldl _ (fun g x hg => OwnSymmetric_aggNode g hg x) _ g hg) _ g h
  · exact h

-- ============================================================
-- La review agresiva y el filtro
-- ============================================================

theorem OwnSymmetric_reviewAggFuel : ∀ (fuel : Nat) (g : GPathM), RevOk g →
    isValid (reviewAggFuel fuel g) = true → OwnSymmetric (reviewAggFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h hv; exact OwnSymmetric_review g h hv
  | succ n ih =>
    intro g h hv
    simp only [reviewAggFuel] at hv ⊢
    split
    · next hg1 =>
      rw [if_pos hg1] at hv
      have h1 := RevOk_review g h hg1
      split
      · next hlt =>
        rw [if_pos hlt] at hv
        exact ih _ ⟨PinAliveChain.NodupIds_aggSweep _ h1.nd, h1.sh.of_pruned (pruned_aggSweep _),
          OwnSymmetric_aggSweep _ h1.sym⟩ hv
      · exact h1.sym
    · next hg1 =>
      rw [if_neg hg1] at hv
      exact absurd hv hg1

/-- **La review agresiva conserva la simetría**, si su resultado es válido. -/
theorem OwnSymmetric_reviewAgg (g : GPathM) (h : RevOk g) (hv : isValid (reviewAgg g) = true) :
    OwnSymmetric (reviewAgg g) :=
  OwnSymmetric_reviewAggFuel _ g h hv

/-- **Y el filtro del lector**: los pines no tocan tablas. -/
theorem OwnSymmetric_filterAllAgg (g : GPathM) (h : RevOk g) (reqs : List NodeId)
    (hv : isValid (filterAllAgg g reqs) = true) : OwnSymmetric (filterAllAgg g reqs) := by
  have hpins : ∀ (rs : List NodeId) (g : GPathM), RevOk g → RevOk (rs.foldl filterRequire g) := by
    intro rs
    induction rs with
    | nil => intro g h; exact h
    | cons r rs ih =>
      intro g h
      exact ih _ ⟨h.nd, h.sh.of_pruned (pruned_filterRequire g r),
        Reader.OwnSymmetric_filterRequire g r h.sym⟩
  exact OwnSymmetric_reviewAgg _ (hpins reqs g h) hv

/-- info: 'AbsSat.GraphPath.Model.SymInvariant.OwnSymmetric_filterAllAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_filterAllAgg

/-- info: 'AbsSat.GraphPath.Model.SymInvariant.aggPair_asym_never' depends on axioms: [propext] -/
#guard_msgs in
#print axioms aggPair_asym_never

-- ============================================================
-- La simetría local sale de la global: las pasadas sin hipótesis
-- ============================================================

open AbsSat.GraphPath.Model.PassCtx (PState)
open AbsSat.GraphPath.Model.PassPlain (PStateG)

/-- **La simetría local** (la que usaban las pasadas) **es un caso de la global.** -/
theorem LocSym_of_ownSymmetric (g : GPathM) (h : OwnSymmetric g) : SegReview.LocSym g := by
  intro sel lo hi _ hs r0 nr0 hnr0 _ hin j hj1 hj2
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (hs.1.1 j hj1 hj2).1
  exact h (sel j) nj r0 nr0 hnj hnr0 (hin j hj1 hj2 nj hnj)

theorem LocSymUp_of_ownSymmetric (g : GPathM) (h : OwnSymmetric g) : SegReview.LocSymUp g := by
  intro sel lo hi _ hs r0 nr0 hnr0 _ hin j hj1 hj2
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (hs.1.1 j hj1 hj2).1
  exact h (sel j) nj r0 nr0 hnj hnr0 (hin j hj1 hj2 nj hnj)

/-- **Un paso de la pasada de padres conserva `PStateG` y la simetría, sin `LocSymStable`.** -/
theorem pstateGS_reviewNode (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) (x : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1) :
    PStateG (reviewNode g (·.parents) x) ∧ OwnSymmetric (reviewNode g (·.parents) x) := by
  have hp := h.toP
  have hpr := pruned_reviewNode (·.parents) x g
  have hs' := OwnSymmetric_reviewNode g h.nd (·.parents) x hs
  have hP : PState (reviewNode g (·.parents) x) :=
    { nd := List.Nodup.sublist (NodeIds.ids_reviewNode g (·.parents) x) hp.nd
      sgl := PassCtx.segGoodL_reviewNode_parents g hp.nd hp.i1 hp.i1s hp.plive hp.slive hp.self hp.lsym
        hp.lsymU hp.nr hp.sgl x hx1 hxc
      i1 := PassCtx.i1L_reviewNode_parents g hp.nd hp.sgl hp.i1 hp.i1s hp.self hp.lsym hp.nr hp.below x
        hx1 hxc
      i1s := PassCtx.i1sL_reviewNode_parents g hp.nd hp.sgl hp.i1 hp.i1s hp.self hp.lsym hp.lsymU hp.nr x
        hx1 hxc
      plive := PassCtx.pLive_reviewNode g hp.nd hp.plive _ x
      slive := PassCtx.sLive_reviewNode g hp.nd hp.slive _ x
      self := PassCtx.selfL_reviewNode g hp.nd hp.oos hp.snn hp.below hp.self _ x
      lsym := LocSym_of_ownSymmetric _ hs'
      lsymU := LocSymUp_of_ownSymmetric _ hs'
      nr := Parents.NotRoot_of_pruned hpr hp.nr
      below := Certifies.nodes_below_of_pruned hpr hp.below
      oos := SelfOwn.OOS_of_pruned hpr hp.oos
      snn := SelfOwn.SNN_of_pruned hpr hp.snn
      rootz := Sons.RootAtZero_of_pruned hpr hp.rootz }
  exact ⟨PStateG.ofP hP (PassPlain.ownLive_reviewNode_parents g hp h.ol x hx1 hxc), hs'⟩

/-- **Y un paso de la pasada de hijos.** -/
theorem pstateGS_reviewNode_sons (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) (x : PathNodeId)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2) :
    PStateG (reviewNode g (·.sons) x) ∧ OwnSymmetric (reviewNode g (·.sons) x) := by
  have hp := h.toP
  have hpr := pruned_reviewNode (·.sons) x g
  have hs' := OwnSymmetric_reviewNode g h.nd (·.sons) x hs
  have hP : PState (reviewNode g (·.sons) x) :=
    { nd := List.Nodup.sublist (NodeIds.ids_reviewNode g (·.sons) x) hp.nd
      sgl := PassSons.segGoodL_reviewNode_sons g hp.nd hp.i1 hp.i1s hp.plive hp.slive hp.self hp.lsym
        hp.lsymU hp.rootz hp.sgl x hx0 hxl
      i1 := PassSons.i1L_reviewNode_sons g hp.nd hp.sgl hp.i1 hp.i1s hp.self hp.lsym hp.lsymU hp.rootz x
        hx0 hxl
      i1s := PassSons.i1sL_reviewNode_sons g hp.nd hp.sgl hp.i1 hp.i1s hp.self hp.lsymU hp.rootz hp.snn x
        hx0 hxl
      plive := PassCtx.pLive_reviewNode g hp.nd hp.plive _ x
      slive := PassCtx.sLive_reviewNode g hp.nd hp.slive _ x
      self := PassCtx.selfL_reviewNode g hp.nd hp.oos hp.snn hp.below hp.self _ x
      lsym := LocSym_of_ownSymmetric _ hs'
      lsymU := LocSymUp_of_ownSymmetric _ hs'
      nr := Parents.NotRoot_of_pruned hpr hp.nr
      below := Certifies.nodes_below_of_pruned hpr hp.below
      oos := SelfOwn.OOS_of_pruned hpr hp.oos
      snn := SelfOwn.SNN_of_pruned hpr hp.snn
      rootz := Sons.RootAtZero_of_pruned hpr hp.rootz }
  exact ⟨PStateG.ofP hP (PassPlain.ownLive_reviewNode_sons g hp h.ol x hx0 hxl), hs'⟩

theorem pstateGS_reviewParents (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) :
    PStateG (reviewParents g) ∧ OwnSymmetric (reviewParents g) := by
  have hfold : ∀ (k : Int), 1 ≤ k → ∀ (L : List PathNodeId) (g : GPathM), PStateG g → OwnSymmetric g →
      k ≤ g.current_step - 1 → (∀ id ∈ L, id.id.step = k) →
      PStateG (L.foldl (fun g id => reviewNode g (·.parents) id) g) ∧
        OwnSymmetric (L.foldl (fun g id => reviewNode g (·.parents) id) g) := by
    intro k hk1 L
    induction L with
    | nil => intro g h hs _ _; exact ⟨h, hs⟩
    | cons x xs ih =>
      intro g h hs hkc hL
      have hxs := hL x List.mem_cons_self
      have hstep := (pruned_reviewNode (·.parents) x g).step_eq
      obtain ⟨h1, hs1⟩ := pstateGS_reviewNode g h hs x (by omega) (by omega)
      exact ih _ h1 hs1 (by rw [hstep]; exact hkc) (fun id hid => hL id (List.mem_cons_of_mem _ hid))
  have main : ∀ (ks : List Int) (g' : GPathM), PStateG g' → OwnSymmetric g' →
      g'.current_step - 1 = g.current_step - 1 → (∀ k ∈ ks, 1 ≤ k ∧ k ≤ g.current_step - 1) →
      PStateG (reviewSteps g' (·.parents) ks) ∧ OwnSymmetric (reviewSteps g' (·.parents) ks) := by
    intro ks
    induction ks with
    | nil => intro g' h hs _ _; exact ⟨h, hs⟩
    | cons k ks ih =>
      intro g' h hs hc hks
      unfold reviewSteps
      split
      · have hk := hks k List.mem_cons_self
        have hstep := (pruned_reviewLine (·.parents) k g').step_eq
        obtain ⟨h1, hs1⟩ := hfold k hk.1 ((g'.line k).map (·.id)) g' h hs (by omega) (fun id hid => by
          obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hid
          exact eq_of_beq (List.mem_filter.mp hn).2)
        exact ih _ h1 hs1 (by rw [hstep]; exact hc) (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      · exact ⟨h, hs⟩
  exact main _ g h hs rfl (fun _ hk => ⟨mem_intRange_lower hk, mem_intRange_upper hk⟩)

theorem pstateGS_reviewSons (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) :
    PStateG (reviewSons g) ∧ OwnSymmetric (reviewSons g) := by
  have hfold : ∀ (k : Int), 0 ≤ k → ∀ (L : List PathNodeId) (g : GPathM), PStateG g → OwnSymmetric g →
      k ≤ g.current_step - 2 → (∀ id ∈ L, id.id.step = k) →
      PStateG (L.foldl (fun g id => reviewNode g (·.sons) id) g) ∧
        OwnSymmetric (L.foldl (fun g id => reviewNode g (·.sons) id) g) := by
    intro k hk0 L
    induction L with
    | nil => intro g h hs _ _; exact ⟨h, hs⟩
    | cons x xs ih =>
      intro g h hs hkc hL
      have hxs := hL x List.mem_cons_self
      have hstep := (pruned_reviewNode (·.sons) x g).step_eq
      obtain ⟨h1, hs1⟩ := pstateGS_reviewNode_sons g h hs x (by omega) (by omega)
      exact ih _ h1 hs1 (by rw [hstep]; exact hkc) (fun id hid => hL id (List.mem_cons_of_mem _ hid))
  have main : ∀ (ks : List Int) (g' : GPathM), PStateG g' → OwnSymmetric g' →
      g'.current_step - 2 = g.current_step - 2 → (∀ k ∈ ks, 0 ≤ k ∧ k ≤ g.current_step - 2) →
      PStateG (reviewSteps g' (·.sons) ks) ∧ OwnSymmetric (reviewSteps g' (·.sons) ks) := by
    intro ks
    induction ks with
    | nil => intro g' h hs _ _; exact ⟨h, hs⟩
    | cons k ks ih =>
      intro g' h hs hc hks
      unfold reviewSteps
      split
      · have hk := hks k List.mem_cons_self
        have hstep := (pruned_reviewLine (·.sons) k g').step_eq
        obtain ⟨h1, hs1⟩ := hfold k hk.1 ((g'.line k).map (·.id)) g' h hs (by omega) (fun id hid => by
          obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hid
          exact eq_of_beq (List.mem_filter.mp hn).2)
        exact ih _ h1 hs1 (by rw [hstep]; exact hc) (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      · exact ⟨h, hs⟩
  exact main _ g h hs rfl (fun _ hk => ⟨mem_intRange_lower (List.mem_reverse.mp hk),
    mem_intRange_upper (List.mem_reverse.mp hk)⟩)

/-- **Una vuelta del review conserva `PStateG`, sin `LocSymStable` ni `LocSymStableS`**: basta la
simetría a la salida de `cleanInvalid₂`, que el review simétrico da (`OwnSymmetric_cleanInvalid₂`). -/
theorem pstateG_reviewPass' (g : GPathM) (h : PStateG (cleanInvalid₂ g))
    (hs : OwnSymmetric (cleanInvalid₂ g)) :
    PStateG (reviewPass g) ∧ OwnSymmetric (reviewPass g) := by
  obtain ⟨h1, hs1⟩ := pstateGS_reviewParents _ h hs
  exact pstateGS_reviewSons _ h1 hs1

/-- **Y la simetría a la salida de `cleanInvalid₂` sale de la de la entrada**: la vuelta entera, con
`PStateG` tras la limpieza y el contexto de la simetría a la entrada. -/
theorem pstateG_reviewPass_of (g : GPathM) (hr : RevOk g) (h : PStateG (cleanInvalid₂ g))
    (hv : isValid (cleanInvalid₂ g) = true) :
    PStateG (reviewPass g) ∧ OwnSymmetric (reviewPass g) :=
  pstateG_reviewPass' g h (OwnSymmetric_cleanInvalid₂ g hr.nd hr.sh hr.sym hv)

/-- info: 'AbsSat.GraphPath.Model.SymInvariant.pstateG_reviewPass_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pstateG_reviewPass_of

-- ============================================================
-- S1′ con el espejo: una entrada solo sale si su par queda separado
-- ============================================================

open AbsSat.GraphPath.Model.CompatLoss (Sep)

/-- **S1′ en un paso de la pasada de padres** (review simétrico). Si una entrada `r` sale de la tabla
de `y`, o `y` es el nodo procesado y `r` queda separado de él en el paso de sus padres, o `r` es el
procesado —el espejo— y `y` queda separado de él ahí. -/
theorem commonLoss_node_parents (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) (x : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1)
    (y r : PathNodeId) (ny : PNodeM) (hny : g.node? y = some ny) (hr : r ∈ ny.owners)
    (nr : PNodeM) (hnr : g.node? r = some nr)
    (ny' : PNodeM) (hny' : (reviewNode g (·.parents) x).node? y = some ny') (hr' : r ∉ ny'.owners) :
    (y = x ∧ Sep (reviewNode g (·.parents) x) x r (x.id.step - 1)) ∨
      (r = x ∧ Sep (reviewNode g (·.parents) x) x y (x.id.step - 1)) := by
  have hp := h.toP
  cases hd : g.node? x with
  | none =>
    have hR : reviewNode g (·.parents) x = g := by unfold reviewNode; rw [hd]
    rw [hR, hny] at hny'
    cases hny'
    exact absurd hr hr'
  | some d =>
    have hk := PassCtx.kept_reviewNode_parents g hp.sgl hp.i1 hp.i1s hp.self hp.lsym hp.nr x d hd hx1 hxc
    if hyx : y = x then
      subst hyx
      have hdn : ny = d := Option.some.inj (hny.symm.trans hd)
      subst hdn
      rw [CompatLoss.owners_self_after g _ y ny hd hk ny' hny'] at hr'
      exact Or.inl ⟨rfl, CompatLoss.sep_of_drop_parents g h.nd hs h.i1 h.ol y ny hd hx1 hxc hk r nr hnr hr hr'⟩
    else
      obtain ⟨n, hn, hne, _⟩ := SegReview.reviewNode_owners g h.nd (·.parents) x y ny' hny'
      have hnn : n = ny := Option.some.inj (hn.symm.trans hny)
      subst hnn
      obtain ⟨_, hkeep, hmk, _⟩ := hne hyx
      if hrx : r = x then
        subst hrx
        have hyd : y ∈ d.owners := hs y n r d hny hd hr
        have hdrop : y ∉ intersectOwners d.owners (unionOwnersOf g d.parents) := fun hin =>
          hr' (by rw [hmk (fun dx hdx _ => by rw [hd] at hdx; cases hdx; exact hin)]; exact hr)
        exact Or.inr ⟨rfl, CompatLoss.sep_of_drop_parents g h.nd hs h.i1 h.ol r d hd hx1 hxc hk y n hny
          hyd hdrop⟩
      else
        exact absurd (hkeep r hr hrx) hr'

/-- **S1′ en un paso de la pasada de hijos.** -/
theorem commonLoss_node_sons (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) (x : PathNodeId)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2)
    (y r : PathNodeId) (ny : PNodeM) (hny : g.node? y = some ny) (hr : r ∈ ny.owners)
    (nr : PNodeM) (hnr : g.node? r = some nr)
    (ny' : PNodeM) (hny' : (reviewNode g (·.sons) x).node? y = some ny') (hr' : r ∉ ny'.owners) :
    (y = x ∧ Sep (reviewNode g (·.sons) x) x r (x.id.step + 1)) ∨
      (r = x ∧ Sep (reviewNode g (·.sons) x) x y (x.id.step + 1)) := by
  have hp := h.toP
  cases hd : g.node? x with
  | none =>
    have hR : reviewNode g (·.sons) x = g := by unfold reviewNode; rw [hd]
    rw [hR, hny] at hny'
    cases hny'
    exact absurd hr hr'
  | some d =>
    have hk := PassSons.kept_reviewNode_sons g hp.sgl hp.i1 hp.i1s hp.self hp.lsymU hp.rootz x d hd hx0 hxl
    if hyx : y = x then
      subst hyx
      have hdn : ny = d := Option.some.inj (hny.symm.trans hd)
      subst hdn
      rw [CompatLoss.owners_self_after g _ y ny hd hk ny' hny'] at hr'
      exact Or.inl ⟨rfl, CompatLoss.sep_of_drop_sons g h.nd hs h.i1s h.ol y ny hd hx0 hxl hk r nr hnr hr hr'⟩
    else
      obtain ⟨n, hn, hne, _⟩ := SegReview.reviewNode_owners g h.nd (·.sons) x y ny' hny'
      have hnn : n = ny := Option.some.inj (hn.symm.trans hny)
      subst hnn
      obtain ⟨_, hkeep, hmk, _⟩ := hne hyx
      if hrx : r = x then
        subst hrx
        have hyd : y ∈ d.owners := hs y n r d hny hd hr
        have hdrop : y ∉ intersectOwners d.owners (unionOwnersOf g d.sons) := fun hin =>
          hr' (by rw [hmk (fun dx hdx _ => by rw [hd] at hdx; cases hdx; exact hin)]; exact hr)
        exact Or.inr ⟨rfl, CompatLoss.sep_of_drop_sons g h.nd hs h.i1s h.ol r d hd hx0 hxl hk y n hny
          hyd hdrop⟩
      else
        exact absurd (hkeep r hr hrx) hr'

/-- **Una entrada que sale deja a su par separado**, de `g` a `g'`: si `r` estaba en la tabla de `y` en
`g` y no en `g'`, con los dos vivos en `g'`, entonces `y` y `r` no comparten nada en algún paso, en un
sentido o en el otro. -/
def Lost (g g' : GPathM) : Prop :=
  ∀ y r ny ny', g.node? y = some ny → r ∈ ny.owners → g'.node? y = some ny' → r ∉ ny'.owners →
    (g'.node? r).isSome → ∃ k, Sep g' y r k ∨ Sep g' r y k

theorem Lost.refl (g : GPathM) : Lost g g := by
  intro y r ny ny' hny hr hny' hr' _
  rw [hny] at hny'; cases hny'; exact absurd hr hr'

/-- Un nodo vivo después lo estaba antes. -/
theorem node_back {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g) (y : PathNodeId) (n' : PNodeM)
    (h : g'.node? y = some n') : ∃ n, g.node? y = some n ∧ ∀ q ∈ n'.owners, q ∈ n.owners := by
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' (List.mem_of_find?_eq_some h)
  exact ⟨n, by rw [← node?_id_eq _ y n' h, hid]; exact node?_of_mem hnd n hn, hown⟩

/-- **`Lost` se encadena**: la separación dura (`Sep.of_pruned`). -/
theorem Lost.trans {g₁ g₂ g₃ : GPathM} (h₁₂ : Lost g₁ g₂) (h₂₃ : Lost g₂ g₃) (hpr : Pruned g₂ g₃)
    (hnd : NodupIds g₂) : Lost g₁ g₃ := by
  intro y r ny ny₃ hny hr hny₃ hr₃ hrl
  obtain ⟨ny₂, hny₂, _⟩ := node_back hpr hnd y ny₃ hny₃
  if hr₂ : r ∈ ny₂.owners then
    exact h₂₃ y r ny₂ ny₃ hny₂ hr₂ hny₃ hr₃ hrl
  else
    obtain ⟨nr₃, hnr₃⟩ := Option.isSome_iff_exists.mp hrl
    obtain ⟨nr₂, hnr₂, _⟩ := node_back hpr hnd r nr₃ hnr₃
    obtain ⟨k, hk⟩ := h₁₂ y r ny ny₂ hny hr hny₂ hr₂ (by rw [hnr₂]; rfl)
    refine ⟨k, ?_⟩
    rcases hk with hk | hk
    · exact Or.inl (Sep.of_pruned hpr hnd hk)
    · exact Or.inr (Sep.of_pruned hpr hnd hk)

theorem lost_reviewNode_parents (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) (x : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1) :
    Lost g (reviewNode g (·.parents) x) := by
  intro y r ny ny' hny hr hny' hr' hrl
  obtain ⟨nr', hnr'⟩ := Option.isSome_iff_exists.mp hrl
  obtain ⟨nr, hnr, _⟩ := node_back (pruned_reviewNode _ x g) h.nd r nr' hnr'
  rcases commonLoss_node_parents g h hs x hx1 hxc y r ny hny hr nr hnr ny' hny' hr' with
    ⟨rfl, hsep⟩ | ⟨rfl, hsep⟩
  · exact ⟨_, Or.inl hsep⟩
  · exact ⟨_, Or.inr hsep⟩

theorem lost_reviewNode_sons (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) (x : PathNodeId)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2) :
    Lost g (reviewNode g (·.sons) x) := by
  intro y r ny ny' hny hr hny' hr' hrl
  obtain ⟨nr', hnr'⟩ := Option.isSome_iff_exists.mp hrl
  obtain ⟨nr, hnr, _⟩ := node_back (pruned_reviewNode _ x g) h.nd r nr' hnr'
  rcases commonLoss_node_sons g h hs x hx0 hxl y r ny hny hr nr hnr ny' hny' hr' with
    ⟨rfl, hsep⟩ | ⟨rfl, hsep⟩
  · exact ⟨_, Or.inl hsep⟩
  · exact ⟨_, Or.inr hsep⟩

theorem lost_reviewParents (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) :
    Lost g (reviewParents g) := by
  have hfold : ∀ (k : Int), 1 ≤ k → ∀ (L : List PathNodeId) (g : GPathM), PStateG g → OwnSymmetric g →
      k ≤ g.current_step - 1 → (∀ id ∈ L, id.id.step = k) →
      Lost g (L.foldl (fun g id => reviewNode g (·.parents) id) g) := by
    intro k hk1 L
    induction L with
    | nil => intro g _ _ _ _; exact Lost.refl g
    | cons x xs ih =>
      intro g h hs hkc hL
      have hxs := hL x List.mem_cons_self
      have hstep := (pruned_reviewNode (·.parents) x g).step_eq
      obtain ⟨h1, hs1⟩ := pstateGS_reviewNode g h hs x (by omega) (by omega)
      have hpr : Pruned (reviewNode g (·.parents) x)
          (xs.foldl (fun g id => reviewNode g (·.parents) id) (reviewNode g (·.parents) x)) :=
        pruned_foldl _ (fun g id => pruned_reviewNode _ id g) xs _
      exact Lost.trans (lost_reviewNode_parents g h hs x (by omega) (by omega))
        (ih _ h1 hs1 (by rw [hstep]; exact hkc) (fun id hid => hL id (List.mem_cons_of_mem _ hid)))
        hpr h1.nd
  have main : ∀ (ks : List Int) (g' : GPathM), PStateG g' → OwnSymmetric g' →
      g'.current_step - 1 = g.current_step - 1 → (∀ k ∈ ks, 1 ≤ k ∧ k ≤ g.current_step - 1) →
      Lost g' (reviewSteps g' (·.parents) ks) := by
    intro ks
    induction ks with
    | nil => intro g' _ _ _ _; exact Lost.refl g'
    | cons k ks ih =>
      intro g' h hs hc hks
      unfold reviewSteps
      split
      · have hk := hks k List.mem_cons_self
        have hstep := (pruned_reviewLine (·.parents) k g').step_eq
        have hL : ∀ id ∈ (g'.line k).map (·.id), id.id.step = k := fun id hid => by
          obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hid
          exact eq_of_beq (List.mem_filter.mp hn).2
        obtain ⟨h1, hs1⟩ := (pstateGS_reviewParents_line k hk.1 _ g' h hs (by omega) hL)
        exact Lost.trans (hfold k hk.1 _ g' h hs (by omega) hL)
          (ih _ h1 hs1 (by show (reviewLine g' _ k).current_step - _ = _; rw [hstep]; exact hc)
            (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')))
          (pruned_reviewSteps _ ks _) h1.nd
      · exact Lost.refl g'
  exact main _ g h hs rfl (fun _ hk => ⟨mem_intRange_lower hk, mem_intRange_upper hk⟩)
where
  pstateGS_reviewParents_line (k : Int) (hk1 : 1 ≤ k) : ∀ (L : List PathNodeId) (g : GPathM),
      PStateG g → OwnSymmetric g → k ≤ g.current_step - 1 → (∀ id ∈ L, id.id.step = k) →
      PStateG (L.foldl (fun g id => reviewNode g (·.parents) id) g) ∧
        OwnSymmetric (L.foldl (fun g id => reviewNode g (·.parents) id) g) := by
    intro L
    induction L with
    | nil => intro g h hs _ _; exact ⟨h, hs⟩
    | cons x xs ih =>
      intro g h hs hkc hL
      have hxs := hL x List.mem_cons_self
      have hstep := (pruned_reviewNode (·.parents) x g).step_eq
      obtain ⟨h1, hs1⟩ := pstateGS_reviewNode g h hs x (by omega) (by omega)
      exact ih _ h1 hs1 (by rw [hstep]; exact hkc) (fun id hid => hL id (List.mem_cons_of_mem _ hid))

theorem lost_reviewSons (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g) :
    Lost g (reviewSons g) := by
  have hline : ∀ (k : Int), 0 ≤ k → ∀ (L : List PathNodeId) (g : GPathM), PStateG g → OwnSymmetric g →
      k ≤ g.current_step - 2 → (∀ id ∈ L, id.id.step = k) →
      (PStateG (L.foldl (fun g id => reviewNode g (·.sons) id) g) ∧
        OwnSymmetric (L.foldl (fun g id => reviewNode g (·.sons) id) g)) ∧
      Lost g (L.foldl (fun g id => reviewNode g (·.sons) id) g) := by
    intro k hk0 L
    induction L with
    | nil => intro g h hs _ _; exact ⟨⟨h, hs⟩, Lost.refl g⟩
    | cons x xs ih =>
      intro g h hs hkc hL
      have hxs := hL x List.mem_cons_self
      have hstep := (pruned_reviewNode (·.sons) x g).step_eq
      obtain ⟨h1, hs1⟩ := pstateGS_reviewNode_sons g h hs x (by omega) (by omega)
      obtain ⟨hst, hlost⟩ := ih _ h1 hs1 (by rw [hstep]; exact hkc)
        (fun id hid => hL id (List.mem_cons_of_mem _ hid))
      have hpr : Pruned (reviewNode g (·.sons) x)
          (xs.foldl (fun g id => reviewNode g (·.sons) id) (reviewNode g (·.sons) x)) :=
        pruned_foldl _ (fun g id => pruned_reviewNode _ id g) xs _
      exact ⟨hst, Lost.trans (lost_reviewNode_sons g h hs x (by omega) (by omega)) hlost hpr h1.nd⟩
  have main : ∀ (ks : List Int) (g' : GPathM), PStateG g' → OwnSymmetric g' →
      g'.current_step - 2 = g.current_step - 2 → (∀ k ∈ ks, 0 ≤ k ∧ k ≤ g.current_step - 2) →
      Lost g' (reviewSteps g' (·.sons) ks) := by
    intro ks
    induction ks with
    | nil => intro g' _ _ _ _; exact Lost.refl g'
    | cons k ks ih =>
      intro g' h hs hc hks
      unfold reviewSteps
      split
      · have hk := hks k List.mem_cons_self
        have hstep := (pruned_reviewLine (·.sons) k g').step_eq
        have hL : ∀ id ∈ (g'.line k).map (·.id), id.id.step = k := fun id hid => by
          obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hid
          exact eq_of_beq (List.mem_filter.mp hn).2
        obtain ⟨⟨h1, hs1⟩, hlost⟩ := hline k hk.1 _ g' h hs (by omega) hL
        exact Lost.trans hlost
          (ih _ h1 hs1 (by show (reviewLine g' _ k).current_step - _ = _; rw [hstep]; exact hc)
            (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')))
          (pruned_reviewSteps _ ks _) h1.nd
      · exact Lost.refl g'
  exact main _ g h hs rfl (fun _ hk => ⟨mem_intRange_lower (List.mem_reverse.mp hk),
    mem_intRange_upper (List.mem_reverse.mp hk)⟩)

/-- **S1′ para las dos pasadas de una vuelta** (review simétrico, tu postulado flexible): desde la
salida de `cleanInvalid₂` hasta el final de la vuelta, una entrada que sigue viva y sale de una tabla
deja a su par separado en algún paso —en la tabla de uno o en la del otro—, sin más hipótesis que
`PStateG` y la simetría a la salida de la limpieza. -/
theorem commonLoss_round (g : GPathM) (h : PStateG (cleanInvalid₂ g))
    (hs : OwnSymmetric (cleanInvalid₂ g)) : Lost (cleanInvalid₂ g) (reviewPass g) := by
  obtain ⟨h1, hs1⟩ := pstateGS_reviewParents _ h hs
  exact Lost.trans (lost_reviewParents _ h hs) (lost_reviewSons _ h1 hs1) (pruned_reviewSons _) h1.nd

/-- info: 'AbsSat.GraphPath.Model.SymInvariant.commonLoss_round' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonLoss_round

end AbsSat.GraphPath.Model.SymInvariant
