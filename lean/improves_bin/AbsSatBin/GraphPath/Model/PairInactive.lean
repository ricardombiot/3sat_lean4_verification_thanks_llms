-- lean/improves_bin/AbsSatBin/GraphPath/Model/PairInactive.lean
import AbsSatBin.GraphPath.Model.CleanTwoPhase

/-!
# With the pair rule, the aggressive sweep does nothing: `reviewAgg = review`

Ported from `lean_project` (only what the result needs):

* `SegReview` — what `reviewNode` (with the mirror) does to the tables (`reviewNode_owners`);
* `SymInvariant` — the review keeps `OwnSymmetric` (`OwnSymmetric_review`, hypothesis `RevOk`);
* `PinDoomed.AggInactive` and `PairHelly` B5–B6a — after the clean with pairs the rule removes
  nothing (`pairFixed_cleanPair`), and at the review's fixpoint the aggressive sweep is the identity
  (`aggInactive_of_revOk`).

New here: **`reviewAgg_eq_review`** and **`filterAllAgg_eq_filterAll`**: under `RevOk`, the aggressive
review *is* the review. That is why the reader and Julia (commit `4c644ac`) use the plain one.
-/

namespace AbsSatBin.GraphPath.Model.PairInactive

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Threaded (OwnSymmetric)
open AbsSatBin.GraphPath.Model.AggressiveReview

/-- Los ids no se duplican: el corte los preserva uno a uno. -/
theorem NodupIds_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, (f n).id = n.id) (h : NodupIds g) : NodupIds (updateAt g id f) := by
  have he : ((updateAt g id f).nodes.map (·.id)) = g.nodes.map (·.id) := by
    simp only [updateAt, updateAtGo, List.map_map, Function.comp_def]
    refine List.map_congr_left (fun n _ => ?_)
    cases hb : n.id == id with
    | true => exact hf n
    | false => rfl
  unfold NodupIds
  rw [he]
  exact h

/-- Y el desenlace también. -/
theorem NodupIds_unlinkIncompatible (g : GPathM) (id : PathNodeId) (h : NodupIds g) :
    NodupIds (unlinkIncompatible g id) := by
  cases hn : g.node? id with
  | none =>
    have he : unlinkIncompatible g id = g := by unfold unlinkIncompatible; rw [hn]
    rw [he]; exact h
  | some n =>
    have hshape : (unlinkIncompatible g id).nodes = g.nodes.map (unlinkMap n id) := by
      simp only [unlinkIncompatible, hn]
    unfold NodupIds
    rw [hshape, List.map_map, Function.comp_def]
    have he : (fun x : PNodeM => (unlinkMap n id x).id) = (fun x : PNodeM => x.id) := by
      funext x; rw [unlinkMap_id]
    rw [he]
    exact h

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



/-- **Inversión del desenlace: todo nodo del resultado viene de uno del original, con su misma
tabla.** -/
theorem unlinkIncompatible_node?_inv (g : GPathM) (hnd : NodupIds g) (r x : PathNodeId)
    (nx : PNodeM) (hx : (unlinkIncompatible g r).node? x = some nx) :
    ∃ nx0, g.node? x = some nx0 ∧ nx.owners = nx0.owners := by
  cases hnr : g.node? r with
  | none =>
    have he : unlinkIncompatible g r = g := by unfold unlinkIncompatible; rw [hnr]
    rw [he] at hx
    exact ⟨nx, hx, rfl⟩
  | some n =>
    have hshape : (unlinkIncompatible g r).nodes = g.nodes.map (unlinkMap n r) := by
      simp only [unlinkIncompatible, hnr]
    have hmem : nx ∈ (unlinkIncompatible g r).nodes := List.mem_of_find?_eq_some hx
    rw [hshape] at hmem
    obtain ⟨nx0, hnx0, heq⟩ := List.mem_map.mp hmem
    have hxid : nx.id = x := node?_id_eq _ x nx hx
    have h0id : nx0.id = x := by rw [← hxid, ← heq, unlinkMap_id]
    exact ⟨nx0, by rw [← h0id]; exact node?_of_mem hnd nx0 hnx0, by rw [← heq, unlinkMap_owners]⟩

/-- **Inversión del borrado, igual.** `removeNode` filtra y re-enlaza, pero no toca tablas. -/
theorem removeNode_node?_inv (g : GPathM) (hnd : NodupIds g) (r x : PathNodeId)
    (nx : PNodeM) (hx : (removeNode g r).node? x = some nx) :
    ∃ nx0, g.node? x = some nx0 ∧ nx.owners = nx0.owners := by
  have hmem : nx ∈ (removeNode g r).nodes := List.mem_of_find?_eq_some hx
  rw [removeNode_nodes] at hmem
  obtain ⟨nx0, hnx0, heq⟩ := List.mem_map.mp hmem
  have hxid : nx.id = x := node?_id_eq _ x nx hx
  have h0id : nx0.id = x := by rw [← hxid, ← heq]; rfl
  exact ⟨nx0, by rw [← h0id]; exact node?_of_mem hnd nx0 (List.mem_filter.mp hnx0).1,
    by rw [← heq]; rfl⟩

-- ============================================================
-- Lo que `reviewNode` hace a las tablas
-- ============================================================

theorem removeNode_ne (g : GPathM) (x y : PathNodeId) (n' : PNodeM)
    (h : (removeNode g x).node? y = some n') : y ≠ x := by
  have hmem : n' ∈ (removeNode g x).nodes := List.mem_of_find?_eq_some h
  rw [removeNode_nodes] at hmem
  obtain ⟨n0, hn0, heq⟩ := List.mem_map.mp hmem
  have hid : n'.id = y := node?_id_eq _ y n' h
  have hne := (List.mem_filter.mp hn0).2
  intro hyx
  rw [← heq] at hid
  have : n0.id = x := by rw [← hyx]; exact hid
  simp [this] at hne

/-- `y` sobrevive al corte de `x`: si `x` tenía a `y` en su tabla, lo sigue teniendo tras cortarla con
la unión de sus vecinos. Es la condición para que el espejo no le quite `x` a `y`. -/
def MirrorKeeps (g : GPathM) (nb : PNodeM → List PathNodeId) (x y : PathNodeId) : Prop :=
  ∀ dx, g.node? x = some dx → y ∈ dx.owners → y ∈ intersectOwners dx.owners (unionOwnersOf g (nb dx))

/-- The mirror leaves the cut node's own table alone: if `x` lost itself, it is not in its cut. -/
theorem mirrorMap_self_cut (x : PathNodeId) (d : PNodeM) (B : List PathNodeId) (hd : d.id = x) :
    (mirrorMap x (cutRemoved d B) { d with owners := intersectOwners d.owners B }).owners
      = intersectOwners d.owners B := by
  unfold GPathM.mirrorMap
  split
  · next hc =>
    refine List.filter_eq_self.mpr (fun q hq => bne_iff_ne.mpr (fun hqx => ?_))
    have hxr : x ∈ cutRemoved d B := by
      have : (cutRemoved d B).contains d.id = true := hc
      rw [hd] at this
      exact List.contains_iff_mem.mp this
    have hq' : x ∈ intersectOwners d.owners B := hqx ▸ hq
    exact ((mem_cutRemoved d B x).mp hxr).2 hq'
  · rfl

/-- A node that does not hold `x` is untouched by the mirror of `x`. -/
theorem mirrorMap_of_not_mem (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM)
    (h : x ∉ m.owners) : mirrorMap x rem m = m := by
  unfold GPathM.mirrorMap
  split
  · have hf : m.owners.filter (· != x) = m.owners :=
      List.filter_eq_self.mpr (fun q hq => bne_iff_ne.mpr (fun he => h (he ▸ hq)))
    rw [hf]
  · rfl

/-- The mirror leaves the cut node itself alone. -/
theorem mirrorMap_self_cut_eq (x : PathNodeId) (d : PNodeM) (B : List PathNodeId) (hd : d.id = x) :
    mirrorMap x (cutRemoved d B) { d with owners := intersectOwners d.owners B }
      = { d with owners := intersectOwners d.owners B } := by
  cases hc : (cutRemoved d B).contains x with
  | false => exact mirrorMap_of_not x _ _ (by show (cutRemoved d B).contains d.id = false; rw [hd]; exact hc)
  | true =>
    refine mirrorMap_of_not_mem x _ _ (fun hx => ?_)
    exact ((mem_cutRemoved d B x).mp (List.contains_iff_mem.mp hc)).2 hx

theorem NodupIds_mirrorDrop (g : GPathM) (x : PathNodeId) (rem : List PathNodeId) (h : NodupIds g) :
    NodupIds (mirrorDrop g x rem) := by
  unfold NodupIds mirrorDrop
  simp only [List.map_map, Function.comp_def, mirrorMap_id]
  exact h

/-- **Las tablas tras `reviewNode x`** (con espejo). La de `x`, la de antes cortada con la unión de
las de sus vecinos. La de otro nodo `y`, la de antes salvo, quizá, la entrada `x` —el espejo—, que
solo se va si el corte de `x` dejó fuera a `y`. -/
theorem reviewNode_owners (g : GPathM) (hnd : NodupIds g) (nb : PNodeM → List PathNodeId)
    (x y : PathNodeId) (n' : PNodeM) (h : (reviewNode g nb x).node? y = some n') :
    ∃ n, g.node? y = some n ∧
      (y ≠ x → (∀ q ∈ n'.owners, q ∈ n.owners) ∧ (∀ q ∈ n.owners, q ≠ x → q ∈ n'.owners) ∧
        (MirrorKeeps g nb x y → n'.owners = n.owners) ∧
        (x ∈ n'.owners → ((reviewNode g nb x).node? x).isSome = true → MirrorKeeps g nb x y)) ∧
      (y = x → n'.owners = intersectOwners n.owners (unionOwnersOf g (nb n))) := by
  unfold reviewNode at h
  cases hd : g.node? x with
  | none =>
    rw [hd] at h
    refine ⟨n', h, fun _ => ⟨fun _ hq => hq, fun _ hq _ => hq, fun _ => rfl,
      fun _ _ dx hdx => by rw [hd] at hdx; cases hdx⟩, fun hyx => ?_⟩
    rw [hyx, hd] at h; cases h
  | some d =>
    rw [hd] at h
    simp only at h
    have hf : ∀ n : PNodeM,
        ({ n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) } : PNodeM).id = n.id :=
      fun _ => rfl
    have hnd1 := NodupIds_updateAt g x _ hf hnd
    have hnd1m := NodupIds_mirrorDrop _ x (cutRemoved d (unionOwnersOf g (nb d))) hnd1
    have hnd2 := NodupIds_unlinkIncompatible _ x hnd1m
    -- the three properties, from `n'.owners = (mirrorMap x rem n).owners`
    have props : ∀ n n2 : PNodeM, g.node? y = some n →
        n2.owners = (mirrorMap x (cutRemoved d (unionOwnersOf g (nb d))) n).owners →
        (∀ q ∈ n2.owners, q ∈ n.owners) ∧ (∀ q ∈ n.owners, q ≠ x → q ∈ n2.owners) ∧
          (MirrorKeeps g nb x y → n2.owners = n.owners) ∧ (x ∈ n2.owners → MirrorKeeps g nb x y) := by
      intro n n2 hn ho
      refine ⟨fun q hq => by rw [ho] at hq; exact mirrorMap_owners_sub _ _ n q hq,
        fun q hq hqx => by rw [ho]; exact mirrorMap_owners_keep _ _ n q hq hqx, fun hmk => ?_,
        fun hx dx hdx hin => ?_⟩
      · have hnot : (cutRemoved d (unionOwnersOf g (nb d))).contains n.id = false := by
          rw [node?_id_eq g y n hn]
          exact not_mem_cutRemoved d _ y (fun hq => hmk d hd hq)
        rw [ho, mirrorMap_of_not _ _ n hnot]
      · rw [hd] at hdx
        cases hdx
        cases hc : (cutRemoved d (unionOwnersOf g (nb d))).contains y with
        | true =>
          rw [ho] at hx
          unfold GPathM.mirrorMap at hx
          rw [if_pos (by rw [node?_id_eq g y n hn]; exact hc)] at hx
          have := (List.mem_filter.mp hx).2
          simp at this
        | false =>
          cases hcut : (intersectOwners d.owners (unionOwnersOf g (nb d))).contains y with
          | true => exact List.contains_iff_mem.mp hcut
          | false =>
            have hmem : y ∈ cutRemoved d (unionOwnersOf g (nb d)) :=
              (mem_cutRemoved d _ y).mpr ⟨hin, fun h => by
                rw [List.contains_iff_mem.mpr h] at hcut; exact Bool.noConfusion hcut⟩
            rw [List.contains_iff_mem.mpr hmem] at hc
            exact absurd hc (by simp)
    have fromG2 : ∀ n2, (unlinkIncompatible (mirrorDrop (updateAt g x (fun n =>
          { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x
          (cutRemoved d (unionOwnersOf g (nb d)))) x).node? y = some n2 →
        ∃ n, g.node? y = some n ∧
          (y ≠ x → n2.owners = (mirrorMap x (cutRemoved d (unionOwnersOf g (nb d))) n).owners) ∧
          (y = x → n2.owners = intersectOwners n.owners (unionOwnersOf g (nb n))) := by
      intro n2 hn2
      obtain ⟨n1m, hn1m, ho1⟩ := unlinkIncompatible_node?_inv _ hnd1m x y n2 hn2
      obtain ⟨n1, hn1, hmeq⟩ := mirrorDrop_node?_inv _ x _ y n1m hn1m
      obtain ⟨n0, hn0, heq⟩ := Reader.updateAt_node?_inv g x _ hf y n1 hn1
      have hn0id : n0.id = y := node?_id_eq g y n0 hn0
      refine ⟨n0, hn0, fun hne => ?_, fun hyx => ?_⟩
      · have hb : (n0.id == x) = false := by rw [hn0id]; exact beq_false_of_ne hne
        rw [ho1, hmeq, heq, hb]
      · have hb : (n0.id == x) = true := by rw [hn0id, hyx]; exact beq_self_eq_true x
        have hdn : d = n0 := by rw [hyx] at hn0; exact Option.some.inj (hd.symm.trans hn0)
        rw [ho1, hmeq, heq, hb]
        dsimp only
        rw [← hdn]
        exact mirrorMap_self_cut x d _ (node?_id_eq g x d hd)
    have hgone : ∀ G : GPathM, ((removeNode G x).node? x).isSome = false := by
      intro G
      cases hG : (removeNode G x).node? x with
      | none => rfl
      | some m => exact absurd rfl (removeNode_ne _ x x m hG)
    split at h
    · next hv1 =>
      split at h
      · obtain ⟨n, hn, hne, heq⟩ := fromG2 n' h
        exact ⟨n, hn, fun hyx => by
          obtain ⟨a, b, c, e⟩ := props n n' hn (hne hyx)
          exact ⟨a, b, c, fun hx _ => e hx⟩, heq⟩
      · next hv2 =>
        have hne := removeNode_ne _ x y n' h
        obtain ⟨n2, hn2, ho2⟩ := removeNode_node?_inv _ hnd2 x y n' h
        obtain ⟨n, hn, hne', _⟩ := fromG2 n2 hn2
        refine ⟨n, hn, fun _ => ?_, fun hyx => absurd hyx hne⟩
        obtain ⟨a, b, c, _⟩ := props n n' hn (by rw [ho2]; exact hne' hne)
        refine ⟨a, b, c, fun _ hk => absurd hk ?_⟩
        simp only [reviewNode, hd, hv1, hv2, Bool.false_eq_true, ↓reduceIte, hgone]
        exact id
    · next hv1 =>
      have hne := removeNode_ne _ x y n' h
      obtain ⟨n0, hn0, ho0⟩ := removeNode_node?_inv _ hnd x y n' h
      refine ⟨n0, hn0, fun _ => ⟨fun q hq => by rw [ho0] at hq; exact hq,
        fun q hq _ => by rw [ho0]; exact hq, fun _ => ho0, fun _ hk => absurd hk ?_⟩,
        fun hyx => absurd hyx hne⟩
      simp only [reviewNode, hd, hv1, Bool.false_eq_true, ↓reduceIte, hgone]
      exact id

/-- info: 'AbsSatBin.GraphPath.Model.PairInactive.reviewNode_owners' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reviewNode_owners


-- ============================================================
-- Un paso de una pasada
-- ============================================================

/-- **`reviewNode` conserva la simetría** (review simétrico). Si `x` corta a `q`, el espejo le quita
`x` a `q`; si `q` conserva a `x`, es que el corte de `x` conservó a `q`; y las demás entradas no se
mueven. -/
theorem OwnSymmetric_reviewNode (g : GPathM) (hnd : NodupIds g) (nb : PNodeM → List PathNodeId)
    (x : PathNodeId) (h : OwnSymmetric g) : OwnSymmetric (reviewNode g nb x) := by
  intro p n' q m' hp hq hqn
  obtain ⟨np, hnp, hp1, hp2⟩ := reviewNode_owners g hnd nb x p n' hp
  obtain ⟨nq, hnq, hq1, hq2⟩ := reviewNode_owners g hnd nb x q m' hq
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

/-- info: 'AbsSatBin.GraphPath.Model.PairInactive.OwnSymmetric_reviewNode' depends on axioms: [propext, Quot.sound] -/
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

/-- info: 'AbsSatBin.GraphPath.Model.PairInactive.OwnSymmetric_cleanInvalid₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_cleanInvalid₂

-- ============================================================
-- Una vuelta y el review base
-- ============================================================

-- ============================================================
-- La regla de parejas (plan `pair_mode`)
-- ============================================================

/-- **El test de pareja es simétrico.** -/
theorem pairShares_comm (cs : Int) (a b : List PathNodeId) : pairShares cs a b = pairShares cs b a := by
  unfold pairShares
  congr 1
  funext k
  have hab : (ownersAt a k).any (fun r => b.contains r) = (ownersAt b k).any (fun r => a.contains r) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, ownersAt, List.mem_filter, List.elem_iff, beq_iff_eq]
    constructor
    · rintro ⟨r, ⟨hra, hrk⟩, hrb⟩; exact ⟨r, ⟨hrb, hrk⟩, hra⟩
    · rintro ⟨r, ⟨hrb, hrk⟩, hra⟩; exact ⟨r, ⟨hra, hrk⟩, hrb⟩
  rw [hab]
  cases hasStepEntry a k <;> cases hasStepEntry b k <;> rfl

theorem nodupIds_pairSweep (g : GPathM) (h : NodupIds g) : NodupIds (pairSweep g) := by
  unfold NodupIds
  show ((g.nodes.map (pairMap g)).map (·.id)).Nodup
  rw [List.map_map]
  exact h

/-- **La regla de parejas conserva la simetría**: quita `w` de la tabla de `n` exactamente cuando
quita `n` de la de `w`, porque el test es simétrico. -/
theorem OwnSymmetric_pairSweep (g : GPathM) (h : OwnSymmetric g) : OwnSymmetric (pairSweep g) := by
  intro p n' q m' hp hq hqn
  obtain ⟨n, hn, rfl⟩ := pairSweep_node?_inv g p n' hp
  obtain ⟨m, hm, rfl⟩ := pairSweep_node?_inv g q m' hq
  obtain ⟨hqn0, hbad⟩ := (mem_pairMap_owners g n q).mp hqn
  have hpm := h p n q m hn hm hqn0
  refine (mem_pairMap_owners g m p).mpr ⟨hpm, ?_⟩
  have hnid : n.id = p := node?_id_eq g p n hn
  have hmid : m.id = q := node?_id_eq g q m hm
  unfold pairBad at hbad ⊢
  rw [hm] at hbad
  rw [hn]
  by_cases hpq : p = q
  · subst hpq; rw [hmid]; simp
  · have hsh : pairShares g.current_step n.owners m.owners = true := by
      cases hs : pairShares g.current_step n.owners m.owners
      · exfalso
        simp only [hs, hnid, Bool.not_false, Bool.and_true, bne_eq_false_iff_eq] at hbad
        exact hpq hbad.symm
      · rfl
    have hsh' : pairShares g.current_step m.owners n.owners = true := by
      rw [pairShares_comm]; exact hsh
    simp only [hsh', Bool.not_true, Bool.and_false]

/-- **La limpieza con parejas conserva la simetría**, si su resultado es válido. -/
theorem OwnSymmetric_cleanPair (g : GPathM) (hnd : NodupIds g) (hsh : ShapeOk g)
    (h : OwnSymmetric g) (hv : isValid (cleanPair g) = true) :
    NodupIds (cleanPair g) ∧ OwnSymmetric (cleanPair g) := by
  have key := cleanPair_inv
    (fun x => NodupIds x ∧ ShapeOk x ∧ Pruned g x ∧ (isValid x = true → OwnSymmetric x)) g
    ⟨CleanTwoPhase.nodupIds_cleanInvalid₂ g hnd, hsh.of_pruned (pruned_cleanInvalid₂ g),
      pruned_cleanInvalid₂ g, fun hv' => OwnSymmetric_cleanInvalid₂ g hnd hsh h hv'⟩
    (fun x hvx ⟨hnx, hsx, hpx, hsymx⟩ =>
      ⟨CleanTwoPhase.nodupIds_cleanInvalid₂ _ (nodupIds_pairSweep x hnx),
        hsx.of_pruned (Pruned.trans (pruned_pairSweep x) (pruned_cleanInvalid₂ _)),
        Pruned.trans hpx (Pruned.trans (pruned_pairSweep x) (pruned_cleanInvalid₂ _)),
        fun hv' => OwnSymmetric_cleanInvalid₂ _ (nodupIds_pairSweep x hnx)
          (hsx.of_pruned (pruned_pairSweep x)) (OwnSymmetric_pairSweep x (hsymx hvx)) hv'⟩)
  exact ⟨key.1, key.2.2.2 hv⟩

/-- Lo que el review arrastra para la simetría. -/
structure RevOk (g : GPathM) : Prop where
  nd : NodupIds g
  sh : ShapeOk g
  sym : OwnSymmetric g

/-- **Una vuelta conserva la simetría**, si su resultado es válido. -/
theorem OwnSymmetric_reviewPass (g : GPathM) (h : RevOk g) (hv : isValid (reviewPass g) = true) :
    OwnSymmetric (reviewPass g) := by
  have hpr : Pruned (cleanPair g) (reviewPass g) :=
    Pruned.trans (pruned_reviewParents _) (pruned_reviewSons _)
  have hv' : isValid (cleanPair g) = true := Certifies.isValid_of_pruned hpr hv
  have hc : SymOk (cleanPair g) := by
    obtain ⟨h1, h2⟩ := OwnSymmetric_cleanPair g h.nd h.sh h.sym hv'
    exact ⟨h1, h2⟩
  exact (symOk_reviewSons _ (symOk_reviewParents _ hc)).2

theorem RevOk_reviewPass (g : GPathM) (h : RevOk g) (hv : isValid (reviewPass g) = true) :
    RevOk (reviewPass g) :=
  ⟨List.Sublist.nodup (NodeIds.ids_reviewPass g) h.nd, h.sh.of_pruned (pruned_reviewPass g),
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
  ⟨NodeIds.NodupIds_review g h.nd, h.sh.of_pruned (pruned_review g), OwnSymmetric_review g h hv⟩

-- ============================================================
-- El barrido agresivo
-- ============================================================


/-- **El barrido agresivo no quita nada tras el review base.** -/
def AggInactive (X : GPathM) : Prop :=
  isValid (review X) = true → ¬ measure (aggSweep (review X)) < measure (review X)

-- ============================================================
-- B5. `PairOk`: tras la limpieza con parejas, la regla ya no quita nada
-- ============================================================

/-- **La regla no quita nada**: toda pareja de nodos vivos que se poseen comparte entrada en cada paso
común. -/
def PairFixed (g : GPathM) : Prop := pairSweep g = g

/-- Lo mismo, dicho pareja a pareja. -/
def PairOk (g : GPathM) : Prop :=
  ∀ x n w, g.node? x = some n → w ∈ n.owners → w ≠ x → ∀ nw, g.node? w = some nw →
    pairShares g.current_step n.owners nw.owners = true

theorem pairBad_false_of_fixed (g : GPathM) (h : PairFixed g) (n : PNodeM) (hn : n ∈ g.nodes)
    (w : PathNodeId) (hw : w ∈ n.owners) : pairBad g n w = false := by
  have hmap : g.nodes.map (pairMap g) = g.nodes := congrArg GPathM.nodes h
  have hn' := map_fixed_pointwise (pairMap g) g.nodes hmap n hn
  have hw' : w ∈ (pairMap g n).owners := by rw [hn']; exact hw
  exact ((mem_pairMap_owners g n w).mp hw').2

theorem pairOk_of_fixed (g : GPathM) (h : PairFixed g) : PairOk g := by
  intro x n w hn hw hwx nw hnw
  have hb := pairBad_false_of_fixed g h n (List.mem_of_find?_eq_some hn) w hw
  have hnid : n.id = x := node?_id_eq g x n hn
  unfold pairBad at hb
  rw [hnw] at hb
  have hne : (w != n.id) = true := by rw [hnid]; exact bne_iff_ne.mpr hwx
  rw [hne, Bool.true_and] at hb
  cases hs : pairShares g.current_step n.owners nw.owners
  · simp only [hs, Bool.not_false] at hb; exact absurd hb (by decide)
  · rfl

/-- El bucle de la regla, con combustible de sobra, termina en un estado que la regla no toca, si es
válido. -/
theorem pairFixed_pairFuel : ∀ (fuel : Nat) (g : GPathM), measure g < fuel →
    isValid (pairFuel fuel g) = true → PairFixed (pairFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro g hlt hv
    by_cases hg : isValid g = true
    · by_cases hdec : measure (pairSweep g) < measure g
      · have he : pairFuel (f + 1) g = pairFuel f (cleanInvalid₂ (pairSweep g)) := by
          simp only [pairFuel, hg, if_true, hdec]
        rw [he] at hv ⊢
        have hm := measure_cleanInvalid₂_le (pairSweep g)
        exact ih _ (by omega) hv
      · have he : pairFuel (f + 1) g = g := by
          simp only [pairFuel, hg, if_true, hdec, if_false]
        rw [he]
        exact pairSweep_eq_self g (Nat.le_antisymm (measure_pairSweep_le g) (Nat.not_lt.mp hdec))
    · have he : pairFuel (f + 1) g = g := by simp only [pairFuel, hg, Bool.false_eq_true, if_false]
      rw [he] at hv
      exact absurd hv hg

/-- **Tras la limpieza con parejas, si el estado es válido, la regla ya no quita nada.** -/
theorem pairFixed_cleanPair (g : GPathM) (hv : isValid (cleanPair g) = true) :
    PairFixed (cleanPair g) :=
  pairFixed_pairFuel _ _ (Nat.lt_succ_self _) hv

theorem pairOk_cleanPair (g : GPathM) (hv : isValid (cleanPair g) = true) : PairOk (cleanPair g) :=
  pairOk_of_fixed _ (pairFixed_cleanPair g hv)

/-- info: 'AbsSatBin.GraphPath.Model.PairInactive.pairOk_cleanPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairOk_cleanPair

-- ============================================================
-- B6a. El barrido agresivo no actúa en el punto fijo del review
-- ============================================================

/-- En el punto fijo de una vuelta, la limpieza con parejas es la identidad, y por tanto la regla. -/
theorem pairFixed_of_reviewPass_eq (g : GPathM) (hv : isValid g = true) (h : reviewPass g = g) :
    PairFixed g := by
  have h₁ := measure_cleanPair_le g
  have h₂ := measure_reviewParents_le (cleanPair g)
  have h₃ := measure_reviewSons_le (reviewParents (cleanPair g))
  have hm : measure (reviewPass g) = measure g := by rw [h]
  simp only [reviewPass] at hm
  have hcp := cleanPair_eq_self g (by omega)
  have hfix := pairFixed_cleanPair g (by rw [hcp.2]; exact hv)
  rw [hcp.2] at hfix
  exact hfix

/-- Con la tabla entera en cada paso (nodo válido), el test de pareja es el del filtro agresivo. -/
theorem sharesEveryStep_of_pairShares (g : GPathM) (nx : PNodeM) (hvx : isValidNode g nx = true)
    (wo : List PathNodeId) (h : pairShares g.current_step nx.owners wo = true) :
    sharesEveryStep g.current_step nx.owners wo = true := by
  have hok := owners_ok_of_isValidNode g nx hvx
  unfold sharesEveryStep
  unfold pairShares at h
  rw [List.all_eq_true] at h hok ⊢
  intro k hk
  have h1 := h k hk
  have h2 := hok k hk
  rw [h2] at h1
  simpa using h1

/-- **Un par del barrido no hace nada** en un estado simétrico, con la regla en su punto fijo y todo
nodo válido. -/
theorem aggPair_eq_self (g : GPathM) (hs : OwnSymmetric g) (hp : PairFixed g)
    (hval : ∀ n ∈ g.nodes, isValidNode g n = true) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (w : PathNodeId) (hw : w ∈ nx.owners) : aggPair g x w = g := by
  unfold aggPair
  rw [hx]
  cases hnw : g.node? w with
  | none => rfl
  | some nw =>
    simp only
    have hxw : x ∈ nw.owners := hs x nx w nw hx hnw hw
    have hvx := hval nx (List.mem_of_find?_eq_some hx)
    have hsh : sharesEveryStep g.current_step nx.owners nw.owners = true := by
      by_cases hwx : w = x
      · subst hwx
        rw [hx] at hnw
        obtain rfl := Option.some.inj hnw
        exact sharesEveryStep_self _ _
      · exact sharesEveryStep_of_pairShares g nx hvx _
          (pairOk_of_fixed g hp x nx w hx hw hwx nw hnw)
    simp [hsh]
    intro _ _ hn; exact absurd hxw hn

theorem foldl_eq_self {β : Type} (f : GPathM → β → GPathM) (g : GPathM) :
    ∀ (l : List β), (∀ b ∈ l, f g b = g) → l.foldl f g = g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro h
    simp only [List.foldl_cons, h b List.mem_cons_self]
    exact ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

/-- **Un nodo del barrido no hace nada.** -/
theorem aggNode_eq_self (g : GPathM) (hs : OwnSymmetric g) (hp : PairFixed g)
    (hval : ∀ n ∈ g.nodes, isValidNode g n = true) (x : PathNodeId) : aggNode g x = g := by
  unfold aggNode
  cases hx : g.node? x with
  | none => rfl
  | some nx =>
    simp only
    have hvx := hval nx (List.mem_of_find?_eq_some hx)
    have hin : (intRange 0 (g.current_step - 1)).reverse.foldl
        (fun g kw => (ownersAtNow g x kw).foldl (fun g w => aggPair g x w) g) g = g := by
      refine foldl_eq_self _ g _ (fun kw _ => ?_)
      refine foldl_eq_self _ g _ (fun w hw => ?_)
      have hw' : w ∈ nx.owners := by
        simp only [ownersAtNow, ownersOf, hx, ownersAt, List.mem_filter] at hw
        exact hw.1
      exact aggPair_eq_self g hs hp hval x nx hx w hw'
    simp only [hvx, if_true, hin, hx]

/-- **El barrido agresivo no hace nada** en un estado simétrico, con la regla en su punto fijo y todo
nodo válido. -/
theorem aggSweep_eq_self (g : GPathM) (hs : OwnSymmetric g) (hp : PairFixed g)
    (hval : ∀ n ∈ g.nodes, isValidNode g n = true) : aggSweep g = g := by
  unfold aggSweep
  split
  · refine foldl_eq_self _ g _ (fun k _ => ?_)
    exact foldl_eq_self _ g _ (fun x _ => aggNode_eq_self g hs hp hval x)
  · rfl

/-- **`AggInactive` es un teorema** con la regla de parejas: en el punto fijo del review base, válido,
el barrido agresivo es la identidad. -/
theorem aggInactive_of_revOk (X : GPathM) (hr : RevOk X) : AggInactive X := by
  intro hv hlt
  have hs := OwnSymmetric_review X hr hv
  have hfix := reviewPass_review X hv
  have hp := pairFixed_of_reviewPass_eq (review X) hv hfix
  have hval : ∀ n ∈ (review X).nodes, isValidNode (review X) n = true := by
    intro n hn
    have hnd := NodeIds.NodupIds_review X hr.nd
    exact review_node_valid X hv n.id n (node?_of_mem hnd n hn)
  rw [aggSweep_eq_self _ hs hp hval] at hlt
  exact Nat.lt_irrefl _ hlt

/-- info: 'AbsSatBin.GraphPath.Model.PairInactive.aggInactive_of_revOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms aggInactive_of_revOk


-- ============================================================
-- The aggressive review is the review
-- ============================================================

/-- **Under `RevOk`, the aggressive review is the review.** Its loop runs one base review; if that is
valid, the sweep does not lower the measure (`aggInactive_of_revOk`), so the loop stops there. -/
theorem reviewAgg_eq_review (X : GPathM) (hr : RevOk X) : reviewAgg X = review X := by
  have hin := aggInactive_of_revOk X hr
  unfold reviewAgg
  show reviewAggFuel (measure X + 1) X = review X
  simp only [reviewAggFuel]
  by_cases hv : isValid (review X) = true
  · rw [if_pos hv, if_neg (hin hv)]
  · rw [if_neg hv]

/-- **Pinning with the aggressive review is pinning with the review**, when the filtered state
carries `RevOk`. -/
theorem filterAllAgg_eq_filterAll (g : GPathM) (reqs : List NodeId)
    (hr : RevOk (reqs.foldl filterRequire g)) : filterAllAgg g reqs = filterAll g reqs :=
  reviewAgg_eq_review _ hr

/-- info: 'AbsSatBin.GraphPath.Model.PairInactive.filterAllAgg_eq_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filterAllAgg_eq_filterAll

end AbsSatBin.GraphPath.Model.PairInactive
