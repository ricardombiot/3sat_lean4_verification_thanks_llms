-- lean_project/AbsSat/GraphPath/Model/SupportSplit.lean
import AbsSat.GraphPath.Model.ReviewJoin

/-!
# The review of a join splits into the reviews of its sides

`ReviewJoin` asks that reviewing a join keeps nothing the reviewed sides do not. The review is a
greatest fixpoint, and the project already has its fixpoint theory: a **support relation** inside a
state (`AnchoredSurvive.Sup`) survives the aggressive review of that state (`AOk_filterAllAgg`).

So it is enough to split the support that the review of the join keeps into a support inside each
side.

* **`reviewJoin_of_split`** — `SupportSplit ⟹ ReviewJoin`: if the entries of the reviewed join are
  covered by a support relation inside each side, each survives the review of its side, so the reviewed
  join sits inside the join of the reviewed sides, and a side with a member is valid.
* **`sup_greatest`** — the union of all support relations inside a state is one. So the best split is
  the greatest support of each side, and the only statement left is **`SupportCover`**: *every entry of
  the reviewed join lies in a support relation inside one of the sides* — no borrowing, in its exact
  form (`supportSplit_of_cover`, `sat_of_cover`).

A concrete split, `PartSplit` (entries anchored at a top node of the side), holds at every join the
driver performs (probe `helly split`, 0 exceptions) but fails at the joins of single-key pieces that
`split_branch` merges, where the sides can share a top node (probe `helly pieces`). The distributive
equations themselves hold there too, so the open statement is `SupportCover`, not `PartSplit`.
-/

namespace AbsSat.GraphPath.Model.SupportSplit

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv MInv_join)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk AOk_filterAllAgg)
open AbsSat.GraphPath.Model.ReviewJoin
open AbsSat.GraphPath.Model.PickInduction (gowner_of_isValid)

variable (φ : Cnf)

-- ============================================================
-- The split
-- ============================================================

/-- An entry of `R` that `S`'s tables also carry. -/
def RelIn (R S : GPathM) (x v : PathNodeId) : Prop := Rel R x v ∧ Rel S x v

/-- A node of both `R` and `S` at the top step. -/
def TopIn (R S : GPathM) (z : PathNodeId) : Prop :=
  Mem R z ∧ Mem S z ∧ z.id.step = R.current_step - 1

/-- **The part of `S`**: entries of `R` in `S`'s tables, anchored at a top node of `S`. -/
def Part (R S : GPathM) (x v : PathNodeId) : Prop :=
  RelIn R S x v ∧ ∃ z, TopIn R S z ∧ RelIn R S x z ∧ RelIn R S v z

/-- The members of the part of `S`. -/
def PMem (R S : GPathM) (x : PathNodeId) : Prop := ∃ v, Part R S x v

/-- The top-anchored parts, as a candidate split. They satisfy every condition at the joins the driver
performs (probe `helly split`), but **not** at the joins of single-key pieces that `split_branch`
merges, where two sides can share a top node (probe `helly pieces`); the split below does not depend
on them. -/
def PartSplit (a b : GPathM) : Prop :=
  (∀ x v, Rel (reviewAgg (join a b)) x v →
      Part (reviewAgg (join a b)) a x v ∨ Part (reviewAgg (join a b)) b x v) ∧
    Sup a (PMem (reviewAgg (join a b)) a) (Part (reviewAgg (join a b)) a) ∧
    Sup b (PMem (reviewAgg (join a b)) b) (Part (reviewAgg (join a b)) b)

/-- A node of both `R` and `S` at step `t`. -/
def AtIn (R S : GPathM) (t : Int) (z : PathNodeId) : Prop := Mem R z ∧ Mem S z ∧ z.id.step = t

/-- **The part of `S` anchored at step `t`**: entries of `R` in `S`'s tables, with a common owner at step
`t` that is a node of `S`, through entries also in `S`'s tables. -/
def PartAt (R S : GPathM) (t : Int) (x v : PathNodeId) : Prop :=
  RelIn R S x v ∧ ∃ z, AtIn R S t z ∧ RelIn R S x z ∧ RelIn R S v z

/-- `t` separates the two sides inside `R`: no node of `R` at step `t` is a node of both. -/
def Separates (R a b : GPathM) (t : Int) : Prop :=
  0 ≤ t ∧ t < R.current_step ∧ ∀ z, Mem R z → z.id.step = t → Mem a z → Mem b z → False

/-- **The split at the separation step.** Measured: at the driver's joins (where the top step
separates) and at the joins of pieces `split_branch` merges (where it lies lower), the parts anchored
at the highest separating step cover `R` and satisfy every condition of `Sup` (probes `helly split`,
`helly pieces`). -/
def PartSplitAt (a b : GPathM) (t : Int) : Prop :=
  (∀ x v, Rel (reviewAgg (join a b)) x v →
      PartAt (reviewAgg (join a b)) a t x v ∨ PartAt (reviewAgg (join a b)) b t x v) ∧
    Sup a (fun x => ∃ v, PartAt (reviewAgg (join a b)) a t x v) (PartAt (reviewAgg (join a b)) a t) ∧
    Sup b (fun x => ∃ v, PartAt (reviewAgg (join a b)) b t x v) (PartAt (reviewAgg (join a b)) b t)

/-- **A split of the reviewed join's support**: two support relations, one inside each side, that
together cover every entry of the reviewed join. -/
def SplitOk (a b : GPathM) : Prop :=
  ∃ (SA : PathNodeId → Prop) (RA : PathNodeId → PathNodeId → Prop)
    (SB : PathNodeId → Prop) (RB : PathNodeId → PathNodeId → Prop),
    (∀ x v, Rel (reviewAgg (join a b)) x v → RA x v ∨ RB x v) ∧ Sup a SA RA ∧ Sup b SB RB

theorem splitOk_of_partSplit (a b : GPathM) (h : PartSplit a b) : SplitOk a b :=
  ⟨_, _, _, _, h.1, h.2.1, h.2.2⟩

theorem splitOk_of_partSplitAt (a b : GPathM) (t : Int) (h : PartSplitAt a b t) : SplitOk a b :=
  ⟨_, _, _, _, h.1, h.2.1, h.2.2⟩

/-- **The support of the reviewed join splits** into supports of the two pinned sides. -/
def SupportSplit : Prop :=
  ∀ (k : Int) (key : NodeId) (e h : GPathM), StateOkF φ k (key, e) → StateOkF φ k (key, h) →
    MInv φ e → MInv φ h → ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
    isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true →
      SplitOk (pinned e ws rq) (pinned h ws rq)

-- ============================================================
-- The greatest support inside a state
-- ============================================================

/-- A member of some support relation inside `S`. -/
def GMem (S : GPathM) (x : PathNodeId) : Prop :=
  ∃ (Sm : PathNodeId → Prop) (Rr : PathNodeId → PathNodeId → Prop), Sup S Sm Rr ∧ Sm x

/-- An entry of some support relation inside `S`. -/
def GRel (S : GPathM) (x v : PathNodeId) : Prop :=
  ∃ (Sm : PathNodeId → Prop) (Rr : PathNodeId → PathNodeId → Prop), Sup S Sm Rr ∧ Rr x v

/-- **The union of all support relations inside a state is a support relation.** Every condition of
`Sup` is local to the relation that holds the entry, so the union keeps them all. -/
theorem sup_greatest (S : GPathM) : Sup S (GMem S) (GRel S) where
  gow p := fun ⟨_, _, h, hp⟩ => h.gow p hp
  node p := fun ⟨_, _, h, hp⟩ => h.node p hp
  step p := fun ⟨_, _, h, hp⟩ => h.step p hp
  dom x v := fun ⟨Sm, Rr, h, hr⟩ => ⟨⟨Sm, Rr, h, (h.dom x v hr).1⟩, ⟨Sm, Rr, h, (h.dom x v hr).2⟩⟩
  own x v n := fun ⟨_, _, h, hr⟩ hn => h.own x v n hr hn
  cov x := fun ⟨Sm, Rr, h, hx⟩ l h0 h1 => by
    obtain ⟨v, hv, hs⟩ := h.cov x hx l h0 h1
    exact ⟨v, ⟨Sm, Rr, h, hv⟩, hs⟩
  par x d := fun _ hd hne v ⟨Sm, Rr, h, hv⟩ => by
    obtain ⟨c, hc, h1, h2, h3⟩ := h.par x d (h.dom x v hv).1 hd hne v hv
    exact ⟨c, hc, ⟨Sm, Rr, h, h1⟩, ⟨Sm, Rr, h, h2⟩, ⟨Sm, Rr, h, h3⟩⟩
  son x := fun _ hs v ⟨Sm, Rr, h, hv⟩ => by
    obtain ⟨c, m, hm, hx, h1, h2, h3⟩ := h.son x (h.dom x v hv).1 hs v hv
    exact ⟨c, m, hm, hx, ⟨Sm, Rr, h, h1⟩, ⟨Sm, Rr, h, h2⟩, ⟨Sm, Rr, h, h3⟩⟩
  agg x v := fun ⟨Sm, Rr, h, hv⟩ l h0 h1 => by
    obtain ⟨z, h1', h2', hz⟩ := h.agg x v hv l h0 h1
    exact ⟨z, ⟨Sm, Rr, h, h1'⟩, ⟨Sm, Rr, h, h2'⟩, hz⟩
  sym x v := fun ⟨Sm, Rr, h, hv⟩ => ⟨Sm, Rr, h, h.sym x v hv⟩
  link x c d := fun ⟨Sm, Rr, h, h1⟩ _ hs hd => h.link x c d h1 (h.sym x c h1) hs hd

/-- **No borrowing, in its exact form**: every entry of the reviewed join lies in a support relation
inside one of the two pinned sides. -/
def SupportCover : Prop :=
  ∀ (k : Int) (key : NodeId) (e h : GPathM), StateOkF φ k (key, e) → StateOkF φ k (key, h) →
    MInv φ e → MInv φ h → ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
    isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true →
      ∀ x v, Rel (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) x v →
        GRel (pinned e ws rq) x v ∨ GRel (pinned h ws rq) x v

theorem supportSplit_of_cover (hC : SupportCover φ) : SupportSplit φ := by
  intro k key e h hse hsh hme hmh ws rq hv
  exact ⟨_, _, _, _, hC k key e h hse hsh hme hmh ws rq hv, sup_greatest _, sup_greatest _⟩

-- ============================================================
-- Supports give validity and embeddings
-- ============================================================

/-- A state holding a support relation with a member is valid. -/
theorem valid_of_sup (G : GPathM) (S : PathNodeId → Prop) (Rr : PathNodeId → PathNodeId → Prop)
    (h : Sup G S Rr) (x : PathNodeId) (hx : S x) : isValid G = true := by
  simp only [isValid, List.all_eq_true]
  intro k hk
  have h0 := mem_intRange_lower hk
  have h1 := mem_intRange_upper hk
  obtain ⟨v, hv, hvs⟩ := h.cov x hx k h0 (by omega)
  exact List.any_eq_true.mpr ⟨v, h.gow v (h.dom x v hv).2, beq_iff_eq.mpr hvs⟩

/-- A support relation inside a state survives its aggressive review. -/
theorem sup_reviewAgg (G : GPathM) (S : PathNodeId → Prop) (Rr : PathNodeId → PathNodeId → Prop)
    (h : Sup G S Rr) (hsmp : Sons.SMP G) (hnr : Parents.NotRoot G) : Sup (reviewAgg G) S Rr :=
  (AOk_filterAllAgg G ⟨h, hsmp, hnr⟩ [] (fun _ hr => absurd hr List.not_mem_nil)).sup

/-- Nodes of a reviewed side are nodes of the join of the reviewed sides, keeping owners and parents. -/
theorem join_node_left (A B : GPathM) (p : PathNodeId) (n : PNodeM) (h : A.node? p = some n) :
    ∃ n', (join A B).node? p = some n' ∧ (∀ q ∈ n.owners, q ∈ n'.owners) ∧ (∀ q ∈ n.parents, q ∈ n'.parents) := by
  obtain ⟨n', hn', ho, hp, _⟩ := (grown_join_left A B).node?_grown p n h
  exact ⟨n', hn', ho, hp⟩

theorem join_node_right (A B : GPathM) (p : PathNodeId) (n : PNodeM) (h : B.node? p = some n) :
    ∃ n', (join A B).node? p = some n' ∧ (∀ q ∈ n.owners, q ∈ n'.owners) ∧ (∀ q ∈ n.parents, q ∈ n'.parents) := by
  obtain ⟨n', hn', ho, hp, _⟩ := join_node?_right A B p n h
  exact ⟨n', hn', ho, hp⟩

theorem mem_of_hasNode' (R : GPathM) (ad : AdjacentOwners.Adj R) {q : PathNodeId} (hq : GownersNodes.HasNode R q) : Mem R q := by
  obtain ⟨m, hm, hmid⟩ := hq
  exact ⟨m, by rw [← hmid]; exact node?_of_mem ad.rc.nodup m hm⟩

theorem rel_self (R : GPathM) (ad : AdjacentOwners.Adj R) {p : PathNodeId} (hp : Mem R p) : Rel R p p := by
  obtain ⟨m, hm⟩ := hp
  exact ⟨m, hm, ad.ctx.self p m hm, ⟨m, hm⟩⟩

/-- **Two sides.** If the entries of `R` are covered by two support relations of two states, `R` sits
inside their join. -/
theorem embedded_join_of_cover (R : GPathM) (ad : AdjacentOwners.Adj R) (GA GB : GPathM) (SA SB : PathNodeId → Prop)
    (RA RB : PathNodeId → PathNodeId → Prop) (hA : Sup GA SA RA) (hB : Sup GB SB RB)
    (hstep : R.current_step = GA.current_step)
    (hcov : ∀ x v, Rel R x v → RA x v ∨ RB x v) : Embedded R (join GA GB) := by
  -- the node of the join at a member, and that every side's node there is inside it
  have nodeOf : ∀ p, (RA p p ∨ RB p p) → ∃ n', (join GA GB).node? p = some n' ∧
      (∀ nA, GA.node? p = some nA → (∀ q ∈ nA.owners, q ∈ n'.owners) ∧ (∀ q ∈ nA.parents, q ∈ n'.parents)) ∧
      (∀ nB, GB.node? p = some nB → (∀ q ∈ nB.owners, q ∈ n'.owners) ∧ (∀ q ∈ nB.parents, q ∈ n'.parents)) := by
    intro p hp
    have both : ∀ n', (join GA GB).node? p = some n' →
        (∀ nA, GA.node? p = some nA → (∀ q ∈ nA.owners, q ∈ n'.owners) ∧ (∀ q ∈ nA.parents, q ∈ n'.parents)) ∧
        (∀ nB, GB.node? p = some nB → (∀ q ∈ nB.owners, q ∈ n'.owners) ∧ (∀ q ∈ nB.parents, q ∈ n'.parents)) := by
      intro n' hn'
      refine ⟨fun nA hnA => ?_, fun nB hnB => ?_⟩
      · obtain ⟨n'', hn'', ho, hpa⟩ := join_node_left GA GB p nA hnA
        rw [hn'] at hn''
        cases hn''
        exact ⟨ho, hpa⟩
      · obtain ⟨n'', hn'', ho, hpa⟩ := join_node_right GA GB p nB hnB
        rw [hn'] at hn''
        cases hn''
        exact ⟨ho, hpa⟩
    rcases hp with hp | hp
    · obtain ⟨nA, hnA⟩ := Option.isSome_iff_exists.mp (hA.node p (hA.dom p p hp).1)
      obtain ⟨n', hn', _, _⟩ := join_node_left GA GB p nA hnA
      exact ⟨n', hn', both n' hn'⟩
    · obtain ⟨nB, hnB⟩ := Option.isSome_iff_exists.mp (hB.node p (hB.dom p p hp).1)
      obtain ⟨n', hn', _, _⟩ := join_node_right GA GB p nB hnB
      exact ⟨n', hn', both n' hn'⟩
  refine ⟨hstep, ?_, ?_⟩
  · intro p hp
    have hmem := mem_of_hasNode' R ad (ad.rc.gn p hp)
    show p ∈ GA.gowners ++ GB.gowners.filter (fun q => !GA.gowners.contains q)
    rcases hcov p p (rel_self R ad hmem) with h | h
    · exact List.mem_append_left _ (hA.gow p (hA.dom p p h).1)
    · have hg := hB.gow p (hB.dom p p h).1
      cases hc : GA.gowners.contains p with
      | true => exact List.mem_append_left _ (List.mem_of_elem_eq_true hc)
      | false => exact List.mem_append_right _ (List.mem_filter.mpr ⟨hg, by rw [hc]; rfl⟩)
  · intro p m hm
    obtain ⟨n', hn', hallA, hallB⟩ := nodeOf p (hcov p p (rel_self R ad ⟨m, hm⟩))
    refine ⟨n', hn', fun q hq hqm => ?_, fun q hq hqm => ?_⟩
    · rcases hcov p q ⟨m, hm, hq, hqm⟩ with h | h
      · obtain ⟨nA, hnA⟩ := Option.isSome_iff_exists.mp (hA.node p (hA.dom p q h).1)
        exact (hallA nA hnA).1 q (hA.own p q nA h hnA)
      · obtain ⟨nB, hnB⟩ := Option.isSome_iff_exists.mp (hB.node p (hB.dom p q h).1)
        exact (hallB nB hnB).1 q (hB.own p q nB h hnB)
    · have hmem := List.mem_of_find?_eq_some hm
      have hid := node?_id_eq R p m hm
      have hstepq : q.id.step + 1 = p.id.step := by
        have := ad.rc.shape.pbelow m hmem q hq
        rw [hid] at this
        have h0 := (mem_bounds R ad ⟨m, hm⟩).1
        have h0' := (mem_bounds R ad hqm).1
        omega
      rcases hcov p q ⟨m, hm, (ad.links p m hm).1 q hq, hqm⟩ with h | h
      · obtain ⟨nA, hnA⟩ := Option.isSome_iff_exists.mp (hA.node p (hA.dom p q h).1)
        exact (hallA nA hnA).2 q (hA.link p q nA h (hA.sym p q h) hstepq hnA)
      · obtain ⟨nB, hnB⟩ := Option.isSome_iff_exists.mp (hB.node p (hB.dom p q h).1)
        exact (hallB nB hnB).2 q (hB.link p q nB h (hB.sym p q h) hstepq hnB)

/-- **One side.** If a single support relation covers `R`, `R` sits inside its state. -/
theorem embedded_of_cover (R : GPathM) (ad : AdjacentOwners.Adj R) (G : GPathM) (S : PathNodeId → Prop) (Rr : PathNodeId → PathNodeId → Prop)
    (h : Sup G S Rr) (hstep : R.current_step = G.current_step)
    (hcov : ∀ x v, Rel R x v → Rr x v) : Embedded R G := by
  refine ⟨hstep, ?_, ?_⟩
  · intro p hp
    have hmem := mem_of_hasNode' R ad (ad.rc.gn p hp)
    exact h.gow p (h.dom p p (hcov p p (rel_self R ad hmem))).1
  · intro p m hm
    have hpp := hcov p p (rel_self R ad ⟨m, hm⟩)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p (h.dom p p hpp).1)
    refine ⟨n, hn, fun q hq hqm => h.own p q n (hcov p q ⟨m, hm, hq, hqm⟩) hn, fun q hq hqm => ?_⟩
    have hmem := List.mem_of_find?_eq_some hm
    have hid := node?_id_eq R p m hm
    have hstepq : q.id.step + 1 = p.id.step := by
      have := ad.rc.shape.pbelow m hmem q hq
      rw [hid] at this
      have h0 := (mem_bounds R ad ⟨m, hm⟩).1
      omega
    have hr := hcov p q ⟨m, hm, (ad.links p m hm).1 q hq, hqm⟩
    exact h.link p q n hr (h.sym p q hr) hstepq hn


-- ============================================================
-- SupportSplit ⟹ ReviewJoin
-- ============================================================

theorem frame_pinned (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) :
    (pinned g ws rq).nodes = g.nodes := by
  have hframe : ∀ (l : List NodeId) (g : GPathM), (l.foldl filterRequire g).nodes = g.nodes := by
    intro l
    induction l with
    | nil => intro g; rfl
    | cons r rs ih => intro g; exact ih (filterRequire g r)
  show (rq.foldl filterRequire (filterWeakAll g ws)).nodes = g.nodes
  rw [hframe, (filterWeakAll_frame ws g).1]

theorem nonneg_of_mapNodes (k : Int) (d : NodeId) (h : d ∈ mapNodes φ k) : 0 ≤ k := by
  unfold mapNodes at h
  split at h
  · exact absurd h List.not_mem_nil
  · omega

/-- **The review of a join, from the split of its support.** -/
theorem reviewJoin_of_split (_hwf : WF φ) (hS : SupportSplit φ) : ReviewJoin φ := by
  intro k key e h hse hsh hme hmh ws rq hv
  obtain ⟨SA, RA, SB, RB, hcov, hsa, hsb⟩ := hS k key e h hse hsh hme hmh ws rq hv
  -- the reviewed join is a reader's state
  have hok := okJoin_of_stateOkF φ k key e h hse hsh
  have hmJ := MInv_join φ e h hok hme hmh
  have hpJ : pinned (join e h) ws rq = join (pinned e ws rq) (pinned h ws rq) := by
    show rq.foldl filterRequire (filterWeakAll (join e h) ws) = _
    rw [filterWeakAll_join, foldl_filterRequire_join]
  have hRdef : filterAllAgg (filterWeakAll (join e h) ws) rq =
      reviewAgg (join (pinned e ws rq) (pinned h ws rq)) := by
    rw [← hpJ]; rfl
  have hR : ReadableAgg (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) := by
    rw [← hRdef]
    exact ⟨filterWeakAll (join e h) ws, rq,
      ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmJ.rctx, rfl⟩
  have hwn := (filterWeakAll_frame ws (join e h)).1
  have hpW : Sons.PMS (filterWeakAll (join e h) ws) := by unfold Sons.PMS; rw [hwn]; exact hmJ.pms
  have hnS : Sons.SN (filterWeakAll (join e h) ws) := by
    unfold Sons.SN GownersNodes.HasNode; rw [hwn]; exact hmJ.sn
  have hpms : Sons.PMS (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) := by
    rw [← hRdef]; exact AggInvariants.PMS_filterAllAgg _ _ hpW
  have hsn : Sons.SN (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) := by
    rw [← hRdef]; exact AggInvariants.SN_filterAllAgg _ _ hnS
  have ad := AdjacentOwners.adj_of_readable _ hR hv hpms hsn
  -- the sides keep the shape the survival lemma needs
  have smpS : ∀ g, MInv φ g → Sons.SMP (pinned g ws rq) := by
    intro g hm; unfold Sons.SMP; rw [frame_pinned]; exact hm.smp
  have nrS : ∀ g, MInv φ g → Parents.NotRoot (pinned g ws rq) := by
    intro g hm; unfold Parents.NotRoot; rw [frame_pinned]; exact hm.rctx.shape.notroot
  have supA := sup_reviewAgg _ _ _ hsa (smpS e hme) (nrS e hme)
  have supB := sup_reviewAgg _ _ _ hsb (smpS h hmh) (nrS h hmh)
  have hstepA : (reviewAgg (join (pinned e ws rq) (pinned h ws rq))).current_step =
      (reviewAgg (pinned e ws rq)).current_step := by
    rw [(pruned_reviewAgg _).step_eq, (pruned_reviewAgg _).step_eq]; rfl
  have hstepB : (reviewAgg (join (pinned e ws rq) (pinned h ws rq))).current_step =
      (reviewAgg (pinned h ws rq)).current_step := by
    rw [(pruned_reviewAgg _).step_eq, (pruned_reviewAgg _).step_eq]
    show (pinned e ws rq).current_step = (pinned h ws rq).current_step
    have h1 : (pinned e ws rq).current_step = e.current_step := by
      rw [← (pruned_reviewAgg (pinned e ws rq)).step_eq]
      exact (reviewed_facts φ k key e hse hme ws rq).1.trans hse.step.symm
    have h2 : (pinned h ws rq).current_step = h.current_step := by
      rw [← (pruned_reviewAgg (pinned h ws rq)).step_eq]
      exact (reviewed_facts φ k key h hsh hmh ws rq).1.trans hsh.step.symm
    rw [h1, h2, hse.step, hsh.step]
  -- a member of `R`, in one of the parts
  obtain ⟨p, hp, _⟩ := gowner_of_isValid _ hv 0 (by omega) (by
    rw [hstepA, (pruned_reviewAgg _).step_eq]
    have := (reviewed_facts φ k key e hse hme ws rq).1
    rw [(pruned_reviewAgg _).step_eq] at this
    have := nonneg_of_mapNodes φ k key hse.onMap
    omega)
  have hmem := mem_of_hasNode' _ ad (ad.rc.gn p hp)
  -- decide by the validity of the reviewed sides
  cases hvA : isValid (reviewAgg (pinned e ws rq)) with
  | true =>
    cases hvB : isValid (reviewAgg (pinned h ws rq)) with
    | true => exact Or.inl ⟨rfl, rfl, embedded_join_of_cover _ ad _ _ _ _ _ _ supA supB hstepA hcov⟩
    | false =>
      refine Or.inr (Or.inl ⟨rfl, embedded_of_cover _ ad _ _ _ supA hstepA ?_⟩)
      intro x v hr
      rcases hcov x v hr with h1 | h1
      · exact h1
      · have := valid_of_sup _ _ _ supB x (hsb.dom x v h1).1
        rw [hvB] at this; exact absurd this (by decide)
  | false =>
    have noA : ∀ x v, ¬ RA x v := by
      intro x v h1
      have := valid_of_sup _ _ _ supA x (hsa.dom x v h1).1
      rw [hvA] at this; exact absurd this (by decide)
    have allB : ∀ x v, Rel (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) x v → RB x v := by
      intro x v hr
      rcases hcov x v hr with h1 | h1
      · exact absurd h1 (noA x v)
      · exact h1
    exact Or.inr (Or.inr ⟨valid_of_sup _ _ _ supB p (hsb.dom p p (allB p p (rel_self _ ad hmem))).1,
      embedded_of_cover _ ad _ _ _ supB hstepB allB⟩)

/-- **The Improves verdict from the split of the review's support.** -/
theorem sat_of_split (hwf : WF φ) (hS : SupportSplit φ) (hog : ReviewJoin.OwnGowPinned)
    (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_reviewJoin φ hwf (reviewJoin_of_split φ hwf hS) hog kv hkv hv

/-- **The Improves verdict from no borrowing**: every entry of a reviewed join lies in a support inside
one of its sides. -/
theorem sat_of_cover (hwf : WF φ) (hC : SupportCover φ) (hog : ReviewJoin.OwnGowPinned)
    (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_split φ hwf (supportSplit_of_cover φ hC) hog kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.SupportSplit.sat_of_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_cover

/-- info: 'AbsSat.GraphPath.Model.SupportSplit.sat_of_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_split

end AbsSat.GraphPath.Model.SupportSplit
