-- lean_project/AbsSat/GraphPath/Model/PartSplitReal.lean
import AbsSat.GraphPath.Model.JoinSide

/-!
# The support conditions of the parts, from paths

In the author's machine (`send_to_destine!`, `sat_machine.jl`) the union at a destination
(`impact!`) is **not** reviewed; the review of the union comes at the next send, after the next
destination's requirements are pinned. That is exactly `SupportSplit`'s shape: the review of the join of
the two **pinned** sides.

The top-anchored split (`SupportSplit.PartSplit`) asks for three things: every entry of the reviewed
join is in a part (cover), and each part is a support relation inside its side (eleven conditions).
This module derives **all of them** from one statement per side:

* **`SurvivorsRealized R S`** — every entry of the reviewed join `R` that `S`'s tables carry lies on a
  path of `S` (a sound chain of the pinned side).

A path gives everything at once: its node at any step is a common neighbour (coverage, the common-owner
rule), its neighbours below and above are the parent and son the rules ask for, its top node is the
anchor, and the path survives the join and the review, so all these entries are entries of `R` too.

* **`part_of_chains`** — two nodes of a path of `S` that survives into `R` are in `S`'s part.
* **`sup_part_of_realized`** — the part of `S` is a support relation inside `S`.
* **`partSplit_of_realized`** — the whole split, under `SurvivorsRealized` for both sides.
-/

namespace AbsSat.GraphPath.Model.PartSplitReal

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup)
open AbsSat.GraphPath.Model.SupportSplit (RelIn TopIn Part PMem PartSplit)
open AbsSat.GraphPath.Model.JoinSide (rel_of_chain rel_side)

/-- A path of `S` through two nodes, that survives into `R`. -/
def Through (R S : GPathM) (x v : PathNodeId) : Prop :=
  ∃ sel, ChainSound S sel ∧ ChainSound R sel ∧ 0 ≤ x.id.step ∧ x.id.step < S.current_step ∧
    0 ≤ v.id.step ∧ v.id.step < S.current_step ∧ sel x.id.step = x ∧ sel v.id.step = v

theorem mem_of_chain (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) (k : Int)
    (h0 : 0 ≤ k) (h1 : k < g.current_step) : Mem g (sel k) := by
  obtain ⟨hs, _⟩ := h.chain.1.1 k h0 h1
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨m, hm⟩

/-- **Two nodes of a surviving path are in the part.** -/
theorem part_of_chains (R S : GPathM) (sel : Int → PathNodeId) (hS : ChainSound S sel)
    (hR : ChainSound R sel) (hcs : R.current_step = S.current_step) (i j : Int)
    (hi0 : 0 ≤ i) (hi1 : i < S.current_step) (hj0 : 0 ≤ j) (hj1 : j < S.current_step) :
    Part R S (sel i) (sel j) := by
  have ht0 : 0 ≤ S.current_step - 1 := by omega
  have ht1 : S.current_step - 1 < S.current_step := by omega
  have ri := rel_of_chain R sel hR j i hj0 (by omega) hi0 (by omega)
  have si := rel_of_chain S sel hS j i hj0 hj1 hi0 hi1
  refine ⟨⟨ri, si⟩, sel (S.current_step - 1),
    ⟨mem_of_chain R sel hR _ ht0 (by omega), mem_of_chain S sel hS _ ht0 ht1, ?_⟩,
    ⟨rel_of_chain R sel hR _ i ht0 (by omega) hi0 (by omega), rel_of_chain S sel hS _ i ht0 ht1 hi0 hi1⟩,
    ⟨rel_of_chain R sel hR _ j ht0 (by omega) hj0 (by omega), rel_of_chain S sel hS _ j ht0 ht1 hj0 hj1⟩⟩
  rw [hcs]; exact (hS.chain.1.1 _ ht0 ht1).2

/-- **The part of `S` is a support inside `S`**, when every entry of it lies on a surviving path. -/
theorem sup_part_of_realized (R S : GPathM) (hcs : R.current_step = S.current_step)
    (hreal : ∀ x v, RelIn R S x v → Through R S x v) : Sup S (PMem R S) (Part R S) := by
  have thr : ∀ x v, Part R S x v → Through R S x v := fun x v h => hreal x v h.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- gow
    rintro p ⟨v, hp⟩
    obtain ⟨sel, hS, _, h0, h1, _, _, hsx, _⟩ := thr p v hp
    have := hS.chain.2.2 p.id.step h0 h1
    rw [hsx] at this; exact this
  · -- node
    rintro p ⟨v, hp⟩
    obtain ⟨sel, hS, _, h0, h1, _, _, hsx, _⟩ := thr p v hp
    have := (hS.chain.1.1 p.id.step h0 h1).1
    rw [hsx] at this; exact this
  · -- step
    rintro p ⟨v, hp⟩
    obtain ⟨sel, _, _, h0, h1, _, _, _, _⟩ := thr p v hp
    exact ⟨h0, h1⟩
  · -- dom
    intro x v h
    obtain ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ := thr x v h
    refine ⟨⟨v, h⟩, ⟨x, ?_⟩⟩
    have := part_of_chains R S sel hS hR hcs v.id.step x.id.step hv0 hv1 hx0 hx1
    rw [hsx, hsv] at this; exact this
  · -- own
    intro x v n h hn
    obtain ⟨m, hm, hv, _⟩ := h.1.2
    rw [hn] at hm; cases hm; exact hv
  · -- cov
    rintro x ⟨v, h⟩ l hl0 hl1
    obtain ⟨sel, hS, hR, hx0, hx1, _, _, hsx, _⟩ := thr x v h
    refine ⟨sel l, ?_, (hS.chain.1.1 l hl0 hl1).2⟩
    have := part_of_chains R S sel hS hR hcs x.id.step l hx0 hx1 hl0 hl1
    rw [hsx] at this; exact this
  · -- par
    rintro x d ⟨w, hw⟩ hd hne v hv
    obtain ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ := thr x v hv
    have hxpos : 0 < x.id.step := by
      by_cases hz : x.id.step = 0
      · exfalso; apply hne
        have := hS.root_shape.1
        rw [← hz, hsx] at this; exact this
      · omega
    have hlink := hS.chain.1.2 (x.id.step - 1) (by omega) (by omega)
    rw [show x.id.step - 1 + 1 = x.id.step by omega, hsx, hd] at hlink
    have p1 := part_of_chains R S sel hS hR hcs x.id.step (x.id.step - 1) hx0 hx1 (by omega) (by omega)
    have p2 := part_of_chains R S sel hS hR hcs (x.id.step - 1) x.id.step (by omega) (by omega) hx0 hx1
    have p3 := part_of_chains R S sel hS hR hcs (x.id.step - 1) v.id.step (by omega) (by omega) hv0 hv1
    rw [hsx] at p1 p2
    rw [hsv] at p3
    exact ⟨sel (x.id.step - 1), hlink, p1, p2, p3⟩
  · -- son
    rintro x ⟨w, hw⟩ htop v hv
    obtain ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ := thr x v hv
    have hup : x.id.step + 1 < S.current_step := by omega
    obtain ⟨hs, _⟩ := hS.chain.1.1 (x.id.step + 1) (by omega) hup
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    have hlink := hS.chain.1.2 x.id.step hx0 hup
    rw [hm, hsx] at hlink
    have p1 := part_of_chains R S sel hS hR hcs x.id.step (x.id.step + 1) hx0 hx1 (by omega) hup
    have p2 := part_of_chains R S sel hS hR hcs (x.id.step + 1) x.id.step (by omega) hup hx0 hx1
    have p3 := part_of_chains R S sel hS hR hcs (x.id.step + 1) v.id.step (by omega) hup hv0 hv1
    rw [hsx] at p1 p2
    rw [hsv] at p3
    exact ⟨sel (x.id.step + 1), m, hm, hlink, p1, p2, p3⟩
  · -- agg
    intro x v h l hl0 hl1
    obtain ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ := thr x v h
    have p1 := part_of_chains R S sel hS hR hcs x.id.step l hx0 hx1 hl0 hl1
    have p2 := part_of_chains R S sel hS hR hcs v.id.step l hv0 hv1 hl0 hl1
    rw [hsx] at p1
    rw [hsv] at p2
    exact ⟨sel l, p1, p2, (hS.chain.1.1 l hl0 hl1).2⟩
  · -- sym
    intro x v h
    obtain ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ := thr x v h
    have := part_of_chains R S sel hS hR hcs v.id.step x.id.step hv0 hv1 hx0 hx1
    rw [hsx, hsv] at this; exact this
  · -- link
    intro x c d hxc _ hs hd
    obtain ⟨sel, hS, _, hx0, hx1, hc0, _, hsx, hsc⟩ := thr x c hxc
    have hlink := hS.chain.1.2 c.id.step hc0 (by omega)
    rw [hs, hsx, hd, hsc] at hlink
    exact hlink

/-- `grown_join_right` with only the steps equal (the pinned sides need not be valid). -/
theorem grown_join_right_of_step (g₁ g₂ : GPathM) (hstep : g₁.current_step = g₂.current_step) :
    Grown g₂ (join g₁ g₂) where
  step_eq := hstep
  gowners_grown q hq := by
    show q ∈ g₁.gowners ++ g₂.gowners.filter (fun x => !g₁.gowners.contains x)
    cases hc : g₁.gowners.contains q with
    | true => exact List.mem_append_left _ (List.mem_of_elem_eq_true hc)
    | false => exact List.mem_append_right _ (List.mem_filter.mpr ⟨hq, by simp only [hc]; rfl⟩)
  node?_grown := join_node?_right g₁ g₂

/-- **Every entry carried by a side lies on a path of that side** (a path of the pinned side). -/
def SurvivorsRealized (R S : GPathM) : Prop :=
  ∀ x v, Rel R x v → Rel S x v → Exactness.Realizes S x v

/-- **The split, from paths.** If each side realizes the entries of the reviewed join that its tables
carry, the top-anchored split holds: cover and both support relations. -/
theorem partSplit_of_realized (a b : GPathM) (hstep : a.current_step = b.current_step) (hnd : NodupIds (join a b))
    (hndA : NodupIds a) (hndB : NodupIds b)
    (hownA : ∀ n ∈ a.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode a q)
    (hownB : ∀ n ∈ b.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode b q)
    (hbA : ∀ p, Mem a p → 0 ≤ p.id.step ∧ p.id.step < a.current_step)
    (hbB : ∀ p, Mem b p → 0 ≤ p.id.step ∧ p.id.step < b.current_step)
    (hA : SurvivorsRealized (reviewAgg (join a b)) a) (hB : SurvivorsRealized (reviewAgg (join a b)) b) :
    PartSplit a b := by
  have hpr := pruned_reviewAgg (join a b)
  have gA := grown_join_left a b
  have gB := grown_join_right_of_step a b hstep
  have hcsA : (reviewAgg (join a b)).current_step = a.current_step := hpr.step_eq.trans gA.step_eq.symm
  have hcsB : (reviewAgg (join a b)).current_step = b.current_step := hpr.step_eq.trans gB.step_eq
  have through : ∀ S, Grown S (join a b) → (reviewAgg (join a b)).current_step = S.current_step →
      (∀ p, Mem S p → 0 ≤ p.id.step ∧ p.id.step < S.current_step) →
      SurvivorsRealized (reviewAgg (join a b)) S →
      ∀ x v, RelIn (reviewAgg (join a b)) S x v → Through (reviewAgg (join a b)) S x v := by
    intro S hg _ hb hr x v ⟨hR, hS⟩
    obtain ⟨sel, hsc, hsx, hsv⟩ := hr x v hR hS
    obtain ⟨m, hm, _, hmv⟩ := hS
    obtain ⟨hx0, hx1⟩ := hb x ⟨m, hm⟩
    obtain ⟨hv0, hv1⟩ := hb v hmv
    exact ⟨sel, hsc, ChainSound_reviewAgg _ sel (ChainSound_of_grown hg sel hsc), hx0, hx1, hv0, hv1,
      hsx, hsv⟩
  have tA := through a gA hcsA hbA hA
  have tB := through b gB hcsB hbB hB
  refine ⟨fun x v hxv => ?_, sup_part_of_realized _ a hcsA tA, sup_part_of_realized _ b hcsB tB⟩
  rcases rel_side a b _ hpr hnd hndA hndB hownA hownB hxv with hxa | hxb
  · obtain ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ := tA x v ⟨hxv, hxa⟩
    have := part_of_chains _ a sel hS hR hcsA x.id.step v.id.step hx0 hx1 hv0 hv1
    rw [hsx, hsv] at this; exact Or.inl this
  · obtain ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ := tB x v ⟨hxv, hxb⟩
    have := part_of_chains _ b sel hS hR hcsB x.id.step v.id.step hx0 hx1 hv0 hv1
    rw [hsx, hsv] at this; exact Or.inr this

-- ============================================================
-- The split by paths: every entry on a path of one side
-- ============================================================

/-- Two nodes of a surviving path: a pair the path goes through. -/
theorem through_of_chain (R S : GPathM) (sel : Int → PathNodeId) (hS : ChainSound S sel)
    (hR : ChainSound R sel) (i j : Int) (hi0 : 0 ≤ i) (hi1 : i < S.current_step) (hj0 : 0 ≤ j)
    (hj1 : j < S.current_step) : Through R S (sel i) (sel j) := by
  have hsi := (hS.chain.1.1 i hi0 hi1).2
  have hsj := (hS.chain.1.1 j hj0 hj1).2
  exact ⟨sel, hS, hR, by rw [hsi]; exact hi0, by rw [hsi]; exact hi1, by rw [hsj]; exact hj0,
    by rw [hsj]; exact hj1, by rw [hsi], by rw [hsj]⟩

/-- **The pairs on surviving paths of `S` are a support inside `S`.** -/
theorem sup_through (R S : GPathM) : Sup S (fun x => ∃ v, Through R S x v) (Through R S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨v, sel, hS, _, h0, h1, _, _, hsx, _⟩
    have := hS.chain.2.2 p.id.step h0 h1
    rw [hsx] at this; exact this
  · rintro p ⟨v, sel, hS, _, h0, h1, _, _, hsx, _⟩
    have := (hS.chain.1.1 p.id.step h0 h1).1
    rw [hsx] at this; exact this
  · rintro p ⟨v, sel, _, _, h0, h1, _, _, _, _⟩
    exact ⟨h0, h1⟩
  · intro x v h
    obtain ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ := h
    refine ⟨⟨v, sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩, ⟨x, ?_⟩⟩
    have := through_of_chain R S sel hS hR v.id.step x.id.step hv0 hv1 hx0 hx1
    rw [hsx, hsv] at this; exact this
  · intro x v n h hn
    obtain ⟨sel, hS, _, hx0, hx1, hv0, hv1, hsx, hsv⟩ := h
    have := rel_of_chain S sel hS v.id.step x.id.step hv0 hv1 hx0 hx1
    rw [hsx, hsv] at this
    obtain ⟨m, hm, hin, _⟩ := this
    rw [hn] at hm; cases hm; exact hin
  · rintro x ⟨v, sel, hS, hR, hx0, hx1, _, _, hsx, _⟩ l hl0 hl1
    refine ⟨sel l, ?_, (hS.chain.1.1 l hl0 hl1).2⟩
    have := through_of_chain R S sel hS hR x.id.step l hx0 hx1 hl0 hl1
    rw [hsx] at this; exact this
  · rintro x d _ hd hne v ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩
    have hxpos : 0 < x.id.step := by
      by_cases hz : x.id.step = 0
      · exfalso; apply hne
        have := hS.root_shape.1
        rw [← hz, hsx] at this; exact this
      · omega
    have hlink := hS.chain.1.2 (x.id.step - 1) (by omega) (by omega)
    rw [show x.id.step - 1 + 1 = x.id.step by omega, hsx, hd] at hlink
    have p1 := through_of_chain R S sel hS hR x.id.step (x.id.step - 1) hx0 hx1 (by omega) (by omega)
    have p2 := through_of_chain R S sel hS hR (x.id.step - 1) x.id.step (by omega) (by omega) hx0 hx1
    have p3 := through_of_chain R S sel hS hR (x.id.step - 1) v.id.step (by omega) (by omega) hv0 hv1
    rw [hsx] at p1 p2
    rw [hsv] at p3
    exact ⟨sel (x.id.step - 1), hlink, p1, p2, p3⟩
  · rintro x _ htop v ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩
    have hup : x.id.step + 1 < S.current_step := by omega
    obtain ⟨hs, _⟩ := hS.chain.1.1 (x.id.step + 1) (by omega) hup
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    have hlink := hS.chain.1.2 x.id.step hx0 hup
    rw [hm, hsx] at hlink
    have p1 := through_of_chain R S sel hS hR x.id.step (x.id.step + 1) hx0 hx1 (by omega) hup
    have p2 := through_of_chain R S sel hS hR (x.id.step + 1) x.id.step (by omega) hup hx0 hx1
    have p3 := through_of_chain R S sel hS hR (x.id.step + 1) v.id.step (by omega) hup hv0 hv1
    rw [hsx] at p1 p2
    rw [hsv] at p3
    exact ⟨sel (x.id.step + 1), m, hm, hlink, p1, p2, p3⟩
  · rintro x v ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩ l hl0 hl1
    have p1 := through_of_chain R S sel hS hR x.id.step l hx0 hx1 hl0 hl1
    have p2 := through_of_chain R S sel hS hR v.id.step l hv0 hv1 hl0 hl1
    rw [hsx] at p1
    rw [hsv] at p2
    exact ⟨sel l, p1, p2, (hS.chain.1.1 l hl0 hl1).2⟩
  · rintro x v ⟨sel, hS, hR, hx0, hx1, hv0, hv1, hsx, hsv⟩
    have := through_of_chain R S sel hS hR v.id.step x.id.step hv0 hv1 hx0 hx1
    rw [hsx, hsv] at this; exact this
  · rintro x c d ⟨sel, hS, _, hx0, hx1, hc0, _, hsx, hsc⟩ _ hs hd
    have hlink := hS.chain.1.2 c.id.step hc0 (by omega)
    rw [hs, hsx, hd, hsc] at hlink
    exact hlink

/-- **The split by paths.** If every entry of the reviewed join lies on a path of one of the sides, the
two relations "on a path of this side" are the split. -/
theorem splitOk_of_paths (a b : GPathM) (hstep : a.current_step = b.current_step)
    (hbnd : ∀ x v, Rel (reviewAgg (join a b)) x v →
      0 ≤ x.id.step ∧ x.id.step < a.current_step ∧ 0 ≤ v.id.step ∧ v.id.step < a.current_step)
    (hcov : ∀ x v, Rel (reviewAgg (join a b)) x v →
      Exactness.Realizes a x v ∨ Exactness.Realizes b x v) : SupportSplit.SplitOk a b := by
  have gA := grown_join_left a b
  have gB := grown_join_right_of_step a b hstep
  refine ⟨_, _, _, _, fun x v hxv => ?_, sup_through (reviewAgg (join a b)) a,
    sup_through (reviewAgg (join a b)) b⟩
  obtain ⟨hx0, hx1, hv0, hv1⟩ := hbnd x v hxv
  rcases hcov x v hxv with ⟨sel, hsc, hsx, hsv⟩ | ⟨sel, hsc, hsx, hsv⟩
  · exact Or.inl ⟨sel, hsc, ChainSound_reviewAgg _ sel (ChainSound_of_grown gA sel hsc), hx0, hx1, hv0,
      hv1, hsx, hsv⟩
  · exact Or.inr ⟨sel, hsc, ChainSound_reviewAgg _ sel (ChainSound_of_grown gB sel hsc), hx0,
      by rw [← hstep]; exact hx1, hv0, by rw [← hstep]; exact hv1, hsx, hsv⟩

-- ============================================================
-- The verdict from the paths of the sides
-- ============================================================

section
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAggRun (MInv MInv_join)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.ReviewJoin (pinned)
open AbsSat.GraphPath.Model.SupportSplit (SupportSplit splitOk_of_partSplit frame_pinned nonneg_of_mapNodes sat_of_split)

variable (φ : Cnf)

/-- **At every union the machine reviews, each side realizes the entries it carries.** -/
def RunSurvivors : Prop :=
  ∀ (k : Int) (key : NodeId) (e h : GPathM), StateOkF φ k (key, e) → StateOkF φ k (key, h) →
    MInv φ e → MInv φ h → ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
    isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true →
      SurvivorsRealized (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) (pinned e ws rq) ∧
      SurvivorsRealized (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) (pinned h ws rq)

theorem pinned_step (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) :
    (pinned g ws rq).current_step = g.current_step :=
  (Pruned.trans (ConservationCore.pruned_filterWeakAll g ws)
    (pruned_foldl filterRequire pruned_filterRequire rq _)).step_eq

theorem pinned_node? (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) (p : PathNodeId) :
    (pinned g ws rq).node? p = g.node? p := by
  unfold GPathM.node?; rw [frame_pinned]

/-- **The split at every union, from the paths of the sides.** -/
theorem supportSplit_of_survivors (h : RunSurvivors φ) : SupportSplit φ := by
  intro k key e g hse hsg hme hmg ws rq hv
  obtain ⟨hA, hB⟩ := h k key e g hse hsg hme hmg ws rq hv
  have hok := okJoin_of_stateOkF φ k key e g hse hsg
  have hmJ := MInv_join φ e g hok hme hmg
  have hstep : (pinned e ws rq).current_step = (pinned g ws rq).current_step := by
    rw [pinned_step, pinned_step]; exact hse.step.trans hsg.step.symm
  have hpJ : pinned (join e g) ws rq = join (pinned e ws rq) (pinned g ws rq) := by
    show rq.foldl filterRequire (filterWeakAll (join e g) ws) = _
    rw [ReviewJoin.filterWeakAll_join, ReviewJoin.foldl_filterRequire_join]
  have hnd : NodupIds (join (pinned e ws rq) (pinned g ws rq)) := by
    rw [← hpJ]; unfold NodupIds; rw [frame_pinned]; exact hmJ.rctx.nodup
  have nd : ∀ c, MInv φ c → NodupIds (pinned c ws rq) := by
    intro c hc; unfold NodupIds; rw [frame_pinned]; exact hc.rctx.nodup
  have own : ∀ c, MInv φ c → ∀ n ∈ (pinned c ws rq).nodes, ∀ q ∈ n.owners,
      GownersNodes.HasNode (pinned c ws rq) q := by
    intro c hc n hn q hq
    rw [frame_pinned] at hn
    obtain ⟨m, hm, hid⟩ := hc.own n hn q hq
    exact ⟨m, by rw [frame_pinned]; exact hm, hid⟩
  have bnd : ∀ c, MInv φ c → ∀ p, Mem (pinned c ws rq) p →
      0 ≤ p.id.step ∧ p.id.step < (pinned c ws rq).current_step := by
    intro c hc p ⟨m, hm⟩
    rw [pinned_node?] at hm
    have hmem := List.mem_of_find?_eq_some hm
    have hid := node?_id_eq c p m hm
    have hon := hc.onMap m hmem
    rw [pinned_step]
    refine ⟨?_, ?_⟩
    · rw [← hid]; exact nonneg_of_mapNodes φ _ _ hon
    · rw [← hid]; exact hc.rctx.below m hmem
  exact splitOk_of_partSplit _ _ (partSplit_of_realized _ _ hstep hnd (nd e hme) (nd g hmg)
    (own e hme) (own g hmg) (bnd e hme) (bnd g hmg) hA hB)

/-- **The Improves verdict from the paths of the sides at every union.** -/
theorem sat_of_survivors (hwf : WF φ) (h : RunSurvivors φ)
    (hog : ReviewJoin.OwnGowPinned) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_split φ hwf (supportSplit_of_survivors φ h) hog kv hkv hv

/-- **At every union the machine reviews, every entry lies on a path of one of the pinned sides.** -/
def RunPaths : Prop :=
  ∀ (k : Int) (key : NodeId) (e h : GPathM), StateOkF φ k (key, e) → StateOkF φ k (key, h) →
    MInv φ e → MInv φ h → ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
    isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true →
      ∀ x v, Rel (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) x v →
        Exactness.Realizes (pinned e ws rq) x v ∨ Exactness.Realizes (pinned h ws rq) x v

theorem supportSplit_of_paths (h : RunPaths φ) : SupportSplit φ := by
  intro k key e g hse hsg hme hmg ws rq hv
  have hok := okJoin_of_stateOkF φ k key e g hse hsg
  have hmJ := MInv_join φ e g hok hme hmg
  have hstep : (pinned e ws rq).current_step = (pinned g ws rq).current_step := by
    rw [pinned_step, pinned_step]; exact hse.step.trans hsg.step.symm
  have hpJ : pinned (join e g) ws rq = join (pinned e ws rq) (pinned g ws rq) := by
    show rq.foldl filterRequire (filterWeakAll (join e g) ws) = _
    rw [ReviewJoin.filterWeakAll_join, ReviewJoin.foldl_filterRequire_join]
  have hnd : NodupIds (join (pinned e ws rq) (pinned g ws rq)) := by
    rw [← hpJ]; unfold NodupIds; rw [frame_pinned]; exact hmJ.rctx.nodup
  have bnd : ∀ c, MInv φ c → ∀ p, Mem (pinned c ws rq) p →
      0 ≤ p.id.step ∧ p.id.step < (pinned c ws rq).current_step := by
    intro c hc p ⟨m, hm⟩
    rw [pinned_node?] at hm
    have hmem := List.mem_of_find?_eq_some hm
    have hid := node?_id_eq c p m hm
    have hon := hc.onMap m hmem
    rw [pinned_step]
    refine ⟨?_, ?_⟩
    · rw [← hid]; exact nonneg_of_mapNodes φ _ _ hon
    · rw [← hid]; exact hc.rctx.below m hmem
  have hpr := pruned_reviewAgg (join (pinned e ws rq) (pinned g ws rq))
  have memB : ∀ p, Mem (reviewAgg (join (pinned e ws rq) (pinned g ws rq))) p →
      0 ≤ p.id.step ∧ p.id.step < (pinned e ws rq).current_step := by
    intro p hp
    rcases JoinSide.mem_side _ _ _ hpr hnd hp with ha | hb
    · exact bnd e hme p ha
    · rw [hstep]; exact bnd g hmg p hb
  refine splitOk_of_paths _ _ hstep (fun x v hxv => ?_) (h k key e g hse hsg hme hmg ws rq hv)
  obtain ⟨m, hm, _, hmv⟩ := hxv
  obtain ⟨hx0, hx1⟩ := memB x ⟨m, hm⟩
  obtain ⟨hv0, hv1⟩ := memB v hmv
  exact ⟨hx0, hx1, hv0, hv1⟩

/-- **The Improves verdict from paths at every union**: every entry of the reviewed union lies on a
path of one of the two pinned branches. -/
theorem sat_of_paths (hwf : WF φ) (h : RunPaths φ)
    (hog : ReviewJoin.OwnGowPinned) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_split φ hwf (supportSplit_of_paths φ h) hog kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PartSplitReal.sat_of_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_paths

/-- info: 'AbsSat.GraphPath.Model.PartSplitReal.sat_of_survivors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_survivors

end

/-- info: 'AbsSat.GraphPath.Model.PartSplitReal.partSplit_of_realized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms partSplit_of_realized

end AbsSat.GraphPath.Model.PartSplitReal
