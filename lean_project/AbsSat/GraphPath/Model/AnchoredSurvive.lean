-- lean_project/AbsSat/GraphPath/Model/AnchoredSurvive.lean
import AbsSat.GraphPath.Model.Survive
import AbsSat.GraphPath.Model.AggressiveReview

/-!
# Sets held up by a support relation survive the whole aggressive review

`Survive.Woven` (v44) proved that a set survives the review when **every member owns every member**.
That is too strong for a pin's slice: the slice has many Helly-3 gaps (v117), and the cascade after a
pin does drop owner entries inside it, although it never drops a member.

This module replaces "every member owns every member" by a **support relation** `R` between
members. `Sup g S R` asks:

* members are global owners, nodes, and sit below the current step;
* `R` relates members, and `R x v` means `v` is an owner of `x`;
* **coverage**: at every step, a member has an `R`-owner;
* **parents / sons**: an `R`-owner of a non-root member is an `R`-owner of some parent that is
  `R`-linked both ways to the member (the same for sons, through the parent table);
* **pairs**: two `R`-linked members on the swept steps have, at every step, a common `R`-owner.

`AOk` adds the two structural invariants the sweeps use (`Sons.SMP`, `Parents.NotRoot`). Proved:
every operation of the base review and of the author's sweep keeps `AOk` (the members, with their
`R`-owners and their `R`-links), so **`gowners_filterAllAgg_of_AOk`: after a compatible pin and the
whole aggressive review, every member is still a global owner.**

The relation is a witness, not the result: the cascade may drop any entry outside `R`.
-/

namespace AbsSat.GraphPath.Model.AnchoredSurvive

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview

abbrev fowA (b : List PathNodeId) : PNodeM → PNodeM :=
  fun n => { n with owners := intersectOwners n.owners b }

/-- **A set held up by a support relation.** -/
structure Sup (g : GPathM) (S : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop) : Prop where
  gow : ∀ p, S p → p ∈ g.gowners
  node : ∀ p, S p → (g.node? p).isSome = true
  step : ∀ p, S p → 0 ≤ p.id.step ∧ p.id.step < g.current_step
  dom : ∀ x v, R x v → S x ∧ S v
  own : ∀ x v n, R x v → g.node? x = some n → v ∈ n.owners
  cov : ∀ x, S x → ∀ l, 0 ≤ l → l < g.current_step → ∃ v, R x v ∧ v.id.step = l
  par : ∀ x d, S x → g.node? x = some d → x.parent_id ≠ none → ∀ v, R x v →
    ∃ c ∈ d.parents, R x c ∧ R c x ∧ R c v
  son : ∀ x, S x → x.id.step ≠ g.current_step - 1 → ∀ v, R x v →
    ∃ c m, g.node? c = some m ∧ x ∈ m.parents ∧ R x c ∧ R c x ∧ R c v
  agg : ∀ x v, R x v → 1 ≤ x.id.step → x.id.step ≤ g.current_step - 2 →
    1 ≤ v.id.step → v.id.step ≤ g.current_step - 2 →
    ∀ l, 0 ≤ l → l < g.current_step → ∃ z, R x z ∧ R v z ∧ z.id.step = l

/-- `Sup` plus the structural invariants the sweeps use. -/
structure AOk (g : GPathM) (S : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop) : Prop where
  sup : Sup g S R
  smp : Sons.SMP g
  nr : Parents.NotRoot g

variable {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

-- ============================================================
-- The owners intersection
-- ============================================================

theorem Sup_updateAt (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (hb : S id → ∀ v, R id v → v ∈ b) (h : Sup g S R) : Sup (updateAt g id (fowA b)) S R := by
  have hn : ∀ p n, g.node? p = some n →
      (updateAt g id (fowA b)).node? p = some (match n.id == id with | true => fowA b n | false => n) :=
    fun p n hn => updateAt_node? g id (fowA b) (fun _ => rfl) p n hn
  have hpar : ∀ n : PNodeM, (match n.id == id with | true => fowA b n | false => n).parents = n.parents := by
    intro n; cases n.id == id <;> rfl
  refine ⟨h.gow, ?_, h.step, h.dom, ?_, h.cov, ?_, ?_, h.agg⟩
  · intro p hp
    obtain ⟨n, hn'⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    rw [hn p n hn']; rfl
  · intro x v n' hr hn'
    obtain ⟨n, hn0⟩ := Option.isSome_iff_exists.mp (h.node x (h.dom x v hr).1)
    rw [hn x n hn0] at hn'
    rw [← Option.some.inj hn']
    cases hh : n.id == id with
    | true =>
      have hxid : id = x := by rw [← eq_of_beq hh]; exact node?_id_eq g x n hn0
      have hSid : S id := by rw [hxid]; exact (h.dom x v hr).1
      exact mem_intersectOwners_of_mem _ _ v (h.own x v n hr hn0) (hb hSid v (hxid ▸ hr))
    | false => exact h.own x v n hr hn0
  · intro x d' hS hd' hroot v hr
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (h.node x hS)
    rw [hn x d hd] at hd'
    rw [← Option.some.inj hd', hpar]
    exact h.par x d hS hd hroot v hr
  · intro x hS hlast v hr
    obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := h.son x hS hlast v hr
    exact ⟨c, _, hn c m hm, by rw [hpar]; exact hxm, h1, h2, h3⟩

-- ============================================================
-- The unlink
-- ============================================================

theorem Sup_unlink (g : GPathM) (id : PathNodeId) (h : Sup g S R) :
    Sup (unlinkIncompatible g id) S R := by
  cases hid : g.node? id with
  | none => simpa only [GPathM.unlinkIncompatible, hid] using h
  | some n₀ =>
    have hn : ∀ p m, g.node? p = some m →
        (unlinkIncompatible g id).node? p = some (unlinkMap n₀ id m) :=
      fun p m hm => unlinkIncompatible_node? g id n₀ hid p m hm
    have hcur := unlinkIncompatible_current g id
    -- a link between two `R`-linked members survives
    have hkeep : ∀ x c n m, g.node? x = some n → g.node? c = some m → c ∈ n.parents →
        R x c → R c x → c ∈ (unlinkMap n₀ id n).parents := by
      intro x c n m hn' hm hcn hxc hcx
      have hnid : n.id = x := node?_id_eq g x n hn'
      refine Survive.mem_parents_unlinkMap n₀ id n c hcn ?_ ?_
      · intro he
        have : n = n₀ := Option.some.inj ((show g.node? id = some n by rw [← he, hnid]; exact hn').symm.trans hid)
        rw [← this]; exact h.own x c n hxc hn'
      · intro he
        have : m = n₀ := Option.some.inj ((show g.node? id = some m by rw [← he]; exact hm).symm.trans hid)
        rw [← this, hnid]; exact h.own c x m hcx hm
    refine ⟨?_, ?_, ?_, h.dom, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [unlinkIncompatible_gowners]; exact h.gow p hp
    · intro p hp
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      rw [hn p m hm]; rfl
    · intro p hp; rw [hcur]; exact h.step p hp
    · intro x v n' hr hn'
      obtain ⟨n, hn0⟩ := Option.isSome_iff_exists.mp (h.node x (h.dom x v hr).1)
      rw [hn x n hn0] at hn'
      rw [← Option.some.inj hn', unlinkMap_owners]
      exact h.own x v n hr hn0
    · intro x hS l hlo hhi; rw [hcur] at hhi; exact h.cov x hS l hlo hhi
    · intro x d' hS hd' hroot v hr
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (h.node x hS)
      rw [hn x d hd] at hd'
      obtain ⟨c, hc, h1, h2, h3⟩ := h.par x d hS hd hroot v hr
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node c (h.dom x c h1).2)
      exact ⟨c, by rw [← Option.some.inj hd']; exact hkeep x c d m hd hm hc h1 h2, h1, h2, h3⟩
    · intro x hS hlast v hr
      rw [hcur] at hlast
      obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := h.son x hS hlast v hr
      obtain ⟨n, hn0⟩ := Option.isSome_iff_exists.mp (h.node x hS)
      exact ⟨c, _, hn c m hm, hkeep c x m n hm hn0 hxm h2 h1, h1, h2, h3⟩
    · intro x v hr hx1 hx2 hv1 hv2 l hlo hhi
      rw [hcur] at hx2 hv2 hhi
      exact h.agg x v hr hx1 hx2 hv1 hv2 l hlo hhi

-- ============================================================
-- Removing a non-member
-- ============================================================

theorem Sup_removeNode (g : GPathM) (id : PathNodeId) (h : Sup g S R) (hns : ¬ S id) :
    Sup (removeNode g id) S R := by
  have hne : ∀ p, S p → p ≠ id := fun p hp he => hns (he ▸ hp)
  have hn : ∀ p m, S p → g.node? p = some m → (removeNode g id).node? p = some (unlink id m) :=
    fun p m hp hm => removeNode_node? g id p m hm (hne p hp)
  refine ⟨?_, ?_, h.step, h.dom, ?_, h.cov, ?_, ?_, h.agg⟩
  · intro p hp
    rw [removeNode_gowners]
    exact List.mem_filter.mpr ⟨h.gow p hp, bne_iff_ne.mpr (hne p hp)⟩
  · intro p hp
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    rw [hn p m hp hm]; rfl
  · intro x v n' hr hn'
    have hS := (h.dom x v hr).1
    obtain ⟨n, hn0⟩ := Option.isSome_iff_exists.mp (h.node x hS)
    rw [hn x n hS hn0] at hn'
    rw [← Option.some.inj hn']
    exact h.own x v n hr hn0
  · intro x d' hS hd' hroot v hr
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (h.node x hS)
    rw [hn x d hS hd] at hd'
    obtain ⟨c, hc, h1, h2, h3⟩ := h.par x d hS hd hroot v hr
    refine ⟨c, ?_, h1, h2, h3⟩
    rw [← Option.some.inj hd']
    exact List.mem_filter.mpr ⟨hc, bne_iff_ne.mpr (hne c (h.dom x c h1).2)⟩
  · intro x hS hlast v hr
    obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := h.son x hS hlast v hr
    exact ⟨c, _, hn c m (h.dom x c h1).2 hm,
      List.mem_filter.mpr ⟨hxm, bne_iff_ne.mpr (hne x hS)⟩, h1, h2, h3⟩

-- ============================================================
-- A member passes the validity test
-- ============================================================

private theorem not_isEmpty_of_mem {α : Type} (l : List α) (a : α) (ha : a ∈ l) :
    (!l.isEmpty) = true := by
  cases l with
  | nil => exact absurd ha List.not_mem_nil
  | cons _ _ => rfl

/-- A member passes `isValidNode` after its owners are intersected with a list holding its
`R`-owners, and relinked. -/
theorem isValidNode_relink (g : GPathM) (h : Sup g S R) (hsmp : Sons.SMP g)
    (b : List PathNodeId) (id : PathNodeId) (hb : ∀ v, R id v → v ∈ b)
    (d₀ : PNodeM) (hd : g.node? id = some d₀) (hS : S id)
    (g₂ : GPathM) (hstep : g₂.current_step = g.current_step) :
    isValidNode g₂ (relink (intersectOwners d₀.owners b) d₀) = true := by
  have hdid : d₀.id = id := node?_id_eq g id d₀ hd
  have hid : (relink (intersectOwners d₀.owners b) d₀).id = id := by rw [← hdid]; rfl
  have hkeep : ∀ v, R id v → v ∈ intersectOwners d₀.owners b :=
    fun v hr => mem_intersectOwners_of_mem _ _ v (h.own id v d₀ hr hd) (hb v hr)
  obtain ⟨hs0, hs1⟩ := h.step id hS
  obtain ⟨v₀, hr₀, _⟩ := h.cov id hS 0 (Int.le_refl 0) (by omega)
  have hown : (intRange 0 (g₂.current_step - 1)).all
      (fun k => hasStepEntry (relink (intersectOwners d₀.owners b) d₀).owners k) = true := by
    refine List.all_eq_true.mpr ?_
    intro k hk
    obtain ⟨hlo, hhi⟩ := PickInduction.intRange_bounds hk
    obtain ⟨v, hr, hvs⟩ := h.cov id hS k hlo (by omega)
    exact List.any_eq_true.mpr ⟨v, hkeep v hr, beq_iff_eq.mpr hvs⟩
  have hpar : id.parent_id ≠ none →
      (!(relink (intersectOwners d₀.owners b) d₀).parents.isEmpty) = true := by
    intro hroot
    obtain ⟨c, hc, h1, _, _⟩ := h.par id d₀ hS hd hroot v₀ hr₀
    exact not_isEmpty_of_mem _ c (List.mem_filter.mpr ⟨hc, List.elem_eq_true_of_mem (hkeep c h1)⟩)
  have hsons : id.id.step ≠ g.current_step - 1 →
      (!(relink (intersectOwners d₀.owners b) d₀).sons.isEmpty) = true := by
    intro hlast
    obtain ⟨c, m, hm, hxm, h1, _, _⟩ := h.son id hS hlast v₀ hr₀
    have hmid : m.id = c := node?_id_eq g c m hm
    have hcs : c ∈ d₀.sons := by
      have := hsmp m (List.mem_of_find?_eq_some hm) id hxm d₀ (List.mem_of_find?_eq_some hd) hdid
      rw [hmid] at this; exact this
    exact not_isEmpty_of_mem _ c (List.mem_filter.mpr ⟨hcs, List.elem_eq_true_of_mem (hkeep c h1)⟩)
  simp only [isValidNode]
  split
  · split
    · exact hown
    · next hl =>
      refine (Bool.and_eq_true _ _).mpr ⟨hown, hsons ?_⟩
      intro he
      exact hl (by rw [hid, he, hstep]; exact beq_iff_eq.mpr rfl)
  · next hr =>
    have hroot : id.parent_id ≠ none := by
      intro hn; exact hr (by rw [hid, hn]; rfl)
    split
    · exact (Bool.and_eq_true _ _).mpr ⟨hown, hpar hroot⟩
    · next hl =>
      refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨hown, hpar hroot⟩, ?_⟩
      refine hsons ?_
      intro he
      exact hl (by rw [hid, he, hstep]; exact beq_iff_eq.mpr rfl)

/-- A member passes `isValidNode` as it stands. -/
theorem isValidNode_self (g : GPathM) (h : Sup g S R) (hsmp : Sons.SMP g)
    (id : PathNodeId) (d₀ : PNodeM) (hd : g.node? id = some d₀) (hS : S id) :
    isValidNode g d₀ = true := by
  have hdid : d₀.id = id := node?_id_eq g id d₀ hd
  obtain ⟨hs0, hs1⟩ := h.step id hS
  obtain ⟨v₀, hr₀, _⟩ := h.cov id hS 0 (Int.le_refl 0) (by omega)
  have hown : (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry d₀.owners k) = true := by
    refine List.all_eq_true.mpr ?_
    intro k hk
    obtain ⟨hlo, hhi⟩ := PickInduction.intRange_bounds hk
    obtain ⟨v, hr, hvs⟩ := h.cov id hS k hlo (by omega)
    exact List.any_eq_true.mpr ⟨v, h.own id v d₀ hr hd, beq_iff_eq.mpr hvs⟩
  have hpar : id.parent_id ≠ none → (!d₀.parents.isEmpty) = true := by
    intro hroot
    obtain ⟨c, hc, _, _, _⟩ := h.par id d₀ hS hd hroot v₀ hr₀
    exact not_isEmpty_of_mem _ c hc
  have hsons : id.id.step ≠ g.current_step - 1 → (!d₀.sons.isEmpty) = true := by
    intro hlast
    obtain ⟨c, m, hm, hxm, _, _, _⟩ := h.son id hS hlast v₀ hr₀
    have hmid : m.id = c := node?_id_eq g c m hm
    have hcs : c ∈ d₀.sons := by
      have := hsmp m (List.mem_of_find?_eq_some hm) id hxm d₀ (List.mem_of_find?_eq_some hd) hdid
      rw [hmid] at this; exact this
    exact not_isEmpty_of_mem _ c hcs
  have hroot_iff : d₀.id.parent_id.isNone = true → ¬ (id.parent_id ≠ none) := by
    intro hn hne; rw [hdid] at hn; exact hne (Option.isNone_iff_eq_none.mp hn)
  simp only [isValidNode]
  split
  · split
    · exact hown
    · next hl =>
      refine (Bool.and_eq_true _ _).mpr ⟨hown, hsons ?_⟩
      intro he
      exact hl (by rw [hdid, he]; exact beq_iff_eq.mpr rfl)
  · next hr =>
    have hroot : id.parent_id ≠ none := by
      intro hn; exact hr (by rw [hdid, hn]; rfl)
    split
    · exact (Bool.and_eq_true _ _).mpr ⟨hown, hpar hroot⟩
    · next hl =>
      refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨hown, hpar hroot⟩, hsons ?_⟩
      intro he
      exact hl (by rw [hdid, he]; exact beq_iff_eq.mpr rfl)

-- ============================================================
-- cleanInvalid
-- ============================================================

theorem AOk_cleanInvalidGo :
    ∀ (ids : List PathNodeId) (g : GPathM), AOk g S R → AOk (cleanInvalidGo g ids) S R := by
  intro ids
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGo]
    split
    · exact ih g h
    · next d₀ hd =>
      have hb : S id → ∀ v, R id v → v ∈ g.gowners := fun _ v hr => h.sup.gow v (h.sup.dom id v hr).2
      have hsmp₁ := Sons.SMP_updateAt g id (fowA g.gowners) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) h.smp
      have hsmp₂ := Sons.SMP_unlinkIncompatible _ id hsmp₁
      have h₁ := Sup_updateAt g id g.gowners hb h.sup
      have h₂ := Sup_unlink _ id h₁
      have hpr : Pruned g (unlinkIncompatible (updateAt g id (fowA g.gowners)) id) :=
        Pruned.trans (pruned_updateAt g id (fowA g.gowners) (fun _ => rfl)
          (fun _ _ hq => (List.mem_filter.mp hq).1) (fun _ _ hp => hp))
          (pruned_unlinkIncompatible _ id)
      have hnr₂ := Parents.NotRoot_of_pruned hpr h.nr
      have hstep₂ : (unlinkIncompatible (updateAt g id (fowA g.gowners)) id).current_step
          = g.current_step := by rw [unlinkIncompatible_current]; rfl
      split
      · exact ih _ ⟨h₂, hsmp₂, hnr₂⟩
      · next hbad =>
        have hns : ¬ S id := fun hSid =>
          hbad (isValidNode_relink g h.sup h.smp g.gowners id (fun v hr => hb hSid v hr) d₀ hd hSid _ hstep₂)
        exact ih _ ⟨Sup_removeNode _ id h₂ hns, Sons.SMP_removeNode _ id hsmp₂,
          Parents.NotRoot_of_pruned (pruned_removeNode _ id) hnr₂⟩

theorem AOk_cleanInvalid (g : GPathM) (h : AOk g S R) : AOk (cleanInvalid g) S R :=
  AOk_cleanInvalidGo _ g h

-- ============================================================
-- The coherence sweeps
-- ============================================================

theorem AOk_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (h : AOk g S R) (id : PathNodeId)
    (hsh : ∀ d, g.node? id = some d → S id → ∀ v, R id v → v ∈ unionOwnersOf g (nb d)) :
    AOk (reviewNode g nb id) S R := by
  have hsmp' := Sons.SMP_reviewNode nb id g h.smp
  have hnr' := Parents.NotRoot_of_pruned (pruned_reviewNode nb id g) h.nr
  refine ⟨?_, hsmp', hnr'⟩
  unfold reviewNode
  cases hd : g.node? id with
  | none => exact h.sup
  | some d =>
    simp only
    split
    · have hb : S id → ∀ v, R id v → v ∈ unionOwnersOf g (nb d) := fun hS => hsh d hd hS
      have h₁ := Sup_updateAt g id (unionOwnersOf g (nb d)) hb h.sup
      have h₂ := Sup_unlink _ id h₁
      have hstep₂ : (unlinkIncompatible (updateAt g id (fowA (unionOwnersOf g (nb d)))) id).current_step
          = g.current_step := by rw [unlinkIncompatible_current]; rfl
      split
      · exact h₂
      · next hbad =>
        refine Sup_removeNode _ id h₂ ?_
        intro hSid
        exact hbad (isValidNode_relink g h.sup h.smp _ id (fun v hr => hb hSid v hr) d hd hSid _ hstep₂)
    · next hbad =>
      refine Sup_removeNode g id h.sup ?_
      intro hSid
      exact hbad (isValidNode_self g h.sup h.smp id d hd hSid)

theorem share_parents (g : GPathM) (h : AOk g S R) (id : PathNodeId) (hz : 0 < id.id.step) :
    ∀ d, g.node? id = some d → S id → ∀ v, R id v → v ∈ unionOwnersOf g d.parents := by
  intro d hd hS v hr
  have hdid : d.id = id := node?_id_eq g id d hd
  have hroot : id.parent_id ≠ none := by
    have := h.nr d (List.mem_of_find?_eq_some hd) (by rw [hdid]; exact hz)
    rwa [hdid] at this
  obtain ⟨c, hc, h1, _, h3⟩ := h.sup.par id d hS hd hroot v hr
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.sup.node c (h.sup.dom id c h1).2)
  exact mem_unionOwnersOf g d.parents c m v hc hm (h.sup.own c v m h3 hm)

theorem share_sons (g : GPathM) (h : AOk g S R) (id : PathNodeId) (hl : id.id.step ≠ g.current_step - 1) :
    ∀ d, g.node? id = some d → S id → ∀ v, R id v → v ∈ unionOwnersOf g d.sons := by
  intro d hd hS v hr
  have hdid : d.id = id := node?_id_eq g id d hd
  obtain ⟨c, m, hm, hxm, _, _, h3⟩ := h.sup.son id hS hl v hr
  have hmid : m.id = c := node?_id_eq g c m hm
  have hcs : c ∈ d.sons := by
    have := h.smp m (List.mem_of_find?_eq_some hm) id hxm d (List.mem_of_find?_eq_some hd) hdid
    rw [hmid] at this; exact this
  exact mem_unionOwnersOf g d.sons c m v hcs hm (h.sup.own c v m h3 hm)

theorem AOk_reviewLine_parents (g : GPathM) (h : AOk g S R) (k : Int) (hk : 0 < k) :
    AOk (reviewLine g (·.parents) k) S R := by
  have main : ∀ (ids : List PathNodeId), (∀ id ∈ ids, 0 < id.id.step) →
      ∀ h' : GPathM, AOk h' S R →
        AOk (ids.foldl (fun h'' i => reviewNode h'' (·.parents) i) h') S R := by
    intro ids
    induction ids with
    | nil => intro _ h' hw; exact hw
    | cons x xs ih =>
      intro hx h' hw
      simp only [List.foldl_cons]
      exact ih (fun i hi => hx i (List.mem_cons_of_mem _ hi)) _
        (AOk_reviewNode h' _ hw x (share_parents h' hw x (hx x List.mem_cons_self)))
  exact main _ (fun id hid => by rw [Survive.step_of_mem_line g k id hid]; exact hk) g h

theorem AOk_reviewLine_sons (g : GPathM) (cs : Int) (hcs : g.current_step = cs) (h : AOk g S R)
    (k : Int) (hk : k ≠ cs - 1) :
    AOk (reviewLine g (·.sons) k) S R ∧ (reviewLine g (·.sons) k).current_step = cs := by
  have main : ∀ (ids : List PathNodeId), (∀ id ∈ ids, id.id.step ≠ cs - 1) →
      ∀ h' : GPathM, h'.current_step = cs → AOk h' S R →
        AOk (ids.foldl (fun h'' i => reviewNode h'' (·.sons) i) h') S R ∧
        (ids.foldl (fun h'' i => reviewNode h'' (·.sons) i) h').current_step = cs := by
    intro ids
    induction ids with
    | nil => intro _ h' hc hw; exact ⟨hw, hc⟩
    | cons x xs ih =>
      intro hx h' hc hw
      simp only [List.foldl_cons]
      refine ih (fun i hi => hx i (List.mem_cons_of_mem _ hi)) _ ?_
        (AOk_reviewNode h' _ hw x (share_sons h' hw x (by rw [hc]; exact hx x List.mem_cons_self)))
      rw [(pruned_reviewNode _ x h').step_eq]; exact hc
  exact main _ (fun id hid => by rw [Survive.step_of_mem_line g k id hid]; exact hk) g hcs h

theorem AOk_reviewSteps_parents :
    ∀ (ks : List Int), (∀ k ∈ ks, 0 < k) → ∀ g : GPathM, AOk g S R →
      AOk (reviewSteps g (·.parents) ks) S R := by
  intro ks
  induction ks with
  | nil => intro _ g h; exact h
  | cons k rest ih =>
    intro hk g h
    simp only [reviewSteps]
    split
    · exact ih (fun j hj => hk j (List.mem_cons_of_mem _ hj)) _
        (AOk_reviewLine_parents g h k (hk k List.mem_cons_self))
    · exact h

theorem AOk_reviewSteps_sons (cs : Int) :
    ∀ (ks : List Int), (∀ k ∈ ks, k ≠ cs - 1) → ∀ g : GPathM, g.current_step = cs → AOk g S R →
      AOk (reviewSteps g (·.sons) ks) S R ∧ (reviewSteps g (·.sons) ks).current_step = cs := by
  intro ks
  induction ks with
  | nil => intro _ g hc h; exact ⟨h, hc⟩
  | cons k rest ih =>
    intro hk g hc h
    simp only [reviewSteps]
    split
    · obtain ⟨hw', hc'⟩ := AOk_reviewLine_sons g cs hc h k (hk k List.mem_cons_self)
      exact ih (fun j hj => hk j (List.mem_cons_of_mem _ hj)) _ hc' hw'
    · exact ⟨h, hc⟩

theorem AOk_reviewParents (g : GPathM) (h : AOk g S R) : AOk (reviewParents g) S R :=
  AOk_reviewSteps_parents _ (fun _ hk => (PickInduction.intRange_bounds hk).1) g h

theorem AOk_reviewSons (g : GPathM) (h : AOk g S R) : AOk (reviewSons g) S R :=
  (AOk_reviewSteps_sons g.current_step _
    (fun k hk => by
      have := (PickInduction.intRange_bounds (List.mem_reverse.mp hk)).2
      omega)
    g rfl h).1

theorem AOk_reviewPass (g : GPathM) (h : AOk g S R) : AOk (reviewPass g) S R :=
  AOk_reviewSons _ (AOk_reviewParents _ (AOk_cleanInvalid g h))

theorem AOk_reviewFuel : ∀ (fuel : Nat) (g : GPathM), AOk g S R → AOk (reviewFuel fuel g) S R := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewFuel]
    split
    · split
      · exact ih _ (AOk_reviewPass g h)
      · exact AOk_reviewPass g h
    · exact h

theorem AOk_review (g : GPathM) (h : AOk g S R) : AOk (review g) S R := AOk_reviewFuel _ g h

theorem AOk_filterRequire (g : GPathM) (h : AOk g S R) (req : NodeId)
    (hpin : ∀ p, S p → p.id.step = req.step → p.id = req) : AOk (filterRequire g req) S R := by
  refine ⟨⟨?_, h.sup.node, h.sup.step, h.sup.dom, h.sup.own, h.sup.cov, h.sup.par, h.sup.son, h.sup.agg⟩,
    Sons.SMP_filterRequire g req h.smp, Parents.NotRoot_of_pruned (pruned_filterRequire g req) h.nr⟩
  intro p hp
  refine List.mem_filter.mpr ⟨h.sup.gow p hp, ?_⟩
  cases hs : (p.id.step != req.step) with
  | true => rfl
  | false =>
    have heq : p.id.step = req.step := by
      cases hb : (p.id.step == req.step) with
      | true => exact eq_of_beq hb
      | false => simp only [bne, hb, Bool.not_false] at hs; exact Bool.noConfusion hs
    rw [hpin p hp heq]
    simp only [beq_self_eq_true, Bool.or_true]

-- ============================================================
-- The author's sweep
-- ============================================================

/-- Two `R`-linked members on the swept steps always pass the author's test. -/
theorem shares_of_R (g : GPathM) (h : Sup g S R) (x w : PathNodeId) (nx nw : PNodeM)
    (hx : g.node? x = some nx) (hw : g.node? w = some nw)
    (hx1 : 1 ≤ x.id.step) (hx2 : x.id.step ≤ g.current_step - 2)
    (hw1 : 1 ≤ w.id.step) (hw2 : w.id.step ≤ g.current_step - 2)
    (hr : R x w ∨ R w x) : sharesEveryStep g.current_step nx.owners nw.owners = true := by
  unfold sharesEveryStep
  refine List.all_eq_true.mpr (fun k hk => ?_)
  obtain ⟨hlo, hhi⟩ := PickInduction.intRange_bounds hk
  obtain ⟨z, hz1, hz2, hzs⟩ : ∃ z, R x z ∧ R w z ∧ z.id.step = k := by
    rcases hr with hr | hr
    · exact h.agg x w hr hx1 hx2 hw1 hw2 k hlo (by omega)
    · obtain ⟨z, a, b, c⟩ := h.agg w x hr hw1 hw2 hx1 hx2 k hlo (by omega)
      exact ⟨z, b, a, c⟩
  have hany : (ownersAt nx.owners k).any (fun r => nw.owners.contains r) = true :=
    List.any_eq_true.mpr ⟨z, List.mem_filter.mpr ⟨h.own x z nx hz1 hx, beq_iff_eq.mpr hzs⟩,
      List.elem_eq_true_of_mem (h.own w z nw hz2 hw)⟩
  rw [hany, Bool.or_true]

theorem Sup_aggPair (g : GPathM) (h : Sup g S R) (x w : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hx2 : x.id.step ≤ g.current_step - 2)
    (hw1 : 1 ≤ w.id.step) (hw2 : w.id.step ≤ g.current_step - 2) :
    Sup (aggPair g x w) S R := by
  unfold aggPair
  split
  · next nx nw hx hw =>
    split
    · next hcond =>
      have hsh : sharesEveryStep g.current_step nx.owners nw.owners = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        exact hcond.2
      have hnxw : ¬ R x w := fun hr => by
        rw [shares_of_R g h x w nx nw hx hw hx1 hx2 hw1 hw2 (Or.inl hr)] at hsh
        exact Bool.noConfusion hsh
      have hnwx : ¬ R w x := fun hr => by
        rw [shares_of_R g h x w nx nw hx hw hx1 hx2 hw1 hw2 (Or.inr hr)] at hsh
        exact Bool.noConfusion hsh
      have hb1 : S x → ∀ v, R x v → v ∈ dropList nx.owners w := fun _ v hr =>
        mem_dropList _ w v (h.own x v nx hr hx) (fun he => hnxw (he ▸ hr))
      have hb2 : S w → ∀ v, R w v → v ∈ dropList nw.owners x := fun _ v hr =>
        mem_dropList _ x v (h.own w v nw hr hw) (fun he => hnwx (he ▸ hr))
      exact Sup_updateAt _ w _ hb2 (Sup_updateAt g x _ hb1 h)
    · exact h
  · exact h

theorem SMP_aggPair (g : GPathM) (hs : Sons.SMP g) (x w : PathNodeId) : Sons.SMP (aggPair g x w) := by
  unfold aggPair
  split
  · split
    · exact Sons.SMP_updateAt _ w _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (Sons.SMP_updateAt g x _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hs)
    · exact hs
  · exact hs

theorem AOk_aggPair (g : GPathM) (h : AOk g S R) (x w : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hx2 : x.id.step ≤ g.current_step - 2)
    (hw1 : 1 ≤ w.id.step) (hw2 : w.id.step ≤ g.current_step - 2) :
    AOk (aggPair g x w) S R :=
  ⟨Sup_aggPair g h.sup x w hx1 hx2 hw1 hw2, SMP_aggPair g h.smp x w,
    Parents.NotRoot_of_pruned (pruned_aggPair g x w) h.nr⟩

theorem AOk_pairs (x : PathNodeId) (cs : Int) (hx1 : 1 ≤ x.id.step) (hx2 : x.id.step ≤ cs - 2) :
    ∀ (ws : List PathNodeId), (∀ w ∈ ws, 1 ≤ w.id.step ∧ w.id.step ≤ cs - 2) →
      ∀ g : GPathM, g.current_step = cs → AOk g S R →
        AOk (ws.foldl (fun g w => aggPair g x w) g) S R ∧
        (ws.foldl (fun g w => aggPair g x w) g).current_step = cs := by
  intro ws
  induction ws with
  | nil => intro _ g hc h; exact ⟨h, hc⟩
  | cons w rest ih =>
    intro hws g hc h
    simp only [List.foldl_cons]
    obtain ⟨hw1, hw2⟩ := hws w List.mem_cons_self
    refine ih (fun v hv => hws v (List.mem_cons_of_mem _ hv)) _ ?_
      (AOk_aggPair g h x w hx1 (by rw [hc]; exact hx2) hw1 (by rw [hc]; exact hw2))
    rw [(pruned_aggPair g x w).step_eq]; exact hc

theorem AOk_pairSteps (x : PathNodeId) (cs : Int) (hx1 : 1 ≤ x.id.step) (hx2 : x.id.step ≤ cs - 2) :
    ∀ (ks : List Int), (∀ k ∈ ks, 1 ≤ k ∧ k ≤ cs - 2) →
      ∀ g : GPathM, g.current_step = cs → AOk g S R →
        AOk (ks.foldl (fun g kw => (ownersAtNow g x kw).foldl (fun g w => aggPair g x w) g) g) S R ∧
        (ks.foldl (fun g kw => (ownersAtNow g x kw).foldl (fun g w => aggPair g x w) g) g).current_step
          = cs := by
  intro ks
  induction ks with
  | nil => intro _ g hc h; exact ⟨h, hc⟩
  | cons k rest ih =>
    intro hks g hc h
    simp only [List.foldl_cons]
    obtain ⟨hk1, hk2⟩ := hks k List.mem_cons_self
    have hws : ∀ w ∈ ownersAtNow g x k, 1 ≤ w.id.step ∧ w.id.step ≤ cs - 2 := by
      intro w hw
      have hs : w.id.step = k := eq_of_beq (List.mem_filter.mp hw).2
      rw [hs]; exact ⟨hk1, hk2⟩
    obtain ⟨h', hc'⟩ := AOk_pairs x cs hx1 hx2 _ hws g hc h
    exact ih (fun j hj => hks j (List.mem_cons_of_mem _ hj)) _ hc' h'

theorem AOk_aggNode (g : GPathM) (h : AOk g S R) (x : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hx2 : x.id.step ≤ g.current_step - 2) : AOk (aggNode g x) S R := by
  have hfin : ∀ g₁ : GPathM, AOk g₁ S R → AOk
      (match g₁.node? x with
        | none => g₁
        | some n₁ => if isValidNode g₁ n₁ then g₁ else removeNode g₁ x) S R := by
    intro g₁ h₁
    split
    · exact h₁
    · next n₁ hn₁ =>
      split
      · exact h₁
      · next hbad =>
        have hns : ¬ S x := fun hS => hbad (isValidNode_self g₁ h₁.sup h₁.smp x n₁ hn₁ hS)
        exact ⟨Sup_removeNode g₁ x h₁.sup hns, Sons.SMP_removeNode g₁ x h₁.smp,
          Parents.NotRoot_of_pruned (pruned_removeNode g₁ x) h₁.nr⟩
  unfold aggNode
  split
  · exact h
  · apply hfin
    split
    · exact (AOk_pairSteps x g.current_step hx1 hx2 _
        (fun k hk => PickInduction.intRange_bounds (List.mem_reverse.mp hk)) g rfl h).1
    · exact h

theorem AOk_aggSweep (g : GPathM) (h : AOk g S R) : AOk (aggSweep g) S R := by
  unfold aggSweep
  split
  · have hline : ∀ (k : Int), 1 ≤ k → ∀ cs, k ≤ cs - 2 → ∀ (ids : List PathNodeId),
        (∀ id ∈ ids, id.id.step = k) → ∀ g' : GPathM, g'.current_step = cs → AOk g' S R →
          AOk (ids.foldl aggNode g') S R ∧ (ids.foldl aggNode g').current_step = cs := by
      intro k hk1 cs hk2 ids
      induction ids with
      | nil => intro _ g' hc h'; exact ⟨h', hc⟩
      | cons i rest ih =>
        intro hids g' hc h'
        simp only [List.foldl_cons]
        have hi := hids i List.mem_cons_self
        refine ih (fun j hj => hids j (List.mem_cons_of_mem _ hj)) _ ?_
          (AOk_aggNode g' h' i (by rw [hi]; exact hk1) (by rw [hi, hc]; exact hk2))
        rw [(pruned_aggNode g' i).step_eq]; exact hc
    have hsteps : ∀ (ks : List Int), (∀ k ∈ ks, 1 ≤ k ∧ k ≤ g.current_step - 2) →
        ∀ g' : GPathM, g'.current_step = g.current_step → AOk g' S R →
          AOk (ks.foldl (fun g k => ((g.line k).map (·.id)).foldl aggNode g) g') S R ∧
          (ks.foldl (fun g k => ((g.line k).map (·.id)).foldl aggNode g) g').current_step
            = g.current_step := by
      intro ks
      induction ks with
      | nil => intro _ g' hc h'; exact ⟨h', hc⟩
      | cons k rest ih =>
        intro hks g' hc h'
        simp only [List.foldl_cons]
        obtain ⟨hk1, hk2⟩ := hks k List.mem_cons_self
        obtain ⟨h'', hc''⟩ := hline k hk1 g.current_step hk2 _
          (fun id hid => Survive.step_of_mem_line g' k id hid) g' hc h'
        exact ih (fun j hj => hks j (List.mem_cons_of_mem _ hj)) _ hc'' h''
    exact (hsteps _ (fun k hk => PickInduction.intRange_bounds (List.mem_reverse.mp hk)) g rfl h).1
  · exact h

theorem AOk_reviewAggFuel : ∀ (fuel : Nat) (g : GPathM), AOk g S R → AOk (reviewAggFuel fuel g) S R := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact AOk_review g h
  | succ n ih =>
    intro g h
    simp only [reviewAggFuel]
    have h₁ := AOk_review g h
    split
    · split
      · exact ih _ (AOk_aggSweep _ h₁)
      · exact h₁
    · exact h₁

theorem AOk_filterAllAgg (g : GPathM) (h : AOk g S R) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r) :
    AOk (filterAllAgg g reqs) S R := by
  unfold filterAllAgg reviewAgg
  refine AOk_reviewAggFuel _ _ ?_
  have main : ∀ (l : List NodeId), (∀ r ∈ l, ∀ p, S p → p.id.step = r.step → p.id = r) →
      ∀ h' : GPathM, AOk h' S R → AOk (l.foldl filterRequire h') S R := by
    intro l
    induction l with
    | nil => intro _ h' hw; exact hw
    | cons x xs ih =>
      intro hx h' hw
      simp only [List.foldl_cons]
      exact ih (fun r hr => hx r (List.mem_cons_of_mem _ hr)) _
        (AOk_filterRequire h' hw x (hx x List.mem_cons_self))
  exact main reqs hpin g h

/-- **Every member survives a compatible pin and the whole aggressive review.** -/
theorem gowners_filterAllAgg_of_AOk (g : GPathM) (h : AOk g S R) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r) :
    ∀ p, S p → p ∈ (filterAllAgg g reqs).gowners :=
  (AOk_filterAllAgg g h reqs hpin).sup.gow

/-- With no members, `AOk` is just the two structural invariants. -/
theorem AOk_empty (g : GPathM) (hs : Sons.SMP g) (hn : Parents.NotRoot g) :
    AOk g (fun _ => False) (fun _ _ => False) :=
  ⟨⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ _ h => h.elim,
    fun _ _ _ h => h.elim, fun _ h => h.elim, fun _ _ h => h.elim, fun _ h => h.elim,
    fun _ _ h => h.elim⟩, hs, hn⟩

/-- The aggressive review keeps `SMP` (the empty set's `AOk`). -/
theorem SMP_filterAllAgg (g : GPathM) (hs : Sons.SMP g) (hn : Parents.NotRoot g) (reqs : List NodeId) :
    Sons.SMP (filterAllAgg g reqs) :=
  (AOk_filterAllAgg g (AOk_empty g hs hn) reqs (fun _ _ _ h => h.elim)).smp

theorem NotRoot_filterAllAgg (g : GPathM) (hs : Sons.SMP g) (hn : Parents.NotRoot g) (reqs : List NodeId) :
    Parents.NotRoot (filterAllAgg g reqs) :=
  (AOk_filterAllAgg g (AOk_empty g hs hn) reqs (fun _ _ _ h => h.elim)).nr

/-- info: 'AbsSat.GraphPath.Model.AnchoredSurvive.gowners_filterAllAgg_of_AOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gowners_filterAllAgg_of_AOk

end AbsSat.GraphPath.Model.AnchoredSurvive
