-- lean_project/AbsSat/GraphPath/Model/Survive.lean
import AbsSat.GraphPath.Model.Threaded

/-!
**What survives `cleanInvalid`.**

v41 measured where `PickValid`'s risk lives: over 39,984 allowed picks,
`cleanInvalid` — the sweep that does the pinning work — never leaves the graph
invalid, and the two coherence sweeps remove extra nodes in only 67. So the
question is what `cleanInvalid` cannot destroy.

The answer is **not** "a threaded path". Working the argument through shows
why. `cleanInvalid` re-intersects every node's owners with the *current*
global owners, and those shrink as the sweep removes nodes. So for a node to
keep passing `isValidNode` it needs, at every step, an owner that **itself
survives**. Iterating that, the witness must be a set closed under its own
support — and if you insist the witness is a path, one node per step, "closed
under its own support" is exactly `PairwiseOwned`. There is no cheaper path.

But the witness does not have to be a path. `isValid` asks for a *global
owner* at every step, not a chain. So the right object is a **self-supporting
set**, and that is what this module is about:

    Closed g S : every member is a global owner and a node; every member has,
                 at every step, an owner inside S; every non-root member has a
                 parent inside S and every non-last one a son inside S; and
                 linked members own each other.

`Closed_cleanInvalidGo` proves the sweep **cannot remove a member of such a
set**, and `isValid_cleanInvalid_of_Closed` turns that into validity whenever
`S` reaches every step.

The two clauses that are not free are `support` — an owner *inside S* at every
step — and the `coown` half about linked pairs. The second is a theorem at a
review fixpoint (`Sons.SMP` turns a parent link round, and v39's bridge makes
both ends owners); the first is the residue, and it is the same residue as
ever: it says the pruning has a non-empty arc-consistent core. That is what
`PickValid` is, said without reference to chains.
-/

namespace AbsSat.GraphPath.Model.Survive

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- A **self-supporting** set of path nodes: it holds itself up against every
narrowing `cleanInvalid` performs. -/
structure Closed (g : GPathM) (S : PathNodeId → Prop) : Prop where
  /-- Members are global owners, so they are what `isValid` counts. -/
  gow : ∀ p, S p → p ∈ g.gowners
  /-- Members are real nodes. -/
  node : ∀ p, S p → (g.node? p).isSome = true
  /-- **The residue.** At every step, a member owns a member. -/
  support : ∀ p n, g.node? p = some n → S p → ∀ l, 0 ≤ l → l < g.current_step →
    ∃ v ∈ n.owners, S v ∧ v.id.step = l
  /-- A non-root member has a member among its parents. -/
  parent : ∀ p n, g.node? p = some n → S p → p.parent_id ≠ none →
    ∃ c ∈ n.parents, S c
  /-- A non-last member is the parent of a member. Phrased through the *parent*
  table on purpose: `Sons.SMP` turns it into a son link, and the reverse mirror
  (which does not exist) is never needed. -/
  son : ∀ p, S p → p.id.step ≠ g.current_step - 1 →
    ∃ c m, S c ∧ g.node? c = some m ∧ p ∈ m.parents
  /-- Linked members own each other — free at a review fixpoint from `SMP`
  plus v39's bridge. -/
  coown : ∀ p c n m, S p → S c → g.node? p = some n → g.node? c = some m →
    c ∈ n.parents → c ∈ n.owners ∧ p ∈ m.owners

-- ============================================================
-- The owners intersection
-- ============================================================

private abbrev fow (b : List PathNodeId) : PNodeM → PNodeM :=
  fun n => { n with owners := intersectOwners n.owners b }

theorem Closed_updateAt (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (h : Closed g S) : Closed (updateAt g id (fow g.gowners)) S where
  gow := h.gow
  node := by
    intro p hp
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    rw [updateAt_node? g id (fow g.gowners) (fun _ => rfl) p n hn]
    rfl
  support := by
    intro p n' hn' hp l hlo hhi
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    rw [updateAt_node? g id (fow g.gowners) (fun _ => rfl) p n hn] at hn'
    obtain ⟨v, hv, hSv, hvs⟩ := h.support p n hn hp l hlo hhi
    refine ⟨v, ?_, hSv, hvs⟩
    have := Option.some.inj hn'
    rw [← this]
    cases n.id == id with
    | true => exact mem_intersectOwners_of_mem _ _ v hv (h.gow v hSv)
    | false => exact hv
  parent := by
    intro p n' hn' hp hroot
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    rw [updateAt_node? g id (fow g.gowners) (fun _ => rfl) p n hn] at hn'
    obtain ⟨c, hc, hSc⟩ := h.parent p n hn hp hroot
    refine ⟨c, ?_, hSc⟩
    have := Option.some.inj hn'
    rw [← this]
    cases n.id == id with | true => exact hc | false => exact hc
  son := by
    intro p hp hlast
    obtain ⟨c, m, hSc, hm, hpm⟩ := h.son p hp hlast
    refine ⟨c, _, hSc, updateAt_node? g id (fow g.gowners) (fun _ => rfl) c m hm, ?_⟩
    cases m.id == id with | true => exact hpm | false => exact hpm
  coown := by
    intro p c n' m' hSp hSc hn' hm' hcp
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hSp)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node c hSc)
    rw [updateAt_node? g id (fow g.gowners) (fun _ => rfl) p n hn] at hn'
    rw [updateAt_node? g id (fow g.gowners) (fun _ => rfl) c m hm] at hm'
    have hne : n' = (match n.id == id with | true => fow g.gowners n | false => n) :=
      (Option.some.inj hn').symm
    have hme : m' = (match m.id == id with | true => fow g.gowners m | false => m) :=
      (Option.some.inj hm').symm
    have hpar_eq : (match n.id == id with
        | true => fow g.gowners n | false => n).parents = n.parents := by
      cases n.id == id <;> rfl
    have hcp' : c ∈ n.parents := by rw [hne, hpar_eq] at hcp; exact hcp
    obtain ⟨h1, h2⟩ := h.coown p c n m hSp hSc hn hm hcp'
    constructor
    · rw [hne]
      cases n.id == id with
      | true => exact mem_intersectOwners_of_mem _ _ c h1 (h.gow c hSc)
      | false => exact h1
    · rw [hme]
      cases m.id == id with
      | true => exact mem_intersectOwners_of_mem _ _ p h2 (h.gow p hSp)
      | false => exact h2


-- ============================================================
-- The unlink
-- ============================================================

theorem unlinkMap_parents_sub (n : PNodeM) (id : PathNodeId) (m : PNodeM) :
    ∀ p ∈ (unlinkMap n id m).parents, p ∈ m.parents := by
  unfold GPathM.unlinkMap
  split
  · intro p hp; exact (List.mem_filter.mp hp).1
  · split
    · intro p hp; exact hp
    · intro p hp; exact (List.mem_filter.mp hp).1

/-- A parent link survives the unlink when the two conditions the unlink can
trip are met: if the node *is* the target, the target's owners keep the link;
if the link *is* the target, the target owns the node. -/
theorem mem_parents_unlinkMap (n₀ : PNodeM) (id : PathNodeId) (m : PNodeM)
    (c : PathNodeId) (hc : c ∈ m.parents)
    (h1 : m.id = id → c ∈ n₀.owners)
    (h2 : c = id → m.id ∈ n₀.owners) :
    c ∈ (unlinkMap n₀ id m).parents := by
  unfold GPathM.unlinkMap
  split
  · next hb =>
    exact List.mem_filter.mpr ⟨hc, List.elem_eq_true_of_mem (h1 (eq_of_beq hb))⟩
  · split
    · exact hc
    · next hb2 =>
      refine List.mem_filter.mpr ⟨hc, ?_⟩
      simp only [bne_iff_ne]
      intro heq
      exact hb2 (List.elem_eq_true_of_mem (h2 heq))

theorem Closed_unlink (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (h : Closed g S) : Closed (unlinkIncompatible g id) S := by
  cases hid : g.node? id with
  | none => simpa only [GPathM.unlinkIncompatible, hid] using h
  | some n₀ =>
    have hnode : ∀ p, S p → ∃ m, g.node? p = some m ∧
        (unlinkIncompatible g id).node? p = some (unlinkMap n₀ id m) := by
      intro p hp
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      exact ⟨m, hm, unlinkIncompatible_node? g id n₀ hid p m hm⟩
    -- the two side conditions, discharged from `coown`
    have hside : ∀ p c n m, S p → S c → g.node? p = some n → g.node? c = some m →
        c ∈ n.parents → (n.id = id → c ∈ n₀.owners) ∧ (c = id → n.id ∈ n₀.owners) := by
      intro p c n m hSp hSc hn hm hcp
      obtain ⟨h1, h2⟩ := h.coown p c n m hSp hSc hn hm hcp
      have hnid : n.id = p := node?_id_eq g p n hn
      have hmid : m.id = c := node?_id_eq g c m hm
      constructor
      · intro he
        have : n = n₀ := by
          have : g.node? id = some n := by rw [← he, hnid]; exact hn
          exact Option.some.inj (this.symm.trans hid)
        rw [← this]; exact h1
      · intro he
        have : m = n₀ := by
          have : g.node? id = some m := by rw [← he]; exact hm
          exact Option.some.inj (this.symm.trans hid)
        rw [← this, hnid]; exact h2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [unlinkIncompatible_gowners]; exact h.gow p hp
    · intro p hp
      obtain ⟨m, _, hm'⟩ := hnode p hp
      rw [hm']; rfl
    · intro p n' hn' hp l hlo hhi
      obtain ⟨n, hn, hn2⟩ := hnode p hp
      have := Option.some.inj (hn'.symm.trans hn2)
      obtain ⟨v, hv, hSv, hvs⟩ := h.support p n hn hp l hlo
        (by rw [unlinkIncompatible_current] at hhi; exact hhi)
      exact ⟨v, by rw [this, unlinkMap_owners]; exact hv, hSv, hvs⟩
    · intro p n' hn' hp hroot
      obtain ⟨n, hn, hn2⟩ := hnode p hp
      have heq := Option.some.inj (hn'.symm.trans hn2)
      obtain ⟨c, hc, hSc⟩ := h.parent p n hn hp hroot
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node c hSc)
      obtain ⟨s1, s2⟩ := hside p c n m hp hSc hn hm hc
      exact ⟨c, by rw [heq]; exact mem_parents_unlinkMap n₀ id n c hc s1 s2, hSc⟩
    · intro p hp hlast
      obtain ⟨c, m, hSc, hm, hpm⟩ := h.son p hp
        (by rw [unlinkIncompatible_current] at hlast; exact hlast)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      obtain ⟨s1, s2⟩ := hside c p m n hSc hp hm hn hpm
      exact ⟨c, unlinkMap n₀ id m, hSc, unlinkIncompatible_node? g id n₀ hid c m hm,
        mem_parents_unlinkMap n₀ id m p hpm s1 s2⟩
    · intro p c n' m' hSp hSc hn' hm' hcp
      obtain ⟨n, hn, hn2⟩ := hnode p hSp
      obtain ⟨m, hm, hm2⟩ := hnode c hSc
      have hne := Option.some.inj (hn'.symm.trans hn2)
      have hme := Option.some.inj (hm'.symm.trans hm2)
      have hcp' : c ∈ n.parents := by
        rw [hne] at hcp; exact unlinkMap_parents_sub n₀ id n c hcp
      obtain ⟨h1, h2⟩ := h.coown p c n m hSp hSc hn hm hcp'
      exact ⟨by rw [hne, unlinkMap_owners]; exact h1,
             by rw [hme, unlinkMap_owners]; exact h2⟩

-- ============================================================
-- Removing a non-member
-- ============================================================

theorem Closed_removeNode (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (h : Closed g S) (hns : ¬ S id) : Closed (removeNode g id) S := by
  have hne : ∀ p, S p → p ≠ id := fun p hp he => hns (he ▸ hp)
  have hnode : ∀ p, S p → ∃ m, g.node? p = some m ∧
      (removeNode g id).node? p = some (unlink id m) := by
    intro p hp
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    exact ⟨m, hm, removeNode_node? g id p m hm (hne p hp)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [removeNode_gowners]
    exact List.mem_filter.mpr ⟨h.gow p hp, bne_iff_ne.mpr (hne p hp)⟩
  · intro p hp; obtain ⟨m, _, hm'⟩ := hnode p hp; rw [hm']; rfl
  · intro p n' hn' hp l hlo hhi
    obtain ⟨n, hn, hn2⟩ := hnode p hp
    have heq := Option.some.inj (hn'.symm.trans hn2)
    obtain ⟨v, hv, hSv, hvs⟩ := h.support p n hn hp l hlo hhi
    exact ⟨v, by rw [heq]; exact hv, hSv, hvs⟩
  · intro p n' hn' hp hroot
    obtain ⟨n, hn, hn2⟩ := hnode p hp
    have heq := Option.some.inj (hn'.symm.trans hn2)
    obtain ⟨c, hc, hSc⟩ := h.parent p n hn hp hroot
    refine ⟨c, ?_, hSc⟩
    rw [heq]
    exact List.mem_filter.mpr ⟨hc, bne_iff_ne.mpr (hne c hSc)⟩
  · intro p hp hlast
    obtain ⟨c, m, hSc, hm, hpm⟩ := h.son p hp hlast
    refine ⟨c, unlink id m, hSc, removeNode_node? g id c m hm (hne c hSc), ?_⟩
    exact List.mem_filter.mpr ⟨hpm, bne_iff_ne.mpr (hne p hp)⟩
  · intro p c n' m' hSp hSc hn' hm' hcp
    obtain ⟨n, hn, hn2⟩ := hnode p hSp
    obtain ⟨m, hm, hm2⟩ := hnode c hSc
    have hne1 := Option.some.inj (hn'.symm.trans hn2)
    have hme := Option.some.inj (hm'.symm.trans hm2)
    have hcp' : c ∈ n.parents := by
      rw [hne1] at hcp; exact (List.mem_filter.mp hcp).1
    obtain ⟨h1, h2⟩ := h.coown p c n m hSp hSc hn hm hcp'
    exact ⟨by rw [hne1]; exact h1, by rw [hme]; exact h2⟩


-- ============================================================
-- A member always passes the validity test
-- ============================================================

private theorem not_isEmpty_of_ne_nil {α : Type} (l : List α) (hl : l ≠ []) :
    (!l.isEmpty) = true := by
  cases l with
  | nil => exact absurd rfl hl
  | cons _ _ => rfl

/-- **The heart.** A member of a self-supporting set passes `isValidNode` after
the global intersection, so the sweep cannot drop it. Every clause of
`isValidNode` is answered by a clause of `Closed`: the support table by
`support`, the parents by `parent`, the sons by `son` turned round with
`Sons.SMP`. -/
theorem isValidNode_of_Closed (g : GPathM) (S : PathNodeId → Prop) (h : Closed g S)
    (hsmp : Sons.SMP g) (id : PathNodeId) (d₀ : PNodeM) (hd : g.node? id = some d₀)
    (hS : S id) (g₂ : GPathM) (hstep : g₂.current_step = g.current_step) :
    isValidNode g₂ (relink (intersectOwners d₀.owners g.gowners) d₀) = true := by
  have hdid : d₀.id = id := node?_id_eq g id d₀ hd
  have hid : (relink (intersectOwners d₀.owners g.gowners) d₀).id = id := by
    rw [← hdid]; rfl
  have hown : (intRange 0 (g₂.current_step - 1)).all
      (fun k => hasStepEntry (relink (intersectOwners d₀.owners g.gowners) d₀).owners k)
      = true := by
    refine List.all_eq_true.mpr ?_
    intro k hk
    obtain ⟨hlo, hhi⟩ := PickInduction.intRange_bounds hk
    obtain ⟨v, hv, hSv, hvs⟩ := h.support id d₀ hd hS k hlo (by omega)
    exact List.any_eq_true.mpr
      ⟨v, mem_intersectOwners_of_mem _ _ v hv (h.gow v hSv), beq_iff_eq.mpr hvs⟩
  have hpar : id.parent_id ≠ none →
      (!(relink (intersectOwners d₀.owners g.gowners) d₀).parents.isEmpty) = true := by
    intro hroot
    obtain ⟨c, hc, hSc⟩ := h.parent id d₀ hd hS hroot
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node c hSc)
    obtain ⟨h1, _⟩ := h.coown id c d₀ m hS hSc hd hm hc
    refine not_isEmpty_of_ne_nil _ ?_
    intro hnil
    have hmem : c ∈ (relink (intersectOwners d₀.owners g.gowners) d₀).parents :=
      List.mem_filter.mpr ⟨hc, List.elem_eq_true_of_mem
        (mem_intersectOwners_of_mem _ _ c h1 (h.gow c hSc))⟩
    rw [hnil] at hmem
    exact absurd hmem List.not_mem_nil
  have hsons : id.id.step ≠ g.current_step - 1 →
      (!(relink (intersectOwners d₀.owners g.gowners) d₀).sons.isEmpty) = true := by
    intro hlast
    obtain ⟨c, m, hSc, hm, hpm⟩ := h.son id hS hlast
    obtain ⟨_, h2⟩ := h.coown c id m d₀ hSc hS hm hd hpm
    have hmid : m.id = c := node?_id_eq g c m hm
    have hcs : c ∈ d₀.sons := by
      have := hsmp m (List.mem_of_find?_eq_some hm) id hpm d₀
        (List.mem_of_find?_eq_some hd) hdid
      rw [hmid] at this; exact this
    refine not_isEmpty_of_ne_nil _ ?_
    intro hnil
    have hmem : c ∈ (relink (intersectOwners d₀.owners g.gowners) d₀).sons :=
      List.mem_filter.mpr ⟨hcs, List.elem_eq_true_of_mem
        (mem_intersectOwners_of_mem _ _ c h2 (h.gow c hSc))⟩
    rw [hnil] at hmem
    exact absurd hmem List.not_mem_nil
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

-- ============================================================
-- The sweep
-- ============================================================

/-- **A self-supporting set survives `cleanInvalid`.** No member is ever
removed, so every member is still a global owner afterwards. -/
theorem Closed_cleanInvalidGo (S : PathNodeId → Prop) :
    ∀ (ids : List PathNodeId) (g : GPathM), Sons.SMP g → Closed g S →
      Closed (cleanInvalidGo g ids) S := by
  intro ids
  induction ids with
  | nil => intro g _ h; exact h
  | cons id rest ih =>
    intro g hsmp h
    simp only [cleanInvalidGo]
    split
    · exact ih g hsmp h
    · next d₀ hd =>
      have hsmp₁ := Sons.SMP_updateAt g id (fow g.gowners) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hsmp
      have hsmp₂ := Sons.SMP_unlinkIncompatible _ id hsmp₁
      have h₁ := Closed_updateAt g id S h
      have h₂ := Closed_unlink _ id S h₁
      have hstep₂ : (unlinkIncompatible (updateAt g id (fow g.gowners)) id).current_step
          = g.current_step := by rw [unlinkIncompatible_current]; rfl
      split
      · exact ih _ hsmp₂ h₂
      · next hbad =>
        refine ih _ (Sons.SMP_removeNode _ id hsmp₂) (Closed_removeNode _ id S h₂ ?_)
        intro hSid
        exact hbad (isValidNode_of_Closed g S h hsmp id d₀ hd hSid _ hstep₂)

theorem Closed_cleanInvalid (g : GPathM) (S : PathNodeId → Prop) (hsmp : Sons.SMP g)
    (h : Closed g S) : Closed (cleanInvalid g) S :=
  Closed_cleanInvalidGo S _ g hsmp h

/-- **And therefore the sweep keeps the graph valid**, as soon as the
self-supporting set reaches every step. -/
theorem isValid_cleanInvalid_of_Closed (g : GPathM) (S : PathNodeId → Prop)
    (hsmp : Sons.SMP g) (h : Closed g S)
    (hcov : ∀ l, 0 ≤ l → l < g.current_step → ∃ p, S p ∧ p.id.step = l) :
    isValid (cleanInvalid g) = true := by
  have hc := Closed_cleanInvalid g S hsmp h
  refine PickInduction.isValid_of_gowner _ ?_
  intro k hlo hhi
  obtain ⟨p, hSp, hps⟩ := hcov k hlo (by rw [(pruned_cleanInvalid g).step_eq] at hhi; exact hhi)
  exact ⟨p, hc.gow p hSp, hps⟩

/-- info: 'AbsSat.GraphPath.Model.Survive.isValid_cleanInvalid_of_Closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_cleanInvalid_of_Closed


-- ============================================================
-- What of `Closed` is free, and what is owed
-- ============================================================

/-- **`coown` costs nothing at a review fixpoint.** `Sons.SMP` turns a parent
link round into a son link, and v39's bridge makes a parent *and* a son an
owner. So linked members own each other, whatever `S` is. -/
theorem coown_of_bridge (g : GPathM) (hsmp : Sons.SMP g) (hlink : Bridge.LinksInOwners g)
    (S : PathNodeId → Prop) :
    ∀ p c n m, S p → S c → g.node? p = some n → g.node? c = some m →
      c ∈ n.parents → c ∈ n.owners ∧ p ∈ m.owners := by
  intro p c n m _ _ hn hm hcp
  refine ⟨(hlink p n hn).1 c hcp, ?_⟩
  have hnid : n.id = p := node?_id_eq g p n hn
  have hmid : m.id = c := node?_id_eq g c m hm
  have hs := hsmp n (List.mem_of_find?_eq_some hn) c hcp m (List.mem_of_find?_eq_some hm) hmid
  rw [hnid] at hs
  exact (hlink c m hm).2 p hs

/-!
**The account, for the set the pin defines.** Take
`S = {p : p is a node whose owners at the pinned step include the pinned id}`,
which is exactly the set `cleanInvalid` is trying to keep. Of the six clauses:

* `gow` — free. A node is a global owner, and at the pinned step `OOS` forces
  its own id to be the pinned one, so it survives `filterRequire`.
* `node` — free, by construction of `S`.
* `parent` — free. `coherent_parents` says a node's owners sit inside the
  union of its parents' owners, so a member's pinned owner is owned by some
  parent, and that parent is a member.
* `coown` — free, by `coown_of_bridge` above.
* `son` — **structurally owed.** `coherent_sons` gives a son that is a member,
  but `Closed.son` asks for it through the *parent* table, and turning a son
  link round is the mirror `Sons.SMP` does not have. Same gap as
  `Threaded.hop_up` at step 0.
* `support` — **the residue.** At every step, a member owns a member.

The last one is not a technicality, and it is worth saying exactly what it is:
it says the pruning has a non-empty arc-consistent core. That is `PickValid`,
written without any reference to chains — and it is why the path-shaped
attacks (v27's descent, v41's threading) cannot finish the job on their own.
A path is one node per step, and "a path supports itself" is `PairwiseOwned`.
A *set* need not be, and that is the only room left.
-/

/-- info: 'AbsSat.GraphPath.Model.Survive.coown_of_bridge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms coown_of_bridge


-- ============================================================
-- The core: `support` removed from the account
-- ============================================================

/-!
`support` is the residue, and it does not have to be *proved* — it has to be
**had**. The clauses of `Closed` are all of the form "a member has a member
among its …", so they are closed under union: put every self-supporting set
together and the result is self-supporting. That union is the greatest one,
and it satisfies every clause by construction.

So the account collapses. Instead of six clauses about a set someone has to
exhibit, there is **one** statement left:

> the core reaches every step.

That is the whole of what `cleanInvalid` after a pin still owes. It is also
exactly what the machine's propagation computes, which is the honest reason
this is where the difficulty concentrates — but it is one statement about one
object, not a family of conditions about a chain.
-/

/-- The **arc-consistent core**: the union of every self-supporting set. -/
def Core (g : GPathM) : PathNodeId → Prop := fun p => ∃ S, Closed g S ∧ S p

theorem Core_greatest (g : GPathM) (S : PathNodeId → Prop) (h : Closed g S) :
    ∀ p, S p → Core g p := fun _ hp => ⟨S, h, hp⟩

/-- **The core is self-supporting.** Every clause transfers from the set the
witness came from; `coown` is `S`-independent (`coown_of_bridge`), which is
what makes the union work. -/
theorem Closed_Core (g : GPathM) (hsmp : Sons.SMP g) (hlink : Bridge.LinksInOwners g) :
    Closed g (Core g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, coown_of_bridge g hsmp hlink (Core g)⟩
  · intro p hp; obtain ⟨S, hS, hSp⟩ := hp; exact hS.gow p hSp
  · intro p hp; obtain ⟨S, hS, hSp⟩ := hp; exact hS.node p hSp
  · intro p n hn hp l hlo hhi
    obtain ⟨S, hS, hSp⟩ := hp
    obtain ⟨v, hv, hSv, hvs⟩ := hS.support p n hn hSp l hlo hhi
    exact ⟨v, hv, ⟨S, hS, hSv⟩, hvs⟩
  · intro p n hn hp hroot
    obtain ⟨S, hS, hSp⟩ := hp
    obtain ⟨c, hc, hSc⟩ := hS.parent p n hn hSp hroot
    exact ⟨c, hc, ⟨S, hS, hSc⟩⟩
  · intro p hp hlast
    obtain ⟨S, hS, hSp⟩ := hp
    obtain ⟨c, m, hSc, hm, hpm⟩ := hS.son p hSp hlast
    exact ⟨c, m, ⟨S, hS, hSc⟩, hm, hpm⟩

/-- **The whole of what `cleanInvalid` owes, in one line.** -/
theorem isValid_cleanInvalid_of_Core (g : GPathM) (hsmp : Sons.SMP g)
    (hlink : Bridge.LinksInOwners g)
    (hcov : ∀ l, 0 ≤ l → l < g.current_step → ∃ p, Core g p ∧ p.id.step = l) :
    isValid (cleanInvalid g) = true :=
  isValid_cleanInvalid_of_Closed g (Core g) hsmp (Closed_Core g hsmp hlink) hcov

/-- info: 'AbsSat.GraphPath.Model.Survive.isValid_cleanInvalid_of_Core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_cleanInvalid_of_Core


/-- **The one statement left**, named. Everything `cleanInvalid` owes after a
pin is this — and it is `PickValid` with no reference to chains, no reference
to `isValidNode`, and no reference to the review's fuel loop. -/
def CoreCovers (g : GPathM) : Prop :=
  ∀ l, 0 ≤ l → l < g.current_step → ∃ p, Core g p ∧ p.id.step = l

theorem isValid_cleanInvalid_of_CoreCovers (g : GPathM) (hsmp : Sons.SMP g)
    (hlink : Bridge.LinksInOwners g) (h : CoreCovers g) :
    isValid (cleanInvalid g) = true :=
  isValid_cleanInvalid_of_Core g hsmp hlink h

/-!
**Why the coherence sweeps are not covered by this, and what they would cost.**

`reviewNode` intersects a node's owners with the union of its *neighbours'*
owners, not with the global owners. For a member `p` to keep its support at
step `l` through that, the witness must be owned by one of `p`'s neighbours
too — so `Closed` would need a strictly stronger clause:

> `share` — a member and its member-parent own a common member at every step.

And `share` does not stand still: preserving it one level down asks the
member-parent's own parent to own the same witness, and so on along the whole
member chain. What that adds up to is a selection `u₀ … u_{S-1}`, one per
step, owned by **every** member — and since each `uₗ` is itself a member, the
`u`s own each other. That is `PairwiseOwned` for the selection.

So the wall is now visible from three sides, and it is the same wall:
`PairwiseOwned` along a chain (v28–v42), `support` for a path (v43), and
`share` for the coherence sweeps. Only the core formulation escapes it, and
only for `cleanInvalid` — which is, by v41's measurement, where all of the
risk sits.
-/

/-- info: 'AbsSat.GraphPath.Model.Survive.isValid_cleanInvalid_of_CoreCovers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_cleanInvalid_of_CoreCovers

end AbsSat.GraphPath.Model.Survive
