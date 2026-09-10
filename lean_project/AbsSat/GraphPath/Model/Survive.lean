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


-- ============================================================
-- The candidate set does cover — that half is a theorem
-- ============================================================

/-!
`CoreCovers` is one statement, but it is not atomic. The core is obtained by
**narrowing** a candidate set, and the candidate set for a pin at step `k` to
map id `mid` is

    PinSet g k mid = { p : p is a node owning, at step k, something with map id mid }

Two questions, then: does the candidate set cover every step, and does the
narrowing keep it covering? **The first is a theorem** — v42's threading puts
a full path through the pinned node, and every node of that path owns it, so
every step has a candidate. Only the second is open.

That is worth separating, because it says the difficulty is not "is there
anything compatible with the pick" (there is, at every step, provably) but
"does compatibility survive its own closure".
-/

/-- The candidates a pin leaves: nodes that own something with the pinned map
id at the pinned step. -/
def PinSet (g : GPathM) (k : Int) (mid : NodeId) : PathNodeId → Prop :=
  fun p => ∃ n, g.node? p = some n ∧ ∃ u ∈ ownersAt n.owners k, u.id = mid

/-- **The candidate set reaches every step.** Straight from `Threaded.threaded`:
the pinned node has a full path all of whose nodes own it. -/
theorem pinSet_covers (g : GPathM) (tctx : Threaded.TCtx g) (q : PathNodeId) (nq : PNodeM)
    (hq : g.node? q = some nq) (hself : q ∈ nq.owners) (h1 : 1 ≤ q.id.step)
    (hqhi : q.id.step < g.current_step) :
    ∀ l, 0 ≤ l → l < g.current_step →
      ∃ p, PinSet g q.id.step q.id p ∧ p.id.step = l := by
  obtain ⟨sel, hchain, howns⟩ := Threaded.threaded g tctx q nq hq hself h1 hqhi
  intro l hlo hhi
  obtain ⟨hs, hstep⟩ := hchain.1 l hlo hhi
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨sel l, ⟨n, hn, q, ?_, rfl⟩, hstep⟩
  have hw := howns l hlo hhi
  simp only [ownersOf, hn] at hw
  exact List.mem_filter.mpr ⟨hw, beq_iff_eq.mpr rfl⟩

/-- And on the pinned graph, where `Closed` lives: `filterRequire` touches only
the global owners, so the nodes, their owners and the step count are the same. -/
theorem pinSet_covers_filterRequire (g : GPathM) (tctx : Threaded.TCtx g)
    (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq) (hself : q ∈ nq.owners)
    (h1 : 1 ≤ q.id.step) (hqhi : q.id.step < g.current_step) :
    ∀ l, 0 ≤ l → l < (filterRequire g q.id).current_step →
      ∃ p, PinSet (filterRequire g q.id) q.id.step q.id p ∧ p.id.step = l :=
  pinSet_covers g tctx q nq hq hself h1 hqhi

/-- info: 'AbsSat.GraphPath.Model.Survive.pinSet_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinSet_covers


-- ============================================================
-- The whole chain, with the residue isolated
-- ============================================================

/-- **`Closed` for the candidate set, from two hypotheses and nothing else.**
`gow` comes from `OOS` (at the pinned step a node's only owner is itself, so a
candidate there *is* the pinned id, and survives `filterRequire`); `node` is
free; `parent` is `Threaded.hop_down`; `coown` is `coown_of_bridge`. What is
left as hypotheses is exactly `support` and `son` — the residue of v43. -/
theorem Closed_PinSet (g : GPathM) (tctx : Threaded.TCtx g) (k : Int) (mid : NodeId)
    (hkm : k = mid.step) (hklo : 0 ≤ k) (hkhi : k < g.current_step)
    (hoos : SelfOwn.OOS g) (hrootz : Sons.RootAtZero g) (hsnn : SelfOwn.SNN g)
    (hnodegow : ∀ p n, g.node? p = some n → p ∈ g.gowners)
    (hbelow : ∀ p n, g.node? p = some n → p.id.step < g.current_step)
    (hsmp : Sons.SMP g) (hlink : Bridge.LinksInOwners g)
    (hsupport : ∀ p n, g.node? p = some n → PinSet g k mid p →
      ∀ l, 0 ≤ l → l < g.current_step →
        ∃ v ∈ n.owners, PinSet g k mid v ∧ v.id.step = l)
    (hson : ∀ p, PinSet g k mid p → p.id.step ≠ g.current_step - 1 →
      ∃ c m, PinSet g k mid c ∧ g.node? c = some m ∧ p ∈ m.parents) :
    Closed (filterRequire g mid) (PinSet g k mid) := by
  refine ⟨?_, ?_, ?_, ?_, hson, coown_of_bridge _ hsmp hlink _⟩
  · -- gow
    intro p hp
    obtain ⟨n, hn, u, hu, humid⟩ := hp
    refine List.mem_filter.mpr ⟨hnodegow p n hn, ?_⟩
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
    have hus : u.id.step = k := eq_of_beq (List.mem_filter.mp hu).2
    have hnid : n.id = p := node?_id_eq g p n hn
    by_cases hks : p.id.step = k
    · refine Or.inr (beq_iff_eq.mpr ?_)
      have : u = n.id := hoos n (List.mem_of_find?_eq_some hn) u (List.mem_filter.mp hu).1
        (by rw [hus, hnid, hks])
      rw [← humid, this, hnid]
    · exact Or.inl (fun h => hks (h.trans hkm.symm))
  · intro p hp
    obtain ⟨n, hn, _⟩ := hp
    exact (show (g.node? p).isSome = true by rw [hn]; rfl)
  · exact hsupport
  · -- parent, via hop_down
    intro p n hn hp hroot
    obtain ⟨n', hn', u, hu, humid⟩ := hp
    have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
    have hus : u.id.step = k := eq_of_beq (List.mem_filter.mp hu).2
    have hnid : n.id = p := node?_id_eq g p n hn
    have hpos : 0 < p.id.step := by
      have hz : p.id.step ≠ 0 := by
        intro h0
        exact hroot (by
          have := hrootz n (List.mem_of_find?_eq_some hn) (by rw [hnid]; exact h0)
          rwa [hnid] at this)
      have := hsnn n (List.mem_of_find?_eq_some hn)
      rw [hnid] at this
      omega
    obtain ⟨c, hc, m, hm, hmu⟩ :=
      Threaded.hop_down g tctx p n hn hpos (hbelow p n hn) u (by rw [← hnn]; exact
        (List.mem_filter.mp hu).1) (by rw [hus]; exact hklo) (by rw [hus]; exact hkhi)
    exact ⟨c, hc, m, hm, u, List.mem_filter.mpr ⟨hmu, beq_iff_eq.mpr hus⟩, humid⟩

/-- **The chain, end to end.** Threading gives the coverage of the candidates,
`Closed_PinSet` gives the closure, `Core_greatest` lifts it to the core, and
`isValid_cleanInvalid_of_Core` finishes. Everything is proved except the two
hypotheses of `Closed_PinSet`. -/
theorem isValid_cleanInvalid_pin (g : GPathM) (tctx : Threaded.TCtx g)
    (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq) (hself : q ∈ nq.owners)
    (h1 : 1 ≤ q.id.step) (hqhi : q.id.step < g.current_step)
    (hoos : SelfOwn.OOS g) (hrootz : Sons.RootAtZero g) (hsnn : SelfOwn.SNN g)
    (hnodegow : ∀ p n, g.node? p = some n → p ∈ g.gowners)
    (hbelow : ∀ p n, g.node? p = some n → p.id.step < g.current_step)
    (hsmp : Sons.SMP g) (hlink : Bridge.LinksInOwners g)
    (hsupport : ∀ p n, g.node? p = some n → PinSet g q.id.step q.id p →
      ∀ l, 0 ≤ l → l < g.current_step →
        ∃ v ∈ n.owners, PinSet g q.id.step q.id v ∧ v.id.step = l)
    (hson : ∀ p, PinSet g q.id.step q.id p → p.id.step ≠ g.current_step - 1 →
      ∃ c m, PinSet g q.id.step q.id c ∧ g.node? c = some m ∧ p ∈ m.parents) :
    isValid (cleanInvalid (filterRequire g q.id)) = true := by
  have hcl : Closed (filterRequire g q.id) (PinSet g q.id.step q.id) :=
    Closed_PinSet g tctx q.id.step q.id rfl (by omega) hqhi hoos hrootz hsnn hnodegow hbelow
      hsmp hlink hsupport hson
  refine isValid_cleanInvalid_of_Core _ (Sons.SMP_filterRequire g q.id hsmp) hlink ?_
  intro l hlo hhi
  obtain ⟨p, hp, hps⟩ := pinSet_covers_filterRequire g tctx q nq hq hself h1 hqhi l hlo hhi
  exact ⟨p, Core_greatest _ _ hcl p hp, hps⟩

/-- info: 'AbsSat.GraphPath.Model.Survive.isValid_cleanInvalid_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_cleanInvalid_pin


-- ============================================================
-- How much of `support` is free
-- ============================================================

/-!
`support` asks a candidate for a candidate owner at **every** step. Four of
those steps cost nothing, and it is worth seeing which, because it says where
the residue actually lives.

* the **pinned step** — the candidate owns the pinned node by definition, and
  the pinned node is a candidate (it owns itself);
* the candidate's **own step** — `SelfOwned`;
* the step **below** — `Threaded.hop_down` produces a parent that is a
  candidate, and v39's bridge makes a parent an owner;
* the step **above** — `Threaded.hop_up` and the bridge's son side.

So the residue is not "does a candidate have candidate support" in general; it
is that question **at distance two or more**. And that is exactly where the
refuted transitivity (v40) would have carried it: down twice gives a candidate
owned by the parent, not by the node.
-/

variable (g : GPathM) (k : Int) (mid : NodeId)

/-- At the pinned step. -/
theorem support_at_pin (tctx : Threaded.TCtx g) (hklo : 0 ≤ k) (hkhi : k < g.current_step)
    (hselfown : ∀ p n, g.node? p = some n → p ∈ n.owners)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n) (hp : PinSet g k mid p) :
    ∃ v ∈ n.owners, PinSet g k mid v ∧ v.id.step = k := by
  obtain ⟨n', hn', u, hu, humid⟩ := hp
  have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
  have hus : u.id.step = k := eq_of_beq (List.mem_filter.mp hu).2
  have huo : u ∈ n.owners := by rw [← hnn]; exact (List.mem_filter.mp hu).1
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
    (tctx.ownerNode p n hn u huo (by rw [hus]; exact hklo) (by rw [hus]; exact hkhi))
  refine ⟨u, huo, ⟨m, hm, u, ?_, humid⟩, hus⟩
  exact List.mem_filter.mpr ⟨hselfown u m hm, beq_iff_eq.mpr hus⟩

/-- At its own step. -/
theorem support_at_self (hselfown : ∀ p n, g.node? p = some n → p ∈ n.owners)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n) (hp : PinSet g k mid p) :
    ∃ v ∈ n.owners, PinSet g k mid v ∧ v.id.step = p.id.step :=
  ⟨p, hselfown p n hn, hp, rfl⟩

/-- One step below: the parent the descent produces is a candidate, and v39's
bridge makes it an owner. -/
theorem support_below (tctx : Threaded.TCtx g) (hklo : 0 ≤ k) (hkhi : k < g.current_step)
    (hlink : Bridge.LinksInOwners g)
    (hbelow : ∀ p n, g.node? p = some n → p.id.step < g.current_step)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n) (hp : PinSet g k mid p)
    (hpos : 0 < p.id.step) :
    ∃ v ∈ n.owners, PinSet g k mid v ∧ v.id.step = p.id.step - 1 := by
  obtain ⟨n', hn', u, hu, humid⟩ := hp
  have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
  have hus : u.id.step = k := eq_of_beq (List.mem_filter.mp hu).2
  obtain ⟨c, hc, m, hm, hmu⟩ :=
    Threaded.hop_down g tctx p n hn hpos (hbelow p n hn) u
      (by rw [← hnn]; exact (List.mem_filter.mp hu).1)
      (by rw [hus]; exact hklo) (by rw [hus]; exact hkhi)
  have hnid : n.id = p := node?_id_eq g p n hn
  refine ⟨c, (hlink p n hn).1 c hc, ⟨m, hm, u, List.mem_filter.mpr ⟨hmu, beq_iff_eq.mpr hus⟩,
    humid⟩, ?_⟩
  have := tctx.shape.pbelow n (List.mem_of_find?_eq_some hn) c hc
  rw [this, hnid]

/-- One step above: the son the climb produces is a candidate, and the bridge's
son side makes it an owner. `Sons.SAbove` supplies the step. -/
theorem support_above (tctx : Threaded.TCtx g) (hklo : 0 ≤ k) (hkhi : k < g.current_step)
    (hlink : Bridge.LinksInOwners g)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n) (hp : PinSet g k mid p)
    (hlo : 1 ≤ p.id.step) (hhi : p.id.step ≤ g.current_step - 2) :
    ∃ v ∈ n.owners, PinSet g k mid v ∧ v.id.step = p.id.step + 1 := by
  obtain ⟨n', hn', u, hu, humid⟩ := hp
  have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
  have hus : u.id.step = k := eq_of_beq (List.mem_filter.mp hu).2
  obtain ⟨c, hc, m, hm, hmu, hcstep⟩ :=
    Threaded.hop_up g tctx p n hn hlo hhi u
      (by rw [← hnn]; exact (List.mem_filter.mp hu).1)
      (by rw [hus]; exact hklo) (by rw [hus]; exact hkhi)
  exact ⟨c, (hlink p n hn).2 c hc,
    ⟨m, hm, u, List.mem_filter.mpr ⟨hmu, beq_iff_eq.mpr hus⟩, humid⟩, hcstep⟩

/-- info: 'AbsSat.GraphPath.Model.Survive.support_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms support_below


-- ============================================================
-- Two refutations that pin the residue down
-- ============================================================

/-- The candidate set, closed downward under ownership. ⚠ **Refuted by
measurement** — `lake exe extend --downclosed`, 8 instances: **722,851** of
3,723,185 (candidate, owner) pairs have an owner that is *not* a candidate,
and 618,477 of those sit at a far step.

Had it been true, `support` would have been free: `owners_ok` already hands out
an owner at every step. It is not, so `support`'s **existential is essential** —
a candidate has *some* candidate owner at a far step, not all of them.

(The neighbouring statement, "an owner of a candidate owns the candidate's own
pinned owner", is the support clique, refuted in v28 at 63.9M.) -/
def PinSetDownClosed (g : GPathM) (k : Int) (mid : NodeId) : Prop :=
  ∀ p n, g.node? p = some n → PinSet g k mid p →
    ∀ v ∈ n.owners, 0 ≤ v.id.step → v.id.step < g.current_step → PinSet g k mid v

/-- The obvious witness for `support`: descend from the candidate picking, at
each step, a parent that still owns the pinned node — every node of that
descent is a candidate by `Threaded.hop_down`. ⚠ **Refuted by measurement** —
`lake exe extend --descentin`, 8 instances: the descent leaves the starting
node's own owners in **6,371** of 125,528 runs, and **28,665** of 1,315,726
individual hops land outside it.

v39's bridge gives the first hop for free (a parent is an owner) and v40's
refuted transitivity already said the second could fail; this measures how
often it actually does. So `support` is true (0 failures in 3.47M checks) but
**not by the natural construction**: which parent the descent picks matters. -/
def AnchoredDescentStaysInSupport (g : GPathM) : Prop :=
  ∀ p n, g.node? p = some n → ∀ u ∈ n.owners, ∀ c m,
    g.node? c = some m → u ∈ m.owners → c.id.step < p.id.step → c ∈ n.owners

/-!
**Where that leaves the residue.** Three measured facts now bracket it:

| statement | form | measured |
|---|---|---|
| a candidate has a candidate owner at every step | ∃ | 0 of 3,473,942 |
| *every* owner of a candidate is a candidate | ∀ | **722,851 of 3,723,185** |
| the anchored descent stays inside the support | construction | **6,371 of 125,528** |

The residue is true, strictly existential, and not witnessed by the obvious
construction. `Threaded.owner_below_on_descent` says what the search space
looks like — the owners below a node are ancestors reached by chains that
carry the owner — so what is missing is a *choice rule*: among the descents
from a candidate that carry the pin, one that also stays inside the candidate's
own support.
-/

end AbsSat.GraphPath.Model.Survive
