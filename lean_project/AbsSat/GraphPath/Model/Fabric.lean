-- lean_project/AbsSat/GraphPath/Model/Fabric.lean
import AbsSat.GraphPath.Model.SymReview

/-!
# Fabric: `Survive.Woven` generalised

`Survive.Woven g S` is what survives the whole review loop, and it asks one
thing too many: that **every member owns every member**. That makes a woven set
a clique — in practice, the nodes of one co-owned chain. v64 measured what the
reader actually needs to survive: choosing `r` keeps *all* of `owners(r)`
(0 killed in 195,167), and `owners(r)` is **not** a clique (v54: 18–31 % of
owner pairs do not own each other). So `Woven` cannot be the reason.

What is the reason, then? Look at what the review actually checks of a node:
an owner at every step, a parent and a son among its owners, and every owner
also owned by some parent and some son. None of that needs the node's *whole*
table — only **some** sub-table that holds itself up. That is the
generalisation:

    Fabric g S T : every member p keeps a sub-table T p of its owners, and
      · T is symmetric and stays inside S, and contains p itself;
      · T p has an entry at every step;
      · every entry of T p is backed by a parent c of p with T p c and T c v,
        and by a son c of p with T p c and T c v;
      · members are real nodes and global owners.

`Woven` is the special case `T p v := S v` (`Fabric_of_Woven`). Every theorem
of `Survive` about the review loop has a fabric version here, **and** a version
for the symmetric review and the owners-pin of `SymReview`.

Two things change against `Woven`, both on purpose:

* **Tables may shrink.** The review is free to drop entries outside `T p`; the
  fabric only promises that it never drops one inside. That is exactly the
  behaviour `--selfsupport` measured: tables shrink after a pin, nodes do not
  die.
* **Symmetry of `T`** replaces the co-ownership of linked members, and it is
  what the mirror step of the symmetric review needs.

## What is proved

* `Fabric_updateAt`, `Fabric_symmetrize`, `Fabric_unlink`, `Fabric_removeNode`
  — the four operations; `isValidNode_of_Fabric(_self)` — a member always
  passes the test, so the sweeps never remove one.
* The whole original loop (`FOk_review`, `isValid_filterAll_of_Fabric`) and the
  whole symmetric one with the owners-pin (`FOk_reviewSym`, `FOk_readStepSym`,
  `isValid_readStepSym_of_Fabric`).
* `Fabric_of_Woven` — `Woven` is the case `T p v := S v`.
* `isValid_readStepSym_of_FabricAt` — the reader's step is safe wherever
  `owners(r)` contains a fabric through `r`.
* `Fabric_sol`, `FabricAt_of_chain` — the solutions through `r` form a fabric,
  so a node on a solution always has one under it.
* `alive_readStepSym_of_OwnersExactAt` — under the author's definition of
  owners (every owner of `r` lies on a common solution with `r`), choosing `r`
  kills none of its owners.

## What is measured (`lake exe cnfmap --fabric`)

The greatest fabric inside `owners(r)`, at every choice of every final state
of the symmetric machine, five seeds: **all of `owners(r)`** in 4,888 of 4,888
choices (159,621 nodes), with 0.35 % of the table entries trimmed on the way.

So the reader's wall is now a *static* statement about one state — *`owners(r)`
contains a fabric* — rather than a statement about what the review does next.
That static statement is not proved.
-/

namespace AbsSat.GraphPath.Model.Fabric

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.SymReview

/-- The owners intersection with a list, as a node transformer. -/
abbrev fow (b : List PathNodeId) : PNodeM → PNodeM :=
  fun n => { n with owners := intersectOwners n.owners b }

/-- A **fabric**: members `S`, each holding itself up on a sub-table `T p` of
its owners. -/
structure Fabric (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) : Prop where
  /-- Members are global owners — what `isValid` counts. -/
  gow : ∀ p, S p → p ∈ g.gowners
  /-- Members are real nodes. -/
  node : ∀ p, S p → (g.node? p).isSome = true
  /-- A member's table stays among members. -/
  inS : ∀ p v, S p → T p v → S v
  /-- Tables are symmetric. -/
  symm : ∀ p v, S p → T p v → T v p
  /-- A member keeps itself. -/
  self : ∀ p, S p → T p p
  /-- The table is a sub-table of the node's owners. -/
  sub : ∀ p n, g.node? p = some n → S p → ∀ v, T p v → v ∈ n.owners
  /-- At every step, an entry. -/
  support : ∀ p, S p → ∀ l, 0 ≤ l → l < g.current_step → ∃ v, T p v ∧ v.id.step = l
  /-- Every entry is carried by a parent inside the table. -/
  up : ∀ p n, g.node? p = some n → S p → p.parent_id ≠ none →
    ∀ v, T p v → ∃ c ∈ n.parents, T p c ∧ T c v
  /-- Every entry is carried by a son inside the table — phrased through the
  son's *parent* table, as `Survive.Closed.son`, so `Sons.SMP` turns it round. -/
  down : ∀ p, S p → p.id.step ≠ g.current_step - 1 →
    ∀ v, T p v → ∃ c m, g.node? c = some m ∧ p ∈ m.parents ∧ T p c ∧ T c v

-- ============================================================
-- Node transformers, seen through `node?`
-- ============================================================

theorem updMap_fow_parents (id : PathNodeId) (b : List PathNodeId) (n : PNodeM) :
    (updMap id (fow b) n).parents = n.parents := by
  unfold updMap; split <;> rfl

theorem mem_updMap_fow_owners (id : PathNodeId) (b : List PathNodeId) (n : PNodeM)
    (v : PathNodeId) (hv : v ∈ n.owners) (hb : n.id = id → v ∈ b) :
    v ∈ (updMap id (fow b) n).owners := by
  unfold updMap
  split
  · next hh => exact mem_intersectOwners_of_mem _ _ v hv (hb (eq_of_beq hh))
  · exact hv

-- ============================================================
-- The four operations
-- ============================================================

/-- **The owners intersection**, against any list the member's table sits in. -/
theorem Fabric_updateAt (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (b : List PathNodeId)
    (hb : S id → ∀ v, T id v → v ∈ b) (h : Fabric g S T) :
    Fabric (updateAt g id (fow b)) S T := by
  have hnode : ∀ p n, g.node? p = some n →
      (updateAt g id (fow b)).node? p = some (updMap id (fow b) n) :=
    fun p n hn => updateAt_node? g id (fow b) (fun _ => rfl) p n hn
  have hback : ∀ p n', S p → (updateAt g id (fow b)).node? p = some n' →
      ∃ n, g.node? p = some n ∧ n' = updMap id (fow b) n := by
    intro p n' hp hn'
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    exact ⟨n, hn, Option.some.inj (hn'.symm.trans (hnode p n hn))⟩
  refine ⟨h.gow, ?_, h.inS, h.symm, h.self, ?_, h.support, ?_, ?_⟩
  · intro p hp
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    rw [hnode p n hn]; rfl
  · intro p n' hn' hp v hv
    obtain ⟨n, hn, rfl⟩ := hback p n' hp hn'
    refine mem_updMap_fow_owners id b n v (h.sub p n hn hp v hv) (fun he => ?_)
    have hpid : p = id := (node?_id_eq g p n hn).symm.trans he
    exact hb (hpid ▸ hp) v (hpid ▸ hv)
  · intro p n' hn' hp hroot v hv
    obtain ⟨n, hn, rfl⟩ := hback p n' hp hn'
    rw [updMap_fow_parents]
    exact h.up p n hn hp hroot v hv
  · intro p hp hlast v hv
    obtain ⟨c, m, hm, hpm, h1, h2⟩ := h.down p hp hlast v hv
    exact ⟨c, _, hnode c m hm, by rw [updMap_fow_parents]; exact hpm, h1, h2⟩

/-- **The mirror step.** It removes `id` from a table only where the node is
outside `owners(id)` — and a member holding `id` in its table is inside it, by
symmetry of `T`. -/
theorem Fabric_symmetrize (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : Fabric g S T) :
    Fabric (symmetrize g id) S T := by
  cases hid : g.node? id with
  | none =>
    have : symmetrize g id = g := by simp only [symmetrize, hid]
    rw [this]; exact h
  | some d =>
    have hnode : ∀ p n, g.node? p = some n →
        (symmetrize g id).node? p = some (symMap d id n) := by
      intro p n hn; rw [symmetrize_node? g id d hid, hn]; rfl
    have hback : ∀ p n', S p → (symmetrize g id).node? p = some n' →
        ∃ n, g.node? p = some n ∧ n' = symMap d id n := by
      intro p n' hp hn'
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      exact ⟨n, hn, Option.some.inj (hn'.symm.trans (hnode p n hn))⟩
    have hstep := symmetrize_current g id
    refine ⟨?_, ?_, h.inS, h.symm, h.self, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [symmetrize_gowners]; exact h.gow p hp
    · intro p hp
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      rw [hnode p n hn]; rfl
    · intro p n' hn' hp v hv
      obtain ⟨n, hn, rfl⟩ := hback p n' hp hn'
      refine mem_symMap_owners d id n v (h.sub p n hn hp v hv) ?_
      if hvid : v = id then
        right; right
        have hSid : S id := hvid ▸ h.inS p v hp hv
        have hTid : T id p := hvid ▸ h.symm p v hp hv
        rw [node?_id_eq g p n hn]
        exact h.sub id d hid hSid p hTid
      else exact Or.inl hvid
    · intro p hp l hlo hhi
      rw [hstep] at hhi
      exact h.support p hp l hlo hhi
    · intro p n' hn' hp hroot v hv
      obtain ⟨n, hn, rfl⟩ := hback p n' hp hn'
      rw [symMap_parents]
      exact h.up p n hn hp hroot v hv
    · intro p hp hlast v hv
      rw [hstep] at hlast
      obtain ⟨c, m, hm, hpm, h1, h2⟩ := h.down p hp hlast v hv
      exact ⟨c, _, hnode c m hm, by rw [symMap_parents]; exact hpm, h1, h2⟩

/-- **The unlink.** It cuts a link only between a node and something outside
its owners; a link inside a table is inside the owners at both ends. -/
theorem Fabric_unlink (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : Fabric g S T) :
    Fabric (unlinkIncompatible g id) S T := by
  cases hid : g.node? id with
  | none => simpa only [GPathM.unlinkIncompatible, hid] using h
  | some n₀ =>
    have hnode : ∀ p n, g.node? p = some n →
        (unlinkIncompatible g id).node? p = some (unlinkMap n₀ id n) :=
      fun p n hn => unlinkIncompatible_node? g id n₀ hid p n hn
    have hback : ∀ p n', S p → (unlinkIncompatible g id).node? p = some n' →
        ∃ n, g.node? p = some n ∧ n' = unlinkMap n₀ id n := by
      intro p n' hp hn'
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      exact ⟨n, hn, Option.some.inj (hn'.symm.trans (hnode p n hn))⟩
    -- a link inside a table survives: both side conditions from `sub` + `symm`
    have hlink : ∀ p c n m, S p → g.node? p = some n → g.node? c = some m → T p c →
        c ∈ n.parents → c ∈ (unlinkMap n₀ id n).parents := by
      intro p c n m hp hn hm hpc hcp
      have hSc := h.inS p c hp hpc
      refine Survive.mem_parents_unlinkMap n₀ id n c hcp ?_ ?_
      · intro he
        have : n = n₀ := by
          have : g.node? id = some n := by rw [← he, node?_id_eq g p n hn]; exact hn
          exact Option.some.inj (this.symm.trans hid)
        rw [← this]; exact h.sub p n hn hp c hpc
      · intro he
        have : m = n₀ := by
          have : g.node? id = some m := by rw [← he]; exact hm
          exact Option.some.inj (this.symm.trans hid)
        rw [← this, node?_id_eq g p n hn]
        exact h.sub c m hm hSc p (h.symm p c hp hpc)
    have hstep := unlinkIncompatible_current g id
    refine ⟨?_, ?_, h.inS, h.symm, h.self, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [unlinkIncompatible_gowners]; exact h.gow p hp
    · intro p hp
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      rw [hnode p n hn]; rfl
    · intro p n' hn' hp v hv
      obtain ⟨n, hn, rfl⟩ := hback p n' hp hn'
      rw [unlinkMap_owners]
      exact h.sub p n hn hp v hv
    · intro p hp l hlo hhi
      rw [hstep] at hhi
      exact h.support p hp l hlo hhi
    · intro p n' hn' hp hroot v hv
      obtain ⟨n, hn, rfl⟩ := hback p n' hp hn'
      obtain ⟨c, hc, h1, h2⟩ := h.up p n hn hp hroot v hv
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node c (h.inS p c hp h1))
      exact ⟨c, hlink p c n m hp hn hm h1 hc, h1, h2⟩
    · intro p hp hlast v hv
      rw [hstep] at hlast
      obtain ⟨c, m, hm, hpm, h1, h2⟩ := h.down p hp hlast v hv
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      have hSc := h.inS p c hp h1
      exact ⟨c, _, hnode c m hm,
        hlink c p m n hSc hm hn (h.symm p c hp h1) hpm, h1, h2⟩

/-- **Removing a non-member.** Tables never mention it, so nothing a fabric
relies on goes with it. -/
theorem Fabric_removeNode (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : Fabric g S T) (hns : ¬ S id) :
    Fabric (removeNode g id) S T := by
  have hne : ∀ p, S p → p ≠ id := fun p hp he => hns (he ▸ hp)
  have hnode : ∀ p n, S p → g.node? p = some n →
      (removeNode g id).node? p = some (unlink id n) :=
    fun p n hp hn => removeNode_node? g id p n hn (hne p hp)
  have hback : ∀ p n', S p → (removeNode g id).node? p = some n' →
      ∃ n, g.node? p = some n ∧ n' = unlink id n := by
    intro p n' hp hn'
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    exact ⟨n, hn, Option.some.inj (hn'.symm.trans (hnode p n hp hn))⟩
  refine ⟨?_, ?_, h.inS, h.symm, h.self, ?_, h.support, ?_, ?_⟩
  · intro p hp
    rw [removeNode_gowners]
    exact List.mem_filter.mpr ⟨h.gow p hp, bne_iff_ne.mpr (hne p hp)⟩
  · intro p hp
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    rw [hnode p n hp hn]; rfl
  · intro p n' hn' hp v hv
    obtain ⟨n, hn, rfl⟩ := hback p n' hp hn'
    exact h.sub p n hn hp v hv
  · intro p n' hn' hp hroot v hv
    obtain ⟨n, hn, rfl⟩ := hback p n' hp hn'
    obtain ⟨c, hc, h1, h2⟩ := h.up p n hn hp hroot v hv
    exact ⟨c, List.mem_filter.mpr ⟨hc, bne_iff_ne.mpr (hne c (h.inS p c hp h1))⟩, h1, h2⟩
  · intro p hp hlast v hv
    obtain ⟨c, m, hm, hpm, h1, h2⟩ := h.down p hp hlast v hv
    have hSc := h.inS p c hp h1
    exact ⟨c, unlink id m, hnode c m hSc hm,
      List.mem_filter.mpr ⟨hpm, bne_iff_ne.mpr (hne p hp)⟩, h1, h2⟩


-- ============================================================
-- A member always passes the validity test
-- ============================================================

private theorem not_isEmpty_of_mem {α : Type} (l : List α) (a : α) (ha : a ∈ l) :
    (!l.isEmpty) = true := by
  cases l with
  | nil => exact absurd ha List.not_mem_nil
  | cons _ _ => rfl

/-- **The heart, generalised.** A member passes `isValidNode` after its table
is intersected with any list its sub-table sits in: `support` answers the
owners test, `up` (at the member itself) the parents test, `down` the sons
test turned round with `Sons.SMP`. -/
theorem isValidNode_of_Fabric (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : Fabric g S T) (hsmp : Sons.SMP g)
    (b : List PathNodeId) (id : PathNodeId) (hb : ∀ v, T id v → v ∈ b)
    (d₀ : PNodeM) (hd : g.node? id = some d₀) (hS : S id)
    (g₂ : GPathM) (hstep : g₂.current_step = g.current_step) :
    isValidNode g₂ (relink (intersectOwners d₀.owners b) d₀) = true := by
  have hdid : d₀.id = id := node?_id_eq g id d₀ hd
  have hid : (relink (intersectOwners d₀.owners b) d₀).id = id := by rw [← hdid]; rfl
  have hkeep : ∀ v, T id v → v ∈ intersectOwners d₀.owners b :=
    fun v hv => mem_intersectOwners_of_mem _ _ v (h.sub id d₀ hd hS v hv) (hb v hv)
  have hown : (intRange 0 (g₂.current_step - 1)).all
      (fun k => hasStepEntry (relink (intersectOwners d₀.owners b) d₀).owners k) = true := by
    refine List.all_eq_true.mpr ?_
    intro k hk
    obtain ⟨hlo, hhi⟩ := PickInduction.intRange_bounds hk
    obtain ⟨v, hv, hvs⟩ := h.support id hS k hlo (by omega)
    exact List.any_eq_true.mpr ⟨v, hkeep v hv, beq_iff_eq.mpr hvs⟩
  have hpar : id.parent_id ≠ none →
      (!(relink (intersectOwners d₀.owners b) d₀).parents.isEmpty) = true := by
    intro hroot
    obtain ⟨c, hc, h1, _⟩ := h.up id d₀ hd hS hroot id (h.self id hS)
    exact not_isEmpty_of_mem _ c
      (List.mem_filter.mpr ⟨hc, List.elem_eq_true_of_mem (hkeep c h1)⟩)
  have hsons : id.id.step ≠ g.current_step - 1 →
      (!(relink (intersectOwners d₀.owners b) d₀).sons.isEmpty) = true := by
    intro hlast
    obtain ⟨c, m, hm, hpm, h1, _⟩ := h.down id hS hlast id (h.self id hS)
    have hmid : m.id = c := node?_id_eq g c m hm
    have hcs : c ∈ d₀.sons := by
      have := hsmp m (List.mem_of_find?_eq_some hm) id hpm d₀
        (List.mem_of_find?_eq_some hd) hdid
      rw [hmid] at this; exact this
    exact not_isEmpty_of_mem _ c
      (List.mem_filter.mpr ⟨hcs, List.elem_eq_true_of_mem (hkeep c h1)⟩)
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

/-- **A member passes the test as it stands**, before any intersection. -/
theorem isValidNode_of_Fabric_self (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : Fabric g S T) (hsmp : Sons.SMP g)
    (id : PathNodeId) (d₀ : PNodeM) (hd : g.node? id = some d₀) (hS : S id) :
    isValidNode g d₀ = true := by
  have hdid : d₀.id = id := node?_id_eq g id d₀ hd
  have hown : (intRange 0 (g.current_step - 1)).all
      (fun k => hasStepEntry d₀.owners k) = true := by
    refine List.all_eq_true.mpr ?_
    intro k hk
    obtain ⟨hlo, hhi⟩ := PickInduction.intRange_bounds hk
    obtain ⟨v, hv, hvs⟩ := h.support id hS k hlo (by omega)
    exact List.any_eq_true.mpr ⟨v, h.sub id d₀ hd hS v hv, beq_iff_eq.mpr hvs⟩
  have hpar : id.parent_id ≠ none → (!d₀.parents.isEmpty) = true := by
    intro hroot
    obtain ⟨c, hc, _, _⟩ := h.up id d₀ hd hS hroot id (h.self id hS)
    exact not_isEmpty_of_mem _ c hc
  have hsons : id.id.step ≠ g.current_step - 1 → (!d₀.sons.isEmpty) = true := by
    intro hlast
    obtain ⟨c, m, hm, hpm, _, _⟩ := h.down id hS hlast id (h.self id hS)
    have hmid : m.id = c := node?_id_eq g c m hm
    have hcs : c ∈ d₀.sons := by
      have := hsmp m (List.mem_of_find?_eq_some hm) id hpm d₀
        (List.mem_of_find?_eq_some hd) hdid
      rw [hmid] at this; exact this
    exact not_isEmpty_of_mem _ c hcs
  simp only [isValidNode]
  split
  · split
    · exact hown
    · next hl =>
      refine (Bool.and_eq_true _ _).mpr ⟨hown, hsons ?_⟩
      intro he
      exact hl (by rw [hdid, he]; exact beq_iff_eq.mpr rfl)
  · next hr =>
    split
    · exact (Bool.and_eq_true _ _).mpr ⟨hown, hpar (by rw [hdid] at hr; simpa using hr)⟩
    · next hl =>
      refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr
        ⟨hown, hpar (by rw [hdid] at hr; simpa using hr)⟩, hsons ?_⟩
      intro he
      exact hl (by rw [hdid, he]; exact beq_iff_eq.mpr rfl)

-- ============================================================
-- The structural invariants the sweeps need, through the mirror step
-- ============================================================

theorem symmetrize_nodes_mem (g : GPathM) (id : PathNodeId) (n' : PNodeM)
    (hn' : n' ∈ (symmetrize g id).nodes) :
    ∃ d, ∃ n ∈ g.nodes, n' = symMap d id n ∨ n' = n := by
  unfold symmetrize at hn'
  split at hn'
  · exact ⟨n', n', hn', Or.inr rfl⟩
  · next d _ =>
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
    exact ⟨d, n, hn, Or.inl hEq.symm⟩

theorem SMP_symmetrize (g : GPathM) (id : PathNodeId) (h : Sons.SMP g) :
    Sons.SMP (symmetrize g id) := by
  intro n' hn' p hp m' hm' hmid
  obtain ⟨d, n, hn, hne⟩ := symmetrize_nodes_mem g id n' hn'
  obtain ⟨d', m, hm, hme⟩ := symmetrize_nodes_mem g id m' hm'
  have hnid : n'.id = n.id := by rcases hne with rfl | rfl <;> simp [symMap_id]
  have hnpar : n'.parents = n.parents := by rcases hne with rfl | rfl <;> simp [symMap_parents]
  have hmid' : m'.id = m.id := by rcases hme with rfl | rfl <;> simp [symMap_id]
  have hmson : m'.sons = m.sons := by rcases hme with rfl | rfl <;> simp [symMap_sons]
  rw [hnpar] at hp
  rw [hmid'] at hmid
  rw [hnid, hmson]
  exact h n hn p hp m hm hmid

theorem NotRoot_symmetrize (g : GPathM) (id : PathNodeId) (h : Parents.NotRoot g) :
    Parents.NotRoot (symmetrize g id) := by
  intro n' hn' hpos
  obtain ⟨d, n, hn, hne⟩ := symmetrize_nodes_mem g id n' hn'
  have hnid : n'.id = n.id := by rcases hne with rfl | rfl <;> simp [symMap_id]
  rw [hnid] at hpos ⊢
  exact h n hn hpos


-- ============================================================
-- The bundle, and validity
-- ============================================================

/-- A fabric, plus the two structural invariants that let its `up`/`down`
clauses answer the coherence sweeps. -/
structure FOk (g : GPathM) (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop) :
    Prop where
  fab : Fabric g S T
  smp : Sons.SMP g
  nr  : Parents.NotRoot g

/-- **A non-empty fabric makes the graph valid.** Its `support` clause reaches
every step by itself — no separate coverage hypothesis. -/
theorem isValid_of_Fabric (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : Fabric g S T) (hne : ∃ p, S p) :
    isValid g = true := by
  obtain ⟨p, hp⟩ := hne
  refine PickInduction.isValid_of_gowner _ ?_
  intro k hlo hhi
  obtain ⟨v, hv, hvs⟩ := h.support p hp k hlo hhi
  exact ⟨v, h.gow v (h.inS p v hp hv), hvs⟩

theorem FOk_updateAt (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (b : List PathNodeId)
    (hb : S id → ∀ v, T id v → v ∈ b) (h : FOk g S T) :
    FOk (updateAt g id (fow b)) S T where
  fab := Fabric_updateAt g id S T b hb h.fab
  smp := Sons.SMP_updateAt g id (fow b) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) h.smp
  nr := Parents.NotRoot_of_pruned
    (pruned_updateAt g id (fow b) (fun _ => rfl) (fun _ _ hq => (List.mem_filter.mp hq).1)
      (fun _ _ hp => hp)) h.nr

theorem FOk_unlink (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) :
    FOk (unlinkIncompatible g id) S T where
  fab := Fabric_unlink g id S T h.fab
  smp := Sons.SMP_unlinkIncompatible g id h.smp
  nr := Parents.NotRoot_of_pruned (pruned_unlinkIncompatible g id) h.nr

theorem FOk_symmetrize (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) :
    FOk (symmetrize g id) S T where
  fab := Fabric_symmetrize g id S T h.fab
  smp := SMP_symmetrize g id h.smp
  nr := NotRoot_symmetrize g id h.nr

theorem FOk_removeNode (g : GPathM) (id : PathNodeId) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (hns : ¬ S id) :
    FOk (removeNode g id) S T where
  fab := Fabric_removeNode g id S T h.fab hns
  smp := Sons.SMP_removeNode g id h.smp
  nr := Parents.NotRoot_of_pruned (pruned_removeNode g id) h.nr

/-- The coherence `share` condition, derived: for the top-down pass from `up`
(a member above step 0 is not a root, by `NotRoot`)… -/
theorem share_parents (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (id : PathNodeId)
    (hz : 0 < id.id.step) (d : PNodeM) (hd : g.node? id = some d) (hS : S id) :
    ∀ v, T id v → v ∈ unionOwnersOf g d.parents := by
  intro v hv
  have hdid : d.id = id := node?_id_eq g id d hd
  have hroot : id.parent_id ≠ none := by
    have := h.nr d (List.mem_of_find?_eq_some hd) (by rw [hdid]; exact hz)
    rw [hdid] at this; exact this
  obtain ⟨c, hc, h1, h2⟩ := h.fab.up id d hd hS hroot v hv
  have hSc := h.fab.inS id c hS h1
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.fab.node c hSc)
  exact mem_unionOwnersOf g d.parents c m v hc hm (h.fab.sub c m hm hSc v h2)

/-- …and for the bottom-up pass from `down`, turned round by `Sons.SMP`. -/
theorem share_sons (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (id : PathNodeId)
    (hl : id.id.step ≠ g.current_step - 1) (d : PNodeM) (hd : g.node? id = some d)
    (hS : S id) : ∀ v, T id v → v ∈ unionOwnersOf g d.sons := by
  intro v hv
  have hdid : d.id = id := node?_id_eq g id d hd
  obtain ⟨c, m, hm, hpm, h1, h2⟩ := h.fab.down id hS hl v hv
  have hSc := h.fab.inS id c hS h1
  have hmid : m.id = c := node?_id_eq g c m hm
  have hcs : c ∈ d.sons := by
    have := h.smp m (List.mem_of_find?_eq_some hm) id hpm d (List.mem_of_find?_eq_some hd) hdid
    rw [hmid] at this; exact this
  exact mem_unionOwnersOf g d.sons c m v hcs hm (h.fab.sub c m hm hSc v h2)

-- ============================================================
-- The original review loop
-- ============================================================

theorem FOk_cleanInvalidGo (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop) :
    ∀ (ids : List PathNodeId) (g : GPathM), FOk g S T → FOk (cleanInvalidGo g ids) S T := by
  intro ids
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGo]
    split
    · exact ih g h
    · next d₀ hd =>
      have hb : S id → ∀ v, T id v → v ∈ g.gowners :=
        fun hS v hv => h.fab.gow v (h.fab.inS id v hS hv)
      have h₂ := FOk_unlink _ id S T (FOk_updateAt g id S T g.gowners hb h)
      have hstep₂ : (unlinkIncompatible (updateAt g id (fow g.gowners)) id).current_step
          = g.current_step := by rw [unlinkIncompatible_current]; rfl
      split
      · exact ih _ h₂
      · next hbad =>
        refine ih _ (FOk_removeNode _ id S T h₂ ?_)
        intro hSid
        exact hbad (isValidNode_of_Fabric g S T h.fab h.smp g.gowners id (hb hSid)
          d₀ hd hSid _ hstep₂)

theorem FOk_reviewNode (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (nb : PNodeM → List PathNodeId)
    (h : FOk g S T) (id : PathNodeId)
    (hsh : ∀ d, g.node? id = some d → S id → ∀ v, T id v → v ∈ unionOwnersOf g (nb d)) :
    FOk (reviewNode g nb id) S T := by
  unfold reviewNode
  cases hd : g.node? id with
  | none => exact h
  | some d =>
    simp only
    split
    · have hb : S id → ∀ v, T id v → v ∈ unionOwnersOf g (nb d) := fun hS => hsh d hd hS
      have h₂ := FOk_unlink _ id S T (FOk_updateAt g id S T _ hb h)
      split
      · exact h₂
      · next hbad =>
        refine FOk_removeNode _ id S T h₂ ?_
        intro hSid
        exact hbad (isValidNode_of_Fabric g S T h.fab h.smp _ id (hb hSid) d hd hSid _
          (by rw [unlinkIncompatible_current]; rfl))
    · next hbad =>
      refine FOk_removeNode g id S T h ?_
      intro hSid
      exact hbad (isValidNode_of_Fabric_self g S T h.fab h.smp id d hd hSid)

theorem FOk_reviewLine_parents (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (k : Int) (hk : 0 < k) :
    FOk (reviewLine g (·.parents) k) S T := by
  have main : ∀ (ids : List PathNodeId), (∀ id ∈ ids, 0 < id.id.step) →
      ∀ h' : GPathM, FOk h' S T →
        FOk (ids.foldl (fun h'' i => reviewNode h'' (·.parents) i) h') S T := by
    intro ids
    induction ids with
    | nil => intro _ h' hw; exact hw
    | cons x xs ih =>
      intro hx h' hw
      simp only [List.foldl_cons]
      exact ih (fun i hi => hx i (List.mem_cons_of_mem _ hi)) _
        (FOk_reviewNode h' S T _ hw x (fun d hd hS =>
          share_parents h' S T hw x (hx x List.mem_cons_self) d hd hS))
  exact main _ (fun id hid => by rw [Survive.step_of_mem_line g k id hid]; exact hk) g h

theorem FOk_reviewLine_sons (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (cs : Int) (hcs : g.current_step = cs)
    (h : FOk g S T) (k : Int) (hk : k ≠ cs - 1) :
    FOk (reviewLine g (·.sons) k) S T ∧ (reviewLine g (·.sons) k).current_step = cs := by
  have main : ∀ (ids : List PathNodeId), (∀ id ∈ ids, id.id.step ≠ cs - 1) →
      ∀ h' : GPathM, h'.current_step = cs → FOk h' S T →
        FOk (ids.foldl (fun h'' i => reviewNode h'' (·.sons) i) h') S T ∧
        (ids.foldl (fun h'' i => reviewNode h'' (·.sons) i) h').current_step = cs := by
    intro ids
    induction ids with
    | nil => intro _ h' hc hw; exact ⟨hw, hc⟩
    | cons x xs ih =>
      intro hx h' hc hw
      simp only [List.foldl_cons]
      refine ih (fun i hi => hx i (List.mem_cons_of_mem _ hi)) _ ?_
        (FOk_reviewNode h' S T _ hw x (fun d hd hS =>
          share_sons h' S T hw x (by rw [hc]; exact hx x List.mem_cons_self) d hd hS))
      rw [(pruned_reviewNode _ x h').step_eq]; exact hc
  exact main _ (fun id hid => by rw [Survive.step_of_mem_line g k id hid]; exact hk) g hcs h

theorem FOk_reviewSteps_parents (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop) :
    ∀ (ks : List Int), (∀ k ∈ ks, 0 < k) → ∀ g : GPathM, FOk g S T →
      FOk (reviewSteps g (·.parents) ks) S T := by
  intro ks
  induction ks with
  | nil => intro _ g h; exact h
  | cons k rest ih =>
    intro hk g h
    simp only [reviewSteps]
    split
    · exact ih (fun j hj => hk j (List.mem_cons_of_mem _ hj)) _
        (FOk_reviewLine_parents g S T h k (hk k List.mem_cons_self))
    · exact h

theorem FOk_reviewSteps_sons (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop)
    (cs : Int) :
    ∀ (ks : List Int), (∀ k ∈ ks, k ≠ cs - 1) → ∀ g : GPathM, g.current_step = cs →
      FOk g S T →
      FOk (reviewSteps g (·.sons) ks) S T ∧ (reviewSteps g (·.sons) ks).current_step = cs := by
  intro ks
  induction ks with
  | nil => intro _ g hc h; exact ⟨h, hc⟩
  | cons k rest ih =>
    intro hk g hc h
    simp only [reviewSteps]
    split
    · obtain ⟨hw', hc'⟩ := FOk_reviewLine_sons g S T cs hc h k (hk k List.mem_cons_self)
      exact ih (fun j hj => hk j (List.mem_cons_of_mem _ hj)) _ hc' hw'
    · exact ⟨h, hc⟩

theorem FOk_reviewPass (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) : FOk (reviewPass g) S T := by
  simp only [reviewPass]
  have h1 : FOk (cleanInvalid g) S T := FOk_cleanInvalidGo S T _ g h
  have h2 : FOk (reviewParents (cleanInvalid g)) S T :=
    FOk_reviewSteps_parents S T _ (fun _ hk => (PickInduction.intRange_bounds hk).1) _ h1
  exact (FOk_reviewSteps_sons S T _ _
    (fun k hk => by
      have := (PickInduction.intRange_bounds (List.mem_reverse.mp hk)).2
      omega) _ rfl h2).1

theorem FOk_reviewFuel (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop) :
    ∀ (fuel : Nat) (g : GPathM), FOk g S T → FOk (reviewFuel fuel g) S T := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewFuel]
    split
    · split
      · exact ih _ (FOk_reviewPass g S T h)
      · exact FOk_reviewPass g S T h
    · exact h

/-- **A fabric survives the whole review loop.** -/
theorem FOk_review (g : GPathM) (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop)
    (h : FOk g S T) : FOk (review g) S T :=
  FOk_reviewFuel S T _ g h

theorem FOk_filterRequire (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (req : NodeId)
    (hpin : ∀ p, S p → p.id.step = req.step → p.id = req) :
    FOk (filterRequire g req) S T where
  fab :=
    { gow := by
        intro p hp
        refine List.mem_filter.mpr ⟨h.fab.gow p hp, ?_⟩
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
        if hs : p.id.step = req.step then exact Or.inr (hpin p hp hs)
        else exact Or.inl hs
      node := h.fab.node
      inS := h.fab.inS
      symm := h.fab.symm
      self := h.fab.self
      sub := h.fab.sub
      support := h.fab.support
      up := h.fab.up
      down := h.fab.down }
  smp := Sons.SMP_filterRequire g req h.smp
  nr := Parents.NotRoot_of_pruned (pruned_filterRequire g req) h.nr

theorem FOk_filterAll (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r) :
    FOk (filterAll g reqs) S T := by
  unfold filterAll
  refine FOk_review _ S T ?_
  have main : ∀ (l : List NodeId), (∀ r ∈ l, ∀ p, S p → p.id.step = r.step → p.id = r) →
      ∀ h' : GPathM, FOk h' S T → FOk (l.foldl filterRequire h') S T := by
    intro l
    induction l with
    | nil => intro _ h' hw; exact hw
    | cons x xs ih =>
      intro hx h' hw
      simp only [List.foldl_cons]
      exact ih (fun r hr => hx r (List.mem_cons_of_mem _ hr)) _
        (FOk_filterRequire h' S T hw x (hx x List.mem_cons_self))
  exact main reqs hpin g h

/-- **`Survive.isValid_filterAll_of_Woven`, generalised.** A non-empty fabric
the pin does not contradict keeps the pin valid, review loop and all. -/
theorem isValid_filterAll_of_Fabric (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r) (hne : ∃ p, S p) :
    isValid (filterAll g reqs) = true :=
  isValid_of_Fabric _ S T (FOk_filterAll g S T h reqs hpin).fab hne

/-- info: 'AbsSat.GraphPath.Model.Fabric.isValid_filterAll_of_Fabric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_filterAll_of_Fabric


-- ============================================================
-- The symmetric review loop, and the reader's step
-- ============================================================

theorem FOk_cleanInvalidGoSym (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop) :
    ∀ (ids : List PathNodeId) (g : GPathM), FOk g S T → FOk (cleanInvalidGoSym g ids) S T := by
  intro ids
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGoSym]
    split
    · exact ih g h
    · next d₀ hd =>
      have hb : S id → ∀ v, T id v → v ∈ g.gowners :=
        fun hS v hv => h.fab.gow v (h.fab.inS id v hS hv)
      have h₂ := FOk_unlink _ id S T
        (FOk_symmetrize _ id S T (FOk_updateAt g id S T g.gowners hb h))
      have hstep₂ : (unlinkIncompatible (symmetrize (updateAt g id (fow g.gowners)) id)
          id).current_step = g.current_step := by
        rw [unlinkIncompatible_current, symmetrize_current]; rfl
      split
      · exact ih _ h₂
      · next hbad =>
        refine ih _ (FOk_removeNode _ id S T h₂ ?_)
        intro hSid
        exact hbad (isValidNode_of_Fabric g S T h.fab h.smp g.gowners id (hb hSid)
          d₀ hd hSid _ hstep₂)

theorem FOk_reviewNodeSym (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (nb : PNodeM → List PathNodeId)
    (h : FOk g S T) (id : PathNodeId)
    (hsh : ∀ d, g.node? id = some d → S id → ∀ v, T id v → v ∈ unionOwnersOf g (nb d)) :
    FOk (reviewNodeSym g nb id) S T := by
  unfold reviewNodeSym
  cases hd : g.node? id with
  | none => exact h
  | some d =>
    simp only
    split
    · have hb : S id → ∀ v, T id v → v ∈ unionOwnersOf g (nb d) := fun hS => hsh d hd hS
      have h₂ := FOk_unlink _ id S T (FOk_symmetrize _ id S T (FOk_updateAt g id S T _ hb h))
      split
      · exact h₂
      · next hbad =>
        refine FOk_removeNode _ id S T h₂ ?_
        intro hSid
        exact hbad (isValidNode_of_Fabric g S T h.fab h.smp _ id (hb hSid) d hd hSid _
          (by rw [unlinkIncompatible_current, symmetrize_current]; rfl))
    · next hbad =>
      refine FOk_removeNode g id S T h ?_
      intro hSid
      exact hbad (isValidNode_of_Fabric_self g S T h.fab h.smp id d hd hSid)

theorem FOk_reviewLineSym_parents (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (k : Int) (hk : 0 < k) :
    FOk (reviewLineSym g (·.parents) k) S T := by
  have main : ∀ (ids : List PathNodeId), (∀ id ∈ ids, 0 < id.id.step) →
      ∀ h' : GPathM, FOk h' S T →
        FOk (ids.foldl (fun h'' i => reviewNodeSym h'' (·.parents) i) h') S T := by
    intro ids
    induction ids with
    | nil => intro _ h' hw; exact hw
    | cons x xs ih =>
      intro hx h' hw
      simp only [List.foldl_cons]
      exact ih (fun i hi => hx i (List.mem_cons_of_mem _ hi)) _
        (FOk_reviewNodeSym h' S T _ hw x (fun d hd hS =>
          share_parents h' S T hw x (hx x List.mem_cons_self) d hd hS))
  exact main _ (fun id hid => by rw [Survive.step_of_mem_line g k id hid]; exact hk) g h

theorem FOk_reviewLineSym_sons (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (cs : Int) (hcs : g.current_step = cs)
    (h : FOk g S T) (k : Int) (hk : k ≠ cs - 1) :
    FOk (reviewLineSym g (·.sons) k) S T ∧ (reviewLineSym g (·.sons) k).current_step = cs := by
  have main : ∀ (ids : List PathNodeId), (∀ id ∈ ids, id.id.step ≠ cs - 1) →
      ∀ h' : GPathM, h'.current_step = cs → FOk h' S T →
        FOk (ids.foldl (fun h'' i => reviewNodeSym h'' (·.sons) i) h') S T ∧
        (ids.foldl (fun h'' i => reviewNodeSym h'' (·.sons) i) h').current_step = cs := by
    intro ids
    induction ids with
    | nil => intro _ h' hc hw; exact ⟨hw, hc⟩
    | cons x xs ih =>
      intro hx h' hc hw
      simp only [List.foldl_cons]
      refine ih (fun i hi => hx i (List.mem_cons_of_mem _ hi)) _ ?_
        (FOk_reviewNodeSym h' S T _ hw x (fun d hd hS =>
          share_sons h' S T hw x (by rw [hc]; exact hx x List.mem_cons_self) d hd hS))
      rw [reviewNodeSym_current_step]; exact hc
  exact main _ (fun id hid => by rw [Survive.step_of_mem_line g k id hid]; exact hk) g hcs h

theorem FOk_reviewStepsSym_parents (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) :
    ∀ (ks : List Int), (∀ k ∈ ks, 0 < k) → ∀ g : GPathM, FOk g S T →
      FOk (reviewStepsSym g (·.parents) ks) S T := by
  intro ks
  induction ks with
  | nil => intro _ g h; exact h
  | cons k rest ih =>
    intro hk g h
    simp only [reviewStepsSym]
    split
    · exact ih (fun j hj => hk j (List.mem_cons_of_mem _ hj)) _
        (FOk_reviewLineSym_parents g S T h k (hk k List.mem_cons_self))
    · exact h

theorem FOk_reviewStepsSym_sons (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop)
    (cs : Int) :
    ∀ (ks : List Int), (∀ k ∈ ks, k ≠ cs - 1) → ∀ g : GPathM, g.current_step = cs →
      FOk g S T →
      FOk (reviewStepsSym g (·.sons) ks) S T ∧
        (reviewStepsSym g (·.sons) ks).current_step = cs := by
  intro ks
  induction ks with
  | nil => intro _ g hc h; exact ⟨h, hc⟩
  | cons k rest ih =>
    intro hk g hc h
    simp only [reviewStepsSym]
    split
    · obtain ⟨hw', hc'⟩ := FOk_reviewLineSym_sons g S T cs hc h k (hk k List.mem_cons_self)
      exact ih (fun j hj => hk j (List.mem_cons_of_mem _ hj)) _ hc' hw'
    · exact ⟨h, hc⟩

theorem FOk_reviewPassSym (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) : FOk (reviewPassSym g) S T := by
  simp only [reviewPassSym]
  have h1 : FOk (cleanInvalidSym g) S T := FOk_cleanInvalidGoSym S T _ g h
  have h2 : FOk (reviewParentsSym (cleanInvalidSym g)) S T :=
    FOk_reviewStepsSym_parents S T _ (fun _ hk => (PickInduction.intRange_bounds hk).1) _ h1
  exact (FOk_reviewStepsSym_sons S T _ _
    (fun k hk => by
      have := (PickInduction.intRange_bounds (List.mem_reverse.mp hk)).2
      omega) _ rfl h2).1

theorem FOk_reviewFuelSym (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop) :
    ∀ (fuel : Nat) (g : GPathM), FOk g S T → FOk (reviewFuelSym fuel g) S T := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewFuelSym]
    split
    · split
      · exact ih _ (FOk_reviewPassSym g S T h)
      · exact FOk_reviewPassSym g S T h
    · exact h

/-- **A fabric survives the symmetric review loop.** -/
theorem FOk_reviewSym (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) : FOk (reviewSym g) S T :=
  FOk_reviewFuelSym S T _ g h

/-- The owners-pin keeps a fabric whose members `r` owns. -/
theorem FOk_pinOwners (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (r : PathNodeId) (rn : PNodeM)
    (hr : g.node? r = some rn) (hin : ∀ p, S p → p ∈ rn.owners) :
    FOk (pinOwners g r) S T := by
  have hpin : pinOwners g r
      = { g with gowners := g.gowners.filter (fun q => rn.owners.contains q) } := by
    simp only [pinOwners, hr]
  rw [hpin]
  exact
    { fab :=
        { gow := fun p hp =>
            List.mem_filter.mpr ⟨h.fab.gow p hp, List.elem_eq_true_of_mem (hin p hp)⟩
          node := h.fab.node
          inS := h.fab.inS
          symm := h.fab.symm
          self := h.fab.self
          sub := h.fab.sub
          support := h.fab.support
          up := h.fab.up
          down := h.fab.down }
      smp := h.smp
      nr := h.nr }

/-- **The reader's step survives a fabric inside the chosen node's owners.**
If `owners(r)` contains a non-empty fabric, choosing `r` — pin by owners, clean
symmetrically — leaves the graph valid, and every member of the fabric still
alive. -/
theorem FOk_readStepSym (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (r : PathNodeId) (rn : PNodeM)
    (hr : g.node? r = some rn) (hin : ∀ p, S p → p ∈ rn.owners) :
    FOk (readStepSym g r) S T :=
  FOk_reviewSym _ S T (FOk_pinOwners g S T h r rn hr hin)

theorem isValid_readStepSym_of_Fabric (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : FOk g S T) (r : PathNodeId) (rn : PNodeM)
    (hr : g.node? r = some rn) (hin : ∀ p, S p → p ∈ rn.owners) (hne : ∃ p, S p) :
    isValid (readStepSym g r) = true :=
  isValid_of_Fabric _ S T (FOk_readStepSym g S T h r rn hr hin).fab hne

/-- info: 'AbsSat.GraphPath.Model.Fabric.isValid_readStepSym_of_Fabric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_readStepSym_of_Fabric

-- ============================================================
-- `Woven` is the special case
-- ============================================================

/-- **`Fabric` generalises `Woven`.** A woven set is the fabric whose every
member keeps the whole set as its table. -/
theorem Fabric_of_Woven (g : GPathM) (S : PathNodeId → Prop) (hw : Survive.Woven g S) :
    Fabric g S (fun _ v => S v) where
  gow := hw.closed.gow
  node := hw.closed.node
  inS := fun _ _ _ hv => hv
  symm := fun _ _ hp _ => hp
  self := fun _ hp => hp
  sub := fun p n hn hp v hv => hw.own p n hp hn v hv
  support := by
    intro p hp l hlo hhi
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hw.closed.node p hp)
    obtain ⟨v, _, hSv, hvs⟩ := hw.closed.support p n hn hp l hlo hhi
    exact ⟨v, hSv, hvs⟩
  up := by
    intro p n hn hp hroot v hv
    obtain ⟨c, hc, hSc⟩ := hw.closed.parent p n hn hp hroot
    exact ⟨c, hc, hSc, hv⟩
  down := by
    intro p hp hlast v hv
    obtain ⟨c, m, hSc, hm, hpm⟩ := hw.closed.son p hp hlast
    exact ⟨c, m, hm, hpm, hSc, hv⟩

theorem FOk_of_WOk (g : GPathM) (S : PathNodeId → Prop) (h : Survive.WOk g S) :
    FOk g S (fun _ v => S v) :=
  ⟨Fabric_of_Woven g S h.wov, h.smp, h.nr⟩

/-- info: 'AbsSat.GraphPath.Model.Fabric.Fabric_of_Woven' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_of_Woven


-- ============================================================
-- The wall, restated as a static property
-- ============================================================

/-- **A fabric under `r`**: a fabric inside `owners(r)` that contains `r`. -/
def FabricAt (g : GPathM) (r : PathNodeId) : Prop :=
  ∃ rn S T, g.node? r = some rn ∧ FOk g S T ∧ S r ∧ ∀ p, S p → p ∈ rn.owners

/-- **Choosing a node with a fabric under it never gets the reader stuck**, and
keeps every member of that fabric alive.

This turns the reader's wall from a question about the *dynamics* of the review
— does cleaning after a choice kill anything? — into a *static* property of the
state the choice is made in: does `owners(r)` contain a fabric? `lake exe
cnfmap --fabric` computes the greatest one and finds it is **all of
`owners(r)`** at every choice measured (4,888 choices, 159,621 nodes), after
trimming 0.35 % of the table entries. -/
theorem isValid_readStepSym_of_FabricAt (g : GPathM) (r : PathNodeId) (h : FabricAt g r) :
    isValid (readStepSym g r) = true := by
  obtain ⟨rn, S, T, hr, hok, hSr, hin⟩ := h
  exact isValid_readStepSym_of_Fabric g S T hok r rn hr hin ⟨r, hSr⟩

theorem alive_readStepSym_of_FabricAt (g : GPathM) (r : PathNodeId) (rn : PNodeM)
    (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop)
    (hr : g.node? r = some rn) (hok : FOk g S T) (hin : ∀ p, S p → p ∈ rn.owners) :
    ∀ p, S p → ((readStepSym g r).node? p).isSome = true :=
  (FOk_readStepSym g S T hok r rn hr hin).fab.node

/-- info: 'AbsSat.GraphPath.Model.Fabric.isValid_readStepSym_of_FabricAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_readStepSym_of_FabricAt


-- ============================================================
-- The author's definition of owners, and what it gives
-- ============================================================

/-!
The author's definition: the graph's global owners contain every node while
the graph is valid, and a node's owners are **the nodes compatible with it**.
Read "compatible" as *lying on a common solution* — a sound chain through
both — and the definition is a statement we can state and use.

The first thing it gives is a fabric. Every sound chain is one (its nodes, each
keeping the chain as its table); and the union of all the chains through `r`
is one too, with `T x v` meaning *some solution through `r` passes `x` and `v`*.
-/

/-- `sel` passes through `x`. -/
def Passes (g : GPathM) (sel : Int → PathNodeId) (x : PathNodeId) : Prop :=
  ∃ k, 0 ≤ k ∧ k < g.current_step ∧ sel k = x

/-- The **solution fabric of `r`**: members are the nodes on some solution
through `r`, and `v` is in `x`'s table when one such solution passes both. -/
def SolS (g : GPathM) (r : PathNodeId) : PathNodeId → Prop :=
  fun x => ∃ sel, ChainSound g sel ∧ Passes g sel r ∧ Passes g sel x

def SolT (g : GPathM) (r : PathNodeId) : PathNodeId → PathNodeId → Prop :=
  fun x v => ∃ sel, ChainSound g sel ∧ Passes g sel r ∧ Passes g sel x ∧ Passes g sel v

/-- A chain node owns every chain node. -/
theorem chain_owns (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (i j : Int) (hi : 0 ≤ i) (hi' : i < g.current_step) (hj : 0 ≤ j) (hj' : j < g.current_step)
    (n : PNodeM) (hn : g.node? (sel i) = some n) : sel j ∈ n.owners := by
  if hij : i = j then
    subst hij
    have hs := h.self_owned i hi hi'
    simp only [ownersOf, hn] at hs
    exact hs
  else
    have hm := h.chain.2.1 j i hj hi hj' hi' (Ne.symm hij)
    simp only [ownersAt, List.mem_filter, ownersOf, hn] at hm
    exact hm.1

theorem Fabric_sol (g : GPathM) (r : PathNodeId) : Fabric g (SolS g r) (SolT g r) where
  gow := by
    rintro x ⟨sel, h, _, k, hk0, hk1, rfl⟩
    exact h.chain.2.2 k hk0 hk1
  node := by
    rintro x ⟨sel, h, _, k, hk0, hk1, rfl⟩
    exact (h.chain.1.1 k hk0 hk1).1
  inS := by
    rintro x v _ ⟨sel, h, hr, _, hv⟩
    exact ⟨sel, h, hr, hv⟩
  symm := by
    rintro x v _ ⟨sel, h, hr, hx, hv⟩
    exact ⟨sel, h, hr, hv, hx⟩
  self := by
    rintro x ⟨sel, h, hr, hx⟩
    exact ⟨sel, h, hr, hx, hx⟩
  sub := by
    rintro x n hn _ v ⟨sel, h, _, ⟨i, hi, hi', rfl⟩, ⟨j, hj, hj', rfl⟩⟩
    exact chain_owns g sel h i j hi hi' hj hj' n hn
  support := by
    rintro x ⟨sel, h, hr, hx⟩ l hlo hhi
    exact ⟨sel l, ⟨sel, h, hr, hx, ⟨l, hlo, hhi, rfl⟩⟩, (h.chain.1.1 l hlo hhi).2⟩
  up := by
    rintro x n hn _ hroot v ⟨sel, h, hr, ⟨i, hi, hi', rfl⟩, hv⟩
    have hipos : 0 < i := by
      rcases Int.lt_or_eq_of_le hi with hlt | heq
      · exact hlt
      · exfalso; subst heq; exact hroot h.root_shape.1
    have hlink := h.chain.1.2 (i - 1) (by omega) (by omega)
    rw [show i - 1 + 1 = i from by omega, hn] at hlink
    simp only [Option.map_some, Option.getD_some] at hlink
    exact ⟨sel (i - 1), hlink, ⟨sel, h, hr, ⟨i, hi, hi', rfl⟩, ⟨i - 1, by omega, by omega, rfl⟩⟩,
      ⟨sel, h, hr, ⟨i - 1, by omega, by omega, rfl⟩, hv⟩⟩
  down := by
    rintro x ⟨sel, h, hr, ⟨i, hi, hi', rfl⟩⟩ hlast v ⟨sel', h', hr', ⟨i', hi0', hi1', hsel'⟩, hv'⟩
    -- work on the chain `sel'` that carries `v`
    have hstep : (sel' i').id.step = i' := (h'.chain.1.1 i' hi0' hi1').2
    have hstep0 : (sel i).id.step = i := (h.chain.1.1 i hi hi').2
    have hii : i' = i := by rw [← hstep, hsel', hstep0]
    subst hii
    have hlt : i' + 1 < g.current_step := by
      have : i' ≠ g.current_step - 1 := by rw [← hstep0]; exact hlast
      omega
    obtain ⟨hs, _⟩ := h'.chain.1.1 (i' + 1) (by omega) hlt
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    have hlink := h'.chain.1.2 i' hi0' hlt
    rw [hm] at hlink
    simp only [Option.map_some, Option.getD_some] at hlink
    refine ⟨sel' (i' + 1), m, hm, hsel' ▸ hlink, ?_, ?_⟩
    · exact ⟨sel', h', hr', ⟨i', hi0', hi1', hsel'⟩, ⟨i' + 1, by omega, hlt, rfl⟩⟩
    · exact ⟨sel', h', hr', ⟨i' + 1, by omega, hlt, rfl⟩, hv'⟩

/-- **A node on a solution has a fabric under it.** So the reader's step is safe
at any node on a solution — the fabric form of `isValid_pin_of_chain`, for the
owners-pin and the symmetric review. -/
theorem FabricAt_of_chain (g : GPathM) (hsmp : Sons.SMP g) (hnr : Parents.NotRoot g)
    (r : PathNodeId) (sel : Int → PathNodeId) (h : ChainSound g sel) (hr : Passes g sel r) :
    FabricAt g r := by
  obtain ⟨k, hk0, hk1, rfl⟩ := hr
  obtain ⟨rn, hrn⟩ := Option.isSome_iff_exists.mp (h.chain.1.1 k hk0 hk1).1
  refine ⟨rn, SolS g (sel k), SolT g (sel k), hrn, ⟨Fabric_sol g (sel k), hsmp, hnr⟩,
    ⟨sel, h, ⟨k, hk0, hk1, rfl⟩, ⟨k, hk0, hk1, rfl⟩⟩, ?_⟩
  rintro p ⟨sel', h', ⟨i, hi, hi', hsi⟩, ⟨j, hj, hj', rfl⟩⟩
  rw [← hsi] at hrn
  exact chain_owns g sel' h' i j hi hi' hj hj' rn hrn

/-- **The author's definition of owners**, for one node: every node among `r`'s
owners lies on a common solution with `r`. -/
def OwnersExactAt (g : GPathM) (r : PathNodeId) : Prop :=
  ∀ rn, g.node? r = some rn → ∀ p, (g.node? p).isSome = true → p ∈ rn.owners →
    ∃ sel, ChainSound g sel ∧ Passes g sel r ∧ Passes g sel p

/-- **Under the author's definition, choosing `r` kills none of its owners.**
Every node among `owners(r)` is a member of the solution fabric of `r`, and a
fabric survives the reading step. This is `--pinexact`'s measurement, derived. -/
theorem alive_readStepSym_of_OwnersExactAt (g : GPathM) (hsmp : Sons.SMP g)
    (hnr : Parents.NotRoot g) (r : PathNodeId) (rn : PNodeM) (hrn : g.node? r = some rn)
    (hex : OwnersExactAt g r) :
    ∀ p, (g.node? p).isSome = true → p ∈ rn.owners →
      ((readStepSym g r).node? p).isSome = true := by
  intro p hp hpr
  have hin : ∀ x, SolS g r x → x ∈ rn.owners := by
    rintro x ⟨sel, h, ⟨i, hi, hi', hsi⟩, ⟨j, hj, hj', rfl⟩⟩
    subst hsi
    exact chain_owns g sel h i j hi hi' hj hj' rn hrn
  exact alive_readStepSym_of_FabricAt g r rn (SolS g r) (SolT g r) hrn
    ⟨Fabric_sol g r, hsmp, hnr⟩ hin p (hex rn hrn p hp hpr)

/-- info: 'AbsSat.GraphPath.Model.Fabric.alive_readStepSym_of_OwnersExactAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms alive_readStepSym_of_OwnersExactAt

end AbsSat.GraphPath.Model.Fabric
