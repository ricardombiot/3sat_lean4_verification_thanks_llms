-- lean_project/AbsSat/GraphPath/Model/Review.lean
import AbsSat.GraphPath.Model.L6Up

/-!
The last open statement of the bridge:

    SupportedG g → SupportedG (review g)      (with InhabitedG alongside)

which is simultaneously L6's remaining case, L2's ⊇ direction and L3's ⊇
direction. **It is not proved here.** What this module does is identify and
formalise the *mechanism* — why a review pass cannot cut a chain — and prove
the two local facts that mechanism rests on.

## The mechanism

A review pass can hurt a chain in exactly two ways: it prunes owners
(`intersectOwners`), and it physically drops nodes that stop passing
`isValidNode`. A chain is protected against both, for two different reasons:

* **Against global pruning.** `cleanInvalid` intersects every node's owners
  against `gowners`. An owner that is *itself* a global owner always survives
  that intersection (`mem_intersectOwners_of_mem`). This is precisely why
  `ChainG` carries its `gowners` condition — the condition was not
  bookkeeping, it is the thing that stops the global filter from cutting the
  chain.

* **Against being dropped.** `isValidNode` asks for owners covering every step,
  plus parents and sons in the non-boundary cases. A chain supplies all three:
  its own nodes sit inside the node's owners and cover every step
  (`owners_ok_of_chain`), the predecessor is a parent, the successor is a son.
  Hence `isValidNode_of_chain`: **a node a sound chain runs through never fails
  validity**, so no pass can ever remove it.

The step ranges are not arbitrary either: `reviewParents` walks `1 .. cs-1` and
`reviewSons` walks `1 .. cs-2`, which is exactly what keeps the boundary nodes
— the one with no parent and the one with no son — out of the passes that
would otherwise reject them.

## Why `ChainSound` and not `ChainG`

`ChainG` is not enough, because `isValidNode` looks at parents, sons and the
root flag, not only at owners. `ChainSound` adds the three facts that closes
that gap: each chain node owns itself, the son link mirrors the parent link,
and only the step-0 node is a root. All three are established by `addNode`
(the new id is appended to *every* node's owners including its own; parents
gain the new node as a son; step-0 nodes come from seeds, whose `map_parent`
is `none`).

## What is still missing

1. ~~The induction over `cleanInvalidGo`'s walk.~~ **Done** in
   `CleanInvalid.lean` (`ChainSound_cleanInvalid`): the first of the three
   stages of a pass preserves a sound chain.
2. For the coherence passes: `sel i ∈ unionOwnersOf g (parents of sel j)`.
   The argument is worked out but not formalised — it follows from pairwise
   ownership of `i` and `j-1` when `i ≠ j-1`, and from self-ownership when
   `i = j-1`, using that `sel (j-1)` is a parent of `sel j`.
3. That `ChainSound`'s own extra fields survive a pass.

None of these is the Helly problem the bridge document feared; they are
bookkeeping over a mutating fold. Whether that means L6 is true at this level
of generality — the falsifier has not broken it over 1,680 states with
arbitrary requirements — is still open.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

def sonsOf (g : GPathM) (pid : PathNodeId) : List PathNodeId :=
  match g.node? pid with
  | some n => n.sons
  | none => []

def parentsOf (g : GPathM) (pid : PathNodeId) : List PathNodeId :=
  match g.node? pid with
  | some n => n.parents
  | none => []

/-- Everything a chain needs in order to survive a review pass.

`ChainG` alone is not enough: the pass prunes owners and physically drops
nodes that stop passing `isValidNode`, and that test looks at parents, sons
and the root flag, not only at owners. -/
structure ChainSound (g : GPathM) (sel : Int → PathNodeId) : Prop where
  chain : ChainG g sel
  /-- Each chain node owns itself. `addNode` establishes this — the new id is
  appended to *every* node's owners including its own. -/
  self_owned : ∀ k, 0 ≤ k → k < g.current_step → sel k ∈ ownersOf g (sel k)
  /-- The parent link of `IsChain`, seen from the other side. -/
  son_link : ∀ k, 0 ≤ k → k + 1 < g.current_step → sel (k + 1) ∈ sonsOf g (sel k)
  /-- Only the step-0 node is a root. Needed to pick the right branch of
  `isValidNode`: a non-root node is required to have parents, and the step-0
  node has none. -/
  root_shape : (sel 0).parent_id = none ∧
    ∀ k, 0 < k → k < g.current_step → (sel k).parent_id ≠ none

-- ============================================================
-- Why `ChainG` carries the gowners condition
-- ============================================================

/-- An owner that is also a *global* owner always survives the `cleanInvalid`
intersection. This single fact is the reason `ChainG` tracks `gowners`: it is
what stops the global pruning from cutting a chain. -/
theorem mem_intersectOwners_of_mem (a b : List PathNodeId) (q : PathNodeId)
    (hq : q ∈ a) (hb : q ∈ b) : q ∈ intersectOwners a b := by
  simp only [intersectOwners, List.mem_filter]
  refine ⟨hq, ?_⟩
  simp only [Bool.or_eq_true]
  exact Or.inr (List.elem_eq_true_of_mem hb)

/-- The same for the coherence passes: an owner that also belongs to the
neighbours' union survives. -/
theorem mem_intersectOwners_of_mem_union (a : List PathNodeId) (g : GPathM)
    (ids : List PathNodeId) (q : PathNodeId)
    (hq : q ∈ a) (hb : q ∈ unionOwnersOf g ids) :
    q ∈ intersectOwners a (unionOwnersOf g ids) :=
  mem_intersectOwners_of_mem a _ q hq hb

-- ============================================================
-- A sound chain node always passes `isValidNode`
-- ============================================================

theorem beq_eq_false_of_ne (a b : Int) (hne : a ≠ b) : (a == b) = false := by
  cases hb : (a == b) with
  | false => rfl
  | true => exact absurd (eq_of_beq hb) hne

theorem not_isEmpty_of_ne_nil {α : Type} (l : List α) (h : l ≠ []) :
    (!l.isEmpty) = true := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem hasStepEntry_of_mem (l : List PathNodeId) (q : PathNodeId) (k : Int)
    (hq : q ∈ l) (hs : q.id.step = k) : hasStepEntry l k = true := by
  simp only [hasStepEntry, List.any_eq_true]
  exact ⟨q, hq, by rw [hs]; exact beq_iff_eq.mpr rfl⟩

theorem mem_intRange_lower {lo hi k : Int} (h : k ∈ intRange lo hi) : lo ≤ k := by
  simp only [intRange] at h
  obtain ⟨i, _, hEq⟩ := List.mem_map.mp h
  have hEq' : lo + (i : Int) = k := hEq
  omega

theorem mem_intRange_upper {lo hi k : Int} (h : k ∈ intRange lo hi) : k ≤ hi := by
  simp only [intRange] at h
  obtain ⟨i, hi', hEq⟩ := List.mem_map.mp h
  have hlt : i < (hi - lo + 1).toNat := List.mem_range.mp hi'
  have hEq' : lo + (i : Int) = k := hEq
  omega

/-- **The owners of a sound chain node cover every step below `current_step`,
because the chain itself sits inside them.** This is the `owners_ok` half of
`isValidNode`, and it is why a review pass cannot drop a chain node for lack
of support. -/
theorem owners_ok_of_chain (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (j : Int) (n : PNodeM) (hn : g.node? (sel j) = some n)
    (hj : 0 ≤ j) (hj' : j < g.current_step) :
    (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry n.owners k) = true := by
  obtain ⟨hchain, howned, _⟩ := h.chain
  simp only [List.all_eq_true]
  intro k hk
  have hk0 := mem_intRange_lower hk
  have hk1 := mem_intRange_upper hk
  have hstepk := (hchain.1 k hk0 (by omega)).2
  rcases int_eq_or_ne k j with hkj | hkj
  · subst hkj
    have hself := h.self_owned k hk0 (by omega)
    simp only [ownersOf, hn] at hself
    exact hasStepEntry_of_mem _ (sel k) k hself hstepk
  · have hmem := howned k j hk0 hj (by omega) hj' hkj
    simp only [ownersAt, List.mem_filter, ownersOf, hn] at hmem
    exact hasStepEntry_of_mem _ (sel k) k hmem.1 hstepk

/-- **A sound chain node always passes `isValidNode`.** Owners cover every
step (the chain is inside them); a node above step 0 has the chain's
predecessor as a parent; a node below the top has the chain's successor as a
son; and only the step-0 node is a root. So no review pass can ever drop a
node that a sound chain runs through. -/
theorem isValidNode_of_chain (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (j : Int) (n : PNodeM) (hn : g.node? (sel j) = some n)
    (hj : 0 ≤ j) (hj' : j < g.current_step) : isValidNode g n = true := by
  have hid : n.id = sel j := node?_id_eq g (sel j) n hn
  have hstepj := (h.chain.1.1 j hj hj').2
  have howners := owners_ok_of_chain g sel h j n hn hj hj'
  have hpar : 0 < j → n.parents ≠ [] := by
    intro hpos
    have hlink := h.chain.1.2 (j - 1) (by omega) (by omega)
    rw [show j - 1 + 1 = j from by omega, hn] at hlink
    simp only [Option.map_some, Option.getD_some] at hlink
    exact List.ne_nil_of_mem hlink
  have hson : j < g.current_step - 1 → n.sons ≠ [] := by
    intro hlt
    have hlink := h.son_link j hj (by omega)
    simp only [sonsOf, hn] at hlink
    exact List.ne_nil_of_mem hlink
  have hroot : n.id.parent_id.isNone = (j == 0) := by
    rw [hid]
    rcases int_eq_or_ne j 0 with hj0 | hj0
    · subst hj0
      rw [h.root_shape.1, beq_iff_eq.mpr (rfl : (0:Int) = 0)]
      rfl
    · have hne := h.root_shape.2 j (by omega) hj'
      rw [beq_eq_false_of_ne j 0 hj0]
      cases hp : (sel j).parent_id with
      | none => exact absurd hp hne
      | some _ => rfl
  have hj0_of_root : n.id.parent_id.isNone = true → j = 0 := by
    intro hr; rw [hroot] at hr; exact eq_of_beq hr
  have hjne_of_nonroot : ¬(n.id.parent_id.isNone = true) → j ≠ 0 := by
    intro hr hje; exact hr (by rw [hroot, hje]; exact beq_iff_eq.mpr rfl)
  have hlast : (n.id.id.step == g.current_step - 1) = (j == g.current_step - 1) := by
    rw [hid, hstepj]
  have hnotlast : ¬((j == g.current_step - 1) = true) → j < g.current_step - 1 := by
    intro hl
    have : j ≠ g.current_step - 1 := fun he => hl (by rw [he]; exact beq_iff_eq.mpr rfl)
    omega
  simp only [isValidNode, hlast]
  split
  · next hr =>
    have hje := hj0_of_root hr
    split
    · exact howners
    · next hl =>
      simp only [howners, not_isEmpty_of_ne_nil _ (hson (hnotlast hl)), Bool.and_self]
  · next hr =>
    have hje := hjne_of_nonroot hr
    split
    · simp only [howners, not_isEmpty_of_ne_nil _ (hpar (by omega)), Bool.and_self]
    · next hl =>
      simp only [howners, not_isEmpty_of_ne_nil _ (hpar (by omega)),
        not_isEmpty_of_ne_nil _ (hson (hnotlast hl)), Bool.and_self]

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.isValidNode_of_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValidNode_of_chain

/-- info: 'AbsSat.GraphPath.Model.mem_intersectOwners_of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_intersectOwners_of_mem

end AbsSat.GraphPath.Model
