-- lean/improves_bin/AbsSatBin/GraphPath/Model/CleanTwoPhase.lean
import AbsSatBin.GraphPath.Model.ReaderAgg

/-!
# `cleanInvalid` in two phases (report v181, §6)

The sequential `cleanInvalid` walks the nodes one by one, cutting each table with the global owners
*as they stand at that moment*. It depends on the order, and it leaves ids of nodes removed later
in the tables of nodes processed earlier. The two-phase version (`GPathM.cleanInvalid₂`, the
review's clean since 2026-09-23) separates the two things it does:

1. **Purge, to a fixpoint** (`purgeFuel`): remove every node that *would* be invalid once cut
   against the current global owners, and repeat while something is removed. No table is touched.
2. **One cut** (`cutAll`): cut every surviving node against the final global owners.

What "cut" means (`cutNode`) is what the sequential sweep leaves behind once every node has been
processed: the owners intersected with the global ones, and a link `x — y` kept only when each end
admits the other, both read through `node?`.

The per-invariant lemmas the review needs live next to each `X_reviewPass` (`Pruned`, `Fuel`,
`NodeIds`, `GownersNodes`, `Parents`, `Sons`, `CleanInvalid` for `ChainSound`, `Survive`,
`AnchoredSurvive`, `Fabric`). This module keeps what is proper to the two phases:

* `keeps_cleanInvalid₂`, hence `RCtx_cleanInvalid₂`: the reader's context survives;
* the postconditions: `owners_live_cleanInvalid₂` — no dead ids in the tables — and
  `isValidNode_cleanInvalid₂` — every node valid when the graph is.
-/

namespace AbsSatBin.GraphPath.Model.CleanTwoPhase

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderAgg (Keeps keeps_removeNode keeps_foldl RCtx_of_keeps)
open AbsSatBin.GraphPath.Model.Reader (RCtx)
open AbsSatBin.GraphPath.Model.GownersNodes (HasNode GN hasNode_cutAll)

-- ============================================================
-- The reader's context survives
-- ============================================================

theorem keeps_cutAll (g : GPathM) : Keeps g (cutAll g) := by
  refine ⟨pruned_cutAll g, ?_, ?_, ?_⟩
  · intro h q hq
    exact hasNode_cutAll g q (h q hq)
  · intro h n' hn' p hp
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
    subst hEq
    exact hasNode_cutAll g p (h n hn p (cutNode_parents_sub _ _ n p hp))
  · rw [cutAll, NodeIds.ids_map g (cutNode g.gowners g) (fun _ => rfl)]
    exact List.Sublist.refl _

theorem keeps_purgeStep (g : GPathM) (id : PathNodeId) : Keeps g (purgeStep g id) := by
  unfold purgeStep
  split
  · exact Keeps.refl g
  · split
    · exact Keeps.refl g
    · exact keeps_removeNode g id

theorem keeps_purgeRound (g : GPathM) : Keeps g (purgeRound g) := by
  rw [purgeRound_eq]
  exact keeps_foldl purgeStep keeps_purgeStep _ g

theorem keeps_purgeFuel : ∀ (fuel : Nat) (g : GPathM), Keeps g (purgeFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Keeps.refl g
  | succ n ih =>
    intro g
    simp only [purgeFuel]
    split
    · split
      · exact Keeps.trans (keeps_purgeRound g) (ih _)
      · exact keeps_purgeRound g
    · exact Keeps.refl g

theorem keeps_cleanInvalid₂ (g : GPathM) : Keeps g (cleanInvalid₂ g) :=
  Keeps.trans (keeps_purgeFuel _ g) (keeps_cutAll _)

theorem RCtx_cleanInvalid₂ (g : GPathM) (h : RCtx g) : RCtx (cleanInvalid₂ g) :=
  RCtx_of_keeps (keeps_cleanInvalid₂ g) h

theorem nodupIds_cleanInvalid₂ (g : GPathM) (h : NodupIds g) : NodupIds (cleanInvalid₂ g) :=
  List.Sublist.nodup (keeps_cleanInvalid₂ g).2.2.2 h

-- ============================================================
-- Postconditions (plan step 6, brick 3)
-- ============================================================

/-! What the two phases buy. After `cleanInvalid₂`:

* **(a) the tables are inside the global** (`owners_in_gowners_cleanInvalid₂`): an owner at a step
  where the global has entries is a global entry — so, with `GN`, a **live node**
  (`owners_live_cleanInvalid₂`). The sequential sweep does not have this: a table cut before a
  removal keeps the removed id;
* **(b) the global are nodes** (`GN`, already in `keeps_cleanInvalid₂`);
* **(c) every node is valid** when the graph is (`isValidNode_cleanInvalid₂`): the purge ran to its
  fixpoint (`length + 1` units of fuel suffice), and the cut there is the one the purge tested. -/

theorem owners_in_gowners_cutAll (g : GPathM) :
    ∀ n' ∈ (cutAll g).nodes, ∀ q ∈ n'.owners,
      hasStepEntry (cutAll g).gowners q.id.step = true → q ∈ (cutAll g).gowners := by
  intro n' hn' q hq hs
  obtain ⟨n, _, hEq⟩ := List.mem_map.mp hn'
  subst hEq
  have hq' := (List.mem_filter.mp hq).2
  have hs' : hasStepEntry g.gowners q.id.step = true := hs
  rw [hs', Bool.not_true, Bool.false_or] at hq'
  exact List.mem_of_elem_eq_true hq'

theorem owners_in_gowners_cleanInvalid₂ (g : GPathM) :
    ∀ n' ∈ (cleanInvalid₂ g).nodes, ∀ q ∈ n'.owners,
      hasStepEntry (cleanInvalid₂ g).gowners q.id.step = true → q ∈ (cleanInvalid₂ g).gowners :=
  owners_in_gowners_cutAll _

/-- **No dead ids in the tables**: with `GN`, every owner at a step the global covers is a node. -/
theorem owners_live_cleanInvalid₂ (g : GPathM) (hgn : GN g) :
    ∀ n' ∈ (cleanInvalid₂ g).nodes, ∀ q ∈ n'.owners,
      hasStepEntry (cleanInvalid₂ g).gowners q.id.step = true → HasNode (cleanInvalid₂ g) q :=
  fun n' hn' q hq hs =>
    (keeps_cleanInvalid₂ g).2.1 hgn q (owners_in_gowners_cleanInvalid₂ g n' hn' q hq hs)

-- The purge's fixpoint

private theorem length_filter_lt_of {α : Type} (p : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l → p x = false → (l.filter p).length < l.length := by
  intro l
  induction l with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons a as ih =>
    intro x hx hpx
    rcases List.mem_cons.mp hx with h | h
    · subst h
      simp only [List.filter_cons, hpx, Bool.false_eq_true, if_false, List.length_cons]
      have := List.length_filter_le p as
      omega
    · have h' := ih x h hpx
      simp only [List.filter_cons]
      split
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

theorem length_removeNode_lt (g : GPathM) (id : PathNodeId) (n : PNodeM)
    (h : g.node? id = some n) : (removeNode g id).nodes.length < g.nodes.length := by
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some h
  have hid : n.id = id := node?_id_eq g id n h
  simp only [removeNode, List.length_map]
  exact length_filter_lt_of _ g.nodes n hmem (by rw [hid]; exact bne_self_eq_false id)

theorem purgeStep_eq_or_lt (g : GPathM) (id : PathNodeId) :
    purgeStep g id = g ∨ (purgeStep g id).nodes.length < g.nodes.length := by
  unfold purgeStep
  split
  · exact Or.inl rfl
  · next n hn =>
    split
    · exact Or.inl rfl
    · exact Or.inr (length_removeNode_lt g id n hn)

theorem length_purgeStep_le (g : GPathM) (id : PathNodeId) :
    (purgeStep g id).nodes.length ≤ g.nodes.length := by
  rcases purgeStep_eq_or_lt g id with h | h
  · rw [h]; exact Nat.le_refl _
  · exact Nat.le_of_lt h

theorem length_foldl_purgeStep_le :
    ∀ (ids : List PathNodeId) (g : GPathM), (ids.foldl purgeStep g).nodes.length ≤ g.nodes.length := by
  intro ids
  induction ids with
  | nil => intro g; exact Nat.le_refl _
  | cons id rest ih =>
    intro g
    simp only [List.foldl_cons]
    exact Nat.le_trans (ih _) (length_purgeStep_le g id)

/-- A pass of the purge that removes nothing leaves every step on the spot. -/
theorem foldl_purgeStep_stable :
    ∀ (ids : List PathNodeId) (g : GPathM),
      (ids.foldl purgeStep g).nodes.length = g.nodes.length →
      ids.foldl purgeStep g = g ∧ ∀ id ∈ ids, purgeStep g id = g := by
  intro ids
  induction ids with
  | nil => intro g _; exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | cons id rest ih =>
    intro g hlen
    simp only [List.foldl_cons] at hlen ⊢
    rcases purgeStep_eq_or_lt g id with h | h
    · rw [h] at hlen ⊢
      obtain ⟨h1, h2⟩ := ih g hlen
      refine ⟨h1, fun id' hid' => ?_⟩
      rcases List.mem_cons.mp hid' with e | e
      · rw [e]; exact h
      · exact h2 id' e
    · have hle := length_foldl_purgeStep_le rest (purgeStep g id)
      rw [hlen] at hle
      exact absurd (Nat.lt_of_le_of_lt hle h) (Nat.lt_irrefl _)

/-- Every node would pass the purge test: its cut is a valid node. -/
def Stable (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, isValidNode g (cutNode g.gowners g n) = true

theorem stable_of_round (g : GPathM) (hnd : NodupIds g)
    (hlen : (purgeRound g).nodes.length = g.nodes.length) : Stable g := by
  rw [purgeRound_eq] at hlen
  have hsteps := (foldl_purgeStep_stable _ g hlen).2
  intro n hn
  have hstep := hsteps n.id (List.mem_map_of_mem hn)
  have hnode := node?_of_mem hnd n hn
  cases hv : isValidNode g (cutNode g.gowners g n) with
  | true => rfl
  | false =>
    have hlt := length_removeNode_lt g n.id n hnode
    have hrm : purgeStep g n.id = removeNode g n.id := by
      unfold purgeStep
      rw [hnode]
      simp only [hv]
      rfl
    rw [hrm] at hstep
    rw [hstep] at hlt
    exact absurd hlt (Nat.lt_irrefl _)

theorem length_purgeRound_le (g : GPathM) : (purgeRound g).nodes.length ≤ g.nodes.length := by
  rw [purgeRound_eq]; exact length_foldl_purgeStep_le _ g

/-- **The purge reaches its fixpoint**: with more fuel than nodes, a valid result is `Stable`. -/
theorem stable_purgeFuel : ∀ (fuel : Nat) (g : GPathM), NodupIds g → g.nodes.length < fuel →
    isValid (purgeFuel fuel g) = true → Stable (purgeFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ k ih =>
    intro g hnd hlt hv
    simp only [purgeFuel] at hv ⊢
    split
    · next hg =>
      rw [if_pos hg] at hv
      split
      · next hshr =>
        rw [if_pos hshr] at hv
        exact ih _ (List.Sublist.nodup (keeps_purgeRound g).2.2.2 hnd) (by omega) hv
      · next hshr =>
        have heq : (purgeRound g).nodes.length = g.nodes.length :=
          Nat.le_antisymm (length_purgeRound_le g) (Nat.not_lt.mp hshr)
        have hfix := (foldl_purgeStep_stable _ g (by rw [← purgeRound_eq]; exact heq)).1
        rw [← purgeRound_eq] at hfix
        rw [hfix]
        exact stable_of_round g hnd heq
    · next hg =>
      rw [if_neg hg] at hv
      exact absurd hv hg

theorem isValid_cutAll (g : GPathM) : isValid (cutAll g) = isValid g := rfl

/-- **Every node is valid after `cleanInvalid₂`**, when the graph is. -/
theorem isValidNode_cleanInvalid₂ (g : GPathM) (hnd : NodupIds g)
    (hv : isValid (cleanInvalid₂ g) = true) :
    ∀ n ∈ (cleanInvalid₂ g).nodes, isValidNode (cleanInvalid₂ g) n = true := by
  have hst := stable_purgeFuel _ g hnd (Nat.lt_succ_self _) hv
  intro n' hn'
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  subst hEq
  exact hst n hn

/-- info: 'AbsSatBin.GraphPath.Model.CleanTwoPhase.owners_live_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms owners_live_cleanInvalid₂


/-- info: 'AbsSatBin.GraphPath.Model.CleanTwoPhase.isValidNode_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms isValidNode_cleanInvalid₂

end AbsSatBin.GraphPath.Model.CleanTwoPhase
