-- lean_project/AbsSat/GraphPath/Model/CleanTwoPhase.lean
import AbsSat.GraphPath.Model.ReaderAgg

/-!
# `cleanInvalid` in two phases (report v181, §6)

The current `cleanInvalid` walks the nodes one by one, cutting each table with the global owners
*as they stand at that moment*. It depends on the order, and it leaves ids of nodes removed later
in the tables of nodes processed earlier. The two-phase version separates the two things it does:

1. **Purge, to a fixpoint** (`purgeFuel`): remove every node that *would* be invalid once cut
   against the current global owners, and repeat while something is removed. No table is touched.
2. **One cut** (`cutAll`): cut every surviving node against the final global owners.

What "cut" means (`cutNode`) is what the sequential sweep leaves behind once every node has been
processed: the owners intersected with the global ones, and a link `x — y` kept only when each end
admits the other (`relink` drops the links outside the node's own cut table, and
`unlinkIncompatible` drops the node from the neighbours outside it).

Proved here, the shape (plan step 6, bricks 1–2):

* `pruned_cleanInvalid₂`, `measure_cleanInvalid₂_le` (and for `reviewPass₂`): it only narrows;
* `keeps_cleanInvalid₂`, hence `RCtx_cleanInvalid₂`: the reader's context survives;
* `SN_cleanInvalid₂`, and with `NodupIds` `SMP_cleanInvalid₂`, `PMS_cleanInvalid₂`: the two link
  tables stay mirrors of each other. The cut keeps a link exactly when both ends admit it, which
  is what makes the mirror hold after one simultaneous cut.

And the postconditions (brick 3): `owners_live_cleanInvalid₂` — no dead ids in the tables — and
`isValidNode_cleanInvalid₂` — every node valid when the graph is.

The probe `clean2` (`Probes/RowDegree.lean`) compares the review over it with the current one.
-/

namespace AbsSat.GraphPath.Model.CleanTwoPhase

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview (aggSweep)
open AbsSat.GraphPath.Model.ReaderAgg (Keeps keeps_removeNode keeps_foldl RCtx_of_keeps)
open AbsSat.GraphPath.Model.Reader (RCtx)
open AbsSat.GraphPath.Model.GownersNodes (HasNode GN)
open AbsSat.GraphPath.Model.Parents (PN)
open AbsSat.GraphPath.Model.Sons (SMP PMS SN)

/-- The owners of `n` cut against `gow`. -/
def cutOwners (gow : List PathNodeId) (n : PNodeM) : List PathNodeId :=
  intersectOwners n.owners gow

/-- `m`, cut against `gow`, still owns `x`. A missing node admits nothing. -/
def admits (gow : List PathNodeId) (g : GPathM) (m x : PathNodeId) : Bool :=
  match g.node? m with
  | some pm => (cutOwners gow pm).contains x
  | none => false

/-- A node cut against `gow`: owners intersected, and only the links both ends admit. -/
def cutNode (gow : List PathNodeId) (g : GPathM) (n : PNodeM) : PNodeM :=
  let ow := cutOwners gow n
  { n with owners := ow,
           parents := n.parents.filter (fun p => ow.contains p && admits gow g p n.id),
           sons := n.sons.filter (fun s => ow.contains s && admits gow g s n.id) }

/-- One purge round over a snapshot of the ids: a node that would be invalid once cut against the
current global owners is removed; removals are seen by the nodes that follow. -/
def purgeRound (g : GPathM) : GPathM :=
  (g.nodes.map (·.id)).foldl (fun g id =>
    match g.node? id with
    | none => g
    | some n => if isValidNode g (cutNode g.gowners g n) then g else removeNode g id) g

/-- Phase 1: purge rounds while the graph is valid and a round removes something. Every round
that continues removes a node, so `g.nodes.length + 1` units of fuel suffice. -/
def purgeFuel : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    if isValid g then
      let g' := purgeRound g
      if g'.nodes.length < g.nodes.length then purgeFuel fuel g' else g'
    else g

/-- Phase 2: every node cut against the final global owners, at once. -/
def cutAll (g : GPathM) : GPathM :=
  { g with nodes := g.nodes.map (cutNode g.gowners g) }

/-- **`cleanInvalid` in two phases.** -/
def cleanInvalid₂ (g : GPathM) : GPathM :=
  cutAll (purgeFuel (g.nodes.length + 1) g)

-- ============================================================
-- The review over it (same shape as `reviewPass` … `reviewAgg`)
-- ============================================================

def reviewPass₂ (g : GPathM) : GPathM :=
  reviewSons (reviewParents (cleanInvalid₂ g))

def reviewFuel₂ : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    if isValid g then
      let g' := reviewPass₂ g
      if measure g' < measure g then reviewFuel₂ fuel g' else g'
    else
      g

def review₂ (g : GPathM) : GPathM :=
  reviewFuel₂ (measure g + 1) g

def reviewAggFuel₂ : Nat → GPathM → GPathM
  | 0, g => review₂ g
  | fuel + 1, g =>
    let g₁ := review₂ g
    if isValid g₁ then
      let g₂ := aggSweep g₁
      if measure g₂ < measure g₁ then reviewAggFuel₂ fuel g₂ else g₁
    else g₁

def reviewAgg₂ (g : GPathM) : GPathM := reviewAggFuel₂ (measure g + 1) g

-- ============================================================
-- Shape: it only narrows, and the measure does not grow
-- ============================================================

theorem cutNode_id (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    (cutNode gow g n).id = n.id := rfl

theorem cutNode_owners_sub (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    ∀ q ∈ (cutNode gow g n).owners, q ∈ n.owners :=
  fun _ hq => (List.mem_filter.mp hq).1

theorem cutNode_parents_sub (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    ∀ p ∈ (cutNode gow g n).parents, p ∈ n.parents :=
  fun _ hp => (List.mem_filter.mp hp).1

theorem cutNode_sons_sub (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    ∀ s ∈ (cutNode gow g n).sons, s ∈ n.sons :=
  fun _ hs => (List.mem_filter.mp hs).1

/-- One step of the purge: keep the graph or remove the node. -/
def purgeStep (g : GPathM) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some n => if isValidNode g (cutNode g.gowners g n) then g else removeNode g id

theorem purgeRound_eq (g : GPathM) : purgeRound g = (g.nodes.map (·.id)).foldl purgeStep g := rfl

theorem pruned_purgeStep (g : GPathM) (id : PathNodeId) : Pruned g (purgeStep g id) := by
  unfold purgeStep
  split
  · exact Pruned.refl g
  · split
    · exact Pruned.refl g
    · exact pruned_removeNode g id

theorem pruned_purgeRound (g : GPathM) : Pruned g (purgeRound g) := by
  rw [purgeRound_eq]
  exact pruned_foldl purgeStep pruned_purgeStep _ g

theorem pruned_purgeFuel : ∀ (fuel : Nat) (g : GPathM), Pruned g (purgeFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Pruned.refl g
  | succ n ih =>
    intro g
    simp only [purgeFuel]
    split
    · split
      · exact Pruned.trans (pruned_purgeRound g) (ih _)
      · exact pruned_purgeRound g
    · exact Pruned.refl g

theorem pruned_cutAll (g : GPathM) : Pruned g (cutAll g) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n' hn' := by
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
    subst hEq
    exact ⟨n, hn, rfl, cutNode_owners_sub _ _ n, cutNode_parents_sub _ _ n⟩

theorem pruned_cleanInvalid₂ (g : GPathM) : Pruned g (cleanInvalid₂ g) :=
  Pruned.trans (pruned_purgeFuel _ g) (pruned_cutAll _)

theorem pruned_reviewPass₂ (g : GPathM) : Pruned g (reviewPass₂ g) :=
  Pruned.trans (pruned_cleanInvalid₂ g)
    (Pruned.trans (pruned_reviewParents _) (pruned_reviewSons _))

theorem weight_cutNode_le (gow : List PathNodeId) (g : GPathM) (n : PNodeM) :
    PNodeM.weight (cutNode gow g n) ≤ PNodeM.weight n := by
  simp only [PNodeM.weight, cutNode, cutOwners, intersectOwners]
  have h1 := List.length_filter_le (fun q => !hasStepEntry gow q.id.step || gow.contains q) n.owners
  have h2 := List.length_filter_le
    (fun p => (n.owners.filter (fun q => !hasStepEntry gow q.id.step || gow.contains q)).contains p
      && admits gow g p n.id) n.parents
  have h3 := List.length_filter_le
    (fun s => (n.owners.filter (fun q => !hasStepEntry gow q.id.step || gow.contains q)).contains s
      && admits gow g s n.id) n.sons
  omega

private theorem sum_map_le' {α : Type} (l : List α) (f h : α → Nat)
    (hle : ∀ a ∈ l, f a ≤ h a) : (l.map f).sum ≤ (l.map h).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hle a List.mem_cons_self)
      (ih (fun x hx => hle x (List.mem_cons_of_mem _ hx)))

theorem measure_cutAll_le (g : GPathM) : GPathM.measure (cutAll g) ≤ GPathM.measure g := by
  simp only [GPathM.measure, cutAll]
  rw [List.map_map]
  exact Nat.add_le_add_left
    (sum_map_le' g.nodes _ _ (fun n _ => weight_cutNode_le g.gowners g n)) _

theorem measure_purgeStep_le (g : GPathM) (id : PathNodeId) :
    measure (purgeStep g id) ≤ measure g := by
  unfold purgeStep
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · exact measure_removeNode_le g id

theorem measure_foldl_purgeStep_le :
    ∀ (ids : List PathNodeId) (g : GPathM), measure (ids.foldl purgeStep g) ≤ measure g := by
  intro ids
  induction ids with
  | nil => intro g; exact Nat.le_refl _
  | cons id rest ih =>
    intro g
    simp only [List.foldl_cons]
    exact Nat.le_trans (ih _) (measure_purgeStep_le g id)

theorem measure_purgeRound_le (g : GPathM) : measure (purgeRound g) ≤ measure g := by
  rw [purgeRound_eq]; exact measure_foldl_purgeStep_le _ g

theorem measure_purgeFuel_le : ∀ (fuel : Nat) (g : GPathM), measure (purgeFuel fuel g) ≤ measure g := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Nat.le_refl _
  | succ n ih =>
    intro g
    simp only [purgeFuel]
    split
    · split
      · exact Nat.le_trans (ih _) (measure_purgeRound_le g)
      · exact measure_purgeRound_le g
    · exact Nat.le_refl _

theorem measure_cleanInvalid₂_le (g : GPathM) : measure (cleanInvalid₂ g) ≤ measure g :=
  Nat.le_trans (measure_cutAll_le _) (measure_purgeFuel_le _ g)

theorem measure_reviewPass₂_le (g : GPathM) : measure (reviewPass₂ g) ≤ measure g :=
  Nat.le_trans (measure_reviewSons_le _)
    (Nat.le_trans (measure_reviewParents_le _) (measure_cleanInvalid₂_le g))

/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.pruned_reviewPass₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms pruned_reviewPass₂

/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.measure_reviewPass₂_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms measure_reviewPass₂_le

-- ============================================================
-- Shape: the reader's context and the link invariants survive
-- ============================================================

theorem hasNode_cutAll (g : GPathM) (q : PathNodeId) (h : HasNode g q) : HasNode (cutAll g) q := by
  obtain ⟨n, hn, hid⟩ := h
  exact ⟨cutNode g.gowners g n, List.mem_map_of_mem hn, hid⟩

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

/-- A property preserved by `removeNode` is preserved by the whole purge. -/
theorem purgeFuel_inv (P : GPathM → Prop) (hP : ∀ g id, P g → P (removeNode g id)) :
    ∀ (fuel : Nat) (g : GPathM), P g → P (purgeFuel fuel g) := by
  have hstep : ∀ g id, P g → P (purgeStep g id) := by
    intro g id hg
    unfold purgeStep
    split
    · exact hg
    · split
      · exact hg
      · exact hP g id hg
  have hround : ∀ g, P g → P (purgeRound g) := by
    intro g hg
    rw [purgeRound_eq]
    generalize g.nodes.map (·.id) = ids
    induction ids generalizing g with
    | nil => exact hg
    | cons id rest ih => exact ih _ (hstep g id hg)
  intro fuel
  induction fuel with
  | zero => intro g hg; exact hg
  | succ n ih =>
    intro g hg
    simp only [purgeFuel]
    split
    · split
      · exact ih _ (hround g hg)
      · exact hround g hg
    · exact hg

theorem SN_cutAll (g : GPathM) (h : SN g) : SN (cutAll g) := by
  intro n' hn' s hs
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  subst hEq
  exact hasNode_cutAll g s (h n hn s (cutNode_sons_sub _ _ n s hs))

theorem SN_cleanInvalid₂ (g : GPathM) (h : SN g) : SN (cleanInvalid₂ g) :=
  SN_cutAll _ (purgeFuel_inv SN (fun g id h => Sons.SN_removeNode g id h) _ g h)

/-- A link kept by the cut is admitted by both ends: the other end's cut table has this node. -/
theorem admits_of_mem (gow : List PathNodeId) (g : GPathM) (hnd : NodupIds g) (m : PNodeM)
    (hm : m ∈ g.nodes) (x : PathNodeId) (h : admits gow g m.id x = true) :
    (cutOwners gow m).contains x = true := by
  unfold admits at h
  rw [node?_of_mem hnd m hm] at h
  exact h

theorem admits_of_contains (gow : List PathNodeId) (g : GPathM) (hnd : NodupIds g) (n : PNodeM)
    (hn : n ∈ g.nodes) (x : PathNodeId) (h : (cutOwners gow n).contains x = true) :
    admits gow g n.id x = true := by
  unfold admits
  rw [node?_of_mem hnd n hn]
  exact h

theorem SMP_cutAll (g : GPathM) (hnd : NodupIds g) (h : SMP g) : SMP (cutAll g) := by
  intro n' hn' p hp m' hm' hmid
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  subst hEq
  obtain ⟨m, hm, hmEq⟩ := List.mem_map.mp hm'
  subst hmEq
  simp only [cutNode, List.mem_filter, Bool.and_eq_true] at hp
  obtain ⟨hpn, hown, hadm⟩ := hp
  have hmid' : m.id = p := hmid
  subst hmid'
  simp only [cutNode, List.mem_filter, Bool.and_eq_true]
  exact ⟨h n hn m.id hpn m hm rfl, admits_of_mem _ g hnd m hm n.id hadm,
    admits_of_contains _ g hnd n hn m.id hown⟩

theorem PMS_cutAll (g : GPathM) (hnd : NodupIds g) (h : PMS g) : PMS (cutAll g) := by
  intro n' hn' s hs m' hm' hmid
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  subst hEq
  obtain ⟨m, hm, hmEq⟩ := List.mem_map.mp hm'
  subst hmEq
  simp only [cutNode, List.mem_filter, Bool.and_eq_true] at hs
  obtain ⟨hsn, hown, hadm⟩ := hs
  have hmid' : m.id = s := hmid
  subst hmid'
  simp only [cutNode, List.mem_filter, Bool.and_eq_true]
  exact ⟨h n hn m.id hsn m hm rfl, admits_of_mem _ g hnd m hm n.id hadm,
    admits_of_contains _ g hnd n hn m.id hown⟩

theorem nodupIds_purgeFuel (fuel : Nat) (g : GPathM) (h : NodupIds g) :
    NodupIds (purgeFuel fuel g) :=
  List.Sublist.nodup (keeps_purgeFuel fuel g).2.2.2 h

theorem SMP_cleanInvalid₂ (g : GPathM) (hnd : NodupIds g) (h : SMP g) : SMP (cleanInvalid₂ g) :=
  SMP_cutAll _ (nodupIds_purgeFuel _ g hnd)
    (purgeFuel_inv SMP (fun g id h => Sons.SMP_removeNode g id h) _ g h)

theorem PMS_cleanInvalid₂ (g : GPathM) (hnd : NodupIds g) (h : PMS g) : PMS (cleanInvalid₂ g) :=
  PMS_cutAll _ (nodupIds_purgeFuel _ g hnd)
    (purgeFuel_inv PMS (fun g id h => Sons.PMS_removeNode g id h) _ g h)

/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.RCtx_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms RCtx_cleanInvalid₂

/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.SN_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SN_cleanInvalid₂

/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.SMP_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SMP_cleanInvalid₂

/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.PMS_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PMS_cleanInvalid₂

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

/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.owners_live_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms owners_live_cleanInvalid₂


/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.isValidNode_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms isValidNode_cleanInvalid₂

end AbsSat.GraphPath.Model.CleanTwoPhase
