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

end AbsSat.GraphPath.Model.CleanTwoPhase
