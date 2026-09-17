-- lean_project/AbsSat/GraphPath/Model/AggFixpoint.lean
import AbsSat.GraphPath.Model.AggressiveReview
import AbsSat.GraphPath.Model.Fuel
import AbsSat.GraphPath.Model.PickInduction
import AbsSat.GraphPath.Model.SelfOwn
import AbsSat.GraphPath.Model.L6Up

/-!
# What the aggressive review guarantees when it stops

`reviewAgg` stops when the sweep no longer lowers the measure. This module turns that stopping rule
into a property of the state it returns.

* Every step of the sweep either leaves the state unchanged or strictly lowers the measure
  (`aggPair_eqOrLt`, `aggNode_eqOrLt`). A pair that fires — `w` a valid owner of `x` but `x` not an
  owner of `w`, or the two tables sharing nothing at some step — always removes an entry, and that
  strictly lowers the measure (`measure_aggPair_lt`).
* **`aggOk_of_noProgress`** — if the sweep, which visits **every** step (`current_step − 1 … 0`),
  does not lower the measure of a valid state, every owner pair `x`, `w` of valid nodes passes both
  tests: `x` is an owner of `w`, and at every step `w` has owners, `x` has one there that `w` also owns.
* **`aggOk_reviewAgg`** — so every valid result of `reviewAgg` has that property (`AggOk`).
* **`ownSym_of_aggOk`** — in particular owner tables of valid nodes are symmetric, on every step.

Before the author's 14-sept change (report v121) the sweep skipped steps `0` and `current_step − 1`
and had no symmetry test; symmetry then came only from the consistency test through `OOS`, and only
on the interior steps.
-/

namespace AbsSat.GraphPath.Model.AggFixpoint

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PickInduction (intRange_bounds measure_review_le)

-- ============================================================
-- Measure arithmetic
-- ============================================================

theorem sum_map_le {α : Type} (f : α → α) (w : α → Nat) (hf : ∀ a, w (f a) ≤ w a) :
    ∀ l : List α, ((l.map f).map w).sum ≤ (l.map w).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hf a) ih

theorem sum_map_lt {α : Type} (f : α → α) (w : α → Nat) (hf : ∀ a, w (f a) ≤ w a) :
    ∀ l : List α, (∃ a ∈ l, w (f a) < w a) → ((l.map f).map w).sum < (l.map w).sum := by
  intro l
  induction l with
  | nil => intro ⟨_, h, _⟩; cases h
  | cons a rest ih =>
    intro ⟨b, hb, hlt⟩
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact Nat.add_lt_add_of_lt_of_le hlt (sum_map_le f w hf rest)
    · exact Nat.add_lt_add_of_le_of_lt (hf a) (ih ⟨b, hb', hlt⟩)

theorem sum_filter_lt {α : Type} (p : α → Bool) (w : α → Nat) (hw : ∀ a, 1 ≤ w a) :
    ∀ l : List α, (∃ a ∈ l, p a = false) → ((l.filter p).map w).sum < (l.map w).sum := by
  intro l
  induction l with
  | nil => intro ⟨_, h, _⟩; cases h
  | cons a rest ih =>
    intro ⟨b, hb, hpb⟩
    have hle : ∀ l : List α, ((l.filter p).map w).sum ≤ (l.map w).sum := by
      intro l
      induction l with
      | nil => simp
      | cons c cs ihc =>
        simp only [List.filter_cons]
        split
        · simp only [List.map_cons, List.sum_cons]; omega
        · simp only [List.map_cons, List.sum_cons]; omega
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · rw [if_neg (by simp [hpb])]
      simp only [List.map_cons, List.sum_cons]
      have := hle rest
      have := hw b
      omega
    · have hr := ih ⟨b, hb', hpb⟩
      split
      · simp only [List.map_cons, List.sum_cons]; omega
      · simp only [List.map_cons, List.sum_cons]; omega

theorem weight_uniMap_le (B : List PathNodeId) (n : PNodeM) : (uniMap B n).weight ≤ n.weight := by
  simp only [uniMap, PNodeM.weight, intersectOwners]
  have := List.length_filter_le (fun q => !hasStepEntry B q.id.step || B.contains q) n.owners
  omega

theorem measure_updateAt_uniMap_lt (g : GPathM) (id : PathNodeId) (B : List PathNodeId) (n : PNodeM)
    (hn : g.node? id = some n) (hlt : (uniMap B n).weight < n.weight) :
    GPathM.measure (updateAt g id (uniMap B)) < GPathM.measure g := by
  simp only [GPathM.measure, updateAt, updateAtGo]
  apply Nat.add_lt_add_left
  refine sum_map_lt _ PNodeM.weight (fun a => ?_) g.nodes ⟨n, List.mem_of_find?_eq_some hn, ?_⟩
  · split
    · exact weight_uniMap_le B a
    · exact Nat.le_refl _
  · have hid : (n.id == id) = true := beq_iff_eq.mpr (node?_id_eq g id n hn)
    simp only [hid]
    exact hlt

theorem measure_removeNode_lt (g : GPathM) (id : PathNodeId) (n : PNodeM) (hn : g.node? id = some n) :
    GPathM.measure (removeNode g id) < GPathM.measure g := by
  simp only [GPathM.measure, removeNode]
  have hg := List.length_filter_le (fun q => q != id) g.gowners
  have h1 : (((g.nodes.filter (fun m => m.id != id)).map (fun m =>
      ({ m with parents := m.parents.filter (fun p => p != id),
                sons := m.sons.filter (fun s => s != id) } : PNodeM))).map PNodeM.weight).sum
      ≤ ((g.nodes.filter (fun m => m.id != id)).map PNodeM.weight).sum := by
    refine sum_map_le _ PNodeM.weight (fun m => ?_) _
    simp only [PNodeM.weight]
    have := List.length_filter_le (fun p => p != id) m.parents
    have := List.length_filter_le (fun s => s != id) m.sons
    omega
  have h2 : ((g.nodes.filter (fun m => m.id != id)).map PNodeM.weight).sum
      < (g.nodes.map PNodeM.weight).sum := by
    refine sum_filter_lt _ PNodeM.weight (fun m => by simp only [PNodeM.weight]; omega) _
      ⟨n, List.mem_of_find?_eq_some hn, ?_⟩
    simp [node?_id_eq g id n hn]
  omega

-- ============================================================
-- Each step of the sweep: unchanged, or strictly smaller
-- ============================================================

def EqOrLt (g g' : GPathM) : Prop := g' = g ∨ measure g' < measure g

theorem EqOrLt.le {g g' : GPathM} (h : EqOrLt g g') : measure g' ≤ measure g := by
  rcases h with rfl | h
  · exact Nat.le_refl _
  · exact Nat.le_of_lt h

theorem EqOrLt.trans {g₁ g₂ g₃ : GPathM} (h₁ : EqOrLt g₁ g₂) (h₂ : EqOrLt g₂ g₃) : EqOrLt g₁ g₃ := by
  rcases h₁ with rfl | h₁
  · exact h₂
  · exact Or.inr (Nat.lt_of_le_of_lt h₂.le h₁)

theorem eqOrLt_foldl {β : Type} (f : GPathM → β → GPathM) (hf : ∀ g b, EqOrLt g (f g b)) :
    ∀ (l : List β) (g : GPathM), EqOrLt g (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g; exact Or.inl rfl
  | cons b rest ih => intro g; exact EqOrLt.trans (hf g b) (ih (f g b))

/-- A fold of such steps that does not lower the measure left every one of its steps unchanged. -/
theorem foldl_noProgress {β : Type} (f : GPathM → β → GPathM) (hf : ∀ g b, EqOrLt g (f g b)) :
    ∀ (l : List β) (g : GPathM), ¬ measure (l.foldl f g) < measure g → ∀ b ∈ l, f g b = g := by
  intro l
  induction l with
  | nil => intro g _ b hb; cases hb
  | cons a rest ih =>
    intro g hnp b hb
    simp only [List.foldl_cons] at hnp
    rcases hf g a with heq | hlt
    · rw [heq] at hnp
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact heq
      · exact ih g hnp b hb'
    · exact absurd (Nat.lt_of_le_of_lt (eqOrLt_foldl f hf rest _).le hlt) hnp

/-- The sentinel of `dropList` makes the intersection drop `w`. -/
theorem weight_drop_lt (n : PNodeM) (w : PathNodeId) (hw : w ∈ n.owners) :
    (uniMap (dropList n.owners w) n).weight < n.weight := by
  simp only [uniMap, PNodeM.weight, intersectOwners]
  have hlt : (n.owners.filter (fun q => !hasStepEntry (dropList n.owners w) q.id.step ||
      (dropList n.owners w).contains q)).length < n.owners.length := by
    refine List.length_filter_lt_length_iff_exists.mpr ⟨w, hw, ?_⟩
    have hent : hasStepEntry (dropList n.owners w) w.id.step = true :=
      List.any_eq_true.mpr ⟨_, List.mem_append_right _ List.mem_cons_self, beq_iff_eq.mpr rfl⟩
    have hnot : (dropList n.owners w).contains w = false := by
      simp only [dropList, List.contains_append, List.contains_cons, List.contains_nil,
        Bool.or_false]
      have h1 : (n.owners.filter (fun q => q != w)).contains w = false := by
        cases h : (n.owners.filter (fun q => q != w)).contains w with
        | false => rfl
        | true =>
          have hm := (List.mem_filter.mp (List.contains_iff_mem.mp h)).2
          simp only [bne_self_eq_false] at hm
          exact Bool.noConfusion hm
      have h2 : (w == ({ id := { step := w.id.step, index := w.id.index + 1 }, parent_id := w.parent_id } : PathNodeId)) = false := by
        cases h : (w == ({ id := { step := w.id.step, index := w.id.index + 1 }, parent_id := w.parent_id } : PathNodeId)) with
        | false => rfl
        | true =>
          have he := congrArg (fun p : PathNodeId => p.id.index) (eq_of_beq h)
          simp only at he
          omega
      rw [h1, h2]; rfl
    intro hp
    simp only [hent, Bool.not_true, Bool.false_or] at hp
    rw [hnot] at hp
    exact Bool.noConfusion hp
  omega

theorem aggPair_eqOrLt (g : GPathM) (x w : PathNodeId) : EqOrLt g (aggPair g x w) := by
  unfold aggPair
  split
  · next nx nw hx hw =>
    split
    · next hasym =>
      have hmem : w ∈ nx.owners := by
        simp only [Bool.and_eq_true] at hasym
        exact List.contains_iff_mem.mp hasym.1.1
      exact Or.inr (measure_updateAt_uniMap_lt g x _ nx hx (weight_drop_lt nx w hmem))
    · split
      · next hcond =>
        have hmem : w ∈ nx.owners := by
          simp only [Bool.and_eq_true] at hcond
          exact List.contains_iff_mem.mp hcond.1.1
        refine Or.inr (Nat.lt_of_le_of_lt ?_ (measure_updateAt_uniMap_lt g x _ nx hx (weight_drop_lt nx w hmem)))
        exact measure_updateAt_le _ w _ (weight_uniMap_le _)
      · exact Or.inl rfl
  · exact Or.inl rfl

/-- A pair that fires (asymmetric, or sharing nothing at some step) strictly lowers the measure. -/
theorem measure_aggPair_lt (g : GPathM) (x w : PathNodeId) (nx nw : PNodeM)
    (hx : g.node? x = some nx) (hw : g.node? w = some nw) (hmem : w ∈ nx.owners)
    (hvw : isValidNode g nw = true)
    (hfire : nw.owners.contains x = false ∨ sharesEveryStep g.current_step nx.owners nw.owners = false) :
    GPathM.measure (aggPair g x w) < GPathM.measure g := by
  have hcw : nx.owners.contains w = true := List.contains_iff_mem.mpr hmem
  by_cases ha : (nx.owners.contains w && isValidNode g nw && !nw.owners.contains x) = true
  · have heq : aggPair g x w = updateAt g x (uniMap (dropList nx.owners w)) := by
      unfold aggPair
      rw [hx, hw]
      simp only [ha, if_pos]
    rw [heq]
    exact measure_updateAt_uniMap_lt g x _ nx hx (weight_drop_lt nx w hmem)
  · have hcond : (nx.owners.contains w && isValidNode g nw &&
        !sharesEveryStep g.current_step nx.owners nw.owners) = true := by
      rcases hfire with h | h
      · exfalso
        apply ha
        simp only [hcw, hvw, h, Bool.and_self, Bool.not_false]
      · simp only [hcw, hvw, h, Bool.and_self, Bool.not_false]
    have heq : aggPair g x w = dropOwnerPair g x w nx.owners nw.owners := by
      unfold aggPair
      rw [hx, hw]
      simp only [ha, hcond, if_pos, if_neg, Bool.false_eq_true, not_false_eq_true]
    rw [heq]
    refine Nat.lt_of_le_of_lt ?_ (measure_updateAt_uniMap_lt g x _ nx hx (weight_drop_lt nx w hmem))
    exact measure_updateAt_le _ w _ (weight_uniMap_le _)

/-- The pair checks of one node, before the node itself is re-examined. -/
def aggPairsOf (g : GPathM) (x : PathNodeId) : GPathM :=
  (intRange 0 (g.current_step - 1)).reverse.foldl
    (fun g kw => (ownersAtNow g x kw).foldl (fun g w => aggPair g x w) g) g

theorem eqOrLt_aggPairsOf (g : GPathM) (x : PathNodeId) : EqOrLt g (aggPairsOf g x) :=
  eqOrLt_foldl _ (fun g _kw => eqOrLt_foldl _ (fun g w => aggPair_eqOrLt g x w) _ g) _ g

theorem eqOrLt_finish (g₁ : GPathM) (x : PathNodeId) :
    EqOrLt g₁ (match g₁.node? x with
      | none => g₁
      | some n₁ => if isValidNode g₁ n₁ then g₁ else removeNode g₁ x) := by
  split
  · exact Or.inl rfl
  · next n₁ hn₁ =>
    split
    · exact Or.inl rfl
    · exact Or.inr (measure_removeNode_lt g₁ x n₁ hn₁)

theorem aggNode_eqOrLt (g : GPathM) (x : PathNodeId) : EqOrLt g (aggNode g x) := by
  unfold aggNode
  split
  · exact Or.inl rfl
  · refine EqOrLt.trans ?_ (eqOrLt_finish _ x)
    split
    · exact eqOrLt_aggPairsOf g x
    · exact Or.inl rfl

theorem aggNode_of_valid (g : GPathM) (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx)
    (hvx : isValidNode g nx = true) :
    aggNode g x = (match (aggPairsOf g x).node? x with
      | none => aggPairsOf g x
      | some n₁ => if isValidNode (aggPairsOf g x) n₁ then aggPairsOf g x
        else removeNode (aggPairsOf g x) x) := by
  unfold aggNode
  rw [hx]
  simp only [hvx, if_pos]
  rfl

-- ============================================================
-- The stopping rule, as a property of the state
-- ============================================================

/-- **Every owner pair of valid nodes passes both of the author's tests**: the entry is symmetric, and
the two tables share every step. -/
def AggOk (g : GPathM) : Prop :=
  ∀ x nx w nw, g.node? x = some nx → g.node? w = some nw →
    0 ≤ x.id.step → x.id.step < g.current_step →
    0 ≤ w.id.step → w.id.step < g.current_step →
    w ∈ nx.owners → isValidNode g nx = true → isValidNode g nw = true →
    x ∈ nw.owners ∧ sharesEveryStep g.current_step nx.owners nw.owners = true

theorem mem_reverse_intRange {lo hi k : Int} (h1 : lo ≤ k) (h2 : k ≤ hi) :
    k ∈ (intRange lo hi).reverse :=
  List.mem_reverse.mpr (mem_intRange h1 h2)

/-- **If the sweep does not lower the measure of a valid state, the state passes the test.** -/
theorem aggOk_of_noProgress (g : GPathM) (hv : isValid g = true)
    (hnp : ¬ GPathM.measure (aggSweep g) < GPathM.measure g) : AggOk g := by
  intro x nx w nw hx hw hx1 hx2 hw1 hw2 hmem hvx hvw
  by_cases hgood : x ∈ nw.owners ∧ sharesEveryStep g.current_step nx.owners nw.owners = true
  · exact hgood
  · exfalso
    have hs : nw.owners.contains x = false ∨ sharesEveryStep g.current_step nx.owners nw.owners = false := by
      by_cases hc : x ∈ nw.owners
      · right
        cases h : sharesEveryStep g.current_step nx.owners nw.owners with
        | false => rfl
        | true => exact absurd ⟨hc, h⟩ hgood
      · left
        cases h : nw.owners.contains x with
        | false => rfl
        | true => exact absurd (List.contains_iff_mem.mp h) hc
    have hsweep : aggSweep g = (intRange 0 (g.current_step - 1)).reverse.foldl
        (fun g k => ((g.line k).map (·.id)).foldl aggNode g) g := by
      unfold aggSweep
      rw [if_pos hv]
    rw [hsweep] at hnp
    have houter := foldl_noProgress _
      (fun g k => eqOrLt_foldl _ aggNode_eqOrLt _ g) _ g hnp x.id.step
      (mem_reverse_intRange hx1 (by omega))
    have hline : x ∈ (g.line x.id.step).map (·.id) := mem_line_of_node? g x nx hx _ rfl
    have hinner := foldl_noProgress _ aggNode_eqOrLt _ g
      (by rw [houter]; exact Nat.lt_irrefl _) x hline
    -- the node's pair checks did not lower the measure either
    have hpairs : ¬ GPathM.measure (aggPairsOf g x) < GPathM.measure g := by
      intro hlt
      have hfin := eqOrLt_finish (aggPairsOf g x) x
      rw [← aggNode_of_valid g x nx hx hvx, hinner] at hfin
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hfin.le hlt)
    have hkw := foldl_noProgress _
      (fun g kw => eqOrLt_foldl _ (fun g w => aggPair_eqOrLt g x w) _ g) _ g hpairs w.id.step
      (mem_reverse_intRange hw1 (by omega))
    have hof : ownersOf g x = nx.owners := by unfold ownersOf; rw [hx]
    have hwmem : w ∈ ownersAtNow g x w.id.step := by
      show w ∈ ownersAt (ownersOf g x) w.id.step
      rw [hof]
      exact List.mem_filter.mpr ⟨hmem, beq_iff_eq.mpr rfl⟩
    have hpair := foldl_noProgress _ (fun g w => aggPair_eqOrLt g x w) _ g
      (by rw [hkw]; exact Nat.lt_irrefl _) w hwmem
    have hlt := measure_aggPair_lt g x w nx nw hx hw hmem hvw hs
    have hle : GPathM.measure g ≤ GPathM.measure (aggPair g x w) :=
      Nat.le_of_eq (congrArg GPathM.measure hpair).symm
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)

/-- **Every valid result of `reviewAgg` passes the test.** -/
theorem aggOk_reviewAggFuel : ∀ (fuel : Nat) (g : GPathM), GPathM.measure g < fuel →
    isValid (reviewAggFuel fuel g) = true → AggOk (reviewAggFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro g hm hv
    simp only [reviewAggFuel] at hv ⊢
    split at hv
    · next hv₁ =>
      rw [if_pos hv₁]
      split at hv
      · next hlt =>
        rw [if_pos hlt]
        exact ih _ (Nat.lt_of_lt_of_le hlt (Nat.le_trans (measure_review_le g) (Nat.le_of_lt_succ hm))) hv
      · next hnlt =>
        rw [if_neg hnlt]
        exact aggOk_of_noProgress _ hv₁ hnlt
    · next hv₁ => exact absurd hv hv₁

theorem aggOk_reviewAgg (g : GPathM) (hv : isValid (reviewAgg g) = true) : AggOk (reviewAgg g) :=
  aggOk_reviewAggFuel _ g (Nat.lt_succ_self _) hv

-- ============================================================
-- Symmetry on every step
-- ============================================================

/-- **Owner tables of valid nodes are symmetric**, on every step. -/
theorem ownSym_of_aggOk (g : GPathM) (hok : AggOk g)
    (x w : PathNodeId) (nx nw : PNodeM) (hx : g.node? x = some nx) (hw : g.node? w = some nw)
    (hx1 : 0 ≤ x.id.step) (hx2 : x.id.step < g.current_step)
    (hw1 : 0 ≤ w.id.step) (hw2 : w.id.step < g.current_step)
    (hmem : w ∈ nx.owners) (hvx : isValidNode g nx = true) (hvw : isValidNode g nw = true) :
    x ∈ nw.owners :=
  (hok x nx w nw hx hw hx1 hx2 hw1 hw2 hmem hvx hvw).1

/-- info: 'AbsSat.GraphPath.Model.AggFixpoint.aggOk_reviewAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms aggOk_reviewAgg


end AbsSat.GraphPath.Model.AggFixpoint
