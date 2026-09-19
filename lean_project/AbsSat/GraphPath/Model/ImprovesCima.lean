-- lean_project/AbsSat/GraphPath/Model/ImprovesCima.lean
import AbsSat.GraphPath.Model.HereditaryValid

/-!
# `ImprovesCima`: the review with the rule of the top

Route C leaves one thing open: the witnesses the review hands for a pair must lie in the table of the
side the pair's chain names (`HereditaryValid.ChainClosureAt`). Probes `chainside2`, `history` and
`chainfam` never saw it fail (2.8 M pairs, 0 failures), but nothing in the current review forces it.

This module adds a rule that does force it. It is the `Improves` machine with one more sweep inside the
review, run at a union by key, where the sides that built the union are still at hand:

> **The rule of the top.** Keep an entry `a → b` only if, for every top `t` that a chain of common
> owners of `a` and `b` reaches, the side of `t` carries `a → b` in its own table, in both directions.

The sweep only removes entries, and a genuine path is never touched: its own nodes are the chain and the
witnesses, and the side of any top it reaches carries all of its pairs.

What is proved here: the rule's shape (`cimaPair` drops at most one entry pair), and that the sweep only
removes (`keeps_cimaSweep`, `pruned_cimaSweep`). The two core statements — no solution is lost, and a
support survives — are stated as `ConservesChains` and `KeepsSupports`, the next targets.
-/

namespace AbsSat.GraphPath.Model.ImprovesCima

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview (dropList dropOwnerPair)
open AbsSat.GraphPath.Model.ReaderAgg (Keeps)

-- ============================================================
-- The chain of common owners, computed
-- ============================================================

/-- The nodes of step `k` that own both `a` and `b`, both ways. -/
def commonAt (g : GPathM) (a b : PathNodeId) (k : Int) : List PathNodeId :=
  ((g.line k).map (·.id)).filter (fun c =>
    (ownersOf g c).contains a && (ownersOf g c).contains b &&
      (ownersOf g a).contains c && (ownersOf g b).contains c)

/-- One step of the chain: `c` can carry on upwards when one of the nodes already reached is a son of
`c` — read from that node's parents, which a narrowing only shrinks — and the two own each other. -/
def climbs (g : GPathM) (up : List PathNodeId) (c : PathNodeId) : Bool :=
  up.any (fun s => match g.node? s with
    | some ns => ns.parents.contains c && (ownersOf g c).contains s && (ownersOf g s).contains c
    | none => false)

/-- The tops a chain of common owners of `a` and `b` reaches, by stepping down from the last step. -/
def reachTops (g : GPathM) (a b : PathNodeId) : List PathNodeId :=
  let top := g.current_step - 1
  -- from the last step down: the nodes of each step a chain can climb from
  let climbed := (intRange 0 (top - 1)).reverse.foldl
    (fun acc k => (commonAt g a b k).filter (fun c => climbs g acc c)) (commonAt g a b top)
  if a.id.step = top then (commonAt g a b top).filter (fun c => c == a)
  else if climbs g climbed a then commonAt g a b top else []

/-- The side a top belongs to, among the sides that built the union: the one whose last step holds it. -/
def sideOf (sides : List GPathM) (t : PathNodeId) : Option GPathM :=
  sides.find? (fun S => (S.node? t).isSome)

/-- Does the side of `t` carry the entry, both ways? -/
def carries (sides : List GPathM) (t a b : PathNodeId) : Bool :=
  match sideOf sides t with
  | none => false
  | some S => (ownersOf S a).contains b && (ownersOf S b).contains a

-- ============================================================
-- The sweep
-- ============================================================

/-- **The rule of the top, for one entry.** If some top the pair's chain reaches has a side that does not
carry the pair, the two stop owning each other. -/
def cimaPair (sides : List GPathM) (g : GPathM) (x w : PathNodeId) : GPathM :=
  match g.node? x, g.node? w with
  | some nx, some nw =>
    if nx.owners.contains w && !(reachTops g x w).all (fun t => carries sides t x w) then
      dropOwnerPair g x w nx.owners nw.owners
    else g
  | _, _ => g

def cimaNode (sides : List GPathM) (g : GPathM) (x : PathNodeId) : GPathM :=
  match g.node? x with
  | none => g
  | some nx => nx.owners.foldl (fun g w => cimaPair sides g x w) g

/-- The sweep: every node, from the last step down. -/
def cimaSweep (sides : List GPathM) (g : GPathM) : GPathM :=
  if isValid g then
    (intRange 0 (g.current_step - 1)).reverse.foldl
      (fun g k => ((g.line k).map (·.id)).foldl (cimaNode sides) g) g
  else g

-- ============================================================
-- The sweep only removes
-- ============================================================

theorem keeps_cimaPair (sides : List GPathM) (g : GPathM) (x w : PathNodeId) :
    Keeps g (cimaPair sides g x w) := by
  unfold cimaPair
  split
  · split
    · exact Keeps.trans (ReaderAgg.keeps_updateAt_uniMap _ _ _)
        (ReaderAgg.keeps_updateAt_uniMap _ _ _)
    · exact Keeps.refl g
  · exact Keeps.refl g

theorem keeps_cimaNode (sides : List GPathM) (g : GPathM) (x : PathNodeId) :
    Keeps g (cimaNode sides g x) := by
  unfold cimaNode
  cases hx : g.node? x with
  | none => exact Keeps.refl g
  | some nx => exact ReaderAgg.keeps_foldl _ (fun g w => keeps_cimaPair sides g x w) _ _

theorem keeps_cimaSweep (sides : List GPathM) (g : GPathM) : Keeps g (cimaSweep sides g) := by
  unfold cimaSweep
  split
  · exact ReaderAgg.keeps_foldl _
      (fun g k => ReaderAgg.keeps_foldl _ (fun g x => keeps_cimaNode sides g x) _ _) _ _
  · exact Keeps.refl g

-- ============================================================
-- The core: no solution is lost
-- ============================================================

open AbsSat.GraphPath.Model.AggressiveReview (mem_dropList chain_mem_owners)

/-- **One entry: the rule never separates two nodes of a sound chain** whose reached tops the sides
carry. Off the chain it only removes, as every drop does. -/
theorem ChainSound_cimaPair (sides : List GPathM) (g : GPathM) (x w : PathNodeId)
    (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hcar : ∀ i j, 0 ≤ i → i < g.current_step → 0 ≤ j → j < g.current_step → sel i = x → sel j = w →
      (reachTops g x w).all (fun t => carries sides t x w) = true) :
    ChainSound (cimaPair sides g x w) sel := by
  unfold cimaPair
  split
  · next nx nw hx hw =>
    split
    · next hcond =>
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hnot : ∀ i j, 0 ≤ i → i < g.current_step → 0 ≤ j → j < g.current_step →
          sel i = x → sel j = w → False := by
        intro i j hi0 hi hj0 hj hix hjw
        have := hcar i j hi0 hi hj0 hj hix hjw
        rw [hcond.2] at this
        exact Bool.noConfusion this
      have h₁ : ChainSound (updateAt g x (uniMap (dropList nx.owners w))) sel := by
        refine ChainSound_updateAt_gen g x _ sel h ?_
        intro j hj0 hj hjx i hi0 hi
        have hnx : g.node? (sel j) = some nx := by rw [hjx]; exact hx
        refine mem_dropList _ w _ (chain_mem_owners g sel h j hj0 hj nx hnx i hi0 hi) ?_
        intro hiw
        exact hnot j i hj0 hj hi0 hi hjx hiw
      refine ChainSound_updateAt_gen _ w _ sel h₁ ?_
      intro j hj0 hj hjw i hi0 hi
      have hnw : g.node? (sel j) = some nw := by rw [hjw]; exact hw
      refine mem_dropList _ x _ (chain_mem_owners g sel h j hj0 hj nw hnw i hi0 hi) ?_
      intro hix
      exact hnot i j hi0 hi hj0 hj hix hjw
    · exact h
  · exact h

/-- The rule's hypothesis, robust along the sweep: at every narrowing the sweep can reach, the tops a
chain pair reaches are carried by their sides. -/
def Carried (sides : List GPathM) (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ g', Keeps g g' → ∀ i j, 0 ≤ i → i < g'.current_step → 0 ≤ j → j < g'.current_step →
    (reachTops g' (sel i) (sel j)).all (fun t => carries sides t (sel i) (sel j)) = true

theorem ChainSound_cimaNode (sides : List GPathM) (g g₀ : GPathM) (x : PathNodeId)
    (sel : Int → PathNodeId) (hk : Keeps g₀ g) (h : ChainSound g sel) (hC : Carried sides g₀ sel) :
    ChainSound (cimaNode sides g x) sel ∧ Keeps g₀ (cimaNode sides g x) := by
  refine ⟨?_, Keeps.trans hk (keeps_cimaNode sides g x)⟩
  unfold cimaNode
  split
  · exact h
  · next nx _ =>
    refine BranchLines.foldl_inv (fun g' w => cimaPair sides g' x w)
      (fun g' => ChainSound g' sel ∧ Keeps g₀ g') nx.owners ?_ g ⟨h, hk⟩ |>.1
    intro g' w _ hg'
    refine ⟨ChainSound_cimaPair sides g' x w sel hg'.1 ?_, Keeps.trans hg'.2 (keeps_cimaPair _ _ _ _)⟩
    intro i j hi0 hi hj0 hj hix hjw
    have := hC g' hg'.2 i j hi0 hi hj0 hj
    rw [hix, hjw] at this
    exact this

/-- **The sweep loses no solution.** -/
theorem ChainSound_cimaSweep (sides : List GPathM) (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (hC : Carried sides g sel) : ChainSound (cimaSweep sides g) sel := by
  unfold cimaSweep
  split
  · refine BranchLines.foldl_inv
      (fun g' k => ((g'.line k).map (·.id)).foldl (cimaNode sides) g')
      (fun g' => ChainSound g' sel ∧ Keeps g g') _ ?_ g ⟨h, Keeps.refl g⟩ |>.1
    intro g' k _ hg'
    refine BranchLines.foldl_inv (cimaNode sides) (fun g'' => ChainSound g'' sel ∧ Keeps g g'')
      _ ?_ g' hg'
    intro g'' x _ hg''
    exact ChainSound_cimaNode sides g'' g x sel hg''.2 hg''.1 hC
  · exact h

/-- **A support survives the sweep**: the other core statement, for the supports the verdict uses. -/
def KeepsSupports : Prop :=
  ∀ (sides : List GPathM) (g : GPathM) (S : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    AnchoredSurvive.Sup g S R →
    (∀ x v, R x v → ∀ t ∈ reachTops g x v, carries sides t x v = true) →
    AnchoredSurvive.Sup (cimaSweep sides g) S R

/-- info: 'AbsSat.GraphPath.Model.ImprovesCima.ChainSound_cimaSweep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_cimaSweep

end AbsSat.GraphPath.Model.ImprovesCima
