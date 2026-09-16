import AbsSat.GraphPath.Model.ConservationImproves
import AbsSat.GraphPath.Model.SacFilter

/-!
# Conservation, once, for any filter that keeps the branch

`ConservationImproves` proves the weak-filter machine loses no solution, and `ConservationPins` does
the same work again for the pin prune. A third filter — the conditioned one of `SacFilter` — would
mean a third copy, so this module does the argument once, for an arbitrary

```
F : NodeId → GPathM → GPathM
```

applied before the hard requirements, under two hypotheses:

* `hFpr` — the filtered state is a `Pruned` narrowing, so every shape fact survives;
* `hFcs` — a sound chain whose ids are the assignment's own choices survives the filter.

`chainSound_up_of_pruned` is already stated for an arbitrary narrowing, so the heart of the
conservation law needs nothing new; what the filter touches is the branch invariant and the driver
bookkeeping.

The weak filter satisfies `hFcs` through `weakReqOfCnf_sound`; the conditioned filter satisfies it
with no side condition at all (`SacFilter.ChainSound_filterACn`).

This slice covers the branch invariant and the chain results; the driver bookkeeping follows.
-/

namespace AbsSat.GraphPath.Model.ConservationFilter

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.ConservationImproves (ShapeOk ShapeOk_of_pruned ShapeOk_initSeed
  ShapeOk_addNode ShapeOk_join chainSound_up_of_pruned stepCount_pos)

variable (φ : Cnf) (a : Assign) (F : NodeId → GPathM → GPathM)

/-- The filter, then the hard requirements and the review, then `up`. -/
def upFilteringF (g : GPathM) (d : NodeId) (title : String) : GPathM :=
  upFiltering (F d g) (reqOfCnf φ d) d title

/-- What the filter has to keep: a narrowing that loses no branch chain. -/
abbrev PrunesF : Prop := ∀ d g, Pruned g (F d g)

/-- A sound chain that follows the assignment survives the filter at the node the assignment
picks. The weak filter needs `weakReqOfCnf_sound` for this; the conditioned filter needs nothing. -/
abbrev KeepsBranchF : Prop :=
  ∀ (d : NodeId) (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
    (∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k) →
    d = selOfAssign φ a g.current_step → ChainSound (F d g) sel

-- ============================================================
-- Shape
-- ============================================================

theorem ShapeOk_upFilteringF (hFpr : PrunesF F) (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (h : ShapeOk g) : ShapeOk (upFilteringF φ F g d title) := by
  have hpr : Pruned g (filterAll (F d g) (reqOfCnf φ d)) :=
    Pruned.trans (hFpr d g) (pruned_filterAll _ _)
  have hf := ShapeOk_of_pruned hpr h
  simp only [upFilteringF, upFiltering, GPathM.up]
  split
  · exact ShapeOk_addNode _ d title (by rw [hpr.step_eq]; exact hd) hf
  · exact hf

-- ============================================================
-- The branch invariant
-- ============================================================

/-- The states the driver builds along the assignment's branch. -/
inductive AlongAssignF : GPathM → Prop where
  | seed (title : String) :
      AlongAssignF (GPathM.initSeed (selOfAssign φ a 0) title)
  | up (g : GPathM) (title : String) :
      AlongAssignF g →
      AlongAssignF (upFilteringF φ F g (selOfAssign φ a g.current_step) title)
  | joinL (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₂ : ShapeOk g₂) :
      AlongAssignF g₁ → AlongAssignF (GPathM.join g₁ g₂)
  | joinR (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₁ : ShapeOk g₁) :
      AlongAssignF g₂ → AlongAssignF (GPathM.join g₁ g₂)

theorem shapeOk_of_alongF (hFpr : PrunesF F) (g : GPathM) (h : AlongAssignF φ a F g) :
    ShapeOk g := by
  induction h with
  | seed title => exact ShapeOk_initSeed _ title (selOfAssign_step φ a 0)
  | up g title _ ih =>
    exact ShapeOk_upFilteringF φ F hFpr g _ title (selOfAssign_step φ a g.current_step) ih
  | joinL g₁ g₂ hok h₂ _ ih => exact ShapeOk_join g₁ g₂ hok ih h₂
  | joinR g₁ g₂ hok h₁ _ ih => exact ShapeOk_join g₁ g₂ hok h₁ ih

-- ============================================================
-- The conservation law
-- ============================================================

/-- **The branch's chain survives every state the driver builds**, whatever the filter, as long as
it narrows and keeps the branch. -/
theorem chainSound_alongF (hwf : WF φ) (hFpr : PrunesF F) (hFcs : KeepsBranchF φ a F)
    (g : GPathM) (h : AlongAssignF φ a F g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k := by
  induction h with
  | seed title =>
    refine ⟨fun _ => { id := selOfAssign φ a 0, parent_id := none }, ?_, ?_⟩
    · exact ChainSound_initSeed _ title (selOfAssign_step φ a 0)
    · intro k hlo hhi
      rw [initSeed_current] at hhi
      have hk : k = 0 := by omega
      subst hk
      rfl
  | up g title hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    obtain ⟨sel', hs', hcur, hids'⟩ :=
      chainSound_up_of_pruned φ a hwf g _ (hFpr _ g) (shapeOk_of_alongF φ a F hFpr g hal) sel
        (hFcs _ g sel hsel hids rfl) hids title
    exact ⟨sel', hs', fun k hk0 hk => hids' k hk0 (lt_of_lt_of_eq hk hcur)⟩
  | joinL g₁ g₂ hok h₂ _ ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_left g₁ g₂).step_eq] at hk; exact hk)⟩
  | joinR g₁ g₂ hok h₁ _ ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_right g₁ g₂ hok).step_eq] at hk; exact hk)⟩

theorem isValid_alongF (hwf : WF φ) (hFpr : PrunesF F) (hFcs : KeepsBranchF φ a F)
    (g : GPathM) (h : AlongAssignF φ a F g) : isValid g = true := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongF φ a F hwf hFpr hFcs g h
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

theorem inhabited_alongF (hwf : WF φ) (hFpr : PrunesF F) (hFcs : KeepsBranchF φ a F)
    (g : GPathM) (h : AlongAssignF φ a F g) : ∃ sel, ChainSound g sel := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongF φ a F hwf hFpr hFcs g h
  exact ⟨sel, hsel⟩

-- ============================================================
-- The conditioned filter as an instance
-- ============================================================

open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf weakReqOfCnf_sound)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeakAll)
open AbsSat.GraphPath.Model.ConservationImproves (pruned_filterWeakAll ChainSound_filterWeakAll)
open AbsSat.GraphPath.Model.SacFilter (filterACn pruned_filterACn ChainSound_filterACn)

/-- The weak filter of `CnfMapImproves`, then `n` passes of the conditioned filter. -/
def Fsac (n : Nat) (d : NodeId) (g : GPathM) : GPathM :=
  filterACn n (filterWeakAll g (weakReqOfCnf φ d))

theorem prunes_Fsac (n : Nat) : PrunesF (Fsac φ n) := fun _d g =>
  Pruned.trans (pruned_filterWeakAll g _) (pruned_filterACn n _)

/-- The branch survives both filters: the weak one by `weakReqOfCnf_sound`, the conditioned one for
free. -/
theorem keepsBranch_Fsac (hsat : Sat a φ) (n : Nat) : KeepsBranchF φ a (Fsac φ n) := by
  intro d g sel hsel hids hd
  refine ChainSound_filterACn n _ sel (ChainSound_filterWeakAll _ g sel hsel ?_)
  intro e he k hk0 hk hke
  rw [hids k hk0 hk, hke]
  exact weakReqOfCnf_sound φ a hsat g.current_step e (by rw [← hd]; exact he)

/-- **The machine with the conditioned filter keeps the branch.** Along a satisfying assignment,
the selection it names is a sound chain of every state the driver builds, for any number of
conditioned passes. -/
theorem chainSound_alongSac (hwf : WF φ) (hsat : Sat a φ) (n : Nat) (g : GPathM)
    (h : AlongAssignF φ a (Fsac φ n) g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k :=
  chainSound_alongF φ a _ hwf (prunes_Fsac φ n) (keepsBranch_Fsac φ a hsat n) g h

theorem isValid_alongSac (hwf : WF φ) (hsat : Sat a φ) (n : Nat) (g : GPathM)
    (h : AlongAssignF φ a (Fsac φ n) g) : isValid g = true :=
  isValid_alongF φ a _ hwf (prunes_Fsac φ n) (keepsBranch_Fsac φ a hsat n) g h

/-- info: 'AbsSat.GraphPath.Model.ConservationFilter.chainSound_alongF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_alongF

/-- info: 'AbsSat.GraphPath.Model.ConservationFilter.chainSound_alongSac' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_alongSac

end AbsSat.GraphPath.Model.ConservationFilter
