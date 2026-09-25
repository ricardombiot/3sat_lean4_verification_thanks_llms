-- lean/improves_bin/AbsSatBin/GraphPath/Model/Conservation.lean
import AbsSatBin.GraphPath.Model.L7
import AbsSatBin.GraphPath.Model.AddNode
import AbsSatBin.GraphPath.Model.JoinSound
import AbsSatBin.GraphPath.Model.PickInduction

/-!
# Conservation on the bin map: the machine keeps every solution — **rewritten**

As in `lean_project`: for every assignment satisfying `φ`, the selection it names is a sound chain
in every state the machine builds along that assignment's branch. The machine never builds a
chain; it only fails to destroy the one the assignment hands it.

| step | lemma | where |
|---|---|---|
| seed | `ChainSound_initSeed` | `AddNode` |
| filter + grow (+ review if a window was skipped) | `ChainSound_upFiltering` | `AddNode` |
| join | `ChainSound_join_left` / `_right` | `JoinSound` |

**What the bin map adds.** `ChainSound_upFiltering` now also asks that the chain's extension into
the new row is not a prohibited window. The extension is `(d, sel(k−1), parent of sel(k−1))`;
by the parent coherence of the state (`ParentId.PMP`) and the chain's root shape it is exactly
`pidOfAssign φ a k` (`extendPid_eq_pidOfAssign`), and a satisfying assignment's window is never
prohibited (`CnfSelBin.pidOfAssign_not_prohibited`). That is the one place `Sat` is used.
-/

namespace AbsSatBin.GraphPath.Model.Conservation

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.MapReachable

variable (φ : Cnf) (a : Assign)

/-- The machine's run **along one assignment's branch**: at every step it takes the map node that
assignment names. Joins may bring in any other reachable branch. -/
inductive AlongAssign : GPathM → Prop where
  | seed (title : String) :
      AlongAssign (GPathM.initSeed (selOfAssign φ a 0) title)
  | up (g : GPathM) (title : String)
      (hlo : 0 ≤ g.current_step) (hhi : g.current_step < stepCount φ) :
      AlongAssign g →
      AlongAssign (GPathM.upFiltering g
        (reqOf φ (selOfAssign φ a g.current_step))
        (selOfAssign φ a g.current_step) title (isProhibited φ))
  | joinL (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₂ : MapReachable φ g₂) :
      AlongAssign g₁ → AlongAssign (GPathM.join g₁ g₂)
  | joinR (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₁ : MapReachable φ g₁) :
      AlongAssign g₂ → AlongAssign (GPathM.join g₁ g₂)

/-- A run along an assignment's branch is a run of the machine on the map. -/
theorem mapReachable_of_alongAssign (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) : MapReachable φ g := by
  induction h with
  | seed title =>
    exact MapReachable.seed _ title (selOfAssign_step φ a 0)
      (by rw [selOfAssign_step]; exact selOfAssign_onMap φ a 0 (by omega) hzero)
  | up g title hlo hhi _ ih =>
    exact MapReachable.up g _ title (selOfAssign_step φ a g.current_step)
      (by rw [selOfAssign_step]; exact selOfAssign_onMap φ a _ hlo hhi) ih
  | joinL g₁ g₂ hok h₂ _ ih => exact MapReachable.join g₁ g₂ hok ih h₂
  | joinR g₁ g₂ hok h₁ _ ih => exact MapReachable.join g₁ g₂ hok h₁ ih

/-- The UP advances the step by one on a valid filtered state, reviewed or not. -/
theorem current_step_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) (hvalid : isValid (filterAll g reqs) = true) :
    (upFiltering g reqs d title forb).current_step = g.current_step + 1 := by
  have hpr := pruned_filterAll g reqs
  simp only [upFiltering, GPathM.up, hvalid, if_true]
  split
  · rw [(pruned_review _).step_eq, addNode_current, hpr.step_eq]
  · rw [addNode_current, hpr.step_eq]

/-- **The chain's extension is the assignment's own window.** -/
theorem extendPid_eq_pidOfAssign (g : GPathM) (sel : Int → PathNodeId)
    (hchain : IsChain g sel) (hpmp : ParentId.PMP g)
    (hroot : (sel 0).parent_id = none)
    (hids : ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k)
    (h0 : 0 ≤ g.current_step) :
    extendPid g (selOfAssign φ a g.current_step) sel = pidOfAssign φ a g.current_step := by
  unfold extendPid pidOfAssign
  by_cases hpos : 0 < g.current_step
  · rw [if_pos hpos]
    apply ParentId.pathNodeId_ext
    · rfl
    · show some (sel (g.current_step - 1)).id = _
      rw [if_pos hpos, hids _ (by omega) (by omega)]
    · show (sel (g.current_step - 1)).parent_id = _
      by_cases h1 : 1 < g.current_step
      · rw [if_pos h1]
        have := ParentId.parentId_coherent g hpmp sel hchain (g.current_step - 2) (by omega)
          (by omega)
        rw [show g.current_step - 2 + 1 = g.current_step - 1 by omega] at this
        rw [this, hids _ (by omega) (by omega)]
      · rw [if_neg h1, show g.current_step - 1 = 0 by omega]
        exact hroot
  · rw [if_neg hpos]
    have hz : g.current_step = 0 := by omega
    apply ParentId.pathNodeId_ext
    · rfl
    · simp only; rw [if_neg (by omega)]
    · simp only; rw [if_neg (by omega)]

/-- **The conservation law.** Along a satisfying assignment's branch, the selection that
assignment names is a sound chain of every state the machine builds, and its map ids are exactly
the assignment's own choices. -/
theorem chainSound_along (hbd : Bounded φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k := by
  induction h with
  | seed title =>
    refine ⟨fun _ => { id := selOfAssign φ a 0, parent_id := none }, ?_, ?_⟩
    · exact ChainSound_initSeed _ title (selOfAssign_step φ a 0)
    · intro k hlo hhi
      rw [initSeed_current] at hhi
      have : k = 0 := by omega
      subst this
      rfl
  | up g title hlo hhi hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    have hreach : Reachable (reqOf φ) (isProhibited φ) g :=
      reachable_of_mapReachable φ hbd g (mapReachable_of_alongAssign φ a hzero g hal)
    have hreqs : ∀ req ∈ reqOf φ (selOfAssign φ a g.current_step),
        0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req := by
      intro req hreq hr0 hr1
      rw [hids req.step hr0 hr1]
      exact reqSat_selOfAssign φ hbd a g.current_step req hreq
    have hpr := pruned_filterAll g (reqOf φ (selOfAssign φ a g.current_step))
    have hfil : ChainSound (filterAll g (reqOf φ (selOfAssign φ a g.current_step))) sel :=
      ChainSound_filterAll g _ sel hsel hreqs
    have hvalid : isValid (filterAll g (reqOf φ (selOfAssign φ a g.current_step))) = true :=
      PickInduction.isValid_of_ChainG _ sel hfil.chain
    have hd : (selOfAssign φ a g.current_step).step
        = (filterAll g (reqOf φ (selOfAssign φ a g.current_step))).current_step := by
      rw [hpr.step_eq, selOfAssign_step]
    have hbelow := Certifies.nodes_below_of_pruned hpr
      (steps_below_current (reqOf φ) (isProhibited φ) hreach)
    have hmok := MachineOk_of_pruned hpr
      (Certifies.MachineOk_reachable (reqOf φ) (isProhibited φ) g hreach)
    -- the extension is the assignment's own window, which is not prohibited
    have hf : isProhibited φ (extendPid (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) sel) = false := by
      have hpmp := ParentId.PMP_filterAll (reqOf φ) (isProhibited φ) g
        (reqOf φ (selOfAssign φ a g.current_step)) hreach
      have heq := extendPid_eq_pidOfAssign φ a _ sel hfil.chain.1 hpmp hsel.root_shape.1
        (by intro k hk0 hk; rw [hpr.step_eq] at hk; exact hids k hk0 hk) (by rw [hpr.step_eq]; exact hlo)
      rw [hpr.step_eq] at heq
      rw [heq]
      exact pidOfAssign_not_prohibited φ a hsat _
    refine ⟨extend (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
      (selOfAssign φ a g.current_step) sel, ?_, ?_⟩
    · exact ChainSound_upFiltering g _ _ title _ hvalid hd hbelow hmok sel hsel hreqs hf
    · intro k hk0 hk
      rw [current_step_upFiltering g _ _ title _ hvalid] at hk
      if he : k = g.current_step then
        have hextend : extend (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
            (selOfAssign φ a g.current_step) sel g.current_step
            = extendPid (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
              (selOfAssign φ a g.current_step) sel := by
          simp only [extend, if_pos hpr.step_eq.symm]
        rw [he, hextend, extendPid_mapId]
      else
        rw [extend_below (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
          (selOfAssign φ a g.current_step) sel k (by rw [hpr.step_eq]; omega)]
        exact hids k hk0 (by omega)
  | joinL g₁ g₂ hok h₂ hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_left g₁ g₂).step_eq] at hk; exact hk)⟩
  | joinR g₁ g₂ hok h₁ hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_right g₁ g₂ hok).step_eq] at hk; exact hk)⟩

-- ============================================================
-- What falls out
-- ============================================================

/-- **The machine cannot invalidate a state that still holds a solution.** -/
theorem isValid_along (hbd : Bounded φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) : isValid g = true := by
  obtain ⟨sel, hsel, _⟩ := chainSound_along φ a hbd hsat hzero g h
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

theorem inhabited_along (hbd : Bounded φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) :
    AbsSatBin.GraphPath.Model.Inhabited g := by
  obtain ⟨sel, hsel, _⟩ := chainSound_along φ a hbd hsat hzero g h
  exact ⟨pathOf sel g, sel, hsel.chain.1, hsel.chain.2.1, rfl⟩

theorem isValid_filterAll_along (hbd : Bounded φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) (g : GPathM) (h : AlongAssign φ a g) :
    isValid (filterAll g (reqOf φ (selOfAssign φ a g.current_step))) = true := by
  obtain ⟨sel, hsel, hids⟩ := chainSound_along φ a hbd hsat hzero g h
  have hreqs : ∀ req ∈ reqOf φ (selOfAssign φ a g.current_step),
      0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req := by
    intro req hreq hr0 hr1
    rw [hids req.step hr0 hr1]
    exact reqSat_selOfAssign φ hbd a g.current_step req hreq
  exact PickInduction.isValid_of_ChainG _ sel (ChainSound_filterAll g _ sel hsel hreqs).chain

theorem current_step_up_along (hbd : Bounded φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) (g : GPathM) (h : AlongAssign φ a g) (title : String) :
    (GPathM.upFiltering g (reqOf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title (isProhibited φ)).current_step
        = g.current_step + 1 :=
  current_step_upFiltering g _ _ title _ (isValid_filterAll_along φ a hbd hsat hzero g h)

/-- **The branch is walkable to the end.** -/
theorem alongAssign_exists (hbd : Bounded φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ) :
    ∀ n : Nat, (n : Int) < stepCount φ →
      ∃ g, AlongAssign φ a g ∧ g.current_step = (n : Int) + 1 := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨GPathM.initSeed (selOfAssign φ a 0) "", AlongAssign.seed _,
      by rw [initSeed_current]; omega⟩
  | succ m ih =>
    intro hlt
    obtain ⟨g, hal, hcs⟩ := ih (by omega)
    refine ⟨GPathM.upFiltering g (reqOf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) "" (isProhibited φ),
      AlongAssign.up g "" (by omega) (by omega) hal, ?_⟩
    rw [current_step_up_along φ a hbd hsat hzero g hal, hcs]
    omega

/-- **The completeness of the verdict, in its final form.** -/
theorem exists_full_valid_state (hbd : Bounded φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) :
    ∃ g, AlongAssign φ a g ∧ g.current_step = stepCount φ ∧ isValid g = true ∧
      AbsSatBin.GraphPath.Model.Inhabited g := by
  obtain ⟨g, hal, hcs⟩ := alongAssign_exists φ a hbd hsat hzero
    (stepCount φ - 1).toNat (by omega)
  refine ⟨g, hal, by omega, isValid_along φ a hbd hsat hzero g hal,
    inhabited_along φ a hbd hsat hzero g hal⟩

/-- **The two directions, side by side.** -/
theorem sound_and_complete (hbd : Bounded φ) (hzero : (0 : Int) < stepCount φ) :
    (∀ g, MapReachable φ g → g.current_step = stepCount φ →
      AbsSatBin.GraphPath.Model.Inhabited g → Satisfiable φ)
    ∧ (∀ b : Assign, Sat b φ → ∀ g, AlongAssign φ b g →
      AbsSatBin.GraphPath.Model.Inhabited g ∧ isValid g = true) :=
  ⟨fun g hmr hcs hinh => L7.sat_of_inhabited φ hbd g hmr hcs hinh,
   fun b hb g hal =>
     ⟨inhabited_along φ b hbd hb hzero g hal, isValid_along φ b hbd hb hzero g hal⟩⟩

/-- info: 'AbsSatBin.GraphPath.Model.Conservation.chainSound_along' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_along

/-- info: 'AbsSatBin.GraphPath.Model.Conservation.exists_full_valid_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_full_valid_state

/-- info: 'AbsSatBin.GraphPath.Model.Conservation.sound_and_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sound_and_complete

end AbsSatBin.GraphPath.Model.Conservation
