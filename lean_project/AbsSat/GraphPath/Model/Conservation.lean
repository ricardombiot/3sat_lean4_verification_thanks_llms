-- lean_project/AbsSat/GraphPath/Model/Conservation.lean
import AbsSat.GraphPath.Model.L7
import AbsSat.GraphPath.Model.AddNode
import AbsSat.GraphPath.Model.JoinSound
import AbsSat.GraphPath.Model.PickInduction

/-!
# Conservation: the machine keeps every solution it started with

Every attempt so far has tried to prove an **existence** — that a valid state
carries *a* co-owned chain — and each one hit the same wall from a different
side (`PairwiseOwned`, `PickValid`, `support` at distance two, `CoreCovers`,
`share`). The wall is real: producing a witness out of a set built by
successive prunings is exactly the hard part.

The author's reading of his own construction says the statement is of a
different kind:

> the valid set contains, abstractly, **not one solution but all of them**

That is not an existence claim. It is a **conservation law**, and conservation
laws are proved by induction over the construction — which is how this machine
is built.

## The reformulation

Instead of "∃ a chain", the statement is: **for every assignment satisfying φ,
the selection that assignment names is a sound chain in every state the machine
builds along that assignment's branch.**

The witness is no longer something the proof must produce. It comes from
outside, handed over by the assignment. The machine never has to *build* a
chain — it only has to **not destroy** one, and every non-destruction lemma
was already proved, for other purposes, in the four modules this one imports:

| step | lemma | where |
|---|---|---|
| seed | `ChainSound_initSeed` | `AddNode.lean` |
| filter + grow | `ChainSound_upFiltering` | `AddNode.lean` |
| join | `ChainSound_join_left` / `_right` | `JoinSound.lean` |

and the hypothesis the filter step needs — *the selection satisfies every
requirement* — is `CnfSel.reqSat_selOfAssign`, proved for the map side today.

## What falls out for free

`isValid_of_ChainG` says a graph carrying a chain inside its global owners is
valid. So the chain's survival **proves the validity**: the machine cannot
invalidate a state that still holds a solution. Validity is not an extra
obligation here, it is a consequence.

## What this does and does not close

It closes the **decision problem's completeness**: if `φ` is satisfiable, the
state along a satisfying assignment's branch stays valid to the end and denotes
something. With `L7.sat_of_inhabited` — the other direction, proved earlier —
the machine's validity becomes *equivalent* to satisfiability.

It does **not** prove `Supported` ("no zombies"). A reader that checks validity
after each pick never gets stuck, because by conservation an invalid result
means no solution passes through that pick; a reader that must never backtrack
still needs `Supported`, which stays open.
-/

namespace AbsSat.GraphPath.Model.Conservation

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable

variable (φ : Cnf) (a : Assign)

/-- The machine's run **along one assignment's branch**: at every step it takes
the map node that assignment names. Joins may bring in any other reachable
branch — a join only grows the graph, so it cannot cost the chain. -/
inductive AlongAssign : GPathM → Prop where
  | seed (title : String) :
      AlongAssign (GPathM.initSeed (selOfAssign φ a 0) title)
  | up (g : GPathM) (title : String)
      (hlo : 0 ≤ g.current_step) (hhi : g.current_step < stepCount φ) :
      AlongAssign g →
      AlongAssign (GPathM.upFiltering g
        (reqOfCnf φ (selOfAssign φ a g.current_step))
        (selOfAssign φ a g.current_step) title)
  | joinL (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₂ : MapReachable φ g₂) :
      AlongAssign g₁ → AlongAssign (GPathM.join g₁ g₂)
  | joinR (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₁ : MapReachable φ g₁) :
      AlongAssign g₂ → AlongAssign (GPathM.join g₁ g₂)

/-- A run along an assignment's branch is a run of the machine on the map. -/
theorem mapReachable_of_alongAssign (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) : MapReachable φ g := by
  induction h with
  | seed title =>
    exact MapReachable.seed _ title (selOfAssign_step φ a 0)
      (by rw [selOfAssign_step]; exact selOfAssign_onMap φ a hsat 0 (by omega) hzero)
  | up g title hlo hhi _ ih =>
    exact MapReachable.up g _ title (selOfAssign_step φ a g.current_step)
      (by rw [selOfAssign_step]; exact selOfAssign_onMap φ a hsat _ hlo hhi) ih
  | joinL g₁ g₂ hok h₂ _ ih => exact MapReachable.join g₁ g₂ hok ih h₂
  | joinR g₁ g₂ hok h₁ _ ih => exact MapReachable.join g₁ g₂ hok h₁ ih

/-- **The conservation law.** Along a satisfying assignment's branch, the
selection that assignment names is a sound chain of every state the machine
builds, and its map ids are exactly the assignment's own choices. -/
theorem chainSound_along (hwf : WF φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
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
    have hreach : Reachable (reqOfCnf φ) g :=
      reachable_of_mapReachable φ hwf g
        (mapReachable_of_alongAssign φ a hsat hzero g hal)
    -- the selection satisfies every requirement of the node about to be added
    have hreqs : ∀ req ∈ reqOfCnf φ (selOfAssign φ a g.current_step),
        0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req := by
      intro req hreq hr0 hr1
      rw [hids req.step hr0 hr1]
      exact reqSat_selOfAssign φ hwf a g.current_step req hreq
    have hpr := pruned_filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step))
    have hfil : ChainSound (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step))) sel :=
      ChainSound_filterAll g _ sel hsel hreqs
    -- the chain's survival *is* the validity: the machine cannot invalidate a
    -- state that still holds a solution
    have hvalid : isValid (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
        = true := PickInduction.isValid_of_ChainG _ sel hfil.chain
    have hd : (selOfAssign φ a g.current_step).step
        = (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step))).current_step := by
      rw [hpr.step_eq, selOfAssign_step]
    have hbelow := Certifies.nodes_below_of_pruned hpr (steps_below_current (reqOfCnf φ) hreach)
    have hmok := MachineOk_of_pruned hpr (Certifies.MachineOk_reachable (reqOfCnf φ) g hreach)
    refine ⟨extend (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
      (selOfAssign φ a g.current_step) sel, ?_, ?_⟩
    · exact ChainSound_upFiltering g _ _ title hvalid hd hbelow hmok sel hsel hreqs
    · intro k hk0 hk
      have hshape : upFiltering g (reqOfCnf φ (selOfAssign φ a g.current_step))
          (selOfAssign φ a g.current_step) title
          = addNode (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
            (selOfAssign φ a g.current_step) title := by
        simp only [upFiltering, GPathM.up, hvalid, if_pos]
      rw [hshape, addNode_current] at hk
      rw [hpr.step_eq] at hk
      if he : k = g.current_step then
        have hextend : extend (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
            (selOfAssign φ a g.current_step) sel g.current_step
            = newPid (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
              (selOfAssign φ a g.current_step) := by
          simp only [extend, if_pos hpr.step_eq.symm]
        rw [he, hextend]
        rfl
      else
        rw [extend_below (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
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
theorem isValid_along (hwf : WF φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) : isValid g = true := by
  obtain ⟨sel, hsel, _⟩ := chainSound_along φ a hwf hsat hzero g h
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

/-- **Completeness of the verdict.** If `φ` is satisfiable, the state along a
satisfying assignment's branch denotes something — so the machine's set is
non-empty, which is what the SAT answer rests on. -/
theorem inhabited_along (hwf : WF φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) :
    AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨sel, hsel, _⟩ := chainSound_along φ a hwf hsat hzero g h
  exact ⟨pathOf sel g, sel, hsel.chain.1, hsel.chain.2.1, rfl⟩

-- ============================================================
-- The branch exists, and it runs to the end of the map
-- ============================================================

/-- The filtered graph at the next step is valid — again because the chain
survives the filter, not because anything extra was assumed. -/
theorem isValid_filterAll_along (hwf : WF φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) :
    isValid (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step))) = true := by
  obtain ⟨sel, hsel, hids⟩ := chainSound_along φ a hwf hsat hzero g h
  have hreqs : ∀ req ∈ reqOfCnf φ (selOfAssign φ a g.current_step),
      0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req := by
    intro req hreq hr0 hr1
    rw [hids req.step hr0 hr1]
    exact reqSat_selOfAssign φ hwf a g.current_step req hreq
  exact PickInduction.isValid_of_ChainG _ sel
    (ChainSound_filterAll g _ sel hsel hreqs).chain

theorem current_step_up_along (hwf : WF φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ)
    (g : GPathM) (h : AlongAssign φ a g) (title : String) :
    (GPathM.upFiltering g (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title).current_step = g.current_step + 1 := by
  have hvalid := isValid_filterAll_along φ a hwf hsat hzero g h
  have hpr := pruned_filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step))
  have hshape : GPathM.upFiltering g (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title
      = addNode (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) title := by
    simp only [upFiltering, GPathM.up, hvalid, if_pos]
  rw [hshape, addNode_current, hpr.step_eq]

/-- **The branch is walkable to the end.** For a satisfying assignment there is
a state along its branch at every length up to the map's, built by the
machine's own operations. -/
theorem alongAssign_exists (hwf : WF φ) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ) :
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
    refine ⟨GPathM.upFiltering g (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) "", AlongAssign.up g "" (by omega) (by omega) hal, ?_⟩
    rw [current_step_up_along φ a hwf hsat hzero g hal, hcs]
    omega

/-- **The completeness of the verdict, in its final form.** A satisfiable
formula gives a state the machine's own operations reach, spanning the whole
map, still valid, and denoting a solution. -/
theorem exists_full_valid_state (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) :
    ∃ g, AlongAssign φ a g ∧ g.current_step = stepCount φ ∧ isValid g = true ∧
      AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨g, hal, hcs⟩ := alongAssign_exists φ a hwf hsat hzero
    (stepCount φ - 1).toNat (by omega)
  refine ⟨g, hal, by omega, isValid_along φ a hwf hsat hzero g hal,
    inhabited_along φ a hwf hsat hzero g hal⟩

/-- info: 'AbsSat.GraphPath.Model.Conservation.exists_full_valid_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_full_valid_state

/-- **The two directions, side by side.**

*Soundness* (v49's link 4, proved in `L7`): a state the machine holds that
denotes something says the formula is satisfiable.

*Completeness* (here): a satisfiable formula keeps the machine's state alive —
along the satisfying assignment's own branch it stays valid and keeps denoting.

Together: **the machine's set being non-empty is exactly satisfiability.** The
decision problem is closed on both sides, without ever proving that a valid
state must produce a chain — the chain is supplied by the assignment, and the
machine only has to fail to destroy it. -/
theorem sound_and_complete (hwf : WF φ) (hzero : (0 : Int) < stepCount φ) :
    (∀ g, MapReachable φ g → g.current_step = stepCount φ →
      AbsSat.GraphPath.Model.Inhabited g → Satisfiable φ)
    ∧ (∀ b : Assign, Sat b φ → ∀ g, AlongAssign φ b g →
      AbsSat.GraphPath.Model.Inhabited g ∧ isValid g = true) :=
  ⟨fun g hmr hcs hinh => L7.sat_of_inhabited φ hwf g hmr hcs hinh,
   fun b hb g hal =>
     ⟨inhabited_along φ b hwf hb hzero g hal, isValid_along φ b hwf hb hzero g hal⟩⟩

/-- info: 'AbsSat.GraphPath.Model.Conservation.sound_and_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sound_and_complete

/-- info: 'AbsSat.GraphPath.Model.Conservation.chainSound_along' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_along

/-- info: 'AbsSat.GraphPath.Model.Conservation.inhabited_along' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inhabited_along

end AbsSat.GraphPath.Model.Conservation
