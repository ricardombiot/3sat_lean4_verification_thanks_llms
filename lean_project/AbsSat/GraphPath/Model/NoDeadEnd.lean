-- lean_project/AbsSat/GraphPath/Model/NoDeadEnd.lean
import AbsSat.GraphPath.Model.EmptinessReduction
import AbsSat.GraphPath.Model.NodeInvariant
import AbsSat.GraphPath.Model.Parents
import AbsSat.GraphPath.Model.SelfOwn
import AbsSat.GraphPath.Model.GownersNodes
import AbsSat.GraphPath.Model.Sons
import AbsSat.GraphPath.Model.LocalContradiction

/-!
# No dead ends

A state's subset is `denotS g`, the paths of its `ChainSound` chains. This module states,
over the current machine definitions only, the one-step property that builds such a chain
from the top step down:

* `SoundFrom g sel lo` — the picks of `sel` on the steps `lo .. current_step - 1` satisfy
  every condition of `ChainSound` restricted to those steps: a node at each step, parent and
  son links between consecutive picks, pairwise ownership, global ownership, self-ownership
  and the root shape.
* `TopAnchor g` — some single pick at the top step satisfies the conditions.
* `NoDeadEnd g` — every such partial chain with `0 < lo` extends by one pick at `lo - 1`.
* `FilterNoDeadEnd φ` — `NoDeadEnd` after every filter the driver performs.

Proved here:

* `chainSound_iff_soundFrom_zero` — a partial chain reaching step 0 is a `ChainSound` chain.
* `nonempty_of_noDeadEnd` — `TopAnchor` and `NoDeadEnd` give a non-empty subset.
* `topAnchor_of`, `topAnchor_filterAll` — **the top anchor always exists** after a valid
  filter of a reachable state: `isValid` gives a global owner at the top step, `GN` makes it a
  node, `isValidNode` and `OOS` make it own itself, `Shape` and `RootAtZero` give its root shape.
* `SendExact_of_FilterNoDeadEnd` — `FilterNoDeadEnd` gives `SendExact`.

`FilterNoDeadEnd` itself is not proved here.
-/

namespace AbsSat.GraphPath.Model.NoDeadEnd

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.SubsetSemantics
open AbsSat.GraphPath.Model.EmptinessReduction

/-- `sel` with the pick at step `j` replaced by `c`. -/
def upd (sel : Int → PathNodeId) (j : Int) (c : PathNodeId) : Int → PathNodeId :=
  fun i => if i = j then c else sel i

/-- The picks on steps `lo .. current_step - 1` satisfy `ChainSound`'s conditions on
those steps. -/
structure SoundFrom (g : GPathM) (sel : Int → PathNodeId) (lo : Int) : Prop where
  node : ∀ k, lo ≤ k → k < g.current_step → (g.node? (sel k)).isSome ∧ (sel k).id.step = k
  parent_link : ∀ k, lo ≤ k → k + 1 < g.current_step →
    sel k ∈ ((g.node? (sel (k + 1))).map PNodeM.parents).getD []
  owned : ∀ i j, lo ≤ i → lo ≤ j → i < g.current_step → j < g.current_step → i ≠ j →
    sel i ∈ ownersAt (ownersOf g (sel j)) i
  gowner : ∀ k, lo ≤ k → k < g.current_step → sel k ∈ g.gowners
  self_owned : ∀ k, lo ≤ k → k < g.current_step → sel k ∈ ownersOf g (sel k)
  son_link : ∀ k, lo ≤ k → k + 1 < g.current_step → sel (k + 1) ∈ sonsOf g (sel k)
  root_shape : ∀ k, lo ≤ k → k < g.current_step → ((sel k).parent_id = none ↔ k = 0)

/-- A single pick at the top step satisfies the conditions. -/
def TopAnchor (g : GPathM) : Prop :=
  ∃ q, SoundFrom g (fun _ => q) (g.current_step - 1)

/-- **No dead ends.** Every partial chain from the top step down to `lo > 0` extends by
one pick at `lo - 1`. -/
def NoDeadEnd (g : GPathM) : Prop :=
  ∀ sel lo, 0 < lo → lo ≤ g.current_step - 1 → SoundFrom g sel lo →
    ∃ c, SoundFrom g (upd sel (lo - 1) c) (lo - 1)

/-- **The statement for the machine**: after every filter the driver performs on a
reachable, non-empty state, the filtered state has no dead ends. -/
def FilterNoDeadEnd (φ : Cnf) : Prop :=
  ∀ (g : GPathM) (d : NodeId), MapReachable φ g → isValid g = true → (∃ p, denotS g p) →
    d.step = g.current_step → d ∈ mapNodes φ d.step →
    isValid (filterAll g (reqOfCnf φ d)) = true →
    NoDeadEnd (filterAll g (reqOfCnf φ d))

-- ============================================================
-- The statement is the right one
-- ============================================================

/-- A partial chain that reaches step 0 is exactly a `ChainSound` chain. -/
theorem chainSound_iff_soundFrom_zero (g : GPathM) (sel : Int → PathNodeId)
    (hpos : 0 < g.current_step) : ChainSound g sel ↔ SoundFrom g sel 0 := by
  constructor
  · intro h
    obtain ⟨⟨hn, hp⟩, how, hgo⟩ := h.chain
    refine ⟨hn, hp, how, hgo, h.self_owned, h.son_link, fun k h0 hk => ⟨fun hnone => ?_, ?_⟩⟩
    · exact Decidable.byContradiction fun hne => h.root_shape.2 k (by omega) hk hnone
    · intro hk0; subst hk0; exact h.root_shape.1
  · intro h
    refine ⟨⟨⟨h.node, h.parent_link⟩, h.owned, h.gowner⟩, h.self_owned, h.son_link,
      (h.root_shape 0 (Int.le_refl 0) hpos).mpr rfl, fun k hk hkc hnone => ?_⟩
    have := (h.root_shape k (by omega) hkc).mp hnone
    omega

/-- Descending with no dead ends reaches step 0, keeping every pick already made. -/
theorem descend (g : GPathM) (hnd : NoDeadEnd g) (m : Nat) :
    ∀ (sel : Int → PathNodeId) (lo : Int), lo.toNat ≤ m → 0 ≤ lo →
      lo ≤ g.current_step - 1 → SoundFrom g sel lo →
      ∃ sel', (∀ i, lo ≤ i → sel' i = sel i) ∧ SoundFrom g sel' 0 := by
  induction m with
  | zero =>
    intro sel lo hm hlo _ hs
    have hEq : lo = 0 := by omega
    subst hEq
    exact ⟨sel, fun _ _ => rfl, hs⟩
  | succ m ih =>
    intro sel lo hm hlo hlohi hs
    if hpos : 0 < lo then
      obtain ⟨c, hc⟩ := hnd sel lo hpos hlohi hs
      obtain ⟨sel', hagree, hs'⟩ :=
        ih (upd sel (lo - 1) c) (lo - 1) (by omega) (by omega) (by omega) hc
      refine ⟨sel', fun i hi => ?_, hs'⟩
      rw [hagree i (by omega)]
      unfold upd
      rw [if_neg (by omega)]
    else
      have hEq : lo = 0 := by omega
      subst hEq
      exact ⟨sel, fun _ _ => rfl, hs⟩

/-- **No dead ends and a top anchor give a non-empty subset.** -/
theorem nonempty_of_noDeadEnd (g : GPathM) (hpos : 0 < g.current_step)
    (ha : TopAnchor g) (hnd : NoDeadEnd g) : ∃ p, denotS g p := by
  obtain ⟨q, hq⟩ := ha
  obtain ⟨sel, _, hs⟩ := descend g hnd (g.current_step - 1).toNat (fun _ => q)
    (g.current_step - 1) (Nat.le_refl _) (by omega) (Int.le_refl _) hq
  exact ⟨pathOf sel g, sel, (chainSound_iff_soundFrom_zero g sel hpos).mpr hs, rfl⟩

-- ============================================================
-- The top anchor
-- ============================================================

/-- **A top anchor exists** in a valid state with at least one step whose nodes pass
`isValidNode`, whose global owners are nodes, and which satisfies `OOS`, `Shape` and
`RootAtZero`. -/
theorem topAnchor_of (h : GPathM) (hv : isValid h = true) (hpos : 0 < h.current_step)
    (hgn : GownersNodes.GN h) (hoos : SelfOwn.OOS h) (hshape : Parents.Shape h)
    (hrz : Sons.RootAtZero h)
    (hval : ∀ q d, h.node? q = some d → isValidNode h d = true) : TopAnchor h := by
  -- a global owner at the top step
  have hent := hasStepEntry_of_isValid h hv (h.current_step - 1) (by omega) (by omega)
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨q, hq, hqs⟩ := hent
  -- it is a node
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff h q).mp (hgn q hq))
  have hdmem : d ∈ h.nodes := List.mem_of_find?_eq_some hd
  have hdid : d.id = q := node?_id_eq h q d hd
  -- it owns itself: its owner at its own step can only be itself
  have hself : q ∈ ownersOf h q := by
    have hown := LocalContradiction.ownersOk_of_isValidNode h d (hval q d hd)
      (h.current_step - 1) (by omega) (by omega)
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hown
    obtain ⟨o, ho, hos⟩ := hown
    have hoq : o = d.id := hoos d hdmem o ho (by rw [hos, hdid, hqs])
    simp only [ownersOf, hd]
    rw [← hoq.trans hdid]
    exact ho
  refine ⟨q, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro k hk1 hk2
    have hk : k = h.current_step - 1 := by omega
    subst hk
    refine ⟨?_, hqs⟩
    simp only [hd, Option.isSome_some]
  · intro k hk1 hk2; omega
  · intro i j hi hj hi2 hj2 hne; omega
  · intro _ _ _; exact hq
  · intro _ _ _; exact hself
  · intro k hk1 hk2; omega
  · intro k hk1 hk2
    have hk : k = h.current_step - 1 := by omega
    subst hk
    constructor
    · intro hnone
      exact Decidable.byContradiction fun hne =>
        hshape.notroot d hdmem (by rw [hdid, hqs]; omega) (by rw [hdid]; exact hnone)
    · intro hz
      have hroot := hrz d hdmem (by rw [hdid, hqs]; exact hz)
      rw [hdid] at hroot
      exact hroot

/-- **After a valid filter of a reachable state, the top anchor exists.** -/
theorem topAnchor_filterAll (reqOf : NodeId → List NodeId) (g : GPathM)
    (hr : Reachable reqOf g) (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true) :
    TopAnchor (filterAll g reqs) :=
  topAnchor_of _ hv
    (by rw [(pruned_filterAll g reqs).step_eq]; exact NodeInvariant.pos_reachable reqOf g hr)
    (GownersNodes.GN_filterAll g reqs (GownersNodes.GN_reachable reqOf g hr))
    (SelfOwn.OOS_filterAll g reqs (SelfOwn.OOS_reachable reqOf g hr))
    (Parents.Shape_filterAll reqOf g reqs hr)
    (Sons.RootAtZero_reachable_filterAll reqOf g reqs hr)
    (fun q d hd => review_node_valid (reqs.foldl filterRequire g) hv q d hd)

-- ============================================================
-- The reduction
-- ============================================================

/-- **`FilterNoDeadEnd` gives `SendExact`.** -/
theorem SendExact_of_FilterNoDeadEnd (φ : Cnf) (hwf : WF φ) (h : FilterNoDeadEnd φ) :
    SendExact φ := by
  intro g d hmr hv hne hd hdm hfv
  have hr := reachable_of_mapReachable φ hwf g hmr
  have hpos : 0 < (filterAll g (reqOfCnf φ d)).current_step := by
    rw [(pruned_filterAll g (reqOfCnf φ d)).step_eq]
    exact NodeInvariant.pos_reachable (reqOfCnf φ) g hr
  obtain ⟨p, hp⟩ := nonempty_of_noDeadEnd _ hpos
    (topAnchor_filterAll (reqOfCnf φ) g hr _ hfv) (h g d hmr hv hne hd hdm hfv)
  exact ⟨p, (denotS_filterAll (reqOfCnf φ) g hr _ hfv p).mp hp⟩

/-- info: 'AbsSat.GraphPath.Model.NoDeadEnd.chainSound_iff_soundFrom_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_iff_soundFrom_zero

/-- info: 'AbsSat.GraphPath.Model.NoDeadEnd.nonempty_of_noDeadEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nonempty_of_noDeadEnd

/-- info: 'AbsSat.GraphPath.Model.NoDeadEnd.topAnchor_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topAnchor_filterAll

/-- info: 'AbsSat.GraphPath.Model.NoDeadEnd.SendExact_of_FilterNoDeadEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SendExact_of_FilterNoDeadEnd

end AbsSat.GraphPath.Model.NoDeadEnd
