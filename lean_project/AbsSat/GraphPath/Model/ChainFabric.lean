-- lean_project/AbsSat/GraphPath/Model/ChainFabric.lean
import AbsSat.GraphPath.Model.FabricInduction

/-!
# The fabric of all full chains, and no zombies outside the closure

`Fabric.Fabric_sol` builds a fabric from the solutions through one node `r`. Dropping `r` gives the
fabric of **all** full chains of a state:

* `ChainS g x` — some `ChainSound` chain of `g` passes through `x`;
* `ChainT g x v` — some `ChainSound` chain of `g` passes through both;
* `Fabric_chains` — that is a fabric. Symmetry, self-ownership, owners, global owners and support
  come from the chain; the parent and son backers are the chain's own neighbours.

With it, the filter-step hypothesis of the fabric induction reduces to a statement about nodes:

* `NoZombieOutside P` — every node of the pinned state `P` is in the removal closure or lies on a
  full chain of `P` (a full chain of `g` through the pins).
* `fabricOutside_of_noZombie`, `filterFabric_of_pinnedNoZombie` — it gives `FabricOutside` and
  `FabricInduction.FilterFabric`.
* `survives_iff_onChain` — under it, **a node survives the filter iff it lies on a full chain
  through the pins.**

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210): every one of the 117,518 nodes outside
the closure, over 6,111 valid filters, lies on a full chain of `P` and of the filtered state; no
search was cut. `NoZombieOutside` itself is not proved here.
-/

namespace AbsSat.GraphPath.Model.ChainFabric

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.ReviewNodes

/-- Some full sound chain passes through `x`. -/
def ChainS (g : GPathM) : PathNodeId → Prop :=
  fun x => ∃ sel, ChainSound g sel ∧ Fabric.Passes g sel x

/-- Some full sound chain passes through both. -/
def ChainT (g : GPathM) : PathNodeId → PathNodeId → Prop :=
  fun x v => ∃ sel, ChainSound g sel ∧ Fabric.Passes g sel x ∧ Fabric.Passes g sel v

/-- **The full chains of a state form a fabric.** -/
theorem Fabric_chains (g : GPathM) : Fabric.Fabric g (ChainS g) (ChainT g) where
  gow := by
    rintro x ⟨sel, h, k, hk0, hk1, rfl⟩
    exact h.chain.2.2 k hk0 hk1
  node := by
    rintro x ⟨sel, h, k, hk0, hk1, rfl⟩
    exact (h.chain.1.1 k hk0 hk1).1
  inS := by
    rintro x v _ ⟨sel, h, _, hv⟩
    exact ⟨sel, h, hv⟩
  symm := by
    rintro x v _ ⟨sel, h, hx, hv⟩
    exact ⟨sel, h, hv, hx⟩
  self := by
    rintro x ⟨sel, h, hx⟩
    exact ⟨sel, h, hx, hx⟩
  sub := by
    rintro x n hn _ v ⟨sel, h, ⟨i, hi, hi', rfl⟩, ⟨j, hj, hj', rfl⟩⟩
    exact Fabric.chain_owns g sel h i j hi hi' hj hj' n hn
  support := by
    rintro x ⟨sel, h, hx⟩ l hlo hhi
    exact ⟨sel l, ⟨sel, h, hx, ⟨l, hlo, hhi, rfl⟩⟩, (h.chain.1.1 l hlo hhi).2⟩
  agg := by
    rintro x v _ ⟨sel, h, hx, hv⟩ l hlo hhi
    exact ⟨sel l, ⟨sel, h, hx, ⟨l, hlo, hhi, rfl⟩⟩, ⟨sel, h, hv, ⟨l, hlo, hhi, rfl⟩⟩,
      (h.chain.1.1 l hlo hhi).2⟩
  up := by
    rintro x n hn _ hroot v ⟨sel, h, ⟨i, hi, hi', rfl⟩, hv⟩
    have hipos : 0 < i := by
      rcases Int.lt_or_eq_of_le hi with hlt | heq
      · exact hlt
      · exfalso; subst heq; exact hroot h.root_shape.1
    have hlink := h.chain.1.2 (i - 1) (by omega) (by omega)
    rw [show i - 1 + 1 = i from by omega, hn] at hlink
    simp only [Option.map_some, Option.getD_some] at hlink
    exact ⟨sel (i - 1), hlink, ⟨sel, h, ⟨i, hi, hi', rfl⟩, ⟨i - 1, by omega, by omega, rfl⟩⟩,
      ⟨sel, h, ⟨i - 1, by omega, by omega, rfl⟩, hv⟩⟩
  down := by
    rintro x ⟨sel, h, ⟨i, hi, hi', rfl⟩⟩ hlast v ⟨sel', h', ⟨i', hi0', hi1', hsel'⟩, hv'⟩
    have hstep : (sel' i').id.step = i' := (h'.chain.1.1 i' hi0' hi1').2
    have hstep0 : (sel i).id.step = i := (h.chain.1.1 i hi hi').2
    have hii : i' = i := by rw [← hstep, hsel', hstep0]
    subst hii
    have hlt : i' + 1 < g.current_step := by
      have : i' ≠ g.current_step - 1 := by rw [← hstep0]; exact hlast
      omega
    obtain ⟨hs, _⟩ := h'.chain.1.1 (i' + 1) (by omega) hlt
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    have hlink := h'.chain.1.2 i' hi0' hlt
    rw [hm] at hlink
    simp only [Option.map_some, Option.getD_some] at hlink
    refine ⟨sel' (i' + 1), m, hm, hsel' ▸ hlink, ?_, ?_⟩
    · exact ⟨sel', h', ⟨i', hi0', hi1', hsel'⟩, ⟨i' + 1, by omega, hlt, rfl⟩⟩
    · exact ⟨sel', h', ⟨i' + 1, by omega, hlt, rfl⟩, hv'⟩

-- ============================================================
-- No zombies outside the closure
-- ============================================================

/-- Every node of the pinned state is unsupported or lies on a full chain. -/
def NoZombieOutside (P : GPathM) : Prop :=
  ∀ x, (P.node? x).isSome = true → Unsupported P x ∨ ChainS P x

theorem fabricOutside_of_noZombie (P : GPathM) (h : NoZombieOutside P) : FabricOutside P :=
  ⟨ChainS P, ChainT P, Fabric_chains P, h⟩

/-- No zombies outside the closure at every valid filter of a reachable state. -/
def PinnedNoZombie (reqOf : NodeId → List NodeId) : Prop :=
  ∀ (g : GPathM) (reqs : List NodeId), Reachable reqOf g → isValid (filterAll g reqs) = true →
    NoZombieOutside (reqs.foldl filterRequire g)

theorem filterFabric_of_pinnedNoZombie (reqOf : NodeId → List NodeId) (h : PinnedNoZombie reqOf) :
    FabricInduction.FilterFabric reqOf :=
  fun g reqs hr _ hv => fabricOutside_of_noZombie _ (h g reqs hr hv)

/-- **The filter keeps exactly the nodes on full chains through the pins**, under
`NoZombieOutside`. -/
theorem survives_iff_onChain (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true)
    (hnz : NoZombieOutside (reqs.foldl filterRequire g)) (x : PathNodeId)
    (hx : ((reqs.foldl filterRequire g).node? x).isSome = true) :
    ((filterAll g reqs).node? x).isSome = true ↔ ChainS (reqs.foldl filterRequire g) x := by
  constructor
  · intro hs
    rcases hnz x hx with hu | hc
    · have hnone := unsupported_removed reqOf g hr reqs hv hu
      rw [hnone] at hs
      exact absurd hs (by simp)
    · exact hc
  · intro hc
    exact fabric_survives reqOf g hr reqs (Fabric_chains _) hc

/-- **Every valid reachable state is covered by a fabric**, under `PinnedNoZombie`. -/
theorem fullFabric_reachable_of_noZombie (reqOf : NodeId → List NodeId)
    (h : PinnedNoZombie reqOf) (g : GPathM) (hr : Reachable reqOf g) (hv : isValid g = true) :
    FabricInduction.FullFabric g :=
  FabricInduction.fullFabric_reachable reqOf (filterFabric_of_pinnedNoZombie reqOf h) g hr hv

/-- info: 'AbsSat.GraphPath.Model.ChainFabric.Fabric_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_chains

/-- info: 'AbsSat.GraphPath.Model.ChainFabric.survives_iff_onChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms survives_iff_onChain

/-- info: 'AbsSat.GraphPath.Model.ChainFabric.fullFabric_reachable_of_noZombie' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullFabric_reachable_of_noZombie

end AbsSat.GraphPath.Model.ChainFabric
