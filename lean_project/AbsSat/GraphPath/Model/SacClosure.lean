import AbsSat.GraphPath.Model.ChainFabric

/-!
# The conditioned closure: singleton arc consistency over the owners

Measurement (`altchain_m1..m7`, 2026-09-16) says the review's removals are captured by a rule that
the unconditioned closures of `IdClosureSep` miss: **condition on one node, then propagate**. Fixing
a node `x`, keep at each step only the global owners compatible with `x`, and drop a node when some
step keeps nothing compatible with it; iterate. On that family the rule removes exactly the nodes
with no chain, in `⌈k/2⌉ + 1` passes, where the tree-shaped refutation of `Depth` needed a branching
argument of depth `log₂(k + 2)`.

This module defines the rule and proves it sound: **what it removes is on no chain**. The passes of
the measurement are the derivations of `DeadFor`; nothing here bounds their number.

* `Compat` — two path nodes own each other, which is what a chain gives for any two of its members;
* `DeadFor g x` — the closure conditioned on `x`;
* `SacDead g x` — `x` kills itself, so `x` carries no chain;
* `not_chainS_of_sacDead` — **soundness**: `SacDead g x → ¬ ChainS g x`.

The other direction is false in general (it is exactly what the measurement checks per family), and
the link with the review — that the review removes every `SacDead` node — is the next piece.
-/

namespace AbsSat.GraphPath.Model.SacClosure

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.ChainFabric

/-- Two nodes own each other. A sound chain makes any two of its members compatible, including a
member with itself. -/
def Compat (g : GPathM) (x y : PathNodeId) : Prop :=
  x ∈ ownersOf g y ∧ y ∈ ownersOf g x

theorem compat_symm {g : GPathM} {x y : PathNodeId} (h : Compat g x y) : Compat g y x :=
  ⟨h.2, h.1⟩

/-- **Any two members of a sound chain are compatible.** Off the diagonal this is `PairwiseOwned`;
on it, `self_owned`. -/
theorem compat_of_chainSound {g : GPathM} {sel : Int → PathNodeId} (h : ChainSound g sel)
    {i j : Int} (hi0 : 0 ≤ i) (hi : i < g.current_step) (hj0 : 0 ≤ j) (hj : j < g.current_step) :
    Compat g (sel i) (sel j) := by
  rcases Decidable.em (i = j) with rfl | hne
  · exact ⟨h.self_owned i hi0 hi, h.self_owned i hi0 hi⟩
  · refine ⟨?_, ?_⟩
    · exact (List.mem_filter.mp (h.chain.2.1 i j hi0 hj0 hi hj hne)).1
    · exact (List.mem_filter.mp (h.chain.2.1 j i hj0 hi0 hj hi (fun e => hne e.symm))).1

-- ============================================================
-- The rule
-- ============================================================

/-- **The closure conditioned on `x`.** In the network where every step keeps only the global owners
compatible with `x`, node `y` is gone when it is itself incompatible with `x`, or when some step
keeps nothing compatible with `y` that is not already gone. -/
inductive DeadFor (g : GPathM) (x : PathNodeId) : PathNodeId → Prop where
  | incompat (y : PathNodeId) (h : ¬ Compat g x y) : DeadFor g x y
  | noSupport (y : PathNodeId) (k : Int) (h0 : 0 ≤ k) (hk : k < g.current_step)
      (h : ∀ z ∈ g.gowners, z.id.step = k → Compat g x z → Compat g y z → DeadFor g x z) :
      DeadFor g x y

/-- The conditioned closure kills the node it is conditioned on. -/
def SacDead (g : GPathM) (x : PathNodeId) : Prop := DeadFor g x x

-- ============================================================
-- Soundness
-- ============================================================

/-- No member of a sound chain is killed by the closure conditioned on another member. -/
theorem not_deadFor_of_passes {g : GPathM} {sel : Int → PathNodeId} (hcs : ChainSound g sel)
    {kx : Int} (hkx0 : 0 ≤ kx) (hkx : kx < g.current_step) {y : PathNodeId}
    (hd : DeadFor g (sel kx) y) : ¬ Fabric.Passes g sel y := by
  induction hd with
  | incompat y h =>
    rintro ⟨k, hk0, hk, rfl⟩
    exact h (compat_of_chainSound hcs hkx0 hkx hk0 hk)
  | noSupport y k h0 hk _ ih =>
    rintro ⟨j, hj0, hj, rfl⟩
    exact ih (sel k) (hcs.chain.2.2 k h0 hk) ((hcs.chain.1.1 k h0 hk).2)
      (compat_of_chainSound hcs hkx0 hkx h0 hk) (compat_of_chainSound hcs hj0 hj h0 hk)
      ⟨k, h0, hk, rfl⟩

/-- **Soundness of the rule.** A node its own conditioned closure kills lies on no sound chain, so
removing it loses nothing. -/
theorem not_chainS_of_sacDead (g : GPathM) (x : PathNodeId) (h : SacDead g x) : ¬ ChainS g x := by
  rintro ⟨sel, hcs, hp⟩
  obtain ⟨kx, hkx0, hkx, hsel⟩ := hp
  rw [← hsel] at h
  exact not_deadFor_of_passes hcs hkx0 hkx h ⟨kx, hkx0, hkx, rfl⟩

/-- Contrapositive, in the shape the no-zombie statements use. -/
theorem sacDead_not_chain (g : GPathM) (x : PathNodeId) (h : ChainS g x) : ¬ SacDead g x :=
  fun hd => not_chainS_of_sacDead g x hd h

/-- info: 'AbsSat.GraphPath.Model.SacClosure.compat_of_chainSound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms compat_of_chainSound

/-- info: 'AbsSat.GraphPath.Model.SacClosure.not_chainS_of_sacDead' depends on axioms: [propext] -/
#guard_msgs in
#print axioms not_chainS_of_sacDead

end AbsSat.GraphPath.Model.SacClosure
