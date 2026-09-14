-- lean_project/AbsSat/GraphPath/Model/IdClosureSep.lean
import AbsSat.GraphPath.Model.IdDiesProof

/-!
# S1 without a fixed depth: the id closure

S1 in one level (`IdSeparator`) is false in general: when the clauses that correlate the pinned
variables are not consecutive, no id records them together, and the removal closure needs a second
round. This module drops the fixed depth.

* `IdClosure φ reqs P` — the closure the ids generate: a node whose id contradicts a pin is in it, and
  so is a node with a step at which every owner that is still a global owner is in it.
* `idClosure_unsupported` — **every global owner in the id closure is in the removal closure**, by
  induction, with `IdDiesProof.idDies` as the base case.
* `IdClosureSeparator` — S1 at any depth: every node of the pinned state lies on a full chain, or has a
  step at which every global owner is in the id closure.
* `idClosureSeparator_of_idSeparator` — one-level S1 is the first level of it.
* `lossInClosure_of_idClosureSeparator`, `noZombie_of_idClosureSeparator` — `LossInClosure`, and with it
  no zombies in every valid reachable state, follow from `IdClosureSeparator` alone.

Measured on `SatMachinePure`: on 30 random formulas with their clauses interleaved with fresh-variable
fillers, the 457,928 nodes off every pinned chain all have a separator of depth at most 2 (42 need the
second level), and no node on a pinned chain has one; on the hand-built counterexamples to one-level
S1 (`far2`, `far3`, `far4`) the same holds with 18, 12 and 6 nodes at the second level.
`IdClosureSeparator` itself is not proved here.
-/

namespace AbsSat.GraphPath.Model.IdClosureSep

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.ChainFabric
open AbsSat.GraphPath.Model.NoZombies
open AbsSat.GraphPath.Model.IdSeparator

/-- The closure the ids generate in a pinned state. -/
inductive IdClosure (φ : Cnf) (reqs : List NodeId) (P : GPathM) : PathNodeId → Prop where
  | base (q : PathNodeId) (h : IdContradicts φ reqs q) : IdClosure φ reqs P q
  | step (x : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (k : Int)
      (h0 : 0 ≤ k) (hk : k < P.current_step)
      (h : ∀ q ∈ ownersAt n.owners k, q ∈ P.gowners → IdClosure φ reqs P q) :
      IdClosure φ reqs P x

/-- **Every global owner in the id closure is in the removal closure.** -/
theorem idClosure_unsupported (φ : Cnf) (hwf : WF φ) (g : GPathM)
    (hr : Reachable (reqOfCnf φ) g) (d : NodeId) (hd : d.step = g.current_step)
    {x : PathNodeId}
    (hx : IdClosure φ (reqOfCnf φ d) ((reqOfCnf φ d).foldl filterRequire g) x) :
    x ∈ ((reqOfCnf φ d).foldl filterRequire g).gowners →
      Unsupported ((reqOfCnf φ d).foldl filterRequire g) x := by
  induction hx with
  | base q h =>
    intro hg
    exact IdDiesProof.idDies φ hwf g hr d hd q h hg
  | step x n hn k h0 hk _ ih =>
    intro _
    exact Unsupported.noSupport x n hn k h0 hk (fun q hq hg => ih q hq hg hg)

/-- **S1 at any depth.** -/
def IdClosureSeparator (φ : Cnf) (g : GPathM) (d : NodeId) : Prop :=
  Separator ((reqOfCnf φ d).foldl filterRequire g)
    (IdClosure φ (reqOfCnf φ d) ((reqOfCnf φ d).foldl filterRequire g))

/-- One-level S1 is the first level of it. -/
theorem idClosureSeparator_of_idSeparator (φ : Cnf) (g : GPathM) (d : NodeId)
    (h : IdSeparator φ g d) : IdClosureSeparator φ g d := by
  intro x hx
  rcases h x hx with hc | ⟨n, k, hn, h0, hk, hall⟩
  · exact Or.inl hc
  · exact Or.inr ⟨n, k, hn, h0, hk, fun q hq hg => IdClosure.base q (hall q hq hg)⟩

/-- **`LossInClosure` from S1 at any depth.** -/
theorem lossInClosure_of_idClosureSeparator (φ : Cnf) (hwf : WF φ)
    (h : ∀ (g : GPathM) (d : NodeId), Reachable (reqOfCnf φ) g → d.step = g.current_step →
      NoZombie g → isValid (filterAll g (reqOfCnf φ d)) = true → IdClosureSeparator φ g d) :
    LossInClosure (reqOfCnf φ) :=
  fun g d hr hd hnz hv =>
    noZombieOutside_of_separator _ _ (h g d hr hd hnz hv)
      (fun _ hq hg => idClosure_unsupported φ hwf g hr d hd hq hg)

/-- **No zombies in every valid reachable state of the machine, from S1 at any depth.** -/
theorem noZombie_of_idClosureSeparator (φ : Cnf) (hwf : WF φ)
    (h : ∀ (g : GPathM) (d : NodeId), Reachable (reqOfCnf φ) g → d.step = g.current_step →
      NoZombie g → isValid (filterAll g (reqOfCnf φ d)) = true → IdClosureSeparator φ g d)
    (g : GPathM) (hr : Reachable (reqOfCnf φ) g) (hv : isValid g = true) : NoZombie g :=
  noZombie_reachable (reqOfCnf φ) (lossInClosure_of_idClosureSeparator φ hwf h) g hr hv

/-- info: 'AbsSat.GraphPath.Model.IdClosureSep.idClosure_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms idClosure_unsupported

/-- info: 'AbsSat.GraphPath.Model.IdClosureSep.noZombie_of_idClosureSeparator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noZombie_of_idClosureSeparator

end AbsSat.GraphPath.Model.IdClosureSep
