-- lean_project/AbsSat/GraphPath/Model/IdSeparator.lean
import AbsSat.GraphPath.Model.NoZombies

/-!
# The id separator: `LossInClosure` from two lemmas about the map

A path node's id is its map node together with its parent's map node, and a map node fixes the values
of some variables: a value node fixes its variable, a negation node the variable of the value it
requires, a clause row the variables of its literals. `fixes φ w` collects those `(variable, value)`
pairs, and `IdContradicts φ reqs w` says one of them contradicts a pin.

`LossInClosure` follows from two statements about a pinned state `P`:

* `IdSeparator` (S1) — every node of `P` lies on a full chain, or has a step at which every owner
  that is still a global owner has an id contradicting a pin;
* `IdDies` (S2) — every global owner whose id contradicts a pin is in the removal closure.

`noZombieOutside_of_separator` is the reduction for any predicate on nodes, and
`lossInClosure_of_idSeparator` instantiates it with `IdContradicts`: at the separator step every owner
dies (S2), so the node dies by `Unsupported.noSupport`.

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210), at every valid clause filter: the
41,501 nodes off every pinned chain all have a separator, the 97,548 nodes on a pinned chain none;
and the 39,655 nodes whose id contradicts a pin all die in the first round of the closure. S2 is
proved in `IdDiesProof.lean`.

**S1 is false in general.** On a hand-built formula with 8 variables (`a ∧ b → u` and `u ∧ c → f` in
two clauses that are not consecutive, the last clause before the send avoiding their variables, and
the send pinning `a = b = c = 1`), the value node `f = 0` lies on no pinned chain and has no step whose
owners all contradict a pin by id: an id records only its map node and its parent's. The removal
closure still removes it, in a second round. So `noZombieOutside_of_separator` and
`lossInClosure_of_idSeparator` are correct reductions whose S1 hypothesis does not hold for every
formula.
-/

namespace AbsSat.GraphPath.Model.IdSeparator

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.ChainFabric
open AbsSat.GraphPath.Model.NoZombies

-- ============================================================
-- What an id fixes
-- ============================================================

/-- The `(variable, value)` a literal node of the map stands for: a value node directly, a negation
node through the value node it requires. -/
def varVal (φ : Cnf) (l : NodeId) : Option (Int × Int) :=
  if l.step < 0 ∨ litBlock φ ≤ l.step then none
  else if l.step % 2 = 0 then some (l.step / 2, l.index)
  else match reqOfCnf φ l with
    | v :: _ => if v.step % 2 = 0 then some (v.step / 2, v.index) else none
    | [] => none

/-- What a map node fixes by itself. -/
def fixesMap (φ : Cnf) (m : NodeId) : List (Int × Int) :=
  if m.step < litBlock φ then (varVal φ m).toList
  else if m.step = litBlock φ then []
  else (reqOfCnf φ m).filterMap (varVal φ)

/-- What a path node fixes: its map node and its parent's. -/
def fixes (φ : Cnf) (w : PathNodeId) : List (Int × Int) :=
  fixesMap φ w.id ++ (match w.parent_id with | some p => fixesMap φ p | none => [])

/-- Some value the id fixes contradicts a pin. -/
def IdContradicts (φ : Cnf) (reqs : List NodeId) (w : PathNodeId) : Prop :=
  ∃ vv ∈ fixes φ w, ∃ r ∈ reqs, ∃ pv, varVal φ r = some pv ∧ pv.1 = vv.1 ∧ pv.2 ≠ vv.2

-- ============================================================
-- The two lemmas and the reduction
-- ============================================================

/-- **S1, generic.** Every node of `P` lies on a full chain, or has a step at which every owner that
is still a global owner satisfies `Bad`. -/
def Separator (P : GPathM) (Bad : PathNodeId → Prop) : Prop :=
  ∀ x, (P.node? x).isSome = true →
    ChainS P x ∨ ∃ n k, P.node? x = some n ∧ 0 ≤ k ∧ k < P.current_step ∧
      ∀ q ∈ ownersAt n.owners k, q ∈ P.gowners → Bad q

/-- **The reduction.** A separator whose owners all die gives no zombies outside the closure. -/
theorem noZombieOutside_of_separator (P : GPathM) (Bad : PathNodeId → Prop)
    (hsep : Separator P Bad) (hdies : ∀ q, Bad q → q ∈ P.gowners → Unsupported P q) :
    NoZombieOutside P := by
  intro x hx
  rcases hsep x hx with hc | ⟨n, k, hn, h0, hk, hall⟩
  · exact Or.inr hc
  · exact Or.inl (Unsupported.noSupport x n hn k h0 hk
      (fun q hq hg => hdies q (hall q hq hg) hg))

/-- **S1** for the machine's pins: the separator is made of ids contradicting a pin. -/
def IdSeparator (φ : Cnf) (g : GPathM) (d : NodeId) : Prop :=
  Separator ((reqOfCnf φ d).foldl filterRequire g) (IdContradicts φ (reqOfCnf φ d))

/-- **S2** for the machine's pins: a global owner whose id contradicts a pin is in the closure. -/
def IdDies (φ : Cnf) (g : GPathM) (d : NodeId) : Prop :=
  ∀ q, IdContradicts φ (reqOfCnf φ d) q → q ∈ ((reqOfCnf φ d).foldl filterRequire g).gowners →
    Unsupported ((reqOfCnf φ d).foldl filterRequire g) q

/-- **`LossInClosure` from S1 and S2** at every valid filter of a reachable state with no zombies. -/
theorem lossInClosure_of_idSeparator (φ : Cnf)
    (h : ∀ (g : GPathM) (d : NodeId), Reachable (reqOfCnf φ) g → d.step = g.current_step →
      NoZombie g → isValid (filterAll g (reqOfCnf φ d)) = true → IdSeparator φ g d ∧ IdDies φ g d) :
    LossInClosure (reqOfCnf φ) :=
  fun g d hr hd hnz hv =>
    let ⟨hsep, hdies⟩ := h g d hr hd hnz hv
    noZombieOutside_of_separator _ _ hsep hdies

/-- **No zombies in every valid reachable state of the machine**, from S1 and S2. -/
theorem noZombie_of_idSeparator (φ : Cnf)
    (h : ∀ (g : GPathM) (d : NodeId), Reachable (reqOfCnf φ) g → d.step = g.current_step →
      NoZombie g → isValid (filterAll g (reqOfCnf φ d)) = true → IdSeparator φ g d ∧ IdDies φ g d)
    (g : GPathM) (hr : Reachable (reqOfCnf φ) g) (hv : isValid g = true) : NoZombie g :=
  noZombie_reachable (reqOfCnf φ) (lossInClosure_of_idSeparator φ h) g hr hv

/-- info: 'AbsSat.GraphPath.Model.IdSeparator.noZombieOutside_of_separator' does not depend on any axioms -/
#guard_msgs in
#print axioms noZombieOutside_of_separator

/-- info: 'AbsSat.GraphPath.Model.IdSeparator.noZombie_of_idSeparator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noZombie_of_idSeparator

end AbsSat.GraphPath.Model.IdSeparator
