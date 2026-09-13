-- lean_project/AbsSat/GraphPath/Model/PathLattice.lean
import AbsSat.GraphPath.Model.EmptinessReduction

/-!
# The machine as an abstract interpretation over the lattice of path sets

The **concrete domain** is the lattice of sets of partial paths (`PathSet`), ordered by
inclusion, with intersection as meet, union as join and the empty set as bottom.

A machine state is an **abstract element**: a compressed, polynomial-size table of
owners. Its **concretization** `conc g` is the set of partial paths it represents (the
paths of its sound chains, `denotS`).

* `conc_pruned`, `conc_grown` — concretization is monotone: narrowing a state can only
  lose paths, growing it can only add them.
* `conc_review` — the review is a **reduction**: it rewrites the table but not the set
  it represents.
* `conc_filterAll`, `conc_upFiltering`, `conc_join` — the transfer functions: the filter
  is exactly a meet with the paths through the pins, `up` is exactly the extension of
  that meet, and a join is above the union.
* `test_sound` — the machine's emptiness test `isValid` is sound: a non-empty set gives a
  valid state.
* `PreciseAt`, `SendExact_iff_precise_filter` — its precision is the open question, and
  `SendExact` is **exactly** precision of the test right after each meet with pins.

No Mathlib: the lattice structure is stated with named operations and its laws.
-/

namespace AbsSat.GraphPath.Model.PathLattice

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.SubsetSemantics
open AbsSat.GraphPath.Model.EmptinessReduction

-- ============================================================
-- The concrete lattice
-- ============================================================

/-- Sets of partial paths through the map. -/
abbrev PathSet := List NodeId → Prop

namespace PathSet

def Le (A B : PathSet) : Prop := ∀ p, A p → B p
def inf (A B : PathSet) : PathSet := fun p => A p ∧ B p
def sup (A B : PathSet) : PathSet := fun p => A p ∨ B p
def bot : PathSet := fun _ => False
def NonEmpty (A : PathSet) : Prop := ∃ p, A p

theorem le_refl (A : PathSet) : Le A A := fun _ h => h
theorem le_trans {A B C : PathSet} (h₁ : Le A B) (h₂ : Le B C) : Le A C := fun p h => h₂ p (h₁ p h)
theorem inf_le_left (A B : PathSet) : Le (inf A B) A := fun _ h => h.1
theorem inf_le_right (A B : PathSet) : Le (inf A B) B := fun _ h => h.2
theorem le_inf {A B C : PathSet} (h₁ : Le C A) (h₂ : Le C B) : Le C (inf A B) :=
  fun p h => ⟨h₁ p h, h₂ p h⟩
theorem le_sup_left (A B : PathSet) : Le A (sup A B) := fun _ h => Or.inl h
theorem le_sup_right (A B : PathSet) : Le B (sup A B) := fun _ h => Or.inr h
theorem sup_le {A B C : PathSet} (h₁ : Le A C) (h₂ : Le B C) : Le (sup A B) C :=
  fun p h => h.elim (h₁ p) (h₂ p)
theorem bot_le (A : PathSet) : Le bot A := fun _ h => absurd h id
theorem not_nonempty_bot : ¬ NonEmpty bot := fun ⟨_, h⟩ => h
theorem NonEmpty.mono {A B : PathSet} (h : Le A B) (hA : NonEmpty A) : NonEmpty B :=
  let ⟨p, hp⟩ := hA; ⟨p, h p hp⟩

end PathSet

/-- The paths that go through every pin placed below step `n`. -/
def Through (reqs : List NodeId) (n : Int) : PathSet :=
  fun p => ∀ req ∈ reqs, 0 ≤ req.step → req.step < n → req ∈ p

/-- Extending every path of a set by one node. -/
def Extend (d : NodeId) (A : PathSet) : PathSet := fun p => ∃ p', p = d :: p' ∧ A p'

theorem Extend_mono (d : NodeId) {A B : PathSet} (h : PathSet.Le A B) :
    PathSet.Le (Extend d A) (Extend d B) :=
  fun _ ⟨p', hp, hA⟩ => ⟨p', hp, h p' hA⟩

theorem nonEmpty_Extend_iff (d : NodeId) (A : PathSet) :
    PathSet.NonEmpty (Extend d A) ↔ PathSet.NonEmpty A :=
  ⟨fun ⟨_, p', _, hA⟩ => ⟨p', hA⟩, fun ⟨p', hA⟩ => ⟨d :: p', p', rfl, hA⟩⟩

-- ============================================================
-- Concretization
-- ============================================================

/-- The set of partial paths a machine state represents. -/
def conc (g : GPathM) : PathSet := denotS g

/-- **Narrowing loses paths, never invents them.** -/
theorem conc_pruned (reqOf : NodeId → List NodeId) {g g' : GPathM} (hr : Reachable reqOf g)
    (hpr : Pruned g g') : PathSet.Le (conc g') (conc g) := by
  rintro p ⟨sel, hs, rfl⟩
  exact ⟨sel, ChainSound_of_pruned hpr (Reader.NodupIds_reachable reqOf g hr)
    (Sons.SMP_reachable reqOf g hr) sel hs, by simp only [pathOf, hpr.step_eq]⟩

/-- **Growing keeps every path.** -/
theorem conc_grown {g g' : GPathM} (hgr : Grown g g') : PathSet.Le (conc g) (conc g') := by
  rintro p ⟨sel, hs, rfl⟩
  exact ⟨sel, ChainSound_of_grown hgr sel hs, by simp only [pathOf, hgr.step_eq]⟩

/-- **The review is a reduction**: it rewrites the table, not the set. -/
theorem conc_review (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (p : List NodeId) : conc (review g) p ↔ conc g p := by
  constructor
  · exact conc_pruned reqOf hr (pruned_review g) p
  · rintro ⟨sel, hs, rfl⟩
    exact ⟨sel, ChainSound_review g sel hs, by simp only [pathOf, (pruned_review g).step_eq]⟩

-- ============================================================
-- Transfer functions
-- ============================================================

/-- **The filter is a meet.** -/
theorem conc_filterAll (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true) (p : List NodeId) :
    conc (filterAll g reqs) p ↔ PathSet.inf (conc g) (Through reqs g.current_step) p :=
  denotS_filterAll reqOf g hr reqs hv p

/-- **`up` is the extension of that meet.** -/
theorem conc_upFiltering (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (d : NodeId) (title : String)
    (hv : isValid (filterAll g reqs) = true) (hd : d.step = g.current_step) (p : List NodeId) :
    conc (upFiltering g reqs d title) p ↔
      Extend d (PathSet.inf (conc g) (Through reqs g.current_step)) p :=
  denotS_upFiltering reqOf g hr reqs d title hv hd p

/-- **A join is above the union.** -/
theorem conc_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) :
    PathSet.Le (PathSet.sup (conc g₁) (conc g₂)) (conc (join g₁ g₂)) :=
  fun p h => denotS_join_union g₁ g₂ hok p h

-- ============================================================
-- The emptiness test
-- ============================================================

/-- **The abstract test is sound**: a non-empty set gives a valid state. -/
theorem test_sound (g : GPathM) (h : PathSet.NonEmpty (conc g)) : isValid g = true :=
  let ⟨p, hp⟩ := h; isValid_of_denotS g p hp

/-- The abstract test is precise at `g`: validity implies a non-empty set. -/
def PreciseAt (g : GPathM) : Prop := isValid g = true → PathSet.NonEmpty (conc g)

/-- **`SendExact` is precision of the test right after a meet with pins.** -/
theorem SendExact_iff_precise_filter (φ : Cnf) (hwf : WF φ) :
    SendExact φ ↔
      ∀ (g : GPathM) (d : NodeId), MapReachable φ g → isValid g = true →
        PathSet.NonEmpty (conc g) → d.step = g.current_step → d ∈ mapNodes φ d.step →
        PreciseAt (filterAll g (reqOfCnf φ d)) := by
  constructor
  · intro hex g d hmr hv hne hd hdm hfv
    obtain ⟨p, hp, hth⟩ := hex g d hmr hv hne hd hdm hfv
    exact ⟨p, (denotS_filterAll (reqOfCnf φ) g (reachable_of_mapReachable φ hwf g hmr) _ hfv p).mpr
      ⟨hp, hth⟩⟩
  · intro h g d hmr hv hne hd hdm hfv
    obtain ⟨p, hp⟩ := h g d hmr hv hne hd hdm hfv
    exact ⟨p, (denotS_filterAll (reqOfCnf φ) g (reachable_of_mapReachable φ hwf g hmr) _ hfv p).mp hp⟩

/-- Under `SendExact`, the test is precise on every state the driver keeps. -/
theorem precise_on_driver (φ : Cnf) (hwf : WF φ) (hex : SendExact φ) (k : Nat)
    (kv : NodeId × GPathM) (hkv : kv ∈ PartialPaths.lineAt φ k) : PreciseAt kv.2 :=
  fun _ => lineAt_nonempty φ hwf hex k kv hkv

/-- info: 'AbsSat.GraphPath.Model.PathLattice.conc_review' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conc_review

/-- info: 'AbsSat.GraphPath.Model.PathLattice.conc_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conc_filterAll

/-- info: 'AbsSat.GraphPath.Model.PathLattice.conc_upFiltering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conc_upFiltering

/-- info: 'AbsSat.GraphPath.Model.PathLattice.conc_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conc_join

/-- info: 'AbsSat.GraphPath.Model.PathLattice.test_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms test_sound

/-- info: 'AbsSat.GraphPath.Model.PathLattice.SendExact_iff_precise_filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SendExact_iff_precise_filter

end AbsSat.GraphPath.Model.PathLattice
