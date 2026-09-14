-- lean_project/AbsSat/GraphPath/Model/IdClosureLevels.lean
import AbsSat.GraphPath.Model.IdClosureSep

/-!
# Stratified id closure by finite depth levels

This module defines `IdClosureAt`, the level-stratified version of `IdClosure`.
* Level 0: direct pin contradiction (`IdContradicts`).
* Level `l + 1`: nodes whose global owners at step `k` are in level `l`.

Key theorems:
* `idClosure_of_idClosureAt` — every node at a finite level `l` is in `IdClosure`.
* `idClosureAt_mono_succ`, `idClosureAt_mono` — monotonic growth with depth.
* `idClosureAt_unsupported` — all global owners at level `l` are in the removal closure.
* `idClosureSeparator_of_idClosureAtSeparator` — any finite level separator implies `IdClosureSeparator`.
* `chain_survives_of_compatible`, `break_of_no_chain` — a node off every pinned chain has every chain of
  the unpinned state breaking some pin in range.

Levels are cumulative and start at the base: the separators measured with depth at most 2 (owners that
contradict a pin, or have a separator of such owners) are `IdClosureAtSeparator 1`.
-/

namespace AbsSat.GraphPath.Model.IdClosureLevels

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.ChainFabric
open AbsSat.GraphPath.Model.NoZombies
open AbsSat.GraphPath.Model.IdSeparator
open AbsSat.GraphPath.Model.IdClosureSep

/-- Stratified id closure by level `l : Nat`. -/
inductive IdClosureAt (φ : Cnf) (reqs : List NodeId) (P : GPathM) : Nat → PathNodeId → Prop where
  | base (q : PathNodeId) (h : IdContradicts φ reqs q) :
      IdClosureAt φ reqs P 0 q
  | succ_base (l : Nat) (q : PathNodeId) (h : IdClosureAt φ reqs P l q) :
      IdClosureAt φ reqs P (l + 1) q
  | succ_step (l : Nat) (x : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (k : Int)
      (h0 : 0 ≤ k) (hk : k < P.current_step)
      (h : ∀ q ∈ ownersAt n.owners k, q ∈ P.gowners → IdClosureAt φ reqs P l q) :
      IdClosureAt φ reqs P (l + 1) x

/-- Monotonicity with respect to successor level. -/
theorem idClosureAt_mono_succ (φ : Cnf) (reqs : List NodeId) (P : GPathM)
    (l : Nat) (q : PathNodeId) (h : IdClosureAt φ reqs P l q) :
    IdClosureAt φ reqs P (l + 1) q :=
  IdClosureAt.succ_base l q h

/-- Monotonicity with respect to any higher level `l ≤ m`. -/
theorem idClosureAt_mono (φ : Cnf) (reqs : List NodeId) (P : GPathM)
    {l m : Nat} (hlm : l ≤ m) (q : PathNodeId) (h : IdClosureAt φ reqs P l q) :
    IdClosureAt φ reqs P m q := by
  induction hlm with
  | refl => exact h
  | step _ ih => exact IdClosureAt.succ_base _ q ih

/-- **Soundness of stratification**: every node in `IdClosureAt l` is in `IdClosure`. -/
theorem idClosure_of_idClosureAt (φ : Cnf) (reqs : List NodeId) (P : GPathM)
    {l : Nat} {x : PathNodeId} (hx : IdClosureAt φ reqs P l x) :
    IdClosure φ reqs P x := by
  induction hx with
  | base q h =>
    exact IdClosure.base q h
  | succ_base _ _ _ ih =>
    exact ih
  | succ_step _ x n hn k h0 hk _ ih =>
    exact IdClosure.step x n hn k h0 hk ih

/-- Level-stratified separator at depth `l`. -/
def IdClosureAtSeparator (l : Nat) (φ : Cnf) (g : GPathM) (d : NodeId) : Prop :=
  Separator ((reqOfCnf φ d).foldl filterRequire g)
    (IdClosureAt φ (reqOfCnf φ d) ((reqOfCnf φ d).foldl filterRequire g) l)

/-- Level 0 separator is exactly `IdSeparator`. -/
theorem idClosureAtSeparator_zero (φ : Cnf) (g : GPathM) (d : NodeId)
    (h : IdSeparator φ g d) : IdClosureAtSeparator 0 φ g d := by
  intro x hx
  rcases h x hx with hc | ⟨n, k, hn, h0, hk, hall⟩
  · exact Or.inl hc
  · exact Or.inr ⟨n, k, hn, h0, hk, fun q hq hg => IdClosureAt.base q (hall q hq hg)⟩

/-- **A separator at any finite level `l` implies `IdClosureSeparator`.** -/
theorem idClosureSeparator_of_idClosureAtSeparator (l : Nat) (φ : Cnf) (g : GPathM) (d : NodeId)
    (h : IdClosureAtSeparator l φ g d) : IdClosureSeparator φ g d := by
  intro x hx
  rcases h x hx with hc | ⟨n, k, hn, h0, hk, hall⟩
  · exact Or.inl hc
  · exact Or.inr ⟨n, k, hn, h0, hk, fun q hq hg => idClosure_of_idClosureAt φ _ _ (hall q hq hg)⟩

/-- **Every global owner in `IdClosureAt l` is in the removal closure.** -/
theorem idClosureAt_unsupported (φ : Cnf) (hwf : WF φ) (g : GPathM)
    (hr : Reachable (reqOfCnf φ) g) (d : NodeId) (hd : d.step = g.current_step)
    {l : Nat} {x : PathNodeId}
    (hx : IdClosureAt φ (reqOfCnf φ d) ((reqOfCnf φ d).foldl filterRequire g) l x) :
    x ∈ ((reqOfCnf φ d).foldl filterRequire g).gowners →
      Unsupported ((reqOfCnf φ d).foldl filterRequire g) x := by
  intro hg
  exact idClosure_unsupported φ hwf g hr d hd (idClosure_of_idClosureAt φ _ _ hx) hg

/-- info: 'AbsSat.GraphPath.Model.IdClosureLevels.idClosureSeparator_of_idClosureAtSeparator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms idClosureSeparator_of_idClosureAtSeparator

/-- info: 'AbsSat.GraphPath.Model.IdClosureLevels.idClosureAt_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms idClosureAt_unsupported

-- ============================================================
-- Preservation of compatible chains (branch 1 of separator)
-- ============================================================

/-- **Compatible chain survives**: a chain passing through `x` that satisfies `reqs`
survives as a sound full chain in `reqs.foldl filterRequire g`. -/
theorem chain_survives_of_compatible (g : GPathM) (reqs : List NodeId)
    (sel : Int → PathNodeId) (hchain : ChainSound g sel) (x : PathNodeId)
    (hpass : Fabric.Passes g sel x)
    (hcomp : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    ChainS (reqs.foldl filterRequire g) x := by
  have hcs := foldl_filterRequire_step reqs g
  refine ⟨sel, ChainSound_foldl_filterRequire reqs g sel hchain hcomp, ?_⟩
  obtain ⟨k, hk0, hk1, hselk⟩ := hpass
  exact ⟨k, hk0, hcs.symm ▸ hk1, hselk⟩

-- ============================================================
-- Localization of chain break (branch 2 of separator)
-- ============================================================

/-- Constructive extraction of a failed requirement from a negated universal condition on lists. -/
theorem exists_break_of_not_all (reqs : List NodeId) (g : GPathM) (sel : Int → PathNodeId)
    (hnot : ¬ (∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req)) :
    ∃ req ∈ reqs, 0 ≤ req.step ∧ req.step < g.current_step ∧ (sel req.step).id ≠ req := by
  induction reqs with
  | nil =>
    exfalso
    exact hnot (fun _ hmem => nomatch hmem)
  | cons req rest ih =>
    if h0 : 0 ≤ req.step then
      if hk : req.step < g.current_step then
        if heq : (sel req.step).id = req then
          have hrest : ¬ (∀ r ∈ rest, 0 ≤ r.step → r.step < g.current_step → (sel r.step).id = r) := by
            intro hall
            apply hnot
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hr_rest
            · intro _ _; exact heq
            · exact hall r hr_rest
          obtain ⟨r, hr_mem, hr0, hrk, hr_ne⟩ := ih hrest
          exact ⟨r, List.mem_cons_of_mem req hr_mem, hr0, hrk, hr_ne⟩
        else
          exact ⟨req, List.mem_cons.mpr (Or.inl rfl), h0, hk, heq⟩
      else
        have hrest : ¬ (∀ r ∈ rest, 0 ≤ r.step → r.step < g.current_step → (sel r.step).id = r) := by
          intro hall
          apply hnot
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr_rest
          · intro _ hlt; exfalso; exact hk hlt
          · exact hall r hr_rest
        obtain ⟨r, hr_mem, hr0, hrk, hr_ne⟩ := ih hrest
        exact ⟨r, List.mem_cons_of_mem req hr_mem, hr0, hrk, hr_ne⟩
    else
      have hrest : ¬ (∀ r ∈ rest, 0 ≤ r.step → r.step < g.current_step → (sel r.step).id = r) := by
        intro hall
        apply hnot
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr_rest
        · intro hge _; exfalso; exact h0 hge
        · exact hall r hr_rest
      obtain ⟨r, hr_mem, hr0, hrk, hr_ne⟩ := ih hrest
      exact ⟨r, List.mem_cons_of_mem req hr_mem, hr0, hrk, hr_ne⟩

/-- **Break on incompatible chain**: if `x` loses all chains in the pinned state,
any prior sound chain `sel` through `x` fails at least one requirement. -/
theorem break_of_no_chain (g : GPathM) (reqs : List NodeId)
    (x : PathNodeId) (hno : ¬ ChainS (reqs.foldl filterRequire g) x)
    (sel : Int → PathNodeId) (hchain : ChainSound g sel) (hpass : Fabric.Passes g sel x) :
    ∃ req ∈ reqs, 0 ≤ req.step ∧ req.step < g.current_step ∧ (sel req.step).id ≠ req := by
  have hnot : ¬ (∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :=
    fun hcomp => hno (chain_survives_of_compatible g reqs sel hchain x hpass hcomp)
  exact exists_break_of_not_all reqs g sel hnot

-- ============================================================
-- Propagation to Level 2 (owners_in_closure_level2)
-- ============================================================

/-- A node with a direct contradiction is at level 1 (via level 0). -/
theorem idClosureAt_one_of_base (φ : Cnf) (reqs : List NodeId) (P : GPathM)
    (q : PathNodeId) (h : IdContradicts φ reqs q) :
    IdClosureAt φ reqs P 1 q :=
  IdClosureAt.succ_base 0 q (IdClosureAt.base q h)

/-- An owner whose global owners at step `s` have direct contradictions is at level 1. -/
theorem idClosureAt_one_of_step0 (φ : Cnf) (reqs : List NodeId) (P : GPathM)
    (q : PathNodeId) (m : PNodeM) (hm : P.node? q = some m) (s : Int)
    (hs0 : 0 ≤ s) (hsk : s < P.current_step)
    (hall0 : ∀ o ∈ ownersAt m.owners s, o ∈ P.gowners → IdContradicts φ reqs o) :
    IdClosureAt φ reqs P 1 q :=
  IdClosureAt.succ_step 0 q m hm s hs0 hsk (fun o ho hg => IdClosureAt.base o (hall0 o ho hg))

/-- **Two levels**: a node whose global owners at step `k` either contradict a pin or have a step whose
global owners all contradict one is in `IdClosureAt 2`. -/
theorem idClosureAt_two_of_owners (φ : Cnf) (reqs : List NodeId) (P : GPathM)
    (x : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (k : Int)
    (hk0 : 0 ≤ k) (hkk : k < P.current_step)
    (howners : ∀ q ∈ ownersAt n.owners k, q ∈ P.gowners →
      IdContradicts φ reqs q ∨
      ∃ m s, P.node? q = some m ∧ 0 ≤ s ∧ s < P.current_step ∧
        ∀ o ∈ ownersAt m.owners s, o ∈ P.gowners → IdContradicts φ reqs o) :
    IdClosureAt φ reqs P 2 x := by
  refine IdClosureAt.succ_step 1 x n hn k hk0 hkk ?_
  intro q hq hg
  rcases howners q hq hg with hbase | ⟨m, s, hm, hs0, hsk, hall0⟩
  · exact idClosureAt_one_of_base φ reqs P q hbase
  · exact idClosureAt_one_of_step0 φ reqs P q m hm s hs0 hsk hall0

/-- info: 'AbsSat.GraphPath.Model.IdClosureLevels.idClosureAt_two_of_owners' depends on axioms: [propext] -/
#guard_msgs in
#print axioms idClosureAt_two_of_owners

/-- info: 'AbsSat.GraphPath.Model.IdClosureLevels.chain_survives_of_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_survives_of_compatible

/-- info: 'AbsSat.GraphPath.Model.IdClosureLevels.break_of_no_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms break_of_no_chain

end AbsSat.GraphPath.Model.IdClosureLevels
