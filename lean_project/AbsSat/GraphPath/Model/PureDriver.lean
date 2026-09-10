-- lean_project/AbsSat/GraphPath/Model/PureDriver.lean
import AbsSat.GraphPath.Model.Conservation

/-!
# The driver, over the arithmetic map

`MirrorTest.mirrorRun` is the machine's timeline loop, and it is written over
`GMap` — `Std.HashMap` underneath. Reasoning about it directly would drag
`Classical.choice` into every closure downstream, which is exactly what the
arithmetic model of the map was built to avoid.

So this is the same loop over `CnfMap`/`CnfSel`: `mapSons` in place of
`map_node.sons`, `reqOfCnf` in place of `destine_node.requires`, `mapNodes` in
place of `get_ids_step gmap 0`. One more layer of the same mirror pattern that
`GPathM` applies to `GPath` — the model is for proving, and a differential band
ties it to the thing that runs.

Titles are the one deliberate difference: the real driver copies the map node's
title into the graph, and nothing in `isValid`, `owners` or `denot` reads it, so
the model passes `""`. The band therefore compares keys, node counts and
validity, not titles.
-/

namespace AbsSat.GraphPath.Model.PureDriver

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.Conservation

/-- One timeline row: states keyed by the map node just visited. -/
abbrev PureLine := List (NodeId × GPathM)

/-- Mirror of `MirrorTest.insertGPath`: states arriving at the same map node
are merged. -/
def insertPure (line : PureLine) (key : NodeId) (g : GPathM) : PureLine :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, existing) =>
    line.map (fun kv => if kv.1 == key then (key, doJoin existing g) else kv)
  | none => line ++ [(key, g)]

/-- Mirror of `MirrorTest.mirrorAdvance`: every state is sent to every son of
its origin, filtered by the destination's requirements, and kept only if the
result is still valid. -/
def pureAdvance (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv =>
    (mapSons φ kv.1.step kv.1.index).foldl (fun next d =>
      let g' := upFiltering kv.2 (reqOfCnf φ d) d ""
      if isValid g' then insertPure next d g' else next) next) []

def pureInit (φ : Cnf) : PureLine :=
  (mapNodes φ 0).foldl (fun line id => insertPure line id (initSeed id "")) []

def pureSteps (φ : Cnf) : Nat → PureLine → PureLine
  | 0, line => line
  | n + 1, line => pureSteps φ n (pureAdvance φ line)

/-- The whole run. An empty result is the UNSAT answer. -/
def pureRun (φ : Cnf) : PureLine := pureSteps φ (stepCount φ - 1).toNat (pureInit φ)

-- ============================================================
-- What one insert does
-- ============================================================

/-- After an insert there is an entry at the key, and its state is either the
one inserted or its join with what was already parked there. -/
theorem mem_insertPure (line : PureLine) (key : NodeId) (g : GPathM) :
    ∃ h, (key, h) ∈ insertPure line key g ∧
      (h = g ∨ ∃ e, (key, e) ∈ line ∧ h = doJoin e g) := by
  unfold insertPure
  cases hf : line.find? (fun kv => kv.1 == key) with
  | none => exact ⟨g, List.mem_append_right _ List.mem_cons_self, Or.inl rfl⟩
  | some kv =>
    have hmem : kv ∈ line := List.mem_of_find?_eq_some hf
    have hkey : kv.1 = key :=
      eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
    refine ⟨doJoin kv.2 g, ?_, Or.inr ⟨kv.2, by rw [← hkey]; exact hmem, rfl⟩⟩
    have : (key, doJoin kv.2 g)
        = (fun x : NodeId × GPathM => if x.1 == key then (key, doJoin kv.2 g) else x) kv := by
      simp only [hkey, beq_self_eq_true, if_pos]
    rw [this]
    exact List.mem_map_of_mem hmem

/-- An entry at a *different* key survives an insert. -/
theorem mem_insertPure_of_ne (line : PureLine) (key k' : NodeId) (g h : GPathM)
    (hne : k' ≠ key) (hmem : (k', h) ∈ line) : (k', h) ∈ insertPure line key g := by
  unfold insertPure
  cases hf : line.find? (fun kv => kv.1 == key) with
  | none => exact List.mem_append_left _ hmem
  | some kv =>
    have hnb : ¬ ((k' == key) = true) := fun hc => hne (eq_of_beq hc)
    have : (k', h)
        = (fun x : NodeId × GPathM => if x.1 == key then (key, doJoin kv.2 g) else x) (k', h) := by
      simp only
      rw [if_neg hnb]
    rw [this]
    exact List.mem_map_of_mem hmem

-- ============================================================
-- The edge the driver takes from the branch's state
-- ============================================================

/-- **The driver's own edge carries the branch forward.** From the state parked
at the assignment's node at step `k`, the son the driver is about to walk to is
the assignment's node at step `k+1`; the state it builds there is the branch's
next state; and it passes the validity guard, so the driver keeps it rather
than dropping it.

The three conjuncts are the three things `pureAdvance` needs at that point: the
destination is among `mapSons`, so the inner fold visits it; the result is
`AlongAssign`, so the conservation law still applies to it; and `isValid` holds,
so the `if` takes the inserting branch. -/
theorem advance_target (φ : Cnf) (a : Assign) (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssign φ a g) (hcs : g.current_step = k + 1) :
    selOfAssign φ a (k + 1)
        ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index
      ∧ AlongAssign φ a (upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
          (selOfAssign φ a (k + 1)) "")
      ∧ isValid (upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
          (selOfAssign φ a (k + 1)) "") = true := by
  have hson : selOfAssign φ a (k + 1)
      ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index := by
    rw [selOfAssign_step]
    exact selOfAssign_son φ a hsat k h0 hk
  have hup : AlongAssign φ a (upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
      (selOfAssign φ a (k + 1)) "") := by
    have := AlongAssign.up (φ := φ) (a := a) g "" (by omega) (by omega) hal
    rwa [hcs] at this
  exact ⟨hson, hup, isValid_along φ a hwf hsat hzero _ hup⟩

/-- info: 'AbsSat.GraphPath.Model.PureDriver.advance_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms advance_target

/-!
## What is left of the driver, said precisely

`advance_target` is the content: the edge exists, it leads to the branch's next
state, and the guard lets it through. What remains is bookkeeping about the
list the driver carries — that `pureAdvance`'s two nested folds keep the entry
once it is inserted. Three invariants, each preserved by `insertPure`:

* the keys of a line are pairwise distinct (so `find?` returns *our* entry);
* every state in a line has `current_step = k + 1`, `map_parent = some` its key,
  and is valid (so `okJoin` holds whenever two states meet at one key, and the
  merge is a real `join`);
* every state in a line is `MapReachable φ` (so `AlongAssign.joinL` applies when
  our entry absorbs another).

With those, `mem_insertPure` and `mem_insertPure_of_ne` above carry the branch's
entry through both folds, and `pureRun` ends non-empty whenever `φ` is
satisfiable.

None of it is mathematical: it is the same argument `MirrorTest`'s own timeline
makes, and `lake exe cnfmap --driver` checks the whole loop against the real one
end to end.
-/

end AbsSat.GraphPath.Model.PureDriver
