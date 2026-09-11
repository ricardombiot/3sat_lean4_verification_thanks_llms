-- lean_project/AbsSat/GraphPath/Model/DownVerdict.lean
import AbsSat.GraphPath.Model.Extendable
import AbsSat.GraphPath.Model.PickInduction
import AbsSat.GraphPath.Model.GownersNodes

/-!
# The verdict from the descent alone

`Extendable.lean` reduces "no zombies" to backtrack-freeness in **both**
directions, and the upward half is refuted. This module spends the observation
`Verdict.lean` already recorded — that `Inhabited` needs a chain through **one**
node, not through every node — to drop the refuted half entirely.

Pick the node at the top step (`isValid` guarantees a global owner there, `GN`
makes it a node), and only `Extendable.ExtendDownTop` is left: the descent,
anchored at the top, which `lake exe extend --randomdowntop` measures
exhaustively at **0 dead ends in 9,331 chains**.

It lives in its own module because `PickInduction` imports `Extendable`, so the
assembly cannot go in either of them.
-/

namespace AbsSat.GraphPath.Model.DownVerdict

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Extendable

/-- **The verdict, from the descent alone.** `isValid` puts a global owner at
the top step, `GN` makes it a node, the descent threads it to step 0, and
`Verdict.Inhabited_of_SupportedAt` turns that one chain into the denotation.

`ExtendUp` — the refuted half — does not appear. -/
theorem Inhabited_of_ExtendDownTop (g : GPathM) (hgn : GownersNodes.GN g)
    (hpos : 0 < g.current_step) (hval : isValid g = true) (hdown : ExtendDownTop g) :
    AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨q, hq, hqs⟩ :=
    PickInduction.gowner_of_isValid g hval (g.current_step - 1) (by omega) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
  exact Verdict.Inhabited_of_SupportedAt g q
    (SupportedAt_top_of_ExtendDownTop g hdown q n hn hqs hpos)

/-- info: 'AbsSat.GraphPath.Model.Extendable.SupportedAt_top_of_ExtendDownTop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SupportedAt_top_of_ExtendDownTop

/-- info: 'AbsSat.GraphPath.Model.DownVerdict.Inhabited_of_ExtendDownTop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_ExtendDownTop


/-- **The verdict from the local statement.** Chaining
`ExtendDownTop_of_GoodParentOnCliques` with the reduction above: one node, its
parents and its owners decide the whole thing.

This is the shortest route from an open statement to the verdict the
development has: `GoodParentOnCliques` is universally quantified, node-local,
one step wide, and says nothing about chains. -/
theorem Inhabited_of_GoodParentOnCliques (g : GPathM) (hgn : GownersNodes.GN g)
    (hpos : 0 < g.current_step) (hval : isValid g = true)
    (hgp : GoodParentOnCliques g) : AbsSat.GraphPath.Model.Inhabited g :=
  Inhabited_of_ExtendDownTop g hgn hpos hval (ExtendDownTop_of_GoodParentOnCliques g hgp)

/-- info: 'AbsSat.GraphPath.Model.DownVerdict.Inhabited_of_GoodParentOnCliques' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_GoodParentOnCliques

end AbsSat.GraphPath.Model.DownVerdict
