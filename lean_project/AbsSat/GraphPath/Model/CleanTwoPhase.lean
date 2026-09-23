-- lean_project/AbsSat/GraphPath/Model/CleanTwoPhase.lean
import AbsSat.GraphPath.Model.AggressiveReview

/-!
# `cleanInvalid` in two phases (report v181, §6)

The current `cleanInvalid` walks the nodes one by one, cutting each table with the global owners
*as they stand at that moment*. It depends on the order, and it leaves ids of nodes removed later
in the tables of nodes processed earlier. The two-phase version separates the two things it does:

1. **Purge, to a fixpoint** (`purgeFuel`): remove every node that *would* be invalid once cut
   against the current global owners, and repeat while something is removed. No table is touched.
2. **One cut** (`cutAll`): cut every surviving node against the final global owners.

What "cut" means (`cutNode`) is what the sequential sweep leaves behind once every node has been
processed: the owners intersected with the global ones, and a link `x — y` kept only when each end
admits the other (`relink` drops the links outside the node's own cut table, and
`unlinkIncompatible` drops the node from the neighbours outside it).

This module only holds the definitions and the review built on them; the lemmas come after the
probe `clean2` (`Probes/RowDegree.lean`) has compared it with the current review.
-/

namespace AbsSat.GraphPath.Model.CleanTwoPhase

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview (aggSweep)

/-- The owners of `n` cut against `gow`. -/
def cutOwners (gow : List PathNodeId) (n : PNodeM) : List PathNodeId :=
  intersectOwners n.owners gow

/-- `m`, cut against `gow`, still owns `x`. A missing node admits nothing. -/
def admits (gow : List PathNodeId) (g : GPathM) (m x : PathNodeId) : Bool :=
  match g.node? m with
  | some pm => (cutOwners gow pm).contains x
  | none => false

/-- A node cut against `gow`: owners intersected, and only the links both ends admit. -/
def cutNode (gow : List PathNodeId) (g : GPathM) (n : PNodeM) : PNodeM :=
  let ow := cutOwners gow n
  { n with owners := ow,
           parents := n.parents.filter (fun p => ow.contains p && admits gow g p n.id),
           sons := n.sons.filter (fun s => ow.contains s && admits gow g s n.id) }

/-- One purge round over a snapshot of the ids: a node that would be invalid once cut against the
current global owners is removed; removals are seen by the nodes that follow. -/
def purgeRound (g : GPathM) : GPathM :=
  (g.nodes.map (·.id)).foldl (fun g id =>
    match g.node? id with
    | none => g
    | some n => if isValidNode g (cutNode g.gowners g n) then g else removeNode g id) g

/-- Phase 1: purge rounds while the graph is valid and a round removes something. Every round
that continues removes a node, so `g.nodes.length + 1` units of fuel suffice. -/
def purgeFuel : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    if isValid g then
      let g' := purgeRound g
      if g'.nodes.length < g.nodes.length then purgeFuel fuel g' else g'
    else g

/-- Phase 2: every node cut against the final global owners, at once. -/
def cutAll (g : GPathM) : GPathM :=
  { g with nodes := g.nodes.map (cutNode g.gowners g) }

/-- **`cleanInvalid` in two phases.** -/
def cleanInvalid₂ (g : GPathM) : GPathM :=
  cutAll (purgeFuel (g.nodes.length + 1) g)

-- ============================================================
-- The review over it (same shape as `reviewPass` … `reviewAgg`)
-- ============================================================

def reviewPass₂ (g : GPathM) : GPathM :=
  reviewSons (reviewParents (cleanInvalid₂ g))

def reviewFuel₂ : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    if isValid g then
      let g' := reviewPass₂ g
      if measure g' < measure g then reviewFuel₂ fuel g' else g'
    else
      g

def review₂ (g : GPathM) : GPathM :=
  reviewFuel₂ (measure g + 1) g

def reviewAggFuel₂ : Nat → GPathM → GPathM
  | 0, g => review₂ g
  | fuel + 1, g =>
    let g₁ := review₂ g
    if isValid g₁ then
      let g₂ := aggSweep g₁
      if measure g₂ < measure g₁ then reviewAggFuel₂ fuel g₂ else g₁
    else g₁

def reviewAgg₂ (g : GPathM) : GPathM := reviewAggFuel₂ (measure g + 1) g

end AbsSat.GraphPath.Model.CleanTwoPhase
