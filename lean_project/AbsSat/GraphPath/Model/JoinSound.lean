-- lean_project/AbsSat/GraphPath/Model/JoinSound.lean
import AbsSat.GraphPath.Model.AddNode

/-!
L6's join case in `ChainSound` currency, completing the four preservation
lemmas — and an honest account of what that does and does not amount to.

`Grown` now tracks sons and global owners as well as owners and parents, which
is all `ChainSound` needs to travel forwards. `join` only ever adds, so
`ChainSound_of_grown` carries a chain from either side into the join.

## The four preservation lemmas are complete

| constructor | lemma |
|---|---|
| seed | `ChainSound_initSeed` (`AddNode.lean`) |
| up | `ChainSound_upFiltering` (`AddNode.lean`) |
| join | `ChainSound_join_left` / `_right` (here) |
| review | `ChainSound_review` (`Coherence.lean`) |

Together: **a chain that satisfies the requirements survives everything the
machine does.**

## Preservation is only half of L6, and the other half is still open

L6 says *every surviving node lies on some chain*. The lemmas above say
*a good chain survives*. Those are different statements, and three of the four
constructors close the gap by themselves — seed builds the chain, join takes
it from one side, `addNode` extends it, and none of them removes anything.

`filterAll` is the exception, and it is the whole remaining content:

    SupportedS g → SupportedS (filterAll g reqs)          -- NOT proved

From `SupportedS g` a surviving node has *some* chain, but that chain need not
satisfy the requirements, and `ChainSound_filterAll` only rescues the ones
that do. Closing this needs the converse of everything proved so far: that
`review` **removes** every node whose support died — that it leaves no
zombies. That is the original meaning of L6's name, and it is exactly the
property `lake exe l6search` has been unable to break over 1,680 states.

So: the "a chain cannot be cut" half is done, and it turned out not to need
the 3SAT structure. The "a node cannot outlive its chains" half has not been
attacked at all.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

theorem ChainSound_of_grown {g g' : GPathM} (hgr : Grown g g') (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound g' sel := by
  obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
  refine ⟨⟨IsChain_of_grown hgr sel hchain, PairwiseOwned_of_grown hgr sel howned, ?_⟩,
    ?_, ?_, ?_⟩
  · intro k hlo hhi
    rw [hgr.step_eq] at hhi
    exact hgr.gowners_grown _ (hgow k hlo hhi)
  · intro k hlo hhi
    rw [hgr.step_eq] at hhi
    have hs := hself k hlo hhi
    simp only [ownersOf] at hs ⊢
    cases hn : g.node? (sel k) with
    | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hn] at hs
      obtain ⟨n', hn', hown, _, _⟩ := hgr.node?_grown _ n hn
      rw [hn']
      exact hown _ hs
  · intro k hlo hhi
    rw [hgr.step_eq] at hhi
    have hs := hson k hlo hhi
    simp only [sonsOf] at hs ⊢
    cases hn : g.node? (sel k) with
    | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hn] at hs
      obtain ⟨n', hn', _, _, hsons⟩ := hgr.node?_grown _ n hn
      rw [hn']
      exact hsons _ hs
  · exact ⟨hroot.1, fun k hk hk' => hroot.2 k hk (by rw [hgr.step_eq] at hk'; exact hk')⟩

theorem ChainSound_join_left (g₁ g₂ : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g₁ sel) : ChainSound (join g₁ g₂) sel :=
  ChainSound_of_grown (grown_join_left g₁ g₂) sel h

theorem ChainSound_join_right (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (sel : Int → PathNodeId) (h : ChainSound g₂ sel) : ChainSound (join g₁ g₂) sel :=
  ChainSound_of_grown (grown_join_right g₁ g₂ hok) sel h

/-- **L6's join case, in `ChainSound` currency.** -/
theorem SupportedS_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : SupportedS g₁) (h₂ : SupportedS g₂) : SupportedS (join g₁ g₂) := by
  intro pid n hn
  rcases join_node?_source g₁ g₂ pid n hn with hs | hs
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨sel, hsel, htop⟩ := h₁ pid m hm
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel, htop⟩
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨sel, hsel, htop⟩ := h₂ pid m hm
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsel, htop⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.SupportedS_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SupportedS_join

/-- info: 'AbsSat.GraphPath.Model.ChainSound_of_grown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_of_grown

end AbsSat.GraphPath.Model
