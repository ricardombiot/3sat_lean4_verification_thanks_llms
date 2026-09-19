-- lean_project/AbsSat/GraphPath/Model/LiveSolution.lean
import AbsSat.GraphPath.Model.RunNoBorrow

/-!
# The core in the language of paths: a live value is part of a real solution

The history technique that proved no borrowing (v148) places paths that exist: every path of a state is a
genuine partial solution, and every genuine partial solution is in the state of its key. `LivePinUp`
asks for the other thing — that a path **exist** through a live value. This module states the core in
that language:

* **`livePinUp_of_onPath`** — `LivePinUp` follows from: *in a valid reader's state with the prefix
  decided, every live value of the next variable lies on a path of the state*.
* **`path_is_solution`** (no hypothesis) — a path of any state the reader reaches spells a model of `φ`.

So the core is exactly: **in a valid reader's state, a value that survives the review is part of a real
solution.**
-/

namespace AbsSat.GraphPath.Model.LiveSolution

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem)
open AbsSat.GraphPath.Model.PinExtends (RF rf_readFrom)
open AbsSat.GraphPath.Model.PinUp (Decided LivePinUp)

variable (φ : Cnf)

/-- **A live value on a path**: in a valid reader's state with the prefix decided, every live value of
the next variable lies on a path of the state. -/
def LiveOnPath (g₀ : GPathM) : Prop :=
  ∀ S, ReadFrom g₀ S → isValid S = true → ∀ v : Nat, v < φ.nVars →
    (∀ k, 0 ≤ k → k < 2 * (v : Int) → Decided S k) →
    ∀ a, Mem S a → a.id.step = 2 * (v : Int) → ∃ sel, ChainSound S sel ∧ sel a.id.step = a

/-- **`LivePinUp` from live values on paths**: the path through the value survives its pin. -/
theorem livePinUp_of_onPath {g₀ : GPathM} (h : LiveOnPath φ g₀) : LivePinUp φ g₀ := by
  intro S hS hv v hvn hpre a ha has
  obtain ⟨sel, hsc, hsa⟩ := h S hS hv v hvn hpre a ha has
  have hp := ChainSound_filterAllAgg S [a.id] sel hsc (fun r hr _ _ => by
    rw [List.mem_singleton.mp hr, hsa])
  exact PickInduction.isValid_of_ChainG _ sel hp.chain

/-- **Every path of a reader's state is a real solution** (no hypothesis). -/
theorem path_is_solution (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (h0 : RF (filterAllAgg kv.2 [])) {S : GPathM} (hS : ReadFrom (filterAllAgg kv.2 []) S)
    (sel : Int → PathNodeId) (hsc : ChainSound S sel) : Sat (CnfChain.decode sel) φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hpr := Pruned.trans (pruned_filterAllAgg kv.2 []) (rf_readFrom h0 hS).2
  exact ReaderComplete.sat_decode φ hwf kv hkv sel
    (SubsetSemantics.ChainSound_of_pruned hpr hm.rctx.nodup hm.smp sel hsc)

/-- info: 'AbsSat.GraphPath.Model.LiveSolution.livePinUp_of_onPath' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms livePinUp_of_onPath

/-- info: 'AbsSat.GraphPath.Model.LiveSolution.path_is_solution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms path_is_solution

end AbsSat.GraphPath.Model.LiveSolution
