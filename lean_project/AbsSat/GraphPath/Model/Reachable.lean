-- lean_project/AbsSat/GraphPath/Model/Reachable.lean
import AbsSat.GraphPath.Model.GPathM

/-!
Phase F3 of `docs/plans/espejo_gpathm_lema_L1.md`: the set of states the
machine actually builds, captured as an inductive predicate parameterized
by `reqOf : NodeId → List NodeId`.

The constructors carry the structural hypotheses that the concrete GMap
guarantees: seeds at step 0, UP nodes at the current step with
requirements strictly backward-pointing and pairwise step-distinct.
Lemma L7 will discharge these from the concrete driver.
-/

namespace AbsSat.GraphPath.Model

open AbsSat.Utils.Alias

variable (reqOf : NodeId → List NodeId)

inductive Reachable : GPathM → Prop where
  | seed (d : NodeId) (title : String) (hstep : d.step = 0)
      (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step) :
      Reachable (GPathM.initSeed d title)
  | up (g : GPathM) (d : NodeId) (title : String)
      (hstep : d.step = g.current_step)
      (hreqs_back : ∀ req, req ∈ reqOf d → req.step < d.step)
      (hreqs_distinct : ∀ r₁ r₂, r₁ ∈ reqOf d → r₂ ∈ reqOf d → r₁.step = r₂.step → r₁ = r₂) :
      Reachable g → Reachable (GPathM.upFiltering g (reqOf d) d title)
  | join (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂) :
      Reachable g₁ → Reachable g₂ → Reachable (GPathM.join g₁ g₂)

end AbsSat.GraphPath.Model
