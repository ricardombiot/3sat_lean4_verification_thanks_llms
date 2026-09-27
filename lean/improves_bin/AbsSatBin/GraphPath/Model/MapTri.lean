-- lean/improves_bin/AbsSatBin/GraphPath/Model/MapTri.lean
import AbsSatBin.GraphPath.Model.NoDeadEnd

/-!
# `FExt`: `CliqueTri` at the grain of the map

`CliqueTri`, `CertClique` and `FCert` speak of cliques of **path nodes**. In the joined states of
`clause_mix.cnf` and `clause_mix_sep.cnf` there are 20 triples of path nodes that are a clique with
witnesses at every step and lie on no chain of the state, not even after the review, nor after pinning
their map nodes (probes `triple_sem_probe.jl`, `joinpin_probe.jl`, docs/context/ambfar.md §4.2ξ). So
those invariants are false there. The reader never sees path nodes: it pins **map nodes**, and at that
grain every valid pin set measured has a chain through its pins.

* **`ReadAny`**: the states reached from `g₀` by pinning, one after another, any live map node of any
  step that keeps the state valid (each pin followed by its review, as the reader does), in any order.
* **`FExt g₀`**: at every valid such state, every step with a choice has a node whose pin keeps the
  state valid. It is the map version of `CliqueTri` (grow a valid pin set by one step) and, unlike
  `ProgressFirst`, it does not depend on the reader's order.
* **`progressFirst_of_fExt`**: the reader's states are `ReadAny` states, so `FExt ⇒ NoDeadEnd`.
* **`readerVerdictW_iff_of_fExt`**: the reader decides under `FExt` of the starting states.
-/

namespace AbsSatBin.GraphPath.Model.MapTri

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.PickInduction (choiceAt)

/-- States reached by valid pins of map nodes, in any order, each followed by its review. -/
inductive ReadAny (g₀ : GPathM) : GPathM → Prop where
  | start : ReadAny g₀ g₀
  | pin (g : GPathM) (k : Int) (q : PathNodeId) : ReadAny g₀ g → isValid g = true →
      q ∈ ownersAt g.gowners k → isValid (filterAll g [q.id]) = true → ReadAny g₀ (filterAll g [q.id])

/-- **`FExt`**: a valid pin set grows by one pin at every step with a choice. -/
def FExt (g₀ : GPathM) : Prop :=
  ∀ g, ReadAny g₀ g → isValid g = true → ∀ k, choiceAt g k = true →
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAll g [q.id]) = true

theorem readAny_of_readFirst (g₀ g : GPathM) (h : ReadFirst g₀ g) : ReadAny g₀ g := by
  induction h with
  | start => exact ReadAny.start
  | pin g k q _ hv _ hq hv' ih => exact ReadAny.pin g k q ih hv hq hv'

/-- **`FExt ⇒ NoDeadEnd`.** -/
theorem progressFirst_of_fExt (g₀ : GPathM) (h : FExt g₀) : ProgressFirst g₀ := by
  intro g hF hv k hf
  exact h g (readAny_of_readFirst g₀ g hF) hv k (choiceAt_of_firstChoice g k hf)

variable (φ : Cnf)

/-- **The reader decides under `FExt`** of the starting states. -/
theorem readerVerdictW_iff_of_fExt (hbd : Bounded φ)
    (hfe : ∀ kv ∈ pureRun φ, FExt (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  NoDeadEnd.readerVerdictW_iff_of_noDeadEnd φ hbd
    (fun kv hkv => progressFirst_of_fExt _ (hfe kv hkv))

end AbsSatBin.GraphPath.Model.MapTri

/-- info: 'AbsSatBin.GraphPath.Model.MapTri.readerVerdictW_iff_of_fExt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.MapTri.readerVerdictW_iff_of_fExt
