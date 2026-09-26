-- lean/improves_bin/AbsSatBin/GraphPath/Model/PieceFilter.lean
import AbsSatBin.GraphPath.Model.ChainRoute

/-!
# The join is decompressed by filtering by the key of the source

Measured (`julia/improves_bin/test_3sat/probes/decompress_probe.jl`, D1): filtering a joined state `J` of
line `n+1` by the key `k` of the source of one of its pieces `A` gives back exactly `A`, table by table
(4 094 pieces of 4 094). The union loses nothing and can be undone.

* **`piece_survives_filter`** (the half `A ⊆ filter(J, {k})`, proved): the reviewed piece is a kernel
  (`KernelReader.kernel_of_review`), it sits below `J` (the join only adds, `PieceJoin.piece_grown`), and at
  step `n` it names only `k` (`PieceJoin.mid_key`). The review never goes below a kernel
  (`Kernel.below_filterAll`), so the whole reviewed piece survives the filter by its own key.
* The other half, `filter(J, {k}) ⊆ A` (no entry of the other piece survives), is open: it says that every
  entry left by the filter lies on a chain through `k`, the entry form of `NoDeadEnd`.
-/

namespace AbsSatBin.GraphPath.Model.PieceFilter

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel

/-- `Below` is transitive. -/
theorem below_trans {X Y Z : GPathM} (h₁ : Below X Y) (h₂ : Below Y Z) : Below X Z where
  step := h₁.step.trans h₂.step
  gow := fun q hq => h₁.gow q (h₂.gow q hq)
  node := fun p nz hz => by
    obtain ⟨ny, hny, hoy, hpy, hsy⟩ := h₂.node p nz hz
    obtain ⟨nx, hnx, hox, hpx, hsx⟩ := h₁.node p ny hny
    exact ⟨nx, hnx, fun q hq => hox q (hoy q hq), fun q hq => hpx q (hpy q hq), fun q hq => hsx q (hsy q hq)⟩

/-- A state sits below what it grows into. -/
theorem below_of_grown {g g' : GPathM} (h : Grown g g') : Below g' g where
  step := h.step_eq
  gow := h.gowners_grown
  node := h.node?_grown

variable (φ : Cnf) (hbd : Bounded φ) (n : Nat)
include hbd

/-- **The reviewed piece survives the filter of the joined state by the key of its source.** -/
theorem piece_survives_filter (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true)
    (hvr : isValid (review (upF φ kv.2 d)) = true) :
    ∃ J, (d, J) ∈ line φ (n + 1) ∧ Below (filterAll J [kv.1]) (review (upF φ kv.2 d)) := by
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hA : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd _ hA.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach
  have c := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) _ hnd hreach
  have hs := (SymMachine.symInv_reachable (reqOf φ) (isProhibited φ) _ hreach hv).1
  have hab := KernelReader.ownAbove_reachable (reqOf φ) (isProhibited φ) _ hreach
  have hk : Kernel (review (upF φ kv.2 d)) := KernelReader.kernel_of_review _ c hs hab hvr
  have hbA : Below (upF φ kv.2 d) (review (upF φ kv.2 d)) :=
    KernelIff.below_filterAll_self (upF φ kv.2 d) hnd []
  obtain ⟨J, hJ, hgr⟩ := PieceJoin.piece_grown φ n kv hkv d hd hv
  refine ⟨J, hJ, below_filterAll hk (below_trans (below_of_grown hgr) hbA) [kv.1] ?_⟩
  -- at step `n` the reviewed piece names only the key of its source
  intro r hr q hq hqs
  rw [List.mem_singleton.mp hr] at hqs ⊢
  have hkey : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 hok.onMap
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff _ q).mp (c.gn q (hbA.gow q hq)))
  exact PieceJoin.mid_key φ hbd n kv hkv d hd hv q nq hnq (by rw [hqs, hkey])

/-- info: 'AbsSatBin.GraphPath.Model.PieceFilter.piece_survives_filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms piece_survives_filter

end AbsSatBin.GraphPath.Model.PieceFilter
