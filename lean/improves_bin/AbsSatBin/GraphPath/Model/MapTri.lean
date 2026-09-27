-- lean/improves_bin/AbsSatBin/GraphPath/Model/MapTri.lean
import AbsSatBin.GraphPath.Model.NoDeadEnd
import AbsSatBin.GraphPath.Model.KernelSplit

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
* **`KExt`**: the same statement about kernels: every valid kernel pruned from `g₀` narrows, at the step of any of
  its nodes, to a valid kernel below it that names one map node there. It needs no reader.
* **`fExt_of_kExt`**: every valid `ReadAny` state is a kernel pruned from the start, and a pin survives when a valid
  kernel below agrees with it (`Kernel.isValid_filterAll_of_kernel`), so `KExt ⇒ FExt`.
  **`readerVerdictW_iff_of_kExt`**: the reader decides under `KExt` of the starting states.
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
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.Threaded (OwnSymmetric)

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

-- ============================================================
-- `KExt`: the statement about kernels
-- ============================================================

/-- **`KExt`**: a valid kernel pruned from `g₀` narrows, at the step of any of its nodes, to a valid kernel below it
that names one map node there. -/
def KExt (g₀ : GPathM) : Prop :=
  ∀ h, Kernel h → isValid h = true → Pruned g₀ h → ∀ q ∈ h.gowners, ∃ h' x, Kernel h' ∧ isValid h' = true ∧
    Below h h' ∧ x ∈ h'.gowners ∧ x.id.step = q.id.step ∧ ∀ y ∈ h'.gowners, y.id.step = q.id.step → y.id = x.id

theorem pruned_readAny (g₀ g : GPathM) (h : ReadAny g₀ g) : Pruned g₀ g := by
  induction h with
  | start => exact Pruned.refl _
  | pin g _ q _ _ _ _ ih => exact Pruned.trans ih (pruned_filterAll g [q.id])

theorem binCtx_readAny (g₀ : GPathM) (h₀ : PinChainBin.BinCtx φ g₀) (g : GPathM) (hA : ReadAny g₀ g) :
    PinChainBin.BinCtx φ g := by
  induction hA with
  | start => exact h₀
  | pin g _ q _ _ _ _ ih => exact PinChainBin.binCtx_filterAll φ g ih [q.id]

theorem sym_readAny (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ) :
    ∀ g, ReadAny (filterAll kv.2 []) g → isValid g = true → OwnSymmetric g := by
  obtain ⟨c, s⟩ := SymMachine.machine_ctx φ hbd kv hkv
  have b₀ := PinChainBin.binCtx_start φ hbd kv hkv
  intro g hA
  induction hA with
  | start => exact fun hv => PairInactive.OwnSymmetric_review _ (SymMachine.revOk_foldl kv.2 c s []) hv
  | pin g k q hA hv _ hv' ih =>
    intro _
    have cg := (binCtx_readAny φ _ b₀ g hA).rctx
    exact PairInactive.OwnSymmetric_review _ (SymMachine.revOk_foldl g cg (ih hv) [q.id]) hv'

/-- **Every valid `ReadAny` state is a kernel.** -/
theorem kernel_readAny (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (g : GPathM) (hA : ReadAny (filterAll kv.2 []) g) (hv : isValid g = true) : Kernel g := by
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hok := Decision.stateOk_pureRun φ hzero kv hkv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd kv.2 hok.reach
  obtain ⟨cm, sm⟩ := SymMachine.machine_ctx φ hbd kv hkv
  have abm := KernelReader.ownAbove_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have b₀ := PinChainBin.binCtx_start φ hbd kv hkv
  cases hA with
  | start => exact KernelReader.kernel_of_review kv.2 cm sm abm hv
  | pin g' k q hA' hv' _ _ =>
    have cg' := (binCtx_readAny φ _ b₀ g' hA').rctx
    have sg' := sym_readAny φ hbd kv hkv g' hA' hv'
    have abg' := KernelReader.ownAbove_of_pruned
      (Pruned.trans (pruned_filterAll kv.2 []) (pruned_readAny _ g' hA')) abm
    have cX : Reader.RCtx ([q.id].foldl filterRequire g') :=
      ReaderAgg.RCtx_of_keeps (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire [q.id] g') cg'
    have abX : KernelReader.OwnAbove ([q.id].foldl filterRequire g') := by
      intro n hn; rw [SymMachine.foldl_filterRequire_nodes] at hn; exact abg' n hn
    exact KernelReader.kernel_of_review _ cX (SymMachine.sym_foldl_filterRequire [q.id] g' sg') abX hv

/-- **`KExt ⇒ FExt`** on the starting states of the machine. -/
theorem fExt_of_kExt (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (hk : KExt (filterAll kv.2 [])) : FExt (filterAll kv.2 []) := by
  intro g hA hv k hc
  obtain ⟨q, hq, _⟩ := List.any_eq_true.mp hc
  obtain ⟨hqg, hqs⟩ := List.mem_filter.mp hq
  have hqk : q.id.step = k := eq_of_beq hqs
  obtain ⟨h', x, hk', hv', hb, hx, hxs, hpin⟩ :=
    hk g (kernel_readAny φ hbd kv hkv g hA hv) hv (pruned_readAny _ g hA) q hqg
  refine ⟨x, List.mem_filter.mpr ⟨hb.gow x hx, beq_iff_eq.mpr (by rw [hxs, hqk])⟩, ?_⟩
  refine isValid_filterAll_of_kernel hk' hv' hb [x.id] (fun r hr y hy hys => ?_)
  rw [List.mem_singleton.mp hr] at hys ⊢
  exact hpin y hy (by rw [hys, hxs])

/-- **The reader decides under `KExt`** of the starting states. -/
theorem readerVerdictW_iff_of_kExt (hbd : Bounded φ)
    (hke : ∀ kv ∈ pureRun φ, KExt (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_fExt φ hbd (fun kv hkv => fExt_of_kExt φ hbd kv hkv (hke kv hkv))

end AbsSatBin.GraphPath.Model.MapTri

/-- info: 'AbsSatBin.GraphPath.Model.MapTri.readerVerdictW_iff_of_fExt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.MapTri.readerVerdictW_iff_of_fExt

/-- info: 'AbsSatBin.GraphPath.Model.MapTri.readerVerdictW_iff_of_kExt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.MapTri.readerVerdictW_iff_of_kExt
