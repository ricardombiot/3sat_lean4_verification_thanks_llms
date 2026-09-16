-- lean_project/AbsSat/GraphPath/Model/FinalReadable.lean
import AbsSat.GraphPath.Model.TopPhantom
import AbsSat.GraphPath.Model.ParentOwners
import AbsSat.GraphPath.Model.L6Up

/-!
# The obligation moved to the final line: readable without backtracking

`FilterNoDeadEnd` asked for no dead ends after **every** filter of the run. It is false as stated:
`Probes/cnf/top_phantom_s31337_4.cnf` has a filtered state meeting all its hypotheses with one
phantom anchored at the top (a pure Helly gap: every pick and every pair lies on a real chain, so no
sound review rule removes it; the next filter does).

The verdict only needs something about the states it reads, the ones in the final line. So the
obligation is restated there, and reduced to phantoms alone:

* `topAnchor_valid` — **every valid state the machine builds has a pick at the top.** By induction
  over `MapReachable`: after `up`, the node just added is one (it is a global owner and, since
  `addNode` makes it an owner of every node, it owns itself; `MachineOk` gives its root shape); a
  `join` grows its left side, which is valid, and growth keeps the pick (`topAnchor_grown`).
* `FinalReadable φ` — **no phantom is anchored at the top of any final state** (`NoTopPhantom`). By
  `TopPhantom.noDeadEnd_iff_noTopPhantom`, with the anchor above, this is exactly: a reader without
  backtracking can start at the top of every final state and never gets stuck.
* `final_nonempty` — then every final state holds a full chain.
* `soundness_of_FinalReadable`, `run_pure_decides_of_FinalReadable` — and the machine decides 3SAT
  (completeness is already unconditional, `PureProofs.completeness_pure`).

Unlike `SendExact`, nothing is asked of intermediate states: phantoms may appear and die along the
run. Measured with `lake exe join-borrow top` (20,369 states, 6–10 variables): 0 phantoms at the top
of any final state.

Open: `FinalReadable φ` for every well-formed φ.
-/

namespace AbsSat.GraphPath.Model.FinalReadable

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.SubsetSemantics
open AbsSat.GraphPath.Model.PartialPaths
open AbsSat.GraphPath.Model.NoDeadEnd
open AbsSat.GraphPath.Model.TopPhantom
open AbsSat.SatMachine.PureSatMachine
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.Certifies
open AbsSat.GraphPath.Model.ParentOwners

-- ============================================================
-- The top anchor, for every valid state the machine builds
-- ============================================================

/-- Growth keeps a pick at the top: its node, its owners and the global owners only grow. -/
theorem topAnchor_grown {g g' : GPathM} (hgr : Grown g g') (h : TopAnchor g) : TopAnchor g' := by
  obtain ⟨q, hq⟩ := h
  have hs := hgr.step_eq
  obtain ⟨hsome, hstep⟩ := hq.node (g.current_step - 1) (Int.le_refl _) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨n', hn', ho, _⟩ := hgr.node?_grown q n hn
  refine ⟨q, ⟨fun k h1 h2 => ⟨by show (g'.node? q).isSome; rw [hn']; rfl, by show q.id.step = k; omega⟩,
    fun k h1 h2 => by omega, fun i j hi hj hi2 hj2 hne => by omega,
    fun k h1 h2 => hgr.gowners_grown q (hq.gowner _ (Int.le_refl _) (by omega)),
    fun k h1 h2 => ?_, fun k h1 h2 => by omega,
    fun k h1 h2 => by
      have hk : k = g.current_step - 1 := by omega
      subst hk
      exact hq.root_shape _ (Int.le_refl _) (by omega)⟩⟩
  have hso := hq.self_owned _ (Int.le_refl _) (by omega)
  show q ∈ ownersOf g' q
  simp only [ownersOf, hn] at hso
  simp only [ownersOf, hn']
  exact ho q hso

/-- **The node `addNode` just created is a pick at the top.** -/
theorem topAnchor_addNode (f : GPathM) (d : NodeId) (title : String)
    (hd : d.step = f.current_step) (hmok : MachineOk f) : TopAnchor (addNode f d title) := by
  obtain ⟨h0, hz, hpos⟩ := hmok
  have hcur := addNode_current f d title
  have hmem : addOwner (newPid f d) (upNode f d title) ∈ (addNode f d title).nodes := by
    rw [addNode_nodes]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hsome : ((addNode f d title).node? (newPid f d)).isSome :=
    node?_isSome_of_mem (addNode f d title) _ hmem
  have hall : ∀ n ∈ (addNode f d title).nodes, newPid f d ∈ n.owners := by
    intro n hn
    rcases mem_addNode_nodes hn with ⟨m, _, rfl⟩ | rfl
    · rw [upMap_owners]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨newPid f d, ⟨fun k h1 h2 => ⟨hsome, ?_⟩, fun k h1 h2 => ?_,
    fun i j hi hj hi2 hj2 hne => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_,
    fun k h1 h2 => ?_⟩⟩
  · show d.step = k
    rw [hcur] at h1 h2
    omega
  · rw [hcur] at h1 h2
    omega
  · rw [hcur] at hi hj hi2 hj2
    omega
  · show newPid f d ∈ (addNode f d title).gowners
    rw [addNode_gowners]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · show newPid f d ∈ ownersOf (addNode f d title) (newPid f d)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    simp only [ownersOf, hn]
    exact hall n (List.mem_of_find?_eq_some hn)
  · rw [hcur] at h1 h2
    omega
  · rw [hcur] at h1 h2
    show (f.map_parent = none ↔ k = 0)
    constructor
    · intro hnone
      exact Decidable.byContradiction fun hne => hpos (by omega) hnone
    · intro hk0
      exact hz (by omega)

private theorem initSeed_eq (d : NodeId) (title : String) :
    initSeed d title = addNode empty d title := rfl

/-- **Every valid state the machine builds has a pick at the top.** -/
theorem topAnchor_valid (φ : Cnf) (hwf : WF φ) (g : GPathM) (h : MapReachable φ g)
    (hv : isValid g = true) : TopAnchor g := by
  induction h with
  | seed d title hstep _ =>
    rw [initSeed_eq]
    exact topAnchor_addNode empty d title hstep MachineOk_empty
  | up g d title hstep _ hg ih =>
    have hpr := pruned_filterAll g (reqOfCnf φ d)
    have hmok : MachineOk (filterAll g (reqOfCnf φ d)) :=
      MachineOk_of_pruned hpr
        (Certifies.MachineOk_reachable (reqOfCnf φ) g (reachable_of_mapReachable φ hwf g hg))
    simp only [upFiltering, up] at hv ⊢
    cases hf : isValid (filterAll g (reqOfCnf φ d)) with
    | false =>
      rw [hf] at hv
      simp only [Bool.false_eq_true, if_false] at hv
      rw [hf] at hv
      exact absurd hv (by simp)
    | true =>
      simp only [if_true]
      exact topAnchor_addNode _ d title (by rw [hpr.step_eq]; exact hstep) hmok
  | join g₁ g₂ hok _ _ ih₁ _ =>
    have hok' : okJoin g₁ g₂ = true := hok
    simp only [okJoin, Bool.and_eq_true] at hok'
    exact topAnchor_grown (grown_join_left g₁ g₂) (ih₁ hok'.1.2)

-- ============================================================
-- The obligation on the final line
-- ============================================================

/-- **The obligation, on the final line only: no phantom at the top.** -/
def FinalReadable (φ : Cnf) : Prop :=
  ∀ kv ∈ pureRun φ, NoTopPhantom kv.2

theorem noDeadEnd_final (φ : Cnf) (hr : FinalReadable φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRun φ) : NoDeadEnd kv.2 :=
  noDeadEnd_of_noTopPhantom (hr kv hkv)

private theorem pos_of_step (g : GPathM) (n : Nat) (h : g.current_step = (n : Int) + 1) :
    0 < g.current_step := by
  omega

/-- **Every final state holds a full chain.** -/
theorem final_nonempty (φ : Cnf) (hwf : WF φ) (hr : FinalReadable φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRun φ) : ∃ p, denotS kv.2 p := by
  have hkv' : kv ∈ lineAt φ (stepCount φ - 1).toNat := hkv
  have hok := (lineAt_ok φ _).2 kv hkv'
  exact nonempty_of_noDeadEnd kv.2 (pos_of_step kv.2 _ hok.step)
    (topAnchor_valid φ hwf kv.2 hok.reach hok.valid) (noDeadEnd_final φ hr kv hkv)

/-- **`FinalReadable` makes the machine sound.** -/
theorem soundness_of_FinalReadable (φ : Cnf) (hwf : WF φ) (hr : FinalReadable φ)
    (h : pureRun φ ≠ []) : Satisfiable φ := by
  obtain ⟨kv, hkv⟩ := List.exists_mem_of_ne_nil _ h
  have hkv' : kv ∈ lineAt φ (stepCount φ - 1).toNat := hkv
  obtain ⟨p, sel, hs, hp⟩ := final_nonempty φ hwf hr kv hkv
  obtain ⟨hchain, howned, _⟩ := hs.chain
  exact (satisfiable_iff_Phi_nonempty φ hwf).mpr ⟨p, kv, hkv', sel, hchain, howned, hp⟩

/-- **`FinalReadable` makes the machine decide 3SAT.** -/
theorem run_pure_decides_of_FinalReadable (φ : Cnf) (hwf : WF φ) (hr : FinalReadable φ) :
    is_satisfiable (run_pure φ) = true ↔ Satisfiable φ :=
  ⟨fun h => soundness_of_FinalReadable φ hwf hr
      ((AbsSat.SatMachine.PureProofs.is_satisfiable_run_pure_iff φ).mp h),
   AbsSat.SatMachine.PureProofs.completeness_pure φ hwf⟩

/-- info: 'AbsSat.GraphPath.Model.FinalReadable.topAnchor_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topAnchor_valid

/-- info: 'AbsSat.GraphPath.Model.FinalReadable.soundness_of_FinalReadable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundness_of_FinalReadable

/-- info: 'AbsSat.GraphPath.Model.FinalReadable.run_pure_decides_of_FinalReadable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_pure_decides_of_FinalReadable

end AbsSat.GraphPath.Model.FinalReadable
