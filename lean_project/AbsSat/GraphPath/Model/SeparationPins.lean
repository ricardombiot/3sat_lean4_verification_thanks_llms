-- lean_project/AbsSat/GraphPath/Model/SeparationPins.lean
import AbsSat.GraphPath.Model.PureDriverPins
import AbsSat.GraphPath.Model.ReviewWorkImproves
import AbsSat.GraphPath.Model.Candidates
import AbsSat.GraphPath.Model.SelfOwn

/-!
# Separation: after the pin prune, the review only works beyond the pins

The pin prune (`PureDriverPins.pinPrune`) removes everything whose id
contradicts a pin of the destination `d`. This module proves that this is a
clean split of the review's work at every send of the reference machine:

1. **Nothing pairwise reaches the review** (`noPinConflict_review_start`,
   `noPinConflict_of_pruned`). On the state the improved review starts from, and
   on every narrowing of it — every state the review passes through, and its
   result — no global owner, no node and no owners entry contradicts a pin of `d`.
   By construction.
2. **The prune only does the review's work** (`review_gowners_survive_pins`,
   `review_node_not_idContradicts`). The base review keeps no global owner and no
   node the prune removes, and no owners entry inside the step range that
   contradicts a pin. This is `IdDiesProof.idDies` (such an owner is in the
   removal closure) and `RemovalClosure.unsupported_removed` (the review removes
   the closure), read through the review's fixpoint facts: a surviving node owns
   itself (`SelfOwn.OOS`) and its owners are global owners
   (`Candidates.owner_mem_gowners`).

So what the improved review still removes is never a direct conflict with a pin:
it is the cascade — nodes left without support or parents because others fell.

## What is not claimed

That the two reviews end in the same state, and how much cascade remains, are
measured (`lake exe improves-diff`: identical results; the cascade is 0.1–8 % of
the base review's removals), not proved. Nor is conservation for the pin prune
driver proved here.
-/

namespace AbsSat.GraphPath.Model.SeparationPins

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.IdSeparator (IdContradicts)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeakAll)
open AbsSat.GraphPath.Model.PureDriverPins (pinValues contradictsB pinPrune)

variable (φ : Cnf)

-- ============================================================
-- The Bool test is `IdContradicts`
-- ============================================================

theorem contradictsB_iff (d : NodeId) (w : PathNodeId) :
    contradictsB φ (pinValues φ d) w = true ↔ IdContradicts φ (reqOfCnf φ d) w := by
  unfold contradictsB pinValues IdContradicts
  constructor
  · intro h
    obtain ⟨vv, hvv, h1⟩ := List.any_eq_true.mp h
    obtain ⟨pv, hpv, h2⟩ := List.any_eq_true.mp h1
    obtain ⟨r, hr, hvr⟩ := List.mem_filterMap.mp hpv
    rw [Bool.and_eq_true] at h2
    refine ⟨vv, hvv, r, hr, pv, hvr, eq_of_beq h2.1, fun he => ?_⟩
    have h22 := h2.2
    rw [he, bne_self_eq_false] at h22
    cases h22
  · rintro ⟨vv, hvv, r, hr, pv, hvr, h1, h2⟩
    refine List.any_eq_true.mpr ⟨vv, hvv, List.any_eq_true.mpr
      ⟨pv, List.mem_filterMap.mpr ⟨r, hr, hvr⟩, ?_⟩⟩
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr h1, bne_iff_ne.mpr h2⟩

theorem not_idContradicts_of_kept (d : NodeId) {w : PathNodeId}
    (h : (!contradictsB φ (pinValues φ d) w) = true) : ¬ IdContradicts φ (reqOfCnf φ d) w := by
  intro hc
  rw [(contradictsB_iff φ d w).mpr hc] at h
  exact absurd h (by decide)

-- ============================================================
-- What the prune leaves
-- ============================================================

theorem pruned_pinPrune (d : NodeId) (g : GPathM) : Pruned g (pinPrune φ d g) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n' hn' := by
    simp only [pinPrune] at hn'
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hn'
    exact ⟨n, (List.mem_filter.mp hn).1, rfl, fun _ hq => (List.mem_filter.mp hq).1,
      fun _ hp => (List.mem_filter.mp hp).1⟩

theorem mem_pinPrune_gowners (d : NodeId) (g : GPathM) (q : PathNodeId) :
    q ∈ (pinPrune φ d g).gowners ↔ q ∈ g.gowners ∧ ¬ IdContradicts φ (reqOfCnf φ d) q := by
  show q ∈ g.gowners.filter (fun q => !contradictsB φ (pinValues φ d) q) ↔ _
  rw [List.mem_filter]
  cases hc : contradictsB φ (pinValues φ d) q with
  | false =>
    have hn : ¬ IdContradicts φ (reqOfCnf φ d) q := fun h => by
      rw [(contradictsB_iff φ d q).mpr h] at hc
      cases hc
    exact ⟨fun h => ⟨h.1, hn⟩, fun h => ⟨h.1, rfl⟩⟩
  | true =>
    have hy := (contradictsB_iff φ d q).mp hc
    exact ⟨fun h => absurd h.2 (by decide), fun h => absurd hy h.2⟩

theorem pinPrune_nodes (d : NodeId) (g : GPathM) :
    ∀ n ∈ (pinPrune φ d g).nodes, ¬ IdContradicts φ (reqOfCnf φ d) n.id ∧
      ∀ o ∈ n.owners, ¬ IdContradicts φ (reqOfCnf φ d) o := by
  intro n' hn'
  simp only [pinPrune] at hn'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hn'
  exact ⟨not_idContradicts_of_kept φ d (List.mem_filter.mp hn).2,
    fun o ho => not_idContradicts_of_kept φ d (List.mem_filter.mp ho).2⟩

/-- No global owner, node or owners entry contradicts a pin of `d`. -/
def NoPinConflict (d : NodeId) (P : GPathM) : Prop :=
  (∀ q ∈ P.gowners, ¬ IdContradicts φ (reqOfCnf φ d) q) ∧
  ∀ n ∈ P.nodes, ¬ IdContradicts φ (reqOfCnf φ d) n.id ∧
    ∀ o ∈ n.owners, ¬ IdContradicts φ (reqOfCnf φ d) o

theorem noPinConflict_pinPrune (d : NodeId) (g : GPathM) : NoPinConflict φ d (pinPrune φ d g) :=
  ⟨fun q hq => ((mem_pinPrune_gowners φ d g q).mp hq).2, pinPrune_nodes φ d g⟩

/-- Narrowing never brings a conflict back. -/
theorem noPinConflict_of_pruned {d : NodeId} {P P' : GPathM} (hpr : Pruned P P')
    (h : NoPinConflict φ d P) : NoPinConflict φ d P' := by
  refine ⟨fun q hq => h.1 q (hpr.gowners_sub q hq), fun n' hn' => ?_⟩
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
  obtain ⟨h1, h2⟩ := h.2 n hn
  exact ⟨by rw [hid]; exact h1, fun o ho => h2 o (hown o ho)⟩

/-- **Separation, part 1.** The state the improved review starts from has no
conflict with a pin of `d`; with `noPinConflict_of_pruned` neither does any state
the review passes through, nor its result. -/
theorem noPinConflict_review_start (d : NodeId) (g : GPathM) :
    NoPinConflict φ d ((reqOfCnf φ d).foldl filterRequire
      (pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d)))) :=
  noPinConflict_of_pruned φ (pruned_foldl _ pruned_filterRequire _ _) (noPinConflict_pinPrune φ d _)

theorem noPinConflict_improved_review (d : NodeId) (g : GPathM) :
    NoPinConflict φ d (filterAll (pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d))) (reqOfCnf φ d)) :=
  noPinConflict_of_pruned φ (pruned_review _) (noPinConflict_review_start φ d g)

-- ============================================================
-- The base review keeps nothing the prune removes
-- ============================================================

theorem mapNodes_nonneg (k : Int) (x : NodeId) (h : x ∈ mapNodes φ k) : 0 ≤ k := by
  by_cases hk : k < 0
  · unfold mapNodes at h
    rw [if_pos hk] at h
    exact absurd h List.not_mem_nil
  · omega

theorem not_idContradicts_of_review_gowner (hwf : WF φ) (g : GPathM) (hr : Reachable (reqOfCnf φ) g)
    (d : NodeId) (hd : d.step = g.current_step)
    (hv : isValid (filterAll g (reqOfCnf φ d)) = true)
    (q : PathNodeId) (hq : q ∈ (filterAll g (reqOfCnf φ d)).gowners) :
    ¬ IdContradicts φ (reqOfCnf φ d) q := by
  intro hc
  have hq0 : q ∈ ((reqOfCnf φ d).foldl filterRequire g).gowners := (pruned_review _).gowners_sub q hq
  have hu := IdDiesProof.idDies φ hwf g hr d hd q hc hq0
  have hnone := RemovalClosure.unsupported_removed (reqOfCnf φ) g hr (reqOfCnf φ d) hv hu
  obtain ⟨n, hn', hid⟩ :=
    GownersNodes.GN_filterAll g _ (GownersNodes.GN_reachable (reqOfCnf φ) g hr) q hq
  have hfind := List.find?_eq_none.mp hnone n hn'
  exact hfind (by simp [hid])

/-- **Separation, part 2 (global owners).** Every global owner the base review
keeps survives both the weak filter and the pin prune. -/
theorem review_gowners_survive_pins (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g)
    (d : NodeId) (hd : d.step = g.current_step)
    (hv : isValid (filterAll g (reqOfCnf φ d)) = true) :
    ∀ q ∈ (filterAll g (reqOfCnf φ d)).gowners,
      q ∈ (pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d))).gowners := by
  intro q hq
  have hr := reachable_of_mapReachable φ hwf g hmr
  exact (mem_pinPrune_gowners φ d _ q).mpr
    ⟨ReviewWorkImproves.review_gowners_survive_weak φ hwf g hmr d hd hv q hq,
     not_idContradicts_of_review_gowner φ hwf g hr d hd hv q hq⟩

/-- **Separation, part 2 (nodes and owners tables).** A node the base review keeps
does not contradict a pin — so the prune would not have removed it — and neither
does any entry of its owners table inside the step range. -/
theorem review_node_not_idContradicts (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g)
    (d : NodeId) (hd : d.step = g.current_step)
    (hv : isValid (filterAll g (reqOfCnf φ d)) = true)
    (pid : PathNodeId) (n : PNodeM) (hn : (filterAll g (reqOfCnf φ d)).node? pid = some n) :
    ¬ IdContradicts φ (reqOfCnf φ d) pid ∧
      ∀ o ∈ n.owners, 0 ≤ o.id.step → o.id.step < g.current_step →
        ¬ IdContradicts φ (reqOfCnf φ d) o := by
  have hr := reachable_of_mapReachable φ hwf g hmr
  have hpf := pruned_filterAll g (reqOfCnf φ d)
  have howner : ∀ o ∈ n.owners, 0 ≤ o.id.step → o.id.step < g.current_step →
      ¬ IdContradicts φ (reqOfCnf φ d) o := by
    intro o ho hlo hhi
    have hog := Candidates.owner_mem_gowners ((reqOfCnf φ d).foldl filterRequire g) hv pid n hn o ho
      hlo (by rw [show (review ((reqOfCnf φ d).foldl filterRequire g)).current_step = g.current_step
        from hpf.step_eq]; exact hhi)
    exact not_idContradicts_of_review_gowner φ hwf g hr d hd hv o hog
  refine ⟨?_, howner⟩
  have hmem : n ∈ (filterAll g (reqOfCnf φ d)).nodes := List.mem_of_find?_eq_some hn
  have hnid : n.id = pid := node?_id_eq _ pid n hn
  have hbelow := Certifies.nodes_below_of_pruned hpf (steps_below_current (reqOfCnf φ) hr) n hmem
  have hmap := NodesOnMap_filterAll φ g (reqOfCnf φ d) (nodesOnMap_of_mapReachable φ g hmr) n hmem
  have h0 : 0 ≤ n.id.id.step := mapNodes_nonneg φ _ _ hmap
  have hent := LocalContradiction.ownersOk_of_isValidNode _ n
    (review_node_valid ((reqOfCnf φ d).foldl filterRequire g) hv pid n hn) n.id.id.step h0 hbelow
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨o, ho, hos⟩ := hent
  have hoo : o = n.id := SelfOwn.OOS_filterAll g _ (SelfOwn.OOS_reachable (reqOfCnf φ) g hr) n hmem o ho hos
  have hc := howner o ho (by rw [hos]; exact h0) (by rw [hos]; rw [hpf.step_eq] at hbelow; exact hbelow)
  rw [hoo, hnid] at hc
  exact hc

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.SeparationPins.noPinConflict_improved_review' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noPinConflict_improved_review

/-- info: 'AbsSat.GraphPath.Model.SeparationPins.review_gowners_survive_pins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_gowners_survive_pins

/-- info: 'AbsSat.GraphPath.Model.SeparationPins.review_node_not_idContradicts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_node_not_idContradicts

end AbsSat.GraphPath.Model.SeparationPins
