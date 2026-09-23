-- lean_project/AbsSat/GraphPath/Model/CleanTwoPhaseAOk.lean
import AbsSat.GraphPath.Model.CleanTwoPhase
import AbsSat.GraphPath.Model.AnchoredSurvive

/-!
# A supported set survives `cleanInvalid₂` (plan step 6, brick 5b)

The mirror of `AnchoredSurvive.AOk_cleanInvalid` for the two-phase version, by the same route as
`ChainSound_cleanInvalid₂`:

* **the cut** (`Sup_cutAll`): an `R`-owner of a member is a member, hence a global owner, so every
  cut keeps it; and the links `Sup` asks for join two members that own each other through `R`, so
  both ends admit them;
* **the purge**: a member's cut is a node of the cut graph, which is `Sup` and `SMP`, so it is valid
  (`AnchoredSurvive.isValidNode_self`) — the purge never removes a member.

`SMP` of the cut needs `NodupIds` (the admission test looks nodes up by id), so the lemma takes it;
it is part of the reader's context `RCtx`.
-/

namespace AbsSat.GraphPath.Model.CleanTwoPhase

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk)

variable {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- A link `c — x` between two members that own each other through `R` survives the cut of `x`. -/
theorem mem_cut_link (g : GPathM) (h : Sup g S R) (x c : PathNodeId) (hxc : R x c) (hcx : R c x)
    (d : PNodeM) (hd : g.node? x = some d) (l : List PathNodeId) (hl : c ∈ l) :
    c ∈ l.filter (fun p => (cutOwners g.gowners d).contains p && admits g.gowners g p d.id) := by
  have hdid : d.id = x := node?_id_eq g x d hd
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.node c (h.dom x c hxc).2)
  refine List.mem_filter.mpr ⟨hl, (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩⟩
  · exact contains_cut _ d c (h.own x c d hxc hd) (h.gow c (h.dom x c hxc).2)
  · rw [hdid]
    exact admits_of_node _ g c m hm x (h.own c x m hcx hm) (h.gow x (h.dom x c hxc).1)

theorem Sup_cutAll (g : GPathM) (h : Sup g S R) : Sup (cutAll g) S R := by
  have hnode : ∀ p d', (cutAll g).node? p = some d' →
      ∃ d, g.node? p = some d ∧ d' = cutNode g.gowners g d := by
    intro p d' hd'
    rw [node?_cutAll] at hd'
    cases hd : g.node? p with
    | none => rw [hd] at hd'; exact absurd hd' (by simp)
    | some d =>
      rw [hd] at hd'
      exact ⟨d, rfl, (Option.some.inj hd').symm⟩
  refine ⟨h.gow, ?_, h.step, h.dom, ?_, h.cov, ?_, ?_, h.agg, h.sym, ?_⟩
  · intro p hp
    rw [node?_cutAll]
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    rw [hd]; rfl
  · intro x v n' hr hn'
    obtain ⟨d, hd, rfl⟩ := hnode x n' hn'
    exact mem_intersectOwners_of_mem _ _ v (h.own x v d hr hd) (h.gow v (h.dom x v hr).2)
  · intro x d' hS hd' hroot v hr
    obtain ⟨d, hd, rfl⟩ := hnode x d' hd'
    obtain ⟨c, hc, h1, h2, h3⟩ := h.par x d hS hd hroot v hr
    exact ⟨c, mem_cut_link g h x c h1 h2 d hd _ hc, h1, h2, h3⟩
  · intro x hS hlast v hr
    obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := h.son x hS hlast v hr
    refine ⟨c, cutNode g.gowners g m, by rw [node?_cutAll, hm]; rfl, ?_, h1, h2, h3⟩
    exact mem_cut_link g h c x h2 h1 m hm _ hxm
  · intro x c d' hxc hcx hstep hd'
    obtain ⟨d, hd, rfl⟩ := hnode x d' hd'
    exact mem_cut_link g h x c hxc hcx d hd _ (h.link x c d hxc hcx hstep hd)

theorem AOk_cutAll (g : GPathM) (hnd : NodupIds g) (h : AOk g S R) : AOk (cutAll g) S R :=
  ⟨Sup_cutAll g h.sup, SMP_cutAll g hnd h.smp, Parents.NotRoot_of_pruned (pruned_cutAll g) h.nr⟩

/-- A member's cut is valid. -/
theorem cut_valid_of_member (g : GPathM) (hnd : NodupIds g) (h : AOk g S R) (id : PathNodeId)
    (n : PNodeM) (hn : g.node? id = some n) (hS : S id) :
    isValidNode g (cutNode g.gowners g n) = true := by
  have hc := AOk_cutAll g hnd h
  have hn' : (cutAll g).node? id = some (cutNode g.gowners g n) := by
    rw [node?_cutAll, hn]; rfl
  exact AnchoredSurvive.isValidNode_self (cutAll g) hc.sup hc.smp id _ hn' hS

theorem AOk_purgeStep (g : GPathM) (hnd : NodupIds g) (h : AOk g S R) (id : PathNodeId) :
    AOk (purgeStep g id) S R := by
  unfold purgeStep
  split
  · exact h
  · next n hn =>
    split
    · exact h
    · next hbad =>
      have hns : ¬ S id := fun hS => hbad (cut_valid_of_member g hnd h id n hn hS)
      exact ⟨AnchoredSurvive.Sup_removeNode g id h.sup hns, Sons.SMP_removeNode g id h.smp,
        Parents.NotRoot_of_pruned (pruned_removeNode g id) h.nr⟩

theorem AOk_purgeFuel : ∀ (fuel : Nat) (g : GPathM), NodupIds g → AOk g S R →
    AOk (purgeFuel fuel g) S R := by
  have hround : ∀ g, NodupIds g → AOk g S R → AOk (purgeRound g) S R := by
    intro g hnd hg
    rw [purgeRound_eq]
    generalize g.nodes.map (·.id) = ids
    induction ids generalizing g with
    | nil => exact hg
    | cons id rest ih =>
      exact ih _ (List.Sublist.nodup (keeps_purgeStep g id).2.2.2 hnd) (AOk_purgeStep g hnd hg id)
  intro fuel
  induction fuel with
  | zero => intro g _ hg; exact hg
  | succ k ih =>
    intro g hnd hg
    simp only [purgeFuel]
    split
    · split
      · exact ih _ (List.Sublist.nodup (keeps_purgeRound g).2.2.2 hnd) (hround g hnd hg)
      · exact hround g hnd hg
    · exact hg

/-- **A supported set survives `cleanInvalid₂`.** -/
theorem AOk_cleanInvalid₂ (g : GPathM) (hnd : NodupIds g) (h : AOk g S R) :
    AOk (cleanInvalid₂ g) S R :=
  AOk_cutAll _ (nodupIds_purgeFuel _ g hnd) (AOk_purgeFuel _ g hnd h)

/-- info: 'AbsSat.GraphPath.Model.CleanTwoPhase.AOk_cleanInvalid₂' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AOk_cleanInvalid₂

end AbsSat.GraphPath.Model.CleanTwoPhase
