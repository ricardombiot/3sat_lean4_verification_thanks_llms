-- lean_project/AbsSat/GraphPath/Model/FilterDescent.lean
import AbsSat.GraphPath.Model.DescentInvariant

/-!
# No dead ends after a filter, in subset terms

The third case of the induction, stated at the top step (the form `SendExact` consumes). For a
reachable state `g` whose filter is valid:

    NoDeadEnd (filterAll g reqs)  ↔  PinnedCompletion g reqs

`PinnedCompletion g reqs` — every partial chain from the top step that **survives the filter**
is the top of a **full** `ChainSound` chain of `g` that goes through every pin.

* `←` a full chain of `g` through the pins survives the filter (`ChainSound_filterAll`), and its
  pick at `lo - 1` is the extension.
* `→` descending with no dead ends gives a full chain of the filtered state; it was a chain of
  `g` (`ChainSound_of_pruned`), and it goes through the pins (`pinned_step_pure`).

So what the review has to guarantee is exactly this: it removes every partial chain from the top
whose completions in `g` all miss a pin. `SendExact_of_pinnedCompletion` closes the loop with
`SendExact`.
-/

namespace AbsSat.GraphPath.Model.FilterDescent

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.SubsetSemantics
open AbsSat.GraphPath.Model.EmptinessReduction
open AbsSat.GraphPath.Model.UnitPropagation
open AbsSat.GraphPath.Model.NoDeadEnd
open AbsSat.GraphPath.Model.DescentInvariant

theorem soundOn_mono_lo {g : GPathM} {sel : Int → PathNodeId} {lo hi : Int} (lo' : Int)
    (h : SoundOn g sel lo hi) (hle : lo ≤ lo') : SoundOn g sel lo' hi :=
  ⟨fun k h1 h2 => h.node k (by omega) h2, fun k h1 h2 => h.parent_link k (by omega) h2,
   fun i j hi1 hj1 hi2 hj2 hne => h.owned i j (by omega) (by omega) hi2 hj2 hne,
   fun k h1 h2 => h.gowner k (by omega) h2, fun k h1 h2 => h.self_owned k (by omega) h2,
   fun k h1 h2 => h.son_link k (by omega) h2, fun k h1 h2 => h.root_shape k (by omega) h2⟩

/-- Every partial chain from the top step that survives the filter is the top of a full chain
of `g` through every pin. -/
def PinnedCompletion (g : GPathM) (reqs : List NodeId) : Prop :=
  ∀ sel lo, 0 < lo → lo ≤ g.current_step - 1 → SoundFrom (filterAll g reqs) sel lo →
    ∃ sel', ChainSound g sel' ∧ (∀ k, lo ≤ k → k < g.current_step → sel' k = sel k) ∧
      ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel' req.step).id = req

/-- **No dead ends after the filter is exactly pinned completion.** -/
theorem noDeadEnd_filterAll_iff (reqOf : NodeId → List NodeId) (g : GPathM)
    (hr : Reachable reqOf g) (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true) :
    NoDeadEnd (filterAll g reqs) ↔ PinnedCompletion g reqs := by
  have hpr := pruned_filterAll g reqs
  have hstep : (filterAll g reqs).current_step = g.current_step := hpr.step_eq
  constructor
  · intro hnd sel lo hlo hlc hs
    have hpos : 0 < (filterAll g reqs).current_step := by omega
    obtain ⟨sel', hag, hs0⟩ :=
      descend _ hnd lo.toNat sel lo (Nat.le_refl _) (by omega) (by omega) hs
    have hch := (chainSound_iff_soundFrom_zero _ sel' hpos).mpr hs0
    refine ⟨sel', ChainSound_of_pruned hpr (Reader.NodupIds_reachable reqOf g hr)
      (Sons.SMP_reachable reqOf g hr) sel' hch, fun k hk _ => hag k hk,
      fun req hreq h0 hlt => ?_⟩
    obtain ⟨hsome, hsst⟩ := hch.chain.1.1 req.step h0 (by omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    have hnmem : n ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hn
    have hnid : n.id = sel' req.step := node?_id_eq _ _ n hn
    have hpure := pinned_step_pure g (SelfOwn.OOS_reachable reqOf g hr) reqs hv req hreq hlt h0
      n hnmem (by rw [hnid, hsst])
    rw [hnid] at hpure
    exact hpure
  · intro hpc sel lo hlo hlc hs
    have hpos : 0 < (filterAll g reqs).current_step := by omega
    obtain ⟨sel', hcs, hag, hpin⟩ := hpc sel lo hlo (by omega) hs
    have hch : ChainSound (filterAll g reqs) sel' := ChainSound_filterAll g reqs sel' hcs hpin
    have hfrom := (chainSound_iff_soundFrom_zero _ sel' hpos).mp hch
    refine ⟨sel' (lo - 1), soundFrom_of_soundOn (soundOn_congr (fun k h1 h2 => ?_)
      (soundOn_mono_lo (lo - 1) (soundOn_of_soundFrom hfrom) (by omega)))⟩
    unfold upd
    rcases int_eq_or_ne k (lo - 1) with hk | hk
    · rw [if_pos hk, hk]
    · rw [if_neg hk]
      exact hag k (by omega) (by omega)

/-- **`SendExact` from pinned completion** at every filter the driver performs. -/
theorem SendExact_of_pinnedCompletion (φ : Cnf) (hwf : WF φ)
    (h : ∀ (g : GPathM) (d : NodeId), MapReachable φ g → isValid g = true →
      (∃ p, denotS g p) → d.step = g.current_step → d ∈ mapNodes φ d.step →
      isValid (filterAll g (reqOfCnf φ d)) = true → PinnedCompletion g (reqOfCnf φ d)) :
    SendExact φ :=
  SendExact_of_FilterNoDeadEnd φ hwf (fun g d hmr hv hne hd hdm hfv =>
    (noDeadEnd_filterAll_iff (reqOfCnf φ) g (reachable_of_mapReachable φ hwf g hmr) _ hfv).mpr
      (h g d hmr hv hne hd hdm hfv))

/-- info: 'AbsSat.GraphPath.Model.FilterDescent.noDeadEnd_filterAll_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_filterAll_iff

/-- info: 'AbsSat.GraphPath.Model.FilterDescent.SendExact_of_pinnedCompletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SendExact_of_pinnedCompletion

end AbsSat.GraphPath.Model.FilterDescent
