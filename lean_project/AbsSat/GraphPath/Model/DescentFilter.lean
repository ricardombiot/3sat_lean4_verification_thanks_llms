-- lean_project/AbsSat/GraphPath/Model/DescentFilter.lean
import AbsSat.GraphPath.Model.DescentJoin

/-!
# The descent through the filter, by construction

The seed, the `up` and the join (on one side) keep the descent (`DescentUp`, `DescentJoin`). The
filter is the case that carries the whole weight, and this file states it in the form the author's
own reasoning gives it:

> the chosen extension cannot die to the pruning, because the review demands that at least one
> valid path exists

That is already a theorem for **complete** chains: `AggressiveReview.ChainSound_filterAllAgg` —
a chain of the state that respects the pins survives the pins and the whole aggressive review. It
is the no-solution-lost result. So the filter keeps the descent as soon as a partial chain of the
filtered state **completes**, inside the unfiltered state, to a full chain that respects the pins:

* `soundFrom_congr` — a partial chain only depends on its picks from `lo` up.
* `ReqCompletion` — the obligation: every partial chain of the filtered state extends downwards to
  a full `ChainSound` chain of the state that meets every requirement of the filter.
* **`noDeadEnd_filterAllAgg_of_completion`** — and then the filtered state has no dead ends: the
  completion survives the filter, and its pick one step below the chain is the extension.

So the residue of the whole induction is that completion, and only below the chain's lowest pick:
above it the picks are already in the filtered state, where every node of a pinned step carries the
pinned map node (`PairChain.node_id_of_pin`).
-/

namespace AbsSat.GraphPath.Model.DescentFilter

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview (filterAllAgg pruned_filterAllAgg ChainSound_filterAllAgg)
open AbsSat.GraphPath.Model.NoDeadEnd (SoundFrom upd NoDeadEnd chainSound_iff_soundFrom_zero)

/-- A partial chain only depends on its picks from `lo` up. -/
theorem soundFrom_congr {g : GPathM} {sel₀ sel₁ : Int → PathNodeId} {lo : Int}
    (hag : ∀ k, lo ≤ k → k < g.current_step → sel₁ k = sel₀ k)
    (hs : SoundFrom g sel₀ lo) : SoundFrom g sel₁ lo := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h1 h2; rw [hag k h1 h2]; exact hs.node k h1 h2
  · intro k h1 h2
    rw [hag k h1 (by omega), hag (k + 1) (by omega) h2]
    exact hs.parent_link k h1 h2
  · intro i j hi1 hj1 hi2 hj2 hij
    rw [hag i hi1 hi2, hag j hj1 hj2]
    exact hs.owned i j hi1 hj1 hi2 hj2 hij
  · intro k h1 h2; rw [hag k h1 h2]; exact hs.gowner k h1 h2
  · intro k h1 h2; rw [hag k h1 h2]; exact hs.self_owned k h1 h2
  · intro k h1 h2
    rw [hag k h1 (by omega), hag (k + 1) (by omega) h2]
    exact hs.son_link k h1 h2
  · intro k h1 h2; rw [hag k h1 h2]; exact hs.root_shape k h1 h2

/-- **The obligation.** Every partial chain of the filtered state completes, inside the state, to a
full chain that meets every requirement of the filter. -/
def ReqCompletion (g : GPathM) (reqs : List NodeId) : Prop :=
  ∀ sel lo, 0 < lo → lo ≤ (filterAllAgg g reqs).current_step - 1 →
    SoundFrom (filterAllAgg g reqs) sel lo →
    ∃ sel', ChainSound g sel' ∧
      (∀ k, lo ≤ k → k < g.current_step → sel' k = sel k) ∧
      (∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel' req.step).id = req)

/-- **The filter keeps the descent, given the completion.** The completed chain respects the pins,
so it survives them and the whole aggressive review — the author's "the review demands that at
least one valid path exists", which for complete chains is `ChainSound_filterAllAgg`. Its pick one
step below the partial chain is the extension. -/
theorem noDeadEnd_filterAllAgg_of_completion (g : GPathM) (reqs : List NodeId)
    (hpos : 0 < g.current_step) (h : ReqCompletion g reqs) :
    NoDeadEnd (filterAllAgg g reqs) := by
  have hstep : (filterAllAgg g reqs).current_step = g.current_step :=
    (pruned_filterAllAgg g reqs).step_eq
  intro sel lo hlo0 hlo hs
  obtain ⟨sel', hcs, hag, hreqs⟩ := h sel lo hlo0 hlo hs
  -- the completion survives the filter
  have hcsB : ChainSound (filterAllAgg g reqs) sel' := ChainSound_filterAllAgg g reqs sel' hcs hreqs
  have hsB : SoundFrom (filterAllAgg g reqs) sel' 0 :=
    (chainSound_iff_soundFrom_zero (filterAllAgg g reqs) sel' (by rw [hstep]; exact hpos)).mp hcsB
  -- so it is a partial chain from one step below, and it agrees with ours above
  have hsB' : SoundFrom (filterAllAgg g reqs) sel' (lo - 1) :=
    ⟨fun k h1 h2 => hsB.node k (by omega) h2,
      fun k h1 h2 => hsB.parent_link k (by omega) h2,
      fun i j hi1 hj1 hi2 hj2 hij => hsB.owned i j (by omega) (by omega) hi2 hj2 hij,
      fun k h1 h2 => hsB.gowner k (by omega) h2,
      fun k h1 h2 => hsB.self_owned k (by omega) h2,
      fun k h1 h2 => hsB.son_link k (by omega) h2,
      fun k h1 h2 => hsB.root_shape k (by omega) h2⟩
  have hagree : ∀ k, lo - 1 ≤ k → k < (filterAllAgg g reqs).current_step →
      upd sel (lo - 1) (sel' (lo - 1)) k = sel' k := by
    intro k hk0 hk1
    rcases int_eq_or_ne k (lo - 1) with rfl | hne
    · show (if (lo - 1) = lo - 1 then sel' (lo - 1) else sel (lo - 1)) = sel' (lo - 1)
      rw [if_pos rfl]
    · show (if k = lo - 1 then sel' (lo - 1) else sel k) = sel' k
      rw [if_neg hne]
      exact (hag k (by omega) (by rw [hstep] at hk1; exact hk1)).symm
  exact ⟨sel' (lo - 1),
    soundFrom_congr (sel₀ := sel') (sel₁ := upd sel (lo - 1) (sel' (lo - 1))) hagree hsB'⟩

/-- info: 'AbsSat.GraphPath.Model.DescentFilter.noDeadEnd_filterAllAgg_of_completion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_filterAllAgg_of_completion

end AbsSat.GraphPath.Model.DescentFilter
