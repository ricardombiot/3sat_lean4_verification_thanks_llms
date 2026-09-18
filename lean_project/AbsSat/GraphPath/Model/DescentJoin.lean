-- lean_project/AbsSat/GraphPath/Model/DescentJoin.lean
import AbsSat.GraphPath.Model.DescentUp
import AbsSat.GraphPath.Model.JoinDescent
import AbsSat.GraphPath.Model.JoinProvenance

/-!
# The descent through a `join`, by construction

The `up` case of the induction is done (`DescentUp.noDeadEnd_addNode`). This file does the `join`
case, in the currency the verdict now uses (`NoDeadEnd`, `SoundFrom`), and connects it to the
descent work that was already there in `SoundOn` currency.

* `soundOn_of_soundFrom`, `soundFrom_of_soundOn` — the two are the same statement, `SoundFrom`
  being `SoundOn` up to the top step.
* `noDeadEnd_of_descendAll` — so the descent from every step gives the descent from the top.
* `noDeadEnd_join_of_covered` — **a join keeps the descent**, given `JoinDescent.JoinCovered`: a
  partial chain of the join that is a partial chain of one side extends there and the extension
  lifts (`JoinDescent.soundOn_of_grown`), and a chain of neither side is covered by the hypothesis.
* `picks_left_of_exclusive_anchor` — **the picks of a partial chain of a join all live on one
  side**, the one that has its anchor: every pick owns the anchor, and the slice of a node one side
  lacks lies entirely on the other (`JoinProvenance.slice_of_exclusive_top`). So a mixed chain can
  only mix *owner entries* at the nodes the sides share, never nodes — which is what `JoinCovered`
  is about, and what the probe measures (v132).
-/

namespace AbsSat.GraphPath.Model.DescentJoin

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.NoDeadEnd (SoundFrom upd NoDeadEnd)
open AbsSat.GraphPath.Model.DescentInvariant (SoundOn DescendAll)
open AbsSat.GraphPath.Model.JoinDescent (JoinCovered descendAll_join)

/-- `SoundFrom` is `SoundOn` up to the top step. -/
theorem soundOn_of_soundFrom {g : GPathM} {sel : Int → PathNodeId} {lo : Int}
    (hs : SoundFrom g sel lo) : SoundOn g sel lo (g.current_step - 1) :=
  ⟨fun k h1 h2 => hs.node k h1 (by omega),
   fun k h1 h2 => hs.parent_link k h1 (by omega),
   fun i j hi1 hj1 hi2 hj2 hij => hs.owned i j hi1 hj1 (by omega) (by omega) hij,
   fun k h1 h2 => hs.gowner k h1 (by omega),
   fun k h1 h2 => hs.self_owned k h1 (by omega),
   fun k h1 h2 => hs.son_link k h1 (by omega),
   fun k h1 h2 => hs.root_shape k h1 (by omega)⟩

/-- And back. -/
theorem soundFrom_of_soundOn {g : GPathM} {sel : Int → PathNodeId} {lo : Int}
    (hs : SoundOn g sel lo (g.current_step - 1)) : SoundFrom g sel lo :=
  ⟨fun k h1 h2 => hs.node k h1 (by omega),
   fun k h1 h2 => hs.parent_link k h1 (by omega),
   fun i j hi1 hj1 hi2 hj2 hij => hs.owned i j hi1 hj1 (by omega) (by omega) hij,
   fun k h1 h2 => hs.gowner k h1 (by omega),
   fun k h1 h2 => hs.self_owned k h1 (by omega),
   fun k h1 h2 => hs.son_link k h1 (by omega),
   fun k h1 h2 => hs.root_shape k h1 (by omega)⟩

/-- **The descent from every step gives the descent from the top.** -/
theorem noDeadEnd_of_descendAll {g : GPathM} (h : DescendAll g) : NoDeadEnd g := by
  intro sel lo hlo0 hlo hs
  obtain ⟨c, hc⟩ := h sel lo (g.current_step - 1) hlo0 hlo (by omega) (soundOn_of_soundFrom hs)
  exact ⟨c, soundFrom_of_soundOn hc⟩

/-- **A join keeps the descent**, given that every partial chain of the join is a partial chain of
one side or extends. -/
theorem noDeadEnd_join_of_covered (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : DescendAll g₁) (h₂ : DescendAll g₂) (hcov : JoinCovered g₁ g₂) :
    NoDeadEnd (join g₁ g₂) :=
  noDeadEnd_of_descendAll (descendAll_join g₁ g₂ hok h₁ h₂ hcov)

/-- **A partial chain of a state is one of any state that grows it.** Every condition of
`SoundFrom` is a membership, and growth only adds. -/
theorem soundFrom_of_grown {g g' : GPathM} (hgr : Grown g g') {sel : Int → PathNodeId} {lo : Int}
    (hs : SoundFrom g sel lo) : SoundFrom g' sel lo := by
  have hlook : ∀ k, lo ≤ k → k < g.current_step → ∃ n n', g.node? (sel k) = some n ∧
      g'.node? (sel k) = some n' ∧ (∀ q ∈ n.owners, q ∈ n'.owners) ∧
      (∀ p ∈ n.parents, p ∈ n'.parents) ∧ (∀ s ∈ n.sons, s ∈ n'.sons) := by
    intro k h1 h2
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hs.node k h1 h2).1
    obtain ⟨n', hn', ho, hp, hsn⟩ := hgr.node?_grown _ n hn
    exact ⟨n, n', hn, hn', ho, hp, hsn⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h1 h2
    obtain ⟨_, _, _, hn', _⟩ := hlook k h1 (by rw [hgr.step_eq] at h2; exact h2)
    exact ⟨by rw [hn']; rfl, (hs.node k h1 (by rw [hgr.step_eq] at h2; exact h2)).2⟩
  · intro k h1 h2
    rw [hgr.step_eq] at h2
    obtain ⟨n, n', hn, hn', _, hp, _⟩ := hlook (k + 1) (by omega) h2
    have hpl := hs.parent_link k h1 h2
    rw [hn] at hpl
    simp only [Option.map_some, Option.getD_some] at hpl
    rw [hn']
    simpa only [Option.map_some, Option.getD_some] using hp _ hpl
  · intro i j hi1 hj1 hi2 hj2 hij
    rw [hgr.step_eq] at hi2 hj2
    obtain ⟨n, n', hn, hn', ho, _, _⟩ := hlook j hj1 hj2
    have how := hs.owned i j hi1 hj1 hi2 hj2 hij
    rw [ownersOf, hn] at how
    rw [ownersOf, hn']
    obtain ⟨hmem, hstep⟩ := List.mem_filter.mp how
    exact List.mem_filter.mpr ⟨ho _ hmem, hstep⟩
  · intro k h1 h2
    rw [hgr.step_eq] at h2
    exact hgr.gowners_grown _ (hs.gowner k h1 h2)
  · intro k h1 h2
    rw [hgr.step_eq] at h2
    obtain ⟨n, n', hn, hn', ho, _, _⟩ := hlook k h1 h2
    have hso := hs.self_owned k h1 h2
    rw [ownersOf, hn] at hso
    rw [ownersOf, hn']
    exact ho _ hso
  · intro k h1 h2
    rw [hgr.step_eq] at h2
    obtain ⟨n, n', hn, hn', _, _, hsn⟩ := hlook k h1 (by omega)
    have hsl := hs.son_link k h1 h2
    simp only [sonsOf, hn] at hsl
    simp only [sonsOf, hn']
    exact hsn _ hsl
  · intro k h1 h2
    rw [hgr.step_eq] at h2
    exact hs.root_shape k h1 h2

/-- Every partial chain of a join is a partial chain of one of its sides, or it extends. The
`SoundFrom` form of `JoinDescent.JoinCovered`. -/
def JoinCoveredF (g₁ g₂ : GPathM) : Prop :=
  ∀ sel lo, 0 < lo → lo ≤ (join g₁ g₂).current_step - 1 → SoundFrom (join g₁ g₂) sel lo →
    SoundFrom g₁ sel lo ∨ SoundFrom g₂ sel lo ∨
      ∃ c, SoundFrom (join g₁ g₂) (upd sel (lo - 1) c) (lo - 1)

/-- **A join keeps the descent**, from the descent on its sides and `JoinCoveredF`. -/
theorem noDeadEnd_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : NoDeadEnd g₁) (h₂ : NoDeadEnd g₂) (hcov : JoinCoveredF g₁ g₂) :
    NoDeadEnd (join g₁ g₂) := by
  intro sel lo hlo0 hlo hs
  rcases hcov sel lo hlo0 hlo hs with hs1 | hs2 | hext
  · have hstep := (grown_join_left g₁ g₂).step_eq
    obtain ⟨c, hc⟩ := h₁ sel lo hlo0 (by rw [hstep] at hlo; omega) hs1
    exact ⟨c, soundFrom_of_grown (grown_join_left g₁ g₂) hc⟩
  · have hstep := (grown_join_right g₁ g₂ hok).step_eq
    obtain ⟨c, hc⟩ := h₂ sel lo hlo0 (by rw [hstep] at hlo; omega) hs2
    exact ⟨c, soundFrom_of_grown (grown_join_right g₁ g₂ hok) hc⟩
  · exact hext

/-- info: 'AbsSat.GraphPath.Model.DescentJoin.noDeadEnd_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_join

/-- **The picks of a partial chain of a join live on the side that has its anchor.** Every pick
owns the anchor, and the slice of a node one side does not have lies entirely on the other. So a
mixed chain never mixes *nodes* — only owner entries, at the nodes the two sides share. -/
theorem picks_left_of_exclusive_anchor (g₁ g₂ : GPathM)
    (hnd : NodupIds (join g₁ g₂)) (ho₂ : JoinProvenance.OwnGow g₂) (hgn₂ : GownersNodes.GN g₂)
    (hstep : (join g₁ g₂).current_step = g₂.current_step)
    {sel : Int → PathNodeId} {lo : Int}
    (hs : SoundFrom (join g₁ g₂) sel lo)
    (hz : g₂.node? (sel ((join g₁ g₂).current_step - 1)) = none)
    (hpos : 0 < (join g₁ g₂).current_step) :
    ∀ k, lo ≤ k → k < (join g₁ g₂).current_step → (g₁.node? (sel k)).isSome = true := by
  intro k hk0 hk1
  obtain ⟨hsome, hstepk⟩ := hs.node k hk0 hk1
  obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp hsome
  have hzstep : (sel ((join g₁ g₂).current_step - 1)).id.step = (join g₁ g₂).current_step - 1 :=
    (hs.node ((join g₁ g₂).current_step - 1) (by omega) (by omega)).2
  -- the pick owns the anchor: itself if it is the anchor, by pairwise ownership otherwise
  have hzk : sel ((join g₁ g₂).current_step - 1) ∈ nk.owners := by
    by_cases heq : k = (join g₁ g₂).current_step - 1
    · rw [← heq]
      have hso := hs.self_owned k hk0 hk1
      simpa only [ownersOf, hnk] using hso
    · have how := hs.owned ((join g₁ g₂).current_step - 1) k (by omega) hk0 (by omega) hk1
        (by omega)
      have h' := (List.mem_filter.mp how).1
      simpa only [ownersOf, hnk] using h'
  exact JoinProvenance.slice_of_exclusive_top g₁ g₂ (join g₁ g₂) (Pruned.refl (join g₁ g₂)) hnd
    ho₂ hgn₂ hstep hnk hzk (by rw [hzstep]; omega) (by rw [hzstep]; omega) hz

/-- **The entry to the anchor is the left side's own.** A pick of the chain owns the anchor in the
*join*; the entry cannot come from the right side, because the owners of a node are nodes of the
same state and the right side has no anchor. So every pick sits in the left side's own slice of the
anchor, in its own table — what is left of a mixed chain is only the entries **between picks**. -/
theorem chain_in_left_slice (g₁ g₂ : GPathM)
    (hnd : NodupIds (join g₁ g₂)) (ho₂ : JoinProvenance.OwnGow g₂) (hgn₂ : GownersNodes.GN g₂)
    (hon₂ : ∀ n ∈ g₂.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode g₂ q)
    (hstep : (join g₁ g₂).current_step = g₂.current_step)
    {sel : Int → PathNodeId} {lo : Int}
    (hs : SoundFrom (join g₁ g₂) sel lo)
    (hz : g₂.node? (sel ((join g₁ g₂).current_step - 1)) = none)
    (hpos : 0 < (join g₁ g₂).current_step) :
    ∀ k, lo ≤ k → k < (join g₁ g₂).current_step →
      ∃ m, g₁.node? (sel k) = some m ∧ sel ((join g₁ g₂).current_step - 1) ∈ m.owners := by
  intro k hk0 hk1
  -- the pick is a node of the left side
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
    (picks_left_of_exclusive_anchor g₁ g₂ hnd ho₂ hgn₂ hstep hs hz hpos k hk0 hk1)
  refine ⟨m, hm, ?_⟩
  -- and it owns the anchor in the join
  obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp (hs.node k hk0 hk1).1
  have hzk : sel ((join g₁ g₂).current_step - 1) ∈ nk.owners := by
    by_cases heq : k = (join g₁ g₂).current_step - 1
    · rw [← heq]
      have hso := hs.self_owned k hk0 hk1
      simpa only [ownersOf, hnk] using hso
    · have how := hs.owned ((join g₁ g₂).current_step - 1) k (by omega) hk0 (by omega) hk1
        (fun hc => heq hc.symm)
      have h' := (List.mem_filter.mp how).1
      simpa only [ownersOf, hnk] using h'
  -- the entry cannot be the right side's: it has no anchor
  rcases join_owners_source g₁ g₂ (sel k) nk hnk _ hzk with ⟨m₁, hm₁, hw₁⟩ | ⟨m₂, hm₂, hw₂⟩
  · have hmm : m₁ = m := by
      rw [hm] at hm₁
      exact (Option.some_inj.mp hm₁).symm
    rw [← hmm]; exact hw₁
  · exfalso
    have hhas := hon₂ m₂ (List.mem_of_find?_eq_some hm₂) _ hw₂
    have hsome := (GownersNodes.hasNode_iff g₂ _).mp hhas
    rw [hz] at hsome
    exact absurd hsome (by simp)

/-- info: 'AbsSat.GraphPath.Model.DescentJoin.chain_in_left_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_in_left_slice

/-- info: 'AbsSat.GraphPath.Model.DescentJoin.noDeadEnd_join_of_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_join_of_covered

/-- info: 'AbsSat.GraphPath.Model.DescentJoin.picks_left_of_exclusive_anchor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms picks_left_of_exclusive_anchor

end AbsSat.GraphPath.Model.DescentJoin
