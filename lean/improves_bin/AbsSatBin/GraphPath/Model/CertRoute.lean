-- lean/improves_bin/AbsSatBin/GraphPath/Model/CertRoute.lean
import AbsSatBin.GraphPath.Model.CertMachine

/-!
# Routing: a union of complementary pins of an exact state is exact

The two sides of a join in the machine descend from the same earlier state by pins on the two values of
a variable. This module proves the core of why that union does no harm:

* **`certClique_join_pins`**: if `J` satisfies `CertClique` and the live entries of `J` at a step `t` name
  only the two map nodes `r₁`, `r₂` (a variable step), then `join (filterAll J [r₁]) (filterAll J [r₂])`
  satisfies `CertClique`.

A clique with witnesses in the union has them in `J` (both sides only shrink `J`'s tables, and the join
only unions them). Its certificate in `J` goes through `r₁` or `r₂` at step `t` — **the certificate
chooses the branch** — so it survives that pin, and so it is in the union. Which side each witness came
from is irrelevant: the mixing of §4.2g–q never has to be resolved.
-/

namespace AbsSatBin.GraphPath.Model.CertRoute

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.CertFix
open AbsSatBin.GraphPath.Model.CertDescent
open AbsSatBin.GraphPath.Model.CertInvariant

/-- A node of the join of two filtered states is a node of `J` with a smaller table. -/
theorem join_sub (J : GPathM) (hnd : NodupIds J) (r₁ r₂ : NodeId) (q : PathNodeId) (nq : PNodeM)
    (hq : (join (filterAll J [r₁]) (filterAll J [r₂])).node? q = some nq) :
    ∃ nJ, J.node? q = some nJ ∧ ∀ v ∈ nq.owners, v ∈ nJ.owners := by
  have hb₁ := KernelIff.below_filterAll_self J hnd [r₁]
  have hb₂ := KernelIff.below_filterAll_self J hnd [r₂]
  -- the node of `J`
  obtain ⟨nJ, hnJ⟩ : ∃ nJ, J.node? q = some nJ := by
    rcases join_node?_source _ _ q nq hq with h | h
    · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨nJ, hnJ, _, _, _⟩ := hb₁.node q m hm
      exact ⟨nJ, hnJ⟩
    · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨nJ, hnJ, _, _, _⟩ := hb₂.node q m hm
      exact ⟨nJ, hnJ⟩
  refine ⟨nJ, hnJ, fun v hv => ?_⟩
  rcases join_owners_source _ _ q nq hq v hv with ⟨m, hm, hvm⟩ | ⟨m, hm, hvm⟩
  · obtain ⟨nJ', hnJ', ho, _, _⟩ := hb₁.node q m hm
    rw [hnJ] at hnJ'; cases hnJ'; exact ho v hvm
  · obtain ⟨nJ', hnJ', ho, _, _⟩ := hb₂.node q m hm
    rw [hnJ] at hnJ'; cases hnJ'; exact ho v hvm

/-- **A union of complementary pins of an exact state is exact.** -/
theorem certClique_join_pins (J : GPathM) (hnd : NodupIds J) (r₁ r₂ : NodeId) (t : Int)
    (hr₁ : r₁.step = t) (hr₂ : r₂.step = t)
    (htwo : ∀ q ∈ J.gowners, q.id.step = t → q.id = r₁ ∨ q.id = r₂)
    (hok : okJoin (filterAll J [r₁]) (filterAll J [r₂]) = true) (h : CertClique J) :
    CertClique (join (filterAll J [r₁]) (filterAll J [r₂])) := by
  have hcs : (join (filterAll J [r₁]) (filterAll J [r₂])).current_step = J.current_step := by
    show (filterAll J [r₁]).current_step = J.current_step
    exact (KernelIff.below_filterAll_self J hnd [r₁]).step.symm
  intro Q hQ hW
  have hQJ : Clique J Q := by
    intro q hq
    obtain ⟨nq, hnq, hqQ⟩ := hQ q hq
    obtain ⟨nJ, hnJ, ho⟩ := join_sub J hnd r₁ r₂ q nq hnq
    exact ⟨nJ, hnJ, fun s hs => ho s (hqQ s hs)⟩
  have hWJ : Wit J Q := by
    intro l h0 h1
    obtain ⟨r, nr, hnr, hrs, hrQ⟩ := hW l h0 (by rw [hcs]; exact h1)
    obtain ⟨nJ, hnJ, ho⟩ := join_sub J hnd r₁ r₂ r nr hnr
    exact ⟨r, nJ, hnJ, hrs, fun s hs => ho s (hrQ s hs)⟩
  obtain ⟨sel, hs, hon⟩ := h Q hQJ hWJ
  -- the certificate chooses its side at step `t`
  have pick : 0 ≤ t → t < J.current_step → (sel t).id = r₁ ∨ (sel t).id = r₂ := by
    intro h0 h1
    exact htwo (sel t) (hs.chain.2.2 t h0 h1) (hs.chain.1.1 t h0 h1).2
  by_cases ht : 0 ≤ t ∧ t < J.current_step
  · rcases pick ht.1 ht.2 with e | e
    · refine ⟨sel, ChainSound_join_left _ _ sel (ChainSound_filterAll J [r₁] sel hs (fun r hr _ _ => ?_)), hon⟩
      rw [List.mem_singleton.mp hr, hr₁, e]
    · refine ⟨sel, ChainSound_join_right _ _ hok sel (ChainSound_filterAll J [r₂] sel hs (fun r hr _ _ => ?_)), hon⟩
      rw [List.mem_singleton.mp hr, hr₂, e]
  · -- the step is outside the state: the pin asks nothing
    refine ⟨sel, ChainSound_join_left _ _ sel (ChainSound_filterAll J [r₁] sel hs (fun r hr h0 h1 => ?_)), hon⟩
    rw [List.mem_singleton.mp hr] at h0 h1
    exact absurd ⟨hr₁ ▸ h0, hr₁ ▸ h1⟩ ht

/-- info: 'AbsSatBin.GraphPath.Model.CertRoute.certClique_join_pins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certClique_join_pins

end AbsSatBin.GraphPath.Model.CertRoute
