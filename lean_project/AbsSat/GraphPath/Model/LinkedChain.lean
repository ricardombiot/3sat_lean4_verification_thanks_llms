-- lean_project/AbsSat/GraphPath/Model/LinkedChain.lean
import AbsSat.GraphPath.Model.EmbeddedSupport

/-!
# Every entry of a reviewed state lies on a linked chain

The review is a greatest fixpoint of support conditions (`AnchoredSurvive.Sup`). Two of them are about
links: an entry `(x, v)` has a **parent** of `x` that also owns `v` (`par`) and, below the top step, a
**son** of `x` that also owns `v` (`son`). Following them down to step 0 and up to the top step gives a
whole chain of parent links through `x`, every node of which owns `v`; and at `v`'s own step the node
of the chain that owns `v` **is** `v`, because at its own step a node owns only itself (`OOS`).

* **`entry_on_linked_chain`** — every entry `(x, v)` of a reviewed state lies on a parent-linked chain
  that covers every step and passes through `x` and through `v`, and every node of which owns `v`.

This is the constructive content of the review. What it does not give is that the nodes of the chain
own **each other** — only that each owns `v`. For a union of paths closed under recombination at shared
map nodes, a linked chain is itself one of the paths, and that is enough; with requirements linking
distant steps, the remaining step is exactly pairwise ownership along the chain.
-/

namespace AbsSat.GraphPath.Model.LinkedChain

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup)
open AbsSat.GraphPath.Model.AggFixpoint (AggOk)
open AbsSat.GraphPath.Model.EmbeddedSupport

variable (R : GPathM)

/-- The review's own tables are a support relation inside it. -/
theorem sup_self (a : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R) : Sup R (Mem R) (Rel R) :=
  sup_of_embedded R R a hok hsmp ⟨rfl, fun _ h => h, fun _ m hm => ⟨m, hm, fun _ hq _ => hq, fun _ hq _ => hq⟩⟩

theorem step_of_mem (a : AdjacentOwners.Adj R) {y : PathNodeId} (h : Mem R y) : 0 ≤ y.id.step ∧ y.id.step < R.current_step :=
  mem_bounds R a h

/-- **Down**: from a node owning `v`, a chain of parents down to step 0, every node owning `v`. -/
theorem chain_down (a : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R) (v : PathNodeId) : ∀ (n : Nat) (y : PathNodeId), Rel R y v → y.id.step = n →
    ∃ f : Int → PathNodeId, f n = y ∧
      (∀ k : Int, 0 ≤ k → k ≤ n → Rel R (f k) v ∧ (f k).id.step = k) ∧
      (∀ k : Int, 0 ≤ k → k < n → ∃ d, R.node? (f (k + 1)) = some d ∧ f k ∈ d.parents) := by
  have S := sup_self R a hok hsmp
  intro n
  induction n with
  | zero =>
    intro y hy hs
    refine ⟨fun _ => y, rfl, fun k h0 h1 => ⟨hy, by rw [hs]; omega⟩, fun k h0 h1 => by omega⟩
  | succ n ih =>
    intro y hy hs
    have hy0 := hy
    obtain ⟨d, hd, _, _⟩ := hy0
    have hmem := List.mem_of_find?_eq_some hd
    have hid := node?_id_eq R y d hd
    have hne : y.parent_id ≠ none := by
      have := a.rc.shape.notroot d hmem (by rw [hid, hs]; omega)
      rw [hid] at this; exact this
    obtain ⟨c, hc, _, _, hcv⟩ := S.par y d (S.dom y v hy).1 hd hne v hy
    have hcs : c.id.step = n := by
      have := a.rc.shape.pbelow d hmem c hc
      rw [hid, hs] at this; omega
    obtain ⟨f, hfn, hf, hlink⟩ := ih c hcv hcs
    refine ⟨fun k => if k = ((n + 1 : Nat) : Int) then y else f k, by simp, ?_, ?_⟩
    · intro k h0 h1
      by_cases hk : k = ((n + 1 : Nat) : Int)
      · simp only [hk, if_true]; exact ⟨hy, by rw [hs]⟩
      · simp only [hk, if_false]; exact hf k h0 (by omega)
    · intro k h0 h1
      by_cases hk : k + 1 = ((n + 1 : Nat) : Int)
      · have hkn : k = (n : Int) := by omega
        have hk' : k ≠ ((n + 1 : Nat) : Int) := by omega
        simp only [hk, hk', if_true, if_false]
        refine ⟨d, hd, ?_⟩
        rw [hkn, hfn]; exact hc
      · have hk' : k ≠ ((n + 1 : Nat) : Int) := by omega
        simp only [hk, hk', if_false]
        exact hlink k h0 (by omega)

/-- **Up**: from a node owning `v`, a chain of sons up to the top step, every node owning `v`. -/
theorem chain_up (a : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R) (v : PathNodeId) : ∀ (m : Nat) (y : PathNodeId), Rel R y v →
    y.id.step = R.current_step - 1 - m →
    ∃ f : Int → PathNodeId, f y.id.step = y ∧
      (∀ k : Int, y.id.step ≤ k → k < R.current_step → Rel R (f k) v ∧ (f k).id.step = k) ∧
      (∀ k : Int, y.id.step ≤ k → k + 1 < R.current_step → ∃ d, R.node? (f (k + 1)) = some d ∧ f k ∈ d.parents) := by
  have S := sup_self R a hok hsmp
  intro m
  induction m with
  | zero =>
    intro y hy hs
    refine ⟨fun _ => y, rfl, fun k h0 h1 => ⟨hy, by show y.id.step = k; omega⟩, fun k h0 h1 => by omega⟩
  | succ m ih =>
    intro y hy hs
    have hnt : y.id.step ≠ R.current_step - 1 := by omega
    obtain ⟨c, mc, hmc, hyc, _, _, hcv⟩ := S.son y (S.dom y v hy).1 hnt v hy
    have hmem := List.mem_of_find?_eq_some hmc
    have hid := node?_id_eq R c mc hmc
    have hcs : c.id.step = y.id.step + 1 := by
      have := a.rc.shape.pbelow mc hmem y hyc
      rw [hid] at this; omega
    obtain ⟨f, hfc, hf, hlink⟩ := ih c hcv (by omega)
    refine ⟨fun k => if k = y.id.step then y else f k, by simp, ?_, ?_⟩
    · intro k h0 h1
      show Rel R (if k = y.id.step then y else f k) v ∧ (if k = y.id.step then y else f k).id.step = k
      by_cases hk : k = y.id.step
      · rw [if_pos hk]; exact ⟨hy, hk.symm⟩
      · rw [if_neg hk]; exact hf k (by omega) h1
    · intro k h0 h1
      show ∃ d, R.node? (if k + 1 = y.id.step then y else f (k + 1)) = some d ∧
        (if k = y.id.step then y else f k) ∈ d.parents
      by_cases hk : k = y.id.step
      · have hk1 : k + 1 ≠ y.id.step := by omega
        rw [if_neg hk1, if_pos hk, hk, ← hcs, hfc]
        exact ⟨mc, hmc, hyc⟩
      · have hk1 : k + 1 ≠ y.id.step := by omega
        rw [if_neg hk1, if_neg hk]
        exact hlink k (by omega) h1

/-- **Every entry of a reviewed state lies on a linked chain** through both of its nodes, every node of
which owns the entry's owner. -/
theorem entry_on_linked_chain (a : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R) (x v : PathNodeId) (hxv : Rel R x v) :
    ∃ sel : Int → PathNodeId, IsChain R sel ∧ sel x.id.step = x ∧ sel v.id.step = v ∧
      ∀ k, 0 ≤ k → k < R.current_step → Rel R (sel k) v := by
  obtain ⟨hx0, hx1⟩ := step_of_mem R a (sup_self R a hok hsmp |>.dom x v hxv).1
  obtain ⟨fd, hfdx, hfd, hlinkd⟩ := chain_down R a hok hsmp v x.id.step.toNat x hxv (by omega)
  obtain ⟨fu, hfux, hfu, hlinku⟩ := chain_up R a hok hsmp v (R.current_step - 1 - x.id.step).toNat x hxv
    (by omega)
  let sel : Int → PathNodeId := fun k => if k ≤ x.id.step then fd k else fu k
  have hrel : ∀ k, 0 ≤ k → k < R.current_step → Rel R (sel k) v ∧ (sel k).id.step = k := by
    intro k h0 h1
    by_cases hk : k ≤ x.id.step
    · simp only [sel, hk, if_true]; exact hfd k h0 (by omega)
    · simp only [sel, hk, if_false]; exact hfu k (by omega) h1
  have hfdx' : fd x.id.step = x := by
    have := hfdx
    rwa [show ((x.id.step.toNat : Nat) : Int) = x.id.step by omega] at this
  have hsx : sel x.id.step = x := by
    show (if x.id.step ≤ x.id.step then fd x.id.step else fu x.id.step) = x
    rw [if_pos (Int.le_refl _)]; exact hfdx'
  refine ⟨sel, ⟨fun k h0 h1 => ?_, fun k h0 h1 => ?_⟩, hsx, ?_, fun k h0 h1 => (hrel k h0 h1).1⟩
  · obtain ⟨⟨d, hd, _, _⟩, hs⟩ := hrel k h0 h1
    exact ⟨by rw [hd]; rfl, hs⟩
  · by_cases hk : k + 1 ≤ x.id.step
    · have hk' : k ≤ x.id.step := by omega
      obtain ⟨d, hd, hp⟩ := hlinkd k h0 (by omega)
      simp only [sel, hk, hk', if_true]
      rw [hd]; exact hp
    · by_cases hk' : k ≤ x.id.step
      · -- the junction: `x` itself, and its son from the up chain
        have hkx : k = x.id.step := by omega
        obtain ⟨d, hd, hp⟩ := hlinku k (by omega) h1
        have hsel1 : sel (k + 1) = fu (k + 1) := by simp only [sel, hk, if_false]
        have hselk : sel k = fu k := by
          simp only [sel, hk', if_true]
          rw [hkx]
          have := hfdx
          rw [show ((x.id.step.toNat : Nat) : Int) = x.id.step by omega] at this
          rw [this, hfux]
        rw [hsel1, hselk, hd]; exact hp
      · obtain ⟨d, hd, hp⟩ := hlinku k (by omega) h1
        simp only [sel, hk, hk', if_false]
        rw [hd]; exact hp
  · -- at `v`'s own step the chain's node is `v`
    obtain ⟨hv0, hv1⟩ := step_of_mem R a (sup_self R a hok hsmp |>.dom x v hxv).2
    obtain ⟨⟨d, hd, hvd, _⟩, hs⟩ := hrel v.id.step hv0 hv1
    have hmem := List.mem_of_find?_eq_some hd
    have hid := node?_id_eq R _ d hd
    have := a.rc.oos d hmem v hvd (by rw [hid, hs])
    rw [hid] at this
    exact this.symm

/-- info: 'AbsSat.GraphPath.Model.LinkedChain.entry_on_linked_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_on_linked_chain

end AbsSat.GraphPath.Model.LinkedChain
