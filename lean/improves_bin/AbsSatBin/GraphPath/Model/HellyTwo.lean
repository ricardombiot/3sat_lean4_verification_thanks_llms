-- lean/improves_bin/AbsSatBin/GraphPath/Model/HellyTwo.lean
import AbsSatBin.GraphPath.Model.ReqFilter

/-!
# Helly on two values: the lever of the bin map

Every step of the bin map has at most two map nodes. On a two-element domain, three sets that meet
pairwise meet all together (Helly number 2). For the tables:

* **`share3_of_two`**: at a step whose live entries are at most two path nodes, three nodes that own each
  other pairwise share an entry at that step — the pair rule alone gives the triple witness.

This is the first-layer witness of `TriPin` (a common entry), not its second layer (the witness'
own links being compatible). Where the live entries of a step are more than two path nodes — the
window keeps the previous steps — it does not apply directly.
-/

namespace AbsSatBin.GraphPath.Model.HellyTwo

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel

/-- **Helly on two values.** Three members of a two-element set, pairwise shared, give a common one. -/
theorem helly2 {α : Type} [DecidableEq α] (u u' : α) (A B C : α → Prop) (a b c : α)
    (ha : a = u ∨ a = u') (hb : b = u ∨ b = u') (hc : c = u ∨ c = u')
    (haA : A a) (haB : B a) (hbA : A b) (hbC : C b) (hcB : B c) (hcC : C c) :
    ∃ r, A r ∧ B r ∧ C r := by
  by_cases hab : a = b
  · subst hab; exact ⟨a, haA, haB, hbC⟩
  · by_cases hac : a = c
    · subst hac; exact ⟨a, haA, haB, hcC⟩
    · by_cases hbc : b = c
      · subst hbc; exact ⟨b, hbA, hcB, hbC⟩
      · exfalso
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
          simp_all

variable {g : GPathM}

/-- **Three nodes that own each other share an entry at a step with at most two live path nodes.** -/
theorem share3_of_two (hk : Kernel g) (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny)
    (w : PathNodeId) (nw : PNodeM) (hw : g.node? w = some nw) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (hwy : w ∈ ny.owners) (hxy : x ∈ ny.owners) (hxw : x ∈ nw.owners)
    (l : Int) (h0 : 0 ≤ l) (h1 : l < g.current_step) (u u' : PathNodeId)
    (htwo : ∀ q ∈ g.gowners, q.id.step = l → q = u ∨ q = u') :
    ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l := by
  obtain ⟨a, hay, haw, has⟩ := hk.pair y ny w nw hy hw hwy l h0 h1
  obtain ⟨b, hby, hbx, hbs⟩ := hk.pair y ny x nx hy hx hxy l h0 h1
  obtain ⟨c, hcw, hcx, hcs⟩ := hk.pair w nw x nx hw hx hxw l h0 h1
  obtain ⟨r, ⟨hry, hrs⟩, ⟨hrw, _⟩, hrx⟩ :=
    helly2 u u' (fun r => r ∈ ny.owners ∧ r.id.step = l) (fun r => r ∈ nw.owners ∧ r.id.step = l)
      (fun r => r ∈ nx.owners) a b c
      (htwo a (hk.own y ny hy a hay) has) (htwo b (hk.own y ny hy b hby) hbs)
      (htwo c (hk.own w nw hw c hcw) hcs) ⟨hay, has⟩ ⟨haw, has⟩ ⟨hby, hbs⟩ hbx ⟨hcw, hcs⟩ hcx
  exact ⟨r, hry, hrw, hrx, hrs⟩

/-- info: 'AbsSatBin.GraphPath.Model.HellyTwo.share3_of_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms share3_of_two

end AbsSatBin.GraphPath.Model.HellyTwo
