-- lean_project/AbsSat/GraphPath/Model/AggInvariants.lean
import AbsSat.GraphPath.Model.AggressiveReview
import AbsSat.GraphPath.Model.Sons

/-!
# Structural invariants through the aggressive review

The author's sweep only rewrites owner lists (`updateAt … uniMap`) and removes nodes. So any invariant
kept by the pins, the base review, those owner rewrites and `removeNode` is kept by `filterAllAgg`
(`inv_filterAllAgg`). Applied to the link invariants `Sons.PMS` (a son lists its parent) and `Sons.SN`
(sons are nodes).
-/

namespace AbsSat.GraphPath.Model.AggInvariants

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview

section
variable (P : GPathM → Prop)
  (hreq : ∀ g r, P g → P (filterRequire g r))
  (hrev : ∀ g, P g → P (review g))
  (hup : ∀ g id B, P g → P (updateAt g id (uniMap B)))
  (hrm : ∀ g id, P g → P (removeNode g id))

private theorem inv_foldl {β : Type} (f : GPathM → β → GPathM) (hf : ∀ g b, P g → P (f g b)) :
    ∀ (l : List β) (g : GPathM), P g → P (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons b rest ih => intro g h; exact ih _ (hf g b h)

include hup in
theorem inv_aggPair (g : GPathM) (x w : PathNodeId) (h : P g) : P (aggPair g x w) := by
  unfold aggPair
  split
  · split
    · exact hup _ _ _ h
    · split
      · exact hup _ _ _ (hup _ _ _ h)
      · exact h
  · exact h

include hup hrm in
theorem inv_aggNode (g : GPathM) (x : PathNodeId) (h : P g) : P (aggNode g x) := by
  unfold aggNode
  split
  · exact h
  · next nx _ =>
    have hA : P ((intRange 0 (g.current_step - 1)).reverse.foldl
        (fun g kw => (ownersAtNow g x kw).foldl (fun g w => aggPair g x w) g) g) :=
      inv_foldl P _ (fun g kw hg => inv_foldl P (fun g w => aggPair g x w)
        (fun g w hg => inv_aggPair P hup g x w hg) (ownersAtNow g x kw) g hg) _ g h
    dsimp only
    repeat' split
    all_goals first | exact hA | exact h | exact hrm _ _ hA | exact hrm _ _ h

include hup hrm in
theorem inv_aggSweep (g : GPathM) (h : P g) : P (aggSweep g) := by
  unfold aggSweep
  split
  · exact inv_foldl P _ (fun g k hg => inv_foldl P _ (fun g x hg => inv_aggNode P hup hrm g x hg) _ g hg) _ g h
  · exact h

include hrev hup hrm in
theorem inv_reviewAggFuel : ∀ (fuel : Nat) (g : GPathM), P g → P (reviewAggFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact hrev g h
  | succ n ih =>
    intro g h
    simp only [reviewAggFuel]
    have h₁ := hrev g h
    split
    · split
      · exact ih _ (inv_aggSweep P hup hrm _ h₁)
      · exact h₁
    · exact h₁

include hreq hrev hup hrm in
/-- **Any invariant of the pins, the base review, owner rewrites and removals survives
`filterAllAgg`.** -/
theorem inv_filterAllAgg (g : GPathM) (reqs : List NodeId) (h : P g) : P (filterAllAgg g reqs) :=
  inv_reviewAggFuel P hrev hup hrm _ _ (inv_foldl P filterRequire hreq reqs g h)

end

theorem PMS_filterAllAgg (g : GPathM) (reqs : List NodeId) (h : Sons.PMS g) :
    Sons.PMS (filterAllAgg g reqs) :=
  inv_filterAllAgg Sons.PMS (fun g r h => Sons.PMS_filterRequire g r h)
    (fun g h => Sons.PMS_review g h)
    (fun g id _ h => Sons.PMS_updateAt g id _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) h)
    (fun g id h => Sons.PMS_removeNode g id h) g reqs h

theorem SN_filterAllAgg (g : GPathM) (reqs : List NodeId) (h : Sons.SN g) :
    Sons.SN (filterAllAgg g reqs) :=
  inv_filterAllAgg Sons.SN (fun g r h => Sons.SN_filterRequire g r h)
    (fun g h => Sons.SN_review g h)
    (fun g id _ h => Sons.SN_updateAt g id _ (fun _ => rfl) (fun _ => rfl) h)
    (fun g id h => Sons.SN_removeNode g id h) g reqs h

/-- info: 'AbsSat.GraphPath.Model.AggInvariants.PMS_filterAllAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PMS_filterAllAgg

end AbsSat.GraphPath.Model.AggInvariants
