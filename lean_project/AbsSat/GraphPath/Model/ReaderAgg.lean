-- lean_project/AbsSat/GraphPath/Model/ReaderAgg.lean
import AbsSat.GraphPath.Model.AggressiveReview
import AbsSat.GraphPath.Model.Reader

/-!
# The reader over the aggressive review: validity reduced to one pin

`Reader.Inhabited_of_pickSome_readable` already closes the author's reading loop for the base
review: select a map node at a step that still has a choice, pin it, review; the measure drops, so
the loop ends with one map node per step, and there the state denotes a path (`Pinned`). The one
hypothesis is `PickSome`: at every state the reader stands in, **some** pin keeps the graph valid.

This module moves that result to the review of the *Improves* machine, `reviewAgg`.

* `reviewAggFuel_form` — **every result of `reviewAgg` is a result of `review`**, of a state that
  keeps the reader's invariants (`RCtx`). The sweep only narrows owner tables and removes nodes
  (`keeps_aggSweep`), and the loop returns the base review's fixpoint.
* `readable_of_readableAgg` — so a state pinned with the aggressive review is a `Reader.Readable`
  state, and every static fact of the base reader applies: the review-fixpoint context, a path
  through a valid state, and the base case (no choice left ⇒ the state denotes a path).
* `Inhabited_of_pickSomeAgg` — **the reading loop with the aggressive review**, with one hypothesis:
  `PickSomeAgg` at the states the reader visits from the starting state (`ReadFrom`), not at every
  readable state.

So the validity of a valid final state reduces to a one-pin statement: *at a state the reader
reaches, some pin followed by the aggressive review leaves the graph valid.* The review re-runs after
every pin, so no static Helly property of the owner tables is asked for.

What is not here: that the Improves machine's own states carry `RCtx` (the base machine gets it from
`Reachable`), and `PickSomeAgg` itself.
-/

namespace AbsSat.GraphPath.Model.ReaderAgg

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.Reader (RCtx)
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice NoChoice measure_filterRequire_lt
  measure_review_le)

-- ============================================================
-- The sweep keeps the reader's invariants
-- ============================================================

/-- A narrowing that also keeps global owners among nodes, parents among nodes, and never
duplicates an id. -/
def Keeps (g g' : GPathM) : Prop :=
  Pruned g g' ∧ (GownersNodes.GN g → GownersNodes.GN g') ∧ (Parents.PN g → Parents.PN g') ∧
    (NodeIds.Ids g').Sublist (NodeIds.Ids g)

theorem Keeps.refl (g : GPathM) : Keeps g g :=
  ⟨Pruned.refl g, id, id, List.Sublist.refl _⟩

theorem Keeps.trans {g₁ g₂ g₃ : GPathM} (h₁ : Keeps g₁ g₂) (h₂ : Keeps g₂ g₃) : Keeps g₁ g₃ :=
  ⟨Pruned.trans h₁.1 h₂.1, fun h => h₂.2.1 (h₁.2.1 h), fun h => h₂.2.2.1 (h₁.2.2.1 h),
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem keeps_updateAt_uniMap (g : GPathM) (id : PathNodeId) (B : List PathNodeId) :
    Keeps g (updateAt g id (uniMap B)) :=
  ⟨pruned_updateAt_uniMap g id B, GownersNodes.GN_updateAt g id _ (uniMap_id B),
    Parents.PN_updateAt g id _ (uniMap_id B) (fun _ => rfl),
    by rw [NodeIds.ids_updateAt g id _ (uniMap_id B)]; exact List.Sublist.refl _⟩

theorem keeps_removeNode (g : GPathM) (id : PathNodeId) : Keeps g (removeNode g id) :=
  ⟨pruned_removeNode g id, GownersNodes.GN_removeNode g id, Parents.PN_removeNode g id,
    NodeIds.ids_removeNode g id⟩

theorem keeps_filterRequire (g : GPathM) (req : NodeId) : Keeps g (filterRequire g req) :=
  ⟨pruned_filterRequire g req, GownersNodes.GN_filterRequire g req, fun h => h,
    List.Sublist.refl _⟩

theorem keeps_foldl {β : Type} (f : GPathM → β → GPathM) (h : ∀ g b, Keeps g (f g b)) :
    ∀ (l : List β) (g : GPathM), Keeps g (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g; exact Keeps.refl g
  | cons b rest ih => intro g; exact Keeps.trans (h g b) (ih (f g b))

theorem keeps_aggPair (g : GPathM) (x w : PathNodeId) : Keeps g (aggPair g x w) := by
  unfold aggPair
  split
  · split
    · exact keeps_updateAt_uniMap _ _ _
    · split
      · exact Keeps.trans (keeps_updateAt_uniMap _ _ _) (keeps_updateAt_uniMap _ _ _)
      · exact Keeps.refl g
  · exact Keeps.refl g

theorem keeps_aggNode (g : GPathM) (x : PathNodeId) : Keeps g (aggNode g x) := by
  unfold aggNode
  split
  · exact Keeps.refl g
  · have h₁ : ∀ g₁ : GPathM, Keeps g g₁ → Keeps g
        (match g₁.node? x with
          | none => g₁
          | some n₁ => if isValidNode g₁ n₁ then g₁ else removeNode g₁ x) := by
      intro g₁ hg₁
      split
      · exact hg₁
      · split
        · exact hg₁
        · exact Keeps.trans hg₁ (keeps_removeNode _ _)
    apply h₁
    split
    · exact keeps_foldl _ (fun g kw => keeps_foldl _ (fun g w => keeps_aggPair g x w) _ g) _ g
    · exact Keeps.refl g

theorem keeps_aggSweep (g : GPathM) : Keeps g (aggSweep g) := by
  unfold aggSweep
  split
  · exact keeps_foldl _ (fun g k => keeps_foldl _ keeps_aggNode _ g) _ g
  · exact Keeps.refl g

theorem RCtx_of_keeps {g g' : GPathM} (hk : Keeps g g') (h : RCtx g) : RCtx g' where
  oos := SelfOwn.OOS_of_pruned hk.1 h.oos
  snn := SelfOwn.SNN_of_pruned hk.1 h.snn
  gn := hk.2.1 h.gn
  shape := Parents.Shape_of_pruned_pn hk.1 (hk.2.2.1 h.shape.pn) h.shape
  rootz := Sons.RootAtZero_of_pruned hk.1 h.rootz
  pmp := ParentId.PMP_of_pruned hk.1 h.pmp
  gpmp := ParentId.GPMP_of_pruned hk.1 h.gpmp
  below := Certifies.nodes_below_of_pruned hk.1 h.below
  nodup := List.Sublist.nodup hk.2.2.2 h.nodup

theorem RCtx_review (g : GPathM) (h : RCtx g) : RCtx (review g) :=
  Reader.RCtx_filterAll g h []

-- ============================================================
-- Every result of the aggressive review is a result of the base review
-- ============================================================

theorem reviewAggFuel_form : ∀ (fuel : Nat) (g : GPathM), RCtx g →
    ∃ h, RCtx h ∧ reviewAggFuel fuel g = review h := by
  intro fuel
  induction fuel with
  | zero => intro g hg; exact ⟨g, hg, rfl⟩
  | succ n ih =>
    intro g hg
    simp only [reviewAggFuel]
    split
    · split
      · exact ih _ (RCtx_of_keeps (keeps_aggSweep _) (RCtx_review g hg))
      · exact ⟨g, hg, rfl⟩
    · exact ⟨g, hg, rfl⟩

theorem filterAllAgg_form (g : GPathM) (hg : RCtx g) (reqs : List NodeId) :
    ∃ h, RCtx h ∧ filterAllAgg g reqs = review h :=
  reviewAggFuel_form _ _ (RCtx_of_keeps (keeps_foldl _ keeps_filterRequire reqs g) hg)

theorem measure_reviewAggFuel_le : ∀ (fuel : Nat) (g : GPathM),
    measure (reviewAggFuel fuel g) ≤ measure g := by
  intro fuel
  induction fuel with
  | zero => intro g; exact measure_review_le g
  | succ n ih =>
    intro g
    simp only [reviewAggFuel]
    split
    · split
      · next hlt => exact Nat.le_trans (ih _) (Nat.le_trans (Nat.le_of_lt hlt) (measure_review_le g))
      · exact measure_review_le g
    · exact measure_review_le g

-- ============================================================
-- The reader's states
-- ============================================================

/-- A state the reader can stand in, pinning with the aggressive review. -/
def ReadableAgg (g : GPathM) : Prop := ∃ g₀ reqs, RCtx g₀ ∧ g = filterAllAgg g₀ reqs

/-- **A state pinned with the aggressive review is a readable state of the base reader.** -/
theorem readable_of_readableAgg (g : GPathM) (h : ReadableAgg g) : Reader.Readable g := by
  obtain ⟨g₀, reqs, hc, rfl⟩ := h
  obtain ⟨h, hh, heq⟩ := filterAllAgg_form g₀ hc reqs
  exact ⟨h, [], hh, heq⟩

theorem RCtx_of_readableAgg (g : GPathM) (h : ReadableAgg g) : RCtx g :=
  Reader.RCtx_of_readable g (readable_of_readableAgg g h)

theorem ReadableAgg_filterAllAgg (g : GPathM) (h : ReadableAgg g) (reqs : List NodeId) :
    ReadableAgg (filterAllAgg g reqs) :=
  ⟨g, reqs, RCtx_of_readableAgg g h, rfl⟩

/-- The states the reader visits from `g₀`: `g₀` itself, and any valid pin of a visited state. -/
inductive ReadFrom (g₀ : GPathM) : GPathM → Prop where
  | start : ReadFrom g₀ g₀
  | pin (g : GPathM) (mid : NodeId) : ReadFrom g₀ g → isValid g = true →
      ReadFrom g₀ (filterAllAgg g [mid])

-- ============================================================
-- The reading loop
-- ============================================================

/-- **The one-pin obligation**, for the aggressive review: at a step that still has a choice, some
pin keeps the graph valid. -/
def PickSomeAgg (g : GPathM) : Prop :=
  hasChoice g = true → ∃ k, 0 ≤ k ∧ k < g.current_step ∧ choiceAt g k = true ∧
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAllAgg g [q.id]) = true

theorem measure_lt_of_choiceAt (g : GPathM) (k : Int) (hck : choiceAt g k = true)
    (q : PathNodeId) (hq : q ∈ ownersAt g.gowners k) :
    measure (filterAllAgg g [q.id]) < measure g := by
  obtain ⟨x, hx, hx2⟩ := List.any_eq_true.mp hck
  obtain ⟨y, hy, hne⟩ := List.any_eq_true.mp hx2
  have hxs : x.id.step = k := eq_of_beq (List.mem_filter.mp hx).2
  have hys : y.id.step = k := eq_of_beq (List.mem_filter.mp hy).2
  have hqs : q.id.step = k := eq_of_beq (List.mem_filter.mp hq).2
  have hxy : x.id ≠ y.id := bne_iff_ne.mp hne
  refine Nat.lt_of_le_of_lt (measure_reviewAggFuel_le _ _) ?_
  show measure (filterRequire g q.id) < measure g
  if hxq : x.id = q.id then
    refine measure_filterRequire_lt g q.id y (List.mem_filter.mp hy).1 (by rw [hys, hqs]) ?_
    intro h; exact hxy (hxq.trans h.symm)
  else
    exact measure_filterRequire_lt g q.id x (List.mem_filter.mp hx).1 (by rw [hxs, hqs]) hxq

theorem inhabited_of_descentAgg (g₀ : GPathM)
    (hpick : ∀ g, ReadFrom g₀ g → isValid g = true → PickSomeAgg g) :
    ∀ (m : Nat) (g : GPathM), measure g ≤ m → ReadableAgg g → ReadFrom g₀ g →
      isValid g = true → Inhabited g := by
  intro m
  induction m with
  | zero =>
    intro g hm hR hF hv
    match hch : hasChoice g with
    | false => exact Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv hch
    | true =>
      obtain ⟨k, _, _, hck, q, hq, _⟩ := hpick g hF hv hch
      exact absurd (measure_lt_of_choiceAt g k hck q hq) (by omega)
  | succ m ih =>
    intro g hm hR hF hv
    match hch : hasChoice g with
    | false => exact Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv hch
    | true =>
      obtain ⟨k, _, _, hck, q, hq, hv'⟩ := hpick g hF hv hch
      have hlt := measure_lt_of_choiceAt g k hck q hq
      obtain ⟨p, hp⟩ := ih (filterAllAgg g [q.id]) (by omega) (ReadableAgg_filterAllAgg g hR [q.id])
        (ReadFrom.pin g q.id hF hv) hv'
      exact ⟨p, denot_of_pruned (pruned_filterAllAgg g [q.id]) (RCtx_of_readableAgg g hR).nodup p hp⟩

/-- **The reading loop with the aggressive review.** A valid readable state denotes a path as soon as,
at every state the reader visits from it, some pin keeps the graph valid. -/
theorem Inhabited_of_pickSomeAgg (g₀ : GPathM) (h : ReadableAgg g₀) (hv : isValid g₀ = true)
    (hpick : ∀ g, ReadFrom g₀ g → isValid g = true → PickSomeAgg g) : Inhabited g₀ :=
  inhabited_of_descentAgg g₀ hpick (measure g₀) g₀ (Nat.le_refl _) h ReadFrom.start hv

/-- info: 'AbsSat.GraphPath.Model.ReaderAgg.readable_of_readableAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readable_of_readableAgg

/-- info: 'AbsSat.GraphPath.Model.ReaderAgg.Inhabited_of_pickSomeAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_pickSomeAgg

end AbsSat.GraphPath.Model.ReaderAgg
