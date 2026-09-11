-- lean_project/AbsSat/GraphPath/Model/NodeIds.lean
import AbsSat.GraphPath.Model.Fuel
import AbsSat.GraphPath.Model.Filter

/-!
# The id list only ever shrinks

`NodupIds` — node ids pairwise distinct — is the one hypothesis `Filter.lean`
and `PickInduction.lean` keep asking for and nobody discharges. It is asked for
because pruning may delete the first node carrying an id and `node?` would then
answer with a different one.

Every operation the review loop performs does one of two things to the node
list: **map** it with a function that leaves `id` alone (`updateAt`,
`unlinkIncompatible`), or **filter** it (`removeNode`). So the list of ids is a
sublist of what it was, and `Nodup` comes along for the ride.

That is all this module proves — and with it the reader can pin as many times
as it likes without re-assuming anything.
-/

namespace AbsSat.GraphPath.Model.NodeIds

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- The ids a state carries, in order. -/
def Ids (g : GPathM) : List PathNodeId := g.nodes.map (·.id)

/-- Mapping the node list with an id-preserving function leaves the ids alone. -/
theorem ids_map (g : GPathM) (f : PNodeM → PNodeM) (hf : ∀ n, (f n).id = n.id) :
    Ids { g with nodes := g.nodes.map f } = Ids g := by
  simp only [Ids, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun n _ => hf n)

theorem ids_filter (g : GPathM) (p : PNodeM → Bool) :
    (Ids { g with nodes := g.nodes.filter p }).Sublist (Ids g) :=
  List.Sublist.map _ List.filter_sublist

-- ============================================================
-- The primitive operations
-- ============================================================

theorem ids_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, (f n).id = n.id) : Ids (updateAt g id f) = Ids g := by
  refine ids_map g (fun n => match n.id == id with | true => f n | false => n) ?_
  intro n
  split
  · exact hf n
  · rfl

theorem ids_unlinkIncompatible (g : GPathM) (id : PathNodeId) :
    Ids (unlinkIncompatible g id) = Ids g := by
  unfold unlinkIncompatible
  cases hn : g.node? id with
  | none => rfl
  | some n =>
    refine ids_map g (unlinkMap n id) ?_
    intro m
    unfold unlinkMap
    split
    · rfl
    · split
      · rfl
      · rfl

theorem ids_removeNode (g : GPathM) (id : PathNodeId) :
    (Ids (removeNode g id)).Sublist (Ids g) := by
  unfold removeNode Ids
  simp only [List.map_map, Function.comp_def]
  have hmap : (g.nodes.filter (fun n => n.id != id)).map
      (fun n => ({ n with
        parents := n.parents.filter (fun p => p != id),
        sons := n.sons.filter (fun s => s != id) } : PNodeM).id)
      = (g.nodes.filter (fun n => n.id != id)).map (·.id) :=
    List.map_congr_left (fun _ _ => rfl)
  rw [hmap]
  exact List.Sublist.map _ List.filter_sublist

-- ============================================================
-- The sweeps
-- ============================================================

theorem ids_cleanInvalidGo (g : GPathM) :
    ∀ (l : List PathNodeId), (Ids (cleanInvalidGo g l)).Sublist (Ids g) := by
  intro l
  induction l generalizing g with
  | nil => exact List.Sublist.refl _
  | cons id rest ih =>
    unfold cleanInvalidGo
    cases hn : g.node? id with
    | none => exact ih g
    | some d =>
      simp only
      have hup : Ids (updateAt g id (fun n => { n with owners := intersectOwners n.owners g.gowners }))
          = Ids g := ids_updateAt g id _ (fun _ => rfl)
      have hunl := ids_unlinkIncompatible
        (updateAt g id (fun n => { n with owners := intersectOwners n.owners g.gowners })) id
      split
      · exact List.Sublist.trans (ih _) (by rw [hunl, hup]; exact List.Sublist.refl _)
      · exact List.Sublist.trans (ih _)
          (List.Sublist.trans (ids_removeNode _ id) (by rw [hunl, hup]; exact List.Sublist.refl _))

theorem ids_cleanInvalid (g : GPathM) : (Ids (cleanInvalid g)).Sublist (Ids g) :=
  ids_cleanInvalidGo g _

theorem ids_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId) :
    (Ids (reviewNode g nb id)).Sublist (Ids g) := by
  unfold reviewNode
  cases hn : g.node? id with
  | none => exact List.Sublist.refl _
  | some d =>
    simp only
    split
    · have hup : Ids (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) }))
          = Ids g := ids_updateAt g id _ (fun _ => rfl)
      have hunl := ids_unlinkIncompatible
        (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) id
      split
      · rw [hunl, hup]; exact List.Sublist.refl _
      · exact List.Sublist.trans (ids_removeNode _ id)
          (by rw [hunl, hup]; exact List.Sublist.refl _)
    · exact ids_removeNode g id

theorem ids_reviewLine (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int) :
    (Ids (reviewLine g nb k)).Sublist (Ids g) := by
  unfold reviewLine
  have main : ∀ (l : List PathNodeId) (h : GPathM),
      (Ids (l.foldl (fun h id => reviewNode h nb id) h)).Sublist (Ids h) := by
    intro l
    induction l with
    | nil => intro h; exact List.Sublist.refl _
    | cons x xs ih =>
      intro h
      simp only [List.foldl_cons]
      exact List.Sublist.trans (ih _) (ids_reviewNode h nb x)
  exact main _ g

theorem ids_reviewSteps (g : GPathM) (nb : PNodeM → List PathNodeId) :
    ∀ (ks : List Int), (Ids (reviewSteps g nb ks)).Sublist (Ids g) := by
  intro ks
  induction ks generalizing g with
  | nil => exact List.Sublist.refl _
  | cons k rest ih =>
    unfold reviewSteps
    split
    · exact List.Sublist.trans (ih _) (ids_reviewLine g nb k)
    · exact List.Sublist.refl _

theorem ids_reviewPass (g : GPathM) : (Ids (reviewPass g)).Sublist (Ids g) :=
  List.Sublist.trans (ids_reviewSteps _ _ _)
    (List.Sublist.trans (ids_reviewSteps _ _ _) (ids_cleanInvalid g))

theorem ids_reviewFuel : ∀ (fuel : Nat) (g : GPathM),
    (Ids (reviewFuel fuel g)).Sublist (Ids g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact List.Sublist.refl _
  | succ f ih =>
    intro g
    unfold reviewFuel
    split
    · simp only
      split
      · exact List.Sublist.trans (ih _) (ids_reviewPass g)
      · exact ids_reviewPass g
    · exact List.Sublist.refl _

theorem ids_review (g : GPathM) : (Ids (review g)).Sublist (Ids g) :=
  ids_reviewFuel _ g

theorem ids_filterRequire (g : GPathM) (req : NodeId) :
    Ids (filterRequire g req) = Ids g := rfl

theorem ids_filterAll (g : GPathM) (reqs : List NodeId) :
    (Ids (filterAll g reqs)).Sublist (Ids g) := by
  unfold filterAll
  refine List.Sublist.trans (ids_review _) ?_
  have main : ∀ (l : List NodeId) (h : GPathM), Ids (l.foldl filterRequire h) = Ids h := by
    intro l
    induction l with
    | nil => intro h; rfl
    | cons x xs ih => intro h; simp only [List.foldl_cons]; rw [ih, ids_filterRequire]
  rw [main reqs g]
  exact List.Sublist.refl _

-- ============================================================
-- What it was for
-- ============================================================

/-- **Pinning never duplicates an id.** So the reader can filter as many times
as it likes: `NodupIds` is established once and survives the whole run. -/
theorem NodupIds_filterAll (g : GPathM) (h : NodupIds g) (reqs : List NodeId) :
    NodupIds (filterAll g reqs) :=
  List.Sublist.nodup (ids_filterAll g reqs) h

/-- info: 'AbsSat.GraphPath.Model.NodeIds.NodupIds_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NodupIds_filterAll

end AbsSat.GraphPath.Model.NodeIds
