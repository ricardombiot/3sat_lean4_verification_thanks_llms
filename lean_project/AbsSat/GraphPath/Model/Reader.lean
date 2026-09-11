-- lean_project/AbsSat/GraphPath/Model/Reader.lean
import AbsSat.GraphPath.Model.Pinned
import AbsSat.GraphPath.Model.NodeIds
import AbsSat.GraphPath.Model.PathExists

/-!
# The reader, as the author designed it

`PathReader.read_step!` in the Julia original does three things and repeats:

1. **select** a node of the current step (`first(ids)`) and take its *map* id;
2. **pin** it — `filter_require!` drops every global owner at that step naming
   a different map node, which is exactly "assume we selected all of this
   node's owners";
3. **review to a fixpoint** — `make_review_owners!` loops `clean_invalid_nodes!`
   and the coherence pass until nothing more moves, and asserts the graph is
   still valid.

Each round shrinks the set of solutions the state denotes. The run ends when
there is nothing left to choose: **one map node per step**, which is one
solution.

That process is already a theorem shape in this development —
`PickInduction.Inhabited_of_pickSome`, with the measure descending by
`measure_lt_of_choiceAt` and the base case discharged by
`Pinned.inhabited_of_noChoice`. What was missing is that the induction wants a
class `P` closed under `filterAll`, and every invariant in the library is
stated for **one** `filterAll` applied to a `Reachable` state — while the
reader pins again and again.

This module supplies that class. `RCtx` bundles the source invariants, each of
which has an invariant-to-invariant transfer lemma (not a `Reachable` one), so
`RCtx` survives pinning; `Readable` is "a pinned state of an `RCtx` state", and
it is closed under pinning by construction.

The result, `Inhabited_of_pickSome_readable`, is the author's reading process
with **one** hypothesis left: that some pick at a step that still has a choice
keeps the graph valid.
-/

namespace AbsSat.GraphPath.Model.Reader

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- The invariants the reader needs to carry, all of them proved for the
machine's states and all of them stable under pinning. -/
structure RCtx (g : GPathM) : Prop where
  oos   : SelfOwn.OOS g
  snn   : SelfOwn.SNN g
  gn    : GownersNodes.GN g
  shape : Parents.Shape g
  rootz : Sons.RootAtZero g
  pmp   : ParentId.PMP g
  below : ∀ n ∈ g.nodes, n.id.id.step < g.current_step
  nodup : NodupIds g

variable (reqOf : NodeId → List NodeId)

theorem RCtx_reachable (g : GPathM) (hnd : NodupIds g) (h : Reachable reqOf g) : RCtx g where
  oos := SelfOwn.OOS_reachable reqOf g h
  snn := SelfOwn.SNN_reachable reqOf g h
  gn := GownersNodes.GN_reachable reqOf g h
  shape := Parents.Shape_reachable reqOf g h
  rootz := Sons.RootAtZero_reachable reqOf g h
  pmp := ParentId.PMP_reachable reqOf g h
  below := steps_below_current reqOf h
  nodup := hnd

/-- **Pinning keeps you inside the class.** Every field transfers by its own
`_of_pruned` / `_filterAll` lemma; `nodup` is `NodeIds.NodupIds_filterAll`. -/
theorem RCtx_filterAll (g : GPathM) (h : RCtx g) (reqs : List NodeId) :
    RCtx (filterAll g reqs) where
  oos := SelfOwn.OOS_filterAll g reqs h.oos
  snn := SelfOwn.SNN_of_pruned (pruned_filterAll g reqs) h.snn
  gn := GownersNodes.GN_filterAll g reqs h.gn
  shape := Parents.Shape_of_pruned_pn (pruned_filterAll g reqs)
    (Parents.PN_filterAll g reqs h.shape.pn) h.shape
  rootz := Sons.RootAtZero_of_pruned (pruned_filterAll g reqs) h.rootz
  pmp := ParentId.PMP_of_pruned (pruned_filterAll g reqs) h.pmp
  below := Certifies.nodes_below_of_pruned (pruned_filterAll g reqs) h.below
  nodup := NodeIds.NodupIds_filterAll g h.nodup reqs

/-- A state the reader can be standing in: a pinned state of a state in the
class. Every state the machine builds is one (`readable_of_reachable`), and
pinning again stays inside (`Readable_filterAll`). -/
def Readable (g : GPathM) : Prop := ∃ g₀ reqs, RCtx g₀ ∧ g = filterAll g₀ reqs

theorem readable_of_reachable (g : GPathM) (hnd : NodupIds g) (h : Reachable reqOf g)
    (reqs : List NodeId) : Readable (filterAll g reqs) :=
  ⟨g, reqs, RCtx_reachable reqOf g hnd h, rfl⟩

theorem RCtx_of_readable (g : GPathM) (h : Readable g) : RCtx g := by
  obtain ⟨g₀, reqs, hc, rfl⟩ := h
  exact RCtx_filterAll g₀ hc reqs

theorem Readable_filterAll (g : GPathM) (h : Readable g) (reqs : List NodeId) :
    Readable (filterAll g reqs) :=
  ⟨g, reqs, RCtx_of_readable g h, rfl⟩

-- ============================================================
-- What a readable state gives, once it is valid
-- ============================================================

/-- The review-fixpoint context, from the class instead of from `Reachable`. -/
theorem Ctx_of_readable (g : GPathM) (h : Readable g) (hv : isValid g = true) :
    Pinned.Ctx g := by
  obtain ⟨g₀, reqs, hc, rfl⟩ := h
  have hrc := RCtx_filterAll g₀ hc reqs
  have hshape := hrc.shape
  exact
    { self := SelfOwn.SelfOwned_of_OOS _ hv hrc.oos hrc.snn hrc.below
      gn := hrc.gn
      shape := hshape
      rootz := hrc.rootz
      pmp := hrc.pmp
      nodeval := fun pid n hn => review_node_valid _ hv pid n hn
      ownGow := fun pid n hn q hq hlo hhi =>
        Candidates.owner_mem_gowners _ hv pid n hn q hq hlo hhi }

/-- A path through a valid readable state — v27's descent, over the class. -/
theorem exists_isChain_of_readable (g : GPathM) (h : Readable g) (hv : isValid g = true) :
    ∃ sel, IsChain g sel := by
  if hpos : 0 < g.current_step then
    obtain ⟨g₀, reqs, hc, rfl⟩ := h
    have hrc := RCtx_filterAll g₀ hc reqs
    obtain ⟨q, hq, hqstep⟩ :=
      PickInduction.gowner_of_isValid _ hv ((filterAll g₀ reqs).current_step - 1)
        (by omega) (by omega)
    obtain ⟨n, hn, hid⟩ := hrc.gn q hq
    have hsome : ((filterAll g₀ reqs).node? n.id).isSome = true :=
      (GownersNodes.hasNode_iff _ n.id).mp ⟨n, hn, rfl⟩
    have hnstep : n.id.id.step = (filterAll g₀ reqs).current_step - 1 := by
      rw [hid]; exact hqstep
    have hseed : Extendable.PartialChain (filterAll g₀ reqs) (fun _ => n.id)
        ((filterAll g₀ reqs).current_step - 1) ((filterAll g₀ reqs).current_step - 1) := by
      refine ⟨?_, ?_⟩
      · intro i hi1 hi2
        have hie : i = (filterAll g₀ reqs).current_step - 1 := by omega
        subst hie
        exact ⟨hsome, hnstep⟩
      · intro i _ hi2; omega
    obtain ⟨sel, hpc⟩ := PathExists.descend _ hv hrc.shape
      ((filterAll g₀ reqs).current_step - 1).toNat (fun _ => n.id)
      ((filterAll g₀ reqs).current_step - 1) ((filterAll g₀ reqs).current_step - 1)
      (Nat.le_refl _) (by omega) (Int.le_refl _) hseed
    exact ⟨sel, Extendable.isChain_of_partial _ sel hpc⟩
  else
    refine ⟨fun _ => { id := { step := 0, index := 0 }, parent_id := none }, ?_, ?_⟩
    · intro k hk1 hk2; omega
    · intro k hk1 hk2; omega

/-- **The base case, on the class.** Nothing left to choose means one map node
per step: `Pinned.pairwiseOwned_of_fullyPinned` makes any path pairwise owned,
so the state denotes something. This is the author's "we are left with one
solution". -/
theorem inhabited_of_noChoice_readable (g : GPathM) (h : Readable g) (hv : isValid g = true)
    (hnc : PickInduction.NoChoice g) : AbsSat.GraphPath.Model.Inhabited g :=
  Pinned.inhabited_of_noChoice g (Ctx_of_readable g h hv) hnc
    (exists_isChain_of_readable g h hv)

-- ============================================================
-- The reading process, closed
-- ============================================================

/-- **The reader's loop, with one hypothesis left.**

Select, pin, review; the measure strictly drops at every round
(`measure_lt_of_choiceAt`), so the loop ends; it ends with no choice left,
and there the state denotes a solution.

The only thing not proved is `PickSome`: that at a step which still has a
choice, *some* pick survives the review. That is the reader's own obligation —
`Verdict.ReadStable` — and `lake exe extend --read` finds no violation of it. -/
theorem Inhabited_of_pickSome_readable (g : GPathM) (h : Readable g) (hv : isValid g = true)
    (hpick : ∀ h' : GPathM, Readable h' → isValid h' = true → PickInduction.PickSome h') :
    AbsSat.GraphPath.Model.Inhabited g :=
  PickInduction.Inhabited_of_pickSome Readable
    (fun h' mid hR _ => Readable_filterAll h' hR [mid])
    (fun h' hR => (RCtx_of_readable h' hR).nodup)
    (fun h' hR hv' => hpick h' hR hv')
    (fun h' hR hv' hnc => inhabited_of_noChoice_readable h' hR hv' hnc)
    g h hv

/-- info: 'AbsSat.GraphPath.Model.Reader.Inhabited_of_pickSome_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_pickSome_readable


-- ============================================================
-- The last hypothesis: ids really are unique
-- ============================================================

theorem map_id_of_idpres (l : List PNodeM) (f : PNodeM → PNodeM) (hf : ∀ n, (f n).id = n.id) :
    (l.map f).map (·.id) = l.map (·.id) := by
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left (fun n _ => hf n)

/-- `addNode` appends one id, and it is new: everything already there sits at a
step strictly below `current_step`, and the newcomer sits *at* it. -/
theorem nodup_addNode (g : GPathM) (d : NodeId) (title : String) (hnd : NodupIds g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hd : d.step = g.current_step) :
    NodupIds (addNode g d title) := by
  have hf : ∀ (ps : List PathNodeId) (n : PNodeM),
      (if ps.contains n.id
        then { n with sons := n.sons ++ [({ id := d, parent_id := g.map_parent } : PathNodeId)] }
        else n).id = n.id := by
    intro ps n; split <;> rfl
  have hids : NodeIds.Ids (addNode g d title)
      = NodeIds.Ids g ++ [({ id := d, parent_id := g.map_parent } : PathNodeId)] := by
    simp only [NodeIds.Ids, addNode, List.map_append, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun n _ => hf _ n)
  show (NodeIds.Ids (addNode g d title)).Nodup
  rw [hids, List.nodup_append]
  refine ⟨hnd, by simp, ?_⟩
  intro a ha b hb hab
  rcases List.mem_singleton.mp hb with rfl
  obtain ⟨n, hn, hnid⟩ := List.mem_map.mp ha
  have hlt := hbelow n hn
  rw [hnid] at hlt
  rw [hab] at hlt
  simp only at hlt
  omega

theorem nodup_up (g : GPathM) (d : NodeId) (title : String) (hnd : NodupIds g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hd : d.step = g.current_step) :
    NodupIds (GPathM.up g d title) := by
  unfold GPathM.up
  split
  · exact nodup_addNode g d title hnd hbelow hd
  · exact hnd

/-- `join` concatenates `g₁`'s ids with the ids of `g₂` that `g₁` does not
already carry, so the result is `Nodup` whenever both sides are. -/
theorem nodup_join (g₁ g₂ : GPathM) (h₁ : NodupIds g₁) (h₂ : NodupIds g₂) :
    NodupIds (GPathM.join g₁ g₂) := by
  have hf : ∀ n : PNodeM,
      (match g₂.node? n.id with | some m => mergeNode n m | none => n).id = n.id := by
    intro n
    cases hm : g₂.node? n.id with
    | none => rfl
    | some m => rfl
  have hids : NodeIds.Ids (GPathM.join g₁ g₂)
      = NodeIds.Ids g₁ ++ (g₂.nodes.filter (fun m => (g₁.node? m.id).isNone)).map (·.id) := by
    simp only [NodeIds.Ids, GPathM.join, List.map_append, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun n _ => hf n)
  show (NodeIds.Ids (GPathM.join g₁ g₂)).Nodup
  rw [hids, List.nodup_append]
  refine ⟨h₁, List.Sublist.nodup (List.Sublist.map _ List.filter_sublist) h₂, ?_⟩
  intro a ha b hb hab
  obtain ⟨m, hm, hmid⟩ := List.mem_map.mp hb
  have hnone : (g₁.node? m.id).isNone = true := (List.mem_filter.mp hm).2
  obtain ⟨n, hn, hnid⟩ := List.mem_map.mp ha
  have hsome : (g₁.node? a).isSome = true := by
    rw [← hnid]
    exact Option.isSome_iff_exists.mpr ⟨n, node?_of_mem h₁ n hn⟩
  rw [hab, ← hmid, Option.isNone_iff_eq_none.mp hnone] at hsome
  exact Bool.noConfusion hsome

/-- **Every state the machine builds has unique ids.** Seed: one node. Up: the
newcomer is above everything already there. Join: the union is taken by id. -/
theorem NodupIds_reachable (g : GPathM) (h : Reachable reqOf g) : NodupIds g := by
  induction h with
  | seed d title _ _ =>
    show (NodeIds.Ids (GPathM.initSeed d title)).Nodup
    simp only [NodeIds.Ids, initSeed_nodes]
    simp
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    refine nodup_up _ d title (NodeIds.NodupIds_filterAll g ih (reqOf d))
      (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hr)) ?_
    rw [hpr.step_eq]; exact hstep
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact nodup_join g₁ g₂ ih₁ ih₂

/-- info: 'AbsSat.GraphPath.Model.Reader.NodupIds_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NodupIds_reachable

/-- **The reader's loop on the machine's own states.** No hypothesis left but
the pick. -/
theorem Inhabited_of_pickSome_machine (g : GPathM) (reqs : List NodeId)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true)
    (hpick : ∀ h' : GPathM, Readable h' → isValid h' = true → PickInduction.PickSome h') :
    AbsSat.GraphPath.Model.Inhabited (filterAll g reqs) :=
  Inhabited_of_pickSome_readable (filterAll g reqs)
    (readable_of_reachable reqOf g (NodupIds_reachable reqOf g hreach) hreach reqs) hv hpick

/-- info: 'AbsSat.GraphPath.Model.Reader.Inhabited_of_pickSome_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_pickSome_machine

end AbsSat.GraphPath.Model.Reader
