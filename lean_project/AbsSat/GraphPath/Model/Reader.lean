-- lean_project/AbsSat/GraphPath/Model/Reader.lean
import AbsSat.GraphPath.Model.Pinned
import AbsSat.GraphPath.Model.NodeIds
import AbsSat.GraphPath.Model.PathExists
import AbsSat.GraphPath.Model.Survive

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


-- ============================================================
-- A chain is a woven set, so the reader can follow it
-- ============================================================

/-- The nodes a chain picks. -/
def ChainSet (g : GPathM) (sel : Int → PathNodeId) : PathNodeId → Prop :=
  fun p => ∃ k, 0 ≤ k ∧ k < g.current_step ∧ sel k = p

/-- **A pairwise-owned chain is woven.** Every clause of `Survive.Closed` is
one clause of `IsChain` or `PairwiseOwned`, and the mutual-ownership clause —
the `share` condition the coherence sweeps need — *is* `PairwiseOwned`. -/
theorem WOk_chainSet (g : GPathM) (ctx : Pinned.Ctx g) (hsmp : Sons.SMP g)
    (hlink : Bridge.LinksInOwners g) (sel : Int → PathNodeId)
    (hchain : IsChain g sel) (howned : PairwiseOwned g sel) :
    Survive.WOk g (ChainSet g sel) := by
  have hmem : ∀ k, 0 ≤ k → k < g.current_step → ∀ n, g.node? (sel k) = some n →
      ∀ l, 0 ≤ l → l < g.current_step → sel l ∈ n.owners := by
    intro k hk0 hk n hn l hl0 hl
    if hlk : l = k then
      have := ctx.self (sel k) n hn
      rw [hlk]; exact this
    else
      have h := howned l k hl0 hk0 hl hk hlk
      have : ownersOf g (sel k) = n.owners := by simp only [ownersOf, hn]
      rw [this] at h
      exact (List.mem_filter.mp h).1
  have hown : ∀ p n, ChainSet g sel p → g.node? p = some n →
      ∀ v, ChainSet g sel v → v ∈ n.owners := by
    rintro p n ⟨k, hk0, hk, rfl⟩ hn v ⟨l, hl0, hl, rfl⟩
    exact hmem k hk0 hk n hn l hl0 hl
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, Survive.coown_of_bridge g hsmp hlink _⟩, hown⟩, hsmp, ctx.shape.notroot⟩
  · -- gow
    rintro p ⟨k, hk0, hk, rfl⟩
    obtain ⟨hs, hstep⟩ := hchain.1 k hk0 hk
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    exact ctx.ownGow (sel k) n hn (sel k) (ctx.self (sel k) n hn)
      (by rw [hstep]; exact hk0) (by rw [hstep]; exact hk)
  · -- node
    rintro p ⟨k, hk0, hk, rfl⟩
    exact (hchain.1 k hk0 hk).1
  · -- support
    rintro p n hn ⟨k, hk0, hk, rfl⟩ l hl0 hl
    obtain ⟨_, hstep⟩ := hchain.1 l hl0 hl
    exact ⟨sel l, hmem k hk0 hk n hn l hl0 hl, ⟨l, hl0, hl, rfl⟩, hstep⟩
  · -- parent
    rintro p n hn ⟨k, hk0, hk, rfl⟩ hroot
    obtain ⟨hs, hstep⟩ := hchain.1 k hk0 hk
    have hkpos : 0 < k := by
      rcases Int.lt_or_lt_of_ne (fun he : k = 0 => hroot (by
        have := ctx.rootz n (List.mem_of_find?_eq_some hn)
          (by rw [node?_id_eq g (sel k) n hn, hstep]; exact he)
        rw [node?_id_eq g (sel k) n hn] at this; exact this)) with h | h
      · omega
      · exact h
    have hlink' := hchain.2 (k - 1) (by omega) (by omega)
    have hkk : k - 1 + 1 = k := by omega
    rw [hkk, hn] at hlink'
    exact ⟨sel (k - 1), hlink', ⟨k - 1, by omega, by omega, rfl⟩⟩
  · -- son
    rintro p ⟨k, hk0, hk, rfl⟩ hlast
    obtain ⟨_, hstep⟩ := hchain.1 k hk0 hk
    have hk1 : k + 1 < g.current_step := by
      rw [hstep] at hlast; omega
    obtain ⟨hs1, _⟩ := hchain.1 (k + 1) (by omega) hk1
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs1
    have hlink' := hchain.2 k hk0 hk1
    rw [hm] at hlink'
    exact ⟨sel (k + 1), m, ⟨k + 1, by omega, hk1, rfl⟩, hm, hlink'⟩

/-- **The reader can always follow a chain that exists.** Pinning on the map
node the chain picks at a step keeps the graph valid — through the pin, the
`cleanInvalid` sweep *and* both coherence sweeps. -/
theorem isValid_pin_of_chain (g : GPathM) (ctx : Pinned.Ctx g) (hsmp : Sons.SMP g)
    (hlink : Bridge.LinksInOwners g) (sel : Int → PathNodeId)
    (hchain : IsChain g sel) (howned : PairwiseOwned g sel)
    (k : Int) (hk0 : 0 ≤ k) (hk : k < g.current_step) :
    isValid (filterAll g [(sel k).id]) = true := by
  have hw := WOk_chainSet g ctx hsmp hlink sel hchain howned
  refine Survive.isValid_filterAll_of_Woven g _ hw [(sel k).id] ?_ ?_
  · rintro r hr p ⟨l, hl0, hl, rfl⟩ hs
    rcases List.mem_singleton.mp hr with rfl
    obtain ⟨_, hstepl⟩ := hchain.1 l hl0 hl
    obtain ⟨_, hstepk⟩ := hchain.1 k hk0 hk
    have : l = k := by rw [hstepl] at hs; rw [hs, hstepk]
    rw [this]
  · intro l hl0 hl
    obtain ⟨_, hstep⟩ := hchain.1 l hl0 hl
    exact ⟨sel l, ⟨l, hl0, hl, rfl⟩, hstep⟩

/-- info: 'AbsSat.GraphPath.Model.Reader.isValid_pin_of_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_pin_of_chain


/-- **The reader's obligation is exactly the verdict.** If the state denotes
anything, the reader has a good pick at every step that still has a choice —
namely the map node the chain itself picks.

With `Inhabited_of_pickSome_readable` in the other direction, `PickSome` and
`Inhabited` stand or fall together. So the reader's `throw("GRAVE ERROR")` is
not a weaker foothold than "no zombies": it is the same statement. -/
theorem PickSome_of_Inhabited (g : GPathM) (ctx : Pinned.Ctx g) (hsmp : Sons.SMP g)
    (hlink : Bridge.LinksInOwners g) (h : AbsSat.GraphPath.Model.Inhabited g) :
    PickInduction.PickSome g := by
  intro hch
  obtain ⟨_, sel, hchain, howned, _⟩ := h
  obtain ⟨k, hkmem, hck⟩ := List.any_eq_true.mp hch
  obtain ⟨hk0, hk1⟩ := PickInduction.intRange_bounds hkmem
  have hk : k < g.current_step := by omega
  obtain ⟨hs, hstep⟩ := hchain.1 k hk0 hk
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
  have hgow : sel k ∈ g.gowners :=
    ctx.ownGow (sel k) n hn (sel k) (ctx.self (sel k) n hn)
      (by rw [hstep]; exact hk0) (by rw [hstep]; exact hk)
  exact ⟨k, hk0, hk, hck, sel k, Extendable.mem_ownersAt hgow hstep,
    isValid_pin_of_chain g ctx hsmp hlink sel hchain howned k hk0 hk⟩

/-- info: 'AbsSat.GraphPath.Model.Reader.PickSome_of_Inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PickSome_of_Inhabited


-- ============================================================
-- Where symmetry can be lost, and where it cannot
-- ============================================================

/-!
`Threaded.OwnSymmetric` is measured to hold at the state the reader is handed
(`--finalowners`: **0 violations in 11,009 nodes** over 64 final states and five
seeds) and to fail on partial states (185 in 116,330, v54). Rather than assume
it, this section asks which of the machine's operations can break it.

The answer is: **exactly one**.

* `addNode` creates ownership *symmetrically*. The newcomer takes every global
  owner, and — the line the executable comments as
  `all_previous_nodes_are_owners_of_me!` — every node takes the newcomer. Since
  a node is always a global owner, the two halves match.
* `filterRequire` touches only the global owner list; node tables are
  untouched.
* `cleanInvalid` intersects **every** node's owners with the *same* list, the
  global owners. A single step of the sweep is asymmetric, but the completed
  sweep removes a dropped id from every table at once, and the id's own node
  loses self-ownership, fails `isValidNode` at its own step and goes. **Argued,
  not proved** — the sweep changes the global owners as it removes nodes, so
  the bookkeeping is a piece of work in itself.
* `reviewNode` intersects a node's owners with the union of **its own
  neighbours'** owners. That quantity is per-node, so it can remove `q` from
  `owners p` while leaving `p` in `owners q`. This is the only operation with
  no symmetric counterpart at all.

The two lemmas below prove the first two bullets. The third is argued, the
fourth is where the 185 violations on partial states must come from — and what
a proof of symmetry at full length would have to close.
-/

theorem OwnSymmetric_filterRequire (g : GPathM) (req : NodeId)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (filterRequire g req) :=
  fun p n q m hp hq hqn => h p n q m hp hq hqn

/-- **`addNode` cannot break symmetry.** The newcomer is owned by everything
and owns every global owner, and a node is always a global owner. -/
theorem OwnSymmetric_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hng : Ownership.NodesAreGowners g)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (addNode g d title) := by
  -- every node of the extension is either an old one or the newcomer
  have hcase : ∀ (p : PathNodeId) (n : PNodeM), (addNode g d title).node? p = some n →
      (∃ n₀, g.node? p = some n₀ ∧ n = upMap g d n₀) ∨
      (p = newPid g d ∧ n.owners = g.gowners ++ [newPid g d]) := by
    intro p n hn
    if hps : p.id.step < g.current_step then
      exact Or.inl (addNode_node?_below g d title hd p n hn hps)
    else
      have hid : n.id = p := node?_id_eq _ p n hn
      have hmem : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn
      rw [addNode_nodes] at hmem
      rcases List.mem_append.mp hmem with hl | hr
      · exfalso
        obtain ⟨n₀, hn₀, hEq⟩ := List.mem_map.mp hl
        have : n.id = n₀.id := by rw [← hEq, upMap_id]
        have := hbelow n₀ hn₀
        rw [← ‹n.id = n₀.id›, hid] at this
        omega
      · rcases List.mem_singleton.mp hr with rfl
        refine Or.inr ⟨?_, ?_⟩
        · rw [← hid]; rfl
        · simp only [addOwner, upNode]
    -- end hcase
  intro p n q m hp hq hqn
  rcases hcase p n hp with ⟨n₀, hn₀, rfl⟩ | ⟨rfl, hno⟩
  · rcases hcase q m hq with ⟨m₀, hm₀, rfl⟩ | ⟨rfl, hmo⟩
    · rw [upMap_owners] at hqn ⊢
      rcases List.mem_append.mp hqn with hq0 | hq1
      · exact List.mem_append_left _ (h p n₀ q m₀ hn₀ hm₀ hq0)
      · exfalso
        rcases List.mem_singleton.mp hq1 with rfl
        have hmid : m₀.id = newPid g d := node?_id_eq g _ m₀ hm₀
        have := hbelow m₀ (List.mem_of_find?_eq_some hm₀)
        rw [hmid] at this
        simp only [newPid] at this
        omega
    · rw [hmo]
      have := hng n₀ (List.mem_of_find?_eq_some hn₀)
      rw [node?_id_eq g p n₀ hn₀] at this
      exact List.mem_append_left _ this
  · rcases hcase q m hq with ⟨m₀, hm₀, rfl⟩ | ⟨rfl, hmo⟩
    · rw [upMap_owners]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · rw [hmo]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- info: 'AbsSat.GraphPath.Model.Reader.OwnSymmetric_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_addNode

end AbsSat.GraphPath.Model.Reader
