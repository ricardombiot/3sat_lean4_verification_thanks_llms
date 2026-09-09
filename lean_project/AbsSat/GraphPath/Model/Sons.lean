-- lean_project/AbsSat/GraphPath/Model/Sons.lean
import AbsSat.GraphPath.Model.Ownership

/-!
**Two more of `ChainSound`'s conditions: `son_link` and `root_shape`.**

`ChainSound` is `IsChain ∧ PairwiseOwned` plus three bookkeeping fields.
v27 proved `IsChain`; v28 showed `PairwiseOwned` is the irreducible one. This
module closes two of the three remaining fields, in the idiom of
`GownersNodes.lean` and `Parents.lean`.

* `son_link` — `sel (k+1)` is a *son* of `sel k`. `IsChain` already gives the
  parent link; what is needed is that the two link tables mirror each other,
  which is `SMP` below.
* `root_shape` — the step-0 node is a root and nothing above it is. The second
  half is `Parents.NotRoot`, proved in v27; the first is `RootAtZero`, its
  mirror, proved here.

Both are structural invariants of the machine, and both go through. The third
field, `self_owned`, does **not** — see the note at the end.
-/

namespace AbsSat.GraphPath.Model.Sons

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- The son table mirrors the parent table
-- ============================================================

/-- If `p` is a parent of `n`, then `n` is a son of `p`. -/
def SMP (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ p ∈ n.parents, ∀ m ∈ h.nodes, m.id = p → n.id ∈ m.sons

theorem SMP_filterRequire (g : GPathM) (req : NodeId) (h : SMP g) :
    SMP (filterRequire g req) := h

theorem SMP_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hid : ∀ n, (f n).id = n.id) (hpar : ∀ n, (f n).parents = n.parents)
    (hson : ∀ n, (f n).sons = n.sons) (h : SMP g) : SMP (updateAt g id f) := by
  intro n' hn' p hp m' hm' hmid
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  obtain ⟨m, hm, hmEq⟩ := List.mem_map.mp hm'
  have hnp : n'.parents = n.parents := by
    rw [← hEq]; cases n.id == id with | true => exact hpar n | false => rfl
  have hni : n'.id = n.id := by
    rw [← hEq]; cases n.id == id with | true => exact hid n | false => rfl
  have hms : m'.sons = m.sons := by
    rw [← hmEq]; cases m.id == id with | true => exact hson m | false => rfl
  have hmi : m'.id = m.id := by
    rw [← hmEq]; cases m.id == id with | true => exact hid m | false => rfl
  rw [hni, hms]
  exact h n hn p (by rw [← hnp]; exact hp) m hm (by rw [← hmi]; exact hmid)

theorem SMP_removeNode (g : GPathM) (id : PathNodeId) (h : SMP g) :
    SMP (removeNode g id) := by
  intro n' hn' p hp m' hm' hmid
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  obtain ⟨m, hm, hmEq⟩ := List.mem_map.mp hm'
  have hnf := List.mem_filter.mp hn
  have hmf := List.mem_filter.mp hm
  have hnp : n'.parents = n.parents.filter (fun q => q != id) := by rw [← hEq]
  have hni : n'.id = n.id := by rw [← hEq]
  have hms : m'.sons = m.sons.filter (fun s => s != id) := by rw [← hmEq]
  have hmi : m'.id = m.id := by rw [← hmEq]
  rw [hnp] at hp
  have hp' := List.mem_filter.mp hp
  have hson := h n hnf.1 p hp'.1 m hmf.1 (by rw [← hmi]; exact hmid)
  rw [hni, hms]
  exact List.mem_filter.mpr ⟨hson, by rw [← hni] at hnf ⊢; exact hnf.2⟩

theorem SMP_cleanInvalidGo (ids : List PathNodeId) :
    ∀ g : GPathM, SMP g → SMP (cleanInvalidGo g ids) := by
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGo]
    split
    · exact ih g h
    · next d _ =>
      have h₁ : SMP (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners g.gowners })) :=
        SMP_updateAt g id _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) h
      split
      · exact ih _ h₁
      · exact ih _ (SMP_removeNode _ id h₁)

theorem SMP_cleanInvalid (g : GPathM) (h : SMP g) : SMP (cleanInvalid g) :=
  SMP_cleanInvalidGo _ g h

theorem SMP_reviewNode (nb : PNodeM → List PathNodeId) (id : PathNodeId) (g : GPathM)
    (h : SMP g) : SMP (reviewNode g nb id) := by
  simp only [reviewNode]
  split
  · exact h
  · next d _ =>
    split
    · have h₁ : SMP (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) :=
        SMP_updateAt g id _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) h
      split
      · exact h₁
      · exact SMP_removeNode _ id h₁
    · exact SMP_removeNode g id h

private theorem SMP_foldl {β : Type} (f : GPathM → β → GPathM)
    (hf : ∀ g b, SMP g → SMP (f g b)) :
    ∀ (l : List β) (g : GPathM), SMP g → SMP (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons b bs ih => intro g h; simp only [List.foldl_cons]; exact ih _ (hf g b h)

theorem SMP_reviewLine (nb : PNodeM → List PathNodeId) (k : Int) (g : GPathM)
    (h : SMP g) : SMP (reviewLine g nb k) :=
  SMP_foldl (fun g id => reviewNode g nb id) (fun g id => SMP_reviewNode nb id g) _ g h

theorem SMP_reviewSteps (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, SMP g → SMP (reviewSteps g nb ks) := by
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    simp only [reviewSteps]
    split
    · exact ih _ (SMP_reviewLine nb k g h)
    · exact h

theorem SMP_reviewPass (g : GPathM) (h : SMP g) : SMP (reviewPass g) := by
  simp only [reviewPass]
  exact SMP_reviewSteps _ _ _ (SMP_reviewSteps _ _ _ (SMP_cleanInvalid g h))

theorem SMP_reviewFuel : ∀ (fuel : Nat) (g : GPathM), SMP g → SMP (reviewFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewFuel]
    split
    · split
      · exact ih _ (SMP_reviewPass g h)
      · exact SMP_reviewPass g h
    · exact h

theorem SMP_review (g : GPathM) (h : SMP g) : SMP (review g) := SMP_reviewFuel _ g h

theorem SMP_filterAll (g : GPathM) (reqs : List NodeId) (h : SMP g) :
    SMP (filterAll g reqs) :=
  SMP_review _ (SMP_foldl filterRequire (fun g r => SMP_filterRequire g r) reqs g h)

-- ============================================================
-- `addNode`, `join`, `initSeed`
-- ============================================================

theorem SMP_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hpb : Parents.PBelow g) (h : SMP g) : SMP (addNode g d title) := by
  intro n' hn' p hp m' hm' hmid
  rw [addNode_nodes] at hn' hm'
  rcases List.mem_append.mp hm' with hmm | hmm
  · obtain ⟨m, hm, hmEq⟩ := List.mem_map.mp hmm
    have hmi : m'.id = m.id := by rw [← hmEq]; exact upMap_id g d m
    have hsub : ∀ x ∈ m.sons, x ∈ m'.sons := by
      rw [← hmEq]
      simp only [upMap, addOwner, upSons]
      split
      · intro x hx; exact List.mem_append_left _ hx
      · intro x hx; exact hx
    rcases List.mem_append.mp hn' with hnn | hnn
    · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hnn
      have hni : n'.id = n.id := by rw [← hEq]; exact upMap_id g d n
      have hnp : n'.parents = n.parents := by rw [← hEq]; exact upMap_parents g d n
      rw [hnp] at hp
      rw [hni]
      exact hsub _ (h n hn p hp m hm (by rw [← hmi]; exact hmid))
    · rcases List.mem_singleton.mp hnn with rfl
      have hnp : (addOwner (newPid g d) (upNode g d title)).parents = newParents g := rfl
      rw [hnp] at hp
      have hcontains : (newParents g).contains m.id = true := by
        rw [hmi] at hmid; rw [hmid]; exact List.elem_iff.mpr hp
      show newPid g d ∈ m'.sons
      rw [← hmEq]
      simp only [upMap, addOwner, upSons, hcontains, if_pos]
      exact List.mem_append_right _ List.mem_cons_self
  · rcases List.mem_singleton.mp hmm with rfl
    exfalso
    have hpstep : p.id.step < g.current_step := by
      rcases List.mem_append.mp hn' with hnn | hnn
      · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hnn
        have hnp : n'.parents = n.parents := by rw [← hEq]; exact upMap_parents g d n
        rw [hnp] at hp
        have h1 := hpb n hn p hp
        have h2 := hbelow n hn
        omega
      · rcases List.mem_singleton.mp hnn with rfl
        have hnp : (addOwner (newPid g d) (upNode g d title)).parents = newParents g := rfl
        rw [hnp] at hp
        unfold newParents at hp
        split at hp
        · have hstep := Parents.mem_line_step g (g.current_step - 1) p hp
          omega
        · exact absurd hp List.not_mem_nil
    have hps : p.id.step = d.step := by rw [← hmid]; rfl
    omega

theorem SMP_up (g : GPathM) (d : NodeId) (title : String) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hpb : Parents.PBelow g) (h : SMP g) : SMP (up g d title) := by
  simp only [GPathM.up]
  split
  · exact SMP_addNode g d title hd hbelow hpb h
  · exact h

theorem SMP_initSeed (d : NodeId) (title : String) : SMP (GPathM.initSeed d title) := by
  intro n hn p hp
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  exact absurd hp List.not_mem_nil

theorem SMP_join (g₁ g₂ : GPathM) (hp₁ : Parents.PN g₁) (hp₂ : Parents.PN g₂)
    (h₁ : SMP g₁) (h₂ : SMP g₂) : SMP (join g₁ g₂) := by
  intro n' hn' p hp m' hm' hmid
  rw [GownersNodes.join_nodes] at hn' hm'
  -- what `n'` is, and where `p` comes from
  have key : ∀ (x : PathNodeId), x = n'.id →
      (∃ n ∈ g₁.nodes, n.id = x ∧ p ∈ n.parents) ∨ (∃ q ∈ g₂.nodes, q.id = x ∧ p ∈ q.parents) := by
    intro x hx
    rcases List.mem_append.mp hn' with hnn | hnn
    · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hnn
      have hni : n'.id = n.id := by rw [← hEq]; cases g₂.node? n.id with
        | some q => rfl
        | none => rfl
      cases hg : g₂.node? n.id with
      | none =>
        have : n'.parents = n.parents := by rw [← hEq, hg]
        rw [this] at hp
        exact Or.inl ⟨n, hn, by rw [hx, hni], hp⟩
      | some q =>
        have hpar : n'.parents =
            n.parents ++ q.parents.filter (fun r => !n.parents.contains r) := by
          rw [← hEq, hg]; rfl
        rw [hpar, List.mem_append] at hp
        have hqid : q.id = n.id := node?_id_eq g₂ n.id q hg
        rcases hp with hp | hp
        · exact Or.inl ⟨n, hn, by rw [hx, hni], hp⟩
        · exact Or.inr ⟨q, List.mem_of_find?_eq_some hg, by rw [hx, hni, hqid],
            (List.mem_filter.mp hp).1⟩
    · exact Or.inr ⟨n', (List.mem_filter.mp hnn).1, hx.symm, hp⟩
  rcases List.mem_append.mp hm' with hmm | hmm
  · -- `m'` is the join's copy of a `g₁` node
    obtain ⟨m₀, hm₀, hmEq⟩ := List.mem_map.mp hmm
    have hm₀id : m₀.id = p := by
      rw [← hmid, ← hmEq]; cases g₂.node? m₀.id with | some q => rfl | none => rfl
    rcases key n'.id rfl with ⟨n, hn, hnid, hnp⟩ | ⟨q, hq, hqid, hqp⟩
    · have hson := h₁ n hn p hnp m₀ hm₀ hm₀id
      rw [← hnid]
      rw [← hmEq]
      cases hg : g₂.node? m₀.id with
      | none => exact hson
      | some q' => exact List.mem_append_left _ hson
    · obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp
        ((GownersNodes.hasNode_iff g₂ p).mp (hp₂ q hq p hqp))
      have hq'mem : q' ∈ g₂.nodes := List.mem_of_find?_eq_some hq'
      have hq'id : q'.id = p := node?_id_eq g₂ p q' hq'
      have hson := h₂ q hq p hqp q' hq'mem hq'id
      rw [← hqid, ← hmEq]
      have hg : g₂.node? m₀.id = some q' := by rw [hm₀id]; exact hq'
      rw [hg]
      show q.id ∈ (mergeNode m₀ q').sons
      have hsons : (mergeNode m₀ q').sons =
          m₀.sons ++ q'.sons.filter (fun s => !m₀.sons.contains s) := rfl
      rw [hsons]
      cases hc : m₀.sons.contains q.id with
      | true => exact List.mem_append_left _ (List.elem_iff.mp hc)
      | false =>
        refine List.mem_append_right _ (List.mem_filter.mpr ⟨hson, ?_⟩)
        rw [hc]; rfl
  · -- `m'` is a node only `g₂` has
    have hm'mem : m' ∈ g₂.nodes := (List.mem_filter.mp hmm).1
    rcases key n'.id rfl with ⟨n, hn, hnid, hnp⟩ | ⟨q, hq, hqid, hqp⟩
    · exfalso
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp
        ((GownersNodes.hasNode_iff g₁ p).mp (hp₁ n hn p hnp))
      have hnone := (List.mem_filter.mp hmm).2
      rw [hmid, hp'] at hnone
      exact absurd hnone (by simp)
    · rw [← hqid]
      exact h₂ q hq p hqp m' hm'mem hmid

-- ============================================================
-- `root_shape`: the mirror of `Parents.NotRoot`
-- ============================================================

/-- A node at step 0 *is* a root. The other half of `ChainSound.root_shape`. -/
def RootAtZero (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, n.id.id.step = 0 → n.id.parent_id = none

theorem RootAtZero_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : RootAtZero g) :
    RootAtZero g' := by
  intro n' hn' hz
  obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived n' hn'
  rw [hid] at hz ⊢
  exact h n hn hz

theorem RootAtZero_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (hmok : MachineOk g) (h : RootAtZero g) :
    RootAtZero (addNode g d title) := by
  intro n' hn' hz
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    rw [← hEq, upMap_id] at hz ⊢
    exact h n hn hz
  · rcases List.mem_singleton.mp hmem with rfl
    show g.map_parent = none
    refine hmok.2.1 ?_
    have : d.step = 0 := hz
    rw [← hd]; exact this

theorem RootAtZero_join (g₁ g₂ : GPathM) (h₁ : RootAtZero g₁) (h₂ : RootAtZero g₂) :
    RootAtZero (join g₁ g₂) := by
  intro n' hn' hz
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    have hni : n'.id = n.id := by
      rw [← hEq]; cases g₂.node? n.id with | some q => rfl | none => rfl
    rw [hni] at hz ⊢
    exact h₁ n hn hz
  · exact h₂ n' (List.mem_filter.mp hmem).1 hz

theorem RootAtZero_initSeed (d : NodeId) (title : String) :
    RootAtZero (GPathM.initSeed d title) := by
  intro n hn _
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  rfl

-- ============================================================
-- Both, over the machine
-- ============================================================

variable (reqOf : NodeId → List NodeId)

theorem SMP_reachable (g : GPathM) (h : Reachable reqOf g) : SMP g := by
  induction h with
  | seed d title _ _ => exact SMP_initSeed d title
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    refine SMP_up _ d title (by rw [hpr.step_eq]; exact hstep) ?_ ?_
      (SMP_filterAll g (reqOf d) ih)
    · exact Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hr)
    · exact (Parents.Shape_of_pruned_pn hpr
        (Parents.PN_filterAll g (reqOf d) (Parents.Shape_reachable reqOf g hr).pn)
        (Parents.Shape_reachable reqOf g hr)).pbelow
  | join g₁ g₂ _ hr₁ hr₂ ih₁ ih₂ =>
    exact SMP_join g₁ g₂ (Parents.Shape_reachable reqOf g₁ hr₁).pn
      (Parents.Shape_reachable reqOf g₂ hr₂).pn ih₁ ih₂

theorem SMP_reachable_filterAll (g : GPathM) (reqs : List NodeId)
    (h : Reachable reqOf g) : SMP (filterAll g reqs) :=
  SMP_filterAll g reqs (SMP_reachable reqOf g h)

theorem RootAtZero_reachable (g : GPathM) (h : Reachable reqOf g) : RootAtZero g := by
  induction h with
  | seed d title _ _ => exact RootAtZero_initSeed d title
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    show RootAtZero (up (filterAll g (reqOf d)) d title)
    simp only [GPathM.up]
    split
    · exact RootAtZero_addNode _ d title (by rw [hpr.step_eq]; exact hstep)
        (MachineOk_of_pruned hpr (Certifies.MachineOk_reachable reqOf g hr))
        (RootAtZero_of_pruned hpr ih)
    · exact RootAtZero_of_pruned hpr ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact RootAtZero_join g₁ g₂ ih₁ ih₂

theorem RootAtZero_reachable_filterAll (g : GPathM) (reqs : List NodeId)
    (h : Reachable reqOf g) : RootAtZero (filterAll g reqs) :=
  RootAtZero_of_pruned (pruned_filterAll g reqs) (RootAtZero_reachable reqOf g h)

-- ============================================================
-- The two `ChainSound` fields
-- ============================================================

/-- **`son_link`.** `IsChain` gives the parent link; `SMP` turns it round. -/
theorem son_link_of_SMP (h : GPathM) (hsmp : SMP h) (sel : Int → PathNodeId)
    (hchain : IsChain h sel) :
    ∀ k, 0 ≤ k → k + 1 < h.current_step → sel (k + 1) ∈ sonsOf h (sel k) := by
  intro k hlo hhi
  have hlink := hchain.2 k hlo hhi
  cases hn : h.node? (sel (k + 1)) with
  | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
  | some n =>
    rw [hn] at hlink
    obtain ⟨hsome, _⟩ := hchain.1 k hlo (by omega)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
    have hnid : n.id = sel (k + 1) := node?_id_eq h _ n hn
    have hmid : m.id = sel k := node?_id_eq h _ m hm
    simp only [sonsOf, hm]
    rw [← hnid]
    exact hsmp n (List.mem_of_find?_eq_some hn) (sel k) hlink m
      (List.mem_of_find?_eq_some hm) hmid

/-- **`root_shape`.** `RootAtZero` below, `Parents.NotRoot` above. -/
theorem root_shape_of (h : GPathM) (hrz : RootAtZero h) (hnr : Parents.NotRoot h)
    (sel : Int → PathNodeId) (hchain : IsChain h sel) (hpos : 0 < h.current_step) :
    (sel 0).parent_id = none ∧
      ∀ k, 0 < k → k < h.current_step → (sel k).parent_id ≠ none := by
  constructor
  · obtain ⟨hsome, hstep⟩ := hchain.1 0 (Int.le_refl _) hpos
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    have hnid : n.id = sel 0 := node?_id_eq h _ n hn
    rw [← hnid]
    exact hrz n (List.mem_of_find?_eq_some hn) (by rw [hnid]; exact hstep)
  · intro k hk0 hk
    obtain ⟨hsome, hstep⟩ := hchain.1 k (by omega) hk
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    have hnid : n.id = sel k := node?_id_eq h _ n hn
    rw [← hnid]
    exact hnr n (List.mem_of_find?_eq_some hn) (by rw [hnid, hstep]; exact hk0)

-- ============================================================
-- `self_owned`: why it is not like the other two
-- ============================================================

/-!
`SMP` and `RootAtZero` went through because both are preserved by every
operation *unconditionally*: they talk about `parents`, `sons` and `id`, and
the review passes never touch those except by removing a node together with
its links.

`Ownership.SelfOwned` is different. It talks about `owners`, which the review
passes prune, and the pruning is exactly where it can fail:

* under `cleanInvalid`, `n.owners` is intersected with `gowners`, and `n.id`
  survives that only if `n.id ∈ gowners` — i.e. only given
  `Ownership.NodesAreGowners`, which the campaign supports (0 violations over
  259,187 nodes) but which is not proved;
* under `reviewNode`, `n.owners` is intersected with the union over `n`'s
  neighbours' owners, and `n.id` survives only if **some neighbour owns `n`**.

That second condition is `ParentOwns` below — and `ParentOwns` is in turn
preserved only given `SelfOwned` (a parent keeps `n` in its owners because the
union over *its* neighbours contains `n`, which needs `n` to own itself). The
two are **mutually recursive**, so neither can be proved alone: they need a
simultaneous induction over the machine, carrying `NodesAreGowners` as well.

That is a genuinely bigger piece of work than the other two — **and it turned
out not to be necessary**. `SelfOwn.lean` closes `self_owned` by a different
route: `OOS`, the invariant that a node's owners at its *own* step contain
nothing but itself. `OOS` only ever shrinks, so no preservation argument has to
fight the coherence pass, and self-ownership then follows from `isValidNode` at
the fixpoint rather than being carried as an invariant. `ParentOwns` below is
kept as the record of the route that does not work.
-/

/-- A parent owns its child. Mutually recursive with `Ownership.SelfOwned`
under the coherence pass — and, as `SelfOwn.lean` shows, not needed: kept as
the record of the route that does not work. -/
def ParentOwns (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ p ∈ n.parents, ∀ m ∈ h.nodes, m.id = p → n.id ∈ m.owners

/-- `SelfOwned` survives the operations that do not prune owners. -/
theorem SelfOwned_filterRequire (g : GPathM) (req : NodeId)
    (h : Ownership.SelfOwned g) : Ownership.SelfOwned (filterRequire g req) := h

/-- info: 'AbsSat.GraphPath.Model.Sons.SMP_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SMP_reachable

/-- info: 'AbsSat.GraphPath.Model.Sons.son_link_of_SMP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms son_link_of_SMP

/-- info: 'AbsSat.GraphPath.Model.Sons.root_shape_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms root_shape_of

end AbsSat.GraphPath.Model.Sons
