-- lean_project/AbsSat/GraphPath/Model/GownersNodes.lean
import AbsSat.GraphPath.Model.Certifies

/-!
**`GownersAreNodes` — every global owner is a node — proved of every state the
machine builds.**

v24 refuted `ArcImpliesChain` with `degenerate`: a graph holding a global owner
at every step and no nodes at all. It is valid, it is a `review` fixpoint and
it is arc consistent for free, yet it has no chain. What it violates is exactly
this invariant, and what supplies the invariant is `Reachable` — silently.
Here it stops being silent.

**A correction to v24 while we are here.** That document said `filterRequire`
breaks this invariant. It does not: `filterRequire` *shrinks* `gowners` and
leaves the nodes alone, so `gowners ⊆ nodes` survives it untouched. What
`filterRequire` breaks is the **converse** — nodes whose id is no longer a
global owner — and `review` is what clears those away. The two directions were
swapped.

Which makes the invariant far more tractable than v24 suggested: every machine
operation either leaves `gowners` alone, shrinks it, or adds an owner together
with its node. The proof is that observation, once per operation, in the same
shape as `Pruned.lean`.
-/

namespace AbsSat.GraphPath.Model.GownersNodes

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Certifies (GownersAreNodes)

-- ============================================================
-- The workable form of `(g.node? q).isSome`
-- ============================================================

/-- Some node carries the id `q`. Unlike `node?`, this is monotone under
everything that preserves ids, which is what makes the proofs uniform. -/
def HasNode (g : GPathM) (q : PathNodeId) : Prop := ∃ n ∈ g.nodes, n.id = q

private theorem find?_isSome_of_mem (q : PathNodeId) (n : PNodeM) :
    ∀ (l : List PNodeM), n ∈ l → n.id = q →
      (l.find? (fun m => m.id == q)).isSome = true := by
  intro l
  induction l with
  | nil => intro hn _; exact absurd hn List.not_mem_nil
  | cons a as ih =>
    intro hn hid
    cases hp : (a.id == q) with
    | true => rw [List.find?_cons_of_pos (p := fun m : PNodeM => m.id == q) hp]; rfl
    | false =>
      rw [List.find?_cons_of_neg (p := fun m : PNodeM => m.id == q)
        (by rw [hp]; exact Bool.false_ne_true)]
      rcases List.mem_cons.mp hn with rfl | hmem
      · exact absurd (beq_iff_eq.mpr hid) (by rw [hp]; exact Bool.false_ne_true)
      · exact ih hmem hid

theorem hasNode_iff (g : GPathM) (q : PathNodeId) :
    HasNode g q ↔ (g.node? q).isSome = true := by
  constructor
  · intro ⟨n, hn, hid⟩; exact find?_isSome_of_mem q n g.nodes hn hid
  · intro h
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
    exact ⟨n, List.mem_of_find?_eq_some hn, node?_id_eq g q n hn⟩

/-- `GownersAreNodes`, in the form the proofs use. -/
def GN (g : GPathM) : Prop := ∀ q ∈ g.gowners, HasNode g q

theorem GownersAreNodes_of_GN {g : GPathM} (h : GN g) : GownersAreNodes g :=
  fun q hq => (hasNode_iff g q).mp (h q hq)

theorem GN_foldl {β : Type} (f : GPathM → β → GPathM) (hf : ∀ g b, GN g → GN (f g b)) :
    ∀ (l : List β) (g : GPathM), GN g → GN (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons b bs ih =>
    intro g h
    simp only [List.foldl_cons]
    exact ih _ (hf g b h)

-- ============================================================
-- Operations that keep or shrink `gowners`
-- ============================================================

theorem GN_updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, (f n).id = n.id) (h : GN g) : GN (updateAt g id f) := by
  intro q hq
  obtain ⟨n, hn, hid⟩ := h q hq
  refine ⟨(match n.id == id with | true => f n | false => n), List.mem_map_of_mem hn, ?_⟩
  cases n.id == id with
  | true => exact (hf n).trans hid
  | false => exact hid

theorem GN_removeNode (g : GPathM) (id : PathNodeId) (h : GN g) :
    GN (removeNode g id) := by
  intro q hq
  have hq' := List.mem_filter.mp hq
  have hne : q ≠ id := bne_iff_ne.mp hq'.2
  obtain ⟨n, hn, hid⟩ := h q hq'.1
  have hmem : n ∈ g.nodes.filter (fun m => m.id != id) :=
    List.mem_filter.mpr ⟨hn, bne_iff_ne.mpr (by rw [hid]; exact hne)⟩
  exact ⟨_, List.mem_map_of_mem hmem, hid⟩

/-- `filterRequire` shrinks `gowners` and leaves the nodes alone. -/
theorem GN_filterRequire (g : GPathM) (req : NodeId) (h : GN g) :
    GN (filterRequire g req) :=
  fun q hq => h q (List.mem_filter.mp hq).1

-- ============================================================
-- The review chain, in `Pruned.lean`'s shape
-- ============================================================

/-- The unlink keeps every node, with its id — so `gowners ⊆ nodes` survives. -/
theorem GN_unlinkIncompatible (g : GPathM) (id : PathNodeId) (h : GN g) :
    GN (unlinkIncompatible g id) := by
  intro q hq
  rw [unlinkIncompatible_gowners] at hq
  obtain ⟨m, hm, hmid⟩ := h q hq
  show ∃ x ∈ (unlinkIncompatible g id).nodes, x.id = q
  unfold GPathM.unlinkIncompatible
  split
  · exact ⟨m, hm, hmid⟩
  · next n _ =>
    exact ⟨unlinkMap n id m, List.mem_map_of_mem hm, by rw [unlinkMap_id]; exact hmid⟩

theorem GN_cleanInvalidGo (ids : List PathNodeId) :
    ∀ g : GPathM, GN g → GN (cleanInvalidGo g ids) := by
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGo]
    split
    · exact ih g h
    · next d _ =>
      have h₁ : GN (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners g.gowners })) :=
        GN_updateAt g id _ (fun _ => rfl) h
      have h₂ := GN_unlinkIncompatible _ id h₁
      split
      · exact ih _ h₂
      · exact ih _ (GN_removeNode _ id h₂)

theorem GN_cleanInvalid (g : GPathM) (h : GN g) : GN (cleanInvalid g) :=
  GN_cleanInvalidGo _ g h

theorem GN_reviewNode (nb : PNodeM → List PathNodeId) (id : PathNodeId) (g : GPathM)
    (h : GN g) : GN (reviewNode g nb id) := by
  simp only [reviewNode]
  split
  · exact h
  · next d _ =>
    split
    · have h₁ : GN (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) :=
        GN_updateAt g id _ (fun _ => rfl) h
      have h₂ := GN_unlinkIncompatible _ id h₁
      split
      · exact h₂
      · exact GN_removeNode _ id h₂
    · exact GN_removeNode g id h

theorem GN_reviewLine (nb : PNodeM → List PathNodeId) (k : Int) (g : GPathM)
    (h : GN g) : GN (reviewLine g nb k) :=
  GN_foldl (fun g id => reviewNode g nb id) (fun g id => GN_reviewNode nb id g) _ g h

theorem GN_reviewSteps (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, GN g → GN (reviewSteps g nb ks) := by
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    simp only [reviewSteps]
    split
    · exact ih _ (GN_reviewLine nb k g h)
    · exact h

theorem GN_reviewPass (g : GPathM) (h : GN g) : GN (reviewPass g) := by
  simp only [reviewPass]
  exact GN_reviewSteps _ _ _ (GN_reviewSteps _ _ _ (GN_cleanInvalid g h))

theorem GN_reviewFuel : ∀ (fuel : Nat) (g : GPathM), GN g → GN (reviewFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewFuel]
    split
    · split
      · exact ih _ (GN_reviewPass g h)
      · exact GN_reviewPass g h
    · exact h

theorem GN_review (g : GPathM) (h : GN g) : GN (review g) := GN_reviewFuel _ g h

theorem GN_filterAll (g : GPathM) (reqs : List NodeId) (h : GN g) :
    GN (filterAll g reqs) :=
  GN_review _ (GN_foldl filterRequire (fun g r => GN_filterRequire g r) reqs g h)

-- ============================================================
-- Growth: `addNode` and `join`
-- ============================================================

theorem GN_addNode (g : GPathM) (d : NodeId) (title : String) (h : GN g) :
    GN (addNode g d title) := by
  intro q hq
  rw [addNode_gowners, List.mem_append] at hq
  show ∃ n ∈ (addNode g d title).nodes, n.id = q
  rw [addNode_nodes]
  rcases hq with hq | hq
  · obtain ⟨n, hn, hid⟩ := h q hq
    exact ⟨upMap g d n, List.mem_append_left _ (List.mem_map_of_mem hn),
      (upMap_id g d n).trans hid⟩
  · rcases List.mem_singleton.mp hq with rfl
    exact ⟨addOwner (newPid g d) (upNode g d title),
      List.mem_append_right _ List.mem_cons_self, rfl⟩

theorem GN_up (g : GPathM) (d : NodeId) (title : String) (h : GN g) :
    GN (up g d title) := by
  simp only [GPathM.up]
  split
  · exact GN_addNode g d title h
  · exact h

theorem GN_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (h : GN g) : GN (upFiltering g reqs d title) :=
  GN_up _ d title (GN_filterAll g reqs h)

theorem join_nodes (g₁ g₂ : GPathM) :
    (join g₁ g₂).nodes =
      g₁.nodes.map (fun n => match g₂.node? n.id with
                             | some m => mergeNode n m
                             | none => n)
        ++ g₂.nodes.filter (fun m => (g₁.node? m.id).isNone) := rfl

theorem join_gowners (g₁ g₂ : GPathM) :
    (join g₁ g₂).gowners =
      g₁.gowners ++ g₂.gowners.filter (fun q => !g₁.gowners.contains q) := rfl

theorem GN_join (g₁ g₂ : GPathM) (h₁ : GN g₁) (h₂ : GN g₂) : GN (join g₁ g₂) := by
  intro q hq
  rw [join_gowners, List.mem_append] at hq
  show ∃ n ∈ (join g₁ g₂).nodes, n.id = q
  rw [join_nodes]
  rcases hq with hq | hq
  · obtain ⟨n, hn, hid⟩ := h₁ q hq
    refine ⟨(match g₂.node? n.id with | some m => mergeNode n m | none => n),
      List.mem_append_left _ (List.mem_map_of_mem hn), ?_⟩
    cases g₂.node? n.id with
    | some m => exact hid
    | none => exact hid
  · obtain ⟨n, hn, hid⟩ := h₂ q (List.mem_filter.mp hq).1
    cases hg : g₁.node? n.id with
    | some m =>
      have hmid : m.id = n.id := node?_id_eq g₁ n.id m hg
      refine ⟨(match g₂.node? m.id with | some m' => mergeNode m m' | none => m),
        List.mem_append_left _ (List.mem_map_of_mem (List.mem_of_find?_eq_some hg)), ?_⟩
      cases g₂.node? m.id with
      | some m' => exact hmid.trans hid
      | none => exact hmid.trans hid
    | none =>
      exact ⟨n, List.mem_append_right _ (List.mem_filter.mpr ⟨hn, by rw [hg]; rfl⟩), hid⟩

-- ============================================================
-- The invariant, over the machine
-- ============================================================

theorem GN_initSeed (d : NodeId) (title : String) : GN (GPathM.initSeed d title) := by
  intro q hq
  rw [Certifies.initSeed_gowners] at hq
  rcases List.mem_singleton.mp hq with rfl
  refine ⟨PNodeM.mk { id := d, parent_id := none } title [] []
    [{ id := d, parent_id := none }], ?_, rfl⟩
  rw [initSeed_nodes]
  exact List.mem_cons_self ..

variable (reqOf : NodeId → List NodeId)

theorem GN_reachable (g : GPathM) (h : Reachable reqOf g) : GN g := by
  induction h with
  | seed d title _ _ => exact GN_initSeed d title
  | up g d title _ _ _ _ ih => exact GN_upFiltering g (reqOf d) d title ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact GN_join g₁ g₂ ih₁ ih₂

/-- **Every state the machine builds has `gowners ⊆ nodes`.** The property
`degenerate` violates, now available wherever `Reachable` is. -/
theorem GownersAreNodes_reachable (g : GPathM) (h : Reachable reqOf g) :
    GownersAreNodes g :=
  GownersAreNodes_of_GN (GN_reachable reqOf g h)

/-- And on the filtered intermediates, which is where the obligation lives. -/
theorem GownersAreNodes_filterAll (g : GPathM) (reqs : List NodeId)
    (h : Reachable reqOf g) : GownersAreNodes (filterAll g reqs) :=
  GownersAreNodes_of_GN (GN_filterAll g reqs (GN_reachable reqOf g h))

/-- **A node at every step.** Validity says every step keeps a global owner;
this invariant turns that into a node — which is what `degenerate` lacked. -/
theorem node_at_every_step (g : GPathM) (reqs : List NodeId) (h : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true) (k : Int) (hlo : 0 ≤ k)
    (hhi : k < (filterAll g reqs).current_step) :
    ∃ n ∈ (filterAll g reqs).nodes, n.id.id.step = k := by
  obtain ⟨q, hq, hstep⟩ := PickInduction.gowner_of_isValid _ hv k hlo hhi
  obtain ⟨n, hn, hid⟩ := GN_filterAll g reqs (GN_reachable reqOf g h) q hq
  exact ⟨n, hn, by rw [hid]; exact hstep⟩

/-- info: 'AbsSat.GraphPath.Model.GownersNodes.GownersAreNodes_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GownersAreNodes_reachable

/-- info: 'AbsSat.GraphPath.Model.GownersNodes.node_at_every_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms node_at_every_step

end AbsSat.GraphPath.Model.GownersNodes
