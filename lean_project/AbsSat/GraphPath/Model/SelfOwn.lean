-- lean_project/AbsSat/GraphPath/Model/SelfOwn.lean
import AbsSat.GraphPath.Model.Sons

/-!
**`self_owned`, closed — and `ParentOwns` turns out not to be needed.**

v29 analysed `Ownership.SelfOwned` and found it mutually recursive with
`ParentOwns`: under `reviewNode` a node keeps itself in its own owners only if
some neighbour owns it, and the neighbour keeps it only if the node owns
itself. That analysis is correct about the *direct* route. It is not the only
route.

The way round is an invariant that only ever **shrinks**, so no preservation
argument has to fight the coherence pass at all:

> **`OOS`** — a node's owners at its *own* step contain nothing but itself.

`addNode` hands the new node `gowners ++ [pid]`, and every global owner at that
moment sits at a strictly lower step, so at its own step the new node's owners
are exactly `{itself}` from birth. Every later operation only removes owners.
So `OOS` holds everywhere, unconditionally.

And then self-ownership is not an invariant to preserve but a **consequence**:
at a valid `review` fixpoint every node passes `isValidNode`, which demands an
owner at *every* step below `current_step` — including the node's own. By `OOS`
that owner can only be the node itself.

    OOS + isValidNode  ⟹  SelfOwned

`ParentOwns` is never needed, and the mutual recursion never has to be entered.
-/

namespace AbsSat.GraphPath.Model.SelfOwn

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- Steps are non-negative
-- ============================================================

def SNN (h : GPathM) : Prop := ∀ n ∈ h.nodes, 0 ≤ n.id.id.step

theorem SNN_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : SNN g) : SNN g' := by
  intro n' hn'
  obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived n' hn'
  rw [hid]; exact h n hn

theorem SNN_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (hmok : MachineOk g) (h : SNN g) :
    SNN (addNode g d title) := by
  intro n' hn'
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    rw [← hEq, upMap_id]; exact h n hn
  · rcases List.mem_singleton.mp hmem with rfl
    show (0 : Int) ≤ d.step
    rw [hd]; exact hmok.1

theorem SNN_join (g₁ g₂ : GPathM) (h₁ : SNN g₁) (h₂ : SNN g₂) : SNN (join g₁ g₂) := by
  intro n' hn'
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    have hni : n'.id = n.id := by
      rw [← hEq]; cases g₂.node? n.id with | some q => rfl | none => rfl
    rw [hni]; exact h₁ n hn
  · exact h₂ n' (List.mem_filter.mp hmem).1

theorem SNN_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    SNN (GPathM.initSeed d title) := by
  intro n hn
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  show (0 : Int) ≤ d.step
  rw [hstep]
  exact Int.le_refl 0

variable (reqOf : NodeId → List NodeId)

theorem SNN_reachable (g : GPathM) (h : Reachable reqOf g) : SNN g := by
  induction h with
  | seed d title hstep _ => exact SNN_initSeed d title hstep
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    show SNN (up (filterAll g (reqOf d)) d title)
    simp only [GPathM.up]
    split
    · exact SNN_addNode _ d title (by rw [hpr.step_eq]; exact hstep)
        (MachineOk_of_pruned hpr (Certifies.MachineOk_reachable reqOf g hr))
        (SNN_of_pruned hpr ih)
    · exact SNN_of_pruned hpr ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact SNN_join g₁ g₂ ih₁ ih₂

-- ============================================================
-- A node's owners at its own step are only itself
-- ============================================================

/-- **The shrink-only invariant.** At a node's own step, its owners contain
nothing but the node. True from birth (`addNode` gives the new node the global
owners, all of which sit strictly lower) and stable because owners only ever
get filtered. -/
def OOS (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ q ∈ n.owners, q.id.step = n.id.id.step → q = n.id

theorem OOS_filterRequire (g : GPathM) (req : NodeId) (h : OOS g) :
    OOS (filterRequire g req) := h

theorem OOS_updateAt (g : GPathM) (id : PathNodeId) (b : List PathNodeId)
    (h : OOS g) :
    OOS (updateAt g id (fun n => { n with owners := intersectOwners n.owners b })) := by
  intro n' hn' q hq hstep
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  have hni : n'.id = n.id := by rw [← hEq]; cases n.id == id with | true => rfl | false => rfl
  have hsub : ∀ x ∈ n'.owners, x ∈ n.owners := by
    rw [← hEq]
    cases n.id == id with
    | true => intro x hx; exact (List.mem_filter.mp hx).1
    | false => intro x hx; exact hx
  rw [hni] at hstep ⊢
  exact h n hn q (hsub q hq) hstep

theorem OOS_removeNode (g : GPathM) (id : PathNodeId) (h : OOS g) :
    OOS (removeNode g id) := by
  intro n' hn' q hq hstep
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  have hni : n'.id = n.id := by rw [← hEq]
  have hno : n'.owners = n.owners := by rw [← hEq]
  rw [hni] at hstep ⊢
  rw [hno] at hq
  exact h n (List.mem_filter.mp hn).1 q hq hstep

theorem OOS_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : OOS g) : OOS g' := by
  intro n' hn' q hq hstep
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
  rw [hid] at hstep ⊢
  exact h n hn q (hown q hq) hstep

/-- The unlink leaves every node's owners alone. -/
theorem OOS_unlinkIncompatible (g : GPathM) (id : PathNodeId) (h : OOS g) :
    OOS (unlinkIncompatible g id) :=
  OOS_of_pruned (pruned_unlinkIncompatible g id) h

theorem OOS_cleanInvalidGo (ids : List PathNodeId) :
    ∀ g : GPathM, OOS g → OOS (cleanInvalidGo g ids) := by
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGo]
    split
    · exact ih g h
    · next d _ =>
      have h₁ := OOS_updateAt g id g.gowners h
      have h₂ := OOS_unlinkIncompatible _ id h₁
      split
      · exact ih _ h₂
      · exact ih _ (OOS_removeNode _ id h₂)

theorem OOS_cleanInvalid (g : GPathM) (h : OOS g) : OOS (cleanInvalid g) :=
  OOS_cleanInvalidGo _ g h

theorem OOS_reviewNode (nb : PNodeM → List PathNodeId) (id : PathNodeId) (g : GPathM)
    (h : OOS g) : OOS (reviewNode g nb id) := by
  simp only [reviewNode]
  split
  · exact h
  · next d _ =>
    split
    · have h₁ := OOS_updateAt g id (unionOwnersOf g (nb d)) h
      have h₂ := OOS_unlinkIncompatible _ id h₁
      split
      · exact h₂
      · exact OOS_removeNode _ id h₂
    · exact OOS_removeNode g id h

private theorem OOS_foldl {β : Type} (f : GPathM → β → GPathM)
    (hf : ∀ g b, OOS g → OOS (f g b)) :
    ∀ (l : List β) (g : GPathM), OOS g → OOS (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons b bs ih => intro g h; simp only [List.foldl_cons]; exact ih _ (hf g b h)

theorem OOS_reviewLine (nb : PNodeM → List PathNodeId) (k : Int) (g : GPathM)
    (h : OOS g) : OOS (reviewLine g nb k) :=
  OOS_foldl (fun g id => reviewNode g nb id) (fun g id => OOS_reviewNode nb id g) _ g h

theorem OOS_reviewSteps (nb : PNodeM → List PathNodeId) (ks : List Int) :
    ∀ g : GPathM, OOS g → OOS (reviewSteps g nb ks) := by
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    simp only [reviewSteps]
    split
    · exact ih _ (OOS_reviewLine nb k g h)
    · exact h

theorem OOS_reviewPass (g : GPathM) (h : OOS g) : OOS (reviewPass g) := by
  simp only [reviewPass]
  exact OOS_reviewSteps _ _ _ (OOS_reviewSteps _ _ _ (OOS_cleanInvalid g h))

theorem OOS_reviewFuel : ∀ (fuel : Nat) (g : GPathM), OOS g → OOS (reviewFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ f ih =>
    intro g h
    simp only [reviewFuel]
    split
    · split
      · exact ih _ (OOS_reviewPass g h)
      · exact OOS_reviewPass g h
    · exact h

theorem OOS_review (g : GPathM) (h : OOS g) : OOS (review g) := OOS_reviewFuel _ g h

theorem OOS_filterAll (g : GPathM) (reqs : List NodeId) (h : OOS g) :
    OOS (filterAll g reqs) :=
  OOS_review _ (OOS_foldl filterRequire (fun g r => OOS_filterRequire g r) reqs g h)

-- ============================================================
-- `addNode`, `join`, `initSeed`
-- ============================================================

theorem OOS_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hgn : GownersNodes.GN g) (h : OOS g) : OOS (addNode g d title) := by
  intro n' hn' q hq hstep
  rw [addNode_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    have hni : n'.id = n.id := by rw [← hEq]; exact upMap_id g d n
    have hno : n'.owners = n.owners ++ [newPid g d] := by rw [← hEq]; exact upMap_owners g d n
    rw [hno, List.mem_append] at hq
    rw [hni] at hstep ⊢
    rcases hq with hq | hq
    · exact h n hn q hq hstep
    · rcases List.mem_singleton.mp hq with rfl
      exfalso
      have h1 : (newPid g d).id.step = d.step := rfl
      have h2 := hbelow n hn
      rw [h1, hd] at hstep
      omega
  · rcases List.mem_singleton.mp hmem with rfl
    have hno : (addOwner (newPid g d) (upNode g d title)).owners = g.gowners ++ [newPid g d] :=
      rfl
    rw [hno, List.mem_append] at hq
    rcases hq with hq | hq
    · exfalso
      obtain ⟨m, hm, hmid⟩ := hgn q hq
      have h2 := hbelow m hm
      rw [hmid] at h2
      have h1 : (addOwner (newPid g d) (upNode g d title)).id.id.step = d.step := rfl
      rw [h1, hd] at hstep
      omega
    · exact List.mem_singleton.mp hq

theorem OOS_join (g₁ g₂ : GPathM) (h₁ : OOS g₁) (h₂ : OOS g₂) : OOS (join g₁ g₂) := by
  intro n' hn' q hq hstep
  rw [GownersNodes.join_nodes] at hn'
  rcases List.mem_append.mp hn' with hmem | hmem
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hmem
    cases hg : g₂.node? n.id with
    | none =>
      have hni : n'.id = n.id := by rw [← hEq, hg]
      have hno : n'.owners = n.owners := by rw [← hEq, hg]
      rw [hni] at hstep ⊢; rw [hno] at hq
      exact h₁ n hn q hq hstep
    | some m =>
      have hni : n'.id = n.id := by rw [← hEq, hg]; rfl
      have hno : n'.owners =
          n.owners ++ m.owners.filter (fun r => !n.owners.contains r) := by
        rw [← hEq, hg]; rfl
      have hmid : m.id = n.id := node?_id_eq g₂ n.id m hg
      rw [hno, List.mem_append] at hq
      rw [hni] at hstep ⊢
      rcases hq with hq | hq
      · exact h₁ n hn q hq hstep
      · have := h₂ m (List.mem_of_find?_eq_some hg) q (List.mem_filter.mp hq).1
          (by rw [hmid]; exact hstep)
        rw [← hmid]; exact this
  · exact h₂ n' (List.mem_filter.mp hmem).1 q hq hstep

theorem OOS_initSeed (d : NodeId) (title : String) : OOS (GPathM.initSeed d title) := by
  intro n hn q hq _
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  exact List.mem_singleton.mp hq

theorem OOS_reachable (g : GPathM) (h : Reachable reqOf g) : OOS g := by
  induction h with
  | seed d title _ _ => exact OOS_initSeed d title
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    show OOS (up (filterAll g (reqOf d)) d title)
    simp only [GPathM.up]
    split
    · exact OOS_addNode _ d title (by rw [hpr.step_eq]; exact hstep)
        (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hr))
        (GownersNodes.GN_filterAll g (reqOf d) (GownersNodes.GN_reachable reqOf g hr))
        (OOS_filterAll g (reqOf d) ih)
    · exact OOS_filterAll g (reqOf d) ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact OOS_join g₁ g₂ ih₁ ih₂

-- ============================================================
-- And therefore self-ownership
-- ============================================================

/-- **`SelfOwned`, as a consequence.** At a valid `review` fixpoint every node
passes `isValidNode`, which demands an owner at every step below
`current_step` — the node's own included. `OOS` says that owner can only be the
node itself. -/
theorem SelfOwned_of_OOS (h : GPathM) (hv : isValid (review h) = true)
    (hoos : OOS (review h)) (hsnn : SNN (review h))
    (hbelow : ∀ n ∈ (review h).nodes, n.id.id.step < (review h).current_step) :
    Ownership.SelfOwned (review h) := by
  intro pid n hn
  have hmem : n ∈ (review h).nodes := List.mem_of_find?_eq_some hn
  have hnid : n.id = pid := node?_id_eq _ pid n hn
  have hall := owners_ok_of_isValidNode _ n (review_node_valid h hv pid n hn)
  have hentry : hasStepEntry n.owners n.id.id.step = true :=
    List.all_eq_true.mp hall n.id.id.step
      (mem_intRange (hsnn n hmem) (by have := hbelow n hmem; omega))
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hentry
  have : q = n.id := hoos n hmem q hq (eq_of_beq hqs)
  rw [← hnid, ← this]
  exact hq

/-- The same, on the graphs the obligation is about. -/
theorem SelfOwned_filterAll (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true) :
    Ownership.SelfOwned (filterAll g reqs) := by
  have hpr := pruned_filterAll g reqs
  exact SelfOwned_of_OOS _ hv (OOS_filterAll g reqs (OOS_reachable reqOf g hreach))
    (SNN_of_pruned hpr (SNN_reachable reqOf g hreach))
    (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hreach))

/-- info: 'AbsSat.GraphPath.Model.SelfOwn.SelfOwned_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SelfOwned_filterAll

end AbsSat.GraphPath.Model.SelfOwn
