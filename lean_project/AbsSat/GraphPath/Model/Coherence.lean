-- lean_project/AbsSat/GraphPath/Model/Coherence.lean
import AbsSat.GraphPath.Model.CleanInvalid

/-!
**Obligations 2 and 3 of `Review.lean`, discharged**, and with them the
statement the whole bridge was blocked on:

    SupportedS_review : SupportedS g → SupportedS (review g)

`reviewPass = reviewSons ∘ reviewParents ∘ cleanInvalid`. `CleanInvalid.lean`
did the first stage; this module does the other two, then composes them and
runs the fuel induction to get `review`.

## The coherence argument

`cleanInvalid` prunes a node's owners against `gowners`, and the chain
survives because every chain node is a global owner. The coherence passes
prune against `unionOwnersOf g (nb d)` — the union of the owners of the node's
*neighbours* — so a different argument is needed, and it is
`chain_mem_unionOwnersOf`:

> if any chain node `sel w` is among the neighbours, then *every* chain node
> lies in the neighbours' owners union — by pairwise ownership when `i ≠ w`,
> and by self-ownership when `i = w`.

So each pass only needs one chain node among the neighbours, and the chain
supplies it: on the top-down pass the predecessor `sel (k-1)` is a parent (the
`IsChain` link), on the bottom-up pass the successor `sel (k+1)` is a son
(`ChainSound`'s `son_link`). This is where `ChainSound`'s two link fields earn
their place, and where self-ownership does: without it the `i = w` case fails,
and the chain would prune itself.

The step ranges do the rest. `reviewParents` walks `1 .. cs-1`, which is
exactly where a predecessor exists; `reviewSons` walks `1 .. cs-2`, exactly
where a successor exists. Neither pass ever visits a node it could not
justify.

## What this does not yet give

Feeding `SupportedS_review` into the `up` case needs `addNode` in the same
currency. That is `AddNode.lean` (`ChainSound_addNode`), which also carries
the structural fact `root_shape` needs (`MachineOk`).
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

private def unionStep (g : GPathM) (acc : List PathNodeId) (pid : PathNodeId) : List PathNodeId :=
  match g.node? pid with
  | some p => acc ++ p.owners
  | none => acc

private theorem unionOwnersOf_eq (g : GPathM) (ids : List PathNodeId) :
    unionOwnersOf g ids = ids.foldl (unionStep g) [] := rfl

private theorem mem_unionFold_acc (g : GPathM) (ids : List PathNodeId) :
    ∀ (acc : List PathNodeId) (q : PathNodeId), q ∈ acc → q ∈ ids.foldl (unionStep g) acc := by
  induction ids with
  | nil => intro acc q hq; exact hq
  | cons id rest ih =>
    intro acc q hq
    simp only [List.foldl_cons]
    refine ih _ q ?_
    simp only [unionStep]
    cases g.node? id
    · exact hq
    · exact List.mem_append_left _ hq

private theorem mem_unionFold (g : GPathM) (ids : List PathNodeId) :
    ∀ (acc : List PathNodeId) (pid : PathNodeId) (p : PNodeM) (q : PathNodeId),
      pid ∈ ids → g.node? pid = some p → q ∈ p.owners →
      q ∈ ids.foldl (unionStep g) acc := by
  induction ids with
  | nil => intro _ _ _ _ hpid; exact absurd hpid List.not_mem_nil
  | cons id rest ih =>
    intro acc pid p q hpid hp hq
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hpid with rfl | hrest
    · refine mem_unionFold_acc g rest _ q ?_
      simp only [unionStep, hp]
      exact List.mem_append_right _ hq
    · exact ih _ pid p q hrest hp hq

/-- An owner of any *existing* neighbour is in the neighbours' union. -/
theorem mem_unionOwnersOf (g : GPathM) (ids : List PathNodeId) (pid : PathNodeId)
    (p : PNodeM) (q : PathNodeId) (hpid : pid ∈ ids) (hp : g.node? pid = some p)
    (hq : q ∈ p.owners) : q ∈ unionOwnersOf g ids :=
  mem_unionFold g ids [] pid p q hpid hp hq

/-- **The coherence analogue of the `gowners` argument.** If some chain node
`sel w` is among the neighbours, then *every* chain node is in the
neighbours' owners union — by pairwise ownership when `i ≠ w`, and by
self-ownership when `i = w`. So the coherence intersection cannot cut the
chain either. -/
theorem chain_mem_unionOwnersOf (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (nbList : List PathNodeId) (w : Int)
    (hw_lo : 0 ≤ w) (hw_hi : w < g.current_step) (hw : sel w ∈ nbList)
    (i : Int) (hi : 0 ≤ i) (hi' : i < g.current_step) :
    sel i ∈ unionOwnersOf g nbList := by
  obtain ⟨⟨hchain, howned, _⟩, hself, _, _⟩ := h
  obtain ⟨hsome, _⟩ := hchain.1 w hw_lo hw_hi
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  refine mem_unionOwnersOf g nbList (sel w) p (sel i) hw hp ?_
  rcases int_eq_or_ne i w with hiw | hiw
  · subst hiw
    have hs := hself i hi hi'
    simp only [ownersOf, hp] at hs
    exact hs
  · have hmem := howned i w hi hw_lo hi' hw_hi hiw
    simp only [ownersAt, List.mem_filter, ownersOf, hp] at hmem
    exact hmem.1

-- ============================================================
-- One coherence step preserves a sound chain
-- ============================================================

/-- **A coherence review of one node preserves a sound chain**, provided the
node — when it is on the chain — has some chain node among its neighbours.
That witness is what carries the chain into the neighbours' owners union, so
the intersection cannot cut it. -/
theorem ChainSound_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hwit : ∀ j, 0 ≤ j → j < g.current_step → sel j = id → ∀ d, g.node? id = some d →
      ∃ w, 0 ≤ w ∧ w < g.current_step ∧ sel w ∈ nb d) :
    ChainSound (reviewNode g nb id) sel := by
  cases hid : g.node? id with
  | none => simpa [reviewNode, hid] using h
  | some d =>
    have hd_id : d.id = id := node?_id_eq g id d hid
    have hB : ∀ j, 0 ≤ j → j < g.current_step → sel j = id →
        ∀ i, 0 ≤ i → i < g.current_step → sel i ∈ unionOwnersOf g (nb d) := by
      intro j hj hj' hsel i hi hi'
      obtain ⟨w, hw, hw', hwm⟩ := hwit j hj hj' hsel d hid
      exact chain_mem_unionOwnersOf g sel h (nb d) w hw hw' hwm i hi hi'
    have hup : ChainSound (updateAt g id (uniMap (unionOwnersOf g (nb d)))) sel :=
      ChainSound_updateAt_gen g id _ sel h hB
    have hshape : reviewNode g nb id =
        if isValidNode g d then
          (if isValidNode (updateAt g id (uniMap (unionOwnersOf g (nb d))))
                (uniMap (unionOwnersOf g (nb d)) d)
            then updateAt g id (uniMap (unionOwnersOf g (nb d)))
            else removeNode (updateAt g id (uniMap (unionOwnersOf g (nb d)))) id)
        else removeNode g id := by
      simp only [reviewNode, hid]
      rfl
    rw [hshape]
    split
    · split
      · exact hup
      · next hbad =>
        refine ChainSound_removeNode _ id sel hup ?_
        intro k hlo hhi hk
        apply hbad
        have hnode : (updateAt g id (uniMap (unionOwnersOf g (nb d)))).node? (sel k)
            = some (uniMap (unionOwnersOf g (nb d)) d) := by
          rw [hk, updateAt_node? g id _ (uniMap_id _) id d hid]
          rw [show (d.id == id) = true from by rw [hd_id]; exact beq_self_eq_true id]
        exact isValidNode_of_chain _ sel hup k _ hnode hlo hhi
    · next hbad =>
      refine ChainSound_removeNode g id sel h ?_
      intro k hlo hhi hk
      apply hbad
      have hnode : g.node? (sel k) = some d := by rw [hk]; exact hid
      exact isValidNode_of_chain g sel h k d hnode hlo hhi

-- ============================================================
-- The fold over a line, and the walk over steps
-- ============================================================

theorem reviewNode_current_step (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) : (reviewNode g nb id).current_step = g.current_step := by
  simp only [reviewNode]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem ChainSound_foldl_reviewNode (nb : PNodeM → List PathNodeId) (k cs : Int)
    (hwit : ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel → g.current_step = cs →
      ∀ d, g.node? (sel k) = some d → ∃ w, 0 ≤ w ∧ w < g.current_step ∧ sel w ∈ nb d)
    (ids : List PathNodeId) (hids : ∀ id ∈ ids, id.id.step = k) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel → g.current_step = cs →
      ChainSound (ids.foldl (fun g id => reviewNode g nb id) g) sel := by
  induction ids with
  | nil => intro g sel h _; simpa using h
  | cons id rest ih =>
    intro g sel h hcs
    simp only [List.foldl_cons]
    have hstep : id.id.step = k := hids id List.mem_cons_self
    have hone : ChainSound (reviewNode g nb id) sel := by
      refine ChainSound_reviewNode g nb id sel h ?_
      intro j hj hj' hsel d hd
      have hjk : j = k := by
        have := (h.chain.1.1 j hj hj').2
        rw [hsel] at this
        omega
      subst hjk
      exact hwit g sel h hcs d (by rw [hsel]; exact hd)
    exact ih (fun x hx => hids x (List.mem_cons_of_mem _ hx)) _ sel hone
      (by rw [reviewNode_current_step]; exact hcs)

theorem line_ids_step (g : GPathM) (k : Int) :
    ∀ id ∈ ((g.line k).map (·.id)), id.id.step = k := by
  intro id hid
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hid
  have := (List.mem_filter.mp hn).2
  rw [← hEq]
  exact eq_of_beq this

-- ============================================================
-- The two coherence passes
-- ============================================================

theorem ChainSound_reviewLine_parents (g : GPathM) (k : Int) (hk : 1 ≤ k)
    (hk2 : k < g.current_step)
    (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (reviewLine g (·.parents) k) sel := by
  refine ChainSound_foldl_reviewNode _ k g.current_step ?_ _ (line_ids_step g k) g sel h rfl
  intro g' sel' h' hcs d hd
  refine ⟨k - 1, by omega, by omega, ?_⟩
  have hrange : k - 1 + 1 < g'.current_step := by omega
  have hlink := h'.chain.1.2 (k - 1) (by omega) hrange
  rw [show k - 1 + 1 = k from by omega, hd] at hlink
  simpa using hlink

theorem ChainSound_reviewLine_sons (g : GPathM) (k : Int) (hk : 0 ≤ k)
    (hk2 : k + 1 < g.current_step)
    (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (reviewLine g (·.sons) k) sel := by
  refine ChainSound_foldl_reviewNode _ k g.current_step ?_ _ (line_ids_step g k) g sel h rfl
  intro g' sel' h' hcs d hd
  refine ⟨k + 1, by omega, by rw [hcs]; exact hk2, ?_⟩
  have hs := h'.son_link k hk (by rw [hcs]; exact hk2)
  simp only [sonsOf, hd] at hs
  exact hs

private theorem foldl_reviewNode_current_step (nb : PNodeM → List PathNodeId)
    (ids : List PathNodeId) :
    ∀ g : GPathM, (ids.foldl (fun g id => reviewNode g nb id) g).current_step
      = g.current_step := by
  induction ids with
  | nil => intro g; rfl
  | cons id rest ih =>
    intro g; simp only [List.foldl_cons]; rw [ih, reviewNode_current_step]

theorem reviewLine_current_step (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int) :
    (reviewLine g nb k).current_step = g.current_step :=
  foldl_reviewNode_current_step nb _ g

theorem ChainSound_reviewSteps_parents (ks : List Int) (cs : Int)
    (hks : ∀ k ∈ ks, 1 ≤ k ∧ k < cs) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel → g.current_step = cs →
      ChainSound (reviewSteps g (·.parents) ks) sel := by
  induction ks with
  | nil => intro g sel h _; simpa [reviewSteps] using h
  | cons k ks ih =>
    intro g sel h hcs
    simp only [reviewSteps]
    split
    · obtain ⟨hk1, hk2⟩ := hks k List.mem_cons_self
      exact ih (fun x hx => hks x (List.mem_cons_of_mem _ hx)) _ sel
        (ChainSound_reviewLine_parents g k hk1 (by rw [hcs]; exact hk2) sel h)
        (by rw [reviewLine_current_step]; exact hcs)
    · exact h

theorem ChainSound_reviewSteps_sons (ks : List Int) (cs : Int)
    (hks : ∀ k ∈ ks, 0 ≤ k ∧ k + 1 < cs) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel → g.current_step = cs →
      ChainSound (reviewSteps g (·.sons) ks) sel := by
  induction ks with
  | nil => intro g sel h _; simpa [reviewSteps] using h
  | cons k ks ih =>
    intro g sel h hcs
    simp only [reviewSteps]
    split
    · obtain ⟨hk1, hk2⟩ := hks k List.mem_cons_self
      exact ih (fun x hx => hks x (List.mem_cons_of_mem _ hx)) _ sel
        (ChainSound_reviewLine_sons g k hk1 (by rw [hcs]; exact hk2) sel h)
        (by rw [reviewLine_current_step]; exact hcs)
    · exact h

theorem ChainSound_reviewParents (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (reviewParents g) sel :=
  ChainSound_reviewSteps_parents _ g.current_step
    (fun k hk => ⟨mem_intRange_lower hk, by have := mem_intRange_upper hk; omega⟩) g sel h rfl

theorem ChainSound_reviewSons (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (reviewSons g) sel :=
  ChainSound_reviewSteps_sons _ g.current_step
    (fun k hk => by
      have hk' := List.mem_reverse.mp hk
      exact ⟨by have := mem_intRange_lower hk'; omega,
             by have := mem_intRange_upper hk'; omega⟩) g sel h rfl

-- ============================================================
-- A whole review pass, and the review loop
-- ============================================================

/-- **A review pass preserves a sound chain.** All three stages: the global
`cleanInvalid` (`CleanInvalid.lean`) and the two coherence passes. -/
theorem ChainSound_reviewPass (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (reviewPass g) sel := by
  simp only [reviewPass]
  exact ChainSound_reviewSons _ sel
    (ChainSound_reviewParents _ sel (ChainSound_cleanInvalid g sel h))

private theorem ChainSound_reviewFuel :
    ∀ (fuel : Nat) (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      ChainSound (reviewFuel fuel g) sel := by
  intro fuel
  induction fuel with
  | zero => intro g sel h; simpa [reviewFuel] using h
  | succ f ih =>
    intro g sel h
    simp only [reviewFuel]
    split
    · split
      · exact ih _ sel (ChainSound_reviewPass g sel h)
      · exact ChainSound_reviewPass g sel h
    · exact h

/-- **`review` preserves a sound chain.** -/
theorem ChainSound_review (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (review g) sel :=
  ChainSound_reviewFuel _ g sel h

-- ============================================================
-- Total support, in the `ChainSound` form
-- ============================================================

/-- `SupportedG` with `ChainSound` witnesses. -/
def SupportedS (g : GPathM) : Prop :=
  ∀ pid n, g.node? pid = some n → ∃ sel, ChainSound g sel ∧ sel pid.id.step = pid

/-- **The statement `Review.lean` was left blocked on.** `review` preserves
total support. -/
theorem SupportedS_review (g : GPathM) (h : SupportedS g) : SupportedS (review g) := by
  intro pid n hn
  have hmem : n ∈ (review g).nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq _ pid n hn
  obtain ⟨n₀, hn₀, hid₀, _, _⟩ := (pruned_review g).nodes_derived n hmem
  have hsome : (g.node? n₀.id).isSome := node?_isSome_of_mem g n₀ hn₀
  rw [← hid₀, hid] at hsome
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨sel, hsel, htop⟩ := h pid m hm
  exact ⟨sel, ChainSound_review g sel hsel, htop⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ChainSound_reviewPass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_reviewPass

/-- info: 'AbsSat.GraphPath.Model.SupportedS_review' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SupportedS_review

end AbsSat.GraphPath.Model
