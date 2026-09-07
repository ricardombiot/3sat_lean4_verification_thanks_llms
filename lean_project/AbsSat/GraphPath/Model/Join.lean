-- lean_project/AbsSat/GraphPath/Model/Join.lean
import AbsSat.GraphPath.Model.Filter
import AbsSat.GraphPath.Model.L6

/-!
Bridge lemma **L4** (`formal_bridge_owners_runpure.md` §5): join respects the
denotation.

    under okJoin:  denot (join g₁ g₂) = denot g₁ ∪ denot g₂

**What is proved here: the ⊇ direction**, `denot_join_union`. Join only adds
nodes, parent links and owners, and `g₁`'s nodes keep their position in the
node list, so `node?` — the lookup both the machine and the denotation use —
still finds them. A chain of either side therefore stays a chain of the join.

The vehicle is `Grown`, the growth counterpart of `Pruned`. It is stated
directly over `node?` rather than over list membership, which is what lets it
transfer `IsChain` and `PairwiseOwned` *forwards with no id-uniqueness
hypothesis* — unlike the backwards transfer in `Filter.lean`, which needs
`NodupIds` precisely because pruning can delete the first node carrying an id
and leave `node?` pointing elsewhere. Growth cannot do that: `join_node?_left`
shows the merged node sits at the same index.

**What is not proved: the ⊆ direction**, and deliberately. A co-owned chain of
the joined graph may mix edges from both branches through shared nodes, and
the bridge document's own recommendation (§5-L4) is *not* to state L4 as exact
per-gpath equality but in the relaxed form — soundness with respect to
`ChoicesValid` plus completeness of the union — because that is all the bridge
needs and it avoids fighting benign mixtures. The relaxed form's content lives
on the `run_pure` side (E2), which this module does not reach.

**Bonus, and the reason this file also imports `L6`:** the same `Grown`
machinery closes L6's join case, `Supported_join`. Two of L6's three
constructors are now done (seed in `L6.lean`, join here); the `up` case is the
whole remaining difficulty.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

/-- The growth counterpart of `Pruned`: `g'` was obtained from `g` by
operations that only *add*. Stated directly over `node?` — the lookup the
machine and the denotation both use — so it transfers `IsChain` and
`PairwiseOwned` forwards without any id-uniqueness hypothesis. -/
structure Grown (g g' : GPathM) : Prop where
  step_eq : g'.current_step = g.current_step
  node?_grown : ∀ pid n, g.node? pid = some n →
    ∃ n', g'.node? pid = some n' ∧ (∀ q ∈ n.owners, q ∈ n'.owners)
      ∧ (∀ p ∈ n.parents, p ∈ n'.parents)

namespace Grown

protected theorem refl (g : GPathM) : Grown g g where
  step_eq := rfl
  node?_grown _ n hn := ⟨n, hn, fun _ hq => hq, fun _ hp => hp⟩

protected theorem trans {g₁ g₂ g₃ : GPathM} (h₁₂ : Grown g₁ g₂) (h₂₃ : Grown g₂ g₃) :
    Grown g₁ g₃ where
  step_eq := h₂₃.step_eq.trans h₁₂.step_eq
  node?_grown pid n hn := by
    obtain ⟨n₂, h₂, ho₂, hp₂⟩ := h₁₂.node?_grown pid n hn
    obtain ⟨n₃, h₃, ho₃, hp₃⟩ := h₂₃.node?_grown pid n₂ h₂
    exact ⟨n₃, h₃, fun q hq => ho₃ q (ho₂ q hq), fun p hp => hp₃ p (hp₂ p hp)⟩

end Grown

-- ============================================================
-- The denotation transfers forwards across growth
-- ============================================================

theorem IsChain_of_grown {g g' : GPathM} (hgr : Grown g g')
    (sel : Int → PathNodeId) (h : IsChain g sel) : IsChain g' sel := by
  constructor
  · intro k hlo hhi
    obtain ⟨hsome, hstep⟩ := h.1 k hlo (by rw [← hgr.step_eq]; exact hhi)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨n', hn', _, _⟩ := hgr.node?_grown _ _ hn
    exact ⟨by rw [hn']; rfl, hstep⟩
  · intro k hlo hhi
    have hlink := h.2 k hlo (by rw [← hgr.step_eq]; exact hhi)
    cases hn : g.node? (sel (k + 1)) with
    | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
    | some n =>
      obtain ⟨n', hn', _, hpar⟩ := hgr.node?_grown _ _ hn
      rw [hn] at hlink
      rw [hn']
      exact hpar _ hlink

theorem PairwiseOwned_of_grown {g g' : GPathM} (hgr : Grown g g')
    (sel : Int → PathNodeId) (h : PairwiseOwned g sel) : PairwiseOwned g' sel := by
  intro i j hi hj hi' hj' hne
  have hmem := h i j hi hj (by rw [← hgr.step_eq]; exact hi') (by rw [← hgr.step_eq]; exact hj') hne
  simp only [ownersAt, List.mem_filter] at hmem ⊢
  obtain ⟨hown, hstep⟩ := hmem
  refine ⟨?_, hstep⟩
  simp only [ownersOf] at hown ⊢
  cases hn : g.node? (sel j) with
  | none => rw [hn] at hown; exact absurd hown List.not_mem_nil
  | some n =>
    rw [hn] at hown
    obtain ⟨n', hn', hsub, _⟩ := hgr.node?_grown _ _ hn
    rw [hn']
    exact hsub _ hown

theorem denot_of_grown {g g' : GPathM} (hgr : Grown g g') (p : List NodeId)
    (h : denot g p) : denot g' p := by
  obtain ⟨sel, hchain, howned, hpath⟩ := h
  refine ⟨sel, IsChain_of_grown hgr sel hchain, PairwiseOwned_of_grown hgr sel howned, ?_⟩
  rw [hpath]
  simp only [pathOf, hgr.step_eq]

-- ============================================================
-- `join` only grows
-- ============================================================

theorem find?_congr {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha := h a List.mem_cons_self
    simp only [List.find?_cons, ha]
    cases hq : q a
    · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rfl

/-- The merge transformer applied to `g₁`'s node list. -/
private def joinMap (g₂ : GPathM) (n : PNodeM) : PNodeM :=
  match g₂.node? n.id with | some m => mergeNode n m | none => n

private theorem joinMap_id (g₂ : GPathM) (n : PNodeM) : (joinMap g₂ n).id = n.id := by
  simp only [joinMap]; cases g₂.node? n.id <;> rfl

private theorem join_nodes (g₁ g₂ : GPathM) :
    (join g₁ g₂).nodes =
      (g₁.nodes.map (joinMap g₂)) ++ g₂.nodes.filter (fun m => (g₁.node? m.id).isNone) := rfl

theorem join_node?_left (g₁ g₂ : GPathM) (pid : PathNodeId) (n : PNodeM)
    (hn : g₁.node? pid = some n) : (join g₁ g₂).node? pid = some (joinMap g₂ n) := by
  have hp : (fun x : PNodeM => (joinMap g₂ x).id == pid) = (fun x : PNodeM => x.id == pid) := by
    funext x; rw [joinMap_id]
  simp only [node?, join_nodes, List.find?_append, List.find?_map, Function.comp_def, hp]
  rw [show g₁.nodes.find? (fun x : PNodeM => x.id == pid) = some n from hn]
  rfl

theorem join_node?_right (g₁ g₂ : GPathM) (pid : PathNodeId) (m : PNodeM)
    (hm : g₂.node? pid = some m) :
    ∃ n', (join g₁ g₂).node? pid = some n' ∧ (∀ q ∈ m.owners, q ∈ n'.owners)
      ∧ (∀ p ∈ m.parents, p ∈ n'.parents) := by
  cases hn : g₁.node? pid with
  | some n =>
    have hnid : n.id = pid := node?_id_eq g₁ pid n hn
    refine ⟨joinMap g₂ n, join_node?_left g₁ g₂ pid n hn, ?_, ?_⟩
    · simp only [joinMap, hnid, hm, mergeNode]
      intro q hq
      cases hc : n.owners.contains q with
      | true => exact List.mem_append_left _ (List.mem_of_elem_eq_true hc)
      | false => exact List.mem_append_right _ (List.mem_filter.mpr ⟨hq, by simp only [hc]; rfl⟩)
    · simp only [joinMap, hnid, hm, mergeNode]
      intro q hq
      cases hc : n.parents.contains q with
      | true => exact List.mem_append_left _ (List.mem_of_elem_eq_true hc)
      | false => exact List.mem_append_right _ (List.mem_filter.mpr ⟨hq, by simp only [hc]; rfl⟩)
  | none =>
    refine ⟨m, ?_, fun _ hq => hq, fun _ hp => hp⟩
    have hnone : g₁.nodes.find? (fun x : PNodeM => x.id == pid) = none := hn
    have hp : (fun x : PNodeM => (joinMap g₂ x).id == pid) = (fun x : PNodeM => x.id == pid) := by
      funext x; rw [joinMap_id]
    simp only [node?, join_nodes, List.find?_append, List.find?_map, Function.comp_def, hp,
      hnone, Option.map_none, Option.none_or, List.find?_filter]
    rw [find?_congr _ _ (fun x : PNodeM => x.id == pid) ?_]
    · exact hm
    · intro a _
      cases hb : a.id == pid with
      | false => simp
      | true =>
        have hid : a.id = pid := eq_of_beq hb
        simp only [hid]
        simp
        intro x hx hxid
        exact (List.find?_eq_none.mp hnone x hx) (by simp [hxid])

theorem node?_isSome_of_mem (g : GPathM) (n : PNodeM) (hn : n ∈ g.nodes) :
    (g.node? n.id).isSome := by
  simp only [node?]
  cases h : g.nodes.find? (fun m => m.id == n.id) with
  | some _ => rfl
  | none => exact absurd (beq_self_eq_true n.id) (List.find?_eq_none.mp h n hn)

theorem grown_join_left (g₁ g₂ : GPathM) : Grown g₁ (join g₁ g₂) where
  step_eq := rfl
  node?_grown pid n hn := by
    refine ⟨joinMap g₂ n, join_node?_left g₁ g₂ pid n hn, ?_, ?_⟩ <;>
      · simp only [joinMap]
        cases g₂.node? n.id
        · exact fun _ hq => hq
        · exact fun _ hq => List.mem_append_left _ hq

theorem grown_join_right (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) :
    Grown g₂ (join g₁ g₂) where
  step_eq := by
    have : (g₁.current_step == g₂.current_step) = true := by
      simp only [okJoin, Bool.and_eq_true] at hok
      exact hok.1.1.1
    show g₁.current_step = g₂.current_step
    exact eq_of_beq this
  node?_grown := join_node?_right g₁ g₂

-- ============================================================
-- L4, the monotone direction
-- ============================================================

/-- **L4 ⊇**: `denot g₁ ∪ denot g₂ ⊆ denot (join g₁ g₂)`. Join only adds nodes,
parent links and owners, and `g₁`'s nodes keep their position, so `node?` still
finds them — a chain of either side stays a chain of the join. -/
theorem denot_join_of_left (g₁ g₂ : GPathM) (p : List NodeId) (h : denot g₁ p) :
    denot (join g₁ g₂) p :=
  denot_of_grown (grown_join_left g₁ g₂) p h

theorem denot_join_of_right (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (p : List NodeId) (h : denot g₂ p) : denot (join g₁ g₂) p :=
  denot_of_grown (grown_join_right g₁ g₂ hok) p h

theorem denot_join_union (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (p : List NodeId) (h : denot g₁ p ∨ denot g₂ p) : denot (join g₁ g₂) p :=
  h.elim (denot_join_of_left g₁ g₂ p) (denot_join_of_right g₁ g₂ hok p)

-- ============================================================
-- L6, join case
-- ============================================================

theorem join_node?_source (g₁ g₂ : GPathM) (pid : PathNodeId) (n : PNodeM)
    (h : (join g₁ g₂).node? pid = some n) :
    (g₁.node? pid).isSome ∨ (g₂.node? pid).isSome := by
  have hmem : n ∈ (join g₁ g₂).nodes := List.mem_of_find?_eq_some h
  have hid : n.id = pid := node?_id_eq _ pid n h
  rw [join_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · obtain ⟨n₁, hn₁, hEq⟩ := List.mem_map.mp hl
    refine Or.inl ?_
    have : n₁.id = pid := by rw [← hid, ← hEq, joinMap_id]
    rw [← this]
    exact node?_isSome_of_mem g₁ n₁ hn₁
  · refine Or.inr ?_
    have hm := (List.mem_filter.mp hr).1
    rw [← hid]
    exact node?_isSome_of_mem g₂ n hm

/-- **L6, join case.** Join preserves total support: a chain witnessing a node
on either side stays a chain of the join. -/
theorem Supported_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : Supported g₁) (h₂ : Supported g₂) : Supported (join g₁ g₂) := by
  intro pid n hn
  rcases join_node?_source g₁ g₂ pid n hn with hs | hs
  · obtain ⟨n₁, hn₁⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨sel, hchain, howned, hsel⟩ := h₁ pid n₁ hn₁
    exact ⟨sel, IsChain_of_grown (grown_join_left g₁ g₂) sel hchain,
      PairwiseOwned_of_grown (grown_join_left g₁ g₂) sel howned, hsel⟩
  · obtain ⟨n₂, hn₂⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨sel, hchain, howned, hsel⟩ := h₂ pid n₂ hn₂
    exact ⟨sel, IsChain_of_grown (grown_join_right g₁ g₂ hok) sel hchain,
      PairwiseOwned_of_grown (grown_join_right g₁ g₂ hok) sel howned, hsel⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.denot_join_union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denot_join_union

/-- info: 'AbsSat.GraphPath.Model.Supported_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Supported_join

end AbsSat.GraphPath.Model
