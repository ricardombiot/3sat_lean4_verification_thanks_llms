-- lean_project/AbsSat/GraphPath/Model/RemovalClosure.lean
import AbsSat.GraphPath.Model.NoDeadEnd
import AbsSat.GraphPath.Model.PathExists

/-!
# The removal closure of the pins

`P = reqs.foldl filterRequire g` is a state with its pins placed and its review not yet run.
`Unsupported P` is the closure the review's removals follow:

* **no support** — a node with some step `k` at which every owner that is still a global owner is
  itself unsupported (in particular: none left at all);
* **no parent** — a node above step 0 all of whose parents that are nodes are unsupported.

Proved here:

* `unsupported_off_chain` — no node of a `ChainSound` chain of `P` is unsupported; with
  `pinned_chain_off_unsupported`, no node of a full chain of `g` through the pins is.
* `unsupported_removed` — **the review removes every unsupported node**: after a valid
  `filterAll`, an unsupported node is no longer a node.

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210): in every valid filtered state the
nodes the review removes are **exactly** the unsupported ones (41,501 = 41,501), and every partial
chain from the top step with no completion through the pins has its wrong pick unsupported
(9,240 of 9,240). What is not proved is the converse of `unsupported_removed` together with the
statement that makes `PinnedCompletion` follow: a pick that is not unsupported, under a partial
chain that has a completion through the pins, keeps one.
-/

namespace AbsSat.GraphPath.Model.RemovalClosure

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- The removal closure of a pinned state. -/
inductive Unsupported (P : GPathM) : PathNodeId → Prop where
  | noSupport (x : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (k : Int)
      (h0 : 0 ≤ k) (hk : k < P.current_step)
      (h : ∀ q ∈ ownersAt n.owners k, q ∈ P.gowners → Unsupported P q) : Unsupported P x
  | noParent (x : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (hstep : 0 < x.id.step)
      (h : ∀ p ∈ n.parents, (P.node? p).isSome = true → Unsupported P p) : Unsupported P x

theorem foldl_filterRequire_nodes (reqs : List NodeId) :
    ∀ g : GPathM, (reqs.foldl filterRequire g).nodes = g.nodes := by
  induction reqs with
  | nil => intro g; rfl
  | cons r rs ih => intro g; exact ih (filterRequire g r)

theorem foldl_filterRequire_step (reqs : List NodeId) :
    ∀ g : GPathM, (reqs.foldl filterRequire g).current_step = g.current_step := by
  induction reqs with
  | nil => intro g; rfl
  | cons r rs ih => intro g; exact ih (filterRequire g r)

-- ============================================================
-- Chains never touch the closure
-- ============================================================

/-- **No node of a sound chain is unsupported.** -/
theorem unsupported_off_chain {P : GPathM} {sel : Int → PathNodeId} (hs : ChainSound P sel)
    {x : PathNodeId} (hx : Unsupported P x) :
    ∀ i, 0 ≤ i → i < P.current_step → sel i ≠ x := by
  induction hx with
  | noSupport x n hn k h0 hk hprem ih =>
    intro i hi0 hi heq
    obtain ⟨⟨hnode, _⟩, howned, hgow⟩ := hs.chain
    have hmem : sel k ∈ ownersAt n.owners k := by
      rcases int_eq_or_ne k i with hki | hki
      · subst hki
        have hso := hs.self_owned k h0 hk
        rw [heq] at hso
        simp only [ownersOf, hn] at hso
        refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr (hnode k h0 hk).2⟩
        rw [heq]
        exact hso
      · have ho := howned k i h0 hi0 hk hi hki
        rw [heq] at ho
        simp only [ownersOf, hn] at ho
        exact ho
    exact ih (sel k) hmem (hgow k h0 hk) k h0 hk rfl
  | noParent x n hn hstep hprem ih =>
    intro i hi0 hi heq
    obtain ⟨⟨hnode, hlink⟩, _, _⟩ := hs.chain
    have hstepi : x.id.step = i := by rw [← heq]; exact (hnode i hi0 hi).2
    have hpar := hlink (i - 1) (by omega) (by omega)
    have hi' : i - 1 + 1 = i := by omega
    rw [hi', heq, hn] at hpar
    have hsome := (hnode (i - 1) (by omega) (by omega)).1
    exact ih (sel (i - 1)) hpar hsome (i - 1) (by omega) (by omega) rfl

/-- **No node of a full chain of `g` through the pins is unsupported.** -/
theorem pinned_chain_off_unsupported (g : GPathM) (reqs : List NodeId) (sel : Int → PathNodeId)
    (hs : ChainSound g sel)
    (hpins : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req)
    {x : PathNodeId} (hx : Unsupported (reqs.foldl filterRequire g) x) :
    ∀ i, 0 ≤ i → i < g.current_step → sel i ≠ x := by
  have hP := ChainSound_foldl_filterRequire reqs g sel hs hpins
  intro i h0 hi
  exact unsupported_off_chain hP hx i h0 (by rw [foldl_filterRequire_step]; exact hi)

-- ============================================================
-- The review removes the closure
-- ============================================================

/-- **The review removes every unsupported node.** -/
theorem unsupported_removed (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true) {x : PathNodeId}
    (hx : Unsupported (reqs.foldl filterRequire g) x) : (filterAll g reqs).node? x = none := by
  have hpr : Pruned (reqs.foldl filterRequire g) (filterAll g reqs) := pruned_review _
  have hs := hpr.step_eq
  have hnd : NodupIds (reqs.foldl filterRequire g) := by
    unfold NodupIds
    rw [foldl_filterRequire_nodes]
    exact Reader.NodupIds_reachable reqOf g hr
  have hgn := GownersNodes.GN_filterAll g reqs (GownersNodes.GN_reachable reqOf g hr)
  have hshape := Parents.Shape_filterAll reqOf g reqs hr
  have hlift : ∀ y d, (filterAll g reqs).node? y = some d →
      ∃ n, (reqs.foldl filterRequire g).node? y = some n ∧ (∀ q ∈ d.owners, q ∈ n.owners) ∧
        (∀ p ∈ d.parents, p ∈ n.parents) := by
    intro y d hd
    obtain ⟨n, hn, hid, ho, hp⟩ := hpr.nodes_derived d (List.mem_of_find?_eq_some hd)
    have hdid : d.id = y := node?_id_eq _ y d hd
    refine ⟨n, ?_, ho, hp⟩
    rw [← hdid, hid]
    exact node?_of_mem hnd n hn
  induction hx with
  | noSupport x n hn k h0 hk hprem ih =>
    cases hd : (filterAll g reqs).node? x with
    | none => rfl
    | some d =>
      exfalso
      obtain ⟨n', hn', ho, _⟩ := hlift x d hd
      have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
      have hval := review_node_valid (reqs.foldl filterRequire g) hv x d hd
      have hk' : k < (filterAll g reqs).current_step := by rw [hs]; exact hk
      have hent := LocalContradiction.ownersOk_of_isValidNode _ d hval k h0 hk'
      simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
      obtain ⟨q, hq, hqs⟩ := hent
      have hqg : q ∈ (filterAll g reqs).gowners :=
        owners_mem_gowners _ d (review_owners_within_gowners (reqs.foldl filterRequire g) hv x d hd)
          q hq (hasStepEntry_of_isValid _ hv _ (by rw [hqs]; exact h0) (by rw [hqs]; exact hk'))
      have hqn : q ∈ ownersAt n.owners k := by
        refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hqs⟩
        rw [← hnn]
        exact ho q hq
      have hnone := ih q hqn (hpr.gowners_sub q hqg)
      obtain ⟨m, hm⟩ :=
        Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff _ q).mp (hgn q hqg))
      rw [hnone] at hm
      cases hm
  | noParent x n hn hstep hprem ih =>
    cases hd : (filterAll g reqs).node? x with
    | none => rfl
    | some d =>
      exfalso
      obtain ⟨n', hn', _, hp⟩ := hlift x d hd
      have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
      have hdmem : d ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hd
      have hdid : d.id = x := node?_id_eq _ x d hd
      have hval := review_node_valid (reqs.foldl filterRequire g) hv x d hd
      have hroot : d.id.parent_id ≠ none := hshape.notroot d hdmem (by rw [hdid]; exact hstep)
      have hne := PathExists.parents_ne_nil_of_isValidNode _ d hval hroot
      obtain ⟨p, rest, hcons⟩ : ∃ p rest, d.parents = p :: rest := by
        cases hl : d.parents with
        | nil => exact absurd hl hne
        | cons a b => exact ⟨a, b, rfl⟩
      have hpmem : p ∈ d.parents := by rw [hcons]; exact List.mem_cons_self ..
      obtain ⟨m, hm, hmid⟩ := hshape.pn d hdmem p hpmem
      have hsomeh : ((filterAll g reqs).node? p).isSome = true :=
        (GownersNodes.hasNode_iff _ p).mp ⟨m, hm, hmid⟩
      obtain ⟨m0, hm0⟩ := Option.isSome_iff_exists.mp hsomeh
      obtain ⟨np, hnp, _, _⟩ := hlift p m0 hm0
      have hsomeP : ((reqs.foldl filterRequire g).node? p).isSome = true := by rw [hnp]; rfl
      have hpn : p ∈ n.parents := by rw [← hnn]; exact hp p hpmem
      have hnone := ih p hpn hsomeP
      rw [hnone] at hm0
      cases hm0

/-- info: 'AbsSat.GraphPath.Model.RemovalClosure.unsupported_off_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unsupported_off_chain

/-- info: 'AbsSat.GraphPath.Model.RemovalClosure.pinned_chain_off_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinned_chain_off_unsupported

/-- info: 'AbsSat.GraphPath.Model.RemovalClosure.unsupported_removed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unsupported_removed

end AbsSat.GraphPath.Model.RemovalClosure
