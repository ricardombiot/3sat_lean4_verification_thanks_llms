-- lean_project/AbsSat/GraphPath/Model/PathExists.lean
import AbsSat.GraphPath.Model.Parents
import AbsSat.GraphPath.Model.Extendable

/-!
**`IsChain` is proved.** The path half of `FilteredChain` closes.

v26 split the obligation into "are there candidates" (proved) and "can they be
chosen together" (open). The second splits again: a chain is a **path**
(parent-linked, one node per step) that is also **pairwise co-owned**. This
module builds the path.

The construction is a descent. Take any node at the top step — v25's
`node_at_every_step` says there is one. At a valid `review` fixpoint every node
passes `isValidNode`, and a node above step 0 is not a root
(`Parents.NotRoot`), so `isValidNode` forces it to have parents. A parent is a
surviving node (`Parents.PN`) sitting exactly one step below
(`Parents.PBelow`). Walk down to step 0.

That is `IsChain`, in full. What it is *not* is `PairwiseOwned`: nothing here
says the nodes on the path own one another. That is the remaining half, and it
is where the Helly property sits.
-/

namespace AbsSat.GraphPath.Model.PathExists

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Extendable (PartialChain upd upd_self upd_other isChain_of_partial)
open AbsSat.GraphPath.Model.Parents (Shape Shape_filterAll)

-- ============================================================
-- A non-root node has parents
-- ============================================================

theorem parents_ne_nil_of_isValidNode (g : GPathM) (n : PNodeM)
    (h : isValidNode g n = true) (hroot : n.id.parent_id ≠ none) : n.parents ≠ [] := by
  simp only [isValidNode] at h
  split at h
  · next hc =>
    cases hpp : n.id.parent_id with
    | none => exact absurd hpp hroot
    | some _ => rw [hpp] at hc; exact (Bool.false_ne_true hc).elim
  · split at h
    · intro hnil
      have hp := ((Bool.and_eq_true _ _).mp h).2
      rw [hnil] at hp
      exact absurd hp (by decide)
    · intro hnil
      have hp := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2
      rw [hnil] at hp
      exact absurd hp (by decide)

-- ============================================================
-- One step down
-- ============================================================

theorem step_down (h : GPathM) (hv : isValid (review h) = true) (hs : Shape (review h))
    (sel : Int → PathNodeId) (lo hi : Int) (hpos : 0 < lo) (hlohi : lo ≤ hi)
    (hpc : PartialChain (review h) sel lo hi) :
    ∃ c, PartialChain (review h) (upd sel (lo - 1) c) (lo - 1) hi := by
  obtain ⟨hsome, hstep⟩ := hpc.1 lo (Int.le_refl _) hlohi
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hnid : n.id = sel lo := node?_id_eq _ _ n hn
  have hmem : n ∈ (review h).nodes := List.mem_of_find?_eq_some hn
  have hnstep : 0 < n.id.id.step := by rw [hnid, hstep]; exact hpos
  have hroot := hs.notroot n hmem hnstep
  have hpar := parents_ne_nil_of_isValidNode _ n (review_node_valid h hv _ n hn) hroot
  obtain ⟨c, rest, hcons⟩ : ∃ c rest, n.parents = c :: rest := by
    cases hl : n.parents with
    | nil => exact absurd hl hpar
    | cons a as => exact ⟨a, as, rfl⟩
  have hcmem : c ∈ n.parents := by rw [hcons]; exact List.mem_cons_self ..
  obtain ⟨m, hm, hmid⟩ := hs.pn n hmem c hcmem
  have hcstep : c.id.step = lo - 1 := by
    have := hs.pbelow n hmem c hcmem
    rw [this, hnid, hstep]
  refine ⟨c, ⟨?_, ?_⟩⟩
  · intro i hi1 hi2
    if hic : i = lo - 1 then
      subst hic
      rw [upd_self]
      exact ⟨(GownersNodes.hasNode_iff _ c).mp ⟨m, hm, hmid⟩, hcstep⟩
    else
      rw [upd_other sel (lo - 1) c hic]
      exact hpc.1 i (by omega) hi2
  · intro i hi1 hi2
    if hic : i = lo - 1 then
      subst hic
      rw [upd_self, upd_other sel (lo - 1) c (by omega)]
      have hlo' : lo - 1 + 1 = lo := by omega
      rw [hlo', hn]
      exact hcmem
    else
      rw [upd_other sel (lo - 1) c hic, upd_other sel (lo - 1) c (by omega)]
      exact hpc.2 i (by omega) hi2

-- ============================================================
-- Descend to step 0
-- ============================================================

theorem descend (h : GPathM) (hv : isValid (review h) = true) (hs : Shape (review h)) :
    ∀ (m : Nat) (sel : Int → PathNodeId) (lo hi : Int), lo.toNat ≤ m → 0 ≤ lo → lo ≤ hi →
      PartialChain (review h) sel lo hi →
      ∃ sel', PartialChain (review h) sel' 0 hi := by
  intro m
  induction m with
  | zero =>
    intro sel lo hi hm hlo hlohi hpc
    have : lo = 0 := by omega
    subst this
    exact ⟨sel, hpc⟩
  | succ m ih =>
    intro sel lo hi hm hlo hlohi hpc
    if hpos : 0 < lo then
      obtain ⟨c, hpc'⟩ := step_down h hv hs sel lo hi hpos hlohi hpc
      exact ih _ (lo - 1) hi (by omega) (by omega) (by omega) hpc'
    else
      have : lo = 0 := by omega
      subst this
      exact ⟨sel, hpc⟩

-- ============================================================
-- The path
-- ============================================================

variable (reqOf : NodeId → List NodeId)

/-- **`IsChain` holds of every valid state the machine builds.** A path from
step 0 to the top exists — parent-linked, one real node per step. -/
theorem exists_isChain (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true)
    (hpos : 0 < (filterAll g reqs).current_step) :
    ∃ sel, IsChain (filterAll g reqs) sel := by
  have hs : Shape (filterAll g reqs) := Shape_filterAll reqOf g reqs hreach
  obtain ⟨t, ht, htstep⟩ :=
    GownersNodes.node_at_every_step reqOf g reqs hreach hv ((filterAll g reqs).current_step - 1)
      (by omega) (by omega)
  have hsome : ((filterAll g reqs).node? t.id).isSome = true :=
    (GownersNodes.hasNode_iff _ t.id).mp ⟨t, ht, rfl⟩
  have hseed : PartialChain (filterAll g reqs) (fun _ => t.id)
      ((filterAll g reqs).current_step - 1) ((filterAll g reqs).current_step - 1) := by
    refine ⟨?_, ?_⟩
    · intro i hi1 hi2
      have : i = (filterAll g reqs).current_step - 1 := by omega
      subst this
      exact ⟨hsome, htstep⟩
    · intro i _ hi2; omega
  obtain ⟨sel, hpc⟩ := descend _ hv hs
    ((filterAll g reqs).current_step - 1).toNat (fun _ => t.id)
    ((filterAll g reqs).current_step - 1) ((filterAll g reqs).current_step - 1)
    (Nat.le_refl _) (by omega) (Int.le_refl _) hseed
  exact ⟨sel, isChain_of_partial _ sel hpc⟩

/-- info: 'AbsSat.GraphPath.Model.PathExists.exists_isChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_isChain

end AbsSat.GraphPath.Model.PathExists
