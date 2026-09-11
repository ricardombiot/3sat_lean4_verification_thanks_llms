-- lean_project/AbsSat/GraphPath/Model/TriReview.lean
import AbsSat.GraphPath.Model.Fabric

/-!
# The triangle pass: path consistency for the owner tables

v66's case 17 held eighteen owner entries that no solution explains — nodes
with `x0 = 0` owning nodes with `x2 = 1`, in a state where every solution has
`x5 = 0` and clause 1, `x5 ∨ ¬x2 ∨ x0`, forbids that pair. The pair had been
compatible through `x5 = 1`; pinning `x5 = 0` removed the clause-1 rows that
carried it. Each node kept *some* owner at step 14, but **not a common one**.
The review never looks at a pair: it checks each node's coverage and the union
of its neighbours' tables, one node at a time.

`triClean` looks at pairs: it drops `q` from `owners(p)` — and `p` from
`owners(q)` — when some step has no node owned by both. That is path
consistency (PC) on the owner tables.

It loses no solution: a sound chain through `p` and `q` puts its own node at
every step inside both tables (`ChainSound_triClean`).
-/

namespace AbsSat.GraphPath.Model.TriReview

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- Do `p`'s table and `q`'s node's table share an entry at every step? -/
def commonAtAll (g : GPathM) (pown : List PathNodeId) (q : PathNodeId) : Bool :=
  match g.node? q with
  | none => true
  | some qn =>
    (intRange 0 (g.current_step - 1)).all (fun k =>
      pown.any (fun w => w.id.step == k && qn.owners.contains w))

/-- One triangle sweep, computed against the tables as they stand. -/
def triMap (g : GPathM) (n : PNodeM) : PNodeM :=
  { n with owners := n.owners.filter (fun q => commonAtAll g n.owners q) }

def triClean (g : GPathM) : GPathM :=
  { g with nodes := g.nodes.map (triMap g) }

theorem triMap_id (g : GPathM) (n : PNodeM) : (triMap g n).id = n.id := rfl
theorem triMap_parents (g : GPathM) (n : PNodeM) : (triMap g n).parents = n.parents := rfl
theorem triMap_sons (g : GPathM) (n : PNodeM) : (triMap g n).sons = n.sons := rfl

theorem triClean_node? (g : GPathM) (p : PathNodeId) :
    (triClean g).node? p = (g.node? p).map (triMap g) :=
  SymReview.node?_of_map g _ _ (triMap_id g) rfl p

/-- **The triangle pass loses no solution.** Every entry a sound chain uses —
`sel j` in `sel i`'s table — has, at every step `k`, the chain's own node
`sel k` owned by both ends. -/
theorem ChainSound_triClean (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (triClean g) sel := by
  have hnode : ∀ pid n, g.node? pid = some n → (triClean g).node? pid = some (triMap g n) := by
    intro pid n hn; rw [triClean_node?, hn]; rfl
  -- chain entries survive the filter
  have hkeep : ∀ i j, 0 ≤ i → i < g.current_step → 0 ≤ j → j < g.current_step →
      ∀ n, g.node? (sel i) = some n → sel j ∈ (triMap g n).owners := by
    intro i j hi hi' hj hj' n hn
    refine List.mem_filter.mpr ⟨Fabric.chain_owns g sel h i j hi hi' hj hj' n hn, ?_⟩
    unfold commonAtAll
    obtain ⟨hs, _⟩ := h.chain.1.1 j hj hj'
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    rw [hm]
    simp only
    refine List.all_eq_true.mpr ?_
    intro k hk
    obtain ⟨hk0, hk1⟩ := PickInduction.intRange_bounds hk
    have hk1' : k < g.current_step := by omega
    refine List.any_eq_true.mpr ⟨sel k, Fabric.chain_owns g sel h i k hi hi' hk0 hk1' n hn, ?_⟩
    refine (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr (h.chain.1.1 k hk0 hk1').2, ?_⟩
    exact List.elem_eq_true_of_mem (Fabric.chain_owns g sel h j k hj hj' hk0 hk1' m hm)
  obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, ?_, hgow⟩, ?_, ?_, hroot⟩
  · intro k hlo hhi
    obtain ⟨hsome, hs⟩ := hchain.1 k hlo hhi
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨by rw [hnode _ n hn]; rfl, hs⟩
  · intro k hlo hhi
    have hlink := hchain.2 k hlo hhi
    cases hn : g.node? (sel (k + 1)) with
    | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
    | some n =>
      rw [hn] at hlink
      rw [hnode _ n hn]
      simpa [triMap_parents] using hlink
  · intro i j hi hj hi' hj' hne
    have hmem := howned i j hi hj hi' hj' hne
    simp only [ownersAt, List.mem_filter, ownersOf] at hmem ⊢
    obtain ⟨_, hs⟩ := hmem
    refine ⟨?_, hs⟩
    obtain ⟨hsj, _⟩ := hchain.1 j hj hj'
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsj
    rw [hnode _ n hn]
    exact hkeep j i hj hj' hi hi' n hn
  · intro k hlo hhi
    simp only [ownersOf]
    obtain ⟨hsk, _⟩ := hchain.1 k hlo hhi
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsk
    rw [hnode _ n hn]
    exact hkeep k k hlo hhi hlo hhi n hn
  · intro k hlo hhi
    have hs := hson k hlo hhi
    simp only [sonsOf] at hs ⊢
    cases hn : g.node? (sel k) with
    | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hn] at hs
      rw [hnode _ n hn]
      simpa [triMap_sons] using hs

/-- info: 'AbsSat.GraphPath.Model.TriReview.ChainSound_triClean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_triClean

-- ============================================================
-- The review with the triangle pass
-- ============================================================

/-- Review to the fixpoint, then the triangle sweep, and again, until neither
changes anything. -/
def reviewTriFuel : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    let g₁ := review g
    if isValid g₁ then
      let g₂ := triClean g₁
      if measure g₂ < measure g₁ then reviewTriFuel fuel g₂ else g₁
    else g₁

def reviewTri (g : GPathM) : GPathM := reviewTriFuel (measure g + 1) g

def filterAllTri (g : GPathM) (reqs : List NodeId) : GPathM :=
  reviewTri (reqs.foldl filterRequire g)

def upFilteringTri (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String) : GPathM :=
  up (filterAllTri g reqs) d title

theorem ChainSound_reviewTriFuel :
    ∀ (fuel : Nat) (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      ChainSound (reviewTriFuel fuel g) sel := by
  intro fuel
  induction fuel with
  | zero => intro g sel h; exact h
  | succ f ih =>
    intro g sel h
    have h₁ := ChainSound_review g sel h
    simp only [reviewTriFuel]
    split
    · split
      · exact ih _ sel (ChainSound_triClean _ sel h₁)
      · exact h₁
    · exact h₁

/-- **The review with the triangle pass loses no solution.** -/
theorem ChainSound_reviewTri (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (reviewTri g) sel :=
  ChainSound_reviewTriFuel _ g sel h

/-- info: 'AbsSat.GraphPath.Model.TriReview.ChainSound_reviewTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_reviewTri

end AbsSat.GraphPath.Model.TriReview
