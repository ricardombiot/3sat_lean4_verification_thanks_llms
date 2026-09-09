-- lean_project/AbsSat/GraphPath/Model/CleanInvalid.lean
import AbsSat.GraphPath.Model.Review

/-!
**Obligation 1 of `Review.lean`, discharged**: `cleanInvalid` — the first of
the three stages of a review pass — preserves a sound chain.

`ChainSound_cleanInvalid`. The walk is a fold whose graph mutates underneath
it, so the argument is threaded one step at a time through
`cleanInvalidGo_cons` (from `Fuel.lean`) and `ChainSound_cleanStep`.

Each step does one of two things, and the chain is safe from both:

* **the node stays**, and the owners intersection could not have touched the
  chain — every chain node is a global owner (`ChainG`'s third field), and a
  global owner always survives an intersection against `gowners`
  (`mem_gowStep_owners`, on top of `Review.mem_intersectOwners_of_mem`);
* **the node is dropped**, and then it cannot have been a chain node at all:
  `Review.isValidNode_of_chain` says a sound chain node always passes
  validity, so the drop branch is unreachable for it. Removal of a non-chain
  node is then harmless — `removeNode` never touches owners, and the parent,
  son and `gowners` filters only ever discard the removed id, which the chain
  does not use.

That second point is the one worth remembering: the walk cannot cut the chain
*because* the chain protects itself — validity is exactly what the chain
supplies.

The two `node?` lemmas at the top (`updateAt_node?`, `removeNode_node?`) are
the mechanical price of `node?` being a first-match lookup: they say the
lookup follows the node through an update and through the removal of a
*different* node.

**Still open after this**: obligations 2 and 3 of `Review.lean` — the two
coherence passes (`reviewParents`, `reviewSons`) and the preservation of
`ChainSound`'s own extra fields across them. `cleanInvalid` was the first of
the three stages; the other two prune against the neighbours' owners rather
than against `gowners`, so they need the argument sketched in `Review.lean`:
pairwise ownership of `i` and `j-1`, plus self-ownership at `i = j-1`.
-/

namespace AbsSat.GraphPath.Model
open AbsSat.Utils.Alias
open GPathM

theorem updateAt_node? (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM)
    (hf : ∀ n, (f n).id = n.id) (pid : PathNodeId) (n : PNodeM) (hn : g.node? pid = some n) :
    (updateAt g id f).node? pid
      = some (match n.id == id with | true => f n | false => n) := by
  simp only [node?] at hn
  simp only [node?, updateAt, updateAtGo, List.find?_map, Function.comp_def]
  rw [find?_congr _ _ (fun x : PNodeM => x.id == pid) (by
    intro x _
    cases hb : x.id == id <;> simp [hf]), hn]
  rfl

def unlink (id : PathNodeId) (n : PNodeM) : PNodeM :=
  { n with parents := n.parents.filter (fun p => p != id),
           sons := n.sons.filter (fun s => s != id) }

theorem removeNode_nodes (g : GPathM) (id : PathNodeId) :
    (removeNode g id).nodes = (g.nodes.filter (fun n => n.id != id)).map (unlink id) := rfl

theorem removeNode_gowners (g : GPathM) (id : PathNodeId) :
    (removeNode g id).gowners = g.gowners.filter (fun q => q != id) := rfl

theorem removeNode_node? (g : GPathM) (id pid : PathNodeId) (n : PNodeM)
    (hn : g.node? pid = some n) (hne : pid ≠ id) :
    (removeNode g id).node? pid = some (unlink id n) := by
  have hp : (fun x : PNodeM => (unlink id x).id == pid) = (fun x : PNodeM => x.id == pid) := by
    funext x; rfl
  simp only [node?] at hn
  simp only [node?, removeNode_nodes, List.find?_map, Function.comp_def, hp, List.find?_filter]
  rw [find?_congr _ _ (fun x : PNodeM => x.id == pid) ?_]
  · rw [hn]; rfl
  · intro a _
    cases hb : a.id == pid with
    | false => simp
    | true =>
      have hid : a.id = pid := eq_of_beq hb
      have : (a.id != id) = true := by
        rw [hid]
        simp only [bne_iff_ne]
        exact hne
      simp [this]

-- ============================================================
-- The global-owners intersection preserves a sound chain
-- ============================================================

/-- Intersect a node's owners against an arbitrary list. Both `cleanInvalid`
(against `gowners`) and the coherence passes (against the neighbours' owners
union) are instances. -/
def uniMap (B : List PathNodeId) (n : PNodeM) : PNodeM :=
  { n with owners := intersectOwners n.owners B }

theorem uniMap_id (B : List PathNodeId) (n : PNodeM) : (uniMap B n).id = n.id := rfl

abbrev gowMap (g : GPathM) : PNodeM → PNodeM := uniMap g.gowners

theorem gowMap_id (g : GPathM) (n : PNodeM) : (gowMap g n).id = n.id := rfl

/-- The step transformer, seen pointwise: only the node carrying `id` moves. -/
def uniStep (B : List PathNodeId) (id : PathNodeId) (n : PNodeM) : PNodeM :=
  match n.id == id with | true => uniMap B n | false => n

theorem uniStep_parents (B : List PathNodeId) (id : PathNodeId) (n : PNodeM) :
    (uniStep B id n).parents = n.parents := by
  simp only [uniStep]; cases n.id == id <;> rfl

theorem uniStep_sons (B : List PathNodeId) (id : PathNodeId) (n : PNodeM) :
    (uniStep B id n).sons = n.sons := by
  simp only [uniStep]; cases n.id == id <;> rfl

/-- **The heart of it.** An owner that also belongs to the list being
intersected against survives the step, whichever branch it takes. -/
theorem mem_uniStep_owners (B : List PathNodeId) (id : PathNodeId) (n : PNodeM)
    (q : PathNodeId) (hq : q ∈ n.owners) (hB : n.id = id → q ∈ B) :
    q ∈ (uniStep B id n).owners := by
  simp only [uniStep]
  split
  · next hb => exact mem_intersectOwners_of_mem _ _ q hq (hB (eq_of_beq hb))
  · exact hq

/-- A sound chain survives an owners intersection at a single node, provided
that — when the touched node *is* on the chain — the whole chain lies inside
the list being intersected against. -/
theorem ChainSound_updateAt_gen (g : GPathM) (id : PathNodeId) (B : List PathNodeId)
    (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hB : ∀ j, 0 ≤ j → j < g.current_step → sel j = id →
      ∀ i, 0 ≤ i → i < g.current_step → sel i ∈ B) :
    ChainSound (updateAt g id (uniMap B)) sel := by
  obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
  have hstep : (updateAt g id (uniMap B)).current_step = g.current_step := rfl
  have hgowners : (updateAt g id (uniMap B)).gowners = g.gowners := rfl
  have hnode : ∀ pid n, g.node? pid = some n →
      (updateAt g id (uniMap B)).node? pid = some (uniStep B id n) := by
    intro pid n hn
    exact updateAt_node? g id (uniMap B) (uniMap_id B) pid n hn
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k hlo hhi
    rw [hstep] at hhi
    obtain ⟨hsome, hs⟩ := hchain.1 k hlo hhi
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨by rw [hnode _ n hn]; rfl, hs⟩
  · intro k hlo hhi
    rw [hstep] at hhi
    have hlink := hchain.2 k hlo hhi
    cases hn : g.node? (sel (k + 1)) with
    | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
    | some n =>
      rw [hn] at hlink
      rw [hnode _ n hn]
      simpa [uniStep_parents] using hlink
  · intro i j hi hj hi' hj' hne
    rw [hstep] at hi' hj'
    have hmem := howned i j hi hj hi' hj' hne
    simp only [ownersAt, List.mem_filter, ownersOf] at hmem ⊢
    obtain ⟨hown, hs⟩ := hmem
    refine ⟨?_, hs⟩
    cases hn : g.node? (sel j) with
    | none => rw [hn] at hown; exact absurd hown List.not_mem_nil
    | some n =>
      rw [hn] at hown
      rw [hnode _ n hn]
      refine mem_uniStep_owners B id n _ hown (fun hnid => ?_)
      exact hB j hj hj' ((node?_id_eq g (sel j) n hn).symm.trans hnid) i hi hi'
  · intro k hlo hhi
    rw [hstep] at hhi
    rw [hgowners]
    exact hgow k hlo hhi
  · intro k hlo hhi
    rw [hstep] at hhi
    have hs := hself k hlo hhi
    simp only [ownersOf] at hs ⊢
    cases hn : g.node? (sel k) with
    | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hn] at hs
      rw [hnode _ n hn]
      refine mem_uniStep_owners B id n _ hs (fun hnid => ?_)
      exact hB k hlo hhi ((node?_id_eq g (sel k) n hn).symm.trans hnid) k hlo hhi
  · intro k hlo hhi
    rw [hstep] at hhi
    have hs := hson k hlo hhi
    simp only [sonsOf] at hs ⊢
    cases hn : g.node? (sel k) with
    | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hn] at hs
      rw [hnode _ n hn]
      simpa [uniStep_sons] using hs
  · exact ⟨hroot.1, fun k hk hk' => hroot.2 k hk (by rw [hstep] at hk'; exact hk')⟩

/-- The `cleanInvalid` instance: the chain is inside `gowners` by `ChainG`. -/
theorem ChainSound_updateAt (g : GPathM) (id : PathNodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (updateAt g id (gowMap g)) sel :=
  ChainSound_updateAt_gen g id g.gowners sel h
    (fun _ _ _ _ i hi hi' => h.chain.2.2 i hi hi')

-- ============================================================
-- Removing a non-chain node preserves a sound chain
-- ============================================================

theorem unlink_owners (id : PathNodeId) (n : PNodeM) : (unlink id n).owners = n.owners := rfl

theorem ChainSound_removeNode (g : GPathM) (id : PathNodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (hne : ∀ k, 0 ≤ k → k < g.current_step → sel k ≠ id) :
    ChainSound (removeNode g id) sel := by
  obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
  have hstep : (removeNode g id).current_step = g.current_step := rfl
  have hnode : ∀ k, 0 ≤ k → k < g.current_step → ∀ n, g.node? (sel k) = some n →
      (removeNode g id).node? (sel k) = some (unlink id n) :=
    fun k hk hk' n hn => removeNode_node? g id (sel k) n hn (hne k hk hk')
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k hlo hhi
    rw [hstep] at hhi
    obtain ⟨hsome, hs⟩ := hchain.1 k hlo hhi
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨by rw [hnode k hlo hhi n hn]; rfl, hs⟩
  · intro k hlo hhi
    rw [hstep] at hhi
    have hlink := hchain.2 k hlo hhi
    cases hn : g.node? (sel (k + 1)) with
    | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
    | some n =>
      rw [hn] at hlink
      rw [hnode (k + 1) (by omega) hhi n hn]
      simp only [Option.map_some, Option.getD_some, unlink, List.mem_filter]
      simp only [Option.map_some, Option.getD_some] at hlink
      exact ⟨hlink, by simp only [bne_iff_ne]; exact hne k hlo (by omega)⟩
  · intro i j hi hj hi' hj' hnei
    rw [hstep] at hi' hj'
    have hmem := howned i j hi hj hi' hj' hnei
    simp only [ownersAt, List.mem_filter, ownersOf] at hmem ⊢
    obtain ⟨hown, hs⟩ := hmem
    refine ⟨?_, hs⟩
    cases hn : g.node? (sel j) with
    | none => rw [hn] at hown; exact absurd hown List.not_mem_nil
    | some n =>
      rw [hn] at hown
      rw [hnode j hj hj' n hn]
      exact hown
  · intro k hlo hhi
    rw [hstep] at hhi
    rw [removeNode_gowners, List.mem_filter]
    exact ⟨hgow k hlo hhi, by simp only [bne_iff_ne]; exact hne k hlo hhi⟩
  · intro k hlo hhi
    rw [hstep] at hhi
    have hs := hself k hlo hhi
    simp only [ownersOf] at hs ⊢
    cases hn : g.node? (sel k) with
    | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hn] at hs
      rw [hnode k hlo hhi n hn]
      exact hs
  · intro k hlo hhi
    rw [hstep] at hhi
    have hs := hson k hlo hhi
    simp only [sonsOf] at hs ⊢
    cases hn : g.node? (sel k) with
    | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hn] at hs
      rw [hnode k hlo (by omega) n hn]
      simp only [unlink, List.mem_filter]
      exact ⟨hs, by simp only [bne_iff_ne]; exact hne (k + 1) (by omega) hhi⟩
  · exact ⟨hroot.1, fun k hk hk' => hroot.2 k hk (by rw [hstep] at hk'; exact hk')⟩

-- ============================================================
-- One `cleanInvalidGo` step, and the whole walk
-- ============================================================

-- ============================================================
-- The unlink preserves a sound chain
-- ============================================================

theorem unlinkIncompatible_current (g : GPathM) (id : PathNodeId) :
    (unlinkIncompatible g id).current_step = g.current_step := by
  unfold GPathM.unlinkIncompatible; split <;> rfl

theorem unlinkIncompatible_gowners (g : GPathM) (id : PathNodeId) :
    (unlinkIncompatible g id).gowners = g.gowners := by
  unfold GPathM.unlinkIncompatible; split <;> rfl

theorem unlinkIncompatible_node? (g : GPathM) (id : PathNodeId) (n : PNodeM)
    (hn : g.node? id = some n) (pid : PathNodeId) (m : PNodeM)
    (hm : g.node? pid = some m) :
    (unlinkIncompatible g id).node? pid = some (unlinkMap n id m) := by
  have hshape : (unlinkIncompatible g id).nodes = g.nodes.map (unlinkMap n id) := by
    simp only [GPathM.unlinkIncompatible, hn]
  have hp : (fun x : PNodeM => (unlinkMap n id x).id == pid)
      = (fun x : PNodeM => x.id == pid) := by
    funext x; rw [unlinkMap_id]
  show List.find? _ (unlinkIncompatible g id).nodes = _
  rw [hshape]
  simp only [List.find?_map, Function.comp_def, hp]
  rw [show g.nodes.find? (fun x : PNodeM => x.id == pid) = some m from hm]
  rfl

/-- **The unlink cannot break a sound chain.** A chain node's parent is one of
its owners — that is `PairwiseOwned`, already a field of `ChainSound` — so the
filter keeps it; and a neighbour that would lose the link is one the chain
never used, for the same reason. -/
theorem ChainSound_unlinkIncompatible (g : GPathM) (id : PathNodeId)
    (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (unlinkIncompatible g id) sel := by
  cases hn : g.node? id with
  | none => simpa [GPathM.unlinkIncompatible, hn] using h
  | some n =>
    obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
    have hcs := unlinkIncompatible_current g id
    have hnode : ∀ pid m, g.node? pid = some m →
        (unlinkIncompatible g id).node? pid = some (unlinkMap n id m) :=
      fun pid m hm => unlinkIncompatible_node? g id n hn pid m hm
    -- owners never move
    have howners : ∀ pid m, g.node? pid = some m →
        ownersOf (unlinkIncompatible g id) pid = ownersOf g pid := by
      intro pid m hm
      simp only [ownersOf, hm, hnode pid m hm, unlinkMap_owners]
    have hnodeAt : ∀ k, 0 ≤ k → k < g.current_step → ∃ m, g.node? (sel k) = some m := by
      intro k hlo hhi
      obtain ⟨hsome, _⟩ := hchain.1 k hlo hhi
      exact Option.isSome_iff_exists.mp hsome
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
    · -- nodes present, at their step
      intro k hlo hhi
      rw [hcs] at hhi
      obtain ⟨hsome, hstep⟩ := hchain.1 k hlo hhi
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨by rw [hnode _ m hm]; rfl, hstep⟩
    · -- parent link
      intro k hlo hhi
      rw [hcs] at hhi
      have hlink := hchain.2 k hlo hhi
      obtain ⟨hsome, _⟩ := hchain.1 (k + 1) (by omega) (by omega)
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
      have hmid : m.id = sel (k + 1) := node?_id_eq g _ m hm
      rw [hm] at hlink
      have hown : sel k ∈ m.owners := by
        have := howned k (k + 1) hlo (by omega) (by omega) hhi (by omega)
        simp only [ownersAt, List.mem_filter, ownersOf, hm] at this
        exact this.1
      rw [hnode _ m hm]
      show sel k ∈ (unlinkMap n id m).parents
      unfold GPathM.unlinkMap
      split
      · next hc =>
        have hmn : m = n := by
          have : g.node? id = some m := by rw [← eq_of_beq hc, hmid]; exact hm
          rw [hn] at this; exact (Option.some.inj this).symm
        exact List.mem_filter.mpr ⟨hlink, List.elem_iff.mpr (by rw [← hmn]; exact hown)⟩
      · next hc =>
        split
        · exact hlink
        · next hc2 =>
          refine List.mem_filter.mpr ⟨hlink, bne_iff_ne.mpr ?_⟩
          intro heq
          apply hc2
          -- if `sel k = id` then `n` owns `sel (k+1) = m.id`
          have hnk : g.node? (sel k) = some n := by rw [heq]; exact hn
          have := howned (k + 1) k (by omega) hlo (by omega) (by omega) (by omega)
          simp only [ownersAt, List.mem_filter, ownersOf, hnk] at this
          rw [hmid]
          exact List.elem_iff.mpr this.1
    · -- pairwise ownership: owners never moved
      intro i j hi hj hi' hj' hne
      rw [hcs] at hi' hj'
      obtain ⟨mj, hmj⟩ := hnodeAt j hj hj'
      rw [howners (sel j) mj hmj]
      exact howned i j hi hj hi' hj' hne
    · -- gowners
      intro k hlo hhi
      rw [hcs] at hhi
      rw [unlinkIncompatible_gowners]
      exact hgow k hlo hhi
    · -- self ownership
      intro k hlo hhi
      rw [hcs] at hhi
      obtain ⟨mk, hmk⟩ := hnodeAt k hlo hhi
      rw [howners _ mk hmk]
      exact hself k hlo hhi
    · -- son link
      intro k hlo hhi
      rw [hcs] at hhi
      have hlk := hson k hlo hhi
      obtain ⟨hsome, _⟩ := hchain.1 k hlo (by omega)
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
      have hmid : m.id = sel k := node?_id_eq g _ m hm
      simp only [sonsOf, hm] at hlk
      have hown : sel (k + 1) ∈ m.owners := by
        have := howned (k + 1) k (by omega) hlo (by omega) (by omega) (by omega)
        simp only [ownersAt, List.mem_filter, ownersOf, hm] at this
        exact this.1
      simp only [sonsOf, hnode _ m hm]
      show sel (k + 1) ∈ (unlinkMap n id m).sons
      unfold GPathM.unlinkMap
      split
      · next hc =>
        have hmn : m = n := by
          have : g.node? id = some m := by rw [← eq_of_beq hc, hmid]; exact hm
          rw [hn] at this; exact (Option.some.inj this).symm
        exact List.mem_filter.mpr ⟨hlk, List.elem_iff.mpr (by rw [← hmn]; exact hown)⟩
      · next hc =>
        split
        · exact hlk
        · next hc2 =>
          refine List.mem_filter.mpr ⟨hlk, bne_iff_ne.mpr ?_⟩
          intro heq
          apply hc2
          have hnk : g.node? (sel (k + 1)) = some n := by rw [heq]; exact hn
          have := howned k (k + 1) hlo (by omega) (by omega) (by omega) (by omega)
          simp only [ownersAt, List.mem_filter, ownersOf, hnk] at this
          rw [hmid]
          exact List.elem_iff.mpr this.1
    · -- root shape: about the ids alone
      refine ⟨hroot.1, ?_⟩
      intro k hk hk'
      rw [hcs] at hk'
      exact hroot.2 k hk hk'

/-- **A `cleanInvalid` step preserves a sound chain.** Either the node stays,
and the owners intersection could not touch the chain (it lives in `gowners`);
or the node is dropped, and then it cannot have been a chain node, because a
sound chain node always passes `isValidNode`. -/
theorem ChainSound_cleanStep (g : GPathM) (id : PathNodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (cleanStep g id) sel := by
  cases hid : g.node? id with
  | none => simpa [cleanStep, hid] using h
  | some d =>
    have hd_id : d.id = id := node?_id_eq g id d hid
    have hup : ChainSound (updateAt g id (gowMap g)) sel := ChainSound_updateAt g id sel h
    have hunl : ChainSound (unlinkIncompatible (updateAt g id (gowMap g)) id) sel :=
      ChainSound_unlinkIncompatible _ id sel hup
    have hshape : cleanStep g id =
        if isValidNode (unlinkIncompatible (updateAt g id (gowMap g)) id)
             (relink (intersectOwners d.owners g.gowners) d)
        then unlinkIncompatible (updateAt g id (gowMap g)) id
        else removeNode (unlinkIncompatible (updateAt g id (gowMap g)) id) id := by
      simp only [cleanStep, hid]
      rfl
    rw [hshape]
    split
    · exact hunl
    · next hbad =>
      -- the dropped node cannot be on the chain
      refine ChainSound_removeNode _ id sel hunl ?_
      intro k hlo hhi hk
      apply hbad
      have hnode0 : (updateAt g id (gowMap g)).node? id = some (gowMap g d) := by
        rw [updateAt_node? g id (gowMap g) (gowMap_id g) id d hid]
        simp only [gowMap]
        rw [show (d.id == id) = true from beq_iff_eq.mpr hd_id]
      have hnode : (unlinkIncompatible (updateAt g id (gowMap g)) id).node? (sel k)
          = some (relink (intersectOwners d.owners g.gowners) d) := by
        rw [hk]
        rw [unlinkIncompatible_node? _ id _ hnode0 id _ hnode0]
        show some (unlinkMap (gowMap g d) id (gowMap g d)) = _
        unfold GPathM.unlinkMap
        rw [if_pos (show ((gowMap g d).id == id) = true from by
          show (d.id == id) = true; exact beq_iff_eq.mpr hd_id)]
        rfl
      exact isValidNode_of_chain _ sel hunl k _ hnode hlo hhi

theorem ChainSound_cleanInvalidGo (ids : List PathNodeId) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      ChainSound (cleanInvalidGo g ids) sel := by
  induction ids with
  | nil => intro g sel h; simpa [cleanInvalidGo] using h
  | cons id rest ih =>
    intro g sel h
    rw [cleanInvalidGo_cons]
    exact ih _ sel (ChainSound_cleanStep g id sel h)

/-- **Obligation 1 of `Review.lean`, discharged.** `cleanInvalid` — the first
of the three stages of a review pass — preserves a sound chain. -/
theorem ChainSound_cleanInvalid (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (cleanInvalid g) sel :=
  ChainSound_cleanInvalidGo _ g sel h

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ChainSound_cleanInvalid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_cleanInvalid

/-- info: 'AbsSat.GraphPath.Model.ChainSound_cleanStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_cleanStep

end AbsSat.GraphPath.Model
