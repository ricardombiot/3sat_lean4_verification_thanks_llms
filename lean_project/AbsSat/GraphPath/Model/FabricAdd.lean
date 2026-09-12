-- lean_project/AbsSat/GraphPath/Model/FabricAdd.lean
import AbsSat.GraphPath.Model.Fabric
import AbsSat.GraphPath.Model.Reader
import AbsSat.GraphPath.Model.NodeInvariant
import AbsSat.GraphPath.Model.TriReview

/-!
# Where the fabric comes from, and what it buys

`Fabric.lean` (v65) proved the fabric **survives** the review, the pins and the
removals. What it never said is where a fabric *comes from* — and it never
mentioned `join` at all. This module supplies the missing half and then spends
it: the seed already is a fabric, `addNode` extends one, any growth preserves
one (`join` included), the greatest fabric inside a constraint is a fabric, and
from that the reader's obligation `PickSome` follows — on the **original**
machine, with no detour through the symmetric variant.

What is left over, after all of it, is a single existence: that the greatest
fabric agreeing with a clause's pins is non-empty. Everything else between the
construction and the verdict is a theorem.

That is not a coincidence of the encoding, it is the author's
`all_previous_nodes_are_owners_of_me!` doing exactly what it was written to do.
`addNode` hands the new node the whole of `gowners` and hands the new node to
every existing node as an owner — a **symmetric** act, and symmetry is one of
the nine clauses a fabric has to satisfy.

## The one step that needed an idea

Eight clauses are bookkeeping. The ninth, `up`, is not: the new node's table
holds *every* member, and `up` demands that each entry be carried by a **parent
of the new node** that is itself in the table. The new node's parents are the
whole previous line, so what has to be produced is a member at step
`current_step - 1` related to the given entry `v`.

It is there, and the fabric hands it over: `support` gives `v` an entry `w` at
that very step, `symm` turns it round into `T w v`, and `inS` makes `w` a
member. `w` is a node at step `current_step - 1`, so it lies in the previous
line, so it is a parent of the new node. The carrier is `v`'s own support
witness, reflected.

That is why symmetry is load-bearing here and not decoration — and why v64's
`OwnSymmetric_read`, which made symmetry a theorem rather than a hypothesis,
was worth having before attempting this.
-/

namespace AbsSat.GraphPath.Model.FabricAdd

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Fabric
open AbsSat.GraphPath.Model.TriReview

variable (g : GPathM) (d : NodeId) (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop)

/-- The members, plus the new node. -/
def addS : PathNodeId → Prop := fun p => S p ∨ p = newPid g d

/-- The tables, plus the new node related to every member in both directions —
which is exactly what `addNode` does to the owners lists. -/
def addT : PathNodeId → PathNodeId → Prop := fun p v =>
  (S p ∧ T p v) ∨ (v = newPid g d ∧ addS g d S p) ∨ (p = newPid g d ∧ addS g d S v)

variable {g d S T}

theorem addS_new : addS g d S (newPid g d) := Or.inr rfl

theorem addS_of (p : PathNodeId) (h : S p) : addS g d S p := Or.inl h

theorem addT_new_right (p : PathNodeId) (h : addS g d S p) : addT g d S T p (newPid g d) :=
  Or.inr (Or.inl ⟨rfl, h⟩)

theorem addT_new_left (v : PathNodeId) (h : addS g d S v) : addT g d S T (newPid g d) v :=
  Or.inr (Or.inr ⟨rfl, h⟩)

/-- The new id is not an old member: old members are nodes of `g`, and every
node of `g` sits strictly below the step the new node occupies. -/
theorem not_S_newPid (h : Fabric g S T) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) : ¬ S (newPid g d) := by
  intro hs
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node _ hs)
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = newPid g d := node?_id_eq g _ n hn
  have := hbelow n hmem
  rw [hid] at this
  simp only [newPid] at this
  omega

/-- A member sits at a step the graph already has. -/
theorem step_lt_of_S (h : Fabric g S T)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (p : PathNodeId) (hp : S p) : p.id.step < g.current_step := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
  have hid : n.id = p := node?_id_eq g p n hn
  have := hbelow n (List.mem_of_find?_eq_some hn)
  rwa [hid] at this

/-- **A member at the top old step is a parent of the new node.** -/
theorem mem_newParents_of_S (h : Fabric g S T) (hpos : 0 < g.current_step)
    (w : PathNodeId) (hw : S w) (hstep : w.id.step = g.current_step - 1) :
    w ∈ newParents g := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node w hw)
  simp only [newParents, if_pos hpos]
  exact mem_line_of_node? g w n hn _ hstep

/-- Some member sits at every step the graph has. -/
theorem exists_S_at (h : Fabric g S T) (hne : ∃ p, S p)
    (l : Int) (hl0 : 0 ≤ l) (hl : l < g.current_step) : ∃ w, S w ∧ w.id.step = l := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨w, hw, hws⟩ := h.support p hp l hl0 hl
  exact ⟨w, h.inS p w hp hw, hws⟩

/-- **The carrier the new node's `up` clause needs**: for a member `v`, a member
at the previous line related to `v`. It is `v`'s own support witness, turned
round by symmetry. -/
theorem carrier_for (h : Fabric g S T) (hpos : 0 < g.current_step)
    (v : PathNodeId) (hv : S v) : ∃ w, S w ∧ T w v ∧ w ∈ newParents g := by
  obtain ⟨w, hw, hws⟩ := h.support v hv (g.current_step - 1) (by omega) (by omega)
  have hSw : S w := h.inS v w hv hw
  exact ⟨w, hSw, h.symm v w hv hw, mem_newParents_of_S h hpos w hSw hws⟩

-- ============================================================
-- The nine clauses
-- ============================================================

/-- **The fabric is born at `addNode`.** Every member keeps what it had, the
new node joins as a member related to all of them, and the nine clauses hold. -/
theorem Fabric_addNode (title : String) (h : Fabric g S T)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hne : ∃ p, S p) (hpos : 0 < g.current_step) :
    Fabric (addNode g d title) (addS g d S) (addT g d S T) := by
  have hnew := not_S_newPid h hd hbelow
  have hstepNew : (newPid g d).id.step = g.current_step := by
    simp only [newPid]; exact hd
  -- the new node, as the graph sees it
  have hnode_new := addNode_node?_new g d title hd hbelow
  -- membership gives a node of the extended graph
  have hnode : ∀ p, addS g d S p → ((addNode g d title).node? p).isSome = true := by
    intro p hp
    rcases hp with hp | rfl
    · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      rw [addNode_node?_old g d title p n hn]; rfl
    · rw [hnode_new]; rfl
  -- an entry always lands on a member
  have hinS : ∀ p v, addS g d S p → addT g d S T p v → addS g d S v := by
    intro p v _ hT
    rcases hT with ⟨hSp, hTv⟩ | ⟨rfl, _⟩ | ⟨_, hSv⟩
    · exact Or.inl (h.inS p v hSp hTv)
    · exact addS_new
    · exact hSv
  refine
    { gow := ?_, node := hnode, inS := hinS, symm := ?_, self := ?_, sub := ?_,
      support := ?_, up := ?_, down := ?_ }
  · -- gow
    intro p hp
    rw [addNode_gowners]
    rcases hp with hp | rfl
    · exact List.mem_append_left _ (h.gow p hp)
    · exact List.mem_append_right _ List.mem_cons_self
  · -- symm
    intro p v _ hT
    rcases hT with ⟨hSp, hTv⟩ | ⟨rfl, hSp⟩ | ⟨rfl, hSv⟩
    · exact Or.inl ⟨h.inS p v hSp hTv, h.symm p v hSp hTv⟩
    · exact addT_new_left p hSp
    · exact addT_new_right v hSv
  · -- self
    intro p hp
    rcases hp with hp | rfl
    · exact Or.inl ⟨hp, h.self p hp⟩
    · exact addT_new_right _ addS_new
  · -- sub
    intro p n hn hp v hT
    rcases hp with hp | rfl
    · obtain ⟨n₀, hn₀⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      rw [addNode_node?_old g d title p n₀ hn₀] at hn
      rw [← Option.some.inj hn, upMap_owners]
      rcases hT with ⟨hSp, hTv⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact List.mem_append_left _ (h.sub p n₀ hn₀ hSp v hTv)
      · exact List.mem_append_right _ List.mem_cons_self
      · exact absurd hp hnew
    · rw [hnode_new] at hn
      rw [← Option.some.inj hn]
      show v ∈ (upNode g d title).owners ++ [newPid g d]
      simp only [upNode]
      rcases hT with ⟨hSp, _⟩ | ⟨rfl, _⟩ | ⟨_, hSv⟩
      · exact absurd hSp hnew
      · exact List.mem_append_right _ List.mem_cons_self
      · rcases hSv with hSv | rfl
        · exact List.mem_append_left _ (h.gow v hSv)
        · exact List.mem_append_right _ List.mem_cons_self
  · -- support
    intro p hp l hl0 hl
    have hcs : (addNode g d title).current_step = g.current_step + 1 := rfl
    rw [hcs] at hl
    if hltop : l = g.current_step then
      exact ⟨newPid g d, addT_new_right p hp, by rw [hstepNew, hltop]⟩
    else
      have hlt : l < g.current_step := by omega
      rcases hp with hp | rfl
      · obtain ⟨v, hv, hvs⟩ := h.support p hp l hl0 hlt
        exact ⟨v, Or.inl ⟨hp, hv⟩, hvs⟩
      · obtain ⟨w, hw, hws⟩ := exists_S_at h hne l hl0 hlt
        exact ⟨w, addT_new_left w (addS_of w hw), hws⟩
  · -- up
    intro p n hn hp hpnr v hT
    rcases hp with hp | rfl
    · -- an old member: its parents are the ones it had
      obtain ⟨n₀, hn₀⟩ := Option.isSome_iff_exists.mp (h.node p hp)
      have hpar : n.parents = n₀.parents := by
        rw [addNode_node?_old g d title p n₀ hn₀] at hn
        rw [← Option.some.inj hn, upMap_parents]
      rcases hT with ⟨hSp, hTv⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · obtain ⟨c, hc, hpc, hcv⟩ := h.up p n₀ hn₀ hSp hpnr v hTv
        have hSc : S c := h.inS p c hSp hpc
        exact ⟨c, by rw [hpar]; exact hc, Or.inl ⟨hSp, hpc⟩, Or.inl ⟨hSc, hcv⟩⟩
      · -- the entry is the new node: any parent-carrier of an old entry will do
        obtain ⟨v₀, hv₀, _⟩ := h.support p hp 0 (by omega) hpos
        obtain ⟨c, hc, hpc, _⟩ := h.up p n₀ hn₀ hp hpnr v₀ hv₀
        have hSc : S c := h.inS p c hp hpc
        exact ⟨c, by rw [hpar]; exact hc, Or.inl ⟨hp, hpc⟩, addT_new_right c (addS_of c hSc)⟩
      · exact absurd hp hnew
    · -- the new node: its parents are the whole previous line
      have hpar : n.parents = newParents g := by
        rw [hnode_new] at hn
        rw [← Option.some.inj hn]
        rfl
      have hSv : addS g d S v := hinS _ v addS_new hT
      rcases hSv with hSv | rfl
      · obtain ⟨w, hSw, hwv, hwmem⟩ := carrier_for h hpos v hSv
        exact ⟨w, by rw [hpar]; exact hwmem, addT_new_left w (addS_of w hSw),
          Or.inl ⟨hSw, hwv⟩⟩
      · obtain ⟨w, hSw, hws⟩ := exists_S_at h hne (g.current_step - 1) (by omega) (by omega)
        exact ⟨w, by rw [hpar]; exact mem_newParents_of_S h hpos w hSw hws,
          addT_new_left w (addS_of w hSw), addT_new_right w (addS_of w hSw)⟩
  · -- down
    intro p hp hptop v hT
    rcases hp with hp | rfl
    · have hSv : addS g d S v := hinS p v (Or.inl hp) hT
      if htop : p.id.step = g.current_step - 1 then
        -- the new node is the son-carrier
        refine ⟨newPid g d, addOwner (newPid g d) (upNode g d title), hnode_new, ?_,
          addT_new_right p (addS_of p hp), addT_new_left v hSv⟩
        show p ∈ (upNode g d title).parents
        exact mem_newParents_of_S h hpos p hp htop
      else
        obtain ⟨n₀, hn₀⟩ := Option.isSome_iff_exists.mp (h.node p hp)
        have hne' : p.id.step ≠ g.current_step - 1 := htop
        rcases hT with ⟨hSp, hTv⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
        · obtain ⟨c, m, hcm, hpm, hpc, hcv⟩ := h.down p hSp hne' v hTv
          have hSc : S c := h.inS p c hSp hpc
          refine ⟨c, upMap g d m, addNode_node?_old g d title c m hcm, ?_,
            Or.inl ⟨hSp, hpc⟩, Or.inl ⟨hSc, hcv⟩⟩
          rw [upMap_parents]; exact hpm
        · obtain ⟨v₀, hv₀, _⟩ := h.support p hp 0 (by omega) hpos
          obtain ⟨c, m, hcm, hpm, hpc, _⟩ := h.down p hp hne' v₀ hv₀
          have hSc : S c := h.inS p c hp hpc
          refine ⟨c, upMap g d m, addNode_node?_old g d title c m hcm, ?_,
            Or.inl ⟨hp, hpc⟩, addT_new_right c (addS_of c hSc)⟩
          rw [upMap_parents]; exact hpm
        · exact absurd hp hnew
    · -- the new node sits at the top step, so the clause does not apply
      refine absurd ?_ hptop
      show (newPid g d).id.step = (addNode g d title).current_step - 1
      rw [hstepNew]
      show g.current_step = g.current_step + 1 - 1
      omega

-- ============================================================
-- The base case: the seed carries a fabric too
-- ============================================================

/-- **The seed is already a fabric.** One node, owning itself, at step 0 — all
nine clauses hold, two of them vacuously (the seed has no parent and sits at
the top step of its own graph). With `Fabric_addNode` this closes the
establishment side: a fabric exists at the start and one exists after every
`addNode`. -/
theorem Fabric_initSeed (d : NodeId) (title : String) (hd : d.step = 0) :
    Fabric (initSeed d title)
      (fun p => p = newPid empty d) (fun p v => p = newPid empty d ∧ v = newPid empty d) := by
  have hseed : initSeed d title = addNode empty d title := rfl
  have hbelow : ∀ n ∈ empty.nodes, n.id.id.step < empty.current_step := by
    intro n hn; exact absurd hn List.not_mem_nil
  have hnode := addNode_node?_new empty d title hd hbelow
  have hstep : (newPid empty d).id.step = 0 := by simp only [newPid]; exact hd
  rw [hseed]
  refine { gow := ?_, node := ?_, inS := ?_, symm := ?_, self := ?_, sub := ?_,
           support := ?_, up := ?_, down := ?_ }
  · intro p hp; rw [hp, addNode_gowners]; exact List.mem_append_right _ List.mem_cons_self
  · intro p hp; rw [hp, hnode]; rfl
  · intro p v _ hT; exact hT.2
  · intro p v _ hT; exact ⟨hT.2, hT.1⟩
  · intro p hp; exact ⟨hp, hp⟩
  · intro p n hn hp v hT
    rw [hp, hnode] at hn
    rw [← Option.some.inj hn, hT.2]
    show newPid empty d ∈ (upNode empty d title).owners ++ [newPid empty d]
    exact List.mem_append_right _ List.mem_cons_self
  · intro p hp l hl0 hl
    have : l = 0 := by
      have hcs : (addNode empty d title).current_step = 1 := rfl
      rw [hcs] at hl; omega
    exact ⟨newPid empty d, ⟨hp, rfl⟩, by rw [hstep, this]⟩
  · -- the seed has no parent id, so the clause does not apply
    intro p _ _ hp hpnr _ _
    exact absurd (by rw [hp]; rfl) hpnr
  · -- the seed sits at the top step of its own graph
    intro p hp hptop _ _
    refine absurd ?_ hptop
    show p.id.step = (addNode empty d title).current_step - 1
    rw [hp, hstep]
    show (0 : Int) = 1 - 1
    omega

-- ============================================================
-- What the route consumes: the new node carries a fabric of its own
-- ============================================================

/-- **The new node's fabric lives inside its own owners.** `addNode` hands it
exactly `gowners`, and a fabric's members are global owners — so the inclusion
`FabricAt` asks for is the `gow` clause, read on the extended graph. -/
theorem FabricAt_addNode_new (title : String) (h : Fabric g S T)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hne : ∃ p, S p) (hpos : 0 < g.current_step)
    (hsmp : Sons.SMP (addNode g d title)) (hnr : Parents.NotRoot (addNode g d title)) :
    FabricAt (addNode g d title) (newPid g d) := by
  have hfab := Fabric_addNode (g := g) (d := d) (S := S) (T := T) title h hd hbelow hne hpos
  refine ⟨addOwner (newPid g d) (upNode g d title), addS g d S, addT g d S T,
    addNode_node?_new g d title hd hbelow, ⟨hfab, hsmp, hnr⟩, addS_new, ?_⟩
  intro p hp
  show p ∈ (upNode g d title).owners ++ [newPid g d]
  simp only [upNode]
  rcases hp with hp | rfl
  · exact List.mem_append_left _ (h.gow p hp)
  · exact List.mem_append_right _ List.mem_cons_self

/-- **And therefore choosing the new node never gets the reader stuck** — the
piece the route needs, for the node the construction has just created. -/
theorem isValid_readStepSym_addNode_new (title : String) (h : Fabric g S T)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hne : ∃ p, S p) (hpos : 0 < g.current_step)
    (hsmp : Sons.SMP (addNode g d title)) (hnr : Parents.NotRoot (addNode g d title)) :
    isValid (SymReview.readStepSym (addNode g d title) (newPid g d)) = true :=
  isValid_readStepSym_of_FabricAt _ _
    (FabricAt_addNode_new (S := S) (T := T) title h hd hbelow hne hpos hsmp hnr)

-- ============================================================
-- The case the ledger was missing: `join`
-- ============================================================

/-! v78 found that `Fabric.lean` never mentions `join`, so the induction over
`Reachable` had a hole where its fourth case should be. It closes in one lemma,
and not by accident: **a fabric only ever asks for things to be *there***. Every
clause is an existence or a membership — an entry at each step, a carrier among
the parents, an owner in a table — and `Grown` says exactly that nothing goes
away. So a fabric survives any growth, and `join` is growth on both sides. -/

/-- **A fabric survives growth.** Nothing a fabric asserts can be broken by
adding nodes, parents, sons or owners. -/
theorem Fabric_of_grown {g g' : GPathM} (hgr : Grown g g')
    (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop) (h : Fabric g S T) :
    Fabric g' S T := by
  -- every member's node grows into the member's node of `g'`
  have hgrow : ∀ p, S p → ∃ n n', g.node? p = some n ∧ g'.node? p = some n' ∧
      (∀ q ∈ n.owners, q ∈ n'.owners) ∧ (∀ c ∈ n.parents, c ∈ n'.parents) := by
    intro p hp
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node p hp)
    obtain ⟨n', hn', ho, hpar, _⟩ := hgr.node?_grown p n hn
    exact ⟨n, n', hn, hn', ho, hpar⟩
  refine
    { gow := fun p hp => hgr.gowners_grown p (h.gow p hp),
      node := ?_, inS := h.inS, symm := h.symm, self := h.self,
      sub := ?_, support := ?_, up := ?_, down := ?_ }
  · intro p hp
    obtain ⟨_, _, _, hn', _, _⟩ := hgrow p hp
    rw [hn']; rfl
  · intro p n hn hp v hT
    obtain ⟨n₀, n', hn₀, hn', ho, _⟩ := hgrow p hp
    rw [hn'] at hn
    rw [← Option.some.inj hn]
    exact ho v (h.sub p n₀ hn₀ hp v hT)
  · intro p hp l hl0 hl
    rw [hgr.step_eq] at hl
    exact h.support p hp l hl0 hl
  · intro p n hn hp hpnr v hT
    obtain ⟨n₀, n', hn₀, hn', _, hpar⟩ := hgrow p hp
    rw [hn'] at hn
    obtain ⟨c, hc, hpc, hcv⟩ := h.up p n₀ hn₀ hp hpnr v hT
    rw [← Option.some.inj hn]
    exact ⟨c, hpar c hc, hpc, hcv⟩
  · intro p hp hptop v hT
    rw [hgr.step_eq] at hptop
    obtain ⟨c, m, hcm, hpm, hpc, hcv⟩ := h.down p hp hptop v hT
    obtain ⟨m', hm', _, hpar, _⟩ := hgr.node?_grown c m hcm
    exact ⟨c, m', hm', hpar p hpm, hpc, hcv⟩

/-- **The join keeps the left side's fabric.** -/
theorem Fabric_join_left (g₁ g₂ : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : Fabric g₁ S T) :
    Fabric (join g₁ g₂) S T :=
  Fabric_of_grown (grown_join_left g₁ g₂) S T h

/-- **And the right side's.** -/
theorem Fabric_join_right (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (S : PathNodeId → Prop) (T : PathNodeId → PathNodeId → Prop) (h : Fabric g₂ S T) :
    Fabric (join g₁ g₂) S T :=
  Fabric_of_grown (grown_join_right g₁ g₂ hok) S T h

-- ============================================================
-- P3: narrowing the fabric to the pins
-- ============================================================

/-! `filterRequire` touches **only `gowners`** — the per-node tables are left
alone, and it is the review that narrows those afterwards. So of the nine
clauses, the pin threatens exactly one: `gow`, that members are global owners.
Everything else is untouched.

That is why v65's `FOk_filterAll` asks its members to agree with the pins: it
is `gow`, and nothing more. And at a clause step the fabric `addNode` builds
fails it at once, because that fabric holds *all* the global owners and so both
values of a pinned step.

So the work is not preservation, it is **narrowing** — and narrowing is where
v44's move applies. The clauses of a fabric are closed under union, because
every one of them is witnessed inside a single fabric. Hence **the greatest
fabric satisfying any constraint is itself a fabric**, and the whole of P3
collapses to one question: *does that greatest one still reach the node we
care about?* -/

/-- The members that survive a pin. -/
def Compat (reqs : List NodeId) (p : PathNodeId) : Prop :=
  ∀ r ∈ reqs, p.id.step = r.step → p.id = r

/-- **The greatest fabric inside a constraint** — members. -/
def CoreS (g : GPathM) (P : PathNodeId → Prop) : PathNodeId → Prop :=
  fun p => ∃ S T, Fabric g S T ∧ (∀ q, S q → P q) ∧ S p

/-- **The greatest fabric inside a constraint** — tables. -/
def CoreT (g : GPathM) (P : PathNodeId → Prop) : PathNodeId → PathNodeId → Prop :=
  fun p v => ∃ S T, Fabric g S T ∧ (∀ q, S q → P q) ∧ S p ∧ T p v

theorem CoreS_of_mem {g : GPathM} {P : PathNodeId → Prop} {S T}
    (hf : Fabric g S T) (hP : ∀ q, S q → P q) {p} (hp : S p) : CoreS g P p :=
  ⟨S, T, hf, hP, hp⟩

/-- Every member of the core satisfies the constraint. -/
theorem CoreS_sat {g : GPathM} {P : PathNodeId → Prop} (p : PathNodeId)
    (hp : CoreS g P p) : P p := by
  obtain ⟨_, _, _, hP, hSp⟩ := hp
  exact hP _ hSp

/-- **The greatest fabric inside a constraint is a fabric.** Each clause is
witnessed inside one component, so the union carries them all. -/
theorem Fabric_core (g : GPathM) (P : PathNodeId → Prop) :
    Fabric g (CoreS g P) (CoreT g P) := by
  refine { gow := ?_, node := ?_, inS := ?_, symm := ?_, self := ?_, sub := ?_,
           support := ?_, up := ?_, down := ?_ }
  · rintro p ⟨S, T, hf, _, hSp⟩; exact hf.gow p hSp
  · rintro p ⟨S, T, hf, _, hSp⟩; exact hf.node p hSp
  · rintro p v _ ⟨S, T, hf, hP, hSp, hT⟩; exact ⟨S, T, hf, hP, hf.inS p v hSp hT⟩
  · rintro p v _ ⟨S, T, hf, hP, hSp, hT⟩
    exact ⟨S, T, hf, hP, hf.inS p v hSp hT, hf.symm p v hSp hT⟩
  · rintro p ⟨S, T, hf, hP, hSp⟩; exact ⟨S, T, hf, hP, hSp, hf.self p hSp⟩
  · rintro p n hn _ v ⟨S, T, hf, _, hSp, hT⟩; exact hf.sub p n hn hSp v hT
  · rintro p ⟨S, T, hf, hP, hSp⟩ l hl0 hl
    obtain ⟨v, hv, hvs⟩ := hf.support p hSp l hl0 hl
    exact ⟨v, ⟨S, T, hf, hP, hSp, hv⟩, hvs⟩
  · rintro p n hn _ hpnr v ⟨S, T, hf, hP, hSp, hT⟩
    obtain ⟨c, hc, hpc, hcv⟩ := hf.up p n hn hSp hpnr v hT
    exact ⟨c, hc, ⟨S, T, hf, hP, hSp, hpc⟩,
      ⟨S, T, hf, hP, hf.inS p c hSp hpc, hcv⟩⟩
  · rintro p ⟨S, T, hf, hP, hSp⟩ hptop v ⟨S', T', hf', hP', hSp', hT'⟩
    obtain ⟨c, m, hcm, hpm, hpc, hcv⟩ := hf'.down p hSp' hptop v hT'
    exact ⟨c, m, hcm, hpm, ⟨S', T', hf', hP', hSp', hpc⟩,
      ⟨S', T', hf', hP', hf'.inS p c hSp' hpc, hcv⟩⟩

/-- **P3, reduced to one question.** With the core in hand, the fabric that
survives a clause's pins is the greatest one whose members agree with them and
lie inside `owners(r)` — and the only thing left to establish is that this
greatest one still reaches `r`. That is v44's `CoreCovers`, in the fabric's
vocabulary. -/
def PinReaches (g : GPathM) (reqs : List NodeId) (r : PathNodeId) (rn : PNodeM) : Prop :=
  CoreS g (fun q => Compat reqs q ∧ q ∈ rn.owners) r

/-- **And with it, the pinned state carries a fabric through `r`.** The `gow`
clause is the only one the pin threatens, and the core's members satisfy it by
construction; `FOk_filterAll` then carries the fabric through the whole clause
filter, review included. -/
theorem FabricAt_filterAll_of_PinReaches (g : GPathM) (reqs : List NodeId)
    (r : PathNodeId) (rn : PNodeM) (hr : (filterAll g reqs).node? r = some rn)
    (hsmp : Sons.SMP g) (hnr : Parents.NotRoot g)
    (h : PinReaches g reqs r rn) :
    FabricAt (filterAll g reqs) r := by
  refine ⟨rn, CoreS g (fun q => Compat reqs q ∧ q ∈ rn.owners),
    CoreT g (fun q => Compat reqs q ∧ q ∈ rn.owners), hr, ?_, h, ?_⟩
  · exact FOk_filterAll g _ _ ⟨Fabric_core g _, hsmp, hnr⟩ reqs
      (fun req hreq p hp hstep => (CoreS_sat p hp).1 req hreq hstep)
  · exact fun p hp => (CoreS_sat p hp).2

-- ============================================================
-- P4: the bridge to `PickSome`, without the symmetric detour
-- ============================================================

/-! v77 flagged a mismatch: `PickSome` asks for `isValid (filterAll g [q.id])`
— the **original** pin and review — while v65's fabric theorem answers about
`readStepSym = reviewSym ∘ pinOwners`. Two different operations, and bridging
them looked like real work.

It is not needed. v65 also proved the two facts that matter for the *original*
machine: `FOk_filterAll`, that a fabric agreeing with the pins survives the
whole filter, and `isValid_of_Fabric`, that a non-empty fabric makes a graph
valid — its `support` clause reaches every step, which is exactly what
`isValid` counts. Put them either side of `Fabric_core` and the bridge is
three lines.

So the route never has to commit to the symmetric variant. That matters: it
keeps everything downstream about the machine as it is written. -/

/-- What one pick needs: some fabric agreeing with that pin is non-empty. -/
def PinNonEmpty (g : GPathM) (q : PathNodeId) : Prop :=
  ∃ p, CoreS g (Compat [q.id]) p

/-- **Pinning an owner whose core is non-empty leaves the state valid.** -/
theorem isValid_filterAll_of_PinNonEmpty (g : GPathM) (q : PathNodeId)
    (hsmp : Sons.SMP g) (hnr : Parents.NotRoot g) (h : PinNonEmpty g q) :
    isValid (filterAll g [q.id]) = true := by
  have hok : FOk (filterAll g [q.id]) (CoreS g (Compat [q.id])) (CoreT g (Compat [q.id])) :=
    FOk_filterAll g _ _ ⟨Fabric_core g _, hsmp, hnr⟩ [q.id]
      (fun req hreq p hp hstep => CoreS_sat p hp req hreq hstep)
  exact isValid_of_Fabric _ _ _ hok.fab h

/-- **P4.** The reader's obligation follows from the fabric, on the original
machine: at a step that still offers a choice, an owner whose core is non-empty
is an owner the pick can take. -/
theorem PickSome_of_PinNonEmpty (g : GPathM) (hsmp : Sons.SMP g) (hnr : Parents.NotRoot g)
    (h : PickInduction.hasChoice g = true → ∃ k, 0 ≤ k ∧ k < g.current_step ∧
      PickInduction.choiceAt g k = true ∧
      ∃ q ∈ ownersAt g.gowners k, PinNonEmpty g q) :
    PickInduction.PickSome g := by
  intro hch
  obtain ⟨k, hk0, hk1, hck, q, hq, hne⟩ := h hch
  exact ⟨k, hk0, hk1, hck, q, hq, isValid_filterAll_of_PinNonEmpty g q hsmp hnr hne⟩

/-- **The route, assembled.** One obligation, stated on the machine's own
structures, and the reader's loop reaches a denotation — which is what the
verdict consumes (`L7.satisfiable_of_inhabited`). Everything between here and
there is already a theorem. -/
theorem Inhabited_of_PinNonEmpty (reqOf : NodeId → List NodeId) (g : GPathM)
    (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true)
    (hinv : ∀ h' : GPathM, Reader.Readable h' → isValid h' = true →
      Sons.SMP h' ∧ Parents.NotRoot h')
    (hpins : ∀ h' : GPathM, Reader.Readable h' → isValid h' = true →
      PickInduction.hasChoice h' = true → ∃ k, 0 ≤ k ∧ k < h'.current_step ∧
        PickInduction.choiceAt h' k = true ∧ ∃ q ∈ ownersAt h'.gowners k, PinNonEmpty h' q) :
    AbsSat.GraphPath.Model.Inhabited (filterAll g reqs) :=
  Reader.Inhabited_of_pickSome_machine reqOf g reqs hreach hv
    (fun h' hr hvv =>
      PickSome_of_PinNonEmpty h' (hinv h' hr hvv).1 (hinv h' hr hvv).2 (hpins h' hr hvv))

-- ============================================================
-- P3, the half that is provable: the pinned candidate covers
-- ============================================================

/-! The fabric P3 needs is the greatest **self-supporting** subset of
`owners(r)` agreeing with the clause's pins, and it is built by narrowing a
candidate. The candidate is `owners(r) ∩ Compat reqs`, and **that it covers
every step is a theorem** — it needs nothing open:

* at a step some requirement names, the only compatible node is the
  requirement itself, and `owns_required` says a survivor of the filter owns
  it. That is the author's own filter doing the work;
* at every other step, `Compat` constrains nothing and `isValidNode`'s owners
  clause supplies an owner.

So the first half of P3 is paid. What is **not** paid is the narrowing: the
greatest self-supporting subset of a covering candidate need not cover. That is
v45's residue, `support` at distance ≥ 2, reached here from a third direction —
and `cnfmap --p3` measures precisely it (39.450 survivors, 0 losses). -/

/-- **The pinned candidate covers every step.** -/
theorem pinnedCandidate_covers (reqOf : NodeId → List NodeId) (g : GPathM)
    (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true)
    (hreqs : ∀ r ∈ reqs, 0 ≤ r.step ∧ r.step < g.current_step)
    (hfun : ∀ r₁ ∈ reqs, ∀ r₂ ∈ reqs, r₁.step = r₂.step → r₁ = r₂)
    (r : PathNodeId) (n : PNodeM) (hn : (filterAll g reqs).node? r = some n)
    (l : Int) (hl0 : 0 ≤ l) (hl : l < g.current_step) :
    ∃ q ∈ n.owners, q.id.step = l ∧ Compat reqs q := by
  if hpin : ∃ req ∈ reqs, req.step = l then
    -- a pinned step: the requirement itself is an owner, and it is the only
    -- compatible node there
    obtain ⟨req, hreq, hreqstep⟩ := hpin
    obtain ⟨hr0, hr1⟩ := hreqs req hreq
    obtain ⟨q, hq, hqid⟩ :=
      NodeInvariant.owns_required reqOf g reqs hreach hv r n hn req hreq hr0 hr1
    refine ⟨q, hq, by rw [hqid]; exact hreqstep, ?_⟩
    intro req' hreq' hstep'
    -- two requirements naming the same step must coincide
    rw [hqid]
    exact (hfun req hreq req' hreq' (by rw [← hstep', hqid])).symm ▸ rfl
  else
    -- an unpinned step: `Compat` says nothing, and validity supplies an owner
    have hcs : (filterAll g reqs).current_step = g.current_step :=
      (pruned_filterAll g reqs).step_eq
    have hok := owners_ok_of_isValidNode _ n
      ((Pinned.ctx_filterAll reqOf g reqs hreach hv).nodeval r n hn)
    have hk : l ∈ intRange 0 ((filterAll g reqs).current_step - 1) :=
      mem_intRange hl0 (by rw [hcs]; omega)
    obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hok l hk)
    exact ⟨q, hq, eq_of_beq hqs, fun req hreq hstep =>
      absurd ⟨req, hreq, by rw [← hstep, eq_of_beq hqs]⟩ hpin⟩

-- ============================================================
-- The narrowing: why nothing is deleted
-- ============================================================

/-! The candidate covers. The question is whether narrowing it to the greatest
self-supporting subset can empty a step. The answer, and it is the point of
this section: **it deletes nothing at all**, because every member already has
its support inside the candidate.

Take a member `p` of `C = owners(r) ∩ Compat reqs` and a step `l`.

* The **triangle** property gives, straight from `p ∈ owners(r)`, a node `w`
  in *both* tables at step `l`. That is exactly what the author's `triClean`
  pass enforces, and it is why v69 was needed before this could work.
* And `w` is automatically in `C`: it is in `owners(r)` by construction, and it
  is `Compat` because **every owner of a survivor is a global owner, and the
  pins filtered the global owners**. No case split on pinned versus free steps
  is needed — the pin did its work once, on `gowners`, and every table inherits
  it.

So the residue of v45 — `support` at distance ≥ 2 — is discharged here by the
triangle.

⚠ v84 and v85 routed the first bullet through **symmetry** — turning
`p ∈ owners(r)` into `r ∈ owners(p)` before applying the triangle — and
reported symmetry as a hypothesis still to be transported. That was a detour:
`TriProp` in the direction it already has yields the same node. The hypothesis
is gone from `pinnedCandidate_selfSupporting`, which now asks for three things,
not four. -/

/-- The pins only ever filtered the global owners, and the fold composes. -/
theorem gowners_foldl_sub : ∀ (reqs : List NodeId) (g : GPathM),
    ∀ q ∈ (reqs.foldl filterRequire g).gowners, q ∈ g.gowners := by
  intro reqs
  induction reqs with
  | nil => intro g q hq; exact hq
  | cons req rest ih =>
    intro g q hq
    simp only [List.foldl_cons] at hq
    exact List.mem_filter.mp (ih (filterRequire g req) q hq) |>.1

/-- **The pinned global owners agree with every pin.** -/
theorem gowners_foldl_compat : ∀ (reqs : List NodeId) (g : GPathM),
    ∀ q ∈ (reqs.foldl filterRequire g).gowners, Compat reqs q := by
  intro reqs
  induction reqs with
  | nil => intro _ q _ r hr; exact absurd hr List.not_mem_nil
  | cons req rest ih =>
    intro g q hq
    simp only [List.foldl_cons] at hq
    intro r hr hstep
    rcases List.mem_cons.mp hr with heq | hrest
    · -- the head pin: `filterRequire` kept only what agrees with it
      have hmem := gowners_foldl_sub rest (filterRequire g req) q hq
      have hfil := List.mem_filter.mp hmem |>.2
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hfil
      rcases hfil with hne | heq2
      · exact absurd (by rw [hstep, heq]) hne
      · rw [heq2, heq]
    · exact ih (filterRequire g req) q hq r hrest hstep

/-- What the triangle pass enforces: two nodes that own each other share an
entry at every step. -/
def TriProp (g : GPathM) : Prop :=
  ∀ a na b nb, g.node? a = some na → g.node? b = some nb → b ∈ na.owners →
    ∀ l, 0 ≤ l → l < g.current_step →
      ∃ w, w ∈ na.owners ∧ w ∈ nb.owners ∧ w.id.step = l

/-- Every in-range owner of a node is one of the global owners. This is what
`review` establishes at its fixpoint, and what the pin then constrains in one
go. -/
def OwnersGlobal (g : GPathM) : Prop :=
  ∀ r n, g.node? r = some n → ∀ w ∈ n.owners,
    0 ≤ w.id.step → w.id.step < g.current_step → w ∈ g.gowners

/-- **The narrowing deletes nothing.** Every member of the pinned candidate has
its support *inside* the candidate, at every step — so the greatest
self-supporting subset is the candidate itself, and it covers.

Three hypotheses, all of them the author's: the owners are global owners, the
global owners carry the pins, and the triangle holds. -/
theorem pinnedCandidate_selfSupporting (reqs : List NodeId) (G : GPathM)
    (hown : OwnersGlobal G)
    (hgow : ∀ q ∈ G.gowners, Compat reqs q)
    (htri : TriProp G)
    (r : PathNodeId) (n : PNodeM) (hn : G.node? r = some n)
    (p : PathNodeId) (hp : p ∈ n.owners)
    (np : PNodeM) (hnp : G.node? p = some np)
    (l : Int) (hl0 : 0 ≤ l) (hl : l < G.current_step) :
    ∃ w, w ∈ np.owners ∧ w ∈ n.owners ∧ Compat reqs w ∧ w.id.step = l := by
  -- the triangle, applied the way it is already stated: a shared entry at `l`
  obtain ⟨w, hwr, hwp, hws⟩ := htri r n p np hn hnp hp l hl0 hl
  refine ⟨w, hwp, hwr, ?_, hws⟩
  -- and it is compatible, because it is a global owner and the pins filtered those
  exact hgow w (hown r n hn w hwr (by rw [hws]; exact hl0) (by rw [hws]; exact hl))

/-- The hypotheses of the previous theorem, discharged for the machine's own
clause filter: owners are global owners, and the global owners carry the
pins. -/
theorem gowners_compat_filterAll (g : GPathM) (reqs : List NodeId) :
    ∀ q ∈ (filterAll g reqs).gowners, Compat reqs q := fun q hq =>
  gowners_foldl_compat reqs g q
    ((pruned_review (reqs.foldl filterRequire g)).gowners_sub q hq)

-- ============================================================
-- `TriProp`, extracted from the triangle pass
-- ============================================================

/-! v84 took `TriProp` as a hypothesis and said extracting it was bookkeeping.
Here it is. The heart is one line of reading: at a fixpoint of `triClean`, an
entry that survived the sweep survived it **because** the sweep's own test held
— and that test *is* `TriProp`. The rest is showing the pass reaches a
fixpoint, which it does as soon as it stops removing anything. -/

/-- A filter that drops nothing is the identity. -/
theorem filter_eq_self_of_length {α : Type} (p : α → Bool) (l : List α)
    (h : l.length ≤ (l.filter p).length) : l.filter p = l :=
  List.filter_sublist.eq_of_length
    (Nat.le_antisymm (List.Sublist.length_le List.filter_sublist) h)

theorem weight_triMap_le (g : GPathM) (n : PNodeM) :
    PNodeM.weight (triMap g n) ≤ PNodeM.weight n := by
  simp only [PNodeM.weight, triMap]
  exact Nat.add_le_add_left (List.Sublist.length_le List.filter_sublist) _

theorem sum_map_le {α : Type} (f h : α → Nat) (hle : ∀ x, f x ≤ h x) :
    ∀ l : List α, (l.map f).sum ≤ (l.map h).sum := by
  intro l
  induction l with
  | nil => exact Nat.le_refl _
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hle y) ih

theorem sum_eq_pointwise {α : Type} (f h : α → Nat) (hle : ∀ x, f x ≤ h x) :
    ∀ l : List α, (l.map h).sum ≤ (l.map f).sum → ∀ x ∈ l, f x = h x := by
  intro l
  induction l with
  | nil => intro _ x hx; exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    intro hsum x hx
    simp only [List.map_cons, List.sum_cons] at hsum
    have hts := sum_map_le f h hle ys
    have hy := hle y
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · exact ih (by omega) x hx'

/-- **A triangle sweep that removes nothing is the identity.** -/
theorem triClean_eq_of_measure_ge (g : GPathM)
    (h : GPathM.measure g ≤ GPathM.measure (triClean g)) : triClean g = g := by
  have hsum : (g.nodes.map PNodeM.weight).sum
      ≤ (g.nodes.map (fun n => PNodeM.weight (triMap g n))).sum := by
    simp only [GPathM.measure, triClean, List.map_map, Function.comp_def] at h
    omega
  have hpt := sum_eq_pointwise (fun n => PNodeM.weight (triMap g n)) PNodeM.weight
    (weight_triMap_le g) g.nodes hsum
  have hid : ∀ n ∈ g.nodes, triMap g n = n := by
    intro n hn
    have hw := hpt n hn
    simp only [PNodeM.weight, triMap] at hw
    have hlen : n.owners.length
        ≤ (n.owners.filter (fun q => commonAtAll g n.owners q)).length := by omega
    simp only [triMap]
    rw [filter_eq_self_of_length _ _ hlen]
  have hnodes : ∀ l : List PNodeM, (∀ n ∈ l, triMap g n = n) → l.map (triMap g) = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons y ys ihl =>
      intro hl
      simp only [List.map_cons, hl y List.mem_cons_self]
      rw [ihl (fun n hn => hl n (List.mem_cons_of_mem _ hn))]
  simp only [triClean, hnodes g.nodes hid]

/-- The review never grows the measure — the fuel loop only ever runs passes
that do not, and stops where they stop. -/
theorem measure_reviewFuel_le : ∀ (fuel : Nat) (g : GPathM),
    GPathM.measure (reviewFuel fuel g) ≤ GPathM.measure g := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Nat.le_refl _
  | succ f ih =>
    intro g
    simp only [reviewFuel]
    if hval : isValid g = true then
      if hlt : GPathM.measure (reviewPass g) < GPathM.measure g then
        simp only [if_pos hval, if_pos hlt]
        exact Nat.le_trans (ih (reviewPass g)) (Nat.le_of_lt hlt)
      else
        simp only [if_pos hval, if_neg hlt]
        exact measure_reviewPass_le g
    else
      simp only [if_neg hval]
      exact Nat.le_refl _

theorem measure_review_le (g : GPathM) : GPathM.measure (review g) ≤ GPathM.measure g :=
  measure_reviewFuel_le _ g

/-- **The fixpoint of the triangle pass satisfies `TriProp`.** An entry that
survived the sweep survived it because the sweep's test held, and that test is
`TriProp` itself. -/
theorem TriProp_of_triClean_fixpoint (g : GPathM) (hfix : triClean g = g) : TriProp g := by
  intro a na b nb hna hnb hb l hl0 hl
  have hmap : some na = some (triMap g na) := by
    have h1 := triClean_node? g a
    rw [hfix, hna] at h1
    simpa using h1
  have heq : na = triMap g na := Option.some.inj hmap
  have hna' : na.owners = na.owners.filter (fun q => commonAtAll g na.owners q) :=
    congrArg PNodeM.owners heq
  have hbf : b ∈ na.owners.filter (fun q => commonAtAll g na.owners q) := by
    rw [← hna']; exact hb
  have hcom : commonAtAll g na.owners b = true := (List.mem_filter.mp hbf).2
  simp only [commonAtAll, hnb, List.all_eq_true] at hcom
  have hk : l ∈ intRange 0 (g.current_step - 1) := mem_intRange hl0 (by omega)
  obtain ⟨w, hw, hwp⟩ := List.any_eq_true.mp (hcom l hk)
  simp only [Bool.and_eq_true, beq_iff_eq] at hwp
  exact ⟨w, hw, List.mem_of_elem_eq_true hwp.2, hwp.1⟩

/-- **And so the triangle review delivers it**, as soon as the loop has fuel to
reach the point where the sweep stops removing anything. -/
theorem TriProp_reviewTriFuel (hrev : ∀ h : GPathM, GPathM.measure (review h) ≤ GPathM.measure h) :
    ∀ (fuel : Nat) (g : GPathM), GPathM.measure g ≤ fuel →
      isValid (reviewTriFuel fuel g) = true → TriProp (reviewTriFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero =>
    intro g hm hv
    simp only [reviewTriFuel] at hv ⊢
    intro a na b nb _ _ _ l hl0 hl
    have hgow : g.gowners = [] := by
      simp only [GPathM.measure] at hm
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hk : l ∈ intRange 0 (g.current_step - 1) := mem_intRange hl0 (by omega)
    have hstep := List.all_eq_true.mp hv l hk
    simp only [hasStepEntry, hgow, List.any_nil] at hstep
    exact absurd hstep (by simp)
  | succ f ih =>
    intro g hm hv
    simp only [reviewTriFuel] at hv ⊢
    if hval : isValid (review g) = true then
      if hlt : GPathM.measure (triClean (review g)) < GPathM.measure (review g) then
        simp only [if_pos hval, if_pos hlt] at hv ⊢
        exact ih _ (by have := hrev g; omega) hv
      else
        simp only [if_pos hval, if_neg hlt] at hv ⊢
        exact TriProp_of_triClean_fixpoint _ (triClean_eq_of_measure_ge _ (by omega))
    else
      simp only [if_neg hval] at hv ⊢
      exact absurd hv hval

/-- **`TriProp` for the triangle review itself.** -/
theorem TriProp_reviewTri (g : GPathM) (hv : isValid (reviewTri g) = true) :
    TriProp (reviewTri g) :=
  TriProp_reviewTriFuel measure_review_le _ g (Nat.le_succ _) hv

-- ============================================================
-- The transport: from `review` to `reviewTri`
-- ============================================================

/-! v85 named two lemmas to carry across to the triangle machine — *the owners
are global owners* and *symmetry*. Attacking them separates them completely.

* **The first transports, and is proved here.** `triClean` shrinks tables and
  leaves `gowners` and `current_step` alone, so the property survives every
  triangle sweep; and every branch of the loop that returns hands back a state
  whose last `review` established it. `OwnersGlobal_reviewTri` asks for nothing
  but validity.
* **The second is false for `reviewTri`, and it does not matter.** Plain
  `review` breaks symmetry — `lake exe cnfmap --symreview` counts 63 violations
  over 3.070 construction states at seed 1001 and 74 over 3.544 at seed 7777,
  against **0** for the symmetric machine of v64, so the detector is not blind.
  `reviewTri` is built on `review`, so symmetry cannot be transported to it.
  But the hypothesis was a detour: `TriProp` read in the direction it already
  has gives the shared entry without it.

What the triangle owes on its own account *is* true, and is proved below: the
sweep's test is symmetric in its two nodes, so `triClean` cannot break
symmetry (`OwnSymmetric_triClean`). It is the review that does. -/

/-- `triClean` only shrinks the tables. -/
theorem pruned_triClean (g : GPathM) : Pruned g (triClean g) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n' hn' := by
    simp only [triClean, List.mem_map] at hn'
    obtain ⟨n, hn, rfl⟩ := hn'
    exact ⟨n, hn, rfl, fun q hq => (List.mem_filter.mp hq).1, fun p hp => hp⟩

theorem pruned_reviewTriFuel : ∀ (fuel : Nat) (g : GPathM),
    Pruned g (reviewTriFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact Pruned.refl g
  | succ f ih =>
    intro g
    simp only [reviewTriFuel]
    if hval : isValid (review g) = true then
      if hlt : GPathM.measure (triClean (review g)) < GPathM.measure (review g) then
        simp only [if_pos hval, if_pos hlt]
        exact Pruned.trans (Pruned.trans (pruned_review g) (pruned_triClean _)) (ih _)
      else
        simp only [if_pos hval, if_neg hlt]
        exact pruned_review g
    else
      simp only [if_neg hval]
      exact pruned_review g

/-- **The triangle review never invents a global owner.** -/
theorem pruned_reviewTri (g : GPathM) : Pruned g (reviewTri g) :=
  pruned_reviewTriFuel _ g

/-- At a valid `review` fixpoint, the owners are global owners — v25 and F2.c,
restated in the shape the narrowing wants. -/
theorem OwnersGlobal_review (g : GPathM) (hv : isValid (review g) = true) :
    OwnersGlobal (review g) :=
  fun r n hn w hw hl0 hl => Candidates.owner_mem_gowners g hv r n hn w hw hl0 hl

/-- **And the triangle sweep keeps it.** It shrinks tables and touches neither
the global owners nor the step count. -/
theorem OwnersGlobal_triClean (g : GPathM) (h : OwnersGlobal g) :
    OwnersGlobal (triClean g) := by
  intro r n hn w hw hl0 hl
  rw [triClean_node?] at hn
  cases hn0 : g.node? r with
  | none => rw [hn0] at hn; exact absurd hn (by simp)
  | some n0 =>
    rw [hn0] at hn
    have heq : triMap g n0 = n := Option.some.inj (by simpa using hn)
    have hw0 : w ∈ n0.owners := by
      rw [← heq] at hw
      simp only [triMap, List.mem_filter] at hw
      exact hw.1
    exact h r n0 hn0 w hw0 hl0 hl

theorem OwnersGlobal_reviewTriFuel : ∀ (fuel : Nat) (g : GPathM), OwnersGlobal g →
    isValid (reviewTriFuel fuel g) = true → OwnersGlobal (reviewTriFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h _; exact h
  | succ f ih =>
    intro g _ hv
    simp only [reviewTriFuel] at hv ⊢
    if hval : isValid (review g) = true then
      have hg1 : OwnersGlobal (review g) := OwnersGlobal_review g hval
      if hlt : GPathM.measure (triClean (review g)) < GPathM.measure (review g) then
        simp only [if_pos hval, if_pos hlt] at hv ⊢
        exact ih _ (OwnersGlobal_triClean _ hg1) hv
      else
        simp only [if_pos hval, if_neg hlt] at hv ⊢
        exact hg1
    else
      simp only [if_neg hval] at hv ⊢
      exact absurd hv hval

/-- **The first lemma, transported.** No hypothesis but validity: the loop
always returns a state that a `review` has just cleaned, possibly narrowed by
triangle sweeps that cannot spoil it. -/
theorem OwnersGlobal_reviewTri (g : GPathM) (hv : isValid (reviewTri g) = true) :
    OwnersGlobal (reviewTri g) := by
  have hstep : ∀ (f : Nat) (h : GPathM), isValid (reviewTriFuel (f + 1) h) = true →
      OwnersGlobal (reviewTriFuel (f + 1) h) := by
    intro f h hvf
    simp only [reviewTriFuel] at hvf ⊢
    if hval : isValid (review h) = true then
      have hg1 : OwnersGlobal (review h) := OwnersGlobal_review h hval
      if hlt : GPathM.measure (triClean (review h)) < GPathM.measure (review h) then
        simp only [if_pos hval, if_pos hlt] at hvf ⊢
        exact OwnersGlobal_reviewTriFuel f _ (OwnersGlobal_triClean _ hg1) hvf
      else
        simp only [if_pos hval, if_neg hlt] at hvf ⊢
        exact hg1
    else
      simp only [if_neg hval] at hvf ⊢
      exact absurd hvf hval
  exact hstep (GPathM.measure g) g hv

/-- **The second lemma, for the half that owns it.** `commonAtAll` asks for a
node in *both* tables, which is symmetric in the two nodes, so a sweep that
drops `q` from `p`'s table drops `p` from `q`'s. The pass cannot break
symmetry; what breaks it is the coherence pass of `review`, which is why v64
exists. -/
theorem OwnSymmetric_triClean (g : GPathM) (h : Threaded.OwnSymmetric g) :
    Threaded.OwnSymmetric (triClean g) := by
  intro a na b nb hna hnb hb
  rw [triClean_node?] at hna hnb
  cases ha0 : g.node? a with
  | none => rw [ha0] at hna; exact absurd hna (by simp)
  | some na0 =>
    cases hb0 : g.node? b with
    | none => rw [hb0] at hnb; exact absurd hnb (by simp)
    | some nb0 =>
      rw [ha0] at hna
      rw [hb0] at hnb
      have hea : triMap g na0 = na := Option.some.inj (by simpa using hna)
      have heb : triMap g nb0 = nb := Option.some.inj (by simpa using hnb)
      rw [← hea] at hb
      simp only [triMap, List.mem_filter] at hb
      obtain ⟨hb1, hcom⟩ := hb
      -- the shared-entry test, read from `b`'s side
      simp only [commonAtAll, hb0, List.all_eq_true] at hcom
      rw [← heb]
      simp only [triMap, List.mem_filter]
      refine ⟨h a na0 b nb0 ha0 hb0 hb1, ?_⟩
      simp only [commonAtAll, ha0, List.all_eq_true]
      intro k hk
      obtain ⟨w, hw, hwp⟩ := List.any_eq_true.mp (hcom k hk)
      simp only [Bool.and_eq_true, beq_iff_eq] at hwp
      exact List.any_eq_true.mpr ⟨w, List.mem_of_elem_eq_true hwp.2,
        (Bool.and_eq_true _ _).mpr ⟨beq_iff_eq.mpr hwp.1,
          List.elem_eq_true_of_mem hw⟩⟩

-- ============================================================
-- P3's narrowing, assembled on the triangle machine
-- ============================================================

/-- The pins survive the triangle review, as they survive the plain one. -/
theorem gowners_compat_filterAllTri (g : GPathM) (reqs : List NodeId) :
    ∀ q ∈ (filterAllTri g reqs).gowners, Compat reqs q := fun q hq =>
  gowners_foldl_compat reqs g q
    ((pruned_reviewTri (reqs.foldl filterRequire g)).gowners_sub q hq)

/-- **P3's narrowing, with nothing left hanging.** On the author's own clause
filter with the triangle pass, every member of the pinned candidate has its
support inside the candidate at every step. The only hypothesis is that the
filter left a valid state. -/
theorem pinnedCandidate_selfSupporting_filterAllTri (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAllTri g reqs) = true)
    (r : PathNodeId) (n : PNodeM) (hn : (filterAllTri g reqs).node? r = some n)
    (p : PathNodeId) (hp : p ∈ n.owners)
    (np : PNodeM) (hnp : (filterAllTri g reqs).node? p = some np)
    (l : Int) (hl0 : 0 ≤ l) (hl : l < (filterAllTri g reqs).current_step) :
    ∃ w, w ∈ np.owners ∧ w ∈ n.owners ∧ Compat reqs w ∧ w.id.step = l :=
  pinnedCandidate_selfSupporting reqs (filterAllTri g reqs)
    (OwnersGlobal_reviewTri _ hv)
    (gowners_compat_filterAllTri g reqs)
    (TriProp_reviewTri _ hv)
    r n hn p hp np hnp l hl0 hl

-- ============================================================
-- P4, clause by clause: the reader's own candidate
-- ============================================================

/-! v82 measured that `PinNonEmpty g q` and `isValid (filterAll g [q.id])`
agree everywhere — 9.926 pins, not one exception — so P4 as it stood was a
restatement of what it was supposed to reduce. To find what P4 actually needs,
this section goes one level down.

`PinNonEmpty` asks for **some** non-empty fabric inside the pin. There is an
obvious candidate, and it is the reader's own: **`owners(q)`**, the table of
the node being pinned. The question becomes concrete — which of the nine
clauses of `Fabric` does that candidate satisfy?

`lake exe cnfmap --p4clause` answers it by measurement. On the symmetric
machine of v64, over 15.241 pins in 1.354 valid states with a choice
(seed 1001) and 22.085 pins (seed 7777):

| clause | failures |
|---|---|
| `gow`, `node`, `inS`, `sub`, `self`, `symm`, `support` | **0** |
| `up` (every entry carried by a parent inside the table) | 85 |
| `down` (… by a son) | 71 |

and **15.150 of 15.241 pins had the candidate be a fabric outright**, with no
narrowing at all. On the original machine `symm` fails 15 times and `support`
8, which is v63's asymmetry showing up exactly where v64 predicted.

So the seven that measure clean are proved here, and they are proved from the
author's own invariants — `OOS` (a node's owners at its own step are only
itself), the triangle of v69, the symmetry of v64, and the owners-are-global
of v25. **What is left is `up` and `down`, and they are not theorems**: the
campaign finds them failing at roughly half a percent of pins. That is P4's
real residue, and it is now named. -/

/-- The reader's own candidate for the pin `q`: the table of `q`, cut to the
steps the state actually has. -/
def StarS (g : GPathM) (qn : PNodeM) : PathNodeId → Prop :=
  fun p => p ∈ qn.owners ∧ 0 ≤ p.id.step ∧ p.id.step < g.current_step

/-- Its tables: what a member owns, inside the candidate. -/
def StarT (g : GPathM) (qn : PNodeM) : PathNodeId → PathNodeId → Prop :=
  fun p v => StarS g qn v ∧ ∃ np, g.node? p = some np ∧ v ∈ np.owners

/-- **The candidate agrees with the pin, for free.** `OOS` says the owners of
`q` at `q`'s own step are `q` and nothing else. -/
theorem StarS_compat (g : GPathM) (q : PathNodeId) (qn : PNodeM)
    (hq : g.node? q = some qn) (hoos : SelfOwn.OOS g) :
    ∀ p, StarS g qn p → Compat [q.id] p := by
  rintro p ⟨hp, _, _⟩ req hreq hstep
  have hid : qn.id = q := node?_id_eq g q qn hq
  rcases List.mem_cons.mp hreq with rfl | hnil
  · have := hoos qn (List.mem_of_find?_eq_some hq) p hp (by rw [hid]; exact hstep)
    rw [this, hid]
  · exact absurd hnil List.not_mem_nil

/-- A node owns itself: validity puts an owner at its own step, and `OOS` says
that owner is the node. -/
theorem self_mem_owners (g : GPathM) (hoos : SelfOwn.OOS g) (p : PathNodeId) (np : PNodeM)
    (hnp : g.node? p = some np) (hval : isValidNode g np = true)
    (hl0 : 0 ≤ p.id.step) (hl : p.id.step < g.current_step) :
    p ∈ np.owners := by
  have hid : np.id = p := node?_id_eq g p np hnp
  have hok := owners_ok_of_isValidNode g np hval
  have hk : p.id.step ∈ intRange 0 (g.current_step - 1) := mem_intRange hl0 (by omega)
  obtain ⟨w, hw, hws⟩ := List.any_eq_true.mp (List.all_eq_true.mp hok _ hk)
  have : w = np.id := hoos np (List.mem_of_find?_eq_some hnp) w hw (by rw [hid]; exact eq_of_beq hws)
  rw [← hid, ← this]; exact hw

/-- **Seven of the nine clauses, on the reader's candidate.** Bundled as the
fields of `Fabric` minus `up` and `down`, which is precisely what the campaign
finds failing. -/
structure PreFabric (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) : Prop where
  gow : ∀ p, S p → p ∈ g.gowners
  node : ∀ p, S p → (g.node? p).isSome = true
  inS : ∀ p v, S p → T p v → S v
  symm : ∀ p v, S p → T p v → T v p
  self : ∀ p, S p → T p p
  sub : ∀ p n, g.node? p = some n → S p → ∀ v, T p v → v ∈ n.owners
  support : ∀ p, S p → ∀ l, 0 ≤ l → l < g.current_step → ∃ v, T p v ∧ v.id.step = l

/-- What `PreFabric` is missing, and only that. -/
theorem Fabric_of_PreFabric (g : GPathM) (S : PathNodeId → Prop)
    (T : PathNodeId → PathNodeId → Prop) (h : PreFabric g S T)
    (hup : ∀ p n, g.node? p = some n → S p → p.parent_id ≠ none →
      ∀ v, T p v → ∃ c ∈ n.parents, T p c ∧ T c v)
    (hdown : ∀ p, S p → p.id.step ≠ g.current_step - 1 →
      ∀ v, T p v → ∃ c m, g.node? c = some m ∧ p ∈ m.parents ∧ T p c ∧ T c v) :
    Fabric g S T :=
  { gow := h.gow, node := h.node, inS := h.inS, symm := h.symm, self := h.self,
    sub := h.sub, support := h.support, up := hup, down := hdown }

/-- **The reader's candidate satisfies the seven.** Each one comes from an
invariant the author's machine already maintains:

* `gow` — the owners of a survivor are global owners (v25, F2.c);
* `node` — and global owners are nodes (v25);
* `symm` — the symmetric review of v64;
* `self` — `OOS` plus validity;
* `support` — **the triangle of v69**: two nodes that own each other share an
  entry at every step, and here the two are `q` and the member;
* `inS`, `sub` — by construction. -/
theorem PreFabric_star (g : GPathM) (q : PathNodeId) (qn : PNodeM)
    (hq : g.node? q = some qn)
    (hown : OwnersGlobal g)
    (hgn : GownersNodes.GN g)
    (hoos : SelfOwn.OOS g)
    (hsym : Threaded.OwnSymmetric g)
    (htri : TriProp g)
    (hnodeval : ∀ p n, g.node? p = some n → isValidNode g n = true) :
    PreFabric g (StarS g qn) (StarT g qn) := by
  have hnode : ∀ p, StarS g qn p → (g.node? p).isSome = true := by
    rintro p ⟨hp, hl0, hl⟩
    exact (GownersNodes.hasNode_iff g p).mp (hgn p (hown q qn hq p hp hl0 hl))
  refine { gow := ?_, node := hnode, inS := ?_, symm := ?_, self := ?_, sub := ?_,
           support := ?_ }
  · rintro p ⟨hp, hl0, hl⟩; exact hown q qn hq p hp hl0 hl
  · rintro p v _ ⟨hv, _⟩; exact hv
  · rintro p v hp ⟨hv, np, hnp, hvp⟩
    obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp (hnode v hv)
    exact ⟨hp, nv, hnv, hsym p np v nv hnp hnv hvp⟩
  · intro p hp
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp (hnode p hp)
    exact ⟨hp, np, hnp,
      self_mem_owners g hoos p np hnp (hnodeval p np hnp) hp.2.1 hp.2.2⟩
  · rintro p n hn _ v ⟨_, np, hnp, hvp⟩
    rw [hn] at hnp
    exact (Option.some.inj hnp) ▸ hvp
  · intro p hp l hl0 hl
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp (hnode p hp)
    obtain ⟨w, hwq, hwp, hws⟩ := htri q qn p np hq hnp hp.1 l hl0 hl
    exact ⟨w, ⟨⟨hwq, by rw [hws]; exact hl0, by rw [hws]; exact hl⟩, np, hnp, hwp⟩, hws⟩

/-- **P4, reduced to `up` and `down`.** With the two carrying clauses supplied,
the reader's own candidate is a fabric inside the pin, so the pick leaves the
state valid. The campaign measures `up` and `down` failing at about half a
percent of pins, so this is a reduction and not a proof of `PickSome`. -/
theorem PinNonEmpty_of_star (g : GPathM) (q : PathNodeId) (qn : PNodeM)
    (hq : g.node? q = some qn)
    (hl0 : 0 ≤ q.id.step) (hl : q.id.step < g.current_step)
    (hown : OwnersGlobal g) (hgn : GownersNodes.GN g) (hoos : SelfOwn.OOS g)
    (hsym : Threaded.OwnSymmetric g) (htri : TriProp g)
    (hnodeval : ∀ p n, g.node? p = some n → isValidNode g n = true)
    (hup : ∀ p n, g.node? p = some n → StarS g qn p → p.parent_id ≠ none →
      ∀ v, StarT g qn p v → ∃ c ∈ n.parents, StarT g qn p c ∧ StarT g qn c v)
    (hdown : ∀ p, StarS g qn p → p.id.step ≠ g.current_step - 1 →
      ∀ v, StarT g qn p v → ∃ c m, g.node? c = some m ∧ p ∈ m.parents ∧
        StarT g qn p c ∧ StarT g qn c v) :
    PinNonEmpty g q := by
  have hpre := PreFabric_star g q qn hq hown hgn hoos hsym htri hnodeval
  have hfab : Fabric g (StarS g qn) (StarT g qn) :=
    Fabric_of_PreFabric g _ _ hpre hup hdown
  have hqs : StarS g qn q :=
    ⟨self_mem_owners g hoos q qn hq (hnodeval q qn hq) hl0 hl, hl0, hl⟩
  exact ⟨q, StarS g qn, StarT g qn, hfab, StarS_compat g q qn hq hoos, hqs⟩

-- ============================================================
-- `up` at the level of the tables: a theorem, not a residue
-- ============================================================

/-! v87 left `up` and `down` failing at about 2% of pins and called that P4's
residue. Measuring **why** they fail changes the picture completely
(`cnfmap --p4why`, seed 31337, triangle machine, 27.564.473 `up` pairs and
27.443.139 `down` pairs):

| why | `up` | `down` |
|---|---|---|
| carried inside the candidate | 27.560.426 | 27.439.571 |
| **no parent (son) carries it at all** | **0** | **0** |
| a parent (son) carries it, but never one inside `owners(q)` | 4.047 | 3.568 |

So the clause never fails *at the level of the tables*. It fails only
**relative to the pin**: the carrier exists and lies outside `owners(q)`.

The table-level half is proved here, and the proof is short once one sees the
right lemma: **an owner sitting one step below a node is a parent of it.** That
is the coherence pass plus `OOS` — the parents' union at the parents' own step
is exactly the parents, because each parent's table at its own step holds
nothing but itself. With it, the triangle supplies the carrier: `p` and `v` own
each other, so they share an entry `w` one step below `p`; `w` is therefore a
parent of `p`, it is in `p`'s table, and symmetry puts `v` in `w`'s.

What is left is exactly the relative half, and that is a condition on the
**triple** `(q, p, v)` — the fourth rung of the ladder v69 climbed to the
third. Binary tables cannot express it; that is a design question, not a proof
one, and §`p4why` measures its size: 0,015% of pairs. -/

/-- Coherence with the parents, in `intersectOwners`' own sense — what
`review_owners_coherent_parents` leaves at the fixpoint. -/
def CoherentParents (g : GPathM) : Prop :=
  ∀ p n, g.node? p = some n → 1 ≤ p.id.step → p.id.step < g.current_step →
    intersectOwners n.owners (unionOwnersOf g n.parents) = n.owners

/-- The invariants a valid fixpoint carries, bundled so the statements below
stay readable. Every field is a named property of the machine. -/
structure TableCtx (g : GPathM) : Prop where
  /-- A node's owners at its own step are only itself (`SelfOwn.OOS`). -/
  oos : SelfOwn.OOS g
  /-- The coherence pass reached its fixpoint. -/
  coh : CoherentParents g
  /-- Tables are symmetric (v64). -/
  sym : Threaded.OwnSymmetric g
  /-- The triangle holds (v69, and `TriProp_reviewTri`). -/
  tri : TriProp g
  /-- Every node in range owns itself (`self_mem_owners`). -/
  selfown : ∀ p n, g.node? p = some n → 0 ≤ p.id.step → p.id.step < g.current_step →
    p ∈ n.owners
  /-- Parents sit one step below. -/
  level : ∀ p n, g.node? p = some n → ∀ c ∈ n.parents, c.id.step = p.id.step - 1
  /-- And they are nodes. -/
  parnode : ∀ p n, g.node? p = some n → ∀ c ∈ n.parents, (g.node? c).isSome = true
  /-- A non-root node has one (`isValidNode`). -/
  hasparent : ∀ p n, g.node? p = some n → 1 ≤ p.id.step → n.parents ≠ []
  /-- The same three facts for the sons. -/
  cohSons : ∀ p n, g.node? p = some n → 0 ≤ p.id.step → p.id.step < g.current_step - 1 →
    intersectOwners n.owners (unionOwnersOf g n.sons) = n.owners
  sonlevel : ∀ p n, g.node? p = some n → ∀ c ∈ n.sons, c.id.step = p.id.step + 1
  sonnode : ∀ p n, g.node? p = some n → ∀ c ∈ n.sons, (g.node? c).isSome = true
  hasson : ∀ p n, g.node? p = some n → p.id.step < g.current_step - 1 → n.sons ≠ []
  /-- Sons and parents mirror each other (`Sons.SMP`). -/
  smp : ∀ p n c m, g.node? p = some n → g.node? c = some m → c ∈ n.sons → p ∈ m.parents

private theorem mem_unionFold_inv (g : GPathM) :
    ∀ (ids acc : List PathNodeId) (q : PathNodeId),
      q ∈ ids.foldl (fun acc pid =>
        match g.node? pid with
        | some p => acc ++ p.owners
        | none => acc) acc →
      q ∈ acc ∨ ∃ pid ∈ ids, ∃ m, g.node? pid = some m ∧ q ∈ m.owners := by
  intro ids
  induction ids with
  | nil => intro acc q hq; exact Or.inl hq
  | cons id rest ih =>
    intro acc q hq
    simp only [List.foldl_cons] at hq
    rcases ih _ q hq with h | ⟨pid, hpid, m, hm, hqm⟩
    · cases hn : g.node? id with
      | none => simp only [hn] at h; exact Or.inl h
      | some m =>
        simp only [hn] at h
        rcases List.mem_append.mp h with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ⟨id, List.mem_cons_self, m, hn, h2⟩
    · exact Or.inr ⟨pid, List.mem_cons_of_mem _ hpid, m, hm, hqm⟩

theorem exists_owner_of_mem_unionOwnersOf (g : GPathM) (ids : List PathNodeId)
    (q : PathNodeId) (hq : q ∈ unionOwnersOf g ids) :
    ∃ pid ∈ ids, ∃ m, g.node? pid = some m ∧ q ∈ m.owners := by
  rcases mem_unionFold_inv g ids [] q hq with h | h
  · exact absurd h List.not_mem_nil
  · exact h

/-- **An owner one step below a node is a parent of it.** The parents' union
has an entry at the parents' own step — each parent owns itself — so coherence
forces the owner into the union; and `OOS` says an entry of a parent's table at
that parent's own step *is* that parent. -/
theorem owner_pred_is_parent (g : GPathM) (ctx : TableCtx g)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n) (hp0 : 1 ≤ p.id.step)
    (hptop : p.id.step < g.current_step)
    (v : PathNodeId) (hv : v ∈ n.owners) (hvs : v.id.step = p.id.step - 1) :
    v ∈ n.parents := by
  -- a parent exists, is a node, and owns itself
  have hne := ctx.hasparent p n hn hp0
  obtain ⟨c₀, hc₀⟩ : ∃ c, c ∈ n.parents := by
    cases h : n.parents with
    | nil => exact absurd h hne
    | cons a as => exact ⟨a, by simp⟩
  obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp (ctx.parnode p n hn c₀ hc₀)
  have hc₀s : c₀.id.step = p.id.step - 1 := ctx.level p n hn c₀ hc₀
  have hc₀own : c₀ ∈ m₀.owners :=
    ctx.selfown c₀ m₀ hm₀ (by rw [hc₀s]; omega) (by rw [hc₀s]; omega)
  have hc₀u : c₀ ∈ unionOwnersOf g n.parents :=
    mem_unionOwnersOf g n.parents c₀ m₀ c₀ hc₀ hm₀ hc₀own
  -- so the union has an entry at that step
  have hentry : hasStepEntry (unionOwnersOf g n.parents) v.id.step = true := by
    refine List.any_eq_true.mpr ⟨c₀, hc₀u, ?_⟩
    exact beq_iff_eq.mpr (by rw [ctx.level p n hn c₀ hc₀, hvs])
  -- coherence then keeps `v` only if it is in the union
  have hfil : ∀ x ∈ n.owners,
      (!hasStepEntry (unionOwnersOf g n.parents) x.id.step ||
        (unionOwnersOf g n.parents).contains x) = true :=
    List.filter_eq_self.mp (ctx.coh p n hn hp0 hptop)
  have hvu : v ∈ unionOwnersOf g n.parents := by
    have := hfil v hv
    simp only [hentry, Bool.not_true, Bool.false_or] at this
    exact List.mem_of_elem_eq_true this
  -- and an entry of a parent's table at that parent's own step is the parent
  obtain ⟨c, hc, mc, hmc, hvc⟩ := exists_owner_of_mem_unionOwnersOf g n.parents v hvu
  have hcid : mc.id = c := node?_id_eq g c mc hmc
  have : v = mc.id :=
    ctx.oos mc (List.mem_of_find?_eq_some hmc) v hvc
      (by rw [hcid, ctx.level p n hn c hc, hvs])
  rw [this, hcid]; exact hc

/-- **`up` at the level of the tables.** Every entry of a node's table is
carried by a **parent** of that node which is itself in the table — no
hypothesis about any pin. Measured at 0 failures over 27.564.473 pairs; here it
is a theorem. -/
theorem table_up (g : GPathM) (ctx : TableCtx g)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n)
    (hp0 : 1 ≤ p.id.step) (hptop : p.id.step < g.current_step)
    (v : PathNodeId) (hv : v ∈ n.owners) (nv : PNodeM) (hnv : g.node? v = some nv) :
    ∃ c ∈ n.parents, ∃ mc, g.node? c = some mc ∧ c ∈ n.owners ∧ v ∈ mc.owners := by
  -- the triangle: `p` and `v` share an entry one step below `p`
  obtain ⟨w, hwn, hwv, hws⟩ :=
    ctx.tri p n v nv hn hnv hv (p.id.step - 1) (by omega) (by omega)
  have hwpar : w ∈ n.parents := owner_pred_is_parent g ctx p n hn hp0 hptop w hwn hws
  obtain ⟨mw, hmw⟩ := Option.isSome_iff_exists.mp (ctx.parnode p n hn w hwpar)
  exact ⟨w, hwpar, mw, hmw, hwn, ctx.sym v nv w mw hnv hmw hwv⟩

/-- **An owner one step above a node is a son of it** — the mirror of
`owner_pred_is_parent`, with the sons' coherence pass in place of the
parents'. -/
theorem owner_succ_is_son (g : GPathM) (ctx : TableCtx g)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n)
    (hp0 : 0 ≤ p.id.step) (hptop : p.id.step < g.current_step - 1)
    (v : PathNodeId) (hv : v ∈ n.owners) (hvs : v.id.step = p.id.step + 1) :
    v ∈ n.sons := by
  have hne := ctx.hasson p n hn hptop
  obtain ⟨c₀, hc₀⟩ : ∃ c, c ∈ n.sons := by
    cases h : n.sons with
    | nil => exact absurd h hne
    | cons a as => exact ⟨a, by simp⟩
  obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp (ctx.sonnode p n hn c₀ hc₀)
  have hc₀u : c₀ ∈ unionOwnersOf g n.sons :=
    mem_unionOwnersOf g n.sons c₀ m₀ c₀ hc₀ hm₀
      (ctx.selfown c₀ m₀ hm₀ (by rw [ctx.sonlevel p n hn c₀ hc₀]; omega)
        (by rw [ctx.sonlevel p n hn c₀ hc₀]; omega))
  have hentry : hasStepEntry (unionOwnersOf g n.sons) v.id.step = true := by
    refine List.any_eq_true.mpr ⟨c₀, hc₀u, ?_⟩
    exact beq_iff_eq.mpr (by rw [ctx.sonlevel p n hn c₀ hc₀, hvs])
  have hfil : ∀ x ∈ n.owners,
      (!hasStepEntry (unionOwnersOf g n.sons) x.id.step ||
        (unionOwnersOf g n.sons).contains x) = true :=
    List.filter_eq_self.mp (ctx.cohSons p n hn hp0 hptop)
  have hvu : v ∈ unionOwnersOf g n.sons := by
    have := hfil v hv
    simp only [hentry, Bool.not_true, Bool.false_or] at this
    exact List.mem_of_elem_eq_true this
  obtain ⟨c, hc, mc, hmc, hvc⟩ := exists_owner_of_mem_unionOwnersOf g n.sons v hvu
  have hcid : mc.id = c := node?_id_eq g c mc hmc
  have : v = mc.id :=
    ctx.oos mc (List.mem_of_find?_eq_some hmc) v hvc
      (by rw [hcid, ctx.sonlevel p n hn c hc, hvs])
  rw [this, hcid]; exact hc

/-- **`down` at the level of the tables.** Measured at 0 failures over
27.443.139 pairs; here it is a theorem. -/
theorem table_down (g : GPathM) (ctx : TableCtx g)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n)
    (hp0 : 0 ≤ p.id.step) (hptop : p.id.step < g.current_step - 1)
    (v : PathNodeId) (hv : v ∈ n.owners) (nv : PNodeM) (hnv : g.node? v = some nv) :
    ∃ c ∈ n.sons, ∃ mc, g.node? c = some mc ∧ p ∈ mc.parents ∧ c ∈ n.owners ∧
      v ∈ mc.owners := by
  obtain ⟨w, hwn, hwv, hws⟩ :=
    ctx.tri p n v nv hn hnv hv (p.id.step + 1) (by omega) (by omega)
  have hwson : w ∈ n.sons := owner_succ_is_son g ctx p n hn hp0 hptop w hwn hws
  obtain ⟨mw, hmw⟩ := Option.isSome_iff_exists.mp (ctx.sonnode p n hn w hwson)
  exact ⟨w, hwson, mw, hmw, ctx.smp p n w mw hn hmw hwson, hwn,
    ctx.sym v nv w mw hnv hmw hwv⟩

/-- **The whole valid state is a fabric.** Members: the nodes whose step is in
range. Tables: their own owners. Every clause is a theorem — the seven of v87,
plus `up` and `down` above — so the structure P1/P2 build and preserve is not
merely *some* fabric: at a fixpoint of the triangle machine the state **is**
one, entire.

That is what the pin has to cut into, and it says exactly where P4's difficulty
lives: **not in the clauses**, which hold on the nose, but in keeping a witness
for each of them *inside* `owners(q)` once the pin restricts the members. -/
theorem Fabric_whole (g : GPathM) (ctx : TableCtx g)
    (hown : OwnersGlobal g) (hgn : GownersNodes.GN g)
    (hnodeval : ∀ p n, g.node? p = some n → isValidNode g n = true)
    (hrootstep : ∀ p : PathNodeId, p.parent_id ≠ none → 1 ≤ p.id.step) :
    Fabric g (fun p => (g.node? p).isSome = true ∧ 0 ≤ p.id.step ∧
                       p.id.step < g.current_step)
             (fun p v => ((g.node? v).isSome = true ∧ 0 ≤ v.id.step ∧
                          v.id.step < g.current_step) ∧
                         ∃ np, g.node? p = some np ∧ v ∈ np.owners) := by
  -- an in-range entry of any table is itself a node
  have hentnode : ∀ p n, g.node? p = some n → ∀ v ∈ n.owners,
      0 ≤ v.id.step → v.id.step < g.current_step → (g.node? v).isSome = true := by
    intro p n hn v hv hl0 hl
    exact (GownersNodes.hasNode_iff g v).mp (hgn v (hown p n hn v hv hl0 hl))
  refine { gow := ?_, node := ?_, inS := ?_, symm := ?_, self := ?_, sub := ?_,
           support := ?_, up := ?_, down := ?_ }
  · rintro p ⟨hp, hl0, hl⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hp
    exact hown p n hn p (ctx.selfown p n hn hl0 hl) hl0 hl
  · rintro p ⟨hp, _, _⟩; exact hp
  · rintro p v _ ⟨hv, _⟩; exact hv
  · rintro p v hp ⟨hv, np, hnp, hvp⟩
    obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp hv.1
    exact ⟨hp, nv, hnv, ctx.sym p np v nv hnp hnv hvp⟩
  · rintro p hp
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hp.1
    exact ⟨hp, n, hn, ctx.selfown p n hn hp.2.1 hp.2.2⟩
  · rintro p n hn _ v ⟨_, np, hnp, hvp⟩
    rw [hn] at hnp; exact (Option.some.inj hnp) ▸ hvp
  · rintro p hp l hl0 hl
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hp.1
    have hok := owners_ok_of_isValidNode g n (hnodeval p n hn)
    have hk : l ∈ intRange 0 (g.current_step - 1) := mem_intRange hl0 (by omega)
    obtain ⟨w, hw, hws⟩ := List.any_eq_true.mp (List.all_eq_true.mp hok l hk)
    have hwl : w.id.step = l := eq_of_beq hws
    exact ⟨w, ⟨⟨hentnode p n hn w hw (by rw [hwl]; exact hl0) (by rw [hwl]; exact hl),
      by rw [hwl]; exact hl0, by rw [hwl]; exact hl⟩, n, hn, hw⟩, hwl⟩
  · rintro p n hn hp hpr v ⟨hv, np, hnp, hvp⟩
    rw [hn] at hnp
    have hvn : v ∈ n.owners := (Option.some.inj hnp) ▸ hvp
    obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp hv.1
    obtain ⟨c, hc, mc, hmc, hcn, hvc⟩ :=
      table_up g ctx p n hn (hrootstep p hpr) hp.2.2 v hvn nv hnv
    have hcs : c.id.step = p.id.step - 1 := ctx.level p n hn c hc
    have hp1 : 1 ≤ p.id.step := hrootstep p hpr
    have hplt : p.id.step < g.current_step := hp.2.2
    refine ⟨c, hc, ⟨⟨?_, by rw [hcs]; omega, by rw [hcs]; omega⟩, n, hn, hcn⟩,
      ⟨hv, mc, hmc, hvc⟩⟩
    exact hentnode p n hn c hcn (by rw [hcs]; omega) (by rw [hcs]; omega)
  · rintro p hp hptop v ⟨hv, np, hnp, hvp⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hp.1
    rw [hn] at hnp
    have hvn : v ∈ n.owners := (Option.some.inj hnp) ▸ hvp
    obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp hv.1
    have hlt : p.id.step < g.current_step - 1 := by
      have := hp.2.2; omega
    obtain ⟨c, hc, mc, hmc, hpar, hcn, hvc⟩ :=
      table_down g ctx p n hn hp.2.1 hlt v hvn nv hnv
    have hcs : c.id.step = p.id.step + 1 := ctx.sonlevel p n hn c hc
    have hp0 : 0 ≤ p.id.step := hp.2.1
    have hplt : p.id.step < g.current_step := hp.2.2
    refine ⟨c, mc, hmc, hpar, ⟨⟨?_, by rw [hcs]; omega, by rw [hcs]; omega⟩, n, hn, hcn⟩,
      ⟨hv, mc, hmc, hvc⟩⟩
    exact hentnode p n hn c hcn (by rw [hcs]; omega) (by rw [hcs]; omega)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.Fabric_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_addNode

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.Fabric_initSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_initSeed

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.Fabric_of_grown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_of_grown

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.Fabric_join_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_join_left

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.Fabric_join_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_join_right

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.Fabric_core' does not depend on any axioms -/
#guard_msgs in
#print axioms Fabric_core

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.FabricAt_filterAll_of_PinReaches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FabricAt_filterAll_of_PinReaches

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.isValid_filterAll_of_PinNonEmpty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_filterAll_of_PinNonEmpty

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.PickSome_of_PinNonEmpty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PickSome_of_PinNonEmpty

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.Inhabited_of_PinNonEmpty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_PinNonEmpty

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.pinnedCandidate_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinnedCandidate_covers

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.gowners_foldl_compat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gowners_foldl_compat

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.pinnedCandidate_selfSupporting' does not depend on any axioms -/
#guard_msgs in
#print axioms pinnedCandidate_selfSupporting

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.TriProp_of_triClean_fixpoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TriProp_of_triClean_fixpoint

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.TriProp_reviewTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TriProp_reviewTri

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.gowners_compat_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gowners_compat_filterAll

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.FabricAt_addNode_new' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FabricAt_addNode_new

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.isValid_readStepSym_addNode_new' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_readStepSym_addNode_new

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.OwnersGlobal_reviewTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnersGlobal_reviewTri

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.OwnSymmetric_triClean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_triClean

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.pruned_reviewTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pruned_reviewTri

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.pinnedCandidate_selfSupporting_filterAllTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinnedCandidate_selfSupporting_filterAllTri

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.StarS_compat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms StarS_compat

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.self_mem_owners' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms self_mem_owners

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.PreFabric_star' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PreFabric_star

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.PinNonEmpty_of_star' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PinNonEmpty_of_star

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.owner_pred_is_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owner_pred_is_parent

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.table_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms table_up

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.table_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms table_down

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.Fabric_whole' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fabric_whole

end AbsSat.GraphPath.Model.FabricAdd
