-- lean_project/AbsSat/GraphPath/Model/FabricAdd.lean
import AbsSat.GraphPath.Model.Fabric
import AbsSat.GraphPath.Model.Reader

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

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.FabricAt_addNode_new' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FabricAt_addNode_new

/-- info: 'AbsSat.GraphPath.Model.FabricAdd.isValid_readStepSym_addNode_new' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_readStepSym_addNode_new

end AbsSat.GraphPath.Model.FabricAdd
