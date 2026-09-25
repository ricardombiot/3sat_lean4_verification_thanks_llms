-- lean/improves_bin/AbsSatBin/GraphPath/Model/L6Up.lean
import AbsSatBin.GraphPath.Model.Up

/-!
**L6's `up` case, reduced to a single statement.**

`upFiltering g reqs d title` is `up (filterAll g reqs) d title`, i.e. three
things in sequence: a fold of `filterRequire`, then `review`, then `addNode`.
This module proves the first and the third, leaving exactly the second.

* **`filterRequire`** rewrites `gowners` only, and `Supported` never reads it:
  `Supported_filterRequire` is `Iff.rfl`. Free.
* **`addNode`** is `SupportedG_addNode`, proved here by an explicit
  chain-extension construction (`ChainG_addNode`): take the base graph's chain
  and select the new node at the new top step. Below the new step nothing
  moved; at the new step the single new node is forced.
* **`review`** is not proved, and it is the whole of L6.

**Why `SupportedG` and not `Supported`.** `addNode` hands the new node exactly
`gowners` as its owners. So for the new node to *co-own* an existing chain,
that chain must live inside `gowners`. `ChainG` carries that condition, and
`SupportedG`/`InhabitedG` are the two forms in which it has to travel: a node
needs a chain through it, and the new node needs *some* chain to attach to.
`InhabitedG` is the second half of L6 (`valid ⇒ denot ≠ ∅`), so the two halves
genuinely feed each other rather than being independent goals.

This condition is not preserved by `filterRequire` in isolation — pruning
`gowners` can drop a chain node — which is precisely why the induction must be
run over the whole `upFiltering` composite and not step by step, and why
`review` is where everything lands.

**The remaining hole, stated once:**

    SupportedG g → SupportedG (review g)        (with InhabitedG alongside)

That is the same sentence as L2's ⊇ direction and as L3's ⊇ direction. All
three of the bridge's open ends are this one statement.

**Empirical status.** `lake exe l6search` now inspects every state the machine
holds at every step, not just the last: 1,680 states over 150 synthetic maps
with arbitrary backward, step-distinct requirements and no 3SAT structure.
Every valid one had a complete co-owned chain.
-/

namespace AbsSatBin.GraphPath.Model
open AbsSatBin.Utils.Alias
open GPathM

/-- Decidable case split on `Int` equality. `by_cases` routes through
`Classical.choice`, which would widen every axiom closure in this file. -/
theorem int_eq_or_ne (a b : Int) : a = b ∨ a ≠ b := by
  cases h : (a == b) with
  | true => exact Or.inl (eq_of_beq h)
  | false =>
    refine Or.inr (fun heq => ?_)
    rw [heq, beq_iff_eq.mpr (rfl : b = b)] at h
    exact Bool.noConfusion h

/-- A chain, together with the extra condition that every node it selects is a
*global* owner. `addNode` hands the new node exactly `gowners` as its owners,
so the new node can co-own a chain only if the chain lives inside `gowners`. -/
def ChainG (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  IsChain g sel ∧ PairwiseOwned g sel ∧
    ∀ k, 0 ≤ k → k < g.current_step → sel k ∈ g.gowners

def SupportedG (g : GPathM) : Prop :=
  ∀ pid n, g.node? pid = some n → ∃ sel, ChainG g sel ∧ sel pid.id.step = pid

def InhabitedG (g : GPathM) : Prop := ∃ sel, ChainG g sel

/-- `filterRequire` rewrites `gowners` only, and `Supported` never reads it. -/
theorem Supported_filterRequire (g : GPathM) (req : NodeId) :
    Supported (filterRequire g req) ↔ Supported g := Iff.rfl

/-- **The identifier the chain continues into.** With a window of two the row is
a single node and this is that node; with three, which node of the row the chain
enters is decided by the branch it came up — by its own last pick. -/
def extendPid (g : GPathM) (d : NodeId) (sel : Int → PathNodeId) : PathNodeId :=
  if 0 < g.current_step then shiftPid (sel (g.current_step - 1)) d
  else { id := d, parent_id := none, gparent_id := none }

theorem extendPid_mapId (g : GPathM) (d : NodeId) (sel : Int → PathNodeId) :
    (extendPid g d sel).id = d := by unfold extendPid; split <;> rfl

def extend (g : GPathM) (d : NodeId) (sel : Int → PathNodeId) : Int → PathNodeId :=
  fun k => if k = g.current_step then extendPid g d sel else sel k

theorem extend_top (g : GPathM) (d : NodeId) (sel : Int → PathNodeId) :
    extend g d sel g.current_step = extendPid g d sel := by simp [extend]

theorem extend_below (g : GPathM) (d : NodeId) (sel : Int → PathNodeId)
    (k : Int) (h : k < g.current_step) : extend g d sel k = sel k := by
  simp [extend, Int.ne_of_lt h]

/-- `find?` against an identifier answers with that identifier. -/
theorem find?_beq_self {α : Type} [BEq α] [LawfulBEq α] (l : List α) (a : α) (h : a ∈ l) :
    l.find? (fun x => x == a) = some a := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b bs ih =>
    rw [List.find?_cons]
    cases hb : (b == a) with
    | true => simp only; rw [eq_of_beq hb]
    | false =>
      simp only
      refine ih ?_
      rcases List.mem_cons.mp h with rfl | h'
      · rw [beq_self_eq_true] at hb; exact absurd hb (by simp)
      · exact h'

/-- **Looking up a node of the new row**, given only that no old node carries its
identifier. -/
theorem addNode_node?_new_of (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (pid : PathNodeId) (hpid : pid ∈ newRowIds g d forb) (hnone : g.node? pid = none) :
    (addNode g d title forb).node? pid = some (rowNode g d title pid) := by
  have hp : (fun x : PNodeM => (upMap g d forb x).id == pid)
      = (fun x : PNodeM => x.id == pid) := by funext x; rw [upMap_id]
  have hrow : (newRow g d title forb).find? (fun x : PNodeM => x.id == pid)
      = some (rowNode g d title pid) := by
    show ((newRowIds g d forb).map (rowNode g d title)).find? (fun x : PNodeM => x.id == pid) = _
    rw [List.find?_map, Function.comp_def]
    show ((newRowIds g d forb).find? (fun q => q == pid)).map (rowNode g d title) = _
    rw [find?_beq_self _ pid hpid]
    rfl
  have hnodes : g.nodes.find? (fun x : PNodeM => x.id == pid) = none := hnone
  simp only [node?, addNode_nodes, List.find?_append, List.find?_map, Function.comp_def, hp,
    hnodes, Option.map_none, Option.none_or]
  exact hrow

/-- **Looking up a node of the new row.** -/
theorem addNode_node?_new (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (pid : PathNodeId) (hpid : pid ∈ newRowIds g d forb) :
    (addNode g d title forb).node? pid = some (rowNode g d title pid) := by
  refine addNode_node?_new_of g d title forb pid hpid ?_
  show g.nodes.find? (fun x : PNodeM => x.id == pid) = none
  rw [List.find?_eq_none]
  intro x hx hbeq
  have hxid : x.id = pid := eq_of_beq hbeq
  have := hbelow x hx
  rw [hxid, mapId_of_mem_newRowIds g d forb pid hpid, hd] at this
  omega

theorem mem_line_of_node? (g : GPathM) (pid : PathNodeId) (n : PNodeM)
    (hn : g.node? pid = some n) (k : Int) (hstep : pid.id.step = k) :
    pid ∈ (g.line k).map (·.id) := by
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq g pid n hn
  have : n ∈ g.line k := by
    simp only [line, List.mem_filter]
    exact ⟨hmem, by rw [hid, hstep]; exact beq_iff_eq.mpr rfl⟩
  have := List.mem_map_of_mem (f := fun m : PNodeM => m.id) this
  rwa [hid] at this

/-- **The identifier the chain continues into is a candidate of the row.** -/
theorem extendPid_mem_shiftRowIds (g : GPathM) (d : NodeId) (sel : Int → PathNodeId)
    (hchain : IsChain g sel) : extendPid g d sel ∈ shiftRowIds g d := by
  unfold extendPid
  split
  · rename_i hpos
    obtain ⟨hsome, hstep⟩ := hchain.1 (g.current_step - 1) (by omega) (by omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    have hmem : sel (g.current_step - 1) ∈ (g.line (g.current_step - 1)).map (·.id) :=
      mem_line_of_node? g _ n hn (g.current_step - 1) hstep
    unfold shiftRowIds
    rw [if_pos hpos]
    refine (mem_dedupPids _ _).mpr (List.mem_map_of_mem ?_)
    unfold newParents
    rw [if_pos hpos]
    exact hmem
  · rename_i hnp
    unfold shiftRowIds
    rw [if_neg hnp]
    exact List.mem_singleton.mpr rfl

/-- **And a node of the row, unless the extension is prohibited.** Bin map: `lean_project`
had no side condition — every chain of the base continued into the row. Here a chain whose
extension is the window `(L1=0, L2=0, L3=0)` does not (error 4 of the Julia report). -/
theorem extendPid_mem_newRowIds (g : GPathM) (d : NodeId) (forb : PathNodeId → Bool)
    (sel : Int → PathNodeId) (hchain : IsChain g sel) (hf : forb (extendPid g d sel) = false) :
    extendPid g d sel ∈ newRowIds g d forb :=
  (mem_newRowIds g d forb _).mpr ⟨extendPid_mem_shiftRowIds g d sel hchain, hf⟩

/-- **And the chain's last pick is one of its parents.** -/
theorem lastPick_mem_rowParents (g : GPathM) (d : NodeId) (sel : Int → PathNodeId)
    (hpos : 0 < g.current_step) (hchain : IsChain g sel) :
    sel (g.current_step - 1) ∈ rowParents g d (extendPid g d sel) := by
  obtain ⟨hsome, hstep⟩ := hchain.1 (g.current_step - 1) (by omega) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hmem : sel (g.current_step - 1) ∈ newParents g := by
    unfold newParents; rw [if_pos hpos]
    exact mem_line_of_node? g _ n hn (g.current_step - 1) hstep
  have := mem_rowParents_of_mem_newParents g d _ hmem
  unfold extendPid
  rw [if_pos hpos]
  exact this

/-- Self-ownership, read along a chain. -/
theorem selfOwned_pointwise (g : GPathM)
    (hso : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (sel : Int → PathNodeId) (hchain : IsChain g sel) :
    ∀ k, 0 ≤ k → k < g.current_step → sel k ∈ ownersOf g (sel k) := by
  intro k h0 h1
  obtain ⟨hsome, _⟩ := hchain.1 k h0 h1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  simpa only [ownersOf, hn] using hso (sel k) n hn

/-- **The chain-extension construction.** A chain of the base graph, extended
by the new node at the new top step, is a chain of the extended graph. -/
theorem ChainG_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (sel : Int → PathNodeId)
    (hself : ∀ k, 0 ≤ k → k < g.current_step → sel k ∈ ownersOf g (sel k))
    (h : ChainG g sel) (hf : forb (extendPid g d sel) = false) :
    ChainG (addNode g d title forb) (extend g d sel) := by
  obtain ⟨hchain, howned, hgow⟩ := h
  have hpidmem : extendPid g d sel ∈ newRowIds g d forb :=
    extendPid_mem_newRowIds g d forb sel hchain hf
  have hnew := addNode_node?_new g d title forb hd hbelow _ hpidmem
  have hnewstep : (extendPid g d sel).id.step = g.current_step := by
    rw [extendPid_mapId]; exact hd
  -- what the row node at the top owns: everything the chain picks
  have howntop : ∀ k, 0 ≤ k → k < g.current_step →
      sel k ∈ rowOwners g d (extendPid g d sel) := by
    intro k hk0 hk1
    have hpos : 0 < g.current_step := by omega
    have hpar := lastPick_mem_rowParents g d sel hpos hchain
    have hinher : sel k ∈ unionOwnersOf g (rowParents g d (extendPid g d sel)) := by
      obtain ⟨hsome, _⟩ := hchain.1 (g.current_step - 1) (by omega) (by omega)
      obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hsome
      have hmemown : sel k ∈ nl.owners := by
        rcases int_eq_or_ne k (g.current_step - 1) with hkeq | hkne
        · have := hself k hk0 hk1
          rw [hkeq] at this ⊢
          simpa only [ownersOf, hnl] using this
        · have := howned k (g.current_step - 1) hk0 (by omega) hk1 (by omega) hkne
          simp only [ownersAt, List.mem_filter, ownersOf, hnl] at this
          exact this.1
      exact mem_unionOwnersOf g _ _ nl _ hpar hnl hmemown
    exact (mem_rowOwners_iff g d _ _).mpr (Or.inl ⟨hinher, hgow k hk0 hk1⟩)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  -- IsChain, node existence and step
  · intro k hlo hhi
    rw [addNode_current] at hhi
    rcases int_eq_or_ne (k) (g.current_step) with hk | hk
    · subst hk
      rw [extend_top]
      exact ⟨by rw [hnew]; rfl, hnewstep⟩
    · have hlt : k < g.current_step := by omega
      rw [extend_below g d sel k hlt]
      obtain ⟨hsome, hstep⟩ := hchain.1 k hlo hlt
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨by rw [addNode_node?_old g d title forb _ n hn]; rfl, hstep⟩
  -- IsChain, parent links
  · intro k hlo hhi
    rw [addNode_current] at hhi
    rcases int_eq_or_ne (k + 1) (g.current_step) with hk | hk
    · rw [hk, extend_top, hnew, extend_below g d sel k (by omega)]
      simp only [Option.map_some, Option.getD_some, rowNode_parents]
      have hpos : 0 < g.current_step := by omega
      have := lastPick_mem_rowParents g d sel hpos hchain
      rw [show g.current_step - 1 = k by omega] at this
      exact this
    · have hlt : k + 1 < g.current_step := by omega
      rw [extend_below g d sel k (by omega), extend_below g d sel (k + 1) hlt]
      have hlink := hchain.2 k hlo hlt
      cases hn : g.node? (sel (k + 1)) with
      | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
      | some n =>
        rw [hn] at hlink
        rw [addNode_node?_old g d title forb _ n hn]
        simpa [upMap_parents] using hlink
  -- PairwiseOwned
  · intro i j hi hj hi' hj' hne
    rw [addNode_current] at hi' hj'
    simp only [ownersAt, List.mem_filter]
    rcases int_eq_or_ne (j) (g.current_step) with hjc | hjc
    · -- the other end is the row node the chain entered
      subst hjc
      have hic : i < g.current_step := by omega
      rw [extend_below g d sel i hic, extend_top]
      simp only [ownersOf, hnew, rowNode_owners]
      refine ⟨howntop i hi hic, ?_⟩
      have hstepi := (hchain.1 i hi hic).2
      rw [hstepi]
      exact beq_iff_eq.mpr rfl
    · have hjlt : j < g.current_step := by omega
      rw [extend_below g d sel j hjlt]
      obtain ⟨hsome, hstepj⟩ := hchain.1 j hj hjlt
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      simp only [ownersOf, addNode_node?_old g d title forb _ n hn, upMap_owners]
      rcases int_eq_or_ne (i) (g.current_step) with hic | hic
      · -- the row node owns the chain's picks, so by symmetry it is gained
        subst hic
        rw [extend_top]
        refine ⟨List.mem_append_right _ ?_, by rw [hnewstep]; exact beq_iff_eq.mpr rfl⟩
        refine List.mem_filter.mpr ⟨hpidmem, ?_⟩
        have hnid : n.id = sel j := node?_id_eq g _ n hn
        have := howntop j hj hjlt
        rw [← hnid] at this
        simpa using this
      · have hilt : i < g.current_step := by omega
        rw [extend_below g d sel i hilt]
        have hmem := howned i j hi hj hilt hjlt hne
        simp only [ownersAt, List.mem_filter, ownersOf, hn] at hmem
        exact ⟨List.mem_append_left _ hmem.1, hmem.2⟩
  -- every selected node is a global owner
  · intro k hlo hhi
    rw [addNode_current] at hhi
    rw [addNode_gowners]
    rcases int_eq_or_ne (k) (g.current_step) with hk | hk
    · subst hk; rw [extend_top]; exact List.mem_append_right _ hpidmem
    · have hlt : k < g.current_step := by omega
      rw [extend_below g d sel k hlt]
      exact List.mem_append_left _ (hgow k hlo hlt)

/-- Bin map: the base needs a chain **whose extension is not prohibited**; `lean_project` took
any chain (`InhabitedG g`). -/
theorem InhabitedG_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hso : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (h : ∃ sel, ChainG g sel ∧ forb (extendPid g d sel) = false) :
    InhabitedG (addNode g d title forb) := by
  obtain ⟨sel, hsel, hf⟩ := h
  exact ⟨extend g d sel,
    ChainG_addNode g d title forb hd hbelow sel (selfOwned_pointwise g hso sel hsel.1) hsel hf⟩

/-- **L6's UP step, for `addNode`.** Adding a row preserves total support. With
a window of two the new node inherited `gowners` and *any* admissible chain of
the base co-owned it, which is why `InhabitedG` travelled alongside; with the
row, a row node inherits only what its own parents own, so the chain that
supports it is the one that supports one of its parents — and that is
`SupportedG` itself. `InhabitedG` is still needed for the seed row, which has no
parents.

**Bin map.** An old node keeps its support only through a chain whose extension is not
prohibited (`hsupW`); a node all of whose chains run into the window is left without a son and
it is the review's job to prune it (error 4 of the Julia report). A row node needs nothing new:
its parent's chain extends to it, and it is in the row, so it is not prohibited. -/
theorem SupportedG_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hso : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (hsup : SupportedG g)
    (hsupW : ∀ pid n, g.node? pid = some n →
      ∃ sel, ChainG g sel ∧ sel pid.id.step = pid ∧ forb (extendPid g d sel) = false)
    (hinh : ∃ sel, ChainG g sel ∧ forb (extendPid g d sel) = false) :
    SupportedG (addNode g d title forb) := by
  intro pid n hn
  have hmem : n ∈ (addNode g d title forb).nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq _ pid n hn
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · -- an old node: reuse a chain of it whose extension is allowed
    obtain ⟨n₁, hn₁, hEq⟩ := List.mem_map.mp hl
    have hsame : n.id = n₁.id := by rw [← hEq, upMap_id]
    have hstep : pid.id.step < g.current_step := by rw [← hid, hsame]; exact hbelow n₁ hn₁
    obtain ⟨n₀, hn₀, _⟩ := addNode_node?_below g d title forb hd pid n hn hstep
    obtain ⟨sel, hsel, htop, hf⟩ := hsupW pid n₀ hn₀
    refine ⟨extend g d sel,
      ChainG_addNode g d title forb hd hbelow sel (selfOwned_pointwise g hso sel hsel.1) hsel hf, ?_⟩
    rw [extend_below g d sel pid.id.step hstep]
    exact htop
  · -- a node of the new row: the chain that supports one of its parents
    obtain ⟨q, hq, rfl⟩ := (mem_newRow_iff g d title forb n).mp hr
    have hqid : q = pid := by rw [← hid]; rfl
    subst hqid
    have hstepq : q.id.step = g.current_step := by
      rw [mapId_of_mem_newRowIds g d forb q hq]; exact hd
    have hqf : forb q = false := not_forb_of_mem_newRowIds g d forb q hq
    by_cases hpos : 0 < g.current_step
    · -- it has parents, and any of them carries a chain
      obtain ⟨p, hp⟩ : ∃ p, p ∈ rowParents g d q := by
        obtain ⟨r, hr', hrq⟩ := exists_shift_of_mem_newRowIds g d forb q hpos hq
        exact ⟨r, List.mem_filter.mpr ⟨hr', beq_iff_eq.mpr hrq.symm⟩⟩
      have hpmem : p ∈ newParents g := rowParents_subset g d q p hp
      have hpline : p ∈ (g.line (g.current_step - 1)).map (·.id) := by
        unfold newParents at hpmem; rwa [if_pos hpos] at hpmem
      obtain ⟨np, hnp, hnpid⟩ := List.mem_map.mp hpline
      have hmemp : np ∈ g.nodes := (List.mem_filter.mp hnp).1
      have hsomep : (g.node? p).isSome = true := by
        have := node?_isSome_of_mem g np hmemp; rwa [hnpid] at this
      obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp hsomep
      obtain ⟨sel, hsel, htop⟩ := hsup p mp hmp
      have hpstep : p.id.step = g.current_step - 1 := by
        rw [← hnpid]; exact eq_of_beq (List.mem_filter.mp hnp).2
      have hselp : sel (g.current_step - 1) = p := by rw [← hpstep]; exact htop
      have hext : extendPid g d sel = q := by
        unfold extendPid
        rw [if_pos hpos, hselp]
        exact shiftPid_of_mem_rowParents g d q p hp
      refine ⟨extend g d sel,
        ChainG_addNode g d title forb hd hbelow sel (selfOwned_pointwise g hso sel hsel.1) hsel
          (by rw [hext]; exact hqf), ?_⟩
      rw [hstepq, extend_top, hext]
    · -- the seed row: no parents, any admissible chain will do
      obtain ⟨sel, hsel, hf⟩ := hinh
      refine ⟨extend g d sel,
        ChainG_addNode g d title forb hd hbelow sel (selfOwned_pointwise g hso sel hsel.1) hsel hf,
        ?_⟩
      rw [hstepq, extend_top]
      unfold extendPid
      rw [if_neg hpos]
      have hq' := shiftRowIds_of_mem_newRowIds g d forb q hq
      unfold shiftRowIds at hq'
      rw [if_neg hpos] at hq'
      exact (List.mem_singleton.mp hq').symm

/-- **L6's `up` case, reduced to the review step.** Everything the UP
constructor does *except* `review` preserves total support:

* the `filterRequire` fold rewrites `gowners` only, and `Supported` never
  reads it (`Supported_filterRequire`);
* `addNode` is `SupportedG_addNode` above.

**Bin map.** When no window is skipped every extension is allowed and the classic argument goes
through. When one is skipped the UP reviews, and support after it needs the review to prune the
nodes left without a son — the same review step L6 already rests on. That branch is `sorry`. -/
theorem SupportedG_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool)
    (hvalid : isValid (filterAll g reqs) = true)
    (hd : d.step = (filterAll g reqs).current_step)
    (hbelow : ∀ n ∈ (filterAll g reqs).nodes,
      n.id.id.step < (filterAll g reqs).current_step)
    (hso : ∀ pid n, (filterAll g reqs).node? pid = some n → pid ∈ n.owners)
    (hsup : SupportedG (filterAll g reqs)) (hinh : InhabitedG (filterAll g reqs)) :
    SupportedG (upFiltering g reqs d title forb) := by
  simp only [upFiltering, up, hvalid, if_true]
  split
  · sorry -- bin: the review after a skipped window must prune the sonless parents (L6 hole)
  · rename_i hskip
    have hnf : ∀ sel, IsChain (filterAll g reqs) sel →
        forb (extendPid (filterAll g reqs) d sel) = false := by
      intro sel hc
      have hmem := extendPid_mem_shiftRowIds _ d sel hc
      cases hfb : forb (extendPid (filterAll g reqs) d sel) with
      | false => rfl
      | true =>
        exfalso; apply hskip
        exact List.any_eq_true.mpr ⟨_, hmem, hfb⟩
    refine SupportedG_addNode _ d title forb hd hbelow hso hsup ?_ ?_
    · intro pid n hn
      obtain ⟨sel, hsel, htop⟩ := hsup pid n hn
      exact ⟨sel, hsel, htop, hnf sel hsel.1⟩
    · obtain ⟨sel, hsel⟩ := hinh
      exact ⟨sel, hsel, hnf sel hsel.1⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSatBin.GraphPath.Model.ChainG_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainG_addNode

-- `SupportedG_upFiltering`: guard removed while its skipped-window branch is `sorry`.

end AbsSatBin.GraphPath.Model
