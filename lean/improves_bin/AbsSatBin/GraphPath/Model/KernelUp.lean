-- lean/improves_bin/AbsSatBin/GraphPath/Model/KernelUp.lean
import AbsSatBin.GraphPath.Model.GrowCert

/-!
# The `UP` of a kernel is a kernel

Measured (`julia/improves_bin/test_3sat/probes/kernel_probe.jl`, after the stale-link fix `LINK_MODE`):
every piece (5 033) and every state of the line (2 986) is a kernel.

**`kernel_addNode`**: if no candidate of the new row is prohibited, `addNode` of a kernel is a kernel. Field by
field, from the kernel below:

* **pair rule at the new step**: two old nodes that own each other have a top node owning both (pair rule at
  the old top step); its child in the new row inherits its table, so owns both.
* **validity at the new step**: every old node is owned by a top node (its entry at the top step, by
  symmetry), and that node's child owns it.
* **support by parents and sons**: a row node's entries come from its parents; an old node gains a row node
  `w` because a parent `q` of `w` owns it, and the kernel's support of `q` gives the parent (or son) that also
  owns `q` — hence is inherited by `w`. At its own step a node owns only itself (`OOS`), which pins the son
  of a top node.

When a candidate is prohibited, `up` reviews the new state and `KernelReader.kernel_of_review` applies.
-/

namespace AbsSatBin.GraphPath.Model.KernelUp

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel

section
variable (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)

theorem mem_gainedOwners (n : PNodeM) (w : PathNodeId) :
    w ∈ gainedOwners g d forb n ↔ w ∈ newRowIds g d forb ∧ n.id ∈ rowOwners g d w := by
  unfold gainedOwners
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, List.elem_eq_true_of_mem h2⟩

theorem mem_gainedSons (n : PNodeM) (w : PathNodeId) :
    w ∈ gainedSons g d forb n ↔ w ∈ newRowIds g d forb ∧ n.id ∈ rowParents g d w := by
  unfold gainedSons
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, List.elem_eq_true_of_mem h2⟩

variable (hd : d.step = g.current_step) (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
include hd hbelow

/-- A node of the new state is an old node, or a node of the new row. -/
theorem node_cases (p : PathNodeId) (n : PNodeM) (hn : (addNode g d title forb).node? p = some n) :
    (∃ n₀, g.node? p = some n₀ ∧ n = upMap g d forb n₀) ∨
      (p ∈ newRowIds g d forb ∧ n = rowNode g d title p) := by
  if hps : p.id.step < g.current_step then
    exact Or.inl (addNode_node?_below g d title forb hd p n hn hps)
  else
    have hid : n.id = p := node?_id_eq _ p n hn
    have hmem : n ∈ (addNode g d title forb).nodes := List.mem_of_find?_eq_some hn
    rw [addNode_nodes] at hmem
    rcases List.mem_append.mp hmem with hl | hr
    · exfalso
      obtain ⟨n₀, hn₀, hEq⟩ := List.mem_map.mp hl
      have hnn : n.id = n₀.id := by rw [← hEq, upMap_id]
      have := hbelow n₀ hn₀
      rw [← hnn, hid] at this
      omega
    · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title forb n).mp hr
      rw [rowNode_id] at hid
      rw [← hid]
      exact Or.inr ⟨hpid, rfl⟩

omit hbelow in
theorem row_step (w : PathNodeId) (hw : w ∈ newRowIds g d forb) : w.id.step = g.current_step := by
  rw [mapId_of_mem_newRowIds g d forb w hw, hd]

omit hd in
theorem old_step (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n) : p.id.step < g.current_step := by
  have := hbelow n (List.mem_of_find?_eq_some hn)
  rwa [node?_id_eq g p n hn] at this

end

section
variable {g : GPathM} (d : NodeId) (title : String) (forb : PathNodeId → Bool)
variable (hk : Kernel g) (hd : d.step = g.current_step)
  (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hpos : 0 < g.current_step)
  (hso : Ownership.SelfOwned g) (hoos : SelfOwn.OOS g) (hownb : SelfOwn.OwnBelow g)
  (hnf : ∀ pid ∈ shiftRowIds g d, forb pid = false)

include hpos hnf in
/-- **Every node of the top step has its child in the new row.** -/
theorem child_mem (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq)
    (hqs : q.id.step = g.current_step - 1) :
    shiftPid q d ∈ newRowIds g d forb ∧ q ∈ rowParents g d (shiftPid q d) := by
  have hnp : q ∈ newParents g := by
    unfold newParents; rw [if_pos hpos]
    refine List.mem_map.mpr ⟨nq, ?_, node?_id_eq g q nq hq⟩
    refine List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hq, ?_⟩
    exact beq_iff_eq.mpr (by rw [node?_id_eq g q nq hq, hqs])
  have hsh : shiftPid q d ∈ shiftRowIds g d := by
    unfold shiftRowIds; rw [if_pos hpos]
    exact (mem_dedupPids _ _).mpr (List.mem_map_of_mem hnp)
  exact ⟨mem_newRowIds_of_mem_newParents g d forb q hpos hnp (hnf _ hsh),
    mem_rowParents_of_mem_newParents g d q hnp⟩

include hk in
/-- A row node inherits what its parents own. -/
theorem inherit (w q : PathNodeId) (hqw : q ∈ rowParents g d w) (nq : PNodeM) (hq : g.node? q = some nq)
    (v : PathNodeId) (hv : v ∈ nq.owners) : v ∈ rowOwners g d w :=
  (mem_rowOwners_iff g d w v).mpr (Or.inl ⟨mem_unionOwnersOf g _ q nq v hqw hq hv, hk.own q nq hq v hv⟩)

/-- What a row node owns besides itself, one of its parents owns. -/
theorem inherit_inv (w v : PathNodeId) (hv : v ∈ rowOwners g d w) (hne : v ≠ w) :
    ∃ q ∈ rowParents g d w, ∃ nq, g.node? q = some nq ∧ v ∈ nq.owners := by
  rcases (mem_rowOwners_iff g d w v).mp hv with ⟨hu, _⟩ | h
  · exact exists_owner_of_mem_unionOwnersOf g _ v hu
  · exact absurd h hne

include hk hso in
/-- A row node owns its parents. -/
theorem owns_parent (w q : PathNodeId) (hqw : q ∈ rowParents g d w) (nq : PNodeM) (hq : g.node? q = some nq) :
    q ∈ rowOwners g d w :=
  inherit d hk w q hqw nq hq q (hso q nq hq)

end

-- ============================================================
-- The theorem
-- ============================================================

section
variable {g : GPathM} (d : NodeId) (title : String) (forb : PathNodeId → Bool)
variable (hk : Kernel g) (hd : d.step = g.current_step)
  (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hpos : 0 < g.current_step)
  (hso : Ownership.SelfOwned g) (hoos : SelfOwn.OOS g) (hownb : SelfOwn.OwnBelow g)
  (hnf : ∀ pid ∈ shiftRowIds g d, forb pid = false)

include hk hpos in
/-- A row node has an entry at every step up to the new one. -/
theorem row_entry (p : PathNodeId) (hp : p ∈ newRowIds g d forb) (hps : p.id.step = g.current_step)
    (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ g.current_step) : ∃ r ∈ rowOwners g d p, r.id.step = k := by
  rcases Int.lt_or_le k g.current_step with hlt | hge
  · obtain ⟨q, hq⟩ := exists_rowParent g d forb hpos hp
    obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (rowParent_node g d hpos hq).1
    obtain ⟨hall, _, _⟩ := (isValidNode_iff g nq).mp (hk.valid q nq hnq)
    obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp hall k (mem_intRange_zero k _ h0 hlt))
    exact ⟨r, inherit d hk p q hq nq hnq r hr, eq_of_beq hrs⟩
  · exact ⟨p, self_mem_rowOwners g d p, by rw [hps]; omega⟩

include hk hpos hnf in
/-- **Two old nodes that own each other are owned by one row node**: the child of a top node owning
both (pair rule at the top step). -/
theorem top_common (p : PathNodeId) (n₀ : PNodeM) (hn₀ : g.node? p = some n₀) (w : PathNodeId)
    (m₀ : PNodeM) (hm₀ : g.node? w = some m₀) (hw : w ∈ n₀.owners) :
    ∃ c ∈ newRowIds g d forb, p ∈ rowOwners g d c ∧ w ∈ rowOwners g d c := by
  obtain ⟨r, hrp, hrw, hrs⟩ := hk.pair p n₀ w m₀ hn₀ hm₀ hw (g.current_step - 1) (by omega) (by omega)
  obtain ⟨nr, hnr⟩ := hk.isNode_owner p n₀ hn₀ r hrp
  obtain ⟨hc, hrc⟩ := child_mem d forb hpos hnf r nr hnr hrs
  exact ⟨_, hc, inherit d hk _ r hrc nr hnr p (hk.sym p n₀ r nr hn₀ hnr hrp),
    inherit d hk _ r hrc nr hnr w (hk.sym w m₀ r nr hm₀ hnr hrw)⟩

include hk hpos hnf in
/-- **An old node gains a row owner**: the child of a top node owning it. -/
theorem old_gain (p : PathNodeId) (n₀ : PNodeM) (hn₀ : g.node? p = some n₀) :
    ∃ w ∈ gainedOwners g d forb n₀, w.id = d := by
  obtain ⟨hall, _, _⟩ := (isValidNode_iff g n₀).mp (hk.valid p n₀ hn₀)
  obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp hall (g.current_step - 1) (mem_intRange_zero _ _ (by omega) (by omega)))
  obtain ⟨nr, hnr⟩ := hk.isNode_owner p n₀ hn₀ r hr
  obtain ⟨hc, hrc⟩ := child_mem d forb hpos hnf r nr hnr (eq_of_beq hrs)
  refine ⟨_, (mem_gainedOwners g d forb n₀ _).mpr ⟨hc, ?_⟩, mapId_of_mem_newRowIds g d forb _ hc⟩
  rw [node?_id_eq g p n₀ hn₀]
  exact inherit d hk _ r hrc nr hnr p (hk.sym p n₀ r nr hn₀ hnr hr)

include hk hd hbelow hpos hso hoos hownb hnf in
/-- **The `UP` of a kernel, with no prohibited candidate, is a kernel.** -/
theorem kernel_addNode : Kernel (addNode g d title forb) := by
  have cases := node_cases g d title forb hd hbelow
  have rstep := row_step g d forb hd
  have ostep := old_step g hbelow
  have hid : ∀ p n₀, g.node? p = some n₀ → n₀.id = p := fun p n₀ h => node?_id_eq g p n₀ h
  have gained : ∀ n₀ w, w ∈ newRowIds g d forb → n₀.id ∈ rowOwners g d w →
      w ∈ (upMap g d forb n₀).owners := fun n₀ w h1 h2 => by
    rw [upMap_owners]; exact List.mem_append_right _ ((mem_gainedOwners g d forb n₀ w).mpr ⟨h1, h2⟩)
  have oldN := fun p n₀ (h : g.node? p = some n₀) => addNode_node?_old g d title forb p n₀ h
  have newN := fun w (h : w ∈ newRowIds g d forb) => addNode_node?_new g d title forb hd hbelow w h
  -- an old table holds no row id
  have fresh : ∀ p n₀, g.node? p = some n₀ → ∀ w ∈ newRowIds g d forb, w ∉ n₀.owners := by
    intro p n₀ hn₀ w hw hmem
    have := hownb n₀ (List.mem_of_find?_eq_some hn₀) w hmem
    rw [rstep w hw] at this; omega
  -- what an old node owns in the new state
  have oldOwn : ∀ p n₀, g.node? p = some n₀ → ∀ v ∈ (upMap g d forb n₀).owners,
      v ∈ n₀.owners ∨ (v ∈ newRowIds g d forb ∧ p ∈ rowOwners g d v) := by
    intro p n₀ hn₀ v hv
    rw [upMap_owners] at hv
    rcases List.mem_append.mp hv with h | h
    · exact Or.inl h
    · have := (mem_gainedOwners g d forb n₀ v).mp h
      rw [hid p n₀ hn₀] at this; exact Or.inr this
  have hcs : (addNode g d title forb).current_step = g.current_step + 1 := addNode_current g d title forb
  refine
    { gow := ?_, gn := ?_, own := ?_, valid := ?_, sym := ?_, linkP := ?_, linkS := ?_, pair := ?_,
      nbrP := ?_, nbrS := ?_ }
  -- gow
  · intro p n hn
    rw [addNode_gowners]
    rcases cases p n hn with ⟨n₀, hn₀, _⟩ | ⟨hp, _⟩
    · exact List.mem_append_left _ (hk.gow p n₀ hn₀)
    · exact List.mem_append_right _ hp
  -- gn
  · intro q hq
    rw [addNode_gowners] at hq
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨n₀, hn₀⟩ := Option.isSome_iff_exists.mp (hk.gn q h)
      rw [oldN q n₀ hn₀]; rfl
    · rw [newN q h]; rfl
  -- own
  · intro p n hn v hv
    rw [addNode_gowners]
    rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
    · rcases oldOwn p n₀ hn₀ v hv with h | ⟨h, _⟩
      · exact List.mem_append_left _ (hk.own p n₀ hn₀ v h)
      · exact List.mem_append_right _ h
    · rw [rowNode_owners] at hv
      rcases rowOwners_mem_gowners_or_self g d p v hv with h | rfl
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ hp
  -- valid
  · intro p n hn
    refine (isValidNode_iff _ n).mpr ⟨List.all_eq_true.mpr (fun k hkr => ?_), ?_, ?_⟩
    · have h0 := mem_intRange_lower hkr
      have h1 := mem_intRange_upper hkr
      rw [hcs] at h1
      rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
      · rcases Int.lt_or_le k g.current_step with hlt | hge
        · obtain ⟨hall, _, _⟩ := (isValidNode_iff g n₀).mp (hk.valid p n₀ hn₀)
          obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp
            (List.all_eq_true.mp hall k (mem_intRange_zero k _ h0 hlt))
          rw [upMap_owners]
          exact List.any_eq_true.mpr ⟨r, List.mem_append_left _ hr, hrs⟩
        · obtain ⟨w, hw, hwd⟩ := old_gain d forb hk hpos hnf p n₀ hn₀
          rw [upMap_owners]
          exact List.any_eq_true.mpr ⟨w, List.mem_append_right _ hw,
            beq_iff_eq.mpr (by rw [hwd, hd]; omega)⟩
      · rw [rowNode_owners]
        obtain ⟨r, hr, hrs⟩ := row_entry d forb hk hpos p hp (rstep p hp) k h0 (by omega)
        exact List.any_eq_true.mpr ⟨r, hr, beq_iff_eq.mpr hrs⟩
    · rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
      · obtain ⟨_, h2, _⟩ := (isValidNode_iff g n₀).mp (hk.valid p n₀ hn₀)
        exact h2
      · right
        rw [rowNode_parents]
        obtain ⟨q, hq⟩ := exists_rowParent g d forb hpos hp
        exact List.ne_nil_of_mem hq
    · rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
      · right
        rw [upMap_sons]
        by_cases htop : p.id.step = g.current_step - 1
        · obtain ⟨hc, hpc⟩ := child_mem d forb hpos hnf p n₀ hn₀ htop
          refine List.ne_nil_of_mem (List.mem_append_right _ ((mem_gainedSons g d forb n₀ _).mpr ⟨hc, ?_⟩))
          rw [hid p n₀ hn₀]; exact hpc
        · obtain ⟨_, _, h3⟩ := (isValidNode_iff g n₀).mp (hk.valid p n₀ hn₀)
          rcases h3 with h | h
          · exact absurd (by rw [← hid p n₀ hn₀]; exact eq_of_beq h) htop
          · intro he; exact h (List.append_eq_nil_iff.mp he).1
      · left
        rw [rowNode_id, rstep p hp, hcs]; exact beq_iff_eq.mpr (by omega)
  -- sym
  · exact Reader.OwnSymmetric_addNode g d title forb hd hbelow hownb hk.sym
  -- linkP
  · intro p n hn c hc
    rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
    · rw [upMap_parents] at hc
      obtain ⟨hco, nc, hnc, hpo⟩ := hk.linkP p n₀ hn₀ c hc
      refine ⟨by rw [upMap_owners]; exact List.mem_append_left _ hco, _, oldN c nc hnc, ?_⟩
      rw [upMap_owners]; exact List.mem_append_left _ hpo
    · rw [rowNode_parents] at hc
      obtain ⟨nc, hnc⟩ := Option.isSome_iff_exists.mp (rowParent_node g d hpos hc).1
      refine ⟨by rw [rowNode_owners]; exact owns_parent d hk hso p c hc nc hnc, _, oldN c nc hnc, ?_⟩
      exact gained nc p hp (by rw [hid c nc hnc]; exact owns_parent d hk hso p c hc nc hnc)
  -- linkS
  · intro p n hn c hc
    rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
    · rw [upMap_sons] at hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨hco, nc, hnc, hpo⟩ := hk.linkS p n₀ hn₀ c hc
        refine ⟨by rw [upMap_owners]; exact List.mem_append_left _ hco, _, oldN c nc hnc, ?_⟩
        rw [upMap_owners]; exact List.mem_append_left _ hpo
      · obtain ⟨hcw, hpar⟩ := (mem_gainedSons g d forb n₀ c).mp hc
        rw [hid p n₀ hn₀] at hpar
        have hpc := owns_parent d hk hso c p hpar n₀ hn₀
        exact ⟨gained n₀ c hcw (by rw [hid p n₀ hn₀]; exact hpc), _, newN c hcw, hpc⟩
    · rw [rowNode_sons] at hc; exact absurd hc List.not_mem_nil
  -- pair
  · intro p n w nw hn hnw hwn k h0 h1
    rw [hcs] at h1
    rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
    · rcases cases w nw hnw with ⟨m₀, hm₀, rfl⟩ | ⟨hw, rfl⟩
      · -- both old
        have hw0 : w ∈ n₀.owners := by
          rcases oldOwn p n₀ hn₀ w hwn with h | ⟨h, _⟩
          · exact h
          · have := ostep w m₀ hm₀; rw [rstep w h] at this; omega
        rcases Int.lt_or_le k g.current_step with hlt | hge
        · obtain ⟨r, hr1, hr2, hrs⟩ := hk.pair p n₀ w m₀ hn₀ hm₀ hw0 k h0 hlt
          refine ⟨r, ?_, ?_, hrs⟩ <;> rw [upMap_owners] <;> exact List.mem_append_left _ (by assumption)
        · obtain ⟨c, hc, hpc, hwc⟩ := top_common d forb hk hpos hnf p n₀ hn₀ w m₀ hm₀ hw0
          exact ⟨c, gained n₀ c hc (by rw [hid p n₀ hn₀]; exact hpc),
            gained m₀ c hc (by rw [hid w m₀ hm₀]; exact hwc), by rw [rstep c hc]; omega⟩
      · -- `p` old, `w` a row node
        have hpw : p ∈ rowOwners g d w := by
          rcases oldOwn p n₀ hn₀ w hwn with h | ⟨_, h⟩
          · exact absurd h (fresh p n₀ hn₀ w hw)
          · exact h
        rw [rowNode_owners]
        rcases Int.lt_or_le k g.current_step with hlt | hge
        · have hne : p ≠ w := by
            intro e; have := ostep p n₀ hn₀; rw [e, rstep w hw] at this; omega
          obtain ⟨q, hq, nq, hnq, hpq⟩ := inherit_inv d w p hpw hne
          obtain ⟨r, hr1, hr2, hrs⟩ := hk.pair q nq p n₀ hnq hn₀ hpq k h0 hlt
          exact ⟨r, by rw [upMap_owners]; exact List.mem_append_left _ hr2,
            inherit d hk w q hq nq hnq r hr1, hrs⟩
        · exact ⟨w, hwn, self_mem_rowOwners g d w, by rw [rstep w hw]; omega⟩
    · rw [rowNode_owners] at hwn ⊢
      rcases cases w nw hnw with ⟨m₀, hm₀, rfl⟩ | ⟨hw, rfl⟩
      · -- `p` a row node, `w` old
        rcases Int.lt_or_le k g.current_step with hlt | hge
        · have hne : w ≠ p := by
            intro e; have := ostep w m₀ hm₀; rw [e, rstep p hp] at this; omega
          obtain ⟨q, hq, nq, hnq, hwq⟩ := inherit_inv d p w hwn hne
          obtain ⟨r, hr1, hr2, hrs⟩ := hk.pair q nq w m₀ hnq hm₀ hwq k h0 hlt
          exact ⟨r, inherit d hk p q hq nq hnq r hr1,
            by rw [upMap_owners]; exact List.mem_append_left _ hr2, hrs⟩
        · exact ⟨p, self_mem_rowOwners g d p, gained m₀ p hp (by rw [hid w m₀ hm₀]; exact hwn),
            by rw [rstep p hp]; omega⟩
      · -- both in the row: `w = p`
        have hwp : w = p := by
          by_cases hne : w = p
          · exact hne
          · exfalso
            obtain ⟨q, _, nq, hnq, hwq⟩ := inherit_inv d p w hwn hne
            exact fresh q nq hnq w hw hwq
        subst hwp
        obtain ⟨r, hr, hrs⟩ := row_entry d forb hk hpos w hp (rstep w hp) k h0 (by omega)
        exact ⟨r, hr, by rw [rowNode_owners]; exact hr, hrs⟩
  -- nbrP
  · intro p n hn h1 v hv
    rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
    · rw [upMap_parents]
      rcases oldOwn p n₀ hn₀ v hv with h | ⟨hw, hpw⟩
      · obtain ⟨c, hc, nc, hnc, hvc⟩ := hk.nbrP p n₀ hn₀ h1 v h
        exact ⟨c, hc, _, oldN c nc hnc, by rw [upMap_owners]; exact List.mem_append_left _ hvc⟩
      · have hne : p ≠ v := by
          intro e; have := ostep p n₀ hn₀; rw [e, rstep v hw] at this; omega
        obtain ⟨q, hq, nq, hnq, hpq⟩ := inherit_inv d v p hpw hne
        obtain ⟨c, hc, nc, hnc, hqc⟩ := hk.nbrP p n₀ hn₀ h1 q (hk.sym q nq p n₀ hnq hn₀ hpq)
        have hcq := hk.sym c nc q nq hnc hnq hqc
        exact ⟨c, hc, _, oldN c nc hnc,
          gained nc v hw (by rw [hid c nc hnc]; exact inherit d hk v q hq nq hnq c hcq)⟩
    · rw [rowNode_parents]
      rw [rowNode_owners] at hv
      by_cases hvp : v = p
      · subst hvp
        obtain ⟨q, hq⟩ := exists_rowParent g d forb hpos hp
        obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (rowParent_node g d hpos hq).1
        exact ⟨q, hq, _, oldN q nq hnq,
          gained nq v hp (by rw [hid q nq hnq]; exact owns_parent d hk hso v q hq nq hnq)⟩
      · obtain ⟨q, hq, nq, hnq, hvq⟩ := inherit_inv d p v hv hvp
        exact ⟨q, hq, _, oldN q nq hnq, by rw [upMap_owners]; exact List.mem_append_left _ hvq⟩
  -- nbrS
  · intro p n hn h2 v hv
    rw [hcs] at h2
    rcases cases p n hn with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
    · rw [upMap_sons]
      by_cases htop : p.id.step = g.current_step - 1
      · obtain ⟨hc, hpc⟩ := child_mem d forb hpos hnf p n₀ hn₀ htop
        have hson : shiftPid p d ∈ gainedSons g d forb n₀ :=
          (mem_gainedSons g d forb n₀ _).mpr ⟨hc, by rw [hid p n₀ hn₀]; exact hpc⟩
        rcases oldOwn p n₀ hn₀ v hv with h | ⟨hw, hpw⟩
        · exact ⟨_, List.mem_append_right _ hson, _, newN _ hc,
            by rw [rowNode_owners]; exact inherit d hk _ p hpc n₀ hn₀ v h⟩
        · -- the row owner of a top node is its own child
          have hne : p ≠ v := by
            intro e; have := ostep p n₀ hn₀; rw [e, rstep v hw] at this; omega
          obtain ⟨q, hq, nq, hnq, hpq⟩ := inherit_inv d v p hpw hne
          have hqs := (rowParent_node g d hpos hq).2
          have hpq' : p = q := by
            have := hoos nq (List.mem_of_find?_eq_some hnq) p hpq (by rw [hid q nq hnq, hqs, htop])
            rw [hid q nq hnq] at this; exact this
          subst hpq'
          exact ⟨v, List.mem_append_right _ ((mem_gainedSons g d forb n₀ v).mpr
            ⟨hw, by rw [hid p n₀ hn₀]; exact hq⟩), _, newN v hw,
            by rw [rowNode_owners]; exact self_mem_rowOwners g d v⟩
      · have hlow : p.id.step ≤ g.current_step - 2 := by have := ostep p n₀ hn₀; omega
        rcases oldOwn p n₀ hn₀ v hv with h | ⟨hw, hpw⟩
        · obtain ⟨c, hc, nc, hnc, hvc⟩ := hk.nbrS p n₀ hn₀ hlow v h
          exact ⟨c, List.mem_append_left _ hc, _, oldN c nc hnc,
            by rw [upMap_owners]; exact List.mem_append_left _ hvc⟩
        · have hne : p ≠ v := by
            intro e; have := ostep p n₀ hn₀; rw [e, rstep v hw] at this; omega
          obtain ⟨q, hq, nq, hnq, hpq⟩ := inherit_inv d v p hpw hne
          obtain ⟨c, hc, nc, hnc, hqc⟩ := hk.nbrS p n₀ hn₀ hlow q (hk.sym q nq p n₀ hnq hn₀ hpq)
          have hcq := hk.sym c nc q nq hnc hnq hqc
          exact ⟨c, List.mem_append_left _ hc, _, oldN c nc hnc,
            gained nc v hw (by rw [hid c nc hnc]; exact inherit d hk v q hq nq hnq c hcq)⟩
    · have := rstep p hp; omega

end

/-- info: 'AbsSatBin.GraphPath.Model.KernelUp.kernel_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kernel_addNode

/-- **The `UP` of a valid kernel that skips no window is a kernel** (when it skips one, `up` reviews and
`KernelReader.kernel_of_review` applies). -/
theorem kernel_up {g : GPathM} (d : NodeId) (title : String) (forb : PathNodeId → Bool) (hk : Kernel g)
    (hd : d.step = g.current_step) (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hpos : 0 < g.current_step) (hso : Ownership.SelfOwned g) (hoos : SelfOwn.OOS g)
    (hownb : SelfOwn.OwnBelow g) (hv : isValid g = true) (hsk : skipsWindow g d forb = false) :
    Kernel (up g d title forb) := by
  have hnf : ∀ pid ∈ shiftRowIds g d, forb pid = false := by
    intro pid hpid
    cases e : forb pid with
    | false => rfl
    | true =>
      have : skipsWindow g d forb = true := List.any_eq_true.mpr ⟨pid, hpid, e⟩
      rw [this] at hsk; exact absurd hsk (by decide)
  unfold up
  rw [if_pos hv, hsk, if_neg (by decide)]
  exact kernel_addNode d title forb hk hd hbelow hpos hso hoos hownb hnf

/-- info: 'AbsSatBin.GraphPath.Model.KernelUp.kernel_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kernel_up

end AbsSatBin.GraphPath.Model.KernelUp
