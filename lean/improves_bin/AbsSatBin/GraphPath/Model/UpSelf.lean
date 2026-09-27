-- lean/improves_bin/AbsSatBin/GraphPath/Model/UpSelf.lean
import AbsSatBin.GraphPath.Model.NodeHistory
import AbsSatBin.GraphPath.Model.L6Up

/-!
# A kernel lies below the UP of its own truncation (`docs/context/escalera_reader.md` §4.2ο.2)

Let `H` be a kernel whose top row carries a single map node `d`, with the window invariants of the machine (`PMP`,
`GPMP`, no root above step 0) and no prohibited node. Cut its top row off (`Trunc.trunc`) and run the UP to `d` again:

**`below_up_trunc`**: `H` lies below `addNode (trunc H) d`.
* A top node `t` of `H` is the shift of any of its parents (`PMP` and `GPMP` fix its window), so it is a new row id.
* Its table: an entry below the top is carried by some parent (the kernel's neighbour clause), and the new node owns
  what its parents own; at the top it owns only itself.
* An old node gains as owners exactly the new nodes whose table holds it, and as sons the new nodes it is a parent of.

This is how the chain form of M1b climbs from a source of line `m-1` to its piece of line `m`: the pinned state, cut at
row `m`, is a kernel below the UP of its cut at row `m-1`.
-/

namespace AbsSatBin.GraphPath.Model.UpSelf

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel

/-- What the lemma reads from the kernel: its context, a top row of the single map node `d`, and no prohibited node. -/
structure Ctx (H : GPathM) (d : NodeId) (forb : PathNodeId → Bool) : Prop where
  pc   : KernelSplit.PinCtx H
  rc   : Reader.RCtx H
  htop : ∀ t nt, H.node? t = some nt → t.id.step = H.current_step - 1 → t.id = d
  hd   : d.step = H.current_step - 1
  h2   : 2 ≤ H.current_step
  hnf  : MapReachable.NoForb forb H

variable {H : GPathM} {d : NodeId} {forb : PathNodeId → Bool} (x : Ctx H d forb)
include x

/-- A top node is the shift of any of its parents. -/
theorem shift_parent (t : PathNodeId) (nt : PNodeM) (ht : H.node? t = some nt) (hts : t.id.step = H.current_step - 1)
    (c : PathNodeId) (hc : c ∈ nt.parents) : shiftPid c d = t := by
  have hm := List.mem_of_find?_eq_some ht
  have hid : nt.id = t := node?_id_eq H t nt ht
  have h1 := x.rc.pmp nt hm c hc
  have h2' := x.rc.gpmp.1 nt hm c hc
  rw [hid] at h1 h2'
  exact AmbTriCore.pid_ext (by show d = t.id; rw [x.htop t nt ht hts]) (by show some c.id = t.parent_id; exact h1)
    (by show c.parent_id = t.gparent_id; exact h2'.symm)

/-- A node of `H` below its top row is a node of the last row of the truncation's candidates, if it is at row `m-1`. -/
theorem mem_newParents (c : PathNodeId) (nc : PNodeM) (hc : H.node? c = some nc)
    (hcs : c.id.step = H.current_step - 2) : c ∈ newParents (Trunc.trunc H) := by
  have hpos : 0 < (Trunc.trunc H).current_step := by show 0 < H.current_step - 1; have := x.h2; omega
  unfold newParents
  rw [if_pos hpos]
  have hT := Trunc.trunc_node?_of H c nc hc (by omega)
  have hmem := List.mem_of_find?_eq_some hT
  have hid : (Trunc.cutTop (H.current_step - 1) nc).id = c := node?_id_eq _ c _ hT
  refine List.mem_map.mpr ⟨Trunc.cutTop (H.current_step - 1) nc, List.mem_filter.mpr ⟨hmem, ?_⟩, hid⟩
  rw [hid]
  show (c.id.step == H.current_step - 1 - 1) = true
  exact beq_iff_eq.mpr (by omega)

/-- A top node of `H` has a parent, and is a new row id of the truncation. -/
theorem top_newRow (t : PathNodeId) (nt : PNodeM) (ht : H.node? t = some nt)
    (hts : t.id.step = H.current_step - 1) :
    t ∈ newRowIds (Trunc.trunc H) d forb ∧ ∀ c ∈ nt.parents, c ∈ rowParents (Trunc.trunc H) d t := by
  have hm := List.mem_of_find?_eq_some ht
  have hid : nt.id = t := node?_id_eq H t nt ht
  have hpar : ∀ c ∈ nt.parents, c ∈ rowParents (Trunc.trunc H) d t := by
    intro c hc
    obtain ⟨_, nc, hnc, _⟩ := x.pc.ker.linkP t nt ht c hc
    have hcs : c.id.step = t.id.step - 1 := by have := x.pc.pb nt hm c hc; rw [hid] at this; exact this
    have := mem_rowParents_of_mem_newParents (Trunc.trunc H) d c (mem_newParents x c nc hnc (by omega))
    rw [shift_parent x t nt ht hts c hc] at this
    exact this
  refine ⟨?_, hpar⟩
  -- a parent exists: the node is not a root above step 0
  have hne : nt.parents ≠ [] := by
    rcases ((isValidNode_iff H nt).mp (x.pc.ker.valid t nt ht)).2.1 with hr | hr
    · exfalso
      have := x.rc.shape.notroot nt hm (by rw [hid]; have := x.h2; omega)
      exact this (Option.isNone_iff_eq_none.mp hr)
    · exact hr
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨_, nc, hnc, _⟩ := x.pc.ker.linkP t nt ht c hc
  have hcs : c.id.step = t.id.step - 1 := by have := x.pc.pb nt hm c hc; rw [hid] at this; exact this
  have hf : forb (shiftPid c d) = false := by
    rw [shift_parent x t nt ht hts c hc]
    have := x.hnf nt hm; rw [hid] at this; exact this
  have := mem_newRowIds_of_mem_newParents (Trunc.trunc H) d forb c (by show 0 < H.current_step - 1; have := x.h2; omega)
    (mem_newParents x c nc hnc (by omega)) hf
  rw [shift_parent x t nt ht hts c hc] at this
  exact this

/-- An entry below the top of a top node is owned by the new node of the UP: it is carried by a parent. -/
theorem top_owner_row (t : PathNodeId) (nt : PNodeM) (ht : H.node? t = some nt)
    (hts : t.id.step = H.current_step - 1) (v : PathNodeId) (hv : v ∈ nt.owners)
    (hvs : v.id.step ≠ H.current_step - 1) : v ∈ rowOwners (Trunc.trunc H) d t := by
  obtain ⟨c, hc, nc, hnc, hvc⟩ := x.pc.ker.nbrP t nt ht (by have := x.h2; omega) v hv
  have hrp := (top_newRow x t nt ht hts).2 c hc
  have hcs : c.id.step = H.current_step - 2 := by
    have := x.pc.pb nt (List.mem_of_find?_eq_some ht) c hc; rw [node?_id_eq H t nt ht] at this; omega
  have hT := Trunc.trunc_node?_of H c nc hnc (by omega)
  have hvT : v ∈ (Trunc.cutTop (H.current_step - 1) nc).owners := (Trunc.mem_cutTop_owners _ _ v).mpr ⟨hvc, hvs⟩
  have hvg : v ∈ (Trunc.trunc H).gowners := List.mem_filter.mpr ⟨x.pc.ker.own t nt ht v hv, bne_iff_ne.mpr hvs⟩
  unfold rowOwners
  exact List.mem_append_left _ (List.mem_filter.mpr ⟨mem_unionOwnersOf _ _ c _ v hrp hT hvT,
    List.elem_eq_true_of_mem hvg⟩)

/-- **A kernel lies below the UP of its own truncation.** -/
theorem below_up_trunc (title : String) : Below (addNode (Trunc.trunc H) d title forb) H := by
  have hTcs : (Trunc.trunc H).current_step = H.current_step - 1 := rfl
  have hdT : d.step = (Trunc.trunc H).current_step := by rw [hTcs, x.hd]
  have hbelowT : ∀ n ∈ (Trunc.trunc H).nodes, n.id.id.step < (Trunc.trunc H).current_step := by
    intro n hn
    obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp hn
    obtain ⟨hm0, hs0⟩ := List.mem_filter.mp hn0
    have := x.pc.below n0 hm0
    have hne : n0.id.id.step ≠ H.current_step - 1 := bne_iff_ne.mp hs0
    show n0.id.id.step < H.current_step - 1
    omega
  refine ⟨by rw [addNode_current, hTcs]; omega, fun q hq => ?_, fun p nh hnh => ?_⟩
  · -- global owners
    rw [addNode_gowners]
    by_cases hqs : q.id.step = H.current_step - 1
    · obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (x.pc.ker.gn q hq)
      exact List.mem_append_right _ (top_newRow x q nq hnq hqs).1
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hq, bne_iff_ne.mpr hqs⟩)
  · have hm := List.mem_of_find?_eq_some hnh
    have hid : nh.id = p := node?_id_eq H p nh hnh
    have hpb : p.id.step < H.current_step := by have := x.pc.below nh hm; rw [hid] at this; exact this
    by_cases hpt : p.id.step = H.current_step - 1
    · -- a top node: the new node of the UP
      have hnew := addNode_node?_new (Trunc.trunc H) d title forb hdT hbelowT p
        (top_newRow x p nh hnh hpt).1
      refine ⟨rowNode (Trunc.trunc H) d title p, hnew, fun v hv => ?_, fun c hc => ?_, fun s hs => ?_⟩
      · by_cases hvs : v.id.step = H.current_step - 1
        · have e := x.pc.oos nh hm v hv (by rw [hid, hvs, hpt])
          rw [hid] at e
          subst e
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        · exact top_owner_row x p nh hnh hpt v hv hvs
      · exact (top_newRow x p nh hnh hpt).2 c hc
      · exfalso
        obtain ⟨_, ns, hns, _⟩ := x.pc.ker.linkS p nh hnh s hs
        have h1 := x.pc.sa nh hm s hs
        have h2'' := x.pc.below ns (List.mem_of_find?_eq_some hns)
        rw [node?_id_eq H s ns hns] at h2''
        rw [hid] at h1
        omega
    · -- an old node: `upMap` of its truncation
      have hT := Trunc.trunc_node?_of H p nh hnh hpt
      refine ⟨upMap (Trunc.trunc H) d forb (Trunc.cutTop (H.current_step - 1) nh),
        addNode_node?_old _ d title forb p _ hT, fun v hv => ?_, fun c hc => ?_, fun s hs => ?_⟩
      · rw [upMap_owners]
        by_cases hvs : v.id.step = H.current_step - 1
        · -- a top owner: a new node whose table holds `p`
          obtain ⟨nv, hnv⟩ := x.pc.ker.isNode_owner p nh hnh v hv
          have hpv := x.pc.ker.sym p nh v nv hnh hnv hv
          refine List.mem_append_right _ (List.mem_filter.mpr ⟨(top_newRow x v nv hnv hvs).1, ?_⟩)
          show (rowOwners (Trunc.trunc H) d v).contains (Trunc.cutTop (H.current_step - 1) nh).id = true
          have : (Trunc.cutTop (H.current_step - 1) nh).id = p := hid
          rw [this]
          exact List.elem_eq_true_of_mem (top_owner_row x v nv hnv hvs p hpv (by omega))
        · exact List.mem_append_left _ ((Trunc.mem_cutTop_owners _ _ v).mpr ⟨hv, hvs⟩)
      · rw [upMap_parents]; exact hc
      · rw [upMap_sons]
        by_cases hss : s.id.step = H.current_step - 1
        · -- a new son: `p` is one of its parents
          obtain ⟨hso, ns, hns, _⟩ := x.pc.ker.linkS p nh hnh s hs
          have hps := x.pc.ker.sym p nh s ns hnh hns hso
          have h1 := x.pc.sa nh hm s hs
          rw [hid] at h1
          have hpar := (KernelSplit.parent_of_owner x.pc s ns hns (by have := x.h2; omega) p hps (by omega)).1
          refine List.mem_append_right _ (List.mem_filter.mpr ⟨(top_newRow x s ns hns hss).1, ?_⟩)
          show (rowParents (Trunc.trunc H) d s).contains (Trunc.cutTop (H.current_step - 1) nh).id = true
          have : (Trunc.cutTop (H.current_step - 1) nh).id = p := hid
          rw [this]
          exact List.elem_eq_true_of_mem ((top_newRow x s ns hns hss).2 p hpar)
        · exact List.mem_append_left _ ((Trunc.mem_cutTop_sons _ _ s).mpr ⟨hs, hss⟩)

end AbsSatBin.GraphPath.Model.UpSelf

/-- info: 'AbsSatBin.GraphPath.Model.UpSelf.below_up_trunc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.UpSelf.below_up_trunc
