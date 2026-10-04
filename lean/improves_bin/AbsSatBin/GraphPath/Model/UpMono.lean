-- lean/improves_bin/AbsSatBin/GraphPath/Model/UpMono.lean
import AbsSatBin.GraphPath.Model.KernelUp

/-!
# `addNode` keeps `Below`

If `h` sits below `X` (same step, fewer global owners, every node of `h` a node of `X` with fewer owners, parents
and sons), then the row `addNode` puts on top of `h` sits below the row it puts on top of `X`: the last row of `h`
is part of the last row of `X`, so every candidate identifier of `h` is one of `X`, a row node of `h` has fewer
parents, and what its parents own in `h` they own in `X`. Old nodes gain, in `h`, only row nodes that they also
gain in `X`.

This is the monotonicity the induction of `FExt` needs to lift a pinned kernel of a source to its piece
(`docs/context/escalera_reader.md` §4.2ο, bridge M3w).
-/

namespace AbsSatBin.GraphPath.Model.UpMono

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel

section
variable {X h : GPathM} (hb : Below X h)
include hb

theorem newParents_mono : ∀ q ∈ newParents h, q ∈ newParents X := by
  intro q hq
  unfold newParents at hq ⊢
  by_cases hpos : h.current_step > 0
  · rw [if_pos hpos] at hq
    rw [if_pos (by rw [hb.step]; exact hpos), hb.step]
    have hqs := Parents.mem_line_step _ _ q hq
    obtain ⟨n, hn, hnid⟩ := Parents.mem_nodes_of_mem_line _ _ q hq
    have hsome := node?_isSome_of_mem h n hn
    rw [hnid] at hsome
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨nx, hnx, _, _, _⟩ := hb.node q n' hn'
    have := Threaded.mem_line_of_node? X q nx hnx
    rwa [hqs] at this
  · rw [if_neg hpos] at hq; cases hq

theorem shiftRowIds_mono (d : NodeId) : ∀ pid ∈ shiftRowIds h d, pid ∈ shiftRowIds X d := by
  intro pid hp
  unfold shiftRowIds at hp ⊢
  by_cases hpos : h.current_step > 0
  · rw [if_pos hpos] at hp
    rw [if_pos (by rw [hb.step]; exact hpos)]
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((mem_dedupPids _ _).mp hp)
    exact (mem_dedupPids _ _).mpr (List.mem_map_of_mem (newParents_mono hb q hq))
  · rw [if_neg hpos] at hp
    rw [if_neg (by rw [hb.step]; exact hpos)]
    exact hp

theorem newRowIds_mono (d : NodeId) (forb : PathNodeId → Bool) :
    ∀ pid ∈ newRowIds h d forb, pid ∈ newRowIds X d forb := by
  intro pid hp
  obtain ⟨h1, h2⟩ := (mem_newRowIds h d forb pid).mp hp
  exact (mem_newRowIds X d forb pid).mpr ⟨shiftRowIds_mono hb d pid h1, h2⟩

theorem rowParents_mono (d : NodeId) (pid : PathNodeId) :
    ∀ q ∈ rowParents h d pid, q ∈ rowParents X d pid := by
  intro q hq
  obtain ⟨h1, h2⟩ := List.mem_filter.mp hq
  exact List.mem_filter.mpr ⟨newParents_mono hb q h1, h2⟩

theorem rowOwners_mono (d : NodeId) (pid : PathNodeId) :
    ∀ v ∈ rowOwners h d pid, v ∈ rowOwners X d pid := by
  intro v hv
  unfold rowOwners at hv ⊢
  rcases List.mem_append.mp hv with hl | hr
  · obtain ⟨hu, hc⟩ := List.mem_filter.mp hl
    have hvg : v ∈ h.gowners := List.mem_of_elem_eq_true hc
    obtain ⟨c, hc', nc, hnc, hvc⟩ := KernelReader.mem_unionOwnersOf_inv h _ v hu
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node c nc hnc
    refine List.mem_append_left _ (List.mem_filter.mpr ⟨?_, List.elem_eq_true_of_mem (hb.gow v hvg)⟩)
    exact mem_unionOwnersOf X _ c nx v (rowParents_mono hb d pid c hc') hnx (ho v hvc)
  · exact List.mem_append_right _ hr

/-- **`addNode` keeps `Below`.** -/
theorem below_addNode (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hdX : d.step = X.current_step) (hbX : ∀ n ∈ X.nodes, n.id.id.step < X.current_step)
    (hbh : ∀ n ∈ h.nodes, n.id.id.step < h.current_step) :
    Below (addNode X d title forb) (addNode h d title forb) where
  step := by rw [addNode_current, addNode_current, hb.step]
  gow := by
    intro q hq
    rw [addNode_gowners] at hq ⊢
    rcases List.mem_append.mp hq with h1 | h1
    · exact List.mem_append_left _ (hb.gow q h1)
    · exact List.mem_append_right _ (newRowIds_mono hb d forb q h1)
  node := by
    intro p nh hnh
    have hdh : d.step = h.current_step := by rw [← hb.step]; exact hdX
    rcases KernelUp.node_cases h d title forb hdh hbh p nh hnh with ⟨n₀, hn₀, rfl⟩ | ⟨hp, rfl⟩
    · obtain ⟨nx, hnx, ho, hpa, hs⟩ := hb.node p n₀ hn₀
      have hid : n₀.id = nx.id := by rw [node?_id_eq _ p n₀ hn₀, node?_id_eq _ p nx hnx]
      refine ⟨upMap X d forb nx, addNode_node?_old X d title forb p nx hnx, ?_, ?_, ?_⟩
      · intro v hv
        rw [upMap_owners] at hv ⊢
        rcases List.mem_append.mp hv with h1 | h1
        · exact List.mem_append_left _ (ho v h1)
        · obtain ⟨hw, hro⟩ := (KernelUp.mem_gainedOwners h d forb n₀ v).mp h1
          refine List.mem_append_right _ ((KernelUp.mem_gainedOwners X d forb nx v).mpr
            ⟨newRowIds_mono hb d forb v hw, ?_⟩)
          rw [← hid]; exact rowOwners_mono hb d v _ hro
      · intro v hv
        rw [upMap_parents] at hv ⊢
        exact hpa v hv
      · intro v hv
        rw [upMap_sons] at hv ⊢
        rcases List.mem_append.mp hv with h1 | h1
        · exact List.mem_append_left _ (hs v h1)
        · obtain ⟨hw, hrp⟩ := (KernelUp.mem_gainedSons h d forb n₀ v).mp h1
          refine List.mem_append_right _ ((KernelUp.mem_gainedSons X d forb nx v).mpr
            ⟨newRowIds_mono hb d forb v hw, ?_⟩)
          rw [← hid]; exact rowParents_mono hb d v _ hrp
    · refine ⟨rowNode X d title p, addNode_node?_new X d title forb hdX hbX p (newRowIds_mono hb d forb p hp),
        ?_, ?_, ?_⟩
      · intro v hv
        rw [rowNode_owners] at hv ⊢
        exact rowOwners_mono hb d p v hv
      · intro v hv
        rw [rowNode_parents] at hv ⊢
        exact rowParents_mono hb d p v hv
      · intro v hv
        rw [rowNode_sons] at hv
        cases hv

end

end AbsSatBin.GraphPath.Model.UpMono

/-- info: 'AbsSatBin.GraphPath.Model.UpMono.below_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.UpMono.below_addNode
