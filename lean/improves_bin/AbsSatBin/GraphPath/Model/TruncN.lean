-- lean/improves_bin/AbsSatBin/GraphPath/Model/TruncN.lean
import AbsSatBin.GraphPath.Model.UpSelf

/-!
# Cutting a kernel down to a row, keeping the machine's invariants (`docs/context/escalera_reader.md` §4.2ο.2)

* **`Good forb g`**: the context the chain form of M1b reads from a state: the pin context (`KernelSplit.PinCtx`: a
  kernel with its window facts), the reader context (`Reader.RCtx`) and no prohibited node.
* **`good_trunc`**: cutting the top row (`Trunc.trunc`) keeps it. **`truncN j g`** cuts `j` rows; **`good_truncN`**.
* **`truncN_node_of`**: a node of `g` below the new top is a node of the cut, with every entry below the new top;
  **`truncN_node_inv`**: a node of the cut is a node of `g`, with fewer entries.
* **`below_of_owners`**: a state with the pin context lies below another one when their tops agree and every table
  of the first is inside the table of the second (links follow: an entry at the next row is a parent or a son).
-/

namespace AbsSatBin.GraphPath.Model.TruncN

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.Trunc

/-- The context read from a state. -/
structure Good (forb : PathNodeId → Bool) (g : GPathM) : Prop where
  pc : KernelSplit.PinCtx g
  rc : Reader.RCtx g
  nf : MapReachable.NoForb forb g

theorem mem_trunc_nodes {g : GPathM} {n' : PNodeM} (h : n' ∈ (trunc g).nodes) :
    ∃ n ∈ g.nodes, n.id.id.step ≠ g.current_step - 1 ∧ n' = cutTop (g.current_step - 1) n := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h
  obtain ⟨hm, hs⟩ := List.mem_filter.mp hn
  exact ⟨n, hm, bne_iff_ne.mp hs, rfl⟩

theorem mem_trunc_nodes_of {g : GPathM} {n : PNodeM} (hn : n ∈ g.nodes) (hs : n.id.id.step ≠ g.current_step - 1) :
    cutTop (g.current_step - 1) n ∈ (trunc g).nodes :=
  List.mem_map_of_mem (List.mem_filter.mpr ⟨hn, bne_iff_ne.mpr hs⟩)

theorem hasNode_trunc {g : GPathM} {q : PathNodeId} (h : GownersNodes.HasNode g q) (hs : q.id.step ≠ g.current_step - 1) :
    GownersNodes.HasNode (trunc g) q := by
  obtain ⟨n, hn, hid⟩ := h
  exact ⟨cutTop _ n, mem_trunc_nodes_of hn (by rw [hid]; exact hs), hid⟩

/-- **Cutting the top row keeps the context.** -/
theorem good_trunc {forb : PathNodeId → Bool} {g : GPathM} (h : Good forb g) : Good forb (trunc g) := by
  have hcs : (trunc g).current_step = g.current_step - 1 := rfl
  have below' : ∀ n ∈ (trunc g).nodes, n.id.id.step < (trunc g).current_step := by
    intro n' hn'
    obtain ⟨n, hn, hs, rfl⟩ := mem_trunc_nodes hn'
    have := h.pc.below n hn
    show n.id.id.step < g.current_step - 1
    omega
  have nd' : NodupIds (trunc g) := by
    unfold NodupIds
    show (((g.nodes.filter (fun n => n.id.id.step != g.current_step - 1)).map (cutTop (g.current_step - 1))).map
      (·.id)).Nodup
    rw [List.map_map]
    have he : ((·.id) ∘ cutTop (g.current_step - 1)) = (fun n : PNodeM => n.id) := rfl
    rw [he]
    exact List.Sublist.nodup (List.Sublist.map _ List.filter_sublist) h.pc.nd
  have oos' : SelfOwn.OOS (trunc g) := by
    intro n' hn' q hq hqs
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.pc.oos n hn q ((mem_cutTop_owners _ _ q).mp hq).1 hqs
  have pb' : Parents.PBelow (trunc g) := by
    intro n' hn' p hp
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.pc.pb n hn p hp
  have sa' : Sons.SAbove (trunc g) := by
    intro n' hn' s hs
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.pc.sa n hn s ((mem_cutTop_sons _ _ s).mp hs).1
  have snn' : SelfOwn.SNN (trunc g) := by
    intro n' hn'
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.pc.snn n hn
  have pn' : Parents.PN (trunc g) := by
    intro n' hn' p hp
    obtain ⟨n, hn, hs, rfl⟩ := mem_trunc_nodes hn'
    have hps := h.pc.pb n hn p hp
    have hnb := h.pc.below n hn
    exact hasNode_trunc (h.rc.shape.pn n hn p hp) (by omega)
  refine ⟨⟨kernel_trunc h.pc.ker h.pc.pb h.pc.sa h.pc.below, nd', oos', pb', sa', snn', below'⟩,
    ⟨oos', snn', ?_, ⟨pn', pb', ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, below', nd'⟩, ?_⟩
  · intro q hq
    obtain ⟨hq, hqs⟩ := List.mem_filter.mp hq
    exact hasNode_trunc (h.rc.gn q hq) (bne_iff_ne.mp hqs)
  · intro n' hn'
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.rc.shape.notroot n hn
  · intro n' hn'
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.rc.rootz n hn
  · intro n' hn' p hp
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.rc.pmp n hn p hp
  · intro n' hn' p hp
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.rc.gpmp.1 n hn p hp
  · intro n' hn'
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.rc.gpmp.2 n hn
  · intro n' hn' q hq
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    obtain ⟨hq, hqs⟩ := (mem_cutTop_owners _ _ q).mp hq
    have := h.rc.ownb n hn q hq
    show q.id.step < g.current_step - 1
    omega
  · intro n' hn'
    obtain ⟨n, hn, _, rfl⟩ := mem_trunc_nodes hn'
    exact h.nf n hn

/-- Cut `j` rows off the top. -/
def truncN : Nat → GPathM → GPathM
  | 0, g => g
  | j + 1, g => truncN j (trunc g)

theorem truncN_cs : ∀ (j : Nat) (g : GPathM), (truncN j g).current_step = g.current_step - j := by
  intro j
  induction j with
  | zero => intro g; simp [truncN]
  | succ j ih => intro g; simp only [truncN]; rw [ih]; show g.current_step - 1 - (j : Int) = _; push_cast; omega

theorem good_truncN {forb : PathNodeId → Bool} : ∀ (j : Nat) (g : GPathM), Good forb g → Good forb (truncN j g) := by
  intro j
  induction j with
  | zero => intro g h; exact h
  | succ j ih => intro g h; exact ih _ (good_trunc h)

/-- **A node of the cut is a node of the state, with fewer entries, the same parents and fewer sons.** -/
theorem truncN_node_inv : ∀ (j : Nat) (g : GPathM) (p : PathNodeId) (n' : PNodeM), (truncN j g).node? p = some n' →
    ∃ n, g.node? p = some n ∧ (∀ v ∈ n'.owners, v ∈ n.owners) ∧ n'.parents = n.parents ∧
      ∀ s ∈ n'.sons, s ∈ n.sons := by
  intro j
  induction j with
  | zero => intro g p n' h; exact ⟨n', h, fun _ x => x, rfl, fun _ x => x⟩
  | succ j ih =>
    intro g p n' h
    obtain ⟨n1, hn1, ho1, hp1, hs1⟩ := ih (trunc g) p n' h
    obtain ⟨n, hn, _, rfl⟩ := trunc_node?_some g p n1 hn1
    exact ⟨n, hn, fun v hv => ((mem_cutTop_owners _ _ v).mp (ho1 v hv)).1, hp1,
      fun s hs => ((mem_cutTop_sons _ _ s).mp (hs1 s hs)).1⟩

/-- **A node below the new top is a node of the cut, with every entry below the new top.** -/
theorem truncN_node_of : ∀ (j : Nat) (g : GPathM) (p : PathNodeId) (n : PNodeM), g.node? p = some n →
    p.id.step < g.current_step - j →
    ∃ n', (truncN j g).node? p = some n' ∧ ∀ v ∈ n.owners, v.id.step < g.current_step - j → v ∈ n'.owners := by
  intro j
  induction j with
  | zero => intro g p n h _; exact ⟨n, h, fun _ x _ => x⟩
  | succ j ih =>
    intro g p n h hps
    have hT := trunc_node?_of g p n h (by push_cast at hps; omega)
    obtain ⟨n', hn', ho'⟩ := ih (trunc g) p _ hT (by show p.id.step < g.current_step - 1 - (j : Int); push_cast at hps; omega)
    refine ⟨n', hn', fun v hv hvs => ho' v ((mem_cutTop_owners _ _ v).mpr ⟨hv, by push_cast at hvs; omega⟩) ?_⟩
    show v.id.step < g.current_step - 1 - (j : Int)
    push_cast at hvs; omega

/-- **Tables inside tables give `Below`**, between two states with the pin context and the same top. -/
theorem below_of_owners {W T : GPathM} (hW : KernelSplit.PinCtx W) (hT : KernelSplit.PinCtx T)
    (hcs : W.current_step = T.current_step)
    (hown : ∀ p np, T.node? p = some np → ∃ nW, W.node? p = some nW ∧ ∀ v ∈ np.owners, v ∈ nW.owners) :
    Below W T := by
  refine ⟨hcs, fun q hq => ?_, fun p np hnp => ?_⟩
  · obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (hT.ker.gn q hq)
    obtain ⟨nW, hnW, _⟩ := hown q nq hnq
    exact hW.ker.gow q nW hnW
  · obtain ⟨nW, hnW, ho⟩ := hown p np hnp
    have hid : np.id = p := node?_id_eq T p np hnp
    refine ⟨nW, hnW, ho, fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨hco, nc, hnc, _⟩ := hT.ker.linkP p np hnp c hc
      have hcs' : c.id.step = p.id.step - 1 := by
        have := hT.pb np (List.mem_of_find?_eq_some hnp) c hc; rw [hid] at this; exact this
      have hc0 : 0 ≤ c.id.step := by
        have := hT.snn nc (List.mem_of_find?_eq_some hnc); rw [node?_id_eq T c nc hnc] at this; exact this
      exact (KernelSplit.parent_of_owner hW p nW hnW (by omega) c (ho c hco) hcs').1
    · obtain ⟨hco, nc, hnc, _⟩ := hT.ker.linkS p np hnp c hc
      have hcs' : c.id.step = p.id.step + 1 := by
        have := hT.sa np (List.mem_of_find?_eq_some hnp) c hc; rw [hid] at this; exact this
      have hcb : c.id.step < T.current_step := by
        have := hT.below nc (List.mem_of_find?_eq_some hnc); rw [node?_id_eq T c nc hnc] at this; exact this
      exact (KernelSplit.son_of_owner hW p nW hnW (by omega) c (ho c hco) hcs').1

end AbsSatBin.GraphPath.Model.TruncN

/-- info: 'AbsSatBin.GraphPath.Model.TruncN.good_truncN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.TruncN.good_truncN
