-- lean/improves_bin/AbsSatBin/GraphPath/Model/BranchRel.lean
import AbsSatBin.GraphPath.Model.BranchFull

/-!
# Exactness relative to a pin, along the machine

**`PairExactRel g x`**: every `x`-compatible link `y–w` lies, together with `x`, on a certificate. It is
`CertLink` for the clique `[x]`, and it gives what the reader needs at `x`:

* `triPin₁_of_pairExactRel`: the witness at each step is the certificate's node, and its links are
  `x`-compatible through the same certificate;
* `commonBranch_of_pairExactRel`: the certificate's node one step below `z` is a common full branch.

**Along the machine** (`PairExactRelAll`: for every live `x`):
* **the review keeps it** (`pairExactRelAll_filterAll_nil`): compatible links after the review were
  compatible before, and certificates survive;
* **`addNode` keeps it where no node merges** (`pairExactRelAll_addNode`, every new node with a single
  parent): each node of the new state has a *shadow* in the old one (itself, or its parent), a compatible
  link has compatible shadows, and the certificate through the shadows extends through the new nodes.

Where it can break is exactly where the pairwise version could not: at a **merge** (a new node with two
parents, whose table is the union of theirs) and at a **join** (the union of two states). A pair takes
its link from one side; a link *relative to `x`* needs witnesses at every step, and those can come from
different sides.
-/

namespace AbsSatBin.GraphPath.Model.BranchRel

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.TriPinCut
open AbsSatBin.GraphPath.Model.CertFix
open AbsSatBin.GraphPath.Model.BranchFull

/-- Every `x`-compatible link lies, with `x`, on a certificate. -/
def PairExactRel (g : GPathM) (x : PathNodeId) : Prop :=
  ∀ y ny w nw, g.node? y = some ny → g.node? w = some nw → x ∈ ny.owners → x ∈ nw.owners →
    Cx g x ny w → CertThrough g [x, y, w]

/-- For every live node. -/
def PairExactRelAll (g : GPathM) : Prop := ∀ x nx, g.node? x = some nx → PairExactRel g x

section
variable {g : GPathM} (c : PinCtx g)
include c

/-- A certificate through `x`, `y` and a node `r` of it makes `y–r` `x`-compatible. -/
theorem cx_of_cert3 {sel : Int → PathNodeId} (hs : ChainSound g sel) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (hxo : sel x.id.step = x) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (hyo : sel y.id.step = y) (l : Int) (h0 : 0 ≤ l)
    (h1 : l < g.current_step) : ∃ nr, g.node? (sel l) = some nr ∧ Cx g x ny (sel l) := by
  obtain ⟨hx0, hx1⟩ := step_range c x nx hx
  obtain ⟨hy0, hy1⟩ := step_range c y ny hy
  have hnx : g.node? (sel x.id.step) = some nx := by rw [hxo]; exact hx
  have hny : g.node? (sel y.id.step) = some ny := by rw [hyo]; exact hy
  obtain ⟨nr, hnr⟩ := cert_node hs l h0 h1
  refine ⟨nr, hnr, nr, nx, hnr, hx, cert_owns hs l y.id.step h0 h1 hy0 hy1 ny hny, fun l' h0' h1' => ?_⟩
  exact ⟨sel l', cert_owns hs l' y.id.step h0' h1' hy0 hy1 ny hny, cert_owns hs l' l h0' h1' h0 h1 nr hnr,
    cert_owns hs l' x.id.step h0' h1' hx0 hx1 nx hnx, (hs.chain.1.1 l' h0' h1').2⟩

/-- **Exactness relative to `x` gives `TriPin₁ g x`.** -/
theorem triPin₁_of_pairExactRel (x : PathNodeId) (h : PairExactRel g x) : TriPin₁ g x := by
  intro y ny w nw nx hy hw hx hxy hxw hC l h0 h1
  obtain ⟨sel, hs, hon⟩ := h y ny w nw hy hw hxy hxw hC
  have hxo := hon x List.mem_cons_self
  have hyo := hon y (List.mem_cons_of_mem _ List.mem_cons_self)
  have hwo := hon w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨hx0, hx1⟩ := step_range c x nx hx
  obtain ⟨hy0, hy1⟩ := step_range c y ny hy
  obtain ⟨hw0, hw1⟩ := step_range c w nw hw
  have hnx : g.node? (sel x.id.step) = some nx := by rw [hxo]; exact hx
  have hny : g.node? (sel y.id.step) = some ny := by rw [hyo]; exact hy
  have hnw : g.node? (sel w.id.step) = some nw := by rw [hwo]; exact hw
  obtain ⟨_, _, cy⟩ := cx_of_cert3 c hs x nx hx hxo y ny hy hyo l h0 h1
  obtain ⟨_, _, cw⟩ := cx_of_cert3 c hs x nx hx hxo w nw hw hwo l h0 h1
  exact ⟨sel l, cert_owns hs l y.id.step h0 h1 hy0 hy1 ny hny, cert_owns hs l w.id.step h0 h1 hw0 hw1 nw hnw,
    cert_owns hs l x.id.step h0 h1 hx0 hx1 nx hnx, (hs.chain.1.1 l h0 h1).2, cy, cw⟩

theorem commonBranch_of_pairExactRel (x : PathNodeId) (h : PairExactRel g x) : CommonBranch g x :=
  commonBranch_of_triPin₁ c x (triPin₁_of_pairExactRel c x h)
end

/-- **The review keeps `PairExactRelAll`.** -/
theorem pairExactRelAll_filterAll_nil (X : GPathM) (hnd : NodupIds X) (h : PairExactRelAll X) :
    PairExactRelAll (filterAll X []) := by
  have hb := KernelIff.below_filterAll_self X hnd []
  intro x nx hx y ny w nw hy hw hxy hxw hC
  obtain ⟨nxX, hnxX, hoX, _, _⟩ := hb.node x nx hx
  obtain ⟨nyX, hnyX, hoY, _, _⟩ := hb.node y ny hy
  obtain ⟨nwX, hnwX, hoW, _, _⟩ := hb.node w nw hw
  have hCX : Cx X x nyX w := by
    obtain ⟨nw', nx', hw', hx', hwy, hl⟩ := hC
    rw [hw] at hw'; cases hw'
    rw [hx] at hx'; cases hx'
    refine ⟨nwX, nxX, hnwX, hnxX, hoY w hwy, fun l h0 h1 => ?_⟩
    obtain ⟨r, hr, hrw, hrx, hrs⟩ := hl l h0 (by rw [← hb.step]; exact h1)
    exact ⟨r, hoY r hr, hoW r hrw, hoX r hrx, hrs⟩
  obtain ⟨sel, hs, hon⟩ := h x nxX hnxX y nyX w nwX hnyX hnwX (hoY x hxy) (hoW x hxw) hCX
  exact ⟨sel, ChainSound_filterAll X [] sel hs (fun _ h => absurd h List.not_mem_nil), hon⟩

-- ============================================================
-- `addNode` without merges
-- ============================================================

section
variable (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)

/-- The shadow of a node of `addNode g d …` in `g`: itself if old, its (first) parent if new. -/
def sh (q : PathNodeId) : PathNodeId :=
  if q.id.step < g.current_step then q else ((rowParents g d q).head?).getD q

variable (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
  (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hmok : MachineOk g) (hnd : NodupIds g)
  (hownb : SelfOwn.OwnBelow g) (hself : ∀ p np, g.node? p = some np → p ∈ np.owners)
  (hsym : ∀ a na b nb, g.node? a = some na → g.node? b = some nb → b ∈ na.owners → a ∈ nb.owners)
  (hnf : ∀ pid ∈ shiftRowIds g d, forb pid = false)
  (hsingle : ∀ z ∈ newRowIds g d forb, ∀ q ∈ rowParents g d z, ∀ q' ∈ rowParents g d z, q = q')

include hd hbelow hnd in
/-- A node of the new state is an old node or a row node. -/
theorem node_cases (q : PathNodeId) (nq : PNodeM) (hq : (addNode g d title forb).node? q = some nq) :
    (∃ n, g.node? q = some n ∧ nq = upMap g d forb n ∧ q.id.step < g.current_step) ∨
      (q ∈ newRowIds g d forb ∧ nq = rowNode g d title q ∧ q.id.step = g.current_step) := by
  have hmem : nq ∈ (addNode g d title forb).nodes := List.mem_of_find?_eq_some hq
  have hid' : nq.id = q := node?_id_eq _ q nq hq
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hl
    have hid : n.id = q := by rw [← hid', ← hEq, upMap_id]
    refine Or.inl ⟨n, by rw [← hid]; exact node?_of_mem hnd n hn, hEq.symm, ?_⟩
    have := hbelow n hn; rw [hid] at this; exact this
  · obtain ⟨z, hz, hEq⟩ := (mem_newRow_iff g d title forb nq).mp hr
    have hzq : z = q := by rw [← hid', hEq, rowNode_id]
    rw [hzq] at hz hEq
    refine Or.inr ⟨hz, hEq, ?_⟩
    rw [mapId_of_mem_newRowIds g d forb q hz]; exact hd

include hpos in
theorem sh_new (q : PathNodeId) (hq : q ∈ newRowIds g d forb) (hs : q.id.step = g.current_step) :
    sh g d q ∈ rowParents g d q := by
  unfold sh
  rw [if_neg (by omega)]
  obtain ⟨p, hp⟩ := exists_rowParent g d forb hpos hq
  cases e : (rowParents g d q).head? with
  | none => rw [List.head?_eq_none_iff] at e; rw [e] at hp; exact absurd hp List.not_mem_nil
  | some p' => exact List.mem_of_mem_head? e

theorem sh_old (q : PathNodeId) (hs : q.id.step < g.current_step) : sh g d q = q := by
  unfold sh; rw [if_pos hs]

include hd hpos hbelow hnd hsingle in
/-- **Entries below the new step pass to the shadow.** -/
theorem sh_entry (q : PathNodeId) (nq : PNodeM) (hq : (addNode g d title forb).node? q = some nq)
    (r : PathNodeId) (hr : r ∈ nq.owners) (hrs : r.id.step < g.current_step) :
    ∃ n, g.node? (sh g d q) = some n ∧ r ∈ n.owners := by
  rcases node_cases g d title forb hd hbelow hnd q nq hq with ⟨n, hn, rfl, hqs⟩ | ⟨hqn, rfl, hqs⟩
  · refine ⟨n, by rw [sh_old g d q hqs]; exact hn, ?_⟩
    rw [upMap_owners] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · exfalso
      have := mapId_of_mem_newRowIds g d forb r (List.mem_filter.mp hr).1
      have : r.id.step = g.current_step := by rw [this]; exact hd
      omega
  · have hp := sh_new g d forb hpos q hqn hqs
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp (rowParent_node g d hpos hp).1
    refine ⟨np, hnp, ?_⟩
    rw [rowNode_owners] at hr
    rcases (mem_rowOwners_iff g d q r).mp hr with ⟨hu, _⟩ | he
    · obtain ⟨p', hp', np', hnp', hrp'⟩ := KernelReader.mem_unionOwnersOf_inv g _ r hu
      rw [hsingle q hqn p' hp' _ hp, hnp] at hnp'; cases hnp'
      exact hrp'
    · exfalso; rw [he] at hrs; omega

include hd hpos hbelow hnd hownb hsingle hself hsym in
/-- **A link passes to the shadows.** -/
theorem sh_link (y : PathNodeId) (ny : PNodeM) (hy : (addNode g d title forb).node? y = some ny)
    (w : PathNodeId) (nw : PNodeM) (hw : (addNode g d title forb).node? w = some nw) (hwy : w ∈ ny.owners) :
    ∃ n, g.node? (sh g d y) = some n ∧ sh g d w ∈ n.owners := by
  rcases node_cases g d title forb hd hbelow hnd w nw hw with ⟨m, hm, _, hws⟩ | ⟨hwn, _, hws⟩
  · obtain ⟨n, hn, hwn⟩ := sh_entry g d title forb hd hpos hbelow hnd hsingle y ny hy w hwy hws
    exact ⟨n, hn, by rw [sh_old g d w hws]; exact hwn⟩
  · have hpw := sh_new g d forb hpos w hwn hws
    obtain ⟨npw, hnpw⟩ := Option.isSome_iff_exists.mp (rowParent_node g d hpos hpw).1
    rcases node_cases g d title forb hd hbelow hnd y ny hy with ⟨n, hn, hEq, hys⟩ | ⟨hyn, hEq, hys⟩
    · -- `w` is a row node gained by the old `y`: `y` is in the table of `w`'s parent
      refine ⟨n, by rw [sh_old g d y hys]; exact hn, ?_⟩
      rw [hEq, upMap_owners] at hwy
      rcases List.mem_append.mp hwy with hwy | hwy
      · exfalso; have := hownb n (List.mem_of_find?_eq_some hn) w hwy; omega
      · have hc := List.mem_of_elem_eq_true (List.mem_filter.mp hwy).2
        have hnid : n.id = y := node?_id_eq g y n hn
        rw [hnid] at hc
        rcases (mem_rowOwners_iff g d w y).mp hc with ⟨hu, _⟩ | he
        · obtain ⟨p', hp', np', hnp', hyp'⟩ := KernelReader.mem_unionOwnersOf_inv g _ y hu
          rw [hsingle w hwn p' hp' _ hpw, hnpw] at hnp'; cases hnp'
          exact hsym (sh g d w) npw y n hnpw hn hyp'
        · exfalso; rw [he] at hys; omega
    · -- two row nodes that own each other are the same
      have hwyeq : w = y := by
        rw [hEq, rowNode_owners] at hwy
        rcases (mem_rowOwners_iff g d y w).mp hwy with ⟨hu, _⟩ | he
        · exfalso
          obtain ⟨p', _, np', hnp', hwp'⟩ := KernelReader.mem_unionOwnersOf_inv g _ w hu
          have := hownb np' (List.mem_of_find?_eq_some hnp') w hwp'; omega
        · exact he
      rw [hwyeq] at hnpw ⊢
      exact ⟨npw, hnpw, hself _ npw hnpw⟩

include hpos in
/-- A certificate through the shadow, extended, goes through the node. -/
theorem sh_extend (q : PathNodeId) (hq : q.id.step < g.current_step ∨ q ∈ newRowIds g d forb ∧ q.id.step = g.current_step)
    (sel : Int → PathNodeId) (hon : sel (sh g d q).id.step = sh g d q) :
    extend g d sel q.id.step = q := by
  rcases hq with hs | ⟨hqn, hs⟩
  · rw [extend_below g d sel q.id.step hs]; rw [sh_old g d q hs] at hon; exact hon
  · have hp := sh_new g d forb hpos q hqn hs
    obtain ⟨_, hps⟩ := rowParent_node g d hpos hp
    have hz : shiftPid (sh g d q) d = q := eq_of_beq (List.mem_filter.mp hp).2
    rw [hs, extend_top]
    unfold extendPid; rw [if_pos hpos]
    have : sel (g.current_step - 1) = sh g d q := by rw [← hps]; exact hon
    rw [this, hz]

include hd hpos hbelow hmok hnd hownb hself hsym hnf hsingle in
/-- **`addNode` without merges keeps exactness relative to every node.** -/
theorem pairExactRelAll_addNode (h : PairExactRelAll g) : PairExactRelAll (addNode g d title forb) := by
  intro x nx hx y ny w nw hy hw hxy hxw hC
  have kind : ∀ q nq, (addNode g d title forb).node? q = some nq →
      q.id.step < g.current_step ∨ q ∈ newRowIds g d forb ∧ q.id.step = g.current_step := by
    intro q nq hq
    rcases node_cases g d title forb hd hbelow hnd q nq hq with ⟨_, _, _, hs⟩ | ⟨hn, _, hs⟩
    · exact Or.inl hs
    · exact Or.inr ⟨hn, hs⟩
  obtain ⟨ny₀, hny₀, hxy₀⟩ := sh_link g d title forb hd hpos hbelow hnd hownb hself hsym hsingle y ny hy x nx hx hxy
  obtain ⟨nw₀, hnw₀, hxw₀⟩ := sh_link g d title forb hd hpos hbelow hnd hownb hself hsym hsingle w nw hw x nx hx hxw
  have hwy : w ∈ ny.owners := by obtain ⟨_, _, _, _, h, _⟩ := hC; exact h
  obtain ⟨ny₁, hny₁, hwy₀⟩ := sh_link g d title forb hd hpos hbelow hnd hownb hself hsym hsingle y ny hy w nw hw hwy
  rw [hny₀] at hny₁; cases hny₁
  have hxx : x ∈ nx.owners := by
    rcases node_cases g d title forb hd hbelow hnd x nx hx with ⟨n, hn', hEq, _⟩ | ⟨_, hEq, _⟩
    · rw [hEq, upMap_owners]; exact List.mem_append_left _ (hself x n hn')
    · rw [hEq, rowNode_owners]; exact (mem_rowOwners_iff g d x x).mpr (Or.inr rfl)
  obtain ⟨nx₀, hnx₀, _⟩ := sh_link g d title forb hd hpos hbelow hnd hownb hself hsym hsingle x nx hx x nx hx hxx
  -- the link, on the shadows
  have hC₀ : Cx g (sh g d x) ny₀ (sh g d w) := by
    obtain ⟨nw', nx', hw', hx', _, hl⟩ := hC
    rw [hw] at hw'; cases hw'
    rw [hx] at hx'; cases hx'
    refine ⟨nw₀, nx₀, hnw₀, hnx₀, hwy₀, fun l h0 h1 => ?_⟩
    obtain ⟨r, hr, hrw, hrx, hrs⟩ := hl l h0 (by rw [addNode_current]; omega)
    have hl' : r.id.step < g.current_step := by rw [hrs]; exact h1
    obtain ⟨a, ha, hra⟩ := sh_entry g d title forb hd hpos hbelow hnd hsingle y ny hy r hr hl'
    obtain ⟨b, hb, hrb⟩ := sh_entry g d title forb hd hpos hbelow hnd hsingle w nw hw r hrw hl'
    obtain ⟨e, he, hre⟩ := sh_entry g d title forb hd hpos hbelow hnd hsingle x nx hx r hrx hl'
    rw [hny₀] at ha; cases ha
    rw [hnw₀] at hb; cases hb
    rw [hnx₀] at he; cases he
    exact ⟨r, hra, hrb, hre, hrs⟩
  obtain ⟨sel, hs, hon⟩ := h (sh g d x) nx₀ hnx₀ (sh g d y) ny₀ (sh g d w) nw₀ hny₀ hnw₀ hxy₀ hxw₀ hC₀
  refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hs
    (hnf _ (extendPid_mem_shiftRowIds g d sel hs.chain.1)), fun q hq => ?_⟩
  rcases List.mem_cons.mp hq with e | hq
  · rw [e]; exact sh_extend g d forb hpos x (kind x nx hx) sel (hon _ List.mem_cons_self)
  rcases List.mem_cons.mp hq with e | hq
  · rw [e]; exact sh_extend g d forb hpos y (kind y ny hy) sel
      (hon _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [List.mem_singleton.mp hq]
    exact sh_extend g d forb hpos w (kind w nw hw) sel
      (hon _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
end

/-- info: 'AbsSatBin.GraphPath.Model.BranchRel.triPin₁_of_pairExactRel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms triPin₁_of_pairExactRel

/-- info: 'AbsSatBin.GraphPath.Model.BranchRel.pairExactRelAll_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairExactRelAll_addNode

end AbsSatBin.GraphPath.Model.BranchRel
