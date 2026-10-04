-- lean/improves_bin/AbsSatBin/GraphPath/Model/BranchFull.lean
import AbsSatBin.GraphPath.Model.OneShot

/-!
# Branch fullness, and pairwise exactness along the machine

At a node `z` with several parents, the table is (inside) the union of the parents' tables. Relative
to a pin `x`, the **branch** of a parent `p` is `T(z) ∩ T(p) ∩ T(x)`, and it is **full** when it has an
entry at every step — that is `Cx g x nz p`.

* **`FullBranch g x`**: every node that owns `x` has a full branch. **`CommonBranch g x`**: every
  `x`-compatible link `z–w` has a parent of `z` that is a full branch of both. Both are what `TriPin₁`
  says one step below a node (`fullBranch_of_triPin₁`, `commonBranch_of_triPin₁`): necessary for the
  reader's route.
* **`PairExact g`**: every link of a table lies on a certificate. It gives `FullBranch`
  (`fullBranch_of_pairExact`): the certificate of the link `z–x` goes through one parent, and its
  nodes fill that branch.

**`PairExact` along the machine** — the operations that build and merge the tables keep it:
* the review (`pairExact_filterAll_nil`): links only disappear, certificates survive;
* `join` (`pairExact_join`): a link of the join comes from one side, and so does its certificate;
* `addNode` when no window is skipped (`pairExact_addNode`): every new link comes from a single parent
  (the union is taken link by link), and a certificate through that parent extends through the new
  node. **Merges do not break it**: a pair never needs two branches.

What is left for `PairExact` is exactly the two operations that enforce the formula: the requirement
filter and the review after a skipped (prohibited) window.
-/

namespace AbsSatBin.GraphPath.Model.BranchFull

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.TriPinCut
open AbsSatBin.GraphPath.Model.CertFix

/-- Every node that owns `x` has a full branch. -/
def FullBranch (g : GPathM) (x : PathNodeId) : Prop :=
  ∀ z nz, g.node? z = some nz → x ∈ nz.owners → 1 ≤ z.id.step → ∃ p ∈ nz.parents, Cx g x nz p

/-- Every `x`-compatible link from `z` has a parent of `z` that is a full branch of both ends. -/
def CommonBranch (g : GPathM) (x : PathNodeId) : Prop :=
  ∀ z nz w nw nx, g.node? z = some nz → g.node? w = some nw → g.node? x = some nx →
    x ∈ nz.owners → x ∈ nw.owners → 1 ≤ z.id.step → Cx g x nz w →
    ∃ p ∈ nz.parents, p ∈ nw.owners ∧ p ∈ nx.owners ∧ Cx g x nz p ∧ Cx g x nw p

/-- Every link of a table lies on a certificate. -/
def PairExact (g : GPathM) : Prop :=
  ∀ y ny v, g.node? y = some ny → v ∈ ny.owners → CertThrough g [y, v]

section
variable {g : GPathM} (c : PinCtx g)
include c

theorem commonBranch_of_triPin₁ (x : PathNodeId) (h : TriPin₁ g x) : CommonBranch g x := by
  intro z nz w nw nx hz hw hx hxz hxw h1 hC
  have hr := step_range c z nz hz
  -- idx: adjacent gpath rows (one row per map step, bin map too)
  obtain ⟨r, hr', hrw, hrx, hrs, cz, cw⟩ := h z nz w nw nx hz hw hx hxz hxw hC (z.id.step - 1) (by omega)
    (by omega)
  exact ⟨r, (parent_of_owner c z nz hz h1 r hr' hrs).1, hrw, hrx, cz, cw⟩

theorem fullBranch_of_triPin₁ (x : PathNodeId) (h : TriPin₁ g x) : FullBranch g x := by
  intro z nz hz hxz h1
  obtain ⟨nx, hnx⟩ := c.ker.isNode_owner z nz hz x hxz
  obtain ⟨p, hp, _, _, cz, _⟩ := commonBranch_of_triPin₁ c x h z nz z nz nx hz hz hnx hxz hxz h1
    (cx_self c hnx hz hxz)
  exact ⟨p, hp, cz⟩

/-- **Pairwise exactness gives full branches.** -/
theorem fullBranch_of_pairExact (x : PathNodeId) (h : PairExact g) : FullBranch g x := by
  intro z nz hz hxz h1
  obtain ⟨nx, hnx⟩ := c.ker.isNode_owner z nz hz x hxz
  obtain ⟨sel, hs, hon⟩ := h z nz x hz hxz
  have hzo : sel z.id.step = z := hon z List.mem_cons_self
  have hxo : sel x.id.step = x := hon x (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨hz0, hz1⟩ := step_range c z nz hz
  obtain ⟨hx0, hx1⟩ := step_range c x nx hnx
  have hnz : g.node? (sel z.id.step) = some nz := by rw [hzo]; exact hz
  have hnx' : g.node? (sel x.id.step) = some nx := by rw [hxo]; exact hnx
  -- idx: adjacent gpath rows (one row per map step, bin map too)
  have hpar := hs.chain.1.2 (z.id.step - 1) (by omega) (by omega)
  -- idx: adjacent gpath rows (one row per map step, bin map too)
  have he : z.id.step - 1 + 1 = z.id.step := by omega
  rw [he, hnz] at hpar
  -- idx: adjacent gpath rows (one row per map step, bin map too)
  obtain ⟨np, hnp⟩ := cert_node hs (z.id.step - 1) (by omega) (by omega)
  refine ⟨_, hpar, np, nx, hnp, hnx, ?_, fun l h0 h1' => ?_⟩
  · -- idx: adjacent gpath rows (one row per map step, bin map too)
    exact cert_owns hs (z.id.step - 1) z.id.step (by omega) (by omega) hz0 hz1 nz hnz
  · refine ⟨sel l, cert_owns hs l z.id.step h0 h1' hz0 hz1 nz hnz, ?_,
      cert_owns hs l x.id.step h0 h1' hx0 hx1 nx hnx', (hs.chain.1.1 l h0 h1').2⟩
    -- idx: adjacent gpath rows (one row per map step, bin map too)
    exact cert_owns hs l (z.id.step - 1) h0 h1' (by omega) (by omega) np hnp
end

-- ============================================================
-- `PairExact` along the machine
-- ============================================================

/-- **The review keeps `PairExact`.** -/
theorem pairExact_filterAll_nil (X : GPathM) (hnd : NodupIds X) (h : PairExact X) :
    PairExact (filterAll X []) := by
  have hb := KernelIff.below_filterAll_self X hnd []
  intro y ny v hy hv
  obtain ⟨nx, hnx, ho, _, _⟩ := hb.node y ny hy
  obtain ⟨sel, hs, hon⟩ := h y nx v hnx (ho v hv)
  exact ⟨sel, ChainSound_filterAll X [] sel hs (fun _ h => absurd h List.not_mem_nil), hon⟩

/-- **`join` keeps `PairExact`.** -/
theorem pairExact_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (h₁ : PairExact g₁)
    (h₂ : PairExact g₂) : PairExact (join g₁ g₂) := by
  intro y ny v hy hv
  rcases join_owners_source g₁ g₂ y ny hy v hv with ⟨m, hm, hvm⟩ | ⟨m, hm, hvm⟩
  · obtain ⟨sel, hs, hon⟩ := h₁ y m v hm hvm
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hs, hon⟩
  · obtain ⟨sel, hs, hon⟩ := h₂ y m v hm hvm
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hs, hon⟩

theorem pairExact_doJoin (g₁ g₂ : GPathM) (h₁ : PairExact g₁) (h₂ : PairExact g₂) :
    PairExact (doJoin g₁ g₂) := by
  unfold doJoin
  cases hok : okJoin g₁ g₂ with
  | true => exact pairExact_join g₁ g₂ hok h₁ h₂
  | false => exact h₁

/-- **`addNode` keeps `PairExact` when no window is skipped**: every new link comes from one parent. -/
theorem pairExact_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hmok : MachineOk g) (hnd : NodupIds g)
    (hownb : SelfOwn.OwnBelow g) (hself : ∀ p np, g.node? p = some np → p ∈ np.owners)
    (hnf : ∀ pid ∈ shiftRowIds g d, forb pid = false) (h : PairExact g) :
    PairExact (addNode g d title forb) := by
  -- extending a certificate of `g`
  have ext : ∀ sel, ChainSound g sel → ChainSound (addNode g d title forb) (extend g d sel) :=
    fun sel hs => ChainSound_addNode g d title forb hd hbelow hmok sel hs
      (hnf _ (extendPid_mem_shiftRowIds g d sel hs.chain.1))
  have extTop : ∀ sel, extend g d sel g.current_step = shiftPid (sel (g.current_step - 1)) d := by
    intro sel; rw [extend_top]; unfold extendPid; rw [if_pos hpos]
  -- a certificate through a parent `p` of a row node `z`, extended, goes through `z`
  have viaParent : ∀ z p sel, p ∈ rowParents g d z → ChainSound g sel → sel p.id.step = p →
      extend g d sel z.id.step = z ∧ z.id.step = g.current_step := by
    intro z p sel hp hs hsp
    obtain ⟨_, hps⟩ := rowParent_node g d hpos hp
    have hz : shiftPid p d = z := eq_of_beq (List.mem_filter.mp hp).2
    have hzs : z.id.step = g.current_step := by rw [← hz]; exact hd
    refine ⟨?_, hzs⟩
    rw [hzs, extTop]
    have : sel (g.current_step - 1) = p := by rw [← hps]; exact hsp
    rw [this, hz]
  have below : ∀ (sel : Int → PathNodeId) (q : PathNodeId), q.id.step < g.current_step → extend g d sel q.id.step = sel q.id.step :=
    fun sel q hq => extend_below g d sel q.id.step hq
  -- owners are below the current step
  have ownb : ∀ p np, g.node? p = some np → ∀ q ∈ np.owners, q.id.step < g.current_step :=
    fun p np hnp q hq => hownb np (List.mem_of_find?_eq_some hnp) q hq
  have nodeb : ∀ p np, g.node? p = some np → p.id.step < g.current_step := by
    intro p np hnp
    have := hbelow np (List.mem_of_find?_eq_some hnp); rw [node?_id_eq g p np hnp] at this; exact this
  intro y' n' v hn' hv
  have hmem : n' ∈ (addNode g d title forb).nodes := List.mem_of_find?_eq_some hn'
  have hid' : n'.id = y' := node?_id_eq _ y' n' hn'
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · -- an old node
    obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hl
    have hny : g.node? y' = some n := by
      have hid : n.id = y' := by rw [← hid', ← hEq, upMap_id]
      rw [← hid]; exact node?_of_mem hnd n hn
    have hys := nodeb y' n hny
    rw [← hEq, upMap_owners] at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨sel, hs, hon⟩ := h y' n v hny hv
      refine ⟨extend g d sel, ext sel hs, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with e | hq
      · rw [e, below sel y' hys]; exact hon y' List.mem_cons_self
      · rw [List.mem_singleton.mp hq, below sel v (ownb y' n hny v hv)]
        exact hon v (List.mem_cons_of_mem _ List.mem_cons_self)
    · -- a gained owner: a row node `v` that owns `y'`, through one of its parents
      obtain ⟨hvnew, hvc⟩ := List.mem_filter.mp hv
      have hnid : n.id = y' := by rw [← hid', ← hEq, upMap_id]
      rw [hnid] at hvc
      rcases (mem_rowOwners_iff g d v y').mp (List.mem_of_elem_eq_true hvc) with ⟨hu, _⟩ | he
      · obtain ⟨p, hp, np, hnp, hyp⟩ := KernelReader.mem_unionOwnersOf_inv g _ y' hu
        obtain ⟨sel, hs, hon⟩ := h p np y' hnp hyp
        obtain ⟨hvtop, _⟩ := viaParent v p sel hp hs (hon p List.mem_cons_self)
        refine ⟨extend g d sel, ext sel hs, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with e | hq
        · rw [e, below sel y' hys]; exact hon y' (List.mem_cons_of_mem _ List.mem_cons_self)
        · rw [List.mem_singleton.mp hq]; exact hvtop
      · exfalso
        have := mapId_of_mem_newRowIds g d forb v hvnew
        have hs' : y'.id.step = g.current_step := by rw [he, this]; exact hd
        omega
  · -- a row node
    obtain ⟨z, hz, hEq⟩ := (mem_newRow_iff g d title forb n').mp hr
    have hzy : z = y' := by rw [← hid', hEq, rowNode_id]
    rw [hEq, rowNode_owners, hzy] at hv
    rw [hzy] at hz
    rcases (mem_rowOwners_iff g d y' v).mp hv with ⟨hu, _⟩ | he
    · obtain ⟨p, hp, np, hnp, hvp⟩ := KernelReader.mem_unionOwnersOf_inv g _ v hu
      obtain ⟨sel, hs, hon⟩ := h p np v hnp hvp
      obtain ⟨hytop, _⟩ := viaParent y' p sel hp hs (hon p List.mem_cons_self)
      refine ⟨extend g d sel, ext sel hs, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with e | hq
      · rw [e]; exact hytop
      · rw [List.mem_singleton.mp hq, below sel v (ownb p np hnp v hvp)]
        exact hon v (List.mem_cons_of_mem _ List.mem_cons_self)
    · obtain ⟨p, hp⟩ := exists_rowParent g d forb hpos hz
      obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp (rowParent_node g d hpos hp).1
      obtain ⟨sel, hs, hon⟩ := h p np p hnp (hself p np hnp)
      obtain ⟨hytop, _⟩ := viaParent y' p sel hp hs (hon p List.mem_cons_self)
      refine ⟨extend g d sel, ext sel hs, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with e | hq
      · rw [e]; exact hytop
      · rw [List.mem_singleton.mp hq, he]; exact hytop

/-- info: 'AbsSatBin.GraphPath.Model.BranchFull.pairExact_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairExact_addNode

/-- info: 'AbsSatBin.GraphPath.Model.BranchFull.fullBranch_of_pairExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullBranch_of_pairExact

end AbsSatBin.GraphPath.Model.BranchFull
