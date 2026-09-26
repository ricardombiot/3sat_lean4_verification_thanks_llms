-- lean/improves_bin/AbsSatBin/GraphPath/Model/ReqFilter.lean
import AbsSatBin.GraphPath.Model.BranchRel

/-!
# The requirement filter is a pin

In bin a node has at most one requirement (`reqOf_length_le_one`), a map node `req` at a variable step,
and `filterAll g [req]` keeps, at that step, only the path nodes whose map node is `req`, then reviews.
That is a pin on a map node. Two cases:

* **One live path node `x` for `req`** (`filterChoice_of_unique`). After the review every table holds `x`
  (it is the only entry of its step), and every surviving link has its witnesses inside, all owning `x`:
  the link was `x`-compatible before. With exactness relative to `x` before the filter, the link lies
  on a certificate through `x`, which satisfies the requirement and survives it.
* **Several path nodes for `req`** (its window remembers the previous variable). The filter is a
  *disjunctive* pin — a union again. What it needs is **`FilterChoice`**: every surviving link is
  compatible relative to one of them.

**`pairExact_filter_of_choice`**: exactness relative to every node before, and `FilterChoice`, give
pairwise exactness after. So the requirement filter turns relative exactness into pairwise exactness —
the hierarchy goes down one order through a pin, as in the reader (`CliqueTri.cliqueTri_pin`).
-/

namespace AbsSatBin.GraphPath.Model.ReqFilter

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
open AbsSatBin.GraphPath.Model.BranchRel

/-- After the filter, a live entry at the requirement's step names the required map node. -/
theorem req_id (g : GPathM) (req : NodeId) (x : PathNodeId) (hx : x ∈ (filterAll g [req]).gowners)
    (hs : x.id.step = req.step) : x.id = req := by
  have hp : Pruned (filterRequire g req) (filterAll g [req]) := pruned_review _
  obtain ⟨_, hkeep⟩ := List.mem_filter.mp (hp.gowners_sub x hx)
  simp only [hs, bne_self_eq_false, Bool.false_or] at hkeep
  exact eq_of_beq hkeep

/-- **The local condition of the filter**: every surviving link is compatible, before the filter,
relative to one path node of the required map node. -/
def FilterChoice (g : GPathM) (req : NodeId) : Prop :=
  ∀ y ny v, (filterAll g [req]).node? y = some ny → v ∈ ny.owners →
    ∃ x nx nyg nvg, x.id = req ∧ x.id.step = req.step ∧ g.node? x = some nx ∧ g.node? y = some nyg ∧
      g.node? v = some nvg ∧ x ∈ nyg.owners ∧ x ∈ nvg.owners ∧ Cx g x nyg v

/-- **Exactness relative to every node, through the filter, gives pairwise exactness.** -/
theorem pairExact_filter_of_choice (g : GPathM) (req : NodeId) (h : PairExactRelAll g)
    (hch : FilterChoice g req) : PairExact (filterAll g [req]) := by
  intro y ny v hy hv
  obtain ⟨x, nx, nyg, nvg, hxid, hxs, hnx, hnyg, hnvg, hxy, hxv, hC⟩ := hch y ny v hy hv
  obtain ⟨sel, hs, hon⟩ := h x nx hnx y nyg v nvg hnyg hnvg hxy hxv hC
  have hxo : sel x.id.step = x := hon x List.mem_cons_self
  refine ⟨sel, ChainSound_filterAll g [req] sel hs (fun r hr _ _ => ?_), fun q hq => ?_⟩
  · rw [List.mem_singleton.mp hr, ← hxs, hxo, hxid]
  · rcases List.mem_cons.mp hq with e | hq
    · rw [e]; exact hon y (List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [List.mem_singleton.mp hq]
      exact hon v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **With a single live path node for the requirement, the local condition holds.** -/
theorem filterChoice_of_unique (g : GPathM) (req : NodeId) (hnd : NodupIds g)
    (hk : Kernel (filterAll g [req]))
    (hsym : ∀ a na b nb, g.node? a = some na → g.node? b = some nb → b ∈ na.owners → a ∈ nb.owners)
    (h0 : 0 ≤ req.step) (h1 : req.step < g.current_step) (x : PathNodeId)
    (huniq : ∀ q ∈ (filterAll g [req]).gowners, q.id.step = req.step → q = x) : FilterChoice g req := by
  have hb := KernelIff.below_filterAll_self g hnd [req]
  -- every table of the filtered state holds `x`
  have own_x : ∀ q nq, (filterAll g [req]).node? q = some nq → x ∈ nq.owners ∧ x ∈ (filterAll g [req]).gowners
      ∧ x.id.step = req.step := by
    intro q nq hq
    have hv := ((isValidNode_iff _ nq).mp (hk.valid q nq hq)).1
    rw [← hb.step] at hv
    obtain ⟨e, he, hes⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv req.step (mem_intRange h0 (by omega)))
    have hes' : e.id.step = req.step := eq_of_beq hes
    have heg := hk.own q nq hq e he
    have hex : e = x := huniq e heg hes'
    rw [hex] at he heg hes'
    exact ⟨he, heg, hes'⟩
  intro y ny v hy hv
  obtain ⟨hxy, hxg, hxs⟩ := own_x y ny hy
  obtain ⟨nxh, hnxh⟩ := Option.isSome_iff_exists.mp (hk.gn x hxg)
  obtain ⟨nx, hnx, _, _, _⟩ := hb.node x nxh hnxh
  obtain ⟨nyg, hnyg, hoy, _, _⟩ := hb.node y ny hy
  obtain ⟨nv, hnv⟩ := hk.isNode_owner y ny hy v hv
  obtain ⟨nvg, hnvg, hov, _, _⟩ := hb.node v nv hnv
  refine ⟨x, nx, nyg, nvg, req_id g req x hxg hxs, hxs, hnx, hnyg, hnvg, hoy x hxy, hov x (own_x v nv hnv).1,
    nvg, nx, hnvg, hnx, hoy v hv, fun l h0' h1' => ?_⟩
  obtain ⟨r, hr, hrv, hrs⟩ := hk.pair y ny v nv hy hnv hv l h0' (by rw [← hb.step]; exact h1')
  obtain ⟨nr, hnr⟩ := hk.isNode_owner y ny hy r hr
  obtain ⟨nrg, hnrg, hor, _, _⟩ := hb.node r nr hnr
  exact ⟨r, hoy r hr, hov r hrv, hsym r nrg x nx hnrg hnx (hor x (own_x r nr hnr).1), hrs⟩

/-- info: 'AbsSatBin.GraphPath.Model.ReqFilter.pairExact_filter_of_choice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairExact_filter_of_choice

/-- info: 'AbsSatBin.GraphPath.Model.ReqFilter.filterChoice_of_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filterChoice_of_unique

end AbsSatBin.GraphPath.Model.ReqFilter
