-- lean/improves_bin/AbsSatBin/GraphPath/Model/CertMachine.lean
import AbsSatBin.GraphPath.Model.HellyTwo

/-!
# `CertClique` along the machine: the filter, and `addNode` on old cliques

`CertClique g` (every clique with witnesses lies on a certificate) is **monotone** in the right way:
after an operation that only shrinks tables, a clique with witnesses had them before. So it can be
followed through the machine without the cut sandwich of the reader.

* **The requirement filter keeps it** when the required map node has a single live path node `x`
  (`certClique_filter_unique`): after the filter every table holds `x`, so a clique `Q` with witnesses
  gives the clique `x :: Q` with witnesses before; its certificate goes through `x`, satisfies the
  requirement, and survives.
* **`addNode` keeps it on cliques of old nodes** when no window is skipped (`certClique_addNode_old`):
  the witnesses below the new step are old, the certificate before extends by its own last node.

What is left for `CertClique` is the cliques that contain a **new** node at a merge (its table is the
union of its parents'), the join, and the review after a skipped window. See `ambfar.md` §4.2r.
-/

namespace AbsSatBin.GraphPath.Model.CertMachine

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.CertFix
open AbsSatBin.GraphPath.Model.CertDescent
open AbsSatBin.GraphPath.Model.CertInvariant
open AbsSatBin.GraphPath.Model.ReqFilter
open AbsSatBin.GraphPath.Model.BranchRel (sh)

/-- **The requirement filter keeps `CertClique`** when the required map node has a single live path
node. -/
theorem certClique_filter_unique (g : GPathM) (req : NodeId) (hnd : NodupIds g)
    (hk : Kernel (filterAll g [req])) (h0 : 0 ≤ req.step) (h1 : req.step < g.current_step)
    (x : PathNodeId) (huniq : ∀ q ∈ (filterAll g [req]).gowners, q.id.step = req.step → q = x)
    (h : CertClique g) : CertClique (filterAll g [req]) := by
  have hb := KernelIff.below_filterAll_self g hnd [req]
  have own_x : ∀ q nq, (filterAll g [req]).node? q = some nq → x ∈ nq.owners ∧
      x ∈ (filterAll g [req]).gowners ∧ x.id.step = req.step := by
    intro q nq hq
    have hv := ((isValidNode_iff _ nq).mp (hk.valid q nq hq)).1
    rw [← hb.step] at hv
    obtain ⟨e, he, hes⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv req.step (mem_intRange h0 (by omega)))
    have hes' : e.id.step = req.step := eq_of_beq hes
    have heg := hk.own q nq hq e he
    have hex : e = x := huniq e heg hes'
    rw [hex] at he heg hes'
    exact ⟨he, heg, hes'⟩
  intro Q hQ hW
  -- a node of the filtered state, seen before
  have up : ∀ q nq, (filterAll g [req]).node? q = some nq →
      ∃ n, g.node? q = some n ∧ ∀ v ∈ nq.owners, v ∈ n.owners := by
    intro q nq hq
    obtain ⟨n, hn, ho, _, _⟩ := hb.node q nq hq
    exact ⟨n, hn, ho⟩
  -- `x` is live after the filter (a table holds it); pick a node of `Q` or a witness to see it
  obtain ⟨xs, hxg, hxs⟩ : ∃ _ : Unit, x ∈ (filterAll g [req]).gowners ∧ x.id.step = req.step := by
    obtain ⟨r, nr, hnr, _, _⟩ := hW req.step h0 (by rw [← hb.step]; exact h1)
    exact ⟨(), (own_x r nr hnr).2.1, (own_x r nr hnr).2.2⟩
  obtain ⟨nxh, hnxh⟩ := Option.isSome_iff_exists.mp (hk.gn x hxg)
  obtain ⟨nx, hnx, hox⟩ := up x nxh hnxh
  have hQx : Clique g (x :: Q) := by
    intro q hq
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]
      refine ⟨nx, hnx, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact hox x (own_x x nxh hnxh).1
      · obtain ⟨ns, hns, _⟩ := hQ s hs
        exact hox s (hk.sym s ns x nxh hns hnxh (own_x s ns hns).1)
    · obtain ⟨nq, hnq, hqQ⟩ := hQ q hq
      obtain ⟨n, hn, ho⟩ := up q nq hnq
      refine ⟨n, hn, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact ho x (own_x q nq hnq).1
      · exact ho s (hqQ s hs)
  have hWx : Wit g (x :: Q) := by
    intro l hl0 hl1
    obtain ⟨r, nr, hnr, hrs, hrQ⟩ := hW l hl0 (by rw [← hb.step]; exact hl1)
    obtain ⟨n, hn, ho⟩ := up r nr hnr
    refine ⟨r, n, hn, hrs, fun s hs => ?_⟩
    rcases List.mem_cons.mp hs with e | hs
    · rw [e]; exact ho x (own_x r nr hnr).1
    · exact ho s (hrQ s hs)
  obtain ⟨sel, hs, hon⟩ := h (x :: Q) hQx hWx
  have hxo : sel x.id.step = x := hon x List.mem_cons_self
  refine ⟨sel, ChainSound_filterAll g [req] sel hs (fun r hr _ _ => ?_), fun q hq => hon q (List.mem_cons_of_mem _ hq)⟩
  rw [List.mem_singleton.mp hr, ← hxs, hxo, req_id g req x hxg hxs]

/-- **`addNode` keeps certificates for cliques of old nodes** (no window skipped): the witnesses below
the new step are old nodes, and the certificate before extends by its own last node. -/
theorem certClique_addNode_old (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (hnf : ∀ pid ∈ shiftRowIds g d, forb pid = false) (h : CertClique g)
    (Q : List PathNodeId) (hold : ∀ q ∈ Q, ∃ n, g.node? q = some n)
    (hQ : Clique (addNode g d title forb) Q) (hW : Wit (addNode g d title forb) Q) :
    CertThrough (addNode g d title forb) Q := by
  -- old nodes: the new state's node is `upMap` of the old one, whose extra owners are all new
  have old : ∀ q nq, (addNode g d title forb).node? q = some nq → ∀ n, g.node? q = some n →
      nq = upMap g d forb n := by
    intro q nq hq n hn
    rw [addNode_node?_old g d title forb q n hn] at hq; cases hq; rfl
  have back : ∀ q n, g.node? q = some n → ∀ v, v ∈ (upMap g d forb n).owners → v.id.step < g.current_step →
      v ∈ n.owners := by
    intro q n hn v hv hvs
    rw [upMap_owners] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hv
    · exfalso
      have := mapId_of_mem_newRowIds g d forb v (List.mem_filter.mp hv).1
      have : v.id.step = g.current_step := by rw [this]; exact hd
      omega
  have qstep : ∀ q ∈ Q, q.id.step < g.current_step := by
    intro q hq
    obtain ⟨n, hn⟩ := hold q hq
    have := hbelow n (List.mem_of_find?_eq_some hn); rw [node?_id_eq g q n hn] at this; exact this
  have hQg : Clique g Q := by
    intro q hq
    obtain ⟨n, hn⟩ := hold q hq
    obtain ⟨nq, hnq, hqQ⟩ := hQ q hq
    rw [old q nq hnq n hn] at hqQ
    exact ⟨n, hn, fun s hs => back q n hn s (hqQ s hs) (qstep s hs)⟩
  have hWg : Wit g Q := by
    intro l hl0 hl1
    obtain ⟨r, nr, hnr, hrs, hrQ⟩ := hW l hl0 (by rw [addNode_current]; omega)
    obtain ⟨n, hn, hEq, _⟩ : ∃ n, g.node? r = some n ∧ nr = upMap g d forb n ∧ True := by
      obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title forb hd r nr hnr (by rw [hrs]; exact hl1)
      exact ⟨n, hn, hEq, trivial⟩
    rw [hEq] at hrQ
    exact ⟨r, n, hn, hrs, fun s hs => back r n hn s (hrQ s hs) (qstep s hs)⟩
  obtain ⟨sel, hs, hon⟩ := h Q hQg hWg
  refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hs
    (hnf _ (extendPid_mem_shiftRowIds g d sel hs.chain.1)), fun q hq => ?_⟩
  rw [extend_below g d sel q.id.step (qstep q hq)]; exact hon q hq

/-- **`addNode` without merges keeps `CertClique`** (no window skipped). A clique with a new node `z`:
the witnesses that own `z` own its single parent `p`, so `p` with the old members is a clique with
witnesses before, and its certificate extends through `z`. -/
theorem certClique_addNode_single (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hmok : MachineOk g) (hnd : NodupIds g)
    (hownb : SelfOwn.OwnBelow g) (hself : ∀ p np, g.node? p = some np → p ∈ np.owners)
    (hsym : ∀ a na b nb, g.node? a = some na → g.node? b = some nb → b ∈ na.owners → a ∈ nb.owners)
    (hnf : ∀ pid ∈ shiftRowIds g d, forb pid = false)
    (hsingle : ∀ z ∈ newRowIds g d forb, ∀ q ∈ rowParents g d z, ∀ q' ∈ rowParents g d z, q = q')
    (h : CertClique g) : CertClique (addNode g d title forb) := by
  intro Q hQ hW
  have back : ∀ q n, g.node? q = some n → ∀ v, v ∈ (upMap g d forb n).owners → v.id.step < g.current_step →
      v ∈ n.owners := by
    intro q n hn v hv hvs
    rw [upMap_owners] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hv
    · exfalso
      have := mapId_of_mem_newRowIds g d forb v (List.mem_filter.mp hv).1
      have : v.id.step = g.current_step := by rw [this]; exact hd
      omega
  cases hz : Q.any (fun q => q.id.step == g.current_step) with
  | false =>
    -- only old nodes
    have hold : ∀ q ∈ Q, ∃ n, g.node? q = some n := by
      intro q hq
      obtain ⟨nq, hnq, _⟩ := hQ q hq
      have hqs : q.id.step < g.current_step := by
        rcases BranchRel.node_cases g d title forb hd hbelow hnd q nq hnq with ⟨_, _, _, hs⟩ | ⟨_, _, hs⟩
        · exact hs
        · exfalso
          have := List.any_eq_false.mp hz q hq
          exact this (beq_iff_eq.mpr hs)
      obtain ⟨n, hn, _⟩ := addNode_node?_below g d title forb hd q nq hnq hqs
      exact ⟨n, hn⟩
    exact certClique_addNode_old g d title forb hd hbelow hmok hnf h Q hold hQ hW
  | true =>
    obtain ⟨z, hzQ, hzs'⟩ := List.any_eq_true.mp hz
    have hzs : z.id.step = g.current_step := eq_of_beq hzs'
    obtain ⟨nz, hnz, hzQo⟩ := hQ z hzQ
    have hznew : z ∈ newRowIds g d forb ∧ nz = rowNode g d title z := by
      rcases BranchRel.node_cases g d title forb hd hbelow hnd z nz hnz with ⟨_, _, _, hs⟩ | ⟨hn, hEq, _⟩
      · omega
      · exact ⟨hn, hEq⟩
    have hp := BranchRel.sh_new g d forb hpos z hznew.1 hzs
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp (rowParent_node g d hpos hp).1
    -- an entry of `z` below the new step is in the table of its parent
    have inp : ∀ v, v ∈ nz.owners → v.id.step < g.current_step → v ∈ np.owners := by
      intro v hv hvs
      rw [hznew.2, rowNode_owners] at hv
      rcases (mem_rowOwners_iff g d z v).mp hv with ⟨hu, _⟩ | he
      · obtain ⟨p', hp', np', hnp', hvp'⟩ := KernelReader.mem_unionOwnersOf_inv g _ v hu
        rw [hsingle z hznew.1 p' hp' _ hp, hnp] at hnp'; cases hnp'
        exact hvp'
      · exfalso; rw [he] at hvs; omega
    -- a member of `Q` at the new step is `z`
    have atTop : ∀ q ∈ Q, q.id.step = g.current_step → q = z := by
      intro q hq hqs
      have hqz := hzQo q hq
      rw [hznew.2, rowNode_owners] at hqz
      rcases (mem_rowOwners_iff g d z q).mp hqz with ⟨hu, _⟩ | he
      · exfalso
        obtain ⟨_, _, np', hnp', hqp'⟩ := KernelReader.mem_unionOwnersOf_inv g _ q hu
        have := hownb np' (List.mem_of_find?_eq_some hnp') q hqp'; omega
      · exact he
    -- an old member, seen before
    have oldNode : ∀ q ∈ Q, q.id.step < g.current_step → ∃ n nq, g.node? q = some n ∧
        (addNode g d title forb).node? q = some nq ∧ nq = upMap g d forb n := by
      intro q hq hqs
      obtain ⟨nq, hnq, _⟩ := hQ q hq
      obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title forb hd q nq hnq hqs
      exact ⟨n, nq, hn, hnq, hEq⟩
    let sp := sh g d z
    let Qg := sp :: Q.filter (fun q => decide (q.id.step < g.current_step))
    have memQg : ∀ q, q ∈ Q.filter (fun q => decide (q.id.step < g.current_step)) ↔
        q ∈ Q ∧ q.id.step < g.current_step := by
      intro q; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
    have hQg : Clique g Qg := by
      intro q hq
      rcases List.mem_cons.mp hq with e | hq
      · rw [e]
        refine ⟨np, hnp, fun s hs => ?_⟩
        rcases List.mem_cons.mp hs with e' | hs
        · rw [e']; exact hself _ np hnp
        · obtain ⟨hsQ, hss⟩ := (memQg s).mp hs
          exact inp s (hzQo s hsQ) hss
      · obtain ⟨hqQ, hqs⟩ := (memQg q).mp hq
        obtain ⟨n, nq, hn, hnq, hEq⟩ := oldNode q hqQ hqs
        obtain ⟨nq', hnq', hqQo⟩ := hQ q hqQ
        rw [hnq] at hnq'; cases hnq'
        rw [hEq] at hqQo
        refine ⟨n, hn, fun s hs => ?_⟩
        rcases List.mem_cons.mp hs with e' | hs
        · rw [e']; exact hsym _ np q n hnp hn (inp q (hzQo q hqQ) hqs)
        · obtain ⟨hsQ, hss⟩ := (memQg s).mp hs
          exact back q n hn s (hqQo s hsQ) hss
    have hWg : Wit g Qg := by
      intro l hl0 hl1
      obtain ⟨r, nr, hnr, hrs, hrQ⟩ := hW l hl0 (by rw [addNode_current]; omega)
      obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title forb hd r nr hnr (by rw [hrs]; exact hl1)
      rw [hEq] at hrQ
      refine ⟨r, n, hn, hrs, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e | hs
      · -- `r` owns `z`, so it lies in the table of `z`'s parent
        rw [e]
        have hzr := hrQ z hzQ
        rw [upMap_owners] at hzr
        rcases List.mem_append.mp hzr with hzr | hzr
        · exfalso; have := hownb n (List.mem_of_find?_eq_some hn) z hzr; omega
        · have hc := List.mem_of_elem_eq_true (List.mem_filter.mp hzr).2
          rw [node?_id_eq g r n hn] at hc
          rcases (mem_rowOwners_iff g d z r).mp hc with ⟨hu, _⟩ | he
          · obtain ⟨p', hp', np', hnp', hrp'⟩ := KernelReader.mem_unionOwnersOf_inv g _ r hu
            rw [hsingle z hznew.1 p' hp' _ hp, hnp] at hnp'; cases hnp'
            exact hsym _ np r n hnp hn hrp'
          · exfalso; rw [he] at hrs; omega
      · obtain ⟨hsQ, hss⟩ := (memQg s).mp hs
        exact back r n hn s (hrQ s hsQ) hss
    obtain ⟨sel, hs, hon⟩ := h Qg hQg hWg
    refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hs
      (hnf _ (extendPid_mem_shiftRowIds g d sel hs.chain.1)), fun q hq => ?_⟩
    rcases Int.lt_or_le q.id.step g.current_step with hqs | hqs
    · rw [extend_below g d sel q.id.step hqs]
      exact hon q (List.mem_cons_of_mem _ ((memQg q).mpr ⟨hq, hqs⟩))
    · have hqs' : q.id.step = g.current_step := by
        obtain ⟨nq, hnq, _⟩ := hQ q hq
        rcases BranchRel.node_cases g d title forb hd hbelow hnd q nq hnq with ⟨_, _, _, hs⟩ | ⟨_, _, hs⟩
        · omega
        · exact hs
      rw [atTop q hq hqs']
      exact BranchRel.extend_shadow g d forb hpos z sp (Or.inr ⟨hznew.1, hzs, hp⟩) sel (hon sp List.mem_cons_self)

-- ============================================================
-- A skipped window: the clause
-- ============================================================

/-- **The local condition of a skipped window**: a clique of old nodes with witnesses after the row
lies on a certificate before whose extension is not prohibited. In bin, at the third literal step of a
clause with value `0`, it asks for a certificate through the clique that satisfies the clause. -/
def SkipChoice (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : Prop :=
  ∀ Q, (∀ q ∈ Q, ∃ n, g.node? q = some n) → Clique (addNode g d title forb) Q →
    Wit (addNode g d title forb) Q →
    ∃ sel, ChainSound g sel ∧ (∀ q ∈ Q, sel q.id.step = q) ∧ forb (extendPid g d sel) = false

/-- **With the local condition, a row with a skipped window keeps certificates for old cliques.** -/
theorem certThrough_addNode_skip (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (hch : SkipChoice g d title forb) (Q : List PathNodeId)
    (hold : ∀ q ∈ Q, ∃ n, g.node? q = some n) (hQ : Clique (addNode g d title forb) Q)
    (hW : Wit (addNode g d title forb) Q) : CertThrough (addNode g d title forb) Q := by
  obtain ⟨sel, hs, hon, hf⟩ := hch Q hold hQ hW
  have qstep : ∀ q ∈ Q, q.id.step < g.current_step := by
    intro q hq
    obtain ⟨n, hn⟩ := hold q hq
    have := hbelow n (List.mem_of_find?_eq_some hn); rw [node?_id_eq g q n hn] at this; exact this
  refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hs hf, fun q hq => ?_⟩
  rw [extend_below g d sel q.id.step (qstep q hq)]; exact hon q hq

/-- **What the local condition asks, in the old state**: a clique with witnesses through a parent of an
allowed row node. The certificate through it ends at that parent, so its extension is that row node. -/
theorem skipChoice_of_parent (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hpos : 0 < g.current_step) (h : CertClique g)
    (hpar : ∀ Q, (∀ q ∈ Q, ∃ n, g.node? q = some n) → Clique (addNode g d title forb) Q →
      Wit (addNode g d title forb) Q →
      ∃ z ∈ newRowIds g d forb, ∃ p ∈ rowParents g d z, Clique g (p :: Q) ∧ Wit g (p :: Q)) :
    SkipChoice g d title forb := by
  intro Q hold hQ hW
  obtain ⟨z, hz, p, hp, hQp, hWp⟩ := hpar Q hold hQ hW
  obtain ⟨sel, hs, hon⟩ := h (p :: Q) hQp hWp
  have hext : extendPid g d sel = z := by
    have hps := (rowParent_node g d hpos hp).2
    have hz' : shiftPid p d = z := eq_of_beq (List.mem_filter.mp hp).2
    unfold extendPid; rw [if_pos hpos]
    have : sel (g.current_step - 1) = p := by rw [← hps]; exact hon p List.mem_cons_self
    rw [this, hz']
  exact ⟨sel, hs, fun q hq => hon q (List.mem_cons_of_mem _ hq), by rw [hext]; exact not_forb_of_mem_newRowIds g d forb z hz⟩

/-- info: 'AbsSatBin.GraphPath.Model.CertMachine.certClique_filter_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certClique_filter_unique

/-- info: 'AbsSatBin.GraphPath.Model.CertMachine.certClique_addNode_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certClique_addNode_old

/-- info: 'AbsSatBin.GraphPath.Model.CertMachine.certClique_addNode_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certClique_addNode_single

/-- info: 'AbsSatBin.GraphPath.Model.CertMachine.skipChoice_of_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms skipChoice_of_parent

end AbsSatBin.GraphPath.Model.CertMachine
