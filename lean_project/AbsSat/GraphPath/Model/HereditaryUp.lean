-- lean_project/AbsSat/GraphPath/Model/HereditaryUp.lean
import AbsSat.GraphPath.Model.HereditaryBuild

/-!
# Hereditary pin validity through UP

`A = addNode F d`: the state `F` grown by one node `new` on the next step, which owns every global owner
and is owned by every node. This module proves that UP keeps `HPV`.

* `U1` (`drop_new`) — if `A` is valid under constraints `C`, dropping `new` from its reviewed tables
  leaves a support relation inside `F` under `C`: so `F` is valid under `C`, and every old global owner of
  the constrained `A` is a global owner of the constrained `F`.
* `U2` (`add_new`) — if `F` is valid under `C ++ [q]` for an old `q`, and `new` survives `C` in `A`, adding
  `new` back to those tables gives a support relation inside `A` under `C ++ [q]`: so `A` is valid there.
* **`hpv_addNode`** — pinning `new` changes nothing (it is the only node of its step); pinning an old `q`
  goes through `U1`, `HPV F`, and `U2`.
-/

namespace AbsSat.GraphPath.Model.HereditaryUp

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.AnchoredSurvive
open AbsSat.GraphPath.Model.AggFixpoint
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchCompat
open AbsSat.GraphPath.Model.Hereditary
open AbsSat.GraphPath.Model.HereditaryBuild

theorem node?_filterWeakAll (g : GPathM) (C : Cons) (p : PathNodeId) :
    (filterWeakAll g C).node? p = g.node? p := by
  simp only [GPathM.node?, (filterWeakAll_frame C g).1]

theorem mem_Fw {g : GPathM} {C : Cons} {p : PathNodeId} (h : Mem (Fw g C) p) : Mem g p := by
  have hpr : Pruned g (Fw g C) :=
    Pruned.trans (ReaderAggRun.keeps_filterWeakAll g C).1 (pruned_filterAllAgg _ [])
  exact mem_of_pruned hpr h

/-- A node of the constrained state keeps, among old steps, only owners and parents of the state. -/
theorem derived_Fw {g : GPathM} {C : Cons} (hnd : NodupIds g) {x : PathNodeId} {m : PNodeM}
    (hm : (Fw g C).node? x = some m) :
    ∃ n, g.node? x = some n ∧ (∀ q ∈ m.owners, q ∈ n.owners) ∧ (∀ q ∈ m.parents, q ∈ n.parents) := by
  have hpr : Pruned g (Fw g C) :=
    Pruned.trans (ReaderAggRun.keeps_filterWeakAll g C).1 (pruned_filterAllAgg _ [])
  obtain ⟨n, hn, hid, ho, hp⟩ := hpr.nodes_derived m (List.mem_of_find?_eq_some hm)
  refine ⟨n, ?_, ho, hp⟩
  rw [← node?_id_eq _ x m hm, hid]; exact node?_of_mem hnd n hn

theorem old_or_new (F : GPathM) (d : NodeId) (hd : d.step = F.current_step) (rcF : Reader.RCtx F)
    {p : PathNodeId} (h : Mem (addNode F d "") p) :
    (p ∈ newRowIds F d ∧ p.id.step = F.current_step) ∨
    (Mem F p ∧ p.id.step < F.current_step) := by
  rcases mem_addNode h with hrow | hp
  · exact Or.inl ⟨hrow, by rw [mapId_of_mem_newRowIds F d p hrow]; exact hd⟩
  · obtain ⟨m, hm⟩ := hp
    have hmem := List.mem_of_find?_eq_some hm
    refine Or.inr ⟨⟨m, hm⟩, ?_⟩
    rw [← node?_id_eq _ p m hm]; exact rcF.below m hmem

/-- **U1.** If the grown state is valid under `C`, so is `F`, and old global owners carry over. -/
theorem drop_new (F : GPathM) (d : NodeId) (hd : d.step = F.current_step)
    (rcF : Reader.RCtx F) (hsF : Sons.SMP F)
    (rcA : Reader.RCtx (addNode F d "")) (hsA : Sons.SMP (addNode F d ""))
    (hpA : Sons.PMS (addNode F d "")) (hnA : Sons.SN (addNode F d "")) (C : Cons) (hv : isValid (Fw (addNode F d "") C) = true) :
    isValid (Fw F C) = true ∧
      ∀ q ∈ (Fw (addNode F d "") C).gowners, q.id.step < F.current_step → q ∈ (Fw F C).gowners := by
  let A := addNode F d ""
  let B := Fw A C
  obtain ⟨hRB, hsB, hpB, hnB⟩ := Fw_facts A rcA hsA hpA hnA C
  have a := AdjacentOwners.adj_of_readable B hRB hv hpB hnB
  have hok : AggOk B := aggOk_reviewAgg _ hv
  have supB := sup_of_embedded B B a hok hsB (BranchLines.embedded_refl B)
  have hcsA : A.current_step = F.current_step + 1 := addNode_current F d ""
  have hcsB : B.current_step = F.current_step + 1 := by
    rw [← hcsA]; exact (Pruned.trans (ReaderAggRun.keeps_filterWeakAll A C).1 (pruned_filterAllAgg _ [])).step_eq
  -- old nodes of B are old nodes of F with contained owners and parents
  have oldTables : ∀ x mB, B.node? x = some mB → x.id.step < F.current_step → ∀ nF, F.node? x = some nF →
      (∀ v ∈ mB.owners, v.id.step < F.current_step → v ∈ nF.owners) ∧ (∀ c ∈ mB.parents, c ∈ nF.parents) := by
    intro x mB hmB hx nF hnF
    obtain ⟨nA, hnA', ho, hpa⟩ := derived_Fw rcA.nodup hmB
    have hA := addNode_node?_old F d "" x nF hnF
    rw [hnA'] at hA
    cases hA
    refine ⟨fun v hv hvs => ?_, fun c hc => ?_⟩
    · have := ho v hv
      rw [upMap_owners] at this
      rcases List.mem_append.mp this with h | h
      · exact h
      · rw [mapId_of_mem_newRowIds _ d v (gainedOwners_subset _ d _ v h), hd] at hvs
        omega
    · have := hpa c hc
      rwa [upMap_parents] at this
  let S : PathNodeId → Prop := fun p => Mem B p ∧ p.id.step < F.current_step
  let R : PathNodeId → PathNodeId → Prop := fun x v => Rel B x v ∧ x.id.step < F.current_step ∧ v.id.step < F.current_step
  have memF : ∀ p, S p → Mem F p := by
    intro p hp
    rcases old_or_new F d hd rcF (mem_Fw hp.1) with ⟨_, hs⟩ | ⟨hm, _⟩
    · exact absurd hp.2 (by omega)
    · exact hm
  have nodeF : ∀ x nF, (filterWeakAll F C).node? x = some nF → F.node? x = some nF := by
    intro x nF h; rwa [node?_filterWeakAll] at h
  have sup : Sup (filterWeakAll F C) S R := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- global owners
      intro p hp
      have hg := gowner_of_mem B a hp.1
      have hgW := (pruned_filterAllAgg (filterWeakAll A C) []).gowners_sub p hg
      obtain ⟨hgA, hcomp⟩ := (mem_filterWeakAll C A p).mp hgW
      have hgA' : p ∈ F.gowners ++ newRowIds F d := hgA
      rcases List.mem_append.mp hgA' with h | h
      · exact (mem_filterWeakAll C F p).mpr ⟨h, hcomp⟩
      · have := hp.2
        rw [mapId_of_mem_newRowIds F d p h, hd] at this
        omega
    · intro p hp
      obtain ⟨m, hm⟩ := memF p hp
      rw [node?_filterWeakAll, hm]; rfl
    · intro p hp
      rw [(filterWeakAll_frame C F).2.1]
      exact ⟨(mem_bounds B a hp.1).1, hp.2⟩
    · intro x v h
      exact ⟨⟨(supB.dom x v h.1).1, h.2.1⟩, ⟨(supB.dom x v h.1).2, h.2.2⟩⟩
    · intro x v n h hn
      obtain ⟨mB, hmB, hvm, _⟩ := h.1
      exact (oldTables x mB hmB h.2.1 n (nodeF x n hn)).1 v hvm h.2.2
    · intro x hx l hl0 hl1
      rw [(filterWeakAll_frame C F).2.1] at hl1
      obtain ⟨v, hv, hvs⟩ := supB.cov x hx.1 l hl0 (by rw [hcsB]; omega)
      exact ⟨v, ⟨hv, hx.2, by rw [hvs]; exact hl1⟩, hvs⟩
    · intro x dF hx hdF hpid v hxv
      obtain ⟨mB, hmB⟩ := hx.1
      obtain ⟨c, hc, h1, h2, h3⟩ := supB.par x mB hx.1 hmB hpid v hxv.1
      have hcs : c.id.step < F.current_step := by
        have := a.rc.shape.pbelow mB (List.mem_of_find?_eq_some hmB) c hc
        rw [node?_id_eq _ x mB hmB] at this
        omega
      exact ⟨c, (oldTables x mB hmB hx.2 dF (nodeF x dF hdF)).2 c hc, ⟨h1, hx.2, hcs⟩, ⟨h2, hcs, hx.2⟩,
        ⟨h3, hcs, hxv.2.2⟩⟩
    · intro x hx hlast v hxv
      rw [(filterWeakAll_frame C F).2.1] at hlast
      obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := supB.son x hx.1 (by rw [hcsB]; omega) v hxv.1
      have hcs : c.id.step = x.id.step + 1 := by
        have := a.rc.shape.pbelow m (List.mem_of_find?_eq_some hm) x hxm
        rw [node?_id_eq _ c m hm] at this
        omega
      have hcF : c.id.step < F.current_step := by omega
      obtain ⟨nc, hnc⟩ := memF c ⟨⟨m, hm⟩, hcF⟩
      refine ⟨c, nc, by rw [node?_filterWeakAll]; exact hnc, (oldTables c m hm hcF nc hnc).2 x hxm,
        ⟨h1, hx.2, hcF⟩, ⟨h2, hcF, hx.2⟩, ⟨h3, hcF, hxv.2.2⟩⟩
    · intro x v hxv l hl0 hl1
      rw [(filterWeakAll_frame C F).2.1] at hl1
      obtain ⟨z, h1, h2, hzs⟩ := supB.agg x v hxv.1 l hl0 (by rw [hcsB]; omega)
      exact ⟨z, ⟨h1, hxv.2.1, by rw [hzs]; exact hl1⟩, ⟨h2, hxv.2.2, by rw [hzs]; exact hl1⟩, hzs⟩
    · intro x v hxv
      exact ⟨supB.sym x v hxv.1, hxv.2.2, hxv.2.1⟩
    · intro x c dF hxc hcx hs hdF
      obtain ⟨mB, hmB, _, _⟩ := hxc.1
      exact (oldTables x mB hmB hxc.2.1 dF (nodeF x dF hdF)).2 c (supB.link x c mB hxc.1 hcx.1 hs hmB)
  have hwn := (filterWeakAll_frame C F).1
  have hsW : Sons.SMP (filterWeakAll F C) := by unfold Sons.SMP; rw [hwn]; exact hsF
  have hnW : Parents.NotRoot (filterWeakAll F C) := by unfold Parents.NotRoot; rw [hwn]; exact rcF.shape.notroot
  have hA := AOk_filterAllAgg (filterWeakAll F C) ⟨sup, hsW, hnW⟩ [] (fun r hr => absurd hr List.not_mem_nil)
  have hcsF : (Fw F C).current_step = F.current_step :=
    (Pruned.trans (ReaderAggRun.keeps_filterWeakAll F C).1 (pruned_filterAllAgg _ [])).step_eq
  refine ⟨?_, fun q hq hqs => ?_⟩
  · simp only [isValid, List.all_eq_true] at hv ⊢
    intro k hk
    rw [hcsF] at hk
    obtain ⟨hk0, hk1⟩ := PickInduction.intRange_bounds hk
    obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (hv k (mem_intRange hk0 (by rw [hcsB]; omega)))
    obtain ⟨mq, hmq, hmqid⟩ := a.rc.gn q hq
    have hqS : S q := ⟨⟨mq, by rw [← hmqid]; exact node?_of_mem a.rc.nodup mq hmq⟩,
      by rw [eq_of_beq hqs]; omega⟩
    exact List.any_eq_true.mpr ⟨q, hA.sup.gow q hqS, hqs⟩
  · obtain ⟨mq, hmq, hmqid⟩ := a.rc.gn q hq
    exact hA.sup.gow q ⟨⟨mq, by rw [← hmqid]; exact node?_of_mem a.rc.nodup mq hmq⟩, hqs⟩

/-- **The row identifiers a support keeps**: one per member of `B` sitting at the top old step.
Kept as a definition rather than a local `let` on purpose — `omega` zeta-reduces a `let` and then
case-splits the step equation inside it through `Classical`, which would put `Classical.choice` in
the axiom closure of every theorem downstream of `hpv_addNode`. -/
def SupRow (B : GPathM) (cs : Int) (d : NodeId) (z : PathNodeId) : Prop :=
  ∃ c, Mem B c ∧ c.id.step = cs - 1 ∧ z = shiftPid c d

/-- **What a kept row node is related to**: whatever one of its own surviving parents owns. This is
the window's half of the support — with a single new node the relation was "every member". -/
def SupRw (B : GPathM) (cs : Int) (d : NodeId) (z v : PathNodeId) : Prop :=
  ∃ c, Mem B c ∧ c.id.step = cs - 1 ∧ z = shiftPid c d ∧ Rel B c v

/-- **U2.** If `F` is valid under `C ++ [q]` for an old `q`, and the grown state is valid under `C`, the
grown state is valid under `C ++ [q]`.

With the window the new step is a whole **row**, so the support that carries `A` is no longer
"`B` plus one node related to everything". It is `B` **plus the surviving row**: one row node
`shiftPid c d` for each member `c` of the top old step, related downwards only through *its own*
parents (`Rw`), and two row nodes related only when they are equal. The piece that closes every
clause where a row node meets a member of the top old step is `relSame` — by `OOS` an owner at the
node's own step *is* the node — so a witness forced to that step is the parent it came from. -/
theorem add_new (F : GPathM) (d : NodeId) (hd : d.step = F.current_step)
    (rcF : Reader.RCtx F) (hsF : Sons.SMP F) (hpF : Sons.PMS F) (hnF : Sons.SN F) (_hmok : MachineOk F)
    (rcA : Reader.RCtx (addNode F d "")) (hsA : Sons.SMP (addNode F d ""))
    (C : Cons) (hvA : isValid (Fw (addNode F d "") C) = true) (q : NodeId) (hqs : q.step < F.current_step)
    (hpos : 0 < F.current_step)
    (hvF : isValid (Fw F (C ++ [pinC q])) = true) :
    isValid (Fw (addNode F d "") (C ++ [pinC q])) = true := by
  let A := addNode F d ""
  let C' := C ++ [pinC q]
  let B := Fw F C'
  obtain ⟨hRB, hsB, hpB, hnB⟩ := Fw_facts F rcF hsF hpF hnF C'
  have a := AdjacentOwners.adj_of_readable B hRB hvF hpB hnB
  have hok : AggOk B := aggOk_reviewAgg _ hvF
  have supB := sup_of_embedded B B a hok hsB (BranchLines.embedded_refl B)
  have hcsA : A.current_step = F.current_step + 1 := addNode_current F d ""
  have hcsB : B.current_step = F.current_step :=
    (Pruned.trans (ReaderAggRun.keeps_filterWeakAll F C').1 (pruned_filterAllAgg _ [])).step_eq
  have hcs0 : (0 : Int) ≤ F.current_step := by omega
  -- ------------------------------------------------------------------
  -- the members of `B`
  -- ------------------------------------------------------------------
  have oldB : ∀ p, Mem B p → Mem F p ∧ p.id.step < F.current_step := by
    intro p hp
    obtain ⟨m, hm⟩ := mem_Fw hp
    exact ⟨⟨m, hm⟩, by rw [← node?_id_eq _ p m hm]; exact rcF.below m (List.mem_of_find?_eq_some hm)⟩
  have gowB : ∀ p, Mem B p → p ∈ F.gowners ∧ ∀ e ∈ C', p.id.step = e.1 → p.id ∈ e.2 := by
    intro p hp
    have hg := gowner_of_mem B a hp
    exact (mem_filterWeakAll C' F p).mp ((pruned_filterAllAgg (filterWeakAll F C') []).gowners_sub p hg)
  have tables : ∀ x mB, B.node? x = some mB → ∀ nF, F.node? x = some nF →
      (∀ v ∈ mB.owners, v ∈ nF.owners) ∧ (∀ c ∈ mB.parents, c ∈ nF.parents) := by
    intro x mB hmB nF hnF
    obtain ⟨n, hn, ho, hpa⟩ := derived_Fw rcF.nodup hmB
    rw [hnF] at hn
    cases hn
    exact ⟨ho, hpa⟩
  have nodeOld : ∀ x nF, F.node? x = some nF → (filterWeakAll A C').node? x = some (upMap F d nF) := by
    intro x nF hnF
    rw [node?_filterWeakAll]; exact addNode_node?_old F d "" x nF hnF
  have selfRel : ∀ x, Mem B x → Rel B x x := by
    rintro x ⟨m, hm⟩
    exact ⟨m, hm, a.ctx.self x m hm, ⟨m, hm⟩⟩
  have gowAt : ∀ l, 0 ≤ l → l < F.current_step → ∃ z, Mem B z ∧ z.id.step = l := by
    intro l hl0 hl1
    simp only [isValid, List.all_eq_true] at hvF
    obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp (hvF l (mem_intRange hl0 (by rw [hcsB]; omega)))
    obtain ⟨mz, hmz, hmzid⟩ := a.rc.gn z hz
    exact ⟨z, ⟨mz, by rw [← hmzid]; exact node?_of_mem a.rc.nodup mz hmz⟩, eq_of_beq hzs⟩
  have ownerAt : ∀ x, Mem B x → ∀ l, 0 ≤ l → l < F.current_step → ∃ z, Rel B x z ∧ z.id.step = l := by
    rintro x ⟨m, hm⟩ l hl0 hl1
    obtain ⟨z, hz, hzs⟩ := owner_at B a x m hm l hl0 (by rw [hcsB]; exact hl1)
    exact ⟨z, ⟨m, hm, hz, mem_of_owner B a x m hm z hz (by omega) (by rw [hcsB]; omega)⟩, hzs⟩
  have inParentsNew : ∀ c, Mem B c → c.id.step = F.current_step - 1 → c ∈ newParents F := by
    intro c hc hs
    unfold newParents
    rw [if_pos hpos]
    obtain ⟨mc, hmc⟩ := (oldB c hc).1
    exact mem_line_of_node? F c mc hmc _ hs
  -- **an owner at the node's own step is the node** (`OOS`); the pivot of the whole construction
  have relSame : ∀ x v, Rel B x v → x.id.step = v.id.step → x = v := by
    rintro x v ⟨m, hm, hv, _⟩ hs
    have hid : m.id = x := node?_id_eq B x m hm
    have h := a.rc.oos m (List.mem_of_find?_eq_some hm) v hv (by rw [hid]; exact hs.symm)
    rw [hid] at h
    exact h.symm
  -- the whole row survives `C`: every row id carries the map id `d`
  have newAllowed : ∀ e ∈ C, F.current_step = e.1 → d ∈ e.2 := by
    intro e he hs
    simp only [isValid, List.all_eq_true] at hvA
    have hcsFwA : (Fw A C).current_step = F.current_step + 1 := by
      rw [← hcsA]; exact (Pruned.trans (ReaderAggRun.keeps_filterWeakAll A C).1 (pruned_filterAllAgg _ [])).step_eq
    obtain ⟨g, hg, hgs⟩ := List.any_eq_true.mp (hvA F.current_step (mem_intRange hcs0 (by rw [hcsFwA]; omega)))
    have hgW := (pruned_filterAllAgg (filterWeakAll A C) []).gowners_sub g hg
    obtain ⟨hgA, hgc⟩ := (mem_filterWeakAll C A g).mp hgW
    have hgA' : g ∈ F.gowners ++ newRowIds F d := hgA
    have hgd : g.id = d := by
      rcases List.mem_append.mp hgA' with h | h
      · exfalso
        obtain ⟨m, hm, hmid⟩ := rcF.gn g h
        have hb := rcF.below m hm
        rw [hmid, eq_of_beq hgs] at hb
        omega
      · exact mapId_of_mem_newRowIds F d g h
    rw [← hgd]
    exact hgc e he (by rw [eq_of_beq hgs]; exact hs)
  -- ------------------------------------------------------------------
  -- the row, and the support it builds
  -- ------------------------------------------------------------------
  let Row : PathNodeId → Prop := SupRow B F.current_step d
  let Rw : PathNodeId → PathNodeId → Prop := SupRw B F.current_step d
  let S : PathNodeId → Prop := fun p => Mem B p ∨ Row p
  let R : PathNodeId → PathNodeId → Prop := fun x v =>
    (Mem B x ∧ Mem B v ∧ Rel B x v) ∨ (Rw x v ∧ Mem B v) ∨ (Rw v x ∧ Mem B x) ∨ (Row x ∧ x = v)
  have rowStep : ∀ z, Row z → z.id.step = F.current_step := by
    rintro z ⟨c, _, _, rfl⟩; exact hd
  have rowIds : ∀ z, Row z → z ∈ newRowIds F d := by
    rintro z ⟨c, hc, hcs, rfl⟩
    exact mem_newRowIds_of_mem_newParents F d c hpos (inParentsNew c hc hcs)
  have rowNotMem : ∀ z, Row z → ¬ Mem B z := by
    intro z hz hm
    have h1 := rowStep z hz
    have h2 := (oldB z hm).2
    omega
  have rowNodeAt : ∀ z, Row z → (filterWeakAll A C').node? z = some (rowNode F d "" z) := by
    intro z hz
    rw [node?_filterWeakAll]
    exact addNode_node?_new F d "" hd rcF.below z (rowIds z hz)
  have rwRow : ∀ z v, Rw z v → Row z := by
    rintro z v ⟨c, hc, hcs, hz, _⟩; exact ⟨c, hc, hcs, hz⟩
  have rowOwn : ∀ z v, Rw z v → v ∈ rowOwners F d z := by
    rintro z v ⟨c, hc, hcs, rfl, mB, hmB, hvm, hv⟩
    obtain ⟨nF', hnF'⟩ := (oldB c hc).1
    refine (mem_rowOwners_iff F d _ v).mpr (Or.inl ⟨?_, (gowB v hv).1⟩)
    exact mem_unionOwnersOf F _ c nF' v
      (mem_rowParents_of_mem_newParents F d c (inParentsNew c hc hcs)) hnF'
      ((tables c mB hmB nF' hnF').1 v hvm)
  have gainRow : ∀ z x nF', Rw z x → F.node? x = some nF' → z ∈ gainedOwners F d nF' := by
    intro z x nF' hrw hnF'
    refine List.mem_filter.mpr ⟨rowIds z (rwRow z x hrw), ?_⟩
    rw [node?_id_eq F x nF' hnF']
    exact List.elem_eq_true_of_mem (rowOwn z x hrw)
  have rowExists : ∃ z, Row z := by
    obtain ⟨c, hc, hcs⟩ := gowAt (F.current_step - 1) (by omega) (by omega)
    exact ⟨shiftPid c d, c, hc, hcs, rfl⟩
  have sup : Sup (filterWeakAll A C') S R := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- global owners
      rintro p (hp | hp)
      · obtain ⟨hgF, hc⟩ := gowB p hp
        exact (mem_filterWeakAll C' A p).mpr ⟨List.mem_append_left _ hgF, hc⟩
      · refine (mem_filterWeakAll C' A p).mpr ⟨List.mem_append_right _ (rowIds p hp), fun e he hs => ?_⟩
        rw [mapId_of_mem_newRowIds F d p (rowIds p hp)]
        rw [rowStep p hp] at hs
        rcases List.mem_append.mp he with he | he
        · exact newAllowed e he hs
        · exfalso
          rw [List.mem_singleton.mp he] at hs
          simp only [pinC] at hs
          omega
    · -- the node exists
      rintro p (hp | hp)
      · obtain ⟨m, hm⟩ := (oldB p hp).1
        rw [nodeOld p m hm]; rfl
      · rw [rowNodeAt p hp]; rfl
    · -- the step is in range
      rintro p (hp | hp)
      · rw [(filterWeakAll_frame C' A).2.1, hcsA]
        exact ⟨(mem_bounds B a hp).1, by have := (oldB p hp).2; omega⟩
      · rw [(filterWeakAll_frame C' A).2.1, hcsA, rowStep p hp]
        exact ⟨hcs0, by omega⟩
    · -- domain
      rintro x v (⟨hx, hv, _⟩ | ⟨hrw, hv⟩ | ⟨hrw, hx⟩ | ⟨hx, rfl⟩)
      · exact ⟨Or.inl hx, Or.inl hv⟩
      · exact ⟨Or.inr (rwRow x v hrw), Or.inl hv⟩
      · exact ⟨Or.inl hx, Or.inr (rwRow v x hrw)⟩
      · exact ⟨Or.inr hx, Or.inr hx⟩
    · -- owners
      rintro x v n (⟨hx, hv, hr⟩ | ⟨hrw, hv⟩ | ⟨hrw, hx⟩ | ⟨hx, rfl⟩) hn
      · obtain ⟨mF, hmF⟩ := (oldB x hx).1
        rw [nodeOld x mF hmF] at hn
        cases hn
        rw [upMap_owners]
        obtain ⟨mB, hmB, hvm, _⟩ := hr
        exact List.mem_append_left _ ((tables x mB hmB mF hmF).1 v hvm)
      · rw [rowNodeAt x (rwRow x v hrw)] at hn
        cases hn
        rw [rowNode_owners]
        exact rowOwn x v hrw
      · obtain ⟨mF, hmF⟩ := (oldB x hx).1
        rw [nodeOld x mF hmF] at hn
        cases hn
        rw [upMap_owners]
        exact List.mem_append_right _ (gainRow v x mF hrw hmF)
      · rw [rowNodeAt x hx] at hn
        cases hn
        rw [rowNode_owners]
        exact self_mem_rowOwners F d x
    · -- cover
      intro x hx l hl0 hl1
      rw [(filterWeakAll_frame C' A).2.1, hcsA] at hl1
      by_cases hl : l = F.current_step
      · rcases hx with hx | hx
        · obtain ⟨c, hc, hcs⟩ := ownerAt x hx (F.current_step - 1) (by omega) (by omega)
          refine ⟨shiftPid c d,
            Or.inr (Or.inr (Or.inl ⟨⟨c, (supB.dom x c hc).2, hcs, rfl, supB.sym x c hc⟩, hx⟩)), ?_⟩
          rw [hl]; exact hd
        · exact ⟨x, Or.inr (Or.inr (Or.inr ⟨hx, rfl⟩)), by rw [rowStep x hx, hl]⟩
      · have hl' : l < F.current_step := by omega
        rcases hx with hx | hx
        · obtain ⟨z, hz, hzs⟩ := ownerAt x hx l hl0 hl'
          exact ⟨z, Or.inl ⟨hx, (supB.dom x z hz).2, hz⟩, hzs⟩
        · obtain ⟨c, hc, hcs, rfl⟩ := hx
          obtain ⟨z, hz, hzs⟩ := ownerAt c hc l hl0 hl'
          exact ⟨z, Or.inr (Or.inl ⟨⟨c, hc, hcs, rfl, hz⟩, (supB.dom c z hz).2⟩), hzs⟩
    · -- parents
      intro x dx hx hdx hpid v hxv
      rcases hx with hx | hx
      · -- an old member: reduce the target to a member of `B`, then use `supB.par`
        obtain ⟨mF, hmF⟩ := (oldB x hx).1
        rw [nodeOld x mF hmF] at hdx
        cases hdx
        obtain ⟨mB, hmB⟩ := id hx
        have hv0 : ∃ v0, Rel B x v0 ∧ (∀ c, Rel B c v0 → R c v) := by
          rcases hxv with ⟨_, hv, hr⟩ | ⟨hrw, _⟩ | ⟨hrw, _⟩ | ⟨hrow, _⟩
          · exact ⟨v, hr, fun c hc => Or.inl ⟨(supB.dom c v hc).1, hv, hc⟩⟩
          · exact absurd hx (rowNotMem x (rwRow x v hrw))
          · obtain ⟨c0, hc0, hc0s, hveq, hrel⟩ := hrw
            exact ⟨c0, supB.sym c0 x hrel, fun c hc =>
              Or.inr (Or.inr (Or.inl ⟨⟨c0, hc0, hc0s, hveq, supB.sym c c0 hc⟩, (supB.dom c c0 hc).1⟩))⟩
          · exact absurd hx (rowNotMem x hrow)
        obtain ⟨v0, hxv0, hcv⟩ := hv0
        obtain ⟨c, hc, h1, h2, h3⟩ := supB.par x mB hx hmB hpid v0 hxv0
        refine ⟨c, ?_, Or.inl ⟨hx, (supB.dom x c h1).2, h1⟩,
          Or.inl ⟨(supB.dom x c h1).2, hx, h2⟩, hcv c h3⟩
        rw [upMap_parents]
        exact (tables x mB hmB mF hmF).2 c hc
      · -- a row node: its own parent witness
        rw [rowNodeAt x hx] at hdx
        cases hdx
        have hwit : ∃ c, Mem B c ∧ c.id.step = F.current_step - 1 ∧ x = shiftPid c d ∧ R c v := by
          rcases hxv with ⟨hm, _, _⟩ | ⟨hrw, hv⟩ | ⟨_, hm⟩ | ⟨hrow, hxeq⟩
          · exact absurd hm (rowNotMem x hx)
          · obtain ⟨c1, hc1, hc1s, hxeq1, hrel⟩ := hrw
            exact ⟨c1, hc1, hc1s, hxeq1, Or.inl ⟨hc1, hv, hrel⟩⟩
          · exact absurd hm (rowNotMem x hx)
          · obtain ⟨c1, hc1, hc1s, hxeq1⟩ := hrow
            refine ⟨c1, hc1, hc1s, hxeq1, ?_⟩
            rw [← hxeq]
            exact Or.inr (Or.inr (Or.inl ⟨⟨c1, hc1, hc1s, hxeq1, selfRel c1 hc1⟩, hc1⟩))
        obtain ⟨c1, hc1, hc1s, hxeq1, hcv⟩ := hwit
        refine ⟨c1, ?_, ?_, ?_, hcv⟩
        · rw [rowNode_parents, hxeq1]
          exact mem_rowParents_of_mem_newParents F d c1 (inParentsNew c1 hc1 hc1s)
        · exact Or.inr (Or.inl ⟨⟨c1, hc1, hc1s, hxeq1, selfRel c1 hc1⟩, hc1⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨⟨c1, hc1, hc1s, hxeq1, selfRel c1 hc1⟩, hc1⟩))
    · -- sons
      intro x hx hlast v hxv
      rw [(filterWeakAll_frame C' A).2.1, hcsA] at hlast
      have hlast' : x.id.step ≠ F.current_step := fun h => hlast (by omega)
      have hxB : Mem B x := by
        rcases hx with hx | hx
        · exact hx
        · exact absurd (rowStep x hx) hlast'
      have hxs := (oldB x hxB).2
      by_cases htop : x.id.step = F.current_step - 1
      · -- the son is the row node `x` shifts to
        have hrowc : Row (shiftPid x d) := ⟨x, hxB, htop, rfl⟩
        refine ⟨shiftPid x d, rowNode F d "" (shiftPid x d), rowNodeAt _ hrowc, ?_, ?_, ?_, ?_⟩
        · rw [rowNode_parents]
          exact mem_rowParents_of_mem_newParents F d x (inParentsNew x hxB htop)
        · exact Or.inr (Or.inr (Or.inl ⟨⟨x, hxB, htop, rfl, selfRel x hxB⟩, hxB⟩))
        · exact Or.inr (Or.inl ⟨⟨x, hxB, htop, rfl, selfRel x hxB⟩, hxB⟩)
        · rcases hxv with ⟨_, hv, hr⟩ | ⟨hrw, _⟩ | ⟨hrw, _⟩ | ⟨hrow, _⟩
          · exact Or.inr (Or.inl ⟨⟨x, hxB, htop, rfl, hr⟩, hv⟩)
          · exact absurd hxB (rowNotMem x (rwRow x v hrw))
          · -- `v`'s witness sits at `x`'s step, so it *is* `x`: the two row nodes coincide
            obtain ⟨c1, hc1, hc1s, hveq, hrel⟩ := hrw
            have hc1x : c1 = x := relSame c1 x hrel (by omega)
            exact Or.inr (Or.inr (Or.inr ⟨hrowc, by rw [hveq, hc1x]⟩))
          · exact absurd hxB (rowNotMem x hrow)
      · -- an ordinary son inside `B`
        have hv0 : ∃ v0, Rel B x v0 ∧ (∀ c, Rel B c v0 → R c v) := by
          rcases hxv with ⟨_, hv, hr⟩ | ⟨hrw, _⟩ | ⟨hrw, _⟩ | ⟨hrow, _⟩
          · exact ⟨v, hr, fun c hc => Or.inl ⟨(supB.dom c v hc).1, hv, hc⟩⟩
          · exact absurd hxB (rowNotMem x (rwRow x v hrw))
          · obtain ⟨c1, hc1, hc1s, hveq, hrel⟩ := hrw
            exact ⟨c1, supB.sym c1 x hrel, fun c hc =>
              Or.inr (Or.inr (Or.inl ⟨⟨c1, hc1, hc1s, hveq, supB.sym c c1 hc⟩, (supB.dom c c1 hc).1⟩))⟩
          · exact absurd hxB (rowNotMem x hrow)
        obtain ⟨v0, hxv0, hcv⟩ := hv0
        obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := supB.son x hxB (by rw [hcsB]; exact htop) v0 hxv0
        have hcB : Mem B c := ⟨m, hm⟩
        obtain ⟨mF, hmF⟩ := (oldB c hcB).1
        refine ⟨c, upMap F d mF, nodeOld c mF hmF, ?_,
          Or.inl ⟨hxB, hcB, h1⟩, Or.inl ⟨hcB, hxB, h2⟩, hcv c h3⟩
        rw [upMap_parents]
        exact (tables c m hm mF hmF).2 x hxm
    · -- pairs
      intro x v hxv l hl0 hl1
      rw [(filterWeakAll_frame C' A).2.1, hcsA] at hl1
      by_cases hl : l = F.current_step
      · rcases hxv with ⟨hx, hv, hr⟩ | ⟨hrw, hv⟩ | ⟨hrw, hx⟩ | ⟨hrow, hxeq⟩
        · obtain ⟨z0, hz1, hz2, hz0s⟩ :=
            supB.agg x v hr (F.current_step - 1) (by omega) (by rw [hcsB]; omega)
          refine ⟨shiftPid z0 d, ?_, ?_, by rw [hl]; exact hd⟩
          · exact Or.inr (Or.inr (Or.inl
              ⟨⟨z0, (supB.dom x z0 hz1).2, hz0s, rfl, supB.sym x z0 hz1⟩, hx⟩))
          · exact Or.inr (Or.inr (Or.inl
              ⟨⟨z0, (supB.dom v z0 hz2).2, hz0s, rfl, supB.sym v z0 hz2⟩, hv⟩))
        · exact ⟨x, Or.inr (Or.inr (Or.inr ⟨rwRow x v hrw, rfl⟩)),
            Or.inr (Or.inr (Or.inl ⟨hrw, hv⟩)), by rw [rowStep x (rwRow x v hrw), hl]⟩
        · exact ⟨v, Or.inr (Or.inr (Or.inl ⟨hrw, hx⟩)),
            Or.inr (Or.inr (Or.inr ⟨rwRow v x hrw, rfl⟩)), by rw [rowStep v (rwRow v x hrw), hl]⟩
        · refine ⟨x, Or.inr (Or.inr (Or.inr ⟨hrow, rfl⟩)), ?_, by rw [rowStep x hrow, hl]⟩
          rw [← hxeq]
          exact Or.inr (Or.inr (Or.inr ⟨hrow, rfl⟩))
      · have hl' : l < F.current_step := by omega
        have oldTo : ∀ y z, Rel B y z → R y z := fun y z h =>
          Or.inl ⟨(supB.dom y z h).1, (supB.dom y z h).2, h⟩
        rcases hxv with ⟨hx, hv, hr⟩ | ⟨hrw, hv⟩ | ⟨hrw, hx⟩ | ⟨hrow, hxeq⟩
        · obtain ⟨z, h1, h2, hzs⟩ := supB.agg x v hr l hl0 (by rw [hcsB]; exact hl')
          exact ⟨z, oldTo x z h1, oldTo v z h2, hzs⟩
        · obtain ⟨c1, hc1, hc1s, hxeq1, hrel⟩ := hrw
          obtain ⟨z, h1, h2, hzs⟩ := supB.agg c1 v hrel l hl0 (by rw [hcsB]; exact hl')
          exact ⟨z, Or.inr (Or.inl ⟨⟨c1, hc1, hc1s, hxeq1, h1⟩, (supB.dom c1 z h1).2⟩),
            oldTo v z h2, hzs⟩
        · obtain ⟨c1, hc1, hc1s, hveq, hrel⟩ := hrw
          obtain ⟨z, h1, h2, hzs⟩ := supB.agg c1 x hrel l hl0 (by rw [hcsB]; exact hl')
          exact ⟨z, oldTo x z h2,
            Or.inr (Or.inl ⟨⟨c1, hc1, hc1s, hveq, h1⟩, (supB.dom c1 z h1).2⟩), hzs⟩
        · obtain ⟨c1, hc1, hc1s, hxeq1⟩ := hrow
          obtain ⟨z, hz, hzs⟩ := ownerAt c1 hc1 l hl0 hl'
          have hR : R x z := Or.inr (Or.inl ⟨⟨c1, hc1, hc1s, hxeq1, hz⟩, (supB.dom c1 z hz).2⟩)
          exact ⟨z, hR, by rw [← hxeq]; exact hR, hzs⟩
    · -- symmetry
      rintro x v (⟨hx, hv, hr⟩ | ⟨hrw, hv⟩ | ⟨hrw, hx⟩ | ⟨hrow, hxeq⟩)
      · exact Or.inl ⟨hv, hx, supB.sym x v hr⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hrw, hv⟩))
      · exact Or.inr (Or.inl ⟨hrw, hx⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by rw [← hxeq]; exact hrow, hxeq.symm⟩))
    · -- links
      intro x c dx hxc hcx hs hdx
      rcases hxc with ⟨hx, hc, hr⟩ | ⟨hrw, hc⟩ | ⟨hrw, hx⟩ | ⟨hrow, hxeq⟩
      · obtain ⟨mF, hmF⟩ := (oldB x hx).1
        rw [nodeOld x mF hmF] at hdx
        cases hdx
        rw [upMap_parents]
        obtain ⟨mB, hmB, _, _⟩ := id hr
        have hcxr : Rel B c x := by
          rcases hcx with ⟨_, _, h⟩ | ⟨hrw2, _⟩ | ⟨hrw2, _⟩ | ⟨hrow2, _⟩
          · exact h
          · exact absurd hc (rowNotMem c (rwRow c x hrw2))
          · exact absurd hx (rowNotMem x (rwRow x c hrw2))
          · exact absurd hc (rowNotMem c hrow2)
        exact (tables x mB hmB mF hmF).2 c (supB.link x c mB hr hcxr hs hmB)
      · -- `x` is a row node and `c` sits at the top old step: `c` is one of its parents
        have hrowx : Row x := rwRow x c hrw
        rw [rowNodeAt x hrowx] at hdx
        cases hdx
        rw [rowNode_parents]
        obtain ⟨c1, hc1, hc1s, hxeq1, hrel⟩ := hrw
        have hcs : c.id.step = F.current_step - 1 := by
          have := rowStep x hrowx; omega
        have hc1c : c1 = c := relSame c1 c hrel (by omega)
        rw [hxeq1, ← hc1c]
        exact mem_rowParents_of_mem_newParents F d c1 (inParentsNew c1 hc1 hc1s)
      · exfalso
        have h1 := rowStep c (rwRow c x hrw)
        have h2 := (oldB x hx).2
        omega
      · exfalso
        rw [hxeq] at hs
        omega
  have hwn := (filterWeakAll_frame C' A).1
  have hsW : Sons.SMP (filterWeakAll A C') := by unfold Sons.SMP; rw [hwn]; exact hsA
  have hnW : Parents.NotRoot (filterWeakAll A C') := by unfold Parents.NotRoot; rw [hwn]; exact rcA.shape.notroot
  have hAok := AOk_filterAllAgg (filterWeakAll A C') ⟨sup, hsW, hnW⟩ [] (fun r hr => absurd hr List.not_mem_nil)
  have hcsFw : (Fw A C').current_step = F.current_step + 1 := by
    rw [← hcsA]; exact (Pruned.trans (ReaderAggRun.keeps_filterWeakAll A C').1 (pruned_filterAllAgg _ [])).step_eq
  simp only [isValid, List.all_eq_true]
  intro k hk
  rw [hcsFw] at hk
  obtain ⟨hk0, hk1⟩ := PickInduction.intRange_bounds hk
  by_cases hkn : k = F.current_step
  · obtain ⟨z, hz⟩ := rowExists
    exact List.any_eq_true.mpr ⟨z, hAok.sup.gow z (Or.inr hz), beq_iff_eq.mpr (by rw [rowStep z hz, hkn])⟩
  · obtain ⟨z, hz, hzs⟩ := gowAt k hk0 (by omega)
    exact List.any_eq_true.mpr ⟨z, hAok.sup.gow z (Or.inl hz), beq_iff_eq.mpr hzs⟩

/-- info: 'AbsSat.GraphPath.Model.HereditaryUp.add_new' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms add_new

/-- **UP keeps hereditary pin validity.** -/
theorem hpv_addNode (F : GPathM) (d : NodeId) (hd : d.step = F.current_step)
    (rcF : Reader.RCtx F) (hsF : Sons.SMP F) (hpF : Sons.PMS F) (hnF : Sons.SN F) (hmok : MachineOk F)
    (rcA : Reader.RCtx (addNode F d "")) (hsA : Sons.SMP (addNode F d ""))
    (hpA : Sons.PMS (addNode F d "")) (hnA : Sons.SN (addNode F d "")) (hh : HPV F) :
    HPV (addNode F d "") := by
  intro C hv q hq
  have hqW := (pruned_filterAllAgg (filterWeakAll (addNode F d "") C) []).gowners_sub q hq
  have hqA := ((mem_filterWeakAll C _ q).mp hqW).1
  have hqA' : q ∈ F.gowners ++ newRowIds F d := hqA
  rcases List.mem_append.mp hqA' with hqF | hqn
  · obtain ⟨m, hm, hmid⟩ := rcF.gn q hqF
    have hqs : q.id.step < F.current_step := by rw [← hmid]; exact rcF.below m hm
    have hq0 : (0 : Int) ≤ q.id.step := by rw [← hmid]; exact rcF.snn m hm
    obtain ⟨hvF, hsub⟩ := drop_new F d hd rcF hsF rcA hsA hpA hnA C hv
    have h1 := hh C hvF q (hsub q hq hqs)
    exact add_new F d hd rcF hsF hpF hnF hmok rcA hsA C hv q.id hqs (by omega) h1
  · -- `q` is a row id: every row id carries the map id `d`, so the pin on it keeps the whole row
    have hqd : q.id = d := mapId_of_mem_newRowIds F d q hqn
    have hnoop := filterWeakAll_append_noop (addNode F d "") C (pinC q.id) (fun x hx hs => by
      have hxA := ((mem_filterWeakAll C _ x).mp hx).1
      have hxA' : x ∈ F.gowners ++ newRowIds F d := hxA
      rcases List.mem_append.mp hxA' with h | h
      · exfalso
        obtain ⟨m, hm, hmid⟩ := rcF.gn x h
        have hb := rcF.below m hm
        rw [hmid] at hb
        change x.id.step = q.id.step at hs
        rw [hs, hqd, hd] at hb
        omega
      · rw [mapId_of_mem_newRowIds F d x h, hqd]
        exact List.mem_singleton_self _)
    unfold Fw at hv ⊢
    rw [hnoop]
    exact hv

/-- info: 'AbsSat.GraphPath.Model.HereditaryUp.hpv_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hpv_addNode

end AbsSat.GraphPath.Model.HereditaryUp
