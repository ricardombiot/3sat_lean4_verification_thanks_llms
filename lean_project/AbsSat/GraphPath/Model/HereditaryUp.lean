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
/-- **U2.** If `F` is valid under `C ++ [q]` for an old `q`, and the grown state is valid under `C`, the
grown state is valid under `C ++ [q]`. -/
theorem add_new (F : GPathM) (d : NodeId) (hd : d.step = F.current_step)
    (rcF : Reader.RCtx F) (hsF : Sons.SMP F) (hpF : Sons.PMS F) (hnF : Sons.SN F) (hmok : MachineOk F)
    (rcA : Reader.RCtx (addNode F d "")) (hsA : Sons.SMP (addNode F d ""))
    (C : Cons) (hvA : isValid (Fw (addNode F d "") C) = true) (q : NodeId) (hqs : q.step < F.current_step)
    (hvF : isValid (Fw F (C ++ [pinC q])) = true) :
    isValid (Fw (addNode F d "") (C ++ [pinC q])) = true := by
  let A := addNode F d ""
  let C' := C ++ [pinC q]
  let B := Fw F C'
  let new := newPid F d
  obtain ⟨hRB, hsB, hpB, hnB⟩ := Fw_facts F rcF hsF hpF hnF C'
  have a := AdjacentOwners.adj_of_readable B hRB hvF hpB hnB
  have hok : AggOk B := aggOk_reviewAgg _ hvF
  have supB := sup_of_embedded B B a hok hsB (BranchLines.embedded_refl B)
  have hcsA : A.current_step = F.current_step + 1 := addNode_current F d ""
  have hcsB : B.current_step = F.current_step :=
    (Pruned.trans (ReaderAggRun.keeps_filterWeakAll F C').1 (pruned_filterAllAgg _ [])).step_eq
  have hnewstep : new.id.step = F.current_step := hd
  have hcs0 : 0 ≤ F.current_step := hmok.1
  -- facts about the members of B
  have oldB : ∀ p, Mem B p → Mem F p ∧ p.id.step < F.current_step := by
    intro p hp
    have hmF := mem_Fw hp
    obtain ⟨m, hm⟩ := hmF
    exact ⟨⟨m, hm⟩, by rw [← node?_id_eq _ p m hm]; exact rcF.below m (List.mem_of_find?_eq_some hm)⟩
  have neNew : ∀ p, Mem B p → p ≠ new := by
    intro p hp he
    have := (oldB p hp).2
    rw [he, hnewstep] at this
    omega
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
  have nodeNew : (filterWeakAll A C').node? new = some (addOwner new (upNode F d "")) := by
    rw [node?_filterWeakAll]; exact addNode_node?_new F d "" hd rcF.below
  -- the new node survives `C`
  have newAllowed : ∀ e ∈ C, new.id.step = e.1 → new.id ∈ e.2 := by
    intro e he hs
    simp only [isValid, List.all_eq_true] at hvA
    have hcsFwA : (Fw A C).current_step = F.current_step + 1 := by
      rw [← hcsA]; exact (Pruned.trans (ReaderAggRun.keeps_filterWeakAll A C).1 (pruned_filterAllAgg _ [])).step_eq
    obtain ⟨g, hg, hgs⟩ := List.any_eq_true.mp (hvA F.current_step (mem_intRange hcs0 (by rw [hcsFwA]; omega)))
    have hgW := (pruned_filterAllAgg (filterWeakAll A C) []).gowners_sub g hg
    obtain ⟨hgA, hgc⟩ := (mem_filterWeakAll C A g).mp hgW
    have hgA' : g ∈ F.gowners ++ [new] := hgA
    have hgnew : g = new := by
      rcases List.mem_append.mp hgA' with h | h
      · obtain ⟨m, hm, hmid⟩ := rcF.gn g h
        have := rcF.below m hm
        rw [hmid, eq_of_beq hgs] at this
        omega
      · exact List.mem_singleton.mp h
    rw [← hgnew]
    exact hgc e he (by rw [hgnew]; exact hs)
  have hcspos : ∀ c, Mem B c → c.id.step = F.current_step - 1 → 0 < F.current_step := by
    intro c hc hs
    have := (mem_bounds B a hc).1
    omega
  have inParentsNew : ∀ c, Mem B c → c.id.step = F.current_step - 1 → c ∈ newParents F := by
    intro c hc hs
    unfold newParents
    rw [if_pos (hcspos c hc hs)]
    obtain ⟨mc, hmc⟩ := (oldB c hc).1
    exact mem_line_of_node? F c mc hmc _ hs
  let S : PathNodeId → Prop := fun p => Mem B p ∨ p = new
  let R : PathNodeId → PathNodeId → Prop := fun x v =>
    S x ∧ S v ∧ (x = new ∨ (Mem B x ∧ (Rel B x v ∨ v = new)))
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
  have sup : Sup (filterWeakAll A C') S R := by
    refine ⟨?_, ?_, ?_, fun x v h => ⟨h.1, h.2.1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- global owners
      rintro p (hp | rfl)
      · obtain ⟨hgF, hc⟩ := gowB p hp
        exact (mem_filterWeakAll C' A p).mpr ⟨List.mem_append_left _ hgF, hc⟩
      · refine (mem_filterWeakAll C' A new).mpr ⟨List.mem_append_right _ List.mem_cons_self, fun e he hs => ?_⟩
        rcases List.mem_append.mp he with he | he
        · exact newAllowed e he hs
        · rw [List.mem_singleton.mp he] at hs
          simp only [pinC] at hs
          omega
    · rintro p (hp | rfl)
      · obtain ⟨m, hm⟩ := (oldB p hp).1
        rw [nodeOld p m hm]; rfl
      · rw [nodeNew]; rfl
    · rintro p (hp | rfl)
      · rw [(filterWeakAll_frame C' A).2.1, hcsA]
        exact ⟨(mem_bounds B a hp).1, by have := (oldB p hp).2; omega⟩
      · rw [(filterWeakAll_frame C' A).2.1, hcsA, hnewstep]
        exact ⟨hcs0, by omega⟩
    · -- owners
      rintro x v n ⟨_, hSv, hr⟩ hn
      rcases hr with rfl | ⟨hx, hr⟩
      · rw [nodeNew] at hn
        cases hn
        change v ∈ F.gowners ++ [new]
        rcases hSv with hv | rfl
        · exact List.mem_append_left _ (gowB v hv).1
        · exact List.mem_append_right _ List.mem_cons_self
      · obtain ⟨mF, hmF⟩ := (oldB x hx).1
        rw [nodeOld x mF hmF] at hn
        cases hn
        rw [upMap_owners]
        rcases hr with ⟨mB, hmB, hvm, _⟩ | rfl
        · exact List.mem_append_left _ ((tables x mB hmB mF hmF).1 v hvm)
        · exact List.mem_append_right _ List.mem_cons_self
    · -- cover
      intro x hx l hl0 hl1
      rw [(filterWeakAll_frame C' A).2.1, hcsA] at hl1
      by_cases hl : l = F.current_step
      · refine ⟨new, ⟨hx, Or.inr rfl, ?_⟩, by rw [hnewstep, hl]⟩
        rcases hx with hx | rfl
        · exact Or.inr ⟨hx, Or.inr rfl⟩
        · exact Or.inl rfl
      · rcases hx with hx | rfl
        · obtain ⟨z, hz, hzs⟩ := ownerAt x hx l hl0 (by omega)
          exact ⟨z, ⟨Or.inl hx, Or.inl (supB.dom x z hz).2, Or.inr ⟨hx, Or.inl hz⟩⟩, hzs⟩
        · obtain ⟨z, hz, hzs⟩ := gowAt l hl0 (by omega)
          exact ⟨z, ⟨Or.inr rfl, Or.inl hz, Or.inl rfl⟩, hzs⟩
    · -- parents
      intro x dA hx hdA hpid v hxv
      rcases hx with hx | rfl
      · obtain ⟨mF, hmF⟩ := (oldB x hx).1
        rw [nodeOld x mF hmF] at hdA
        cases hdA
        obtain ⟨mB, hmB⟩ := hx
        have hv0 : ∃ v0, Rel B x v0 ∧ (∀ c, Rel B c v0 → R c v) := by
          rcases hxv.2.2 with he | ⟨_, hr | rfl⟩
          · exact absurd he (neNew x ⟨mB, hmB⟩)
          · exact ⟨v, hr, fun c hc => ⟨Or.inl (supB.dom c v hc).1, hxv.2.1, Or.inr ⟨(supB.dom c v hc).1, Or.inl hc⟩⟩⟩
          · exact ⟨x, selfRel x ⟨mB, hmB⟩, fun c hc => ⟨Or.inl (supB.dom c x hc).1, Or.inr rfl,
              Or.inr ⟨(supB.dom c x hc).1, Or.inr rfl⟩⟩⟩
        obtain ⟨v0, hxv0, hcv⟩ := hv0
        obtain ⟨c, hc, h1, h2, h3⟩ := supB.par x mB ⟨mB, hmB⟩ hmB hpid v0 hxv0
        refine ⟨c, ?_, ⟨Or.inl ⟨mB, hmB⟩, Or.inl (supB.dom x c h1).2, Or.inr ⟨⟨mB, hmB⟩, Or.inl h1⟩⟩,
          ⟨Or.inl (supB.dom x c h1).2, Or.inl ⟨mB, hmB⟩, Or.inr ⟨(supB.dom x c h1).2, Or.inl h2⟩⟩, hcv c h3⟩
        rw [upMap_parents]
        exact (tables x mB hmB mF hmF).2 c hc
      · rw [nodeNew] at hdA
        cases hdA
        change ∃ c ∈ newParents F, R new c ∧ R c new ∧ R c v
        rcases hxv.2.1 with hv | rfl
        · have hvb := mem_bounds B a hv
          have hvs : 0 ≤ F.current_step - 1 := by omega
          obtain ⟨c, hc, hcs⟩ := ownerAt v hv (F.current_step - 1) hvs (by omega)
          have hcm := (supB.dom v c hc).2
          obtain ⟨mv, hmv, hcmv, _⟩ := hc
          obtain ⟨mc, hmc⟩ := hcm
          obtain ⟨hc0, hc1⟩ := mem_bounds B a ⟨mc, hmc⟩
          have hvc : v ∈ mc.owners := ownSym_of_aggOk B hok v c mv mc hmv hmc hvb.1 hvb.2 hc0 hc1 hcmv
            (a.ctx.nodeval v mv hmv) (a.ctx.nodeval c mc hmc)
          exact ⟨c, inParentsNew c ⟨mc, hmc⟩ hcs, ⟨Or.inr rfl, Or.inl ⟨mc, hmc⟩, Or.inl rfl⟩,
            ⟨Or.inl ⟨mc, hmc⟩, Or.inr rfl, Or.inr ⟨⟨mc, hmc⟩, Or.inr rfl⟩⟩,
            ⟨Or.inl ⟨mc, hmc⟩, Or.inl hv, Or.inr ⟨⟨mc, hmc⟩, Or.inl ⟨mc, hmc, hvc, hv⟩⟩⟩⟩
        · have hpos : 0 < F.current_step := by
            rcases Int.lt_or_eq_of_le hcs0 with h | h
            · exact h
            · exfalso
              apply hpid
              change F.map_parent = none
              exact hmok.2.1 h.symm
          obtain ⟨c, hc, hcs⟩ := gowAt (F.current_step - 1) (by omega) (by omega)
          exact ⟨c, inParentsNew c hc hcs, ⟨Or.inr rfl, Or.inl hc, Or.inl rfl⟩,
            ⟨Or.inl hc, Or.inr rfl, Or.inr ⟨hc, Or.inr rfl⟩⟩, ⟨Or.inl hc, Or.inr rfl, Or.inr ⟨hc, Or.inr rfl⟩⟩⟩
    · -- sons
      intro x hx hlast v hxv
      rw [(filterWeakAll_frame C' A).2.1, hcsA] at hlast
      rcases hx with hx | rfl
      · have hxs := (oldB x hx).2
        by_cases htop : x.id.step = F.current_step - 1
        · have hxp : x ∈ newParents F := inParentsNew x hx htop
          refine ⟨new, addOwner new (upNode F d ""), nodeNew, hxp, ⟨Or.inl hx, Or.inr rfl, Or.inr ⟨hx, Or.inr rfl⟩⟩,
            ⟨Or.inr rfl, Or.inl hx, Or.inl rfl⟩, ⟨Or.inr rfl, hxv.2.1, Or.inl rfl⟩⟩
        · have hv0 : ∃ v0, Rel B x v0 ∧ (∀ c, Rel B c v0 → R c v) := by
            rcases hxv.2.2 with he | ⟨_, hr | rfl⟩
            · exact absurd he (neNew x hx)
            · exact ⟨v, hr, fun c hc => ⟨Or.inl (supB.dom c v hc).1, hxv.2.1, Or.inr ⟨(supB.dom c v hc).1, Or.inl hc⟩⟩⟩
            · exact ⟨x, selfRel x hx, fun c hc => ⟨Or.inl (supB.dom c x hc).1, Or.inr rfl,
                Or.inr ⟨(supB.dom c x hc).1, Or.inr rfl⟩⟩⟩
          obtain ⟨v0, hxv0, hcv⟩ := hv0
          obtain ⟨c, m, hm, hxm, h1, h2, h3⟩ := supB.son x hx (by rw [hcsB]; exact htop) v0 hxv0
          have hcB : Mem B c := ⟨m, hm⟩
          obtain ⟨mF, hmF⟩ := (oldB c hcB).1
          refine ⟨c, upMap F d mF, nodeOld c mF hmF, ?_, ⟨Or.inl hx, Or.inl hcB, Or.inr ⟨hx, Or.inl h1⟩⟩,
            ⟨Or.inl hcB, Or.inl hx, Or.inr ⟨hcB, Or.inl h2⟩⟩, hcv c h3⟩
          rw [upMap_parents]
          exact (tables c m hm mF hmF).2 x hxm
      · exfalso; exact hlast (by rw [hnewstep]; omega)
    · -- pairs
      intro x v hxv l hl0 hl1
      rw [(filterWeakAll_frame C' A).2.1, hcsA] at hl1
      have toNew : ∀ y, S y → R y new := fun y hy => by
        rcases hy with hy | rfl
        · exact ⟨Or.inl hy, Or.inr rfl, Or.inr ⟨hy, Or.inr rfl⟩⟩
        · exact ⟨Or.inr rfl, Or.inr rfl, Or.inl rfl⟩
      by_cases hl : l = F.current_step
      · exact ⟨new, toNew x hxv.1, toNew v hxv.2.1, by rw [hnewstep, hl]⟩
      have hl' : l < F.current_step := by omega
      have newTo : ∀ z, Mem B z → R new z := fun z hz => ⟨Or.inr rfl, Or.inl hz, Or.inl rfl⟩
      have oldTo : ∀ y z, Rel B y z → R y z := fun y z h =>
        ⟨Or.inl (supB.dom y z h).1, Or.inl (supB.dom y z h).2, Or.inr ⟨(supB.dom y z h).1, Or.inl h⟩⟩
      rcases hxv.2.2 with rfl | ⟨hx, hr | rfl⟩
      · rcases hxv.2.1 with hv | rfl
        · obtain ⟨z, hz, hzs⟩ := ownerAt v hv l hl0 hl'
          exact ⟨z, newTo z (supB.dom v z hz).2, oldTo v z hz, hzs⟩
        · obtain ⟨z, hz, hzs⟩ := gowAt l hl0 hl'
          exact ⟨z, newTo z hz, newTo z hz, hzs⟩
      · obtain ⟨z, h1, h2, hzs⟩ := supB.agg x v hr l hl0 (by rw [hcsB]; exact hl')
        exact ⟨z, oldTo x z h1, oldTo v z h2, hzs⟩
      · obtain ⟨z, hz, hzs⟩ := ownerAt x hx l hl0 hl'
        exact ⟨z, oldTo x z hz, newTo z (supB.dom x z hz).2, hzs⟩
    · -- symmetry
      rintro x v ⟨hSx, hSv, hr⟩
      refine ⟨hSv, hSx, ?_⟩
      rcases hr with hx | ⟨hx, hr | hv⟩
      · rcases hSv with hv | hv
        · exact Or.inr ⟨hv, Or.inr hx⟩
        · exact Or.inl hv
      · have h' := supB.sym x v hr
        exact Or.inr ⟨(supB.dom v x h').1, Or.inl h'⟩
      · exact Or.inl hv
    · -- links
      rintro x c dA ⟨_, hSc, hxc⟩ ⟨_, _, hcx⟩ hs hdA
      rcases hxc with hxn | ⟨hx, hr | hcn⟩
      · rw [hxn, nodeNew] at hdA
        cases hdA
        change c ∈ newParents F
        rw [hxn, hnewstep] at hs
        rcases hSc with hc | hcn
        · exact inParentsNew c hc (by omega)
        · rw [hcn, hnewstep] at hs; omega
      · obtain ⟨mF, hmF⟩ := (oldB x hx).1
        rw [nodeOld x mF hmF] at hdA
        cases hdA
        rw [upMap_parents]
        have hc := (supB.dom x c hr).2
        rcases hcx with he | ⟨_, hr' | he⟩
        · exact absurd he (neNew c hc)
        · obtain ⟨mB, hmB, _, _⟩ := id hr
          exact (tables x mB hmB mF hmF).2 c (supB.link x c mB hr hr' hs hmB)
        · have := (oldB x hx).2
          rw [he, hnewstep] at this
          omega
      · have := (oldB x hx).2
        rw [hcn, hnewstep] at hs
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
  · exact List.any_eq_true.mpr ⟨new, hAok.sup.gow new (Or.inr rfl), beq_iff_eq.mpr (by rw [hnewstep, hkn])⟩
  · obtain ⟨z, hz, hzs⟩ := gowAt k hk0 (by omega)
    exact List.any_eq_true.mpr ⟨z, hAok.sup.gow z (Or.inl hz), beq_iff_eq.mpr hzs⟩

/-- **UP keeps hereditary pin validity.** -/
theorem hpv_addNode (F : GPathM) (d : NodeId) (hd : d.step = F.current_step)
    (rcF : Reader.RCtx F) (hsF : Sons.SMP F) (hpF : Sons.PMS F) (hnF : Sons.SN F) (hmok : MachineOk F)
    (rcA : Reader.RCtx (addNode F d "")) (hsA : Sons.SMP (addNode F d ""))
    (hpA : Sons.PMS (addNode F d "")) (hnA : Sons.SN (addNode F d "")) (hh : HPV F) :
    HPV (addNode F d "") := by
  intro C hv q hq
  have hqW := (pruned_filterAllAgg (filterWeakAll (addNode F d "") C) []).gowners_sub q hq
  have hqA := ((mem_filterWeakAll C _ q).mp hqW).1
  have hqA' : q ∈ F.gowners ++ [newPid F d] := hqA
  rcases List.mem_append.mp hqA' with hqF | hqn
  · obtain ⟨m, hm, hmid⟩ := rcF.gn q hqF
    have hqs : q.id.step < F.current_step := by rw [← hmid]; exact rcF.below m hm
    obtain ⟨hvF, hsub⟩ := drop_new F d hd rcF hsF rcA hsA hpA hnA C hv
    have h1 := hh C hvF q (hsub q hq hqs)
    exact add_new F d hd rcF hsF hpF hnF hmok rcA hsA C hv q.id hqs h1
  · have hqn' := List.mem_singleton.mp hqn
    have hnoop := filterWeakAll_append_noop (addNode F d "") C (pinC q.id) (fun x hx hs => by
      have hxA := ((mem_filterWeakAll C _ x).mp hx).1
      have hxA' : x ∈ F.gowners ++ [newPid F d] := hxA
      rcases List.mem_append.mp hxA' with h | h
      · obtain ⟨m, hm, hmid⟩ := rcF.gn x h
        have := rcF.below m hm
        rw [hmid] at this
        change x.id.step = q.id.step at hs
        rw [hs, hqn'] at this
        simp only [newPid, hd] at this
        omega
      · rw [List.mem_singleton.mp h, hqn']
        exact List.mem_singleton_self _)
    unfold Fw at hv ⊢
    rw [hnoop]
    exact hv

/-- info: 'AbsSat.GraphPath.Model.HereditaryUp.hpv_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hpv_addNode

end AbsSat.GraphPath.Model.HereditaryUp
