-- lean_project/AbsSat/GraphPath/Model/EmbeddedSupport.lean
import AbsSat.GraphPath.Model.SpcSupport

/-!
# A reviewed sub-construction survives inside the whole construction

The global view (report v124): the machine builds, step by step, the set of partial paths. Pinning a
node `q` in a final state gives **exactly** the state the machine builds on the branch of `q` alone
(probe `helly commute`: same nodes and same owner tables, on every pin measured). This module proves
the half of that picture that is about survival.

* `Embedded B G` — `B` sits inside `G`: same current step, `B`'s global owners are `G`'s, and every node
  of `B` is a node of `G` whose owners and parents contain `B`'s.
* **`sup_of_embedded`** — if `B` is a valid state of the reader's kind (`Adj`, `AggOk`, `SMP`), then
  `B`'s own nodes and owner tables are a support relation **inside `G`**: every condition `Sup` asks
  is a fixpoint fact of `B` that only needs more room in `G`.
* **`survives_of_embedded`** — so every node of `B` stays a global owner of `G` after any pin
  compatible with `B` and the whole aggressive review (`AnchoredSurvive`), and **the pinned `G` is
  valid**.

What is left of the global picture is the other half: that pinning `G` does not keep anything the
branch alone would not have (no borrowing across joins).
-/

namespace AbsSat.GraphPath.Model.EmbeddedSupport

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.AnchoredSurvive
open AbsSat.GraphPath.Model.AggFixpoint
open AbsSat.GraphPath.Model.AdjacentOwners

/-- The members: the nodes of `B`. -/
def Mem (B : GPathM) (p : PathNodeId) : Prop := ∃ m, B.node? p = some m

/-- `B` sits inside `G`: same current step, `B`'s global owners are `G`'s, and every node of `B` is a
node of `G` keeping, among `B`'s nodes, its owners and its parents. -/
structure Embedded (B G : GPathM) : Prop where
  step : B.current_step = G.current_step
  gow : ∀ p ∈ B.gowners, p ∈ G.gowners
  node : ∀ p m, B.node? p = some m →
    ∃ n, G.node? p = some n ∧ (∀ q ∈ m.owners, Mem B q → q ∈ n.owners) ∧
      (∀ q ∈ m.parents, Mem B q → q ∈ n.parents)

/-- The relation: `B`'s owner tables, between nodes of `B`. -/
def Rel (B : GPathM) (x v : PathNodeId) : Prop := ∃ m, B.node? x = some m ∧ v ∈ m.owners ∧ Mem B v

section
variable (B : GPathM) (a : Adj B)

include a in
theorem mem_bounds {p : PathNodeId} (h : Mem B p) : 0 ≤ p.id.step ∧ p.id.step < B.current_step := by
  obtain ⟨m, hm⟩ := h
  have hmem := List.mem_of_find?_eq_some hm
  rw [← node?_id_eq B p m hm]
  exact ⟨a.rc.snn m hmem, a.rc.below m hmem⟩

include a in
/-- An owner in range of a node of `B` is a node of `B`. -/
theorem mem_of_owner (x : PathNodeId) (m : PNodeM) (hx : B.node? x = some m) (v : PathNodeId)
    (hv : v ∈ m.owners) (h0 : 0 ≤ v.id.step) (h1 : v.id.step < B.current_step) : Mem B v := by
  obtain ⟨mv, hmv, hmvid⟩ := a.rc.gn v (a.ctx.ownGow x m hx v hv h0 h1)
  exact ⟨mv, by rw [← hmvid]; exact node?_of_mem a.rc.nodup mv hmv⟩

include a in
/-- A valid node of `B` has an owner at every step in range. -/
theorem owner_at (x : PathNodeId) (m : PNodeM) (hx : B.node? x = some m) (l : Int) (h0 : 0 ≤ l)
    (h1 : l < B.current_step) : ∃ r ∈ m.owners, r.id.step = l := by
  have hall := owners_ok_of_isValidNode B m (a.ctx.nodeval x m hx)
  obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall l (mem_intRange h0 (by omega)))
  exact ⟨r, hr, eq_of_beq hrs⟩

include a in
/-- Coherence with a list of neighbours that are valid nodes, read as membership. -/
theorem from_union (ids : List PathNodeId) (os : List PathNodeId) (v : PathNodeId)
    (hcoh : intersectOwners os (unionOwnersOf B ids) = os) (hv : v ∈ os)
    (c0 : PathNodeId) (mc0 : PNodeM) (hc0 : c0 ∈ ids) (hmc0 : B.node? c0 = some mc0)
    (h0 : 0 ≤ v.id.step) (h1 : v.id.step < B.current_step) :
    ∃ c ∈ ids, ∃ mc, B.node? c = some mc ∧ v ∈ mc.owners := by
  obtain ⟨r, hr, hrs⟩ := owner_at B a c0 mc0 hmc0 v.id.step h0 h1
  have hent : hasStepEntry (unionOwnersOf B ids) v.id.step = true :=
    List.any_eq_true.mpr ⟨r, mem_unionOwnersOf B ids c0 mc0 r hc0 hmc0 hr, beq_iff_eq.mpr hrs⟩
  exact mem_union_of_coherent B ids os v hcoh hv hent
end

/-- **A valid reader-kind state is a support relation inside any state that contains it.** -/
theorem sup_of_embedded (B G : GPathM) (a : Adj B) (hok : AggOk B) (hsmp : Sons.SMP B)
    (he : Embedded B G) : Sup G (Mem B) (Rel B) := by
  have gnode : ∀ p m, B.node? p = some m → ∀ n, G.node? p = some n →
      (∀ q ∈ m.owners, Mem B q → q ∈ n.owners) ∧ (∀ q ∈ m.parents, Mem B q → q ∈ n.parents) := by
    intro p m hm n hn
    obtain ⟨n', hn', ho, hp⟩ := he.node p m hm
    rw [hn] at hn'
    cases hn'
    exact ⟨ho, hp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- global owners
    rintro p ⟨m, hm⟩
    obtain ⟨h0, h1⟩ := mem_bounds B a ⟨m, hm⟩
    exact he.gow p (List.mem_filter.mp (Pinned.mem_ownersAt_gowners B a.ctx p m hm h0 h1)).1
  · -- nodes
    rintro p ⟨m, hm⟩
    obtain ⟨n, hn, _⟩ := he.node p m hm
    rw [hn]; rfl
  · -- steps
    intro p hp
    rw [← he.step]; exact mem_bounds B a hp
  · -- domain
    rintro x v ⟨m, hm, _, hv⟩
    exact ⟨⟨m, hm⟩, hv⟩
  · -- owners
    rintro x v n ⟨m, hm, hvm, hv⟩ hn
    exact (gnode x m hm n hn).1 v hvm hv
  · -- cover
    rintro x ⟨m, hm⟩ l hl0 hl1
    rw [← he.step] at hl1
    obtain ⟨r, hr, hrs⟩ := owner_at B a x m hm l hl0 hl1
    exact ⟨r, ⟨m, hm, hr, mem_of_owner B a x m hm r hr (by omega) (by omega)⟩, hrs⟩
  · -- parents
    intro x d hx hd hpid v hxv
    obtain ⟨m, hm, hvm, hv⟩ := hxv
    have hmem := List.mem_of_find?_eq_some hm
    have hid := node?_id_eq B x m hm
    have hroot : m.id.parent_id.isNone = false := by
      rw [hid]
      cases hp : x.parent_id with
      | none => exact absurd hp hpid
      | some _ => rfl
    obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _
      (SelfOwn.have_parents_of_isValidNode B m (a.ctx.nodeval x m hm) hroot)
    obtain ⟨mc0, hmc0, hmc0id⟩ := a.rc.shape.pn m hmem c0 hc0
    have hc0node : B.node? c0 = some mc0 := by rw [← hmc0id]; exact node?_of_mem a.rc.nodup mc0 hmc0
    have hbelow := a.rc.shape.pbelow m hmem c0 hc0
    have hc0nn := a.rc.snn mc0 hmc0
    rw [hmc0id] at hc0nn
    rw [hid] at hbelow
    obtain ⟨hx0, hx1⟩ := mem_bounds B a hx
    obtain ⟨hv0, hv1⟩ := mem_bounds B a hv
    have hk : x.id.step ∈ intRange 1 (B.current_step - 1) := mem_intRange (by omega) (by omega)
    have hcoh := a.cohP _ hk x (mem_line_of_node? B x m hm _ rfl) m hm
    obtain ⟨c, hc, mc, hmc, hvc⟩ := from_union B a m.parents m.owners v hcoh hvm c0 mc0 hc0 hc0node hv0 hv1
    have hxc : x ∈ mc.owners := by
      have hson : m.id ∈ mc.sons :=
        hsmp m hmem c hc mc (List.mem_of_find?_eq_some hmc) (node?_id_eq B c mc hmc)
      rw [hid] at hson
      exact (a.links c mc hmc).2 x hson
    have hdp := (gnode x m hm d hd).2 c hc ⟨mc, hmc⟩
    exact ⟨c, hdp, ⟨m, hm, (a.links x m hm).1 c hc, ⟨mc, hmc⟩⟩, ⟨mc, hmc, hxc, ⟨m, hm⟩⟩,
      ⟨mc, hmc, hvc, hv⟩⟩
  · -- sons
    intro x hx hlast v hxv
    obtain ⟨m, hm, hvm, hv⟩ := hxv
    have hmem := List.mem_of_find?_eq_some hm
    have hid := node?_id_eq B x m hm
    obtain ⟨hx0, hx1⟩ := mem_bounds B a hx
    obtain ⟨hv0, hv1⟩ := mem_bounds B a hv
    rw [← he.step] at hlast
    have hnl : (m.id.id.step == B.current_step - 1) = false := by
      rw [hid]; exact beq_false_of_ne hlast
    obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _
      (SelfOwn.have_sons_of_isValidNode B m (a.ctx.nodeval x m hm) hnl)
    obtain ⟨mc0, hmc0, hmc0id⟩ := a.sn m hmem c0 hc0
    have hc0node : B.node? c0 = some mc0 := by rw [← hmc0id]; exact node?_of_mem a.rc.nodup mc0 hmc0
    have hk : x.id.step ∈ intRange 0 (B.current_step - 2) := mem_intRange hx0 (by omega)
    have hcoh := a.cohS _ hk x (mem_line_of_node? B x m hm _ rfl) m hm
    obtain ⟨c, hc, mc, hmc, hvc⟩ := from_union B a m.sons m.owners v hcoh hvm c0 mc0 hc0 hc0node hv0 hv1
    have hxp : x ∈ mc.parents := by
      have h' := a.pms m hmem c hc mc (List.mem_of_find?_eq_some hmc) (node?_id_eq B c mc hmc)
      rwa [hid] at h'
    obtain ⟨nc, hnc, _, hncp⟩ := he.node c mc hmc
    exact ⟨c, nc, hnc, hncp x hxp ⟨m, hm⟩, ⟨m, hm, (a.links x m hm).2 c hc, ⟨mc, hmc⟩⟩,
      ⟨mc, hmc, (a.links c mc hmc).1 x hxp, ⟨m, hm⟩⟩, ⟨mc, hmc, hvc, hv⟩⟩
  · -- pairs
    intro x v hxv l hl0 hl1
    obtain ⟨m, hm, hvm, hv⟩ := hxv
    obtain ⟨mv, hmv⟩ := hv
    obtain ⟨hx0, hx1⟩ := mem_bounds B a ⟨m, hm⟩
    obtain ⟨hv0, hv1⟩ := mem_bounds B a ⟨mv, hmv⟩
    rw [← he.step] at hl1
    have hs := (hok x m v mv hm hmv hx0 hx1 hv0 hv1 hvm (a.ctx.nodeval x m hm) (a.ctx.nodeval v mv hmv)).2
    have hk := List.all_eq_true.mp hs l (mem_intRange hl0 (by omega))
    obtain ⟨r0, hr0, hr0s⟩ := owner_at B a v mv hmv l hl0 hl1
    have hent : hasStepEntry mv.owners l = true := List.any_eq_true.mpr ⟨r0, hr0, beq_iff_eq.mpr hr0s⟩
    rw [hent] at hk
    simp only [Bool.not_true, Bool.false_or] at hk
    obtain ⟨z, hz, hzv⟩ := List.any_eq_true.mp hk
    obtain ⟨hzx, hzs⟩ := List.mem_filter.mp hz
    have hzs' : z.id.step = l := eq_of_beq hzs
    have hzm := mem_of_owner B a x m hm z hzx (by omega) (by omega)
    exact ⟨z, ⟨m, hm, hzx, hzm⟩, ⟨mv, hmv, List.contains_iff_mem.mp hzv, hzm⟩, hzs'⟩
  · -- symmetry
    rintro x v ⟨m, hm, hvm, ⟨mv, hmv⟩⟩
    obtain ⟨hx0, hx1⟩ := mem_bounds B a ⟨m, hm⟩
    obtain ⟨hv0, hv1⟩ := mem_bounds B a ⟨mv, hmv⟩
    exact ⟨mv, hmv, ownSym_of_aggOk B hok x v m mv hm hmv hx0 hx1 hv0 hv1 hvm (a.ctx.nodeval x m hm)
      (a.ctx.nodeval v mv hmv), ⟨m, hm⟩⟩
  · -- links: in `B` an owner on the step just below is a parent
    rintro x c d ⟨m, hm, hcm, hc⟩ _ hs hd
    have hc0 := (mem_bounds B a hc).1
    have hcp := (owners_below_iff_parents B a x m hm (by omega) c (by omega)).mp hcm
    exact (gnode x m hm d hd).2 c hcp hc

/-- **A valid embedded state survives every compatible pin of the whole state, which stays valid.** -/
theorem survives_of_embedded (B G : GPathM) (a : Adj B) (hok : AggOk B) (hsmp : Sons.SMP B)
    (hvB : isValid B = true) (he : Embedded B G) (hsmpG : Sons.SMP G) (hnrG : Parents.NotRoot G)
    (reqs : List NodeId) (hpin : ∀ r ∈ reqs, ∀ p, Mem B p → p.id.step = r.step → p.id = r) :
    (∀ p, Mem B p → p ∈ (filterAllAgg G reqs).gowners) ∧ isValid (filterAllAgg G reqs) = true := by
  have hsurv := gowners_filterAllAgg_of_AOk G ⟨sup_of_embedded B G a hok hsmp he, hsmpG, hnrG⟩ reqs hpin
  refine ⟨hsurv, ?_⟩
  have hcs : (filterAllAgg G reqs).current_step = B.current_step :=
    (pruned_filterAllAgg G reqs).step_eq.trans he.step.symm
  simp only [isValid, List.all_eq_true] at hvB ⊢
  intro k hk
  rw [hcs] at hk
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (hvB k hk)
  obtain ⟨mq, hmq, hmqid⟩ := a.rc.gn q hq
  have hqn : B.node? q = some mq := by rw [← hmqid]; exact node?_of_mem a.rc.nodup mq hmq
  exact List.any_eq_true.mpr ⟨q, hsurv q ⟨mq, hqn⟩, hqs⟩

/-- info: 'AbsSat.GraphPath.Model.EmbeddedSupport.survives_of_embedded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms survives_of_embedded

end AbsSat.GraphPath.Model.EmbeddedSupport
