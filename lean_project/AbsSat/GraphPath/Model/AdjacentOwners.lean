-- lean_project/AbsSat/GraphPath/Model/AdjacentOwners.lean
import AbsSat.GraphPath.Model.SliceExact

/-!
# On the neighbouring steps, owners are exactly the links

At a result of the review, a node's owner table on the step just below it is **exactly its parents**,
and on the step just above it **exactly its sons**. So the tables coincide with the adjacency of the
partial paths the machine builds: an owner entry between neighbouring steps is a link of a path.

* `owners_below_iff_parents` — for a non-root node `x` of a valid review result with the reader's
  invariants: an owner `w` on step `x.step − 1` is a parent, and every parent is an owner.
  Coherence with the parents' owner union (`review_owners_coherent_parents`) keeps only owners that
  some parent owns; on the parents' own step a parent owns only itself (`OOS`).
* `owners_above_iff_sons` — the same for sons, through `review_owners_coherent_sons` and `PMS`.
* `reader_adjacent_owners` — both, at every state the reader visits from a final machine state.
-/

namespace AbsSat.GraphPath.Model.AdjacentOwners

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg

/-- The facts the two lemmas use, at a valid review result. -/
structure Adj (g : GPathM) : Prop where
  ctx : Pinned.Ctx g
  rc : Reader.RCtx g
  pms : Sons.PMS g
  sn : Sons.SN g
  links : Bridge.LinksInOwners g
  cohP : ∀ k ∈ intRange 1 (g.current_step - 1), ∀ id ∈ (g.line k).map (·.id), ∀ d,
    g.node? id = some d → intersectOwners d.owners (unionOwnersOf g d.parents) = d.owners
  cohS : ∀ k ∈ intRange 0 (g.current_step - 2), ∀ id ∈ (g.line k).map (·.id), ∀ d,
    g.node? id = some d → intersectOwners d.owners (unionOwnersOf g d.sons) = d.owners

/-- The reader's states have `Adj`. -/
theorem adj_of_readable (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (hpms : Sons.PMS g) (hsn : Sons.SN g) : Adj g := by
  obtain ⟨g₀, reqs, hc, rfl⟩ := hR
  obtain ⟨h, _, hform⟩ := filterAllAgg_form g₀ hc reqs
  have hvh : isValid (review h) = true := by rw [← hform]; exact hv
  have hR : ReadableAgg (filterAllAgg g₀ reqs) := ⟨g₀, reqs, hc, rfl⟩
  refine ⟨Reader.Ctx_of_readable _ (readable_of_readableAgg _ hR) hv, RCtx_of_readableAgg _ hR, hpms, hsn,
    ?_, ?_, ?_⟩
  · rw [hform]; exact Bridge.linksInOwners_review h hvh
  · rw [hform]; exact review_owners_coherent_parents h hvh
  · rw [hform]; exact review_owners_coherent_sons h hvh

/-- Coherence, read as membership, when the union has an entry on the owner's step. -/
theorem mem_union_of_coherent (g : GPathM) (ids os : List PathNodeId) (w : PathNodeId)
    (hcoh : intersectOwners os (unionOwnersOf g ids) = os) (hw : w ∈ os)
    (hent : hasStepEntry (unionOwnersOf g ids) w.id.step = true) :
    ∃ c ∈ ids, ∃ m, g.node? c = some m ∧ w ∈ m.owners := by
  have hw' : w ∈ intersectOwners os (unionOwnersOf g ids) := by rw [hcoh]; exact hw
  have hc := (List.mem_filter.mp hw').2
  rw [hent] at hc
  simp only [Bool.not_true, Bool.false_or, List.contains_iff_mem] at hc
  exact FabricAdd.exists_owner_of_mem_unionOwnersOf g ids w hc

/-- A neighbour that is a node owns itself, so the union of neighbours' owners has an entry on its step. -/
theorem union_entry (g : GPathM) (a : Adj g) (ids : List PathNodeId) (c : PathNodeId) (m : PNodeM)
    (hc : c ∈ ids) (hm : g.node? c = some m) :
    hasStepEntry (unionOwnersOf g ids) c.id.step = true :=
  List.any_eq_true.mpr ⟨c, mem_unionOwnersOf g ids c m c hc hm (a.ctx.self c m hm), beq_iff_eq.mpr rfl⟩

/-- A node's owner on its own step is itself. -/
theorem owner_own_step (g : GPathM) (a : Adj g) (c : PathNodeId) (m : PNodeM) (hm : g.node? c = some m)
    (w : PathNodeId) (hw : w ∈ m.owners) (hs : w.id.step = c.id.step) : w = c := by
  have hid := node?_id_eq g c m hm
  have := a.rc.oos m (List.mem_of_find?_eq_some hm) w hw (by rw [hid]; exact hs)
  rw [this, hid]

/-- **Owners on the step below are exactly the parents.** -/
theorem owners_below_iff_parents (g : GPathM) (a : Adj g) (x : PathNodeId) (n : PNodeM)
    (hx : g.node? x = some n) (hx1 : 1 ≤ x.id.step) (w : PathNodeId) (hw : w.id.step = x.id.step - 1) :
    w ∈ n.owners ↔ w ∈ n.parents := by
  have hmem := List.mem_of_find?_eq_some hx
  have hid := node?_id_eq g x n hx
  refine ⟨fun hwo => ?_, fun hwp => (a.links x n hx).1 w hwp⟩
  have hbelow := a.rc.below n hmem
  rw [hid] at hbelow
  have hroot : n.id.parent_id.isNone = false := by
    have hnr := a.rc.shape.notroot n hmem (by rw [hid]; omega)
    cases hp : n.id.parent_id with
    | none => exact absurd hp hnr
    | some _ => rfl
  obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _
    (SymTriReview.have_parents_of_isValidNode g n (a.ctx.nodeval x n hx) hroot)
  obtain ⟨mc0, hmc0, hmc0id⟩ := a.rc.shape.pn n hmem c0 hc0
  have hc0node : g.node? c0 = some mc0 := by rw [← hmc0id]; exact node?_of_mem a.rc.nodup mc0 hmc0
  have hc0step : c0.id.step = x.id.step - 1 := by rw [← hid]; exact a.rc.shape.pbelow n hmem c0 hc0
  have hk : x.id.step ∈ intRange 1 (g.current_step - 1) := mem_intRange hx1 (by omega)
  have hcoh := a.cohP _ hk x (mem_line_of_node? g x n hx _ rfl) n hx
  have hent : hasStepEntry (unionOwnersOf g n.parents) w.id.step = true := by
    rw [hw, ← hc0step]; exact union_entry g a n.parents c0 mc0 hc0 hc0node
  obtain ⟨c, hc, m, hm, hwm⟩ := mem_union_of_coherent g n.parents n.owners w hcoh hwo hent
  have hcstep : c.id.step = x.id.step - 1 := by rw [← hid]; exact a.rc.shape.pbelow n hmem c hc
  have hwc := owner_own_step g a c m hm w hwm (by rw [hw, hcstep])
  rw [hwc]; exact hc

/-- **Owners on the step above are exactly the sons.** -/
theorem owners_above_iff_sons (g : GPathM) (a : Adj g) (x : PathNodeId) (n : PNodeM)
    (hx : g.node? x = some n) (hxl : x.id.step ≤ g.current_step - 2) (w : PathNodeId)
    (hw : w.id.step = x.id.step + 1) :
    w ∈ n.owners ↔ w ∈ n.sons := by
  have hmem := List.mem_of_find?_eq_some hx
  have hid := node?_id_eq g x n hx
  refine ⟨fun hwo => ?_, fun hws => (a.links x n hx).2 w hws⟩
  have hsnn := a.rc.snn n hmem
  rw [hid] at hsnn
  -- a son's step is one above: it lists `x` among its parents
  have sonStep : ∀ c ∈ n.sons, ∀ m, g.node? c = some m → c.id.step = x.id.step + 1 := by
    intro c hc m hm
    have hmm := List.mem_of_find?_eq_some hm
    have hmid := node?_id_eq g c m hm
    have hxp : n.id ∈ m.parents := a.pms n hmem c hc m hmm hmid
    have := a.rc.shape.pbelow m hmm n.id hxp
    rw [hid, hmid] at this
    omega
  have hnl : (n.id.id.step == g.current_step - 1) = false := by
    rw [hid]; exact beq_false_of_ne (by omega)
  obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _
    (SymTriReview.have_sons_of_isValidNode g n (a.ctx.nodeval x n hx) hnl)
  obtain ⟨mc0, hmc0, hmc0id⟩ := a.sn n hmem c0 hc0
  have hc0node : g.node? c0 = some mc0 := by rw [← hmc0id]; exact node?_of_mem a.rc.nodup mc0 hmc0
  have hk : x.id.step ∈ intRange 0 (g.current_step - 2) := mem_intRange hsnn hxl
  have hcoh := a.cohS _ hk x (mem_line_of_node? g x n hx _ rfl) n hx
  have hent : hasStepEntry (unionOwnersOf g n.sons) w.id.step = true := by
    rw [hw, ← sonStep c0 hc0 mc0 hc0node]; exact union_entry g a n.sons c0 mc0 hc0 hc0node
  obtain ⟨c, hc, m, hm, hwm⟩ := mem_union_of_coherent g n.sons n.owners w hcoh hwo hent
  have hwc := owner_own_step g a c m hm w hwm (by rw [hw, sonStep c hc m hm])
  rw [hwc]; exact hc

/-- **At every state the reader visits, owners on neighbouring steps are exactly the links.** -/
theorem reader_adjacent_owners (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ) (g : GPathM) (hF : ReadFrom (filterAllAgg kv.2 []) g)
    (hvg : isValid g = true) : Adj g := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hR₀ : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  obtain ⟨_, hp, hn⟩ := SliceExact.links_readFrom _ hR₀
    (AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot [])
    (AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms) (AggInvariants.SN_filterAllAgg kv.2 [] hm.sn) g hF
  exact adj_of_readable g (PinExact.readableAgg_of_readFrom _ hR₀ g hF) hvg hp hn

/-- info: 'AbsSat.GraphPath.Model.AdjacentOwners.owners_above_iff_sons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owners_above_iff_sons

end AbsSat.GraphPath.Model.AdjacentOwners
