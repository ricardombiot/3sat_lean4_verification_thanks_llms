-- lean_project/AbsSat/GraphPath/Model/PinExact.lean
import AbsSat.GraphPath.Model.ReaderAggRun
import AbsSat.GraphPath.Model.UnitPropagation
import AbsSat.GraphPath.Model.LocalContradiction
import AbsSat.GraphPath.Model.Threaded

/-!
# What a pin does at the aggressive review's fixpoint: exactly its slice

`ReaderAggRun.sat_of_pickSomeAgg` reduces the soundness of the Improves verdict to `PickSomeAgg`: at
every state the reader visits, some pin keeps the graph valid. The probe `helly pins` (report v117)
measured what a pin actually does there: **it removes exactly the nodes outside its slice**, the
slice of a map node `mid` being the nodes with an owner carrying `mid`. No slice node is removed, no
node outside is kept, and every pin is valid, although the slice has many Helly-3 gaps (the sweep
drops owner pairs, not nodes).

* `InSlice n mid` — `n` has an owner carrying the map node `mid`.
* `PinExact g mid` — every node of `g` in the slice of `mid` is still a global owner after the pin.
  **Open**; this is the conjecture the measurement supports.
* `inSlice_of_survives` — the other half, **proved**: whatever survives a valid pin is in the slice.
  Through `pruned_filterAll_filterAllAgg`: the aggressive review starts with the base review, so the
  base review's fixpoint facts (`UnitPropagation.owner_at_step`) apply.
* `isValid_pin_of_pinExact` — **proved**: with symmetric owner tables (measured: no asymmetric entry
  at the aggressive review's fixpoints), `PinExact` makes the pin valid. A pinned node owns a node at
  every step, and by symmetry each of those lies in the slice.
* `pickSomeAgg_of_pinExact`, `sat_of_pinExact` — so `PinExact` and symmetry along the reader's states
  give `PickSomeAgg`, and with `ReaderAggRun` the soundness of the verdict.
-/

namespace AbsSat.GraphPath.Model.PinExact

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice intRange_bounds gowner_of_isValid)

-- ============================================================
-- The slice
-- ============================================================

/-- `n` has an owner carrying the map node `mid`. -/
def InSlice (n : PNodeM) (mid : NodeId) : Prop := ∃ q ∈ n.owners, q.id = mid

/-- **The conjecture.** Pinning `mid` keeps every node of its slice as a global owner. -/
def PinExact (g : GPathM) (mid : NodeId) : Prop :=
  ∀ n ∈ g.nodes, InSlice n mid → n.id ∈ (filterAllAgg g [mid]).gowners

-- ============================================================
-- The aggressive review starts with the base review
-- ============================================================

theorem pruned_review_reviewAggFuel (fuel : Nat) (x : GPathM) :
    Pruned (review x) (reviewAggFuel (fuel + 1) x) := by
  simp only [reviewAggFuel]
  split
  · split
    · exact Pruned.trans (pruned_aggSweep _) (pruned_reviewAggFuel _ _)
    · exact Pruned.refl _
  · exact Pruned.refl _

theorem pruned_filterAll_filterAllAgg (g : GPathM) (reqs : List NodeId) :
    Pruned (filterAll g reqs) (filterAllAgg g reqs) :=
  pruned_review_reviewAggFuel _ _

theorem isValid_of_pruned_valid {g g' : GPathM} (hpr : Pruned g g') (hv : isValid g' = true) :
    isValid g = true := by
  simp only [isValid, List.all_eq_true] at hv ⊢
  intro k hk
  have hk' : k ∈ intRange 0 (g'.current_step - 1) := by rw [hpr.step_eq]; exact hk
  have h := hv k hk'
  simp only [hasStepEntry, List.any_eq_true] at h ⊢
  obtain ⟨q, hq, hqs⟩ := h
  exact ⟨q, hpr.gowners_sub q hq, hqs⟩

-- ============================================================
-- Half of it, proved: survivors are in the slice
-- ============================================================

/-- **What survives a valid pin is in the slice.** -/
theorem inSlice_of_survives (g : GPathM) (hgn : GownersNodes.GN g) (hnd : NodupIds g)
    (mid : NodeId) (h0 : 0 ≤ mid.step) (hlt : mid.step < g.current_step)
    (hv : isValid (filterAllAgg g [mid]) = true)
    (n : PNodeM) (hn : n ∈ g.nodes) (hs : n.id ∈ (filterAllAgg g [mid]).gowners) :
    InSlice n mid := by
  have hpr := pruned_filterAll_filterAllAgg g [mid]
  have hvb : isValid (filterAll g [mid]) = true := isValid_of_pruned_valid hpr hv
  obtain ⟨d, hd, hdid, hdval, hdfix⟩ := UnitPropagation.node_of_gowner g [mid] hvb
    (GownersNodes.GN_filterAll g [mid] hgn) n.id (hpr.gowners_sub _ hs)
  obtain ⟨q, hq, hqs, hqg⟩ := UnitPropagation.owner_at_step g [mid] hvb d hdval hdfix mid.step h0 hlt
  have hq0 := (pruned_review ([mid].foldl filterRequire g)).gowners_sub q hqg
  have hqid : q.id = mid := by
    rcases (LocalContradiction.mem_foldl_filterRequire [mid] g q hq0).2 mid List.mem_cons_self with h | h
    · exact absurd hqs h
    · exact h
  obtain ⟨n₀, hn₀, hid₀, hown₀, _⟩ := (pruned_filterAll g [mid]).nodes_derived d hd
  have heq : n₀ = n := by
    have h1 := node?_of_mem hnd n₀ hn₀
    have h2 := node?_of_mem hnd n hn
    rw [← hid₀, hdid] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  subst heq
  exact ⟨q, hown₀ q hq, hqid⟩

-- ============================================================
-- PinExact makes the pin valid
-- ============================================================

/-- **With symmetric owners, `PinExact` makes the pin valid.** -/
theorem isValid_pin_of_pinExact (g : GPathM) (ctx : Pinned.Ctx g) (hnd : NodupIds g)
    (hsym : Threaded.OwnSymmetric g)
    (p : PathNodeId) (hp : p ∈ g.gowners) (hpe : PinExact g p.id) :
    isValid (filterAllAgg g [p.id]) = true := by
  have hstep := (pruned_filterAllAgg g [p.id]).step_eq
  obtain ⟨np, hnp_mem, hnpid⟩ := ctx.gn p hp
  have hnp : g.node? p = some np := by
    rw [← hnpid]
    exact node?_of_mem hnd np hnp_mem
  have hval := ctx.nodeval p np hnp
  have hall := owners_ok_of_isValidNode g np hval
  simp only [isValid, List.all_eq_true]
  intro j hj
  rw [hstep] at hj
  obtain ⟨hj0, hj1⟩ := intRange_bounds hj
  have hent := List.all_eq_true.mp hall j (mem_intRange hj0 hj1)
  obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp hent
  have hrstep : r.id.step = j := eq_of_beq hrs
  have hrg : r ∈ g.gowners := ctx.ownGow p np hnp r hr (by omega) (by omega)
  obtain ⟨nr, hnr_mem, hnrid⟩ := ctx.gn r hrg
  have hnr : g.node? r = some nr := by rw [← hnrid]; exact node?_of_mem hnd nr hnr_mem
  have hpr : p ∈ nr.owners := hsym p np r nr hnp hnr hr
  have hin := hpe nr hnr_mem ⟨p, hpr, rfl⟩
  rw [hnrid] at hin
  exact List.any_eq_true.mpr ⟨r, hin, beq_iff_eq.mpr hrstep⟩

/-- **`PinExact` at a step with a choice gives `PickSomeAgg`.** -/
theorem pickSomeAgg_of_pinExact (g : GPathM) (ctx : Pinned.Ctx g) (hnd : NodupIds g)
    (hsym : Threaded.OwnSymmetric g)
    (hpe : ∀ p ∈ g.gowners, PinExact g p.id) : PickSomeAgg g := by
  intro hch
  obtain ⟨k, hkmem, hck⟩ := List.any_eq_true.mp hch
  obtain ⟨hk0, hk1⟩ := intRange_bounds hkmem
  obtain ⟨q, hq, _⟩ := List.any_eq_true.mp hck
  exact ⟨k, hk0, by omega, hck, q, hq,
    isValid_pin_of_pinExact g ctx hnd hsym q (List.mem_filter.mp hq).1 (hpe q (List.mem_filter.mp hq).1)⟩

-- ============================================================
-- The verdict, reduced to PinExact
-- ============================================================

theorem readableAgg_of_readFrom (g₀ : GPathM) (h₀ : ReadableAgg g₀) :
    ∀ g, ReadFrom g₀ g → ReadableAgg g := by
  intro g hF
  induction hF with
  | start => exact h₀
  | pin g' mid _ _ ih => exact ReadableAgg_filterAllAgg g' ih [mid]

/-- **Soundness of the Improves verdict from `PinExact` and symmetric owners along the reader's
states.** -/
theorem sat_of_pinExact (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hsym : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → Threaded.OwnSymmetric g)
    (hpe : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true →
      ∀ p ∈ g.gowners, PinExact g p.id) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  refine ReaderAggRun.sat_of_pickSomeAgg φ hwf kv hkv hv (fun g hF hvg => ?_)
  have hR : ReadableAgg g := readableAgg_of_readFrom _ ⟨kv.2, [], hm.rctx, rfl⟩ g hF
  exact pickSomeAgg_of_pinExact g
    (Reader.Ctx_of_readable g (readable_of_readableAgg g hR) hvg) (RCtx_of_readableAgg g hR).nodup
    (hsym g hF hvg) (hpe g hF hvg)

/-- info: 'AbsSat.GraphPath.Model.PinExact.inSlice_of_survives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inSlice_of_survives

/-- info: 'AbsSat.GraphPath.Model.PinExact.sat_of_pinExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinExact

end AbsSat.GraphPath.Model.PinExact
