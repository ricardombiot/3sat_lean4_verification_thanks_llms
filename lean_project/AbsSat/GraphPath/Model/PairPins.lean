-- lean_project/AbsSat/GraphPath/Model/PairPins.lean
import AbsSat.GraphPath.Model.UnionPaths

/-!
# No borrowing, and the pair level as validity

**No borrowing.** Measured (probe `noborrow`, v148): not even the **plain** union of the two pinned
branches has a mixed path — it has exactly the paths of the reviewed union, each on one branch. So
borrowing is a question about the structure of the union, not about the review:

* **`noBorrow_of_plain`** (no hypothesis) — a path of the reviewed union is a path of the plain union;
  so `NoBorrow` for the reviewed union follows from no borrowing in the plain one.

**The pair level as validity.** `PairPinExact` (v143) asks that every entry of a pinned, reviewed reader
state lie on a path. With the bottom-up machinery (v145) this becomes a statement about validity:

* **`realizes_of_entryPins`** — in a state the reader reaches, if pinning the map nodes of `x`, of `q`
  and of their parents keeps the state valid (`EntryPin`), then, under `LivePinUp`, the entry `(x, q)`
  lies on a path: complete the pins bottom-up; the fully decided state is a path (`chain_of_ids`); its
  node at `x`'s step carries `x`'s map node and `x`'s parent's, so it **is** `x`, and likewise `q`.
* **`tablesSound_of_entryPins`** — so every state the reader reaches is exact under `LivePinUp` and
  `EntryPin`.
-/

namespace AbsSat.GraphPath.Model.PairPins

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.BranchCompat (pinOneByOne)
open AbsSat.GraphPath.Model.BranchRun (isValid_of_embedded)
open AbsSat.GraphPath.Model.SupportSplit (mem_of_hasNode')
open AbsSat.GraphPath.Model.PickInduction (gowner_of_isValid)
open AbsSat.GraphPath.Model.PinExtends
open AbsSat.GraphPath.Model.PinUp
open AbsSat.GraphPath.Model.UnionPaths (NoBorrow)

-- ============================================================
-- No borrowing: the reviewed union from the plain one
-- ============================================================

/-- No borrowing in the plain union of two states. -/
def PlainNoBorrow (a b : GPathM) : Prop :=
  ∀ sel, ChainSound (join a b) sel → ChainSound a sel ∨ ChainSound b sel

/-- **The review adds no mixed path**: a path of the reviewed union is a path of the plain union. -/
theorem noBorrow_of_plain (a b : GPathM) (hnd : NodupIds (join a b)) (hsmp : Sons.SMP (join a b))
    (h : PlainNoBorrow a b) : NoBorrow a b :=
  fun sel hsc => h sel (SubsetSemantics.ChainSound_of_pruned (pruned_reviewAgg (join a b)) hnd hsmp sel hsc)

-- ============================================================
-- The pair level as validity
-- ============================================================

/-- The pins of an entry: the map nodes of both ends and of their parents. -/
def entryPins (x q : PathNodeId) : List NodeId :=
  [x.id, q.id] ++ x.parent_id.toList ++ q.parent_id.toList

/-- Pinning one by one from a reader's state, ending valid, stays a reader's state. -/
theorem readFrom_pinOneByOne {g₀ : GPathM} (h0 : RF g₀) : ∀ (P : List NodeId) (S : GPathM),
    ReadFrom g₀ S → isValid S = true → isValid (pinOneByOne S P) = true → ReadFrom g₀ (pinOneByOne S P) := by
  intro P
  induction P with
  | nil => intro S hS _ _; exact hS
  | cons r rest ih =>
    intro S hS hv hvP
    have hS1 := ReadFrom.pin S r hS hv
    have hrf1 := (rf_readFrom h0 hS1).1
    have hv1 : isValid (filterAllAgg S [r]) = true :=
      isValid_of_embedded (Hereditary.embedded_of_pruned_self (SeqPin.pruned_pinOneByOne rest _)
        (RCtx_of_readableAgg _ hrf1.readable).nodup) hvP
    exact ih _ hS1 hv1 hvP

/-- The node at a step of a fully decided state, whose map node and parent's map node are pinned as
`x`'s, is `x`. -/
theorem eq_of_pins (F : GPathM) (ad : AdjacentOwners.Adj F) (hok : AggFixpoint.AggOk F) (hsmp : Sons.SMP F)
    (x g : PathNodeId) (hg : Mem F g) (hs : g.id.step = x.id.step) (hid : g.id = x.id)
    (hroot : x.id.step = 0 → x.parent_id = none)
    (hpar : ∀ w, Mem F w → w.id.step = x.id.step - 1 → 0 < x.id.step → x.parent_id = some w.id) : g = x := by
  have h2 : g.parent_id = x.parent_id := by
    obtain ⟨h0, _⟩ := mem_bounds F ad hg
    by_cases hz : x.id.step = 0
    · rw [root_of_mem F ad hg (by rw [hs]; exact hz), hroot hz]
    · obtain ⟨w, hw, hws, hgw⟩ := parent_of_mem F ad hok hsmp hg (by omega)
      rw [hgw, hpar w hw (by rw [hws, hs]) (by omega)]
  cases g
  cases x
  simp only [PathNodeId.mk.injEq]
  exact ⟨hid, h2⟩

variable (φ : Cnf)

/-- **An entry lies on a path, if pinning its ends and their parents keeps the state valid** (under
`LivePinUp`). -/
theorem realizes_of_entryPins (hwf : WF φ) {g₀ : GPathM} (hB : Base φ g₀) (hL : LivePinUp φ g₀)
    {S : GPathM} (hS : ReadFrom g₀ S) (hv : isValid S = true) (x q : PathNodeId) (hxq : Rel S x q)
    (hvP : isValid (pinOneByOne S (entryPins x q)) = true) : Realizes S x q := by
  obtain ⟨hrfS, _, _, hcsS⟩ := facts_of_readFrom φ hB hS
  have adS := adj_rf hrfS hv
  have okS := aggOk_rf hrfS hv
  have ncS := RCtx_of_readableAgg S hrfS.readable
  have hF0 := readFrom_pinOneByOne hB.rf (entryPins x q) S hS hv hvP
  have hpr0 := SeqPin.pruned_pinOneByOne (entryPins x q) S
  obtain ⟨F, hF, hvF, hprF, hdec⟩ := complete_up φ hwf hB hL (stepCount φ).toNat _ 0 hF0 hvP
    (Int.le_refl _) (by have := ConservationCore.stepCount_pos φ; omega) (fun k h0 h1 => absurd h1 (by omega))
  obtain ⟨hrfF, _, _, hcsF⟩ := facts_of_readFrom φ hB hF
  have adF := adj_rf hrfF hvF
  have okF := aggOk_rf hrfF hvF
  have hpr := Pruned.trans hpr0 hprF
  -- the path of the fully decided state
  obtain ⟨g1, hg1, _⟩ := gowner_of_isValid F hvF 0 (Int.le_refl _)
    (by rw [hcsF]; exact ConservationCore.stepCount_pos φ)
  obtain ⟨sel, hsc, hsel⟩ := chain_of_ids F adF okF hrfF.smp hvF
    (fun a b ha hb hs => by
      obtain ⟨h0, h1⟩ := mem_bounds F adF ha
      exact hdec a.id.step h0 (by rw [← hcsF]; exact h1) a b ha hb rfl hs.symm)
    (mem_of_hasNode' F adF (adF.ctx.gn g1 hg1))
  -- a pinned global owner of `F` carries the pin
  have pinF : ∀ w, Mem F w → ∀ r ∈ entryPins x q, w.id.step = r.step → w.id = r := by
    intro w hw r hr hs
    exact OraclePath.pinned_ids (entryPins x q) S r hr w (hprF.gowners_sub w (mem_gowner F adF hw)) hs
  -- the node of `F` at the step of an end `y ∈ {x, q}` is `y`
  have atEnd : ∀ y, Mem S y → y.id ∈ entryPins x q → (∀ p, y.parent_id = some p → p ∈ entryPins x q) →
      Mem F y := by
    intro y hy hyP hyPar
    obtain ⟨h0, h1⟩ := mem_bounds S adS hy
    obtain ⟨g, hg, hgs⟩ := gowner_of_isValid F hvF y.id.step h0 (by rw [hcsF, ← hcsS]; exact h1)
    have hgm := mem_of_hasNode' F adF (adF.ctx.gn g hg)
    have heq := eq_of_pins F adF okF hrfF.smp y g hgm hgs (pinF g hgm y.id hyP hgs)
      (fun hz => root_of_mem S adS hy hz)
      (fun w hw hws hpos => by
        obtain ⟨v, hv', hvs, hyv⟩ := parent_of_mem S adS okS hrfS.smp hy hpos
        rw [hyv, pinF w hw v.id (hyPar v.id hyv) (by rw [hws, hvs])])
    rw [← heq]; exact hgm
  obtain ⟨mx, hmxm, _, hmq⟩ := hxq
  have hmx : Mem S x := ⟨mx, hmxm⟩
  have inX : x.id ∈ entryPins x q := List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)
  have inQ : q.id ∈ entryPins x q :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have inXP : ∀ p, x.parent_id = some p → p ∈ entryPins x q := by
    intro p hp
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    rw [hp]; exact List.mem_singleton_self p
  have inQP : ∀ p, q.parent_id = some p → p ∈ entryPins x q := by
    intro p hp
    refine List.mem_append_right _ ?_
    rw [hp]; exact List.mem_singleton_self p
  have hxF := atEnd x hmx inX inXP
  have hqF := atEnd q hmq inQ inQP
  exact ⟨sel, SubsetSemantics.ChainSound_of_pruned hpr ncS.nodup hrfS.smp sel hsc, hsel x hxF, hsel q hqF⟩

/-- **Every state the reader reaches is exact**, under `LivePinUp` and `EntryPin`: pinning the ends of an
entry and their parents keeps the state valid. -/
theorem tablesSound_of_entryPins (hwf : WF φ) {g₀ : GPathM} (hB : Base φ g₀) (hL : LivePinUp φ g₀)
    {S : GPathM} (hS : ReadFrom g₀ S) (hv : isValid S = true)
    (hE : ∀ x q, Rel S x q → isValid (pinOneByOne S (entryPins x q)) = true) : TablesSound S := by
  intro x n hx _ _ q _ _ hqn
  have hrfS := (facts_of_readFrom φ hB hS).1
  have adS := adj_rf hrfS hv
  have hq0 : 0 ≤ q.id.step := by assumption
  have hxq : Rel S x q := by
    refine ⟨n, hx, hqn, ?_⟩
    rename_i hq0' hq1'
    exact mem_of_hasNode' S adS (adS.ctx.gn q (adS.ctx.ownGow x n hx q hqn hq0' hq1'))
  exact realizes_of_entryPins φ hwf hB hL hS hv x q hxq (hE x q hxq)

/-- info: 'AbsSat.GraphPath.Model.PairPins.realizes_of_entryPins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms realizes_of_entryPins

/-- info: 'AbsSat.GraphPath.Model.PairPins.noBorrow_of_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noBorrow_of_plain

end AbsSat.GraphPath.Model.PairPins
