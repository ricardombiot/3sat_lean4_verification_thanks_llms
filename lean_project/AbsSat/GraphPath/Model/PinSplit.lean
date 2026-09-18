-- lean_project/AbsSat/GraphPath/Model/PinSplit.lean
import AbsSat.GraphPath.Model.PinExtends

/-!
# Splitting the local hypothesis: only steps with a choice count

`PinExtends` (v144) asks that, in every valid state the reader reaches, every step admit a pin keeping
the state valid. This module proves it for free wherever the state has **no choice left** at a step —
all its nodes there share one map node, as at the fusion steps, or at steps already decided by earlier
pins — and keeps the hypothesis only where a choice remains:

* **`pin_keeps_of_all`** (no hypothesis) — pinning the map node every node of a step already carries
  keeps a valid reader's state valid: the state's own tables are a support carrying the pin, so they
  survive it and the review.
* **`PinExtendsChoice`** — `PinExtends` restricted to steps where two live nodes carry **different** map
  nodes.
* **`pinExtends_of_choice`** — it implies `PinExtends`; so the verdict, UNSAT-completeness and "never
  unknown" hold under `PinExtendsChoice` alone (`verdict_iff_choice`, `answer_unsat_choice`,
  `answer_ne_unknown_choice`).
-/

namespace AbsSat.GraphPath.Model.PinSplit

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk AOk_filterAllAgg)
open AbsSat.GraphPath.Model.BranchRun (isValid_of_embedded)
open AbsSat.GraphPath.Model.SupportSplit (embedded_of_cover mem_of_hasNode')
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.PickInduction (gowner_of_isValid)
open AbsSat.GraphPath.Model.ReaderComplete (exists_false_of_all_false)
open AbsSat.GraphPath.Model.PinExtends

/-- **No choice, no risk.** If every node of a valid reader's state at the step of `m` carries `m`,
pinning `m` keeps the state valid (and inside it). -/
theorem pin_keeps_of_all (S : GPathM) (h : RF S) (hv : isValid S = true) (m : NodeId)
    (hall : ∀ p, Mem S p → p.id.step = m.step → p.id = m) :
    isValid (filterAllAgg S [m]) = true ∧ Embedded S (filterAllAgg S [m]) := by
  have ad := adj_rf h hv
  have hok := aggOk_rf h hv
  have sup := sup_self S ad hok h.smp
  have aok : AOk S (Mem S) (Rel S) := ⟨sup, h.smp, (RCtx_of_readableAgg S h.readable).shape.notroot⟩
  have hF := (AOk_filterAllAgg S aok [m] (fun r hr p hp hs => by
    rw [List.mem_singleton.mp hr] at hs ⊢; exact hall p hp hs)).sup
  have e := embedded_of_cover S ad _ _ _ hF (pruned_filterAllAgg S [m]).step_eq.symm (fun _ _ h => h)
  exact ⟨isValid_of_embedded e hv, e⟩

/-- **The hypothesis, only where a choice remains**: two live nodes of the step carry different map
nodes. -/
def PinExtendsChoice (g₀ : GPathM) : Prop :=
  ∀ S, ReadFrom g₀ S → isValid S = true → ∀ l, 0 ≤ l → l < S.current_step →
    (∃ a b, Mem S a ∧ Mem S b ∧ a.id.step = l ∧ b.id.step = l ∧ a.id ≠ b.id) →
    ∃ m : NodeId, m.step = l ∧ isValid (filterAllAgg S [m]) = true

/-- **Only the steps with a choice count.** -/
theorem pinExtends_of_choice {g₀ : GPathM} (h0 : RF g₀) (h : PinExtendsChoice g₀) : PinExtends g₀ := by
  intro S hS hv l hl0 hl1
  have hrf := (rf_readFrom h0 hS).1
  have ad := adj_rf hrf hv
  have nd := (RCtx_of_readableAgg S hrf.readable).nodup
  obtain ⟨q, hq, hqs⟩ := gowner_of_isValid S hv l hl0 hl1
  have hmq := mem_of_hasNode' S ad (ad.ctx.gn q hq)
  let pred : PNodeM → Bool := fun n => !(n.id.id.step == l) || n.id.id == q.id
  cases hb : S.nodes.all pred with
  | true =>
    -- no choice: every node of the step carries `q.id`
    refine ⟨q.id, hqs, (pin_keeps_of_all S hrf hv q.id (fun p hp hps => ?_)).1⟩
    obtain ⟨n, hn⟩ := hp
    have hmem := List.mem_of_find?_eq_some hn
    have hid := node?_id_eq S p n hn
    have hpn := List.all_eq_true.mp hb n hmem
    have hs : (n.id.id.step == l) = true := by rw [hid, hps, hqs]; exact beq_iff_eq.mpr rfl
    cases he : (n.id.id == q.id) with
    | true => rw [← hid]; exact eq_of_beq he
    | false =>
      have : pred n = false := by show (!(n.id.id.step == l) || n.id.id == q.id) = false; rw [hs, he]; rfl
      rw [this] at hpn; cases hpn
  | false =>
    -- a choice: a live node of the step carries another map node
    obtain ⟨n, hn, hpn⟩ := exists_false_of_all_false pred S.nodes hb
    have hmn : Mem S n.id := ⟨n, node?_of_mem nd n hn⟩
    cases hs : (n.id.id.step == l) with
    | false =>
      have : pred n = true := by show (!(n.id.id.step == l) || n.id.id == q.id) = true; rw [hs]; rfl
      rw [this] at hpn; cases hpn
    | true =>
      cases he : (n.id.id == q.id) with
      | true =>
        have : pred n = true := by show (!(n.id.id.step == l) || n.id.id == q.id) = true; rw [hs, he]; rfl
        rw [this] at hpn; cases hpn
      | false =>
        refine h S hS hv l hl0 hl1 ⟨n.id, q, hmn, hmq, eq_of_beq hs, hqs, fun heq => ?_⟩
        rw [heq] at he
        have : (q.id == q.id) = true := beq_iff_eq.mpr rfl
        rw [this] at he; cases he

-- ============================================================
-- The verdict under the split hypothesis
-- ============================================================

variable (φ : Cnf)

def RunPinExtendsChoice : Prop := ∀ kv ∈ pureRunW φ, PinExtendsChoice (filterAllAgg kv.2 [])

theorem runPinExtends_of_choice (hwf : WF φ) (h : RunPinExtendsChoice φ) : RunPinExtends φ :=
  fun kv hkv => pinExtends_of_choice (rf_final φ hwf kv hkv) (h kv hkv)

theorem verdict_iff_choice (hwf : WF φ) (h : RunPinExtendsChoice φ) :
    (∃ kv ∈ pureRunW φ, isValid (filterAllAgg kv.2 []) = true) ↔ Satisfiable φ :=
  verdict_iff_pinExtends φ hwf (runPinExtends_of_choice φ hwf h)

theorem answer_unsat_choice (hwf : WF φ) (h : RunPinExtendsChoice φ) (hns : ¬ Satisfiable φ) :
    Answer.answer φ = .unsat :=
  answer_unsat_px φ hwf (runPinExtends_of_choice φ hwf h) hns

theorem answer_ne_unknown_choice (hwf : WF φ) (h : RunPinExtendsChoice φ) : Answer.answer φ ≠ .unknown :=
  answer_ne_unknown_px φ hwf (runPinExtends_of_choice φ hwf h)

/-- info: 'AbsSat.GraphPath.Model.PinSplit.pin_keeps_of_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pin_keeps_of_all

/-- info: 'AbsSat.GraphPath.Model.PinSplit.pinExtends_of_choice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinExtends_of_choice

/-- info: 'AbsSat.GraphPath.Model.PinSplit.answer_ne_unknown_choice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown_choice

end AbsSat.GraphPath.Model.PinSplit
