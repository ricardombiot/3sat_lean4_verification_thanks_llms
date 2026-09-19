-- lean_project/AbsSat/GraphPath/Model/HereditaryValid.lean
import AbsSat.GraphPath.Model.ReaderExec

/-!
# Route C: validity is carried, not exactness

The exactness route needs every entry of a pinned union to lie on a path of one side (`SideKeep`), and the
unions do keep foreign entries (probe `topkeep`, report v163). This module carries a weaker invariant
instead:

> **`ValidWitAt m`** — whenever a state of line `m` stays valid after pinning literal values `Q`, some
> genuine partial path ends at its key and passes every pin of `Q`.

At the last line, with no pins, that is a model of the formula (`sat_of_validWit`). The invariant goes
from one line to the next with two statements about validity alone, never about entries:

* **`ValidSideAt`** — validity is not borrowed: a pinned union that stays valid has a side whose pinned
  send stays valid (probe `pinjoin`: `NO_VALID_SIDE = 0`);
* **`SendPinAt`** — a send that stays valid under pins comes from a state that stays valid under the row's
  pins and those pins.

The step between the two is `extend_son`: a genuine partial path through the row's requirements extends
by the son.
-/

namespace AbsSat.GraphPath.Model.HereditaryValid

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.ConservationPrefix (SatBelow)
open AbsSat.GraphPath.Model.BranchLines (sent)
open AbsSat.GraphPath.Model.PinHistory (branchLine branchLine_succ branchLine_inv branchLine_nil mem_restrict)
open AbsSat.GraphPath.Model.RunNoBorrow (Genuine)

variable (φ : Cnf)

-- ============================================================
-- Pieces
-- ============================================================

/-- Pins on literal values, below step `K`. -/
def LitPins (Q : List NodeId) (K : Int) : Prop := ∀ q ∈ Q, 0 ≤ q.step ∧ q.step < K ∧ q.step < litBlock φ

/-- The requirements of a map node are literal values. -/
theorem req_lit (hwf : WF φ) (d : NodeId) : ∀ r ∈ reqOfCnf φ d, 0 ≤ r.step ∧ r.step < litBlock φ := by
  intro r hr
  unfold reqOfCnf at hr
  by_cases h0 : d.step < 0
  · rw [if_pos h0] at hr; exact absurd hr List.not_mem_nil
  rw [if_neg h0] at hr
  by_cases h1 : d.step < litBlock φ
  · rw [if_pos h1] at hr
    by_cases h2 : d.step % 2 = 0
    · rw [if_pos h2] at hr; exact absurd hr List.not_mem_nil
    · rw [if_neg h2] at hr
      rcases List.mem_singleton.mp hr with rfl
      exact ⟨by show (0 : Int) ≤ d.step - 1; omega, by show d.step - 1 < litBlock φ; omega⟩
  rw [if_neg h1] at hr
  by_cases h3 : d.step ≤ litBlock φ
  · rw [if_pos h3] at hr; exact absurd hr List.not_mem_nil
  rw [if_neg h3] at hr
  by_cases h4 : fusionTop φ ≤ d.step
  · rw [if_pos h4] at hr; exact absurd hr List.not_mem_nil
  rw [if_neg h4] at hr
  cases hc : clauseAt φ d.step with
  | none => rw [hc] at hr; exact absurd hr List.not_mem_nil
  | some c =>
    rw [hc] at hr
    have hcm : c ∈ φ.clauses := by simp only [clauseAt] at hc; exact List.mem_of_getElem? hc
    obtain ⟨⟨hv1, hv2, hv3⟩, _⟩ := hwf c hcm
    have key : ∀ (l : Lit) (b : Int), l.v < φ.nVars → 0 ≤ (litReq l b).step ∧ (litReq l b).step < litBlock φ := by
      intro l b hl
      refine ⟨?_, lit_step_lt φ l hl⟩
      show 0 ≤ l.step
      simp only [Lit.step]; split <;> omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact key _ _ hv1
    · exact key _ _ hv2
    · exact key _ _ hv3

/-- **A pin at the top step of a state that stays valid is the state's key** (`topPin_key`, for a list of
pins). -/
theorem topPin_keyL (k : Int) (kv : NodeId × GPathM) (hsok : StateOkF φ k kv) (hm : MInv φ kv.2)
    (Q : List NodeId) (r : NodeId) (hrQ : r ∈ Q) (hr : r.step = k)
    (hv : isValid (filterAllAgg kv.2 Q) = true) : r = kv.1 := by
  have hRr : ReadableAgg (filterAllAgg kv.2 Q) := ⟨kv.2, Q, hm.rctx, rfl⟩
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hv
  have hpr := pruned_filterAllAgg kv.2 Q
  have hcs : (filterAllAgg kv.2 Q).current_step = k + 1 := by rw [hpr.step_eq, hsok.step]
  have htl := ParentId.TL_of_pruned hpr hm.tl
  have hk0 : 0 ≤ k := SliceInvariant.nonneg_of_mapNodes φ k kv.1 hsok.onMap
  have hv' := hv
  simp only [isValid, List.all_eq_true] at hv'
  have hent := hv' k (mem_intRange hk0 (by rw [hcs]; omega))
  obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp hent
  have hzs' : z.id.step = k := eq_of_beq hzs
  have hzid : z.id = r := ReaderAggRun.filterAllAgg_cleans kv.2 Q r hrQ z hz (by rw [hzs', hr])
  obtain ⟨n, hn, hnid⟩ := ctxR.gn z hz
  have := htl n hn (by rw [hnid, hzs', hcs]; omega)
  rw [hnid, hzid, hpr.map_parent_eq, hsok.par] at this
  exact Option.some.inj this

/-- **A genuine partial path through a son's requirements extends by the son.** -/
theorem extend_son (hwf : WF φ) (m : Nat) (hlt : (m : Int) + 1 < stepCount φ) (k p : NodeId)
    (hk : k.step = m) (hp : p ∈ mapSons φ k.step k.index) (sel : Int → PathNodeId)
    (hgen : Genuine φ ((m : Int) + 1) sel) (htop : (sel m).id = k)
    (hreq : ∀ r ∈ reqOfCnf φ p, (sel r.step).id = r) :
    Genuine φ ((m : Int) + 2) (fun j => if j = (m : Int) + 1 then ⟨p, some k⟩ else sel j) := by
  rw [hk] at hp
  obtain ⟨a, hsat, hsel⟩ := id hgen
  have hka : selOfAssign φ a m = k := by rw [← htop]; exact ((hsel m (by omega) (by omega)).1).symm
  have finish : ∀ a' : Assign, SatBelow φ a' ((m : Int) + 2) →
      (∀ j, 0 ≤ j → j ≤ (m : Int) → selOfAssign φ a' j = selOfAssign φ a j) →
      selOfAssign φ a' ((m : Int) + 1) = p →
      Genuine φ ((m : Int) + 2) (fun j => if j = (m : Int) + 1 then ⟨p, some k⟩ else sel j) := by
    intro a' hs hag hap
    refine ⟨a', hs, fun j h0 h1 => ?_⟩
    dsimp only
    by_cases hj : j = (m : Int) + 1
    · rw [if_pos hj]
      have hj0 : ¬ (j = 0) := by omega
      refine ⟨by rw [hj]; exact hap.symm, ?_⟩
      show some k = _
      rw [if_neg hj0, show j - 1 = (m : Int) by omega, hag m (by omega) (Int.le_refl _), hka]
    · rw [if_neg hj]
      obtain ⟨e1, e2⟩ := hsel j h0 (by omega)
      refine ⟨by rw [e1, hag j h0 (by omega)], ?_⟩
      rw [e2]
      by_cases hj0 : j = 0
      · rw [if_pos hj0, if_pos hj0]
      · rw [if_neg hj0, if_neg hj0, hag (j - 1) (by omega) (by omega)]
  have grow : (∀ i (hi : i < φ.clauses.length), clauseStep φ i ≠ (m : Int) + 1) →
      SatBelow φ a ((m : Int) + 2) := by
    intro hno i hi hs
    exact hsat i hi (by have := hno i hi; omega)
  have hlb : litBlock φ = 2 * (φ.nVars : Int) := rfl
  have hft : fusionTop φ = 2 * (φ.nVars : Int) + 1 + (φ.clauses.length : Int) := rfl
  have hsc : stepCount φ = 2 * (φ.nVars : Int) + (φ.clauses.length : Int) + 2 := rfl
  have hcs : ∀ i, clauseStep φ i = 2 * (φ.nVars : Int) + 1 + (i : Int) := fun _ => rfl
  by_cases hcl : litBlock φ < (m : Int) + 1 ∧ (m : Int) + 1 < fusionTop φ
  · -- a clause row
    have hd : p ∈ mapNodes φ ((m : Int) + 1) := by
      rw [mapSons_other φ m k.index (by omega) (by omega)] at hp; exact hp
    have hps : p.step = (m : Int) + 1 := mapNodes_step φ _ p hd
    have hne : reqOfCnf φ p ≠ [] := by
      have hj : ((m : Int) + 1 - litBlock φ - 1).toNat < φ.clauses.length := by omega
      have hjs : p.step = clauseStep φ ((m : Int) + 1 - litBlock φ - 1).toNat := by rw [hcs]; omega
      rw [reqOfCnf_clause φ p _ φ.clauses[((m : Int) + 1 - litBlock φ - 1).toNat] hj
        (List.getElem?_eq_getElem hj) hjs]
      simp
    exact ClauseReview.extend_genuine φ hwf m k p hd hcl.1 hne sel hgen htop hreq
  · by_cases hvar : (m : Int) + 1 < litBlock φ
    · by_cases hev : ((m : Int) + 1) % 2 = 0
      · -- a new variable: its value is the son's
        have hd : p ∈ mapNodes φ ((m : Int) + 1) := by
          rw [mapSons_other φ m k.index (by omega) (by omega)] at hp; exact hp
        rw [mapNodes_var φ _ (by omega) hvar] at hd
        obtain ⟨u, hu, hmu⟩ : ∃ u : Nat, u < φ.nVars ∧ (m : Int) + 1 = varStep u :=
          ⟨(((m : Int) + 1) / 2).toNat, by omega, by simp only [varStep]; omega⟩
        refine finish (fun w => if w = u then decide (p.index = 1) else a w) ?_ ?_ ?_
        · intro i hi hs; rw [hcs] at hs; exfalso; omega
        · intro j h0 h1
          have hju : (j / 2).toNat ≠ u := by simp only [varStep] at hmu; omega
          exact PinVar.sel_local φ _ a j h0 (by omega) (by rw [if_neg hju])
        · rw [hmu, selOfAssign_var φ _ _ hu]
          rw [hmu] at hd
          rcases List.mem_cons.mp hd with rfl | hd'
          · show (⟨varStep u, bit (if u = u then decide ((0 : Int) = 1) else a u)⟩ : NodeId) = _
            rw [if_pos rfl]; rfl
          · rcases List.mem_singleton.mp hd' with rfl
            show (⟨varStep u, bit (if u = u then decide ((1 : Int) = 1) else a u)⟩ : NodeId) = _
            rw [if_pos rfl]; rfl
      · -- the negation of the variable of `k`: forced
        obtain ⟨v, hv, hmv⟩ : ∃ v : Nat, v < φ.nVars ∧ (m : Int) = varStep v :=
          ⟨((m : Int) / 2).toNat, by omega, by simp only [varStep]; omega⟩
        rw [hmv, mapSons_var φ _ hv] at hp
        rcases List.mem_singleton.mp hp with rfl
        refine finish a (grow (fun i hi => by rw [hcs]; omega)) (fun _ _ _ => rfl) ?_
        have hka' := hka
        rw [hmv, selOfAssign_var φ a _ hv] at hka'
        have hneg : varStep v + 1 = negStep v := by simp only [varStep, negStep]
        rw [hmv, hneg, selOfAssign_neg φ a _ hv, bit_not, ← hka']
    · -- the two fusion steps: forced
      have hd : p ∈ mapNodes φ ((m : Int) + 1) := by
        rw [mapSons_other φ m k.index (by omega) (by omega)] at hp; exact hp
      by_cases hL : (m : Int) + 1 = litBlock φ
      · rw [mapNodes_fusion1 φ _ hL] at hd
        rcases List.mem_singleton.mp hd with rfl
        refine finish a (grow (fun i hi => by rw [hcs]; omega)) (fun _ _ _ => rfl) ?_
        have h0' : ¬ ((m : Int) + 1 < 0) := by omega
        have h1' : ¬ ((m : Int) + 1 < litBlock φ) := by omega
        have h2' : (m : Int) + 1 ≤ litBlock φ := by omega
        simp only [selOfAssign, if_neg h0', if_neg h1', if_pos h2']
      · have hcl' : ¬ (litBlock φ < (m : Int) + 1) ∨ ¬ ((m : Int) + 1 < fusionTop φ) := by
          by_cases h : litBlock φ < (m : Int) + 1
          · exact Or.inr (fun h2 => hcl ⟨h, h2⟩)
          · exact Or.inl h
        have hT : fusionTop φ ≤ (m : Int) + 1 := by omega
        rw [mapNodes_fusionTop φ _ hT hlt] at hd
        rcases List.mem_singleton.mp hd with rfl
        refine finish a (grow (fun i hi => by rw [hcs]; omega)) (fun _ _ _ => rfl) ?_
        have h0' : ¬ ((m : Int) + 1 < 0) := by omega
        have h1' : ¬ ((m : Int) + 1 < litBlock φ) := by omega
        have h2' : ¬ ((m : Int) + 1 ≤ litBlock φ) := by omega
        simp only [selOfAssign, if_neg h0', if_neg h1', if_neg h2', if_pos hT]

-- ============================================================
-- The invariant and its two hypotheses
-- ============================================================

/-- **Hereditary validity, at line `m`**: a state of the run that stays valid under literal pins has a
genuine partial path to its key through the pins. -/
def ValidWitAt (m : Nat) : Prop :=
  ∀ kv ∈ branchLine φ [] m, ∀ Q, LitPins φ Q ((m : Int) + 1) → isValid (filterAllAgg kv.2 Q) = true →
    ∃ sel, Genuine φ ((m : Int) + 1) sel ∧ (sel m).id = kv.1 ∧ ∀ q ∈ Q, (sel q.step).id = q

/-- **Validity is not borrowed, at line `m`.** A pinned union that stays valid has a side whose pinned send
stays valid. -/
def ValidSideAt (m : Nat) : Prop :=
  ∀ p J, (p, J) ∈ pureAdvanceW φ (branchLine φ [] m) → ∀ Q, LitPins φ Q ((m : Int) + 2) →
    isValid (filterAllAgg J Q) = true →
    ∃ kv ∈ branchLine φ [] m, p ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 p) = true ∧
      isValid (filterAllAgg (sent φ kv.2 p) Q) = true

/-- **Pins commute with the send, for validity, at line `m`.** A send that stays valid under pins comes
from a state that stays valid under the son's requirements and those pins (below the send's top). -/
def SendPinAt (m : Nat) : Prop :=
  ∀ kv ∈ branchLine φ [] m, ∀ p ∈ mapSons φ kv.1.step kv.1.index, isValid (sent φ kv.2 p) = true →
    ∀ Q, LitPins φ Q ((m : Int) + 2) → isValid (filterAllAgg (sent φ kv.2 p) Q) = true →
      isValid (filterAllAgg kv.2 ((reqOfCnf φ p ++ Q).filter (fun q => decide (q.step < (m : Int) + 1))))
        = true

-- ============================================================
-- The induction
-- ============================================================

theorem validWit_zero (hwf : WF φ) : ValidWitAt φ 0 := by
  intro kv hkv Q hQ hv
  have hl := branchLine_inv φ hwf [] 0
  have hsok : StateOkF φ 0 kv := hl.1.2 kv hkv
  have hm : MInv φ kv.2 := hl.2 kv hkv
  have hd : kv.1 ∈ mapNodes φ 0 := hsok.onMap
  have hsel : ∃ a : Assign, selOfAssign φ a 0 = kv.1 := by
    by_cases h0 : (0 : Int) < litBlock φ
    · rw [mapNodes_var φ 0 (Int.le_refl 0) h0] at hd
      have hv : (0 : Nat) < φ.nVars := by
        have : litBlock φ = 2 * (φ.nVars : Int) := rfl
        omega
      have e : (0 : Int) = varStep 0 := rfl
      rcases List.mem_cons.mp hd with h | h
      · exact ⟨fun _ => false, by rw [e, selOfAssign_var φ _ 0 hv, h]; rfl⟩
      · rcases List.mem_singleton.mp h with h
        exact ⟨fun _ => true, by rw [e, selOfAssign_var φ _ 0 hv, h]; rfl⟩
    · have hL : (0 : Int) = litBlock φ := by
        have : litBlock φ = 2 * (φ.nVars : Int) := rfl
        omega
      rw [mapNodes_fusion1 φ 0 hL] at hd
      rcases List.mem_singleton.mp hd with h
      refine ⟨fun _ => false, ?_⟩
      have h1' : ¬ ((0 : Int) < litBlock φ) := h0
      have h2' : (0 : Int) ≤ litBlock φ := by omega
      simp only [selOfAssign, if_neg (show ¬ ((0 : Int) < 0) by omega), if_neg h1', if_pos h2', h]
  obtain ⟨a, ha⟩ := hsel
  refine ⟨fun _ => ⟨kv.1, none⟩, ⟨a, fun i hi hs => ?_, fun k h0 h1 => ?_⟩, rfl, fun q hq => ?_⟩
  · have : clauseStep φ i = 2 * (φ.nVars : Int) + 1 + (i : Int) := rfl
    exfalso; omega
  · have hk : k = 0 := by omega
    subst hk
    exact ⟨ha.symm, by rw [if_pos rfl]⟩
  · obtain ⟨hq0, hq1, _⟩ := hQ q hq
    exact (topPin_keyL φ 0 kv hsok hm Q q hq (by omega) hv).symm

theorem validWit_succ (hwf : WF φ) (m : Nat) (hW : ValidWitAt φ m) (hVS : ValidSideAt φ m)
    (hSP : SendPinAt φ m) : ValidWitAt φ (m + 1) := by
  intro kv' hkv' Q hQ hvJ
  obtain ⟨p, J⟩ := kv'
  rw [branchLine_succ] at hkv'
  have hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ [] m) := (mem_restrict hkv').1
  have hl := branchLine_inv φ hwf [] m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hQ2 : LitPins φ Q ((m : Int) + 2) := fun q hq => by
    obtain ⟨a, b, c⟩ := hQ q hq; exact ⟨a, by push_cast at b; omega, c⟩
  obtain ⟨kv, hkv, hson, hvS, hvY⟩ := hVS p J hJ Q hQ2 hvJ
  have hv' := hSP kv hkv p hson hvS Q hQ2 hvY
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hk : kv.1.step = m := mapNodes_step φ _ kv.1 hsok.onMap
  have hps : p.step = (m : Int) + 1 := mapNodes_step φ _ p hsJ.onMap
  have hlt : (m : Int) + 1 < stepCount φ := PinVar.lt_of_mapNodes φ _ p hsJ.onMap
  have hQ' : LitPins φ ((reqOfCnf φ p ++ Q).filter (fun q => decide (q.step < (m : Int) + 1)))
      ((m : Int) + 1) := by
    intro q hq
    obtain ⟨hq, hqs⟩ := List.mem_filter.mp hq
    have hqs' : q.step < (m : Int) + 1 := of_decide_eq_true hqs
    rcases List.mem_append.mp hq with hr | hr
    · exact ⟨(req_lit φ hwf p q hr).1, hqs', (req_lit φ hwf p q hr).2⟩
    · exact ⟨(hQ q hr).1, hqs', (hQ q hr).2.2⟩
  obtain ⟨sel, hgen, htop, hpass⟩ := hW kv hkv _ hQ' hv'
  have inQ' : ∀ q, q ∈ reqOfCnf φ p ++ Q → q.step < (m : Int) + 1 →
      q ∈ (reqOfCnf φ p ++ Q).filter (fun q => decide (q.step < (m : Int) + 1)) :=
    fun q hq hs => List.mem_filter.mpr ⟨hq, decide_eq_true hs⟩
  have hreq : ∀ r ∈ reqOfCnf φ p, (sel r.step).id = r := by
    intro r hr
    have hb := reqOfCnf_backward φ hwf p r hr
    exact hpass r (inQ' r (List.mem_append_left _ hr) (by omega))
  have hext := extend_son φ hwf m hlt kv.1 p hk hson sel hgen htop hreq
  refine ⟨_, by push_cast; exact hext, ?_, fun q hq => ?_⟩
  · show (if ((m + 1 : Nat) : Int) = (m : Int) + 1 then (⟨p, some kv.1⟩ : PathNodeId)
      else sel ((m + 1 : Nat) : Int)).id = p
    rw [if_pos (by push_cast; rfl)]
  by_cases hqs : q.step < (m : Int) + 1
  · have hne : q.step ≠ (m : Int) + 1 := by omega
    simp only [if_neg hne]
    exact hpass q (inQ' q (List.mem_append_right _ hq) hqs)
  · have hqe : q.step = (m : Int) + 1 := by have := (hQ q hq).2.1; push_cast at this; omega
    have hqp : q = p := topPin_keyL φ ((m : Int) + 1) (p, J) hsJ hmJ Q q hq hqe hvJ
    subst hqp
    show (if q.step = (m : Int) + 1 then (⟨q, some kv.1⟩ : PathNodeId) else sel q.step).id = q
    rw [if_pos hqe]

theorem validWit_all (hwf : WF φ) (hVS : ∀ m, ValidSideAt φ m) (hSP : ∀ m, SendPinAt φ m) :
    ∀ m, ValidWitAt φ m := by
  intro m
  induction m with
  | zero => exact validWit_zero φ hwf
  | succ m ih => exact validWit_succ φ hwf m ih (hVS m) (hSP m)

/-- **The verdict from hereditary validity.** If validity is never borrowed at a union and pins commute
with the send for validity, a state of the final line that one review leaves valid means a model. No
exactness anywhere: the tables may keep foreign entries. -/
theorem sat_of_validSide (hwf : WF φ) (hVS : ∀ m, ValidSideAt φ m) (hSP : ∀ m, SendPinAt φ m)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ := by
  have hpos := ConservationCore.stepCount_pos φ
  have hkv' : kv ∈ branchLine φ [] (stepCount φ - 1).toNat := by
    rw [branchLine_nil]; exact hkv
  obtain ⟨sel, ⟨a, hsat, _⟩, _, _⟩ := validWit_all φ hwf hVS hSP _ kv hkv' [] (fun q hq => absurd hq List.not_mem_nil) hv
  refine ⟨a, fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  exact hsat i hi (by
    have : clauseStep φ i = 2 * (φ.nVars : Int) + 1 + (i : Int) := rfl
    have : stepCount φ = 2 * (φ.nVars : Int) + (φ.clauses.length : Int) + 2 := rfl
    omega)

/-- info: 'AbsSat.GraphPath.Model.HereditaryValid.sat_of_validSide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_validSide

end AbsSat.GraphPath.Model.HereditaryValid
