-- lean_project/AbsSat/GraphPath/Model/UnitPropReview.lean
import AbsSat.GraphPath.Model.FixAgreeInv
import AbsSat.GraphPath.Model.MapReachable
import AbsSat.Cnf.UnitProp

/-!
# The review is at least as strong as unit propagation

At a send of a state `g` built by the driver (`MapReachable`), take as clauses those already processed
(`processed φ g`: the clause steps below the current step) and as units the literals the destination
pins (`pinLits φ d`). Then:

* `forced_unsupported` — **every node of the pinned state that fixes a value contradicting a literal
  unit propagation derives is in the removal closure**. By induction on `Forced`: a pin's
  contradiction has no global owner at the pin's step (`Agree`); a literal propagated by a clause is
  contradicted only by nodes whose owners at the clause's step are rows making that literal false,
  hence rows making some other literal true, which the induction kills (`FixAgree`).
* `conflict_invalid` — **if unit propagation reaches a conflict, the filter leaves the state
  invalid**: every node dies at the value step of the conflicting variable.

This holds for every formula; nothing here uses Horn clauses.
-/

namespace AbsSat.GraphPath.Model.UnitPropReview

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.IdSeparator
open AbsSat.GraphPath.Model.ParentOwners
open AbsSat.GraphPath.Model.LitOwners
open AbsSat.GraphPath.Model.FixAgreeInv
open AbsSat.GraphPath.Model.MapReachable

variable (φ : Cnf)

-- ============================================================
-- Clauses, units and literals
-- ============================================================

/-- The literal of a `(variable, value)` pair. -/
def vvLit (p : Int × Int) : Lit := { v := p.1.toNat, pos := decide (p.2 = 1) }

theorem vvLit_vv (p : Int × Int) (h0 : 0 ≤ p.1) (hb : p.2 = 0 ∨ p.2 = 1) : (vvLit p).vv = p := by
  obtain ⟨v, b⟩ := p
  have h0' : 0 ≤ v := h0
  refine Prod.ext ?_ ?_
  · show ((v.toNat : Nat) : Int) = v
    omega
  · have hb' : b = 0 ∨ b = 1 := hb
    rcases hb' with rfl | rfl <;> rfl

theorem Lit.vv_snd (l : Lit) : l.vv.2 = 0 ∨ l.vv.2 = 1 := by
  cases l with
  | mk v pos => cases pos <;> simp [Lit.vv]

/-- The clauses whose step is already behind `g`. -/
def processed (g : GPathM) : List Clause :=
  (List.range φ.clauses.length).filterMap
    (fun j => if clauseStep φ j < g.current_step then φ.clauses[j]? else none)

theorem mem_processed {g : GPathM} {c : Clause} (h : c ∈ processed φ g) :
    ∃ j, φ.clauses[j]? = some c ∧ clauseStep φ j < g.current_step := by
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
  split at hj
  · next hlt => exact ⟨j, hj, hlt⟩
  · cases hj

/-- The literals the destination pins. -/
def pinLits (d : NodeId) : List Lit :=
  (reqOfCnf φ d).filterMap (fun r => (varVal φ r).map vvLit)

theorem mem_pinLits {d : NodeId} {l : Lit} (h : l ∈ pinLits φ d) :
    ∃ r ∈ reqOfCnf φ d, ∃ p, varVal φ r = some p ∧ l = vvLit p := by
  obtain ⟨r, hr, hm⟩ := List.mem_filterMap.mp h
  cases hv : varVal φ r with
  | none =>
    rw [hv] at hm
    cases hm
  | some p =>
    rw [hv] at hm
    simp only [Option.map_some] at hm
    exact ⟨r, hr, p, hv, (Option.some.inj hm).symm⟩

-- ============================================================
-- The map
-- ============================================================

/-- A requirement of a map node has index `0` or `1`. -/
theorem pin_index01 {d r : NodeId} (hdm : d ∈ mapNodes φ d.step) (hr : r ∈ reqOfCnf φ d) :
    r.index = 0 ∨ r.index = 1 := by
  rcases step_cases φ d.step with h | ⟨v, hv, h⟩ | ⟨v, hv, h⟩ | h | ⟨j, hj, h⟩ | h
  · rw [reqOfCnf_below φ d h] at hr
    exact absurd hr List.not_mem_nil
  · rw [reqOfCnf_var φ d v hv h] at hr
    exact absurd hr List.not_mem_nil
  · rw [AbsSat.GraphMap.CnfMap.reqOfCnf_neg φ d v hv h] at hr
    have hrr := List.mem_singleton.mp hr
    have hlt : d.step < litBlock φ := by rw [h]; simp only [negStep, litBlock]; omega
    have h0 : 0 ≤ d.step := by rw [h]; simp only [negStep]; omega
    rw [mapNodes_var φ d.step h0 hlt] at hdm
    have hd01 : d.index = 0 ∨ d.index = 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdm
      rcases hdm with e | e <;> rw [e] <;> simp
    rw [hrr]
    show 1 - d.index = 0 ∨ 1 - d.index = 1
    omega
  · rw [reqOfCnf_fusion1 φ d h] at hr
    exact absurd hr List.not_mem_nil
  · obtain ⟨c, hc⟩ : ∃ c, φ.clauses[j]? = some c := ⟨φ.clauses[j], List.getElem?_eq_getElem hj⟩
    rw [reqOfCnf_clause φ d j c hj hc h] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [litReq, b1, b2, b3] <;> omega
  · rw [reqOfCnf_above φ d h] at hr
    exact absurd hr List.not_mem_nil

theorem varVal_01 {r : NodeId} (hr01 : r.index = 0 ∨ r.index = 1) {v b : Int}
    (h : varVal φ r = some (v, b)) : 0 ≤ v ∧ (b = 0 ∨ b = 1) := by
  obtain ⟨h0, _, hcase⟩ := IdDiesProof.varVal_spec φ r v b h
  -- `omega` on a disjunctive goal pulls in `Classical.choice`; split the disjunction by hand.
  rcases hcase with ⟨hs, hi⟩ | ⟨hs, hi⟩
  · rw [← hi]
    exact ⟨by omega, hr01⟩
  · refine ⟨by omega, ?_⟩
    rcases hr01 with e | e
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- A literal requirement of a clause row fixes the literal true (bit `1`) or false (bit `0`). -/
theorem varVal_litReq (l : Lit) (hl : l.v < φ.nVars) (b : Int) (hb : b = 0 ∨ b = 1) :
    varVal φ (litReq l b) = some (if b = 1 then l.vv else l.neg.vv) := by
  have hlt := lit_step_lt φ l hl
  cases l with
  | mk v pos =>
    cases pos with
    | true =>
      have hstep : (litReq ⟨v, true⟩ b).step = 2 * (v : Int) := by simp [litReq, Lit.step]
      have hlt' : 2 * (v : Int) < litBlock φ := by simpa [Lit.step] using hlt
      rw [IdDiesProof.varVal_even φ _ (by rw [hstep]; omega) (by rw [hstep]; exact hlt')
        (by rw [hstep]; omega), hstep]
      rcases hb with rfl | rfl
      · show some (2 * (v : Int) / 2, (0 : Int)) = some ((v : Int), (0 : Int))
        rw [show 2 * (v : Int) / 2 = v by omega]
      · show some (2 * (v : Int) / 2, (1 : Int)) = some ((v : Int), (1 : Int))
        rw [show 2 * (v : Int) / 2 = v by omega]
    | false =>
      have hstep : (litReq ⟨v, false⟩ b).step = 2 * (v : Int) + 1 := by simp [litReq, Lit.step]
      have hlt' : 2 * (v : Int) + 1 < litBlock φ := by simpa [Lit.step] using hlt
      have hreq := IdDiesProof.reqOfCnf_neg φ (litReq ⟨v, false⟩ b) (by rw [hstep]; omega)
        (by rw [hstep]; exact hlt') (by rw [hstep]; omega)
      unfold varVal
      rw [if_neg (by rw [hstep]; omega), if_neg (by rw [hstep]; omega), hreq]
      have hcond : ((litReq ⟨v, false⟩ b).step - 1) % 2 = 0 := by rw [hstep]; omega
      simp only [hcond, ↓reduceIte]
      rw [hstep, show (2 * (v : Int) + 1 - 1) / 2 = v by omega]
      rcases hb with rfl | rfl
      · rfl
      · rfl

/-- A node at a clause step fixes, for each literal of the clause, the value its row gives it. -/
theorem row_fix {q : PathNodeId} {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c)
    (hjlt : j < φ.clauses.length)
    (hwfc : c.l1.v < φ.nVars ∧ c.l2.v < φ.nVars ∧ c.l3.v < φ.nVars)
    (hs : q.id.step = clauseStep φ j) :
    (if b1 q.id.index = 1 then c.l1.vv else c.l1.neg.vv) ∈ fixes φ q ∧
    (if b2 q.id.index = 1 then c.l2.vv else c.l2.neg.vv) ∈ fixes φ q ∧
    (if b3 q.id.index = 1 then c.l3.vv else c.l3.neg.vv) ∈ fixes φ q := by
  have hreq := reqOfCnf_clause φ q.id j c hjlt hj hs
  have hfm : fixesMap φ q.id = (reqOfCnf φ q.id).filterMap (varVal φ) := by
    unfold fixesMap
    rw [if_neg (by rw [hs]; simp only [clauseStep, litBlock]; omega),
      if_neg (by rw [hs]; simp only [clauseStep, litBlock]; omega)]
  have hmem : ∀ (l : Lit) (b : Int), litReq l b ∈ reqOfCnf φ q.id → l.v < φ.nVars →
      (b = 0 ∨ b = 1) → (if b = 1 then l.vv else l.neg.vv) ∈ fixes φ q := by
    intro l b hlr hlv hb
    unfold fixes
    apply List.mem_append_left
    rw [hfm]
    exact List.mem_filterMap.mpr ⟨litReq l b, hlr, varVal_litReq φ l hlv b hb⟩
  refine ⟨hmem _ _ (by rw [hreq]; simp) hwfc.1 (by simp only [b1]; omega),
    hmem _ _ (by rw [hreq]; simp) hwfc.2.1 (by simp only [b2]; omega),
    hmem _ _ (by rw [hreq]; simp) hwfc.2.2 (by simp only [b3]; omega)⟩

-- ============================================================
-- Unit propagation inside the removal closure
-- ============================================================

/-- **Every node contradicting a literal unit propagation derives is in the removal closure.** -/
theorem forced_unsupported (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g) (d : NodeId)
    (hd : d.step = g.current_step) (hdm : d ∈ mapNodes φ d.step) {l : Lit}
    (hl : Forced (processed φ g) (pinLits φ d) l) :
    ∀ (x : PathNodeId) (n : PNodeM), ((reqOfCnf φ d).foldl filterRequire g).node? x = some n →
      l.neg.vv ∈ fixes φ x → Unsupported ((reqOfCnf φ d).foldl filterRequire g) x := by
  have hr := reachable_of_mapReachable φ hwf g hmr
  have hback : ∀ x, ∀ r ∈ reqOfCnf φ x, r.step < x.step :=
    fun x r h => reqOfCnf_backward φ hwf x r h
  have hnonneg : ∀ x, ∀ r ∈ reqOfCnf φ x, 0 ≤ r.step :=
    fun x r h => UnitPropagation.reqOfCnf_nonneg φ x r h
  have hdist : ∀ x, ∀ r₁ ∈ reqOfCnf φ x, ∀ r₂ ∈ reqOfCnf φ x, r₁.step = r₂.step → r₁ = r₂ :=
    fun x r₁ h₁ r₂ h₂ hs => reqOfCnf_functional φ hwf x r₁ h₁ r₂ h₂ hs
  have hoos := SelfOwn.OOS_reachable (reqOfCnf φ) g hr
  have hoc := UnitPropagation.OwnedCompatible_reachable (reqOfCnf φ) hback hnonneg g hr
  have hrf := L1 (reqOfCnf φ) hr
  have hpi := ParentInv_reachable (reqOfCnf φ) hback g hr
  have hli := LitInv_reachable (reqOfCnf φ) hback hnonneg hdist g hr
  have hgn := GownersNodes.GN_reachable (reqOfCnf φ) g hr
  have hnd := Reader.NodupIds_reachable (reqOfCnf φ) g hr
  have hfa := FixAgree_reachable φ hwf g hr
  have hnom := nodesOnMap_of_mapReachable φ g hmr
  have hnodeP : ∀ x n, ((reqOfCnf φ d).foldl filterRequire g).node? x = some n →
      g.node? x = some n := by
    intro x n h
    have heq : ((reqOfCnf φ d).foldl filterRequire g).node? x = g.node? x := by
      show ((reqOfCnf φ d).foldl filterRequire g).nodes.find? (fun y => y.id == x) =
        g.nodes.find? (fun y => y.id == x)
      rw [foldl_filterRequire_nodes]
    rw [← heq]
    exact h
  have hnodeG : ∀ m ∈ g.nodes, ((reqOfCnf φ d).foldl filterRequire g).node? m.id = some m := by
    intro m hm
    show ((reqOfCnf φ d).foldl filterRequire g).nodes.find? (fun y => y.id == m.id) = some m
    rw [foldl_filterRequire_nodes]
    exact node?_of_mem hnd m hm
  induction hl with
  | unit l hl =>
    intro x n hn hfx
    obtain ⟨r, hrr, p, hvr, rfl⟩ := mem_pinLits φ hl
    obtain ⟨v, b⟩ := p
    have h01 := varVal_01 φ (pin_index01 φ hdm hrr) hvr
    have hlv : (vvLit (v, b)).vv = (v, b) := vvLit_vv (v, b) h01.1 h01.2
    rw [Lit.vv_neg, hlv] at hfx
    have hng := hnodeP x n hn
    have hnmem : n ∈ g.nodes := List.mem_of_find?_eq_some hng
    have hnid : n.id = x := node?_id_eq g x n hng
    have hag := IdDiesProof.agree_of_fixes φ hoos hoc hrf hpi hli hnmem (by rw [hnid]; exact hfx)
    obtain ⟨h0, _, hcase⟩ := IdDiesProof.varVal_spec φ r v b hvr
    have hrlt : r.step < ((reqOfCnf φ d).foldl filterRequire g).current_step := by
      rw [foldl_filterRequire_step]
      have := hback d r hrr
      omega
    refine Unsupported.noSupport x n hn r.step h0 hrlt (fun w hw hwg => ?_)
    exfalso
    obtain ⟨hwo, hws⟩ := List.mem_filter.mp hw
    have hws' : w.id.step = r.step := beq_iff_eq.mp hws
    have hwr : w.id = r := FabricAdd.gowners_foldl_compat (reqOfCnf φ d) g w hwg r hrr hws'
    rcases hcase with ⟨hs, hi⟩ | ⟨hs, hi⟩
    · have hidx := hag.1 w hwo (by rw [hwr, hs])
      rw [hwr, hi] at hidx
      have : b = 1 - b := hidx
      omega
    · have hidx := hag.2 w hwo (by rw [hwr, hs])
      rw [hwr, hi] at hidx
      have : 1 - b = 1 - (1 - b) := hidx
      omega
  | prop c hc l hl _ ih =>
    intro x n hn hfx
    obtain ⟨j, hj, hjs⟩ := mem_processed φ hc
    obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hj
    have hcwf := (hwf c (List.mem_of_getElem? hj)).1
    have hng := hnodeP x n hn
    have hnmem : n ∈ g.nodes := List.mem_of_find?_eq_some hng
    have hnid : n.id = x := node?_id_eq g x n hng
    refine Unsupported.noSupport x n hn (clauseStep φ j) (by simp only [clauseStep]; omega)
      (by rw [foldl_filterRequire_step]; exact hjs) (fun q hq hqg => ?_)
    obtain ⟨hqo, hqs⟩ := List.mem_filter.mp hq
    have hqs' : q.id.step = clauseStep φ j := beq_iff_eq.mp hqs
    obtain ⟨m, hm, hmid⟩ := hgn q (FabricAdd.gowners_foldl_sub (reqOfCnf φ d) g q hqg)
    have hmP : ((reqOfCnf φ d).foldl filterRequire g).node? q = some m := by
      rw [← hmid]
      exact hnodeG m hm
    have hrange := index_range_of_clauseNode φ j hjlt q.id (by
      have hon := hnom m hm
      rw [hmid, hqs'] at hon
      exact hon)
    obtain ⟨hr1, hr2, hr3⟩ := row_fix φ hj hjlt hcwf hqs'
    have hcons := hfa n hnmem q hqo
    rw [hnid] at hcons
    have hzero : ∀ (lk : Lit) (bk : Int), (bk = 0 ∨ bk = 1) →
        (if bk = 1 then lk.vv else lk.neg.vv) ∈ fixes φ q → lk = l → bk = 0 := by
      intro lk bk hb hmemq heq
      rw [heq] at hmemq
      rcases hb with hb | hb
      · exact hb
      · exfalso
        rw [if_pos hb] at hmemq
        have hv := hcons _ hfx _ hmemq (by rw [Lit.vv_neg])
        rw [Lit.vv_neg] at hv
        have h01 := Lit.vv_snd l
        have hv' : 1 - l.vv.2 = l.vv.2 := hv
        omega
    have hb1 : b1 q.id.index = 0 ∨ b1 q.id.index = 1 := by simp only [b1]; omega
    have hb2 : b2 q.id.index = 0 ∨ b2 q.id.index = 1 := by simp only [b2]; omega
    have hb3 : b3 q.id.index = 0 ∨ b3 q.id.index = 1 := by simp only [b3]; omega
    rcases bits_not_all_zero q.id.index hrange.1 hrange.2 with h1 | h2 | h3
    · have hne : c.l1 ≠ l := fun e => by have := hzero c.l1 _ hb1 hr1 e; omega
      rw [if_pos h1] at hr1
      exact ih c.l1 (by simp [Clause.lits]) hne q m hmP (by rw [Lit.neg_neg]; exact hr1)
    · have hne : c.l2 ≠ l := fun e => by have := hzero c.l2 _ hb2 hr2 e; omega
      rw [if_pos h2] at hr2
      exact ih c.l2 (by simp [Clause.lits]) hne q m hmP (by rw [Lit.neg_neg]; exact hr2)
    · have hne : c.l3 ≠ l := fun e => by have := hzero c.l3 _ hb3 hr3 e; omega
      rw [if_pos h3] at hr3
      exact ih c.l3 (by simp [Clause.lits]) hne q m hmP (by rw [Lit.neg_neg]; exact hr3)

/-- A derived literal names a variable of the formula whose value step is already behind. -/
theorem forced_var_bound (hwf : WF φ) (g : GPathM) (d : NodeId) (hd : d.step = g.current_step)
    {l : Lit} (hl : Forced (processed φ g) (pinLits φ d) l) :
    l.v < φ.nVars ∧ 2 * (l.v : Int) < g.current_step := by
  induction hl with
  | unit l hl =>
    obtain ⟨r, hrr, p, hvr, rfl⟩ := mem_pinLits φ hl
    obtain ⟨v, b⟩ := p
    obtain ⟨h0, hlt, hcase⟩ := IdDiesProof.varVal_spec φ r v b hvr
    have hbk := reqOfCnf_backward φ hwf d r hrr
    show v.toNat < φ.nVars ∧ 2 * ((v.toNat : Nat) : Int) < g.current_step
    simp only [litBlock] at hlt
    rcases hcase with ⟨hs, _⟩ | ⟨hs, _⟩ <;> constructor <;> omega
  | prop c hc l hl _ _ =>
    obtain ⟨j, hj, hjs⟩ := mem_processed φ hc
    obtain ⟨hv1, hv2, hv3⟩ := (hwf c (List.mem_of_getElem? hj)).1
    simp only [Clause.lits, List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [clauseStep] at hjs
    rcases hl with rfl | rfl | rfl <;> constructor <;> omega

/-- **If unit propagation reaches a conflict, the filter leaves the state invalid.** -/
theorem conflict_invalid (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g) (d : NodeId)
    (hd : d.step = g.current_step) (hdm : d ∈ mapNodes φ d.step)
    (hc : Conflict (processed φ g) (pinLits φ d)) :
    isValid (filterAll g (reqOfCnf φ d)) = false := by
  obtain ⟨l, h1, h2⟩ := hc
  have hr := reachable_of_mapReachable φ hwf g hmr
  obtain ⟨hvn, hvs⟩ := forced_var_bound φ hwf g d hd h1
  have hnom := nodesOnMap_of_mapReachable φ g hmr
  have hgn := GownersNodes.GN_reachable (reqOfCnf φ) g hr
  have hnd := Reader.NodupIds_reachable (reqOfCnf φ) g hr
  have hnodeG : ∀ m ∈ g.nodes, ((reqOfCnf φ d).foldl filterRequire g).node? m.id = some m := by
    intro m hm
    show ((reqOfCnf φ d).foldl filterRequire g).nodes.find? (fun y => y.id == m.id) = some m
    rw [foldl_filterRequire_nodes]
    exact node?_of_mem hnd m hm
  -- every node of the pinned state is unsupported at the variable's value step
  have hall : ∀ x n, ((reqOfCnf φ d).foldl filterRequire g).node? x = some n →
      Unsupported ((reqOfCnf φ d).foldl filterRequire g) x := by
    intro x n hn
    refine Unsupported.noSupport x n hn (2 * (l.v : Int)) (by omega)
      (by rw [foldl_filterRequire_step]; exact hvs) (fun q hq hqg => ?_)
    obtain ⟨_, hqs⟩ := List.mem_filter.mp hq
    have hqs' : q.id.step = 2 * (l.v : Int) := beq_iff_eq.mp hqs
    obtain ⟨m, hm, hmid⟩ := hgn q (FabricAdd.gowners_foldl_sub (reqOfCnf φ d) g q hqg)
    have hmP : ((reqOfCnf φ d).foldl filterRequire g).node? q = some m := by
      rw [← hmid]
      exact hnodeG m hm
    have hlb : q.id.step < litBlock φ := by rw [hqs']; simp only [litBlock]; omega
    have hon : q.id ∈ mapNodes φ q.id.step := by
      have := hnom m hm
      rw [hmid] at this
      exact this
    rw [mapNodes_var φ q.id.step (by omega) hlb] at hon
    have hidx01 : q.id.index = 0 ∨ q.id.index = 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
      rcases hon with e | e <;> rw [e] <;> simp
    have hfix : ((l.v : Int), q.id.index) ∈ fixes φ q := by
      unfold fixes
      apply List.mem_append_left
      unfold fixesMap
      rw [if_pos hlb, IdDiesProof.varVal_even φ q.id (by omega) hlb (by rw [hqs']; omega),
        show q.id.step / 2 = (l.v : Int) by rw [hqs']; omega]
      exact List.mem_singleton_self _
    have h01 := Lit.vv_snd l
    by_cases hlp : q.id.index = l.vv.2
    · have hmem : l.neg.neg.vv ∈ fixes φ q := by
        rw [Lit.neg_neg]
        have e : l.vv = ((l.v : Int), q.id.index) := Prod.ext rfl hlp.symm
        rw [e]
        exact hfix
      exact forced_unsupported φ hwf g hmr d hd hdm h2 q m hmP hmem
    · have hmem : l.neg.vv ∈ fixes φ q := by
        rw [Lit.vv_neg]
        have e : (l.vv.1, 1 - l.vv.2) = ((l.v : Int), q.id.index) :=
          Prod.ext rfl (by show 1 - l.vv.2 = q.id.index; omega)
        rw [e]
        exact hfix
      exact forced_unsupported φ hwf g hmr d hd hdm h1 q m hmP hmem
  -- a valid filter would keep a global owner at that step, which is a removed node
  cases hv : isValid (filterAll g (reqOfCnf φ d)) with
  | false => rfl
  | true =>
    exfalso
    have hent := hasStepEntry_of_isValid _ hv (2 * (l.v : Int)) (by omega)
      (by rw [(pruned_filterAll g (reqOfCnf φ d)).step_eq]; exact hvs)
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
    obtain ⟨q, hq, _⟩ := hent
    have hgnF := GownersNodes.GN_filterAll g (reqOfCnf φ d) hgn
    obtain ⟨mF, hmF⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff _ q).mp (hgnF q hq))
    have hqP : q ∈ ((reqOfCnf φ d).foldl filterRequire g).gowners := (pruned_review _).gowners_sub q hq
    obtain ⟨m, hm, hmid⟩ := hgn q (FabricAdd.gowners_foldl_sub (reqOfCnf φ d) g q hqP)
    have hmP : ((reqOfCnf φ d).foldl filterRequire g).node? q = some m := by
      rw [← hmid]
      exact hnodeG m hm
    have hgone := unsupported_removed (reqOfCnf φ) g hr (reqOfCnf φ d) hv (hall q m hmP)
    rw [hgone] at hmF
    cases hmF

/-- info: 'AbsSat.GraphPath.Model.UnitPropReview.forced_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms forced_unsupported

/-- info: 'AbsSat.GraphPath.Model.UnitPropReview.conflict_invalid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conflict_invalid

end AbsSat.GraphPath.Model.UnitPropReview
