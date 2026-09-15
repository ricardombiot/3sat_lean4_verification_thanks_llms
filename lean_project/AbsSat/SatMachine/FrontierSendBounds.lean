-- lean_project/AbsSat/SatMachine/FrontierSendBounds.lean
import AbsSat.SatMachine.FrontierReduction
import AbsSat.GraphPath.Model.EmptinessReduction
import AbsSat.GraphPath.Model.PrefixDecode

/-!
# Where `FrontierSend` sits

`FrontierReduction` reduces the machine's SAT verdict to `FrontierSend`. This module
places that obligation between what is already known.

* **On the run only** (`FrontierSendRun`). The reduction never needs the obligation on
  every line satisfying `LineOk`, only on the lines the driver actually builds. That
  version is weaker (`frontierSendRun_of_frontierSend`) and still enough
  (`sat_of_pureRun_ne_nil_run`).
* **No harder than `SendExact`** (`frontierSendRun_of_sendExact`). `SendExact` hands a
  path of the source state through the destination's pins; `PrefixDecode.satUpTo_of_chain`
  reads that path as an assignment satisfying every clause the state has seen, and
  `bit_of_pin` says the pins fix that assignment's literals to the destination's row. So
  `FrontierSend` asks for strictly less than the obligation this development already had.

What `FrontierSend` adds is that it is **semantic**: it asks for a model of a prefix, not
for a path inside a state. Nothing here closes it.
-/

namespace AbsSat.SatMachine.FrontierSendBounds

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.CnfChain (decode)
open AbsSat.GraphPath.Model.SubsetSemantics (denotS mem_pathOf_iff)
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.PartialPaths (lineAt lineAt_ok)
open AbsSat.Cnf.FrontierDP (SatPrefix take_succ_of_get)
open AbsSat.SatMachine.PureSatMachine
open AbsSat.SatMachine.FrontierReduction

variable (φ : Cnf)

-- ============================================================
-- The obligation, on the driver's own lines
-- ============================================================

def FrontierSendRun : Prop :=
  ∀ (n : Nat), ∀ kv ∈ lineAt φ n, ∀ d ∈ mapSons φ kv.1.step kv.1.index,
    isValid (upFiltering kv.2 (reqOfCnf φ d) d "") = true →
    ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → d.step = clauseStep φ j →
      ∃ a, SatPrefix a φ j ∧ rowOf a c = d.index

theorem frontierSendRun_of_frontierSend (h : FrontierSend φ) : FrontierSendRun φ :=
  fun n kv hkv d hd hval j c hc hdstep =>
    h n (lineAt φ n) (lineAt_ok φ n) (prefixSound_lineAt φ h n) kv hkv d hd hval j c hc hdstep

-- ============================================================
-- The run version is enough
-- ============================================================

theorem prefixSound_lineAt_succ (hFS : FrontierSendRun φ) (n : Nat) :
    PrefixSound φ (lineAt φ (n + 1)) := by
  have hstep : lineAt φ (n + 1) = pureAdvance φ (lineAt φ n) := by
    show pureSteps φ (n + 1) (pureInit φ) = pureAdvance φ (pureSteps φ n (pureInit φ))
    rw [PureProofs.pureSteps_succ']
  rw [hstep]
  intro e he j c hc hdstep
  obtain ⟨kv, hkv, hd, hval⟩ := pureAdvance_validOrigin φ (lineAt φ n) e he
  have hon : e.1 ∈ mapNodes φ ((n : Int) + 1) :=
    ((LineOk_pureAdvance φ n (lineAt φ n) (lineAt_ok φ n)).2 e he).onMap
  obtain ⟨a, hsat, hrow⟩ := hFS n kv hkv e.1 hd hval j c hc hdstep
  refine ⟨a, ?_, hrow⟩
  have hjlt := lt_of_getElem?_some hc
  have hkstep : (n : Int) + 1 = clauseStep φ j := by
    rw [← mapNodes_step φ ((n : Int) + 1) e.1 hon]; exact hdstep
  have hrange := index_range_of_clauseNode φ j hjlt e.1 (by rw [← hkstep]; exact hon)
  have hcl : SatClause a c := satClause_of_rowOf_pos a c (by rw [hrow]; exact hrange.1)
  intro c' hc'
  rw [take_succ_of_get φ.clauses j c hc] at hc'
  rcases List.mem_append.mp hc' with h | h
  · exact hsat c' h
  · rcases List.mem_singleton.mp h with rfl
    exact hcl

theorem clauseStep_toNat_succ (m : Nat) :
    (clauseStep φ m).toNat = ((clauseStep φ m).toNat - 1) + 1 := by
  unfold clauseStep; omega

/-- **The run version already gives soundness.** -/
theorem sat_of_pureRun_ne_nil_run (hFS : FrontierSendRun φ) (h : pureRun φ ≠ []) :
    Satisfiable φ := by
  cases hm : φ.clauses.length with
  | zero =>
    refine ⟨fun _ => true, fun c hc => ?_⟩
    rw [List.eq_nil_of_length_eq_zero hm] at hc
    exact absurd hc List.not_mem_nil
  | succ m =>
    have hmlt : m < φ.clauses.length := by rw [hm]; exact Nat.lt_succ_self m
    obtain ⟨c, hc⟩ : ∃ c, φ.clauses[m]? = some c := ⟨φ.clauses[m], List.getElem?_eq_getElem hmlt⟩
    have hrun : pureRun φ = pureAdvance φ (lineAt φ (clauseStep φ m).toNat) := by
      show pureSteps φ (stepCount φ - 1).toNat (pureInit φ)
        = pureAdvance φ (pureSteps φ (clauseStep φ m).toNat (pureInit φ))
      rw [stepCount_sub_one_toNat φ m hm, PureProofs.pureSteps_succ']
    have hne : lineAt φ (clauseStep φ m).toNat ≠ [] := by
      intro h0
      apply h
      rw [hrun, h0]
      rfl
    obtain ⟨kv, hkv⟩ := List.exists_mem_of_ne_nil _ hne
    have hon := ((lineAt_ok φ (clauseStep φ m).toNat).2 kv hkv).onMap
    have hstep : kv.1.step = clauseStep φ m :=
      (mapNodes_step φ _ kv.1 hon).trans (clauseStep_toNat_cast φ m)
    have hps : PrefixSound φ (lineAt φ (clauseStep φ m).toNat) := by
      rw [clauseStep_toNat_succ φ m]
      exact prefixSound_lineAt_succ φ hFS _
    obtain ⟨a, hsat, _⟩ := hps kv hkv m c hc hstep
    have hlen : m + 1 = φ.clauses.length := hm.symm
    exact ⟨a, fun c' hc' => hsat c' (by rw [hlen, List.take_length]; exact hc')⟩

-- ============================================================
-- A pin fixes the decoded literal
-- ============================================================

theorem litBlock_le_clauseStep (j : Nat) : litBlock φ ≤ clauseStep φ j := by
  unfold litBlock clauseStep; omega

theorem clauseStep_le_pred (i j : Nat) (h : i < j) : clauseStep φ i ≤ clauseStep φ j - 1 := by
  unfold clauseStep; omega

theorem bit_of_pin (g : GPathM) (sel : Int → PathNodeId)
    (hlb : litBlock φ ≤ g.current_step)
    (hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel)
    (l : Lit) (hl : l.v < φ.nVars) (b : Int) (hb : b = 0 ∨ b = 1)
    (hfirst : (sel l.step).id = litReq l b) :
    bit (litVal (decode sel) l) = b := by
  have hblk : l.step < litBlock φ := lit_step_lt φ l hl
  have hlo : (0 : Int) ≤ l.step := by simp only [Lit.step]; split <;> omega
  have hhi : l.step < g.current_step := by omega
  cases hp : l.pos with
  | true =>
    have hstep : l.step = 2 * (l.v : Int) := by rw [varStep_eq l hp]; rfl
    have hidx : (sel (2 * (l.v : Int))).id.index = b := by rw [← hstep, hfirst]; rfl
    simp only [litVal, hp, decode, hidx]
    rcases hb with rfl | rfl <;> rfl
  | false =>
    have hstep : l.step = 2 * (l.v : Int) + 1 := by rw [negStep_eq l hp]; rfl
    have hnegstep : (sel (2 * (l.v : Int) + 1)).id.step = negStep l.v := by
      rw [← hstep, hfirst]; simp only [litReq, negStep]; omega
    have hnegidx : (sel (2 * (l.v : Int) + 1)).id.index = b := by rw [← hstep, hfirst]; rfl
    have hreqs := reqOfCnf_neg φ (sel (2 * (l.v : Int) + 1)).id l.v hl hnegstep
    rw [hnegidx] at hreqs
    have hmem2 : ({ step := varStep l.v, index := (1 : Int) - b } : NodeId)
        ∈ reqOfCnf φ (sel (2 * (l.v : Int) + 1)).id := by
      rw [hreqs]; exact List.mem_cons_self
    have hk2hi : 2 * (l.v : Int) + 1 < g.current_step := by rw [← hstep]; exact hhi
    have hsecond := hrs (2 * (l.v : Int) + 1) (by omega) hk2hi _ hmem2
      (by simp only [varStep]; omega) (by simp only [varStep]; omega)
    have hidx : (sel (2 * (l.v : Int))).id.index = 1 - b := by
      have h2 : (sel (varStep l.v)).id.index = (1 : Int) - b := by rw [hsecond]
      simp only [varStep] at h2
      exact h2
    simp only [litVal, hp, decode, hidx]
    rcases hb with rfl | rfl <;> rfl

theorem b1_zero_or_one (r : Int) : b1 r = 0 ∨ b1 r = 1 := by unfold b1; omega
theorem b2_zero_or_one (r : Int) : b2 r = 0 ∨ b2 r = 1 := by unfold b2; omega
theorem b3_zero_or_one (r : Int) : b3 r = 0 ∨ b3 r = 1 := by unfold b3; omega

theorem row_of_bits (r : Int) (h0 : 1 ≤ r) (h7 : r ≤ 7) : 4 * b1 r + 2 * b2 r + b3 r = r := by
  unfold b1 b2 b3; omega

-- ============================================================
-- `SendExact` implies it
-- ============================================================

/-- **`FrontierSend` is no harder than `SendExact`.** -/
theorem frontierSendRun_of_sendExact (hwf : WF φ)
    (hex : EmptinessReduction.SendExact φ) : FrontierSendRun φ := by
  intro n kv hkv d hd hval j c hc hdstep
  have hok := (lineAt_ok φ n).2 kv hkv
  have hkey : kv.1.step = (n : Int) := mapNodes_step φ _ kv.1 hok.onMap
  have hmk : (⟨(n : Int), kv.1.index⟩ : NodeId) ∈ mapNodes φ n := by
    have heq : (⟨(n : Int), kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix =>
        rw [hkv1] at hkey
        simp only at hkey ⊢
        rw [hkey]
    rw [heq]; exact hok.onMap
  have hd' : d ∈ mapNodes φ ((n : Int) + 1) :=
    mapSons_subset φ n kv.1.index hmk d (by rw [← hkey]; exact hd)
  have hdstep' : d.step = (n : Int) + 1 := mapNodes_step φ _ d hd'
  have hcs : d.step = kv.2.current_step := by rw [hdstep', hok.step]
  have hfv := isValid_filterAll_of_sent φ kv.2 d hval
  have hdmap : d ∈ mapNodes φ d.step := by rw [hdstep']; exact hd'
  obtain ⟨p, hp, hpins⟩ := hex kv.2 d hok.reach hok.valid
    (EmptinessReduction.lineAt_nonempty φ hwf hex n kv hkv) hcs hdmap hfv
  obtain ⟨sel, hs, rfl⟩ := hp
  have hjlt := lt_of_getElem?_some hc
  have hcmem : c ∈ φ.clauses := List.mem_of_getElem? hc
  obtain ⟨⟨hv1, hv2, hv3⟩, _⟩ := hwf c hcmem
  have hcur : kv.2.current_step = clauseStep φ j := by rw [← hcs, hdstep]
  have hlb : litBlock φ ≤ kv.2.current_step := by
    rw [hcur]; exact litBlock_le_clauseStep φ j
  have hreach := reachable_of_mapReachable φ hwf kv.2 hok.reach
  have hrs : MapChain.ReqSatisfying (reqOfCnf φ) kv.2 sel := by
    intro k hk0 hk req hreq hr0 hr1
    exact L1_cor (reqOfCnf φ) hreach hs.chain.1 hs.chain.2.1 k hk0 hk req hreq hr0 hr1
  have hreqs := reqOfCnf_clause φ d j c hjlt hc hdstep
  -- every pin of `d` is on the path, so it fixes the decoded literal
  have hpin : ∀ (l : Lit) (b : Int), l.v < φ.nVars → (b = 0 ∨ b = 1) →
      litReq l b ∈ reqOfCnf φ d → bit (litVal (decode sel) l) = b := by
    intro l b hlv hb hmem
    have hblk : l.step < litBlock φ := lit_step_lt φ l hlv
    have hlo : (0 : Int) ≤ l.step := by simp only [Lit.step]; split <;> omega
    have hhi : l.step < kv.2.current_step := by omega
    have hmemp := hpins (litReq l b) hmem (by simp only [litReq]; exact hlo)
      (by simp only [litReq]; exact hhi)
    have hfirst : (sel l.step).id = litReq l b := by
      have := (mem_pathOf_iff kv.2 sel hs.chain.1 (litReq l b) (by simp only [litReq]; exact hlo)
        (by simp only [litReq]; exact hhi)).mp hmemp
      simpa only [litReq] using this
    exact bit_of_pin φ kv.2 sel hlb hrs l hlv b hb hfirst
  refine ⟨decode sel, ?_, ?_⟩
  · -- the decoded assignment satisfies every clause the state has seen
    have hsat := PrefixDecode.satUpTo_of_chain φ hwf kv.2 hok.reach sel hs.chain.1 hs.chain.2.1
    intro c' hc'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc'
    have hilen := lt_of_getElem?_some hi
    have hij : i < j := by
      rw [List.length_take] at hilen
      omega
    have hi' : φ.clauses[i]? = some c' := by rw [← List.getElem?_take_of_lt hij]; exact hi
    exact hsat i c' hi' (by rw [hcur]; exact clauseStep_le_pred φ i j hij)
  · -- and its row of `c` is `d`
    have hrange := index_range_of_clauseNode φ j hjlt d (by rw [← hdstep]; exact hdmap)
    have h1 := hpin c.l1 (b1 d.index) hv1 (b1_zero_or_one d.index)
      (by rw [hreqs]; exact List.mem_cons_self)
    have h2 := hpin c.l2 (b2 d.index) hv2 (b2_zero_or_one d.index)
      (by rw [hreqs]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have h3 := hpin c.l3 (b3 d.index) hv3 (b3_zero_or_one d.index)
      (by rw [hreqs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    show 4 * bit (litVal (decode sel) c.l1) + 2 * bit (litVal (decode sel) c.l2)
      + bit (litVal (decode sel) c.l3) = d.index
    rw [h1, h2, h3]
    exact row_of_bits d.index hrange.1 hrange.2

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.SatMachine.FrontierSendBounds.frontierSendRun_of_frontierSend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frontierSendRun_of_frontierSend

/-- info: 'AbsSat.SatMachine.FrontierSendBounds.sat_of_pureRun_ne_nil_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pureRun_ne_nil_run

/-- info: 'AbsSat.SatMachine.FrontierSendBounds.bit_of_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bit_of_pin

/-- info: 'AbsSat.SatMachine.FrontierSendBounds.frontierSendRun_of_sendExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frontierSendRun_of_sendExact

end AbsSat.SatMachine.FrontierSendBounds
