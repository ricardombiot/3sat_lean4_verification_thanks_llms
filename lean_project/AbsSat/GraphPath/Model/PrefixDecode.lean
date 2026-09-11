-- lean_project/AbsSat/GraphPath/Model/PrefixDecode.lean
import AbsSat.GraphPath.Model.PrefixConservation
import AbsSat.GraphPath.Model.L7

/-!
# Decoding, by prefix

`CnfChain.sat_of_reqSatisfying` reads a chain of a **full-length** state as a
model of φ. In the middle of a run the right statement is weaker and just as
true: a chain of a state at step `cs` reads as an assignment satisfying **every
clause the machine has seen** — every clause whose step is below `cs`.

The full-length proof uses the length in two places only: that the literal
steps lie below the current step, and that the clause's step does. Both hold
as soon as the clause itself has been seen. So the proof is the same one with
those two facts as hypotheses.

With `PrefixConservation.pureSteps_carries_prefix` this closes the loop in the
middle of a run: the chains of a machine state and the solutions of the clauses
it has seen are the same objects, read two ways.
-/

namespace AbsSat.GraphPath.Model.PrefixDecode

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.CnfChain
open AbsSat.GraphPath.Model.PrefixConservation

variable (φ : Cnf)

theorem litVal_of_reqSat_prefix (g : GPathM) (sel : Int → PathNodeId)
    (hlb : litBlock φ ≤ g.current_step)
    (hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel)
    (l : Lit) (hl : l.v < φ.nVars)
    (k : Int) (hk0 : 0 ≤ k) (hk : k < g.current_step)
    (hmem : litReq l 1 ∈ reqOfCnf φ (sel k).id) :
    litVal (decode sel) l = true := by
  have hblk : l.step < litBlock φ := lit_step_lt φ l hl
  have hlo : (0 : Int) ≤ l.step := by simp only [Lit.step]; split <;> omega
  have hhi : l.step < g.current_step := by omega
  have hfirst : (sel l.step).id = litReq l 1 :=
    hrs k hk0 hk (litReq l 1) hmem (by simp only [litReq]; exact hlo)
      (by simp only [litReq]; exact hhi)
  cases hp : l.pos with
  | true =>
    have hstep : l.step = 2 * (l.v : Int) := by rw [varStep_eq l hp]; rfl
    have : (sel (2 * (l.v : Int))).id.index = 1 := by
      rw [← hstep, hfirst]; rfl
    simp only [litVal, hp, decode, this]
    rfl
  | false =>
    have hstep : l.step = 2 * (l.v : Int) + 1 := by rw [negStep_eq l hp]; rfl
    have hnegstep : (sel (2 * (l.v : Int) + 1)).id.step = negStep l.v := by
      rw [← hstep, hfirst]; simp only [litReq, negStep]; omega
    have hnegidx : (sel (2 * (l.v : Int) + 1)).id.index = 1 := by
      rw [← hstep, hfirst]; rfl
    have hreqs := reqOfCnf_neg φ (sel (2 * (l.v : Int) + 1)).id l.v hl hnegstep
    rw [hnegidx] at hreqs
    have hmem2 : ({ step := varStep l.v, index := (1 : Int) - 1 } : NodeId)
        ∈ reqOfCnf φ (sel (2 * (l.v : Int) + 1)).id := by
      rw [hreqs]; exact List.mem_cons_self
    have hk2lo : (0 : Int) ≤ 2 * (l.v : Int) + 1 := by omega
    have hk2hi : 2 * (l.v : Int) + 1 < g.current_step := by
      rw [← hstep]; exact hhi
    have hsecond := hrs (2 * (l.v : Int) + 1) hk2lo hk2hi
      { step := varStep l.v, index := (1 : Int) - 1 } hmem2
      (by simp only [varStep]; omega) (by simp only [varStep]; omega)
    have hidx : (sel (2 * (l.v : Int))).id.index = 0 := by
      have : (sel (varStep l.v)).id.index = (1 : Int) - 1 := by rw [hsecond]
      simp only [varStep] at this
      omega
    simp only [litVal, hp, decode, hidx]
    rfl

theorem satClause_of_reqSat_prefix (g : GPathM) (sel : Int → PathNodeId)
    (hwf : WF φ) (hchain : IsChain g sel)
    (hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel)
    (hcm : ChainOnMap φ g sel)
    (j : Nat) (hjlt : j < φ.clauses.length) (c : Clause)
    (hj : φ.clauses[j]? = some c) (hseen : clauseStep φ j < g.current_step) :
    SatClause (decode sel) c := by
  have hk0 : (0 : Int) ≤ clauseStep φ j := by simp only [clauseStep]; omega
  have hlb : litBlock φ ≤ g.current_step := by
    simp only [clauseStep] at hseen; simp only [litBlock]; omega
  obtain ⟨_, hstep⟩ := hchain.1 (clauseStep φ j) hk0 hseen
  have hon : (sel (clauseStep φ j)).id ∈ mapNodes φ (clauseStep φ j) :=
    hcm (clauseStep φ j) hk0 hseen
  obtain ⟨hr1, hr7⟩ := index_range_of_clauseNode φ j hjlt _ hon
  have hreqs := reqOfCnf_clause φ (sel (clauseStep φ j)).id j c hjlt hj hstep
  obtain ⟨⟨h1, h2, h3⟩, _⟩ := wf_of_getElem? φ hwf j c hj
  rcases bits_not_all_zero (sel (clauseStep φ j)).id.index hr1 hr7 with hb | hb | hb
  · refine Or.inl (litVal_of_reqSat_prefix φ g sel hlb hrs c.l1 h1 (clauseStep φ j) hk0 hseen ?_)
    rw [hreqs, hb]
    exact List.mem_cons_self
  · refine Or.inr (Or.inl
      (litVal_of_reqSat_prefix φ g sel hlb hrs c.l2 h2 (clauseStep φ j) hk0 hseen ?_))
    rw [hreqs, hb]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · refine Or.inr (Or.inr
      (litVal_of_reqSat_prefix φ g sel hlb hrs c.l3 h3 (clauseStep φ j) hk0 hseen ?_))
    rw [hreqs, hb]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **Decoding, by prefix.** A co-owned chain of any machine state reads as an
assignment satisfying every clause that state has seen. -/
theorem satUpTo_of_chain (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g)
    (sel : Int → PathNodeId) (hchain : IsChain g sel) (howned : PairwiseOwned g sel) :
    SatUpTo φ (decode sel) (g.current_step - 1) := by
  have hreach : Reachable (reqOfCnf φ) g := reachable_of_mapReachable φ hwf g hmr
  have hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel := by
    intro k hk0 hk req hreq hr0 hr1
    exact L1_cor (reqOfCnf φ) hreach hchain howned k hk0 hk req hreq hr0 hr1
  have hcm : ChainOnMap φ g sel :=
    chainOnMap_of_nodesOnMap φ g (nodesOnMap_of_mapReachable φ g hmr) sel hchain
  intro j c hj hle
  have hjlt : j < φ.clauses.length := by
    rcases Nat.lt_or_ge j φ.clauses.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  exact satClause_of_reqSat_prefix φ g sel hwf hchain hrs hcm j hjlt c hj (by omega)

/-- info: 'AbsSat.GraphPath.Model.PrefixDecode.satUpTo_of_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms satUpTo_of_chain

end AbsSat.GraphPath.Model.PrefixDecode
