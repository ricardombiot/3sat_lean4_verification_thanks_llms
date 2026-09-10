-- lean_project/AbsSat/GraphPath/Model/CnfChain.lean
import AbsSat.GraphPath.Model.MapReachable
import AbsSat.GraphPath.Model.MapChain

/-!
# From a chain to a satisfying assignment

The decode. A chain over the map of `φ` that satisfies the map's requirements
reads off as an assignment that satisfies `φ`.

`decode` is written directly rather than derived from `MirrorTest.readWork`:
that one is `partial` and can never be unfolded in a proof. The two agree by
construction — both take a variable's truth value from the *index* of the node
standing at the variable's own (even) step — and the differential band is where
that agreement is checked, not here.

## The argument, at a clause step

1. **The chain's node there is a real clause node.** `IsChain` puts it at the
   right step and `MapReachable.ChainOnMap` puts it among the seven the map
   builds, so its index `r` is in `1..7`. *This step cannot be skipped*:
   `reqOfCnf` answers for index `0` as well, with the requirements of the row
   the map omits — all three literals false — and the argument would run
   backwards.
2. **Some literal is named true.** The seven indices the map builds are exactly
   the seven satisfying rows, so `bits_not_all_zero` gives a position `p` with
   `b_p r = 1`, and the `p`-th requirement is `⟨lₚ.step, 1⟩`.
3. **`ReqSatisfying`, first application.** The chain stands on `⟨lₚ.step, 1⟩`.
4. **Positive literal:** that *is* the variable's step, so `decode` reads `1`
   and the literal is true. **Negated literal:** the chain stands on `"!v=1"`,
   which `decode` never looks at — so the negation block's own requirement is
   the bridge. `reqOfCnf` at `⟨2v+1,1⟩` is `[⟨2v,0⟩]`, literally `add_var!`'s
   `node1_neg` line, and a **second application** of `ReqSatisfying` (legitimate
   because it quantifies over every step, not only clause steps) puts the chain
   on `"v=0"`. So `decode` reads `0` and the negated literal is true.

Depth is one or two and never more: `reqOfCnf` is empty at even steps below the
literal block. There is no induction here, only a case split on polarity.
-/

namespace AbsSat.GraphPath.Model.CnfChain

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable

variable (φ : Cnf)

/-- The reader as a total function: a variable is true iff the node standing at
its own step carries index 1. Mirrors `MirrorTest.readWork`'s
`sol.push (mid.index == 1)` on even steps. -/
def decode (sel : Int → PathNodeId) : Assign :=
  fun v => ((sel (2 * (v : Int))).id.index == 1)

-- ============================================================
-- One literal
-- ============================================================

theorem litVal_of_reqSat (g : GPathM) (sel : Int → PathNodeId)
    (hcs : g.current_step = stepCount φ)
    (hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel)
    (l : Lit) (hl : l.v < φ.nVars)
    (k : Int) (hk0 : 0 ≤ k) (hk : k < g.current_step)
    (hmem : litReq l 1 ∈ reqOfCnf φ (sel k).id) :
    litVal (decode sel) l = true := by
  have hblk : l.step < litBlock φ := lit_step_lt φ l hl
  have hlo : (0 : Int) ≤ l.step := by simp only [Lit.step]; split <;> omega
  have hhi : l.step < g.current_step := by
    rw [hcs]; simp only [litBlock] at hblk; simp only [stepCount]; omega
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
    -- the chain stands on "!v=1"; the negation block's own requirement moves it to "v=0"
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
      (by simp only [varStep]; omega) (by
        rw [hcs]; simp only [varStep, stepCount]; omega)
    have hidx : (sel (2 * (l.v : Int))).id.index = 0 := by
      have : (sel (varStep l.v)).id.index = (1 : Int) - 1 := by rw [hsecond]
      simp only [varStep] at this
      omega
    simp only [litVal, hp, decode, hidx]
    rfl

-- ============================================================
-- One clause, then the formula
-- ============================================================

theorem satClause_of_reqSat (g : GPathM) (sel : Int → PathNodeId)
    (hwf : WF φ) (hcs : g.current_step = stepCount φ)
    (hchain : IsChain g sel)
    (hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel)
    (hcm : ChainOnMap φ g sel)
    (j : Nat) (hjlt : j < φ.clauses.length) (c : Clause)
    (hj : φ.clauses[j]? = some c) :
    SatClause (decode sel) c := by
  have hk0 : (0 : Int) ≤ clauseStep φ j := by simp only [clauseStep]; omega
  have hk : clauseStep φ j < g.current_step := by
    rw [hcs]; simp only [clauseStep, stepCount]; omega
  obtain ⟨_, hstep⟩ := hchain.1 (clauseStep φ j) hk0 hk
  -- the node the chain stands on is one of the seven the map builds
  have hon : (sel (clauseStep φ j)).id ∈ mapNodes φ (clauseStep φ j) :=
    hcm (clauseStep φ j) hk0 hk
  obtain ⟨hr1, hr7⟩ := index_range_of_clauseNode φ j hjlt _ hon
  have hreqs := reqOfCnf_clause φ (sel (clauseStep φ j)).id j c hjlt hj hstep
  obtain ⟨⟨h1, h2, h3⟩, _⟩ := wf_of_getElem? φ hwf j c hj
  rcases bits_not_all_zero (sel (clauseStep φ j)).id.index hr1 hr7 with hb | hb | hb
  · refine Or.inl (litVal_of_reqSat φ g sel hcs hrs c.l1 h1 (clauseStep φ j) hk0 hk ?_)
    rw [hreqs, hb]
    exact List.mem_cons_self
  · refine Or.inr (Or.inl
      (litVal_of_reqSat φ g sel hcs hrs c.l2 h2 (clauseStep φ j) hk0 hk ?_))
    rw [hreqs, hb]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · refine Or.inr (Or.inr
      (litVal_of_reqSat φ g sel hcs hrs c.l3 h3 (clauseStep φ j) hk0 hk ?_))
    rw [hreqs, hb]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **The decode theorem.** A requirement-satisfying chain over the map of `φ`
reads off as an assignment that satisfies `φ`. -/
theorem sat_of_reqSatisfying (g : GPathM) (sel : Int → PathNodeId)
    (hwf : WF φ) (hcs : g.current_step = stepCount φ)
    (hchain : IsChain g sel)
    (hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel)
    (hcm : ChainOnMap φ g sel) :
    Sat (decode sel) φ := by
  intro c hc
  obtain ⟨j, hjlt, hj⟩ := exists_index_of_mem φ.clauses c hc
  exact satClause_of_reqSat φ g sel hwf hcs hchain hrs hcm j hjlt c hj

/-- info: 'AbsSat.GraphPath.Model.CnfChain.sat_of_reqSatisfying' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_reqSatisfying

end AbsSat.GraphPath.Model.CnfChain
