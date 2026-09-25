-- lean/improves_bin/AbsSatBin/GraphPath/Model/CnfChain.lean
import AbsSatBin.GraphPath.Model.MapReachable
import AbsSatBin.GraphPath.Model.MapChain
import AbsSatBin.GraphPath.Model.ParentId

/-!
# From a chain to a satisfying assignment, on the bin map — **rewritten** (`lean_project`'s `CnfChain`)

The decode. A chain over the bin map of `φ` that satisfies the map's requirements, in a graph
with no prohibited node, reads off as an assignment that satisfies `φ`.

`decode` reads a variable from the index of the node the chain stands on at the variable's own
step `varStep v` (`2v+1` here; `2v` in `lean_project`).

## The argument, at clause `j`

1. **One literal.** At `Lₚ` the chain stands on `⟨Lₚ, bₚ⟩`, `bₚ ∈ {0,1}` (the map has both
   values, `ChainOnMap`). Its one requirement is `⟨lₚ.binStep, bₚ⟩`, so `ReqSatisfying` puts the
   chain there, and the literal's value under `decode` is `bₚ = 1` (`litVal_of_node`). A negated
   literal takes a second application, through the negation node's own requirement, exactly as
   in `lean_project`.
2. **The window.** By the parent coherence of `ParentId`, the chain's pick at `L3` *is* the
   identifier `(L3=b₂, L2=b₁, L1=b₀)` — `clauseWindow φ j b₀ b₁ b₂`.
3. **Not prohibited.** No node of the graph is prohibited (`NoForb`), so that window is not
   `(0,0,0)` (`clauseWindow_prohibited_iff`): some `bₚ = 1`, and literal `p` is true.

Where `lean_project` used "row `000` is not on the map", this uses "window `(0,0,0)` is not in
the graph" — the disjunction moved from the nodes of the map to the identifiers of the gpath.
-/

namespace AbsSatBin.GraphPath.Model.CnfChain

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.MapReachable

variable (φ : Cnf)

/-- The reader as a total function: a variable is true iff the node standing at its own step
carries index 1. -/
def decode (sel : Int → PathNodeId) : Assign :=
  fun v => ((sel (varStep v)).id.index == 1)

-- ============================================================
-- One literal
-- ============================================================

/-- **A literal's value is the index the chain carries at the literal's step.** -/
theorem litVal_of_node (g : GPathM) (sel : Int → PathNodeId)
    (hcs : g.current_step = stepCount φ)
    (hrs : MapChain.ReqSatisfying (reqOf φ) g sel)
    (l : Lit) (hl : l.v < φ.nVars) (b : Int) (hb : b = 0 ∨ b = 1)
    (hat : (sel l.binStep).id = ⟨l.binStep, b⟩) :
    litVal (decode sel) l = (b == 1) := by
  cases hp : l.pos with
  | true =>
    have hstep : l.binStep = varStep l.v := varStep_eq l hp
    have : (sel (varStep l.v)).id.index = b := by rw [← hstep, hat]
    simp only [litVal, hp, decode, this]
    rfl
  | false =>
    have hstep : l.binStep = negStep l.v := negStep_eq l hp
    -- the chain stands on "!v=b"; the negation node's own requirement moves it to "v=1-b"
    have hk0 : (0 : Int) ≤ negStep l.v := by simp only [negStep]; omega
    have hk1 : negStep l.v < g.current_step := by
      rw [hcs]; simp only [negStep, stepCount]; omega
    have hnegstep : (sel (negStep l.v)).id.step = negStep l.v := by rw [← hstep, hat]
    have hreqs := reqOf_neg φ (sel (negStep l.v)).id l.v hl hnegstep
    have hidx : (sel (negStep l.v)).id.index = b := by rw [← hstep, hat]
    rw [hidx] at hreqs
    have hsecond := hrs (negStep l.v) hk0 hk1 { step := varStep l.v, index := 1 - b }
      (by rw [hreqs]; exact List.mem_cons_self)
      (by simp only [varStep]; omega)
      (by rw [hcs]; simp only [varStep, stepCount]; omega)
    have hv : (sel (varStep l.v)).id.index = 1 - b := by rw [hsecond]
    simp only [litVal, hp, decode, hv]
    rcases hb with rfl | rfl <;> rfl

-- ============================================================
-- One clause, then the formula
-- ============================================================

theorem satClause_of_reqSat (g : GPathM) (sel : Int → PathNodeId)
    (hbd : Bounded φ) (hcs : g.current_step = stepCount φ)
    (hchain : IsChain g sel)
    (hrs : MapChain.ReqSatisfying (reqOf φ) g sel)
    (hcm : ChainOnMap φ g sel)
    (hnf : NoForb (isProhibited φ) g)
    (hpmp : ParentId.PMP g) (hgpmp : ParentId.GPMP g)
    (j : Nat) (hjlt : j < φ.clauses.length) (c : Clause)
    (hj : φ.clauses[j]? = some c) :
    SatClause (decode sel) c := by
  -- the three literal steps of the clause, and what the chain picks there
  have pick : ∀ p, p < 3 →
      ∃ b : Int, (b = 0 ∨ b = 1) ∧ (sel (clauseStep φ j p)).id = ⟨clauseStep φ j p, b⟩ ∧
        litVal (decode sel) (litAt c p) = (b == 1) := by
    intro p hp
    have hk0 : (0 : Int) ≤ clauseStep φ j p := by simp only [clauseStep]; omega
    have hk : clauseStep φ j p < g.current_step := by
      rw [hcs]; simp only [clauseStep, stepCount]; omega
    obtain ⟨_, hstep⟩ := hchain.1 _ hk0 hk
    have hon := hcm _ hk0 hk
    rw [mapNodes_two φ _ (by simp only [clauseStep]; omega)
      (by simp only [clauseStep, midFusion]; omega)
      (by simp only [clauseStep, fusionTop]; omega)] at hon
    obtain ⟨b, hb, hid⟩ : ∃ b : Int, (b = 0 ∨ b = 1) ∧
        (sel (clauseStep φ j p)).id = ⟨clauseStep φ j p, b⟩ := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
      rcases hon with h | h
      · exact ⟨0, Or.inl rfl, h⟩
      · exact ⟨1, Or.inr rfl, h⟩
    refine ⟨b, hb, hid, ?_⟩
    have hreqs := reqOf_clause φ (sel (clauseStep φ j p)).id j p c hp hjlt hj hstep
    have hidx : (sel (clauseStep φ j p)).id.index = b := by rw [hid]
    rw [hidx] at hreqs
    obtain ⟨h1, h2, h3⟩ := hbd c (List.mem_of_getElem? hj)
    have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
    have hlo : (0 : Int) ≤ (litAt c p).binStep := by have := (lit_step_bounds φ _ hv).1; omega
    have hhi : (litAt c p).binStep < g.current_step := by
      have := (lit_step_bounds φ _ hv).2
      rw [hcs]; simp only [midFusion, stepCount] at this ⊢; omega
    have hat := hrs _ hk0 hk { step := (litAt c p).binStep, index := b }
      (by rw [hreqs]; exact List.mem_cons_self) hlo hhi
    exact litVal_of_node φ g sel hcs hrs (litAt c p) hv b hb hat
  obtain ⟨b0, hb0, hid0, hv0⟩ := pick 0 (by omega)
  obtain ⟨b1, hb1, hid1, hv1⟩ := pick 1 (by omega)
  obtain ⟨b2, hb2, hid2, hv2⟩ := pick 2 (by omega)
  -- the pick at L3 is the window (L3=b2, L2=b1, L1=b0)
  have e10 : clauseStep φ j 0 + 1 = clauseStep φ j 1 := by simp only [clauseStep]; omega
  have e21 : clauseStep φ j 1 + 1 = clauseStep φ j 2 := by simp only [clauseStep]; omega
  have hl0 : (0 : Int) ≤ clauseStep φ j 0 := by simp only [clauseStep]; omega
  have hl1 : (0 : Int) ≤ clauseStep φ j 1 := by simp only [clauseStep]; omega
  have hhi2 : clauseStep φ j 2 < g.current_step := by
    rw [hcs]; simp only [clauseStep, stepCount]; omega
  have hpar2 := ParentId.parentId_coherent g hpmp sel hchain _ hl1 (by rw [e21]; exact hhi2)
  have hgp2 := ParentId.gparentId_coherent g hgpmp sel hchain _ hl1 (by rw [e21]; exact hhi2)
  have hhi1 : clauseStep φ j 0 + 1 < g.current_step := by
    rw [hcs]; simp only [clauseStep, stepCount]; omega
  have hpar1 := ParentId.parentId_coherent g hpmp sel hchain _ hl0 hhi1
  rw [e21] at hpar2 hgp2
  rw [e10] at hpar1
  have hwin : sel (clauseStep φ j 2) = clauseWindow φ j b0 b1 b2 := by
    apply ParentId.pathNodeId_ext
    · rw [hid2]; rfl
    · rw [hpar2, hid1]; rfl
    · rw [hgp2, hpar1, hid0]; rfl
  -- and it is not prohibited
  have hnot : isProhibited φ (sel (clauseStep φ j 2)) = false :=
    chain_not_forb _ g hnf sel hchain _ (by simp only [clauseStep]; omega) hhi2
  rw [hwin] at hnot
  have hne : ¬ (b0 = 0 ∧ b1 = 0 ∧ b2 = 0) := by
    intro hz
    have := (clauseWindow_prohibited_iff φ j hjlt b0 b1 b2).mpr hz
    rw [hnot] at this
    exact Bool.false_ne_true this
  simp only [SatClause]
  simp only [litAt] at hv0 hv1 hv2
  rw [hv0, hv1, hv2]
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl <;>
    first | (exfalso; exact hne ⟨rfl, rfl, rfl⟩) | decide

/-- **The decode theorem.** A requirement-satisfying chain over the bin map of `φ`, in a graph
with no prohibited node, reads off as an assignment that satisfies `φ`. -/
theorem sat_of_reqSatisfying (g : GPathM) (sel : Int → PathNodeId)
    (hbd : Bounded φ) (hcs : g.current_step = stepCount φ)
    (hchain : IsChain g sel)
    (hrs : MapChain.ReqSatisfying (reqOf φ) g sel)
    (hcm : ChainOnMap φ g sel)
    (hnf : NoForb (isProhibited φ) g)
    (hpmp : ParentId.PMP g) (hgpmp : ParentId.GPMP g) :
    Sat (decode sel) φ := by
  intro c hc
  obtain ⟨j, hjlt, hj⟩ := exists_index_of_mem φ.clauses c hc
  exact satClause_of_reqSat φ g sel hbd hcs hchain hrs hcm hnf hpmp hgpmp j hjlt c hj

/-- info: 'AbsSatBin.GraphPath.Model.CnfChain.sat_of_reqSatisfying' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_reqSatisfying

end AbsSatBin.GraphPath.Model.CnfChain
