-- lean_project/AbsSat/GraphPath/Model/LiveSolution.lean
import AbsSat.GraphPath.Model.RunNoBorrow

/-!
# The core in the language of paths: a live value is part of a real solution

The history technique that proved no borrowing (v148) places paths that exist: every path of a state is a
genuine partial solution, and every genuine partial solution is in the state of its key. `LivePinUp`
asks for the other thing — that a path **exist** through a live value. This module states the core in
that language:

* **`livePinUp_of_onPath`** — `LivePinUp` follows from: *in a valid reader's state with the prefix
  decided, every live value of the next variable lies on a path of the state*.
* **`path_is_solution`** (no hypothesis) — a path of any state the reader reaches spells a model of `φ`.

So the core is exactly: **in a valid reader's state, a value that survives the review is part of a real
solution.**
-/

namespace AbsSat.GraphPath.Model.LiveSolution

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem)
open AbsSat.GraphPath.Model.PinExtends (RF rf_readFrom)
open AbsSat.GraphPath.Model.PinUp (Decided LivePinUp)

variable (φ : Cnf)

/-- **A live value on a path**: in a valid reader's state with the prefix decided, every live value of
the next variable lies on a path of the state. -/
def LiveOnPath (g₀ : GPathM) : Prop :=
  ∀ S, ReadFrom g₀ S → isValid S = true → ∀ v : Nat, v < φ.nVars →
    (∀ k, 0 ≤ k → k < 2 * (v : Int) → Decided S k) →
    ∀ a, Mem S a → a.id.step = 2 * (v : Int) → ∃ sel, ChainSound S sel ∧ sel a.id.step = a

/-- **`LivePinUp` from live values on paths**: the path through the value survives its pin. -/
theorem livePinUp_of_onPath {g₀ : GPathM} (h : LiveOnPath φ g₀) : LivePinUp φ g₀ := by
  intro S hS hv v hvn hpre a ha has
  obtain ⟨sel, hsc, hsa⟩ := h S hS hv v hvn hpre a ha has
  have hp := ChainSound_filterAllAgg S [a.id] sel hsc (fun r hr _ _ => by
    rw [List.mem_singleton.mp hr, hsa])
  exact PickInduction.isValid_of_ChainG _ sel hp.chain

/-- **Every path of a reader's state is a real solution** (no hypothesis). -/
theorem path_is_solution (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (h0 : RF (filterAllAgg kv.2 [])) {S : GPathM} (hS : ReadFrom (filterAllAgg kv.2 []) S)
    (sel : Int → PathNodeId) (hsc : ChainSound S sel) : Sat (CnfChain.decode sel) φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hpr := Pruned.trans (pruned_filterAllAgg kv.2 []) (rf_readFrom h0 hS).2
  exact ReaderComplete.sat_decode φ hwf kv hkv sel
    (SubsetSemantics.ChainSound_of_pruned hpr hm.rctx.nodup hm.smp sel hsc)

/-- info: 'AbsSat.GraphPath.Model.LiveSolution.livePinUp_of_onPath' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms livePinUp_of_onPath

/-- info: 'AbsSat.GraphPath.Model.LiveSolution.path_is_solution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms path_is_solution

-- ============================================================
-- Dividing the core: (A) the decided clauses hold
-- ============================================================

section
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (bit)
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup)
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.PinUp (onMap_of_mem)
open AbsSat.GraphPath.Model.MapReachable (NodesOnMap)

theorem litVal_of_bit {β : Assign} {l : Lit} (h : bit (litVal β l) = 1) : litVal β l = true := by
  cases hl : litVal β l with
  | false => rw [hl] at h; exact absurd h (by decide)
  | true => rfl

/-- **(A) The decided clauses hold.** In a valid reviewed state whose even steps below `2v` are decided
by `β`, a live node `a` at step `2v` carrying `β`'s value of `v` sees every clause whose variables are
all `≤ v` satisfied by `β`: `a` owns a row of the clause; at each literal's step `a` and the row share an
owner; that owner carries the decided value (or `a`'s own); the row's requirements match those values;
and a row the map builds names a true literal. -/
theorem decided_clause_holds (hwf : WF φ) (S : GPathM) (ad : AdjacentOwners.Adj S)
    (hok : AggFixpoint.AggOk S) (hsmp : Sons.SMP S) (hrf : ReqFiltered (reqOfCnf φ) S)
    (hmap : NodesOnMap φ S) (hcs : S.current_step = stepCount φ)
    (v : Nat) (β : Assign)
    (hβ : ∀ p, Mem S p → p.id.step < 2 * (v : Int) → p.id.step % 2 = 0 →
      p.id.index = bit (β (p.id.step / 2).toNat))
    (a : PathNodeId) (ha : Mem S a) (has : a.id.step = 2 * (v : Int)) (hav : a.id.index = bit (β v))
    (j : Nat) (hj : j < φ.clauses.length)
    (hvars : φ.clauses[j].l1.v ≤ v ∧ φ.clauses[j].l2.v ≤ v ∧ φ.clauses[j].l3.v ≤ v) :
    SatClause β φ.clauses[j] := by
  have sup := sup_self S ad hok hsmp
  have hc : φ.clauses[j]? = some φ.clauses[j] := List.getElem?_eq_getElem hj
  obtain ⟨⟨hv1, hv2, hv3⟩, _⟩ := hwf φ.clauses[j] (List.mem_of_getElem? hc)
  have hcj0 : 0 ≤ clauseStep φ j := by unfold clauseStep; omega
  have hcj1 : clauseStep φ j < S.current_step := by rw [hcs]; unfold clauseStep stepCount; omega
  -- a row of the clause that `a` owns
  obtain ⟨r, har, hrs⟩ := sup.cov a ha (clauseStep φ j) hcj0 hcj1
  have hrm : Mem S r := by obtain ⟨_, _, _, h⟩ := har; exact h
  obtain ⟨mr, hmr⟩ := hrm
  have hrid := node?_id_eq S r mr hmr
  have hon := onMap_of_mem φ S hmap ⟨mr, hmr⟩
  rw [hrs] at hon
  obtain ⟨hr1, hr7⟩ := index_range_of_clauseNode φ j hj _ hon
  have hreqs := reqOfCnf_clause φ r.id j φ.clauses[j] hj hc hrs
  -- the bit of each literal of the row is the literal's value under `β`
  have litBit : ∀ (lt : Lit) (b : Int), lt.v ≤ v → lt.v < φ.nVars → litReq lt b ∈ reqOfCnf φ r.id →
      bit (litVal β lt) = b := by
    intro lt b hle hlt hmem
    have hs0 : 0 ≤ lt.step := by unfold Lit.step; split <;> omega
    have hs1 : lt.step < S.current_step := by
      rw [hcs]; unfold Lit.step stepCount; split <;> omega
    obtain ⟨z, haz, hrz, hzs⟩ := sup.agg a r har lt.step hs0 hs1
    -- the row's owner at the literal's step carries the requirement
    have hzreq : z.id = litReq lt b := by
      obtain ⟨m', hm', hzin, _⟩ := hrz
      rw [hmr] at hm'; cases hm'
      exact hrf mr (List.mem_of_find?_eq_some hmr) (litReq lt b) (by rw [hrid]; exact hmem) z hzin
        (by rw [hzs]; rfl)
    have hzm : Mem S z := by obtain ⟨_, _, _, h⟩ := hrz; exact h
    cases hp : lt.pos with
    | true =>
      have hstep : lt.step = 2 * (lt.v : Int) := by unfold Lit.step; rw [hp]; simp
      have hlv : litVal β lt = β lt.v := by simp [litVal, hp]
      rw [hlv]
      by_cases heq : lt.v = v
      · -- `z` sits at `a`'s own step and `a` owns it: it is `a`
        obtain ⟨ma, hma, hzina, _⟩ := haz
        have hid := node?_id_eq S a ma hma
        have hza := ad.rc.oos ma (List.mem_of_find?_eq_some hma) z hzina (by rw [hid, hzs, hstep, has, heq])
        rw [hid] at hza
        rw [hza] at hzreq
        have : a.id.index = b := by rw [hzreq]; rfl
        rw [heq, ← hav, this]
      · have hzstep : z.id.step = 2 * (lt.v : Int) := by rw [hzs, hstep]
        have := hβ z hzm (by rw [hzstep]; omega) (by rw [hzstep]; omega)
        rw [hzstep, show (2 * (lt.v : Int) / 2).toNat = lt.v by omega, hzreq] at this
        exact this.symm
    | false =>
      have hstep : lt.step = 2 * (lt.v : Int) + 1 := by unfold Lit.step; rw [hp]; simp
      have hlv : litVal β lt = !(β lt.v) := by simp [litVal, hp]
      rw [hlv]
      -- the negation node's own requirement names the variable's value
      have hzneg : reqOfCnf φ z.id = [{ step := varStep lt.v, index := 1 - z.id.index }] :=
        reqOfCnf_neg φ z.id lt.v hlt (by rw [hzs, hstep]; rfl)
      have hzb : z.id.index = b := by rw [hzreq]; rfl
      obtain ⟨mz, hmz⟩ := hzm
      have hzid := node?_id_eq S z mz hmz
      have ownVal : ∀ w, w ∈ mz.owners → w.id.step = 2 * (lt.v : Int) → w.id.index = 1 - b := by
        intro w hw hws
        have := hrf mz (List.mem_of_find?_eq_some hmz) _ (by rw [hzid, hzneg]; exact List.mem_cons_self) w hw
          (by rw [hws]; rfl)
        rw [this, hzb]
      by_cases heq : lt.v = v
      · -- `z` owns `a`
        have hza := sup.sym a z haz
        obtain ⟨mz', hmz', hain, _⟩ := hza
        rw [hmz] at hmz'; cases hmz'
        have := ownVal a hain (by rw [has, heq])
        rw [heq, AbsSat.GraphMap.CnfSel.bit_not, ← hav, this]
        omega
      · obtain ⟨w, hzw, hws⟩ := sup.cov z ⟨mz, hmz⟩ (2 * (lt.v : Int)) (by omega) (by omega)
        obtain ⟨mz', hmz', hwin, hwm⟩ := hzw
        rw [hmz] at hmz'; cases hmz'
        have h1 := ownVal w hwin hws
        have h2 := hβ w hwm (by rw [hws]; omega) (by rw [hws]; omega)
        rw [hws, show (2 * (lt.v : Int) / 2).toNat = lt.v by omega] at h2
        rw [AbsSat.GraphMap.CnfSel.bit_not, ← h2, h1]
        omega
  have e1 := litBit _ _ hvars.1 hv1 (by rw [hreqs]; exact List.mem_cons_self)
  have e2 := litBit _ _ hvars.2.1 hv2 (by rw [hreqs]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have e3 := litBit _ _ hvars.2.2 hv3
    (by rw [hreqs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rcases bits_not_all_zero r.id.index hr1 hr7 with hb | hb | hb
  · exact Or.inl (litVal_of_bit (by rw [e1, hb]))
  · exact Or.inr (Or.inl (litVal_of_bit (by rw [e2, hb])))
  · exact Or.inr (Or.inr (litVal_of_bit (by rw [e3, hb])))

/-- info: 'AbsSat.GraphPath.Model.LiveSolution.decided_clause_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decided_clause_holds

end

end AbsSat.GraphPath.Model.LiveSolution
