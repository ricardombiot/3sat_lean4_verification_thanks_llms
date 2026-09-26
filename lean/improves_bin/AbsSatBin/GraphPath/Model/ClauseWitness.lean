-- lean/improves_bin/AbsSatBin/GraphPath/Model/ClauseWitness.lean
import AbsSatBin.GraphPath.Model.NoInvent

/-!
# Witnesses at clause steps carry literals in their window

What the Julia probe of `{a=1, b=1, c=1}` showed (`julia/improves_bin/test_3sat/probes/clause_mix_probe.jl`):
the clique dies at the `L3` of `x ∨ y ∨ z` because the witness at the `L2` of `a∧b → ¬x` has the window
`(¬a, ¬b) = (0, 0)` — its identity already carries `a = 1` and `b = 1` — and no piece lets it own `c = 1`.

The rule, formal: **a node at a clause step fixes, in its table, the variables of the literals of its
window.**

* **`req_in_table`**: at the step of its own requirement, a node owns only path nodes of it
  (`ReqFiltered`, `L1` of `OwnersInvariants`).
* **`parent_req_in_table`**: at the step of its parent's requirement too. The pair rule sends an entry
  `q` of `r` down to a parent `e` of `r` that owns `q`; the parent link gives `e`'s map node, and
  `ReqFiltered` on `e` gives `q`'s.
* **`owns_window_req`** (line form): a node of line `n+1` that owns `q` in any state of the line, at the
  step of its own requirement or of its parent's, owns there only the path node the window names.
* **`witness_fixes_clique`**: a witness at a clause step `L_p` (`p ≥ 1`) of a clique pins the value of
  every member at the variables of the literals `p` and `p-1` of the clause: they are the ones its window
  names. So an `L2` witness sees two literals of the clique at once, and an `L3` witness three
  (the third through its key): every entry it owns is a check of a trio.
-/

namespace AbsSatBin.GraphPath.Model.ClauseWitness

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.LineSem

variable (φ : Cnf)

section state
variable {g : GPathM} (c : AmbTriCore.ACtx g) (hrf : ReqFiltered (reqOf φ) g)
include c hrf

omit c in
/-- At the step of its own requirement, a node owns only path nodes of it. -/
theorem req_in_table (r : PathNodeId) (nr : PNodeM) (hr : g.node? r = some nr) (req : NodeId)
    (hreq : req ∈ reqOf φ r.id) (q : PathNodeId) (hq : q ∈ nr.owners) (hqs : q.id.step = req.step) :
    q.id = req :=
  hrf nr (List.mem_of_find?_eq_some hr) req (by rw [node?_id_eq g r nr hr]; exact hreq) q hq hqs

/-- **At the step of its parent's requirement, a node owns only path nodes of it.** -/
theorem parent_req_in_table (r : PathNodeId) (nr : PNodeM) (hr : g.node? r = some nr) (hr1 : 1 ≤ r.id.step)
    (b : NodeId) (hb : r.parent_id = some b) (req : NodeId) (hreq : req ∈ reqOf φ b)
    (q : PathNodeId) (hq : q ∈ nr.owners) (hqs : q.id.step = req.step) : q.id = req := by
  have hk := c.pc.ker
  obtain ⟨nq, hnq⟩ := hk.isNode_owner r nr hr q hq
  have hbelow : r.id.step < g.current_step := by
    have := c.pc.below nr (List.mem_of_find?_eq_some hr); rw [node?_id_eq g r nr hr] at this; exact this
  -- idx: adjacent gpath rows (one row per map step, bin map too)
  obtain ⟨e, her, heq, hes⟩ := hk.pair r nr q nq hr hnq hq (r.id.step - 1) (by omega) (by omega)
  obtain ⟨hepar, ne, hne⟩ := KernelSplit.parent_of_owner c.pc r nr hr hr1 e her hes
  have hpm := c.rc.pmp nr (List.mem_of_find?_eq_some hr) e hepar
  rw [node?_id_eq g r nr hr, hb] at hpm
  have heb : e.id = b := Option.some.inj hpm
  have hqe : q ∈ ne.owners := hk.sym q nq e ne hnq hne heq
  exact req_in_table φ hrf e ne hne req (by rw [heb]; exact hreq) q hqe hqs
end state

section line
variable (hbd : Bounded φ) (n : Nat)
include hbd

/-- **Line form**: a node of line `n+1` that owns `q`, at the step of its own requirement or of its
parent's, owns there only the path node its window names. -/
theorem owns_window_req (r q : PathNodeId) (h : Owns φ (n + 1) r q) (hr : r.id.step ≤ (n : Int))
    (hq : q.id.step ≤ (n : Int)) (req : NodeId)
    (hreq : req ∈ reqOf φ r.id ∨ (1 ≤ r.id.step ∧ ∃ b, r.parent_id = some b ∧ req ∈ reqOf φ b))
    (hqs : q.id.step = req.step) : q.id = req := by
  obtain ⟨kv', hkv', nr, hnr, hqr⟩ := h
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn', hqn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').2 r nr hnr q hqr
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hreach := reachable_of_mapReachable φ hbd kv.2 hok.reach
  have hrf : ReqFiltered (reqOf φ) (filterAll kv.2 (reqOf φ kv'.1)) :=
    filterAll_preserves_ReqFiltered (reqOf φ) (L1 (reqOf φ) (isProhibited φ) hreach) _
  obtain ⟨nF, hnF, ho⟩ := upF_old φ kv.2 kv'.1 hdst c hv r n' hn' (by omega)
  have hqF := ho q hqn' (by omega)
  rcases hreq with hreq | ⟨hr1, b, hb, hreq⟩
  · exact req_in_table φ hrf r nF hnF req hreq q hqF hqs
  · exact parent_req_in_table φ c hrf r nF hnF hr1 b hb req hreq q hqF hqs

/-- **A witness at a clause step fixes the clique's literals.** A witness `r` of a clique `Q` at step
`L_p` of a clause names in its window the values of literals `p` and `p-1`; every member of `Q` at the
step of one of those variables is the path node the window names. -/
theorem witness_fixes_clique (Q : List PathNodeId) (r : PathNodeId) (hr : r.id.step ≤ (n : Int))
    (hrQ : ∀ q ∈ Q, Owns φ (n + 1) r q) (hQs : ∀ q ∈ Q, q.id.step ≤ (n : Int)) (req : NodeId)
    (hreq : req ∈ reqOf φ r.id ∨ (1 ≤ r.id.step ∧ ∃ b, r.parent_id = some b ∧ req ∈ reqOf φ b)) :
    ∀ q ∈ Q, q.id.step = req.step → q.id = req :=
  fun q hq hqs => owns_window_req φ hbd n r q (hrQ q hq) hr (hQs q hq) req hreq hqs

end line

-- ============================================================
-- Two cases of `ClauseKey` that the window rule settles
-- ============================================================

/-- At a clause step the requirement of `⟨k, i⟩` is the variable node `⟨s, i⟩`, with `s` fixed by `k`. -/
theorem reqOf_clause (k : Int) (hlo : midFusion φ < k) (hhi : k < fusionTop φ) :
    ∃ s : Int, ∀ i, reqOf φ ⟨k, i⟩ = [⟨s, i⟩] := by
  obtain ⟨c, p, _, hc⟩ := clauseOf_isSome φ k hlo hhi
  refine ⟨(litAt c p).binStep, fun i => ?_⟩
  have hm0 : (0 : Int) < midFusion φ := by simp only [midFusion]; omega
  unfold reqOf
  dsimp only
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k < midFusion φ) by omega),
    if_neg (show ¬ (k = midFusion φ) by omega), if_neg (show ¬ (fusionTop φ ≤ k) by omega), hc]

section cases
variable (hbd : Bounded φ) (n : Nat)
include hbd

/-- **Case A: the clique holds a variable value that makes a literal of the clause true.** Every witness
owns it, so they all agree on that literal. -/
theorem clauseKey_trueVar (hL3 : isL3 φ ((n : Int) + 1) = true) (Q : List PathNodeId) (R : List NodeId)
    (hW : LWit φ (n + 1) Q R) (q : PathNodeId) (hqQ : q ∈ Q) (k : Int)
    (hk : k = (n : Int) + 1 ∨ k = (n : Int) ∨ k = (n : Int) - 1) (hq : q.id ∈ reqOf φ ⟨k, 1⟩) :
    ∃ E ∈ ClauseKey.keyOpts φ n, ClauseKey.OldWit φ n Q R E := by
  have hqs : q.id.step < k := reqOf_backward φ hbd _ _ hq
  have hkn : k ≤ (n : Int) + 1 := by omega
  refine ⟨reqOf φ ⟨k, 1⟩, ?_, fun l h0 hl => ?_⟩
  · simp only [ClauseKey.keyOpts, List.mem_cons, List.not_mem_nil, or_false]
    rcases hk with e | e | e <;> rw [e] <;> simp
  · obtain ⟨r, hrs, hrn, hrQ, hrR⟩ := hW l h0 (by push_cast; omega)
    refine ⟨r, hrs, hrn, hrQ, hrR, fun m hm => ?_⟩
    obtain ⟨kv, hkv, nJ, hnJ, hqJ⟩ := owns_old φ hbd n r q (hrQ q hqQ) (by omega) (by omega)
    have hlo : midFusion φ < k := by
      obtain ⟨_, h1, _⟩ := ClauseKey.l3_facts φ n hL3; omega
    have hhi : k < fusionTop φ := by
      obtain ⟨_, _, h3⟩ := ClauseKey.l3_facts φ n hL3; omega
    obtain ⟨s, hs⟩ := reqOf_clause φ k hlo hhi
    rw [hs] at hm hq
    rw [List.mem_singleton.mp hm, ← List.mem_singleton.mp hq]
    exact ⟨kv, hkv, nJ, hnJ, q, hqJ, rfl⟩

/-- **Case B: the clique holds the three variable values that make the literals of the clause false.**
Then it has no witness at `L2`: a witness there names `L1 = L2 = 0` in its window, so it is in no piece of
key `0`; in a piece of key `1` the requirement filter leaves only the value that makes the third literal
true, and the witness cannot own the other one. -/
theorem clauseKey_allFalse (hL3 : isL3 φ ((n : Int) + 1) = true) (Q : List PathNodeId) (R : List NodeId)
    (hW : LWit φ (n + 1) Q R) (q1 q2 q3 : PathNodeId) (h1Q : q1 ∈ Q) (h2Q : q2 ∈ Q) (h3Q : q3 ∈ Q)
    (h1 : q1.id ∈ reqOf φ ⟨(n : Int) - 1, 0⟩) (h2 : q2.id ∈ reqOf φ ⟨(n : Int), 0⟩)
    (h3 : q3.id ∈ reqOf φ ⟨(n : Int) + 1, 0⟩) : False := by
  obtain ⟨hn, hmid, htop⟩ := ClauseKey.l3_facts φ n hL3
  have hm0 : (0 : Int) < midFusion φ := by simp only [midFusion]; omega
  obtain ⟨s1, hs1⟩ := reqOf_clause φ ((n : Int) - 1) (by omega) (by omega)
  obtain ⟨s2, hs2⟩ := reqOf_clause φ (n : Int) (by omega) (by omega)
  obtain ⟨s3, hs3⟩ := reqOf_clause φ ((n : Int) + 1) (by omega) (by omega)
  rw [hs1, List.mem_singleton] at h1
  rw [hs2, List.mem_singleton] at h2
  rw [hs3, List.mem_singleton] at h3
  have hb1 := reqOf_backward φ hbd ⟨(n : Int) - 1, 0⟩ ⟨s1, 0⟩ (by rw [hs1]; exact List.mem_singleton_self _)
  have hb2 := reqOf_backward φ hbd ⟨(n : Int), 0⟩ ⟨s2, 0⟩ (by rw [hs2]; exact List.mem_singleton_self _)
  have hb3 := reqOf_backward φ hbd ⟨(n : Int) + 1, 0⟩ ⟨s3, 0⟩ (by rw [hs3]; exact List.mem_singleton_self _)
  have hq1s : q1.id.step = s1 := by rw [h1]
  have hq2s : q2.id.step = s2 := by rw [h2]
  have hq3s : q3.id.step = s3 := by rw [h3]
  simp only at hb1 hb2 hb3
  -- the witness at `L2`
  obtain ⟨r, hrs, hrn, hrQ, _⟩ := hW (n : Int) (by omega) (by push_cast; omega)
  -- its own literal is `L2 = 0`
  have hrid : r.id = ⟨(n : Int), 0⟩ := by
    have e : r.id = ⟨(n : Int), r.id.index⟩ := by rw [← hrs]
    have := owns_window_req φ hbd n r q2 (hrQ q2 h2Q) (by omega) (by omega) ⟨s2, r.id.index⟩
      (Or.inl (by rw [e, hs2]; exact List.mem_singleton_self _)) hq2s
    rw [h2] at this
    rw [e, ← congrArg NodeId.index this]
  -- its parent's literal is `L1 = 0`
  have hrpar : r.parent_id = some ⟨(n : Int) - 1, 0⟩ := by
    obtain ⟨b, hb, hbs⟩ : ∃ b : NodeId, r.parent_id = some b ∧ b.step = (n : Int) - 1 := by
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hnode : Node φ (k + 1) r := by rw [← hk]; exact node_old φ hbd n r hrn (by omega)
      obtain ⟨_, _, p, hps, hrp, _⟩ := top_node φ hbd k r hnode (by rw [hrs, hk]; push_cast; rfl)
      exact ⟨p.id, hrp, by rw [hps, hk]; push_cast; omega⟩
    have e : b = ⟨(n : Int) - 1, b.index⟩ := by rw [← hbs]
    have := owns_window_req φ hbd n r q1 (hrQ q1 h1Q) (by omega) (by omega) ⟨s1, b.index⟩
      (Or.inr ⟨by omega, b, hb, by rw [e, hs1]; exact List.mem_singleton_self _⟩) hq1s
    rw [h1] at this
    rw [hb, e, ← congrArg NodeId.index this]
  -- the entry `r → q3` lives in a piece; neither key allows it
  obtain ⟨kv', hkv', nr, hnr, hq3r⟩ := hrQ q3 h3Q
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn', hqn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').2 r nr hnr q3 hq3r
  obtain ⟨hok, hdst, hcs, hdm, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  rw [ClauseKey.mapNodes_l3 φ n hL3] at hdm
  rcases List.mem_cons.mp hdm with e0 | e1
  · exact ClauseKey.no00_key0 φ hbd n hL3 kv hkv kv'.1 hd hv e0 r n' hn' hrid hrpar
  · have e1 := List.mem_singleton.mp e1
    have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
    obtain ⟨nF, hnF, ho⟩ := upF_old φ kv.2 kv'.1 hdst c hv r n' hn' (by omega)
    have hq3F := ho q3 hqn' (by omega)
    have hgow := c.pc.ker.own r nF hnF q3 hq3F
    rw [e1, hs3] at hgow
    have := ReqFilter.req_id kv.2 ⟨s3, 1⟩ q3 hgow hq3s
    rw [h3] at this
    have hi := congrArg NodeId.index this
    simp only at hi
    omega

end cases

/-- info: 'AbsSatBin.GraphPath.Model.ClauseWitness.clauseKey_trueVar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms clauseKey_trueVar

/-- info: 'AbsSatBin.GraphPath.Model.ClauseWitness.clauseKey_allFalse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms clauseKey_allFalse

/-- info: 'AbsSatBin.GraphPath.Model.ClauseWitness.witness_fixes_clique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms witness_fixes_clique

end AbsSatBin.GraphPath.Model.ClauseWitness
