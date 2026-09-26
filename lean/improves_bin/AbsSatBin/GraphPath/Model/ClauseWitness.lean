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

-- ============================================================
-- Composition: extending the clique by the clause's variables
-- ============================================================

/-- The requirement of a clause step is a variable step. -/
theorem reqOf_clause_var (hbd : Bounded φ) (k : Int) (hlo : midFusion φ < k) (hhi : k < fusionTop φ) :
    ∃ s : Int, 0 < s ∧ s < midFusion φ ∧ ∀ i, reqOf φ ⟨k, i⟩ = [⟨s, i⟩] := by
  obtain ⟨s, hs⟩ := reqOf_clause φ k hlo hhi
  have hmem : (⟨s, 0⟩ : NodeId) ∈ reqOf φ ⟨k, 0⟩ := by rw [hs]; exact List.mem_singleton_self _
  have hback := reqOf_backward φ hbd _ _ hmem
  refine ⟨s, ?_, ?_, hs⟩
  all_goals
    unfold reqOf at hmem
    dsimp only at hmem
    have hm0 : (0 : Int) < midFusion φ := by simp only [midFusion]; omega
    rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k < midFusion φ) by omega),
      if_neg (show ¬ (k = midFusion φ) by omega), if_neg (show ¬ (fusionTop φ ≤ k) by omega)] at hmem
    split at hmem
    · exact absurd hmem List.not_mem_nil
    · next c p hc =>
      have e := congrArg NodeId.step (List.mem_singleton.mp hmem)
      simp only at e
      have hcm := mem_of_clauseOf φ k c p hc
      obtain ⟨b1, b2, b3⟩ := hbd c hcm
      have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
      have := lit_step_bounds φ (litAt c p) hv
      omega

/-- A node of line `n+1` at a variable step names one of its two values. -/
theorem var_node_value (n : Nat) (x : PathNodeId) (hx : Owns φ (n + 1) x x) (s : Int) (hxs : x.id.step = s)
    (h0 : 0 < s) (h1 : s < midFusion φ) : x.id = ⟨s, 0⟩ ∨ x.id = ⟨s, 1⟩ := by
  obtain ⟨kv, hkv, nx, hnx, _⟩ := hx
  have hok : StateOk φ ((n + 1 : Nat) : Int) kv := (lineOk φ (n + 1)).2 kv hkv
  have := nodesOnMap_of_mapReachable φ kv.2 hok.reach nx (List.mem_of_find?_eq_some hnx)
  rw [node?_id_eq _ x nx hnx, hxs,
    mapNodes_two φ s h0 (by omega) (by simp only [midFusion, fusionTop] at h1 ⊢; omega)] at this
  rcases List.mem_cons.mp this with e | e
  · exact Or.inl e
  · exact Or.inr (List.mem_singleton.mp e)

/-- **The clique can be extended by one node at step `l`, keeping its witnesses.** -/
def ExtAt (n : Nat) (l : Int) : Prop :=
  ∀ Q R, LClique φ (n + 1) Q → LWit φ (n + 1) Q R → (∀ q ∈ Q, q.id.step ≤ (n : Int)) →
    ∃ x : PathNodeId, x.id.step = l ∧ LClique φ (n + 1) (x :: Q) ∧ LWit φ (n + 1) (x :: Q) R

theorem oldWit_sub (n : Nat) (Q Q' : List PathNodeId) (R E : List NodeId) (hsub : ∀ q ∈ Q, q ∈ Q')
    (h : ClauseKey.OldWit φ n Q' R E) : ClauseKey.OldWit φ n Q R E := by
  intro l h0 hl
  obtain ⟨r, hrs, hrn, hrQ, hrR, hrE⟩ := h l h0 hl
  exact ⟨r, hrs, hrn, fun q hq => hrQ q (hsub q hq), hrR, hrE⟩

/-- **`ClauseKey ⇐` extension at the variable steps.** Extend the clique by the three variables of the
clause; if one takes the value that makes its literal true, every witness owns it
(`clauseKey_trueVar`); if the three make their literals false, there is no witness at `L2`
(`clauseKey_allFalse`). -/
theorem clauseKey_of_ext (hbd : Bounded φ) (n : Nat)
    (hext : ∀ l, 0 < l → l < midFusion φ → ExtAt φ n l) : ClauseKey.ClauseKey φ n := by
  intro hL3 Q R hQ hW hlow
  obtain ⟨hn, hmid, htop⟩ := ClauseKey.l3_facts φ n hL3
  obtain ⟨s1, h1a, h1b, hs1⟩ := reqOf_clause_var φ hbd ((n : Int) - 1) (by omega) (by omega)
  obtain ⟨s2, h2a, h2b, hs2⟩ := reqOf_clause_var φ hbd (n : Int) (by omega) (by omega)
  obtain ⟨s3, h3a, h3b, hs3⟩ := reqOf_clause_var φ hbd ((n : Int) + 1) (by omega) (by omega)
  obtain ⟨x1, hx1s, hQ1, hW1⟩ := hext s1 h1a h1b Q R hQ hW hlow
  have hlow1 : ∀ q ∈ x1 :: Q, q.id.step ≤ (n : Int) := by
    intro q hq; rcases List.mem_cons.mp hq with e | hq
    · rw [e, hx1s]; omega
    · exact hlow q hq
  obtain ⟨x2, hx2s, hQ2, hW2⟩ := hext s2 h2a h2b _ R hQ1 hW1 hlow1
  have hlow2 : ∀ q ∈ x2 :: x1 :: Q, q.id.step ≤ (n : Int) := by
    intro q hq; rcases List.mem_cons.mp hq with e | hq
    · rw [e, hx2s]; omega
    · exact hlow1 q hq
  obtain ⟨x3, hx3s, hQ3, hW3⟩ := hext s3 h3a h3b _ R hQ2 hW2 hlow2
  let Q3 := x3 :: x2 :: x1 :: Q
  have m3 : x3 ∈ Q3 := List.mem_cons_self
  have m2 : x2 ∈ Q3 := List.mem_cons_of_mem _ List.mem_cons_self
  have m1 : x1 ∈ Q3 := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hsub : ∀ q ∈ Q, q ∈ Q3 := fun q hq =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  have v1 := var_node_value φ n x1 (hQ3 x1 m1 x1 m1) s1 hx1s h1a h1b
  have v2 := var_node_value φ n x2 (hQ3 x2 m2 x2 m2) s2 hx2s h2a h2b
  have v3 := var_node_value φ n x3 (hQ3 x3 m3 x3 m3) s3 hx3s h3a h3b
  -- a true value: every witness owns it
  have viaTrue : ∀ x ∈ Q3, ∀ k : Int, (k = (n : Int) + 1 ∨ k = (n : Int) ∨ k = (n : Int) - 1) →
      x.id ∈ reqOf φ ⟨k, 1⟩ → ∃ E ∈ ClauseKey.keyOpts φ n, ClauseKey.OldWit φ n Q R E := by
    intro x hx k hk hxk
    obtain ⟨E, hE, hWE⟩ := clauseKey_trueVar φ hbd n hL3 Q3 R hW3 x hx k hk hxk
    exact ⟨E, hE, oldWit_sub φ n Q Q3 R E hsub hWE⟩
  rcases v1 with e1 | e1
  · rcases v2 with e2 | e2
    · rcases v3 with e3 | e3
      · exact (clauseKey_allFalse φ hbd n hL3 Q3 R hW3 x1 x2 x3 m1 m2 m3
          (by rw [e1, hs1]; exact List.mem_singleton_self _) (by rw [e2, hs2]; exact List.mem_singleton_self _)
          (by rw [e3, hs3]; exact List.mem_singleton_self _)).elim
      · exact viaTrue x3 m3 _ (Or.inl rfl) (by rw [e3, hs3]; exact List.mem_singleton_self _)
    · exact viaTrue x2 m2 _ (Or.inr (Or.inl rfl)) (by rw [e2, hs2]; exact List.mem_singleton_self _)
  · exact viaTrue x1 m1 _ (Or.inr (Or.inr rfl)) (by rw [e1, hs1]; exact List.mem_singleton_self _)

/-- **The reader decides `φ` when, at every third literal, cliques extend at the variable steps.** -/
theorem readerVerdictW_iff_of_ext (hbd : Bounded φ)
    (hext : ∀ n : Nat, (n : Int) + 1 < stepCount φ → ∀ l, 0 < l → l < midFusion φ → ExtAt φ n l) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  ClauseKey.readerVerdictW_iff_of_clauseKey φ hbd (fun n hn => clauseKey_of_ext φ hbd n (hext n hn))

/-- info: 'AbsSatBin.GraphPath.Model.ClauseWitness.readerVerdictW_iff_of_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_ext

/-- info: 'AbsSatBin.GraphPath.Model.ClauseWitness.witness_fixes_clique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms witness_fixes_clique

end AbsSatBin.GraphPath.Model.ClauseWitness
