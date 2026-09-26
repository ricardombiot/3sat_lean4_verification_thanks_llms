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

/-- info: 'AbsSatBin.GraphPath.Model.ClauseWitness.witness_fixes_clique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms witness_fixes_clique

end AbsSatBin.GraphPath.Model.ClauseWitness
