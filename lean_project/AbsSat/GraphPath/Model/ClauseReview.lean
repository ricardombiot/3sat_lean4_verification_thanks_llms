-- lean_project/AbsSat/GraphPath/Model/ClauseReview.lean
import AbsSat.GraphPath.Model.RunHistory

/-!
# What the review gives at a clause row, in terms of assignments

At a send from the key `p` (step `m`) to the clause row `d` (step `m + 1`), the machine pins the three
literal values of `d` and reviews. Call the result `F` (`pinnedAt`); the sent state is `F` with `d` on top.

* **`ClauseGlue`** — the core, with the row `d` gone: every entry `x → q` of `F` (towards a literal) is
  explained by **one** partial solution through `p`, `x` and `q` that **takes the three values of `d`**.
  `clauseWitness_of_glue` proves it gives `ClauseWitness`, so the verdict (`sat_of_clauseGlue`): a partial
  solution with the row's values satisfies the row's clause and its branch passes `d` (`extend_genuine`).
* **`clause_review`** (no hypothesis) — what the pinned review actually provides, in the same terms:
  1. **pins**: at the steps of `d`'s literals, `F` only has the pinned values;
  2. **pairs**: every entry of `F` with an end at a literal step is explained by a partial solution
     through `p` (`Explained`), and every node of `F` has an entry to each pinned value;
  3. **triangles**: every entry of `F` has, at **every** step below the key, a node owned both ways by
     both of its ends.

So the review closes the pairwise relation of partial solutions under triangles (path consistency), with the
pins in it. What `ClauseGlue` asks on top is to glue: from pairs and triangles, one solution.
-/

namespace AbsSat.GraphPath.Model.ClauseReview

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_init LineInv_steps)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.ConservationPrefix (SatBelow)
open AbsSat.GraphPath.Model.BranchLines (sent)
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Rel mem_bounds)
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep)
open AbsSat.GraphPath.Model.RunNoBorrow (Genuine)
open AbsSat.GraphPath.Model.RunHistory (ClauseWitness sat_of_clauseWitness)
open AbsSat.GraphPath.Model.AnchoredSurvive (SMP_filterAllAgg)
open AbsSat.GraphPath.Model.AggFixpoint (aggOk_reviewAgg)

variable (φ : Cnf)

/-- The pinned, reviewed state of a send, before `d` goes on top. -/
def pinnedAt (g : GPathM) (d : NodeId) : GPathM :=
  filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)

theorem sent_eq (g : GPathM) (d : NodeId) : sent φ g d = GPathM.up (pinnedAt φ g d) d "" := rfl

/-- **An explained pair**: a partial solution (clauses below `m + 1`) whose branch passes the key `p` at
step `m`, `a` and `b`. -/
def Explained (m : Nat) (p : NodeId) (a b : PathNodeId) : Prop :=
  ∃ sel, Genuine φ ((m : Int) + 1) sel ∧ (sel (m : Int)).id = p ∧ sel a.id.step = a ∧ sel b.id.step = b

theorem Explained.symm {m : Nat} {p : NodeId} {a b : PathNodeId} (h : Explained φ m p a b) :
    Explained φ m p b a := by
  obtain ⟨sel, h1, h2, h3, h4⟩ := h; exact ⟨sel, h1, h2, h4, h3⟩

-- ============================================================
-- The clause stage, from the send's data
-- ============================================================

/-- A clause row sits on a clause step. -/
theorem clause_of_row (d : NodeId) (hlb : litBlock φ < d.step) (hne : reqOfCnf φ d ≠ []) :
    ∃ j, j < φ.clauses.length ∧ d.step = clauseStep φ j := by
  rcases step_cases φ d.step with h | ⟨v, hv, h⟩ | ⟨v, hv, h⟩ | h | h | h
  · unfold litBlock at hlb; omega
  · rw [h] at hlb; unfold varStep litBlock at hlb; omega
  · rw [h] at hlb; unfold negStep litBlock at hlb; omega
  · omega
  · exact h
  · exact absurd (reqOfCnf_above φ d h) hne

theorem nVars_pos (hwf : WF φ) (j : Nat) (hj : j < φ.clauses.length) : 0 < φ.nVars := by
  obtain ⟨⟨h1, _, _⟩, _⟩ := hwf φ.clauses[j] (List.getElem_mem hj)
  omega

theorem index_bits (r : Int) (h0 : 0 ≤ r) (h7 : r ≤ 7) : 4 * b1 r + 2 * b2 r + b3 r = r := by
  unfold b1 b2 b3; omega

theorem bit_eq_of_sel {a : Assign} {l : Lit} {b : Int} (hl : l.v < φ.nVars)
    (h : selOfAssign φ a l.step = litReq l b) : bit (litVal a l) = b := by
  rw [selOfAssign_lit φ a l hl] at h
  exact (congrArg NodeId.index h)

theorem litVal_true_of_bit {a : Assign} {l : Lit} (h : bit (litVal a l) = 1) : litVal a l = true := by
  cases hl : litVal a l with
  | false => rw [hl] at h; exact absurd h (by decide)
  | true => rfl

/-- **A partial solution with the row's values passes the row.** Extend it by `(d, p)` at step `m + 1`: the
assignment satisfies the row's clause (the map builds no all-false row) and selects `d` there. -/
theorem extend_genuine (hwf : WF φ) (m : Nat) (p d : NodeId) (hd : d ∈ mapNodes φ ((m : Int) + 1))
    (hlb : litBlock φ < (m : Int) + 1) (hne : reqOfCnf φ d ≠ [])
    (sel : Int → PathNodeId) (hgen : Genuine φ ((m : Int) + 1) sel) (hp : (sel (m : Int)).id = p)
    (hpin : ∀ r ∈ reqOfCnf φ d, (sel r.step).id = r) :
    Genuine φ ((m : Int) + 2)
      (fun k => if k = (m : Int) + 1 then ⟨d, some p⟩ else sel k) := by
  obtain ⟨a, hsat, hsel⟩ := hgen
  have hdstep : d.step = (m : Int) + 1 := mapNodes_step φ ((m : Int) + 1) d hd
  obtain ⟨j, hj, hjs⟩ := clause_of_row φ d (by rw [hdstep]; exact hlb) hne
  have hc : φ.clauses[j]? = some φ.clauses[j] := List.getElem?_eq_getElem hj
  have hreqs := reqOfCnf_clause φ d j φ.clauses[j] hj hc hjs
  obtain ⟨⟨hv1, hv2, hv3⟩, _⟩ := hwf φ.clauses[j] (List.getElem_mem hj)
  have hon : d ∈ mapNodes φ (clauseStep φ j) := by rw [← hjs, hdstep]; exact hd
  obtain ⟨hi1, hi7⟩ := index_range_of_clauseNode φ j hj d hon
  -- the branch at a literal step of the row carries the row's bit
  have hlit : ∀ (l : Lit) (b : Int), l.v < φ.nVars → litReq l b ∈ reqOfCnf φ d → bit (litVal a l) = b := by
    intro l b hlv hmem
    have hs0 : 0 ≤ l.step := by unfold Lit.step; split <;> omega
    have hs1 : l.step < litBlock φ := by unfold Lit.step litBlock; split <;> omega
    have h1 : (sel l.step).id = litReq l b := hpin _ hmem
    rw [(hsel l.step hs0 (by omega)).1] at h1
    exact bit_eq_of_sel φ hlv h1
  have e1 := hlit _ _ hv1 (by rw [hreqs]; exact List.mem_cons_self)
  have e2 := hlit _ _ hv2 (by rw [hreqs]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have e3 := hlit _ _ hv3
    (by rw [hreqs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hrow : rowOf a φ.clauses[j] = d.index := by
    unfold rowOf; rw [e1, e2, e3]; exact index_bits d.index (by omega) hi7
  have hsatj : SatClause a φ.clauses[j] := by
    rcases bits_not_all_zero d.index hi1 hi7 with h | h | h
    · exact Or.inl (litVal_true_of_bit (by rw [e1, h]))
    · exact Or.inr (Or.inl (litVal_true_of_bit (by rw [e2, h])))
    · exact Or.inr (Or.inr (litVal_true_of_bit (by rw [e3, h])))
  have hseld : selOfAssign φ a ((m : Int) + 1) = d := by
    rw [← hdstep, hjs, selOfAssign_clause φ a j _ hj hc, hrow]
    cases d; simp only at hjs ⊢; rw [hjs]
  refine ⟨a, fun j' hj' hs => ?_, fun k h0 h1 => ?_⟩
  · by_cases hlt : clauseStep φ j' < (m : Int) + 1
    · exact hsat j' hj' hlt
    · have : j' = j := by
        have : clauseStep φ j' = clauseStep φ j := by rw [← hjs, hdstep]; omega
        unfold clauseStep at this; omega
      subst this; exact hsatj
  · dsimp only
    by_cases hk : k = (m : Int) + 1
    · rw [if_pos hk, hk, hseld, if_neg (by omega), show (m : Int) + 1 - 1 = m by omega,
        ← (hsel (m : Int) (by omega) (by omega)).1, hp]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hk]; exact hsel k h0 (by omega)

/-- **The core without the row.** At a send to a clause row, every entry of the pinned, reviewed state
towards a literal is explained by one partial solution through the key that takes the row's three values. -/
def ClauseGlue : Prop :=
  ∀ (m : Nat) (kv : NodeId × GPathM), kv ∈ pureStepsW φ m (pureInit φ) → (m : Int) + 2 ≤ stepCount φ →
    SoundAt (LitStep φ) kv.2 →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index, litBlock φ < d.step → reqOfCnf φ d ≠ [] →
      isValid (pinnedAt φ kv.2 d) = true →
      ∀ x n, (pinnedAt φ kv.2 d).node? x = some n →
        ∀ q, 0 ≤ q.id.step → q.id.step < (m : Int) + 1 → LitStep φ q.id.step → q ∈ n.owners →
          ∃ sel, Genuine φ ((m : Int) + 1) sel ∧ (sel (m : Int)).id = kv.1 ∧ sel x.id.step = x ∧
            sel q.id.step = q ∧ ∀ r ∈ reqOfCnf φ d, (sel r.step).id = r

/-- The facts of a send used below: the key's step, the destination's step, and the pinned state `F` under
the sent state. -/
theorem send_facts (hwf : WF φ) (m : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ))
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) :
    StateOkF φ m kv ∧ MInv φ kv.2 ∧ d ∈ mapNodes φ ((m : Int) + 1) ∧ d.step = (m : Int) + 1 := by
  have hl := LineInv_steps φ hwf m 0 (pureInit φ) (LineInv_init φ hwf)
  rw [show (0 : Int) + (m : Int) = m by omega] at hl
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hkey : kv.1.step = (m : Int) := mapNodes_step φ m kv.1 hsok.onMap
  have hmk : (⟨(m : Int), kv.1.index⟩ : NodeId) ∈ mapNodes φ m := by
    have hid : (⟨(m : Int), kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix => rw [hkv1] at hkey; simp only at hkey ⊢; rw [hkey]
    rw [hid]; exact hsok.onMap
  have hd' : d ∈ mapNodes φ ((m : Int) + 1) := mapSons_subset φ m kv.1.index hmk d (by rw [← hkey]; exact hd)
  exact ⟨hsok, hl.2 kv hkv, hd', mapNodes_step φ ((m : Int) + 1) d hd'⟩

theorem valid_pinned (g : GPathM) (d : NodeId) (hval : isValid (sent φ g d) = true) :
    isValid (pinnedAt φ g d) = true := by
  cases hc : isValid (pinnedAt φ g d) with
  | true => rfl
  | false =>
    exfalso
    have he : GPathM.up (pinnedAt φ g d) d "" = pinnedAt φ g d := by unfold GPathM.up; rw [hc]; rfl
    rw [sent_eq, he, hc] at hval; cases hval

/-- **The glue gives the core.** An entry of the sent state below the new top is an entry of `F`; the new
top owns exactly `F`'s nodes, and each of them owns itself. The glued solution, extended by the row, is the
witness. -/
theorem clauseWitness_of_glue (hwf : WF φ) (hG : ClauseGlue φ) : ClauseWitness φ := by
  intro m kv hkv hm ht d hd hlb hne hval x n hx hx0 hx1 q hq0 hq1 hL hqn
  obtain ⟨hsok, hmkv, hd', hdstep⟩ := send_facts φ hwf m kv hkv d hd
  have hvF := valid_pinned φ kv.2 d hval
  have hkF : Keeps kv.2 (pinnedAt φ kv.2 d) :=
    Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have hRF : ReadableAgg (pinnedAt φ kv.2 d) :=
    ⟨_, _, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmkv.rctx, rfl⟩
  have rcF := RCtx_of_readableAgg _ hRF
  have ctxF := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRF) hvF
  have heq : sent φ kv.2 d = addNode (pinnedAt φ kv.2 d) d "" := by
    rw [sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  have hstepF : (pinnedAt φ kv.2 d).current_step = (m : Int) + 1 := by rw [hkF.1.step_eq, hsok.step]
  have hcsS : (sent φ kv.2 d).current_step = (m : Int) + 2 := by
    rw [heq]; show (pinnedAt φ kv.2 d).current_step + 1 = _; rw [hstepF]; omega
  have hmp : (pinnedAt φ kv.2 d).map_parent = some kv.1 := by rw [hkF.1.map_parent_eq, hsok.par]
  have hqlt : q.id.step < (m : Int) + 1 := by
    rcases hL with h | h
    · rw [hdstep] at hlb; omega
    · omega
  -- every entry of `F` towards `q` gives the witness
  have main : ∀ x' n', (pinnedAt φ kv.2 d).node? x' = some n' → q ∈ n'.owners →
      ∃ sel, Genuine φ ((m : Int) + 2) sel ∧ (sel (m : Int)).id = kv.1 ∧ (sel ((m : Int) + 1)).id = d ∧
        sel x'.id.step = x' ∧ sel q.id.step = q := by
    intro x' n' hx' hqn'
    have hx'lt : x'.id.step < (m : Int) + 1 := by
      rw [← hstepF, ← node?_id_eq _ x' n' hx']; exact rcF.below n' (List.mem_of_find?_eq_some hx')
    obtain ⟨sel, hgen, hp, hsx, hsq, hpin⟩ :=
      hG m kv hkv hm ht d hd hlb hne hvF x' n' hx' q hq0 hqlt hL hqn'
    refine ⟨_, extend_genuine φ hwf m kv.1 d hd' (by rw [← hdstep]; exact hlb) hne sel hgen hp hpin,
      ?_, ?_, ?_, ?_⟩
    · show (if (m : Int) = (m : Int) + 1 then _ else sel (m : Int)).id = kv.1
      rw [if_neg (by omega)]; exact hp
    · show (if (m : Int) + 1 = (m : Int) + 1 then (⟨d, some kv.1⟩ : PathNodeId)
        else sel ((m : Int) + 1)).id = d
      rw [if_pos rfl]
    · show (if x'.id.step = (m : Int) + 1 then _ else sel x'.id.step) = x'
      rw [if_neg (by omega)]; exact hsx
    · show (if q.id.step = (m : Int) + 1 then _ else sel q.id.step) = q
      rw [if_neg (by omega)]; exact hsq
  have hnew : newPid (pinnedAt φ kv.2 d) d ≠ q := by
    intro h; rw [← h] at hqlt; simp only [newPid] at hqlt; omega
  by_cases hxt : x.id.step < (m : Int) + 1
  · -- below the top: an entry of `F`
    rw [heq] at hx
    obtain ⟨n0, hn0, rfl⟩ := addNode_node?_below _ d "" (by rw [hstepF, hdstep]) x n hx
      (by rw [hstepF]; exact hxt)
    rw [upMap_owners] at hqn
    rcases List.mem_append.mp hqn with h | h
    · exact main x n0 hn0 h
    · exact absurd (List.mem_singleton.mp h).symm hnew
  · -- the new top: it owns `F`'s global owners
    have hxs : x.id.step = (m : Int) + 1 := by rw [hcsS] at hx1; omega
    rw [heq] at hx
    have hmem : n ∈ (addNode (pinnedAt φ kv.2 d) d "").nodes := List.mem_of_find?_eq_some hx
    have hxid := node?_id_eq _ x n hx
    have htop := RunNoBorrow.tops_addNode _ d "" rcF.below n hmem (by rw [hxid, hxs, hstepF])
    have hxnew : x = newPid (pinnedAt φ kv.2 d) d := by rw [← hxid, htop]; rfl
    have hnn := addNode_node?_new (pinnedAt φ kv.2 d) d "" (by rw [hstepF, hdstep]) rcF.below
    rw [← hxnew, hx] at hnn
    cases hnn
    have hqg : q ∈ (pinnedAt φ kv.2 d).gowners := by
      simp only [addOwner, upNode, List.mem_append, List.mem_singleton] at hqn
      rcases hqn with h | h
      · exact h
      · exact absurd h.symm (by rw [hxnew]; exact hnew)
    obtain ⟨nq, hnq, hnqid⟩ := ctxF.gn q hqg
    have hq' : (pinnedAt φ kv.2 d).node? q = some nq := by
      rw [← hnqid]; exact node?_of_mem rcF.nodup nq hnq
    obtain ⟨sel, hgen, hp, htd, _, hsq⟩ := main q nq hq' (ctxF.self q nq hq')
    refine ⟨fun k => if k = (m : Int) + 1 then x else sel k, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨a, hsat, hsel⟩ := hgen
      refine ⟨a, hsat, fun k h0 h1 => ?_⟩
      dsimp only
      by_cases hk : k = (m : Int) + 1
      · rw [if_pos hk]
        have := hsel k h0 h1
        rw [hk] at this ⊢
        have hsk : sel ((m : Int) + 1) = x := by
          rw [hxnew]
          apply RunNoBorrow.pid_ext
          · rw [htd]; rfl
          · rw [(hsel _ (by omega) (by omega)).2, if_neg (by omega), show (m : Int) + 1 - 1 = m by omega,
              ← (hsel (m : Int) (by omega) (by omega)).1, hp]
            show _ = (pinnedAt φ kv.2 d).map_parent
            rw [hmp]
        rw [← hsk]; exact this
      · rw [if_neg hk]; exact hsel k h0 h1
    · show (if (m : Int) = (m : Int) + 1 then x else sel (m : Int)).id = kv.1
      rw [if_neg (by omega)]; exact hp
    · show (if (m : Int) + 1 = (m : Int) + 1 then x else sel ((m : Int) + 1)).id = d
      rw [if_pos rfl, hxnew]; rfl
    · show (if x.id.step = (m : Int) + 1 then x else _) = x
      rw [if_pos hxs]
    · show (if q.id.step = (m : Int) + 1 then x else sel q.id.step) = q
      rw [if_neg (by omega)]; exact hsq

/-- **The verdict from the glue.** -/
theorem sat_of_clauseGlue (hwf : WF φ) (hG : ClauseGlue φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_clauseWitness φ hwf (clauseWitness_of_glue φ hwf hG) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.ClauseReview.sat_of_clauseGlue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_clauseGlue

-- ============================================================
-- What the pinned review provides
-- ============================================================

/-- **A path of a line state is a partial solution through its key.** -/
theorem explained_of_realizes (hwf : WF φ) (m : Nat) (hm1 : 1 ≤ m) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hsok : StateOkF φ m kv) (hmkv : MInv φ kv.2) (a b : PathNodeId)
    (h : Realizes kv.2 a b) : Explained φ m kv.1 a b := by
  obtain ⟨sel, hsc, hsa, hsb⟩ := h
  have hcs : kv.2.current_step = ((m - 1 : Nat) : Int) + 2 := by rw [hsok.step]; omega
  have hgen := RunNoBorrow.genuine_of_chain φ hwf (m - 1) kv.2 hmkv hcs (by rw [hsok.step]; omega) sel hsc
  rw [show ((m - 1 : Nat) : Int) + 2 = (m : Int) + 1 by omega] at hgen
  obtain ⟨hsome, hstep⟩ := hsc.chain.1.1 (m : Int) (by omega) (by rw [hsok.step]; omega)
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp hsome
  have hntid := node?_id_eq _ _ nt hnt
  have htl := hmkv.tl nt (List.mem_of_find?_eq_some hnt) (by rw [hntid, hstep, hsok.step]; omega)
  rw [hntid, hsok.par] at htl
  exact ⟨sel, hgen, Option.some.inj htl, hsa, hsb⟩

/-- **What the review gives at a clause row, with no hypothesis.** In the pinned, reviewed state `F` of a
send from the key `p` to a clause row `d`:

1. **pins** — a node of `F` at the step of one of `d`'s literals is that literal's pinned value;
2. **pairs** — every node of `F` has an entry to each pinned value, and every entry with an end at a literal
   step is explained by a partial solution through `p`;
3. **triangles** — every entry has, at every step below the key's, a node owned both ways by both ends. -/
theorem clause_review (hwf : WF φ) (m : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ))
    (hm : (m : Int) + 2 ≤ stepCount φ) (ht : SoundAt (LitStep φ) kv.2)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hlb : litBlock φ < d.step)
    (hne : reqOfCnf φ d ≠ []) (hvF : isValid (pinnedAt φ kv.2 d) = true) :
    let F := pinnedAt φ kv.2 d
    F.current_step = (m : Int) + 1 ∧
    (∀ a, Mem F a → ∀ r ∈ reqOfCnf φ d, a.id.step = r.step → a.id = r) ∧
    (∀ a, Mem F a → ∀ r ∈ reqOfCnf φ d, ∃ b, Rel F a b ∧ b.id = r) ∧
    (∀ a b, Rel F a b → (LitStep φ a.id.step ∨ LitStep φ b.id.step) → Explained φ m kv.1 a b) ∧
    (∀ a b, Rel F a b → ∀ l, 0 ≤ l → l < (m : Int) + 1 →
      ∃ z, z.id.step = l ∧ Rel F a z ∧ Rel F z a ∧ Rel F b z ∧ Rel F z b) := by
  intro F
  obtain ⟨hsok, hmkv, hd', hdstep⟩ := send_facts φ hwf m kv hkv d hd
  obtain ⟨j, hj, hjs⟩ := clause_of_row φ d hlb hne
  have hn0 := nVars_pos φ hwf j hj
  have hm1 : 1 ≤ m := by rw [hdstep] at hlb; unfold litBlock at hlb; omega
  -- the structure of `F`
  have hcW := RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll kv.2 (weakReqOfCnf φ d)) hmkv.rctx
  obtain ⟨sW, pW, nW⟩ := WeakPairs.facts_filterWeakAll (weakReqOfCnf φ d) kv.2 hmkv.smp hmkv.pms hmkv.sn
  have hRF : ReadableAgg F := ⟨_, _, hcW, rfl⟩
  have adF := AdjacentOwners.adj_of_readable _ hRF hvF (AggInvariants.PMS_filterAllAgg _ _ pW)
    (AggInvariants.SN_filterAllAgg _ _ nW)
  have sup := sup_self F adF (aggOk_reviewAgg _ hvF) (SMP_filterAllAgg _ sW hcW.shape.notroot (reqOfCnf φ d))
  have prF : Pruned kv.2 F := Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
  have hcsF : F.current_step = (m : Int) + 1 := by rw [prF.step_eq, hsok.step]
  have pin : ∀ a, Mem F a → ∀ r ∈ reqOfCnf φ d, a.id.step = r.step → a.id = r := by
    intro a ha r hr hs
    have hg := (pruned_reviewAgg _).gowners_sub a (sup.gow a ha)
    exact (SeqPin.gowners_foldl_pin (reqOfCnf φ d) _ a hg).2 r hr hs
  -- the pinned steps lie inside the literal block
  have hreqs := reqOfCnf_clause φ d j φ.clauses[j] hj (List.getElem?_eq_getElem hj) hjs
  have hr0 : ∀ r ∈ reqOfCnf φ d, 0 ≤ r.step := by
    intro r hr
    rw [hreqs] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (show 0 ≤ Lit.step _; unfold Lit.step; split <;> omega)
  refine ⟨hcsF, pin, fun a ha r hr => ?_, fun a b hab hL => ?_, fun a b hab l h0 hl => ?_⟩
  · have hr1 := RunInhabited.reqOfCnf_lit φ hwf d r hr
    obtain ⟨v, hav, hvs⟩ := sup.cov a ha r.step (hr0 r hr) (by rw [hcsF]; rw [hdstep] at hlb; omega)
    have hvm : Mem F v := by obtain ⟨_, _, _, h⟩ := hav; exact h
    exact ⟨v, hav, pin v hvm r hr hvs⟩
  · -- an entry of `F` is an entry of the state it was sent from
    have key : ∀ a b, Rel F a b → LitStep φ b.id.step → Explained φ m kv.1 a b := by
      intro a b hab hLb
      obtain ⟨n, hn, hbn, hbm⟩ := hab
      have ham : Mem F a := ⟨n, hn⟩
      obtain ⟨n₀, hn₀, hid, hown, _⟩ := prF.nodes_derived n (List.mem_of_find?_eq_some hn)
      have hn₀' : kv.2.node? a = some n₀ := by
        rw [← node?_id_eq F a n hn, hid]; exact node?_of_mem hmkv.rctx.nodup n₀ hn₀
      obtain ⟨ha0, ha1⟩ := mem_bounds F adF ham
      obtain ⟨hb0, hb1⟩ := mem_bounds F adF hbm
      rw [hcsF] at ha1 hb1
      exact explained_of_realizes φ hwf m hm1 hm kv hsok hmkv a b
        (ht a n₀ hn₀' ha0 (by rw [hsok.step]; exact ha1) b hb0 (by rw [hsok.step]; exact hb1) hLb
          (hown b hbn))
    rcases hL with h | h
    · exact (key b a (sup.sym a b hab) h).symm
    · exact key a b hab h
  · obtain ⟨z, haz, hbz, hzs⟩ := sup.agg a b hab l h0 (by rw [hcsF]; exact hl)
    exact ⟨z, hzs, haz, sup.sym a z haz, hbz, sup.sym b z hbz⟩

/-- info: 'AbsSat.GraphPath.Model.ClauseReview.clause_review' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms clause_review

end AbsSat.GraphPath.Model.ClauseReview
