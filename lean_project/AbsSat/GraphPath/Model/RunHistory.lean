-- lean_project/AbsSat/GraphPath/Model/RunHistory.lean
import AbsSat.GraphPath.Model.ClausePins

/-!
# The core in the language of the history

The run builds each state by uniting the branches of assignments. Two facts about that history are
already proved: every genuine path through a send's source and destination is in the sent state
(`RunNoBorrow.send_complete`), and every path of a state is genuine (`RunNoBorrow.genuine_of_chain`).
So the construction invariant at a send says exactly this: **every entry towards a literal is explained by
a partial solution through the source key and the destination.**

* **`SentWitness`** — that statement, with no reference to pins, weak requirements or the review.
* **`soundAt_sent_of_witness`**, **`witness_of_soundAt_sent`** — it is equivalent to the invariant on the
  sent state (nothing is lost in the translation).
* **`sat_of_sentWitness`** — the verdict under it, by induction over the run.
* **`owns_iff_witness`** — with the invariant, a table entry towards a literal *is* the existence of such a
  partial solution: the tables are the compatibility relation of the partial solutions.
* **`ClauseWitness`**, **`sat_of_clauseWitness`** — every send that is not a clause row is free (no
  requirement, negation at the top step, weak requirements), so the core is only needed at the clause rows.
-/

namespace AbsSat.GraphPath.Model.RunHistory

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_init LineInv_steps)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.BranchLines (sent sendToW_eq advance_inv)
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep LineSoundAt lineSoundAt_insertPure lineSoundAt_init)
open AbsSat.GraphPath.Model.RunNoBorrow (Genuine send_complete)

variable (φ : Cnf)

/-- **The core, in the history's own terms.** At a send of the run, every entry of the sent state towards a
literal step lies on the branch of a partial solution (all clauses below the destination satisfied) that
passes the source key and the destination. -/
def SentWitness : Prop :=
  ∀ (m : Nat) (kv : NodeId × GPathM), kv ∈ pureStepsW φ m (pureInit φ) → (m : Int) + 2 ≤ stepCount φ →
    SoundAt (LitStep φ) kv.2 →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index, isValid (sent φ kv.2 d) = true →
      ∀ x n, (sent φ kv.2 d).node? x = some n → 0 ≤ x.id.step → x.id.step < (sent φ kv.2 d).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (sent φ kv.2 d).current_step → LitStep φ q.id.step →
          q ∈ n.owners →
          ∃ sel, Genuine φ ((m : Int) + 2) sel ∧ (sel (m : Int)).id = kv.1 ∧ (sel ((m : Int) + 1)).id = d ∧
            sel x.id.step = x ∧ sel q.id.step = q

/-- A witness is a path of the sent state. -/
theorem soundAt_sent_of_witness (hwf : WF φ) (hS : SentWitness φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ)) (ht : SoundAt (LitStep φ) kv.2)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hval : isValid (sent φ kv.2 d) = true) :
    SoundAt (LitStep φ) (sent φ kv.2 d) := by
  intro x n hx hx0 hx1 q hq0 hq1 hL hqn
  obtain ⟨sel, hgen, hsrc, htop, hsx, hsq⟩ := hS m kv hkv hm ht d hd hval x n hx hx0 hx1 q hq0 hq1 hL hqn
  exact ⟨sel, send_complete φ hwf m hm kv hkv d hd hval sel hgen hsrc htop, hsx, hsq⟩

theorem pureStepsW_succ : ∀ (n : Nat) (line : PureLine),
    pureStepsW φ (n + 1) line = pureAdvanceW φ (pureStepsW φ n line)
  | 0, _ => rfl
  | n + 1, line => pureStepsW_succ n (pureAdvanceW φ line)

/-- **Every state of the run keeps the invariant**, given the core. -/
theorem lineSound_of_witness (hwf : WF φ) (hS : SentWitness φ) :
    ∀ (m : Nat), (m : Int) + 1 ≤ stepCount φ → LineSoundAt φ (pureStepsW φ m (pureInit φ)) := by
  intro m
  induction m with
  | zero => intro _; exact lineSoundAt_init φ
  | succ m ih =>
    intro hm
    have hL := ih (by omega)
    rw [pureStepsW_succ]
    refine advance_inv φ (LineSoundAt φ) _ ?_ (fun _ h => absurd h List.not_mem_nil)
    intro kv hkv d hd acc hacc
    rw [sendToW_eq]
    split
    · next hv =>
      exact lineSoundAt_insertPure φ acc d _ hacc
        (soundAt_sent_of_witness φ hwf hS m (by omega) kv hkv (hL kv hkv) d hd hv)
    · exact hacc

/-- **The verdict from the history's core.** -/
theorem sat_of_sentWitness (hwf : WF φ) (hS : SentWitness φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (AggressiveReview.filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  RunInhabited.sat_of_lineSound φ hwf
    (lineSound_of_witness φ hwf hS _ (by have := ConservationCore.stepCount_pos φ; omega)) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.RunHistory.sat_of_sentWitness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_sentWitness

/-- **Nothing is lost in the translation**: the invariant on a sent state gives the witnesses, since every
path of the sent state is genuine and passes the new top node `(d, key)`. -/
theorem witness_of_soundAt_sent (hwf : WF φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ))
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hval : isValid (sent φ kv.2 d) = true)
    (hs : SoundAt (LitStep φ) (sent φ kv.2 d)) :
    ∀ x n, (sent φ kv.2 d).node? x = some n → 0 ≤ x.id.step → x.id.step < (sent φ kv.2 d).current_step →
      ∀ q, 0 ≤ q.id.step → q.id.step < (sent φ kv.2 d).current_step → LitStep φ q.id.step →
        q ∈ n.owners →
        ∃ sel, Genuine φ ((m : Int) + 2) sel ∧ (sel (m : Int)).id = kv.1 ∧ (sel ((m : Int) + 1)).id = d ∧
          sel x.id.step = x ∧ sel q.id.step = q := by
  intro x n hx hx0 hx1 q hq0 hq1 hL hqn
  have hl := LineInv_steps φ hwf m 0 (pureInit φ) (LineInv_init φ hwf)
  rw [show (0 : Int) + (m : Int) = m by omega] at hl
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  have hmS := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv d hd hval
  -- the sent state is the filtered state with the new node on top
  obtain ⟨F, hFdef⟩ : ∃ F, F = AggressiveReview.filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d))
      (reqOfCnf φ d) := ⟨_, rfl⟩
  have hkF : Keeps kv.2 F := by
    rw [hFdef]; exact Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have hsentF : sent φ kv.2 d = GPathM.up F d "" := by rw [hFdef]; rfl
  have hvF : isValid F = true := by
    cases hc : isValid F with
    | true => rfl
    | false =>
      exfalso
      have he : GPathM.up F d "" = F := by unfold GPathM.up; rw [hc]; rfl
      rw [hsentF, he, hc] at hval; cases hval
  have hRF : ReadableAgg F := by
    rw [hFdef]
    exact ⟨_, _, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmkv.rctx, rfl⟩
  have rcF := RCtx_of_readableAgg F hRF
  have heq : sent φ kv.2 d = addNode F d "" := by rw [hsentF]; unfold GPathM.up; rw [hvF]; rfl
  have hstepF : F.current_step = (m : Int) + 1 := by rw [hkF.1.step_eq, hsok.step]
  have hcsS : (sent φ kv.2 d).current_step = (m : Int) + 2 := by
    rw [heq]; show F.current_step + 1 = _; rw [hstepF]; omega
  obtain ⟨sel, hsc, hsx, hsq⟩ := hs x n hx hx0 hx1 q hq0 hq1 hL hqn
  obtain ⟨a, hsat, hsel⟩ := RunNoBorrow.genuine_of_chain φ hwf m _ hmS hcsS (by rw [hcsS]; exact hm) sel hsc
  -- the top of every path is the new node `(d, key)`
  obtain ⟨hsome, hstep⟩ := hsc.chain.1.1 ((m : Int) + 1) (by omega) (by rw [hcsS]; omega)
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp hsome
  have hntid := node?_id_eq _ _ nt hnt
  have hnt' : nt ∈ (addNode F d "").nodes := by rw [← heq]; exact List.mem_of_find?_eq_some hnt
  have htop := RunNoBorrow.tops_addNode F d "" rcF.below nt hnt' (by rw [hntid, hstep, hstepF])
  rw [hntid, hkF.1.map_parent_eq, hsok.par] at htop
  obtain ⟨hid1, hpar1⟩ := hsel ((m : Int) + 1) (by omega) (by omega)
  rw [if_neg (by omega), htop, show (m : Int) + 1 - 1 = m by omega] at hpar1
  obtain ⟨hid0, _⟩ := hsel (m : Int) (by omega) (by omega)
  refine ⟨sel, ⟨a, hsat, hsel⟩, ?_, by rw [htop], hsx, hsq⟩
  rw [hid0]
  exact (Option.some.inj hpar1).symm

/-- **With the invariant, the tables towards the literals are exact, and they speak of assignments.** In a
sent state that keeps the invariant, `x` owns the literal-step node `q` iff some partial solution through
the source key and `d` passes both. -/
theorem owns_iff_witness (hwf : WF φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ))
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hval : isValid (sent φ kv.2 d) = true)
    (hs : SoundAt (LitStep φ) (sent φ kv.2 d)) (x : PathNodeId) (n : PNodeM)
    (hx : (sent φ kv.2 d).node? x = some n) (hx0 : 0 ≤ x.id.step)
    (hx1 : x.id.step < (sent φ kv.2 d).current_step) (q : PathNodeId) (hq0 : 0 ≤ q.id.step)
    (hq1 : q.id.step < (sent φ kv.2 d).current_step) (hL : LitStep φ q.id.step) :
    q ∈ n.owners ↔
      ∃ sel, Genuine φ ((m : Int) + 2) sel ∧ (sel (m : Int)).id = kv.1 ∧ (sel ((m : Int) + 1)).id = d ∧
        sel x.id.step = x ∧ sel q.id.step = q := by
  constructor
  · exact witness_of_soundAt_sent φ hwf m hm kv hkv d hd hval hs x n hx hx0 hx1 q hq0 hq1 hL
  · intro ⟨sel, hgen, hsrc, htop, hsx, hsq⟩
    exact Exactness.tablesComplete _ x n hx hx0 hx1 q hq0 hq1
      ⟨sel, send_complete φ hwf m hm kv hkv d hd hval sel hgen hsrc htop, hsx, hsq⟩

/-- **The core is exactly the history's statement**: at a send, the invariant on the sent state holds iff
every entry towards a literal is explained by a partial solution through the source key and `d`. -/
theorem soundAt_sent_iff (hwf : WF φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ))
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hval : isValid (sent φ kv.2 d) = true) :
    SoundAt (LitStep φ) (sent φ kv.2 d) ↔
      ∀ x n, (sent φ kv.2 d).node? x = some n → 0 ≤ x.id.step → x.id.step < (sent φ kv.2 d).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (sent φ kv.2 d).current_step → LitStep φ q.id.step →
          q ∈ n.owners →
          ∃ sel, Genuine φ ((m : Int) + 2) sel ∧ (sel (m : Int)).id = kv.1 ∧ (sel ((m : Int) + 1)).id = d ∧
            sel x.id.step = x ∧ sel q.id.step = q := by
  constructor
  · exact witness_of_soundAt_sent φ hwf m hm kv hkv d hd hval
  · intro hw x n hx hx0 hx1 q hq0 hq1 hL hqn
    obtain ⟨sel, hgen, hsrc, htop, hsx, hsq⟩ := hw x n hx hx0 hx1 q hq0 hq1 hL hqn
    exact ⟨sel, send_complete φ hwf m hm kv hkv d hd hval sel hgen hsrc htop, hsx, hsq⟩

/-- info: 'AbsSat.GraphPath.Model.RunHistory.soundAt_sent_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundAt_sent_iff

-- ============================================================
-- Only the clause rows need the history
-- ============================================================

/-- **The core at the clause rows.** At a send to a clause row, every entry of the sent state towards a
literal is explained by a partial solution through the source key and the row: an assignment that
satisfies every clause up to this one, takes the row's three literal values, and passes both ends. -/
def ClauseWitness : Prop :=
  ∀ (m : Nat) (kv : NodeId × GPathM), kv ∈ pureStepsW φ m (pureInit φ) → (m : Int) + 2 ≤ stepCount φ →
    SoundAt (LitStep φ) kv.2 →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index, litBlock φ < d.step → reqOfCnf φ d ≠ [] →
      isValid (sent φ kv.2 d) = true →
      ∀ x n, (sent φ kv.2 d).node? x = some n → 0 ≤ x.id.step → x.id.step < (sent φ kv.2 d).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (sent φ kv.2 d).current_step → LitStep φ q.id.step →
          q ∈ n.owners →
          ∃ sel, Genuine φ ((m : Int) + 2) sel ∧ (sel (m : Int)).id = kv.1 ∧ (sel ((m : Int) + 1)).id = d ∧
            sel x.id.step = x ∧ sel q.id.step = q

/-- **Every other send is free.** A send with no requirement only reviews; a negation node pins the top
step, which carries the key (`ClausePins.soundAt_pin_top`); the weak requirements change nothing
(`WeakNoop`). So the sent state keeps the invariant, and has its witnesses (`witness_of_soundAt_sent`). -/
theorem soundAt_sent_of_clauses (hwf : WF φ) (hC : ClauseWitness φ) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureStepsW φ m (pureInit φ)) (ht : SoundAt (LitStep φ) kv.2)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hval : isValid (sent φ kv.2 d) = true) :
    SoundAt (LitStep φ) (sent φ kv.2 d) := by
  have hl := LineInv_steps φ hwf m 0 (pureInit φ) (LineInv_init φ hwf)
  rw [show (0 : Int) + (m : Int) = m by omega] at hl
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  have hkey : kv.1.step = (m : Int) := mapNodes_step φ m kv.1 hsok.onMap
  have hmk : (⟨(m : Int), kv.1.index⟩ : NodeId) ∈ mapNodes φ m := by
    have hid : (⟨(m : Int), kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix => rw [hkv1] at hkey; simp only at hkey ⊢; rw [hkey]
    rw [hid]; exact hsok.onMap
  have hd' : d ∈ mapNodes φ ((m : Int) + 1) := mapSons_subset φ m kv.1.index hmk d (by rw [← hkey]; exact hd)
  have hdstep : d.step = (m : Int) + 1 := mapNodes_step φ ((m : Int) + 1) d hd'
  rcases reqOfCnf_shape φ d with h | h | ⟨c, _, hlb, h⟩
  · refine RunInhabited.soundAt_sent_of φ m kv hsok hmkv d hd hval (fun hvW => ?_)
    refine WeakNoop.soundAt_weak_send φ hwf m kv hsok hmkv d hd hvW (fun hvA => ?_)
    rw [h] at hvA ⊢; exact RunInhabited.soundAt_review _ kv.2 hmkv.rctx.nodup ht
  · refine RunInhabited.soundAt_sent_of φ m kv hsok hmkv d hd hval (fun hvW => ?_)
    refine WeakNoop.soundAt_weak_send φ hwf m kv hsok hmkv d hd hvW (fun hvA => ?_)
    rw [h] at hvA ⊢
    exact ClausePins.soundAt_pin_top φ m kv hsok hmkv ht _ (by show d.step - 1 = (m : Int); omega) hvA
  · intro x n hx hx0 hx1 q hq0 hq1 hL hqn
    obtain ⟨sel, hgen, hsrc, htop, hsx, hsq⟩ :=
      hC m kv hkv hm ht d hd hlb (by rw [h]; exact List.cons_ne_nil _ _) hval x n hx hx0 hx1 q hq0 hq1 hL hqn
    exact ⟨sel, send_complete φ hwf m hm kv hkv d hd hval sel hgen hsrc htop, hsx, hsq⟩

theorem lineSound_of_clauses (hwf : WF φ) (hC : ClauseWitness φ) :
    ∀ (m : Nat), (m : Int) + 1 ≤ stepCount φ → LineSoundAt φ (pureStepsW φ m (pureInit φ)) := by
  intro m
  induction m with
  | zero => intro _; exact lineSoundAt_init φ
  | succ m ih =>
    intro hm
    have hL := ih (by omega)
    rw [pureStepsW_succ]
    refine advance_inv φ (LineSoundAt φ) _ ?_ (fun _ h => absurd h List.not_mem_nil)
    intro kv hkv d hd acc hacc
    rw [sendToW_eq]
    split
    · next hv =>
      exact lineSoundAt_insertPure φ acc d _ hacc
        (soundAt_sent_of_clauses φ hwf hC m (by omega) kv hkv (hL kv hkv) d hd hv)
    · exact hacc

/-- **The verdict from the history's core at the clause rows.** -/
theorem sat_of_clauseWitness (hwf : WF φ) (hC : ClauseWitness φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (AggressiveReview.filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  RunInhabited.sat_of_lineSound φ hwf
    (lineSound_of_clauses φ hwf hC _ (by have := ConservationCore.stepCount_pos φ; omega)) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.RunHistory.sat_of_clauseWitness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_clauseWitness

end AbsSat.GraphPath.Model.RunHistory
