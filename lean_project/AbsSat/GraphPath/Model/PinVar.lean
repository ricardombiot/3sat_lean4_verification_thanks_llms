-- lean_project/AbsSat/GraphPath/Model/PinVar.lean
import AbsSat.GraphPath.Model.PinSend

/-!
# The union by key in the variable stage

Before the first clause, the only constraints are between a variable and its negation, and a node's
identifier names its parent. So nodes that are compatible two by two are compatible all together, and
pinning one value in a union by key gives nothing the sides do not.

* **A. Branches lose no partial solution** (`branch_carries`, `branch_line_complete`): the state of a branch
  at a key holds every genuine partial path through that key that agrees with the branch's pins.
-/

namespace AbsSat.GraphPath.Model.PinVar

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit insertPure key_inj)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF LineOkF CarriesF AlongAssignF Fsac prunes_Fsac
  LineOkF_pureAdvanceF)
open AbsSat.GraphPath.Model.ConservationPrefix (SatBelow satBelow_mono keepsBranch_Fsac_below
  CarriesF_pureAdvanceF_below initF_ok_below chainSound_alongF_below)
open AbsSat.GraphPath.Model.BranchRun (restrictLine)
open AbsSat.GraphPath.Model.PinHistory (branchLine branchLine_succ branchLine_inv mem_restrict)
open AbsSat.GraphPath.Model.RunNoBorrow (Genuine chainSound_congr eq_of_along genuine_restrict)
open AbsSat.GraphPath.Model.BranchLines (sent)

variable (φ : Cnf)

-- ============================================================
-- A. Branches lose no partial solution
-- ============================================================

/-- An assignment agrees with pins below `K`. -/
def Agrees (P : List NodeId) (a : Assign) (K : Int) : Prop :=
  ∀ r ∈ P, 0 ≤ r.step → r.step < K → selOfAssign φ a r.step = r

/-- The restriction keeps the entry at the assignment's node. -/
theorem carries_restrict (a : Assign) (P : List NodeId) (k : Int) (K : Int) (h0k : 0 ≤ k) (hk : k < K)
    (hag : Agrees φ P a K) (line : PureLine) (hc : CarriesF φ a (Fsac φ 0) reviewAgg k line) :
    CarriesF φ a (Fsac φ 0) reviewAgg k (restrictLine P k line) := by
  obtain ⟨g, hmem, hal, hcs⟩ := hc
  refine ⟨g, List.mem_filter.mpr ⟨hmem, List.all_eq_true.mpr fun r hr => ?_⟩, hal, hcs⟩
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  by_cases h : r.step = k
  · right
    rw [← h]; exact hag r hr (by omega) (by omega)
  · exact Or.inl h

/-- **A branch holds the assignment's partial branch**, for an assignment that satisfies the clauses below
`K` and agrees with the branch's pins. -/
theorem branch_carries (hwf : WF φ) (P : List NodeId) (a : Assign) (K : Int) (hK2 : K ≤ stepCount φ)
    (hs : SatBelow φ a K) (hag : Agrees φ P a K) :
    ∀ n : Nat, (n : Int) + 1 ≤ K → CarriesF φ a (Fsac φ 0) reviewAgg n (branchLine φ P n) := by
  intro n
  induction n with
  | zero =>
    intro hK
    obtain ⟨_, hc0⟩ := initF_ok_below φ a (Fsac φ 0) reviewAgg (satBelow_mono hs (by omega))
    exact carries_restrict φ a P 0 K (Int.le_refl 0) (by omega) hag _ hc0
  | succ n ih =>
    intro hK
    rw [branchLine_succ]
    have hl := (branchLine_inv φ hwf P n).1
    have hc := ih (by omega)
    have hadv := CarriesF_pureAdvanceF_below φ a (Fsac φ 0) reviewAgg hwf K hs (prunes_Fsac φ 0)
      (keepsBranch_Fsac_below φ a K hs 0) n (by omega) (by omega) (by omega) _ hl hc
    rw [ConservationImproves.advance_eq] at hadv
    exact carries_restrict φ a P _ K (by omega) (by omega) hag _ (by push_cast; exact hadv)

/-- A genuine path through pins spells an assignment that agrees with them. -/
theorem agrees_of_sel (P : List NodeId) (K : Int) (sel : Int → PathNodeId) (a : Assign)
    (hsel : ∀ k, 0 ≤ k → k < K → (sel k).id = selOfAssign φ a k ∧
      (sel k).parent_id = (if k = 0 then none else some (selOfAssign φ a (k - 1))))
    (hP : ∀ r ∈ P, 0 ≤ r.step → r.step < K → (sel r.step).id = r) : Agrees φ P a K :=
  fun r hr h0 h1 => ((hsel r.step h0 h1).1).symm.trans (hP r hr h0 h1)

/-- **A branch's state holds every genuine path through its key that agrees with the branch's pins.** -/
theorem branch_line_complete (hwf : WF φ) (P : List NodeId) (m : Nat) (hm : (m : Int) + 1 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m) (sel : Int → PathNodeId)
    (hgen : Genuine φ ((m : Int) + 1) sel) (htop : (sel (m : Int)).id = kv.1)
    (hP : ∀ r ∈ P, 0 ≤ r.step → r.step < (m : Int) + 1 → (sel r.step).id = r) : ChainSound kv.2 sel := by
  obtain ⟨a, hs, hsel⟩ := hgen
  have hl := branchLine_inv φ hwf P m
  obtain ⟨g, hmem, hal, hcs⟩ := branch_carries φ hwf P a ((m : Int) + 1) hm hs
    (agrees_of_sel φ P _ sel a hsel hP) m (Int.le_refl _)
  have hkey : selOfAssign φ a (m : Int) = kv.1 := by
    rw [← htop]; exact ((hsel m (by omega) (by omega)).1).symm
  have hsame := key_inj _ hl.1.1 (selOfAssign φ a (m : Int), g) hmem kv hkv hkey
  have hg : g = kv.2 := by rw [← hsame]
  rw [← hg]
  have hmg := hl.2 _ hmem
  obtain ⟨sel', hsc, hids⟩ := chainSound_alongF_below φ a (Fsac φ 0) reviewAgg hwf (prunes_Fsac φ 0)
    ((m : Int) + 1) (keepsBranch_Fsac_below φ a _ hs 0) g hal (by rw [hcs]; exact Int.le_refl _)
  have hpos : 0 < g.current_step := by rw [hcs]; omega
  exact chainSound_congr g sel sel' hsc hpos (eq_of_along φ g hmg.rctx.pmp sel sel' hsc a
    (fun k h0 h1 => (hids k h0 h1).1) (fun k h0 h1 => hsel k h0 (by rw [← hcs]; exact h1)))

open AbsSat.GraphPath.Model.ConservationCore (chainSound_up_of_prunedR SelParent)

/-- **A branch's send holds every genuine path through its source and destination** that agrees with the
branch's pins. -/
theorem branch_send_complete (hwf : WF φ) (P : List NodeId) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true)
    (sel : Int → PathNodeId) (hgen : Genuine φ ((m : Int) + 2) sel)
    (hsrc : (sel (m : Int)).id = kv.1) (htop : (sel ((m : Int) + 1)).id = d)
    (hP : ∀ r ∈ P, 0 ≤ r.step → r.step < (m : Int) + 1 → (sel r.step).id = r) :
    ChainSound (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") sel := by
  have hl := branchLine_inv φ hwf P m
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  have hsc := branch_line_complete φ hwf P m (by omega) kv hkv sel (genuine_restrict φ hgen (by omega)) hsrc hP
  obtain ⟨a, hs, hsel⟩ := hgen
  have hcs : kv.2.current_step = (m : Int) + 1 := hsok.step
  have hids : ∀ k, 0 ≤ k → k < kv.2.current_step →
      (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) := by
    intro k h0 h1
    obtain ⟨hid, hpar⟩ := hsel k h0 (by omega)
    refine ⟨hid, ?_⟩
    by_cases hz : k = 0
    · rw [if_pos hz] at hpar; exact Or.inl hpar
    · rw [if_neg hz] at hpar; exact Or.inr ⟨k - 1, hpar⟩
  have hdsel : d = selOfAssign φ a kv.2.current_step := by
    rw [hcs, ← htop]; exact (hsel _ (by omega) (by omega)).1
  have hmp : kv.2.map_parent = none ∨ ∃ j, kv.2.map_parent = some (selOfAssign φ a j) := by
    refine Or.inr ⟨m, ?_⟩
    rw [hsok.par, ← hsrc]; exact congrArg some (hsel m (by omega) (by omega)).1
  have hkeep := keepsBranch_Fsac_below φ a ((m : Int) + 2) hs 0 d kv.2 sel hsc hids hdsel (by omega)
  obtain ⟨sel', hs', hcur, hids'⟩ := chainSound_up_of_prunedR φ a AggressiveReview.reviewAgg hwf kv.2 _
    (prunes_Fsac φ 0 d kv.2) hsok.shape hmp sel hkeep hids ""
  have hsend : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" =
      AggressiveReview.upFilteringR AggressiveReview.reviewAgg (Fsac φ 0 d kv.2)
        (reqOfCnf φ (selOfAssign φ a kv.2.current_step)) (selOfAssign φ a kv.2.current_step) "" := by
    rw [← hdsel]; rfl
  rw [hsend]
  have hmh := ReaderAggRun.MInv_sent φ hwf m kv hsok hmkv d hd hval
  rw [hsend] at hmh
  have hpos : 0 < (AggressiveReview.upFilteringR AggressiveReview.reviewAgg (Fsac φ 0 d kv.2)
      (reqOfCnf φ (selOfAssign φ a kv.2.current_step)) (selOfAssign φ a kv.2.current_step) "").current_step := by
    rw [hcur]; omega
  refine chainSound_congr _ sel sel' hs' hpos (eq_of_along φ _ hmh.rctx.pmp sel sel' hs' a
    (fun k h0 h1 => (hids' k h0 (by rw [← hcur]; exact h1)).1)
    (fun k h0 h1 => hsel k h0 (by rw [hcur, hcs] at h1; exact h1)))

-- ============================================================
-- B. The variable stage is exact
-- ============================================================

open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep LineSoundAt lineSoundAt_insertPure lineSoundAt_init)
open AbsSat.GraphPath.Model.BranchLines (advance_inv sendToW_eq)

/-- **In the variable stage every send keeps the invariant** (no clause row is reached). -/
theorem adv_sound_var (hwf : WF φ) (P : List NodeId) (m : Nat) (hm : (m : Int) + 1 < litBlock φ)
    (hL : LineSoundAt φ (branchLine φ P m)) : LineSoundAt φ (pureAdvanceW φ (branchLine φ P m)) := by
  refine advance_inv φ (LineSoundAt φ) _ ?_ (fun _ h => absurd h List.not_mem_nil)
  intro kv hkv d hd acc hacc
  rw [sendToW_eq]
  split
  · next hval =>
    refine lineSoundAt_insertPure φ acc d _ hacc ?_
    have hl := branchLine_inv φ hwf P m
    have hsok : StateOkF φ m kv := hl.1.2 kv hkv
    have hmkv : MInv φ kv.2 := hl.2 kv hkv
    have ht : SoundAt (LitStep φ) kv.2 := hL kv hkv
    have hdstep := PinHistory.dstep_of φ m kv hsok d hd
    refine RunInhabited.soundAt_sent_of φ m kv hsok hmkv d hd hval (fun hvW => ?_)
    refine WeakNoop.soundAt_weak_send φ hwf m kv hsok hmkv d hd hvW (fun hvA => ?_)
    rcases reqOfCnf_shape φ d with h | h | ⟨c, _, hlb, h⟩
    · rw [h] at hvA ⊢; exact RunInhabited.soundAt_review _ kv.2 hmkv.rctx.nodup ht
    · rw [h] at hvA ⊢
      exact ClausePins.soundAt_pin_top φ m kv hsok hmkv ht _ (by show d.step - 1 = (m : Int); omega) hvA
    · rw [hdstep] at hlb
      exact absurd (Int.lt_trans hlb hm) (Int.lt_irrefl _)
  · exact hacc

/-- **Every branch state of the variable stage keeps the invariant**, with no hypothesis. -/
theorem branch_sound_var (hwf : WF φ) (P : List NodeId) :
    ∀ m : Nat, (m : Int) < litBlock φ → LineSoundAt φ (branchLine φ P m) := by
  intro m
  induction m with
  | zero =>
    intro _ kv hkv
    unfold branchLine at hkv
    exact lineSoundAt_init φ kv (mem_restrict (show kv ∈ restrictLine P 0 (pureInit φ) from hkv)).1
  | succ m ih =>
    intro hm kv hkv
    rw [branchLine_succ] at hkv
    exact adv_sound_var φ hwf P m (by omega) (ih (by omega)) kv (mem_restrict hkv).1

-- ============================================================
-- C. Gluing in the variable stage
-- ============================================================

/-- In the variable stage, the node an assignment picks at a step depends only on that step's variable. -/
theorem sel_local (a b : Assign) (k : Int) (h0 : 0 ≤ k) (hk : k < litBlock φ)
    (h : a (k / 2).toNat = b (k / 2).toNat) : selOfAssign φ a k = selOfAssign φ b k := by
  simp only [selOfAssign, if_neg (show ¬ k < 0 by omega), if_pos hk]
  split
  · rw [h]
  · next hodd => rw [show ((k - 1) / 2).toNat = (k / 2).toNat by omega, h]

theorem bit_inj {x y : Bool} (h : bit x = bit y) : x = y := by
  cases x <;> cases y <;> simp_all [bit]

/-- ... and it determines that variable's value. -/
theorem sel_det (a b : Assign) (k : Int) (h0 : 0 ≤ k) (hk : k < litBlock φ)
    (h : selOfAssign φ a k = selOfAssign φ b k) : a (k / 2).toNat = b (k / 2).toNat := by
  simp only [selOfAssign, if_neg (show ¬ k < 0 by omega), if_pos hk] at h
  split at h
  · exact bit_inj (congrArg NodeId.index h)
  · next hodd =>
    rw [show ((k - 1) / 2).toNat = (k / 2).toNat by omega] at h
    have := bit_inj (congrArg NodeId.index h)
    cases ha : a (k / 2).toNat <;> cases hb : b (k / 2).toNat <;> simp_all

/-- The glued assignment: `b₂` on the variable `u`, `b₁` elsewhere. -/
def glue (b₁ b₂ : Assign) (u : Nat) : Assign := fun w => if w = u then b₂ w else b₁ w

/-- **Where two assignments pick the same node, the glued one picks it too.** -/
theorem glue_agree (b₁ b₂ : Assign) (u : Nat) (k : Int) (h0 : 0 ≤ k) (hk : k < litBlock φ) (t : NodeId)
    (h₁ : selOfAssign φ b₁ k = t) (h₂ : selOfAssign φ b₂ k = t) : selOfAssign φ (glue b₁ b₂ u) k = t := by
  by_cases hu : (k / 2).toNat = u
  · rw [sel_local φ _ b₂ k h0 hk (by simp [glue, hu])]; exact h₂
  · rw [sel_local φ _ b₁ k h0 hk (by simp [glue, hu])]; exact h₁

theorem glue_self (b₁ b₂ : Assign) (k : Int) (h0 : 0 ≤ k) (hk : k < litBlock φ) :
    selOfAssign φ (glue b₁ b₂ (k / 2).toNat) k = selOfAssign φ b₂ k :=
  sel_local φ _ b₂ k h0 hk (by simp [glue])

/-- **A branch's send, with no validity hypothesis**: a genuine path through source and destination that
agrees with the pins makes the send valid and lies on it. -/
theorem branch_send_chain (hwf : WF φ) (P : List NodeId) (m : Nat) (hm : (m : Int) + 2 ≤ stepCount φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (sel : Int → PathNodeId) (hgen : Genuine φ ((m : Int) + 2) sel)
    (hsrc : (sel (m : Int)).id = kv.1) (htop : (sel ((m : Int) + 1)).id = d)
    (hP : ∀ r ∈ P, 0 ≤ r.step → r.step < (m : Int) + 1 → (sel r.step).id = r) :
    isValid (sent φ kv.2 d) = true ∧ ChainSound (sent φ kv.2 d) sel := by
  have hl := branchLine_inv φ hwf P m
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hsc := branch_line_complete φ hwf P m (by omega) kv hkv sel (genuine_restrict φ hgen (by omega)) hsrc hP
  have hgen' := hgen
  obtain ⟨a, hs, hsel⟩ := hgen'
  have hcs : kv.2.current_step = (m : Int) + 1 := hsok.step
  have hids : ∀ k, 0 ≤ k → k < kv.2.current_step →
      (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) := by
    intro k h0 h1
    obtain ⟨hid, hpar⟩ := hsel k h0 (by omega)
    refine ⟨hid, ?_⟩
    by_cases hz : k = 0
    · rw [if_pos hz] at hpar; exact Or.inl hpar
    · rw [if_neg hz] at hpar; exact Or.inr ⟨k - 1, hpar⟩
  have hdsel : d = selOfAssign φ a kv.2.current_step := by
    rw [hcs, ← htop]; exact (hsel _ (by omega) (by omega)).1
  have hmp : kv.2.map_parent = none ∨ ∃ j, kv.2.map_parent = some (selOfAssign φ a j) := by
    refine Or.inr ⟨m, ?_⟩
    rw [hsok.par, ← hsrc]; exact congrArg some (hsel m (by omega) (by omega)).1
  have hkeep := keepsBranch_Fsac_below φ a ((m : Int) + 2) hs 0 d kv.2 sel hsc hids hdsel (by omega)
  obtain ⟨sel', hs', _, _⟩ := chainSound_up_of_prunedR φ a AggressiveReview.reviewAgg hwf kv.2 _
    (prunes_Fsac φ 0 d kv.2) hsok.shape hmp sel hkeep hids ""
  have hsend : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" =
      AggressiveReview.upFilteringR AggressiveReview.reviewAgg (Fsac φ 0 d kv.2)
        (reqOfCnf φ (selOfAssign φ a kv.2.current_step)) (selOfAssign φ a kv.2.current_step) "" := by
    rw [← hdsel]; rfl
  have hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true := by
    rw [hsend]; exact PickInduction.isValid_of_ChainG _ sel' hs'.chain
  exact ⟨hval, branch_send_complete φ hwf P m hm kv hkv d hd hval sel hgen hsrc htop hP⟩

open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Rel Embedded mem_bounds)
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.AggFixpoint (aggOk_reviewAgg)
open AbsSat.GraphPath.Model.PinHistory (PinIdsBelow)

/-- The facts a path of a state of the next line carries: its assignment, the key on top, the pins. -/
theorem path_facts (hwf : WF φ) (P : List NodeId) (m : Nat) (p : NodeId) (J : GPathM)
    (hsJ : StateOkF φ ((m : Int) + 1) (p, J)) (hmJ : MInv φ J) (hpins : PinIdsBelow P ((m : Int) + 1) J)
    (hle : (m : Int) + 2 ≤ stepCount φ) (s : Int → PathNodeId) (hsc : ChainSound J s) :
    ∃ b : Assign, (∀ k, 0 ≤ k → k < (m : Int) + 2 → (s k).id = selOfAssign φ b k ∧
        (s k).parent_id = (if k = 0 then none else some (selOfAssign φ b (k - 1)))) ∧
      selOfAssign φ b ((m : Int) + 1) = p ∧
      (∀ r ∈ P, 0 ≤ r.step → r.step < (m : Int) + 1 → selOfAssign φ b r.step = r) := by
  have hcs : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  obtain ⟨b, _, hsel⟩ := RunNoBorrow.genuine_of_chain φ hwf m J hmJ hcs (by rw [hcs]; exact hle) s hsc
  have node : ∀ k, 0 ≤ k → k < (m : Int) + 2 → ∃ n ∈ J.nodes, n.id = s k ∧ (s k).id.step = k := by
    intro k h0 h1
    obtain ⟨hsome, hstep⟩ := hsc.chain.1.1 k h0 (by rw [hcs]; exact h1)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨n, List.mem_of_find?_eq_some hn, node?_id_eq _ _ n hn, hstep⟩
  refine ⟨b, hsel, ?_, fun r hr h0 h1 => ?_⟩
  · obtain ⟨n, hn, hid, hst⟩ := node ((m : Int) + 1) (by omega) (by omega)
    have := hmJ.tl n hn (by rw [hid, hst, hcs]; omega)
    rw [hsJ.par, hid] at this
    rw [← (hsel _ (by omega) (by omega)).1]; exact Option.some.inj this
  · obtain ⟨n, hn, hid, hst⟩ := node r.step h0 (by omega)
    have := hpins n hn (by rw [hid, hst]; exact h1) r hr (by rw [hid, hst])
    rw [← (hsel _ h0 (by omega)).1, ← hid]; exact this

/-- No clause lies below the variable stage. -/
theorem satBelow_var (a : Assign) (K : Int) (hK : K ≤ litBlock φ + 1) : SatBelow φ a K := by
  intro j _ hj
  exfalso
  unfold clauseStep at hj
  unfold litBlock at hK
  omega

/-- **The glue in the variable stage.** Every entry of a pinned, reviewed union by key lies on a genuine
path that is a path of one side's pinned send. The entry, and each of its ends with the pinned value,
lie on paths of the union (the variable stage is exact); take the path of the entry and, on the pinned
variable only, the value of the pin: in the variable stage each step depends on one variable, so the
glued path passes the entry, the pin, the key and the branch's pins. -/
theorem var_glue (hwf : WF φ) (P : List NodeId) (m : Nat) (hm : (m : Int) + 1 < litBlock φ) (r : NodeId)
    (h0r : 0 ≤ r.step) (hrm : r.step ≤ m) (p J : _) (hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m))
    (hvX : isValid (filterAllAgg J [r]) = true) (x v : PathNodeId) (hxv : Rel (filterAllAgg J [r]) x v) :
    ∃ sel, ∃ kv ∈ branchLine φ P m, p ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 p) = true ∧
      ChainSound (filterAllAgg (sent φ kv.2 p) [r]) sel ∧ sel x.id.step = x ∧ sel v.id.step = v := by
  have hlb : litBlock φ ≤ stepCount φ := by unfold litBlock stepCount; omega
  have hm2 : (m : Int) + 2 ≤ litBlock φ + 1 := by omega
  have hlt12 : (m : Int) + 1 < (m : Int) + 2 := by omega
  have h01 : (0 : Int) ≤ (m : Int) + 1 := by omega
  have hm0 : (0 : Int) ≤ (m : Int) := by omega
  have hrl : r.step < litBlock φ := by omega
  have hle1 : (m : Int) + 1 ≤ stepCount φ := by omega
  have hlt1 : (m : Int) + 1 < stepCount φ := by omega
  have hm1m2 : (m : Int) + 1 ≤ (m : Int) + 2 := by omega
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  have hsound : SoundAt (LitStep φ) J :=
    adv_sound_var φ hwf P m hm (branch_sound_var φ hwf P m (by omega)) _ hJ
  have hpinsJ : PinIdsBelow P ((m : Int) + 1) J :=
    PinHistory.pinIds_advance φ P m _ hl (PinHistory.pinIds_branch φ hwf P m) _ hJ
  -- the pinned union, kept opaque
  have hRX : ReadableAgg (filterAllAgg J [r]) := ⟨J, [r], hmJ.rctx, rfl⟩
  have okX : AggFixpoint.AggOk (filterAllAgg J [r]) := aggOk_reviewAgg _ hvX
  have smpX := AnchoredSurvive.SMP_filterAllAgg J hmJ.smp hmJ.rctx.shape.notroot [r]
  have pmsX := AggInvariants.PMS_filterAllAgg J [r] hmJ.pms
  have snX := AggInvariants.SN_filterAllAgg J [r] hmJ.sn
  have prX : Pruned J (filterAllAgg J [r]) := pruned_filterAllAgg _ _
  have cleanX : ∀ q, q ∈ (filterAllAgg J [r]).gowners → q.id.step = r.step → q.id = r :=
    fun q hq hs => ReaderAggRun.filterAllAgg_cleans J [r] r List.mem_cons_self q hq hs
  generalize filterAllAgg J [r] = X at hRX hvX okX smpX pmsX snX prX cleanX hxv
  have adX := AdjacentOwners.adj_of_readable X hRX hvX pmsX snX
  have supX := sup_self X adX okX smpX
  have hcsX : X.current_step = (m : Int) + 2 := by rw [prX.step_eq, hcsJ]
  have bnd : ∀ a, Mem X a → 0 ≤ a.id.step ∧ a.id.step < (m : Int) + 2 := by
    intro a ha; have := mem_bounds X adX ha; rw [hcsX] at this; exact this
  -- every entry of `X` lies on a path of the union
  have real : ∀ a b, Rel X a b → Realizes J a b := by
    intro a b hab
    obtain ⟨n, hn, hb, _⟩ := hab
    obtain ⟨n0, hn0, hid, hown, _⟩ := prX.nodes_derived n (List.mem_of_find?_eq_some hn)
    have hJa : J.node? a = some n0 := by
      rw [← node?_id_eq X a n hn, hid]; exact node?_of_mem hmJ.rctx.nodup n0 hn0
    have ha := (supX.dom a b ⟨n, hn, hb, ‹_›⟩).1
    have hb' := (supX.dom a b ⟨n, hn, hb, ‹_›⟩).2
    exact hsound a n0 hJa (bnd a ha).1 (by rw [hcsJ]; exact (bnd a ha).2) b (bnd b hb').1
      (by rw [hcsJ]; exact (bnd b hb').2) (Or.inl (by have := bnd b hb'; omega)) (hown b hb)
  -- each end reaches the pinned value
  have pinN : ∀ a, Mem X a → ∃ ρ, Rel X a ρ ∧ ρ.id = r ∧ ρ.id.step = r.step := by
    intro a ha
    obtain ⟨ρ, har, hρs⟩ := supX.cov a ha r.step h0r (by rw [hcsX]; omega)
    exact ⟨ρ, har, cleanX ρ (supX.gow ρ (supX.dom a ρ har).2) hρs, hρs⟩
  have hxm := (supX.dom x v hxv).1
  have hvm := (supX.dom x v hxv).2
  obtain ⟨ρx, hxρ, hρx, hρxs⟩ := pinN x hxm
  obtain ⟨ρv, hvρ, hρv, hρvs⟩ := pinN v hvm
  have hle : (m : Int) + 2 ≤ stepCount φ := by omega
  obtain ⟨s1, hs1, hs1x, hs1v⟩ := real x v hxv
  obtain ⟨s2, hs2, hs2x, hs2r⟩ := real x ρx hxρ
  obtain ⟨s3, hs3, hs3v, hs3r⟩ := real v ρv hvρ
  obtain ⟨b1, hb1, hb1p, hb1P⟩ := path_facts φ hwf P m p J hsJ hmJ hpinsJ hle s1 hs1
  obtain ⟨b2, hb2, hb2p, hb2P⟩ := path_facts φ hwf P m p J hsJ hmJ hpinsJ hle s2 hs2
  obtain ⟨b3, hb3, hb3p, hb3P⟩ := path_facts φ hwf P m p J hsJ hmJ hpinsJ hle s3 hs3
  -- the glued assignment: the entry's path, with the pinned value on its variable
  have hlit : ∀ k : Int, k < (m : Int) + 2 → k < litBlock φ := fun k hk => by omega
  have selr : ∀ (s : Int → PathNodeId) (b : Assign) (ρ : PathNodeId), s ρ.id.step = ρ → ρ.id = r →
      ρ.id.step = r.step → (∀ k, 0 ≤ k → k < (m : Int) + 2 → (s k).id = selOfAssign φ b k ∧
        (s k).parent_id = (if k = 0 then none else some (selOfAssign φ b (k - 1)))) →
      selOfAssign φ b r.step = r := by
    intro s b ρ hsρ hρ hρs hb
    rw [← (hb r.step h0r (by omega)).1, ← hρs, hsρ, hρ]
  have h2r := selr s2 b2 ρx hs2r hρx hρxs hb2
  have h3r := selr s3 b3 ρv hs3r hρv hρvs hb3
  have h23 := sel_det φ b2 b3 r.step h0r (by omega) (h2r.trans h3r.symm)
  let u := (r.step / 2).toNat
  let A := glue b1 b2 u
  have hA3 : A = glue b1 b3 u := by
    funext w; simp only [A, glue]; split
    · next h => rw [h]; exact h23
    · rfl
  -- a node on two of the paths is on the glued one
  have onA : ∀ (bb : Assign) (hA : A = glue b1 bb u) (s s' : Int → PathNodeId) (y : PathNodeId),
      (∀ k, 0 ≤ k → k < (m : Int) + 2 → (s k).id = selOfAssign φ b1 k ∧
        (s k).parent_id = (if k = 0 then none else some (selOfAssign φ b1 (k - 1)))) →
      (∀ k, 0 ≤ k → k < (m : Int) + 2 → (s' k).id = selOfAssign φ bb k ∧
        (s' k).parent_id = (if k = 0 then none else some (selOfAssign φ bb (k - 1)))) →
      s y.id.step = y → s' y.id.step = y → 0 ≤ y.id.step → y.id.step < (m : Int) + 2 →
      (⟨selOfAssign φ A y.id.step, if y.id.step = 0 then none else some (selOfAssign φ A (y.id.step - 1))⟩ :
        PathNodeId) = y := by
    intro bb hA s s' y hs hs' hsy hs'y hy0 hy1
    obtain ⟨hi1, hp1⟩ := hs y.id.step hy0 hy1
    obtain ⟨hi2, hp2⟩ := hs' y.id.step hy0 hy1
    rw [hsy] at hi1 hp1
    rw [hs'y] at hi2 hp2
    apply RunNoBorrow.pid_ext
    · show selOfAssign φ A y.id.step = y.id
      rw [hA]; exact glue_agree φ b1 bb u _ hy0 (hlit _ hy1) _ hi1.symm hi2.symm
    · show (if y.id.step = 0 then none else some (selOfAssign φ A (y.id.step - 1))) = y.parent_id
      by_cases hz : y.id.step = 0
      · rw [if_pos hz]; rw [if_pos hz] at hp1; exact hp1.symm
      · rw [if_neg hz]; rw [if_neg hz] at hp1 hp2
        have e := Option.some.inj (hp1.symm.trans hp2)
        rw [hp1, hA, glue_agree φ b1 bb u _ (by omega) (hlit _ (by omega)) _ rfl e.symm]
  -- the glued path
  let selA : Int → PathNodeId := fun k =>
    ⟨selOfAssign φ A k, if k = 0 then none else some (selOfAssign φ A (k - 1))⟩
  have hsatA : ∀ K, K ≤ (m : Int) + 2 → SatBelow φ A K := fun K hK => satBelow_var φ A K (Int.le_trans hK hm2)
  have hgenA : Genuine φ ((m : Int) + 2) selA := ⟨A, hsatA _ (Int.le_refl _), fun k _ _ => ⟨rfl, rfl⟩⟩
  have agP : ∀ r' ∈ P, 0 ≤ r'.step → r'.step < (m : Int) + 1 → selOfAssign φ A r'.step = r' :=
    fun r' hr' h0 h1 => glue_agree φ b1 b2 u _ h0 (hlit _ (Int.lt_trans h1 hlt12)) _ (hb1P r' hr' h0 h1)
      (hb2P r' hr' h0 h1)
  have hAp : selOfAssign φ A ((m : Int) + 1) = p :=
    glue_agree φ b1 b2 u _ h01 (hlit _ hlt12) _ hb1p hb2p
  have hAr : selOfAssign φ A r.step = r := by
    show selOfAssign φ (glue b1 b2 (r.step / 2).toNat) r.step = r
    rw [glue_self φ b1 b2 r.step h0r hrl]; exact h2r
  -- the side: the branch's state at the glued key
  obtain ⟨g, hmem, _, _⟩ := branch_carries φ hwf P A ((m : Int) + 1) hle1 (hsatA _ hm1m2)
    (fun r' hr' h0 h1 => agP r' hr' h0 h1) m (Int.le_refl _)
  have hson : p ∈ mapSons φ (selOfAssign φ A (m : Int)).step (selOfAssign φ A (m : Int)).index := by
    rw [selOfAssign_step, ← hAp]
    exact ConservationPrefix.selOfAssign_son_below φ A m (hsatA _ (Int.le_refl _)) hm0 hlt1
  obtain ⟨hvS, hscS⟩ := branch_send_chain φ hwf P m hle (selOfAssign φ A (m : Int), g) hmem p hson selA hgenA
    rfl hAp (fun r' hr' h0 h1 => agP r' hr' h0 h1)
  refine ⟨selA, (selOfAssign φ A (m : Int), g), hmem, hson, hvS,
    ChainSound_filterAllAgg _ [r] selA hscS (fun q hq _ _ => by
      rw [List.mem_singleton.mp hq]; exact hAr), ?_, ?_⟩
  · exact onA b2 rfl s1 s2 x hb1 hb2 hs1x hs2x (bnd x hxm).1 (bnd x hxm).2
  · exact onA b3 hA3 s1 s3 v hb1 hb3 hs1v hs3v (bnd v hvm).1 (bnd v hvm).2

-- ============================================================
-- D. The union by key in the variable stage
-- ============================================================

/-- **`PinJoin` holds in the variable stage**, with no hypothesis. -/
theorem pinJoinVar (hwf : WF φ) : PinSend.PinJoinVar φ := by
  intro m hm P L r h0 h1 hlb p J hJ0 hvX
  have hJ : (p, J) ∈ pureAdvanceW φ (branchLine φ P m) := hJ0
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hRX : ReadableAgg (filterAllAgg J [r]) := ⟨J, [r], hmJ.rctx, rfl⟩
  have ctxX := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRX) hvX
  have adX := AdjacentOwners.adj_of_readable _ hRX hvX (AggInvariants.PMS_filterAllAgg J [r] hmJ.pms)
    (AggInvariants.SN_filterAllAgg J [r] hmJ.sn)
  have hcsX : (filterAllAgg J [r]).current_step = (m : Int) + 2 := by
    rw [(pruned_filterAllAgg J [r]).step_eq, hsJ.step]; omega
  have glue := var_glue φ hwf P m hm r h0 h1 p J hJ hvX
  have relSelf : ∀ x n, (filterAllAgg J [r]).node? x = some n → Rel (filterAllAgg J [r]) x x :=
    fun x n hx => ⟨n, hx, ctxX.self x n hx, ⟨n, hx⟩⟩
  refine ⟨?_, fun Z hsZ hmZ hY => ?_⟩
  · -- a valid side: the pinned union has a node
    have hv' := hvX
    simp only [isValid, List.all_eq_true] at hv'
    obtain ⟨z, hz, _⟩ := List.any_eq_true.mp (hv' 0 (mem_intRange (Int.le_refl 0) (by rw [hcsX]; omega)))
    obtain ⟨n, hn, hnid⟩ := ctxX.gn z hz
    have hzn : (filterAllAgg J [r]).node? z = some n := by
      rw [← hnid]; exact node?_of_mem adX.rc.nodup n hn
    obtain ⟨sel, kv, hkv, hson, hvS, hsc, _⟩ := glue z z (relSelf z n hzn)
    exact ⟨kv, hkv, hson, hvS, PickInduction.isValid_of_ChainG _ sel hsc.chain⟩
  · -- every entry lies on a path of a valid pinned side, which sits in `Z`
    have hcsZ : Z.current_step = (m : Int) + 2 := by rw [hsZ.step]; omega
    have inZ : ∀ x v, Rel (filterAllAgg J [r]) x v → ∃ sel, ChainSound Z sel ∧ sel x.id.step = x ∧
        sel v.id.step = v := by
      intro x v hxv
      obtain ⟨sel, kv, hkv, hson, hvS, hsc, hsx, hsv⟩ := glue x v hxv
      have e := hY kv hkv hson hvS (PickInduction.isValid_of_ChainG _ sel hsc.chain)
      exact ⟨sel, SeqPin.chainSound_of_embedded e hmZ.smp sel hsc, hsx, hsv⟩
    have bnd : ∀ a, Mem (filterAllAgg J [r]) a → 0 ≤ a.id.step ∧ a.id.step < (m : Int) + 2 := by
      intro a ha; have := mem_bounds _ adX ha; rw [hcsX] at this; exact this
    refine ⟨by rw [hcsX, hcsZ], fun q hq => ?_, fun x mx hx => ?_⟩
    · obtain ⟨n, hn, hnid⟩ := ctxX.gn q hq
      have hqn : (filterAllAgg J [r]).node? q = some n := by
        rw [← hnid]; exact node?_of_mem adX.rc.nodup n hn
      obtain ⟨sel, hsc, hsq, _⟩ := inZ q q (relSelf q n hqn)
      have hb := bnd q ⟨n, hqn⟩
      have := hsc.chain.2.2 q.id.step hb.1 (by rw [hcsZ]; exact hb.2)
      rwa [hsq] at this
    · have hb := bnd x ⟨mx, hx⟩
      obtain ⟨sel, hsc, hsx, _⟩ := inZ x x (relSelf x mx hx)
      obtain ⟨hsome, _⟩ := hsc.chain.1.1 x.id.step hb.1 (by rw [hcsZ]; exact hb.2)
      rw [hsx] at hsome
      obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨nz, hnz, fun q hq hqm => ?_, fun q hq hqm => ?_⟩
      · obtain ⟨sel', hsc', hsx', hsq'⟩ := inZ x q ⟨mx, hx, hq, hqm⟩
        have hbq := bnd q hqm
        obtain ⟨m', hm', hqo, _⟩ := JoinSide.rel_of_chain Z sel' hsc' q.id.step x.id.step hbq.1
          (by rw [hcsZ]; exact hbq.2) hb.1 (by rw [hcsZ]; exact hb.2)
        rw [hsx', hnz] at hm'; cases hm'
        rwa [hsq'] at hqo
      · have hqo : q ∈ mx.owners := (adX.links x mx hx).1 q hq
        obtain ⟨sel', hsc', hsx', hsq'⟩ := inZ x q ⟨mx, hx, hqo, hqm⟩
        have hstep : q.id.step + 1 = x.id.step := by
          have := adX.rc.shape.pbelow mx (List.mem_of_find?_eq_some hx) q hq
          rw [node?_id_eq _ x mx hx] at this; omega
        have hlink := hsc'.chain.1.2 q.id.step (bnd q hqm).1 (by rw [hcsZ]; omega)
        rw [hstep, hsx', hnz, hsq'] at hlink
        exact hlink

/-- **The verdict under the clause stage alone.** -/
theorem sat_of_pinJoinClause (hwf : WF φ) (hC : PinSend.PinJoinClause φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  PinSend.sat_of_pinJoin φ hwf (PinSend.pinJoin_of_stages φ (pinJoinVar φ hwf) hC) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PinVar.sat_of_pinJoinClause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinJoinClause

end AbsSat.GraphPath.Model.PinVar
