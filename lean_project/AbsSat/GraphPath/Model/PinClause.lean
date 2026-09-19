-- lean_project/AbsSat/GraphPath/Model/PinClause.lean
import AbsSat.GraphPath.Model.PinVar

/-!
# The clause stage: one flip, carried by the history

`PinVar` reduced the clause stage to `FlipAt`: pairs of paths, and one condition that is not about pairs.
This module removes the pairs from the hypothesis. By a joint induction on the line, for all branches at
once, it carries two facts:

* **every state of every branch is exact, towards every step** (`LineSoundL Full`), and
* **pinning one literal value commutes with the history** (`PC1At`).

At each line the first gives the pairs, so the only hypothesis left is **`FlipSat`**: some path of the
pinned union's union through the entry's two ends still satisfies the clauses once the pinned variable
takes its pinned value.
-/

namespace AbsSat.GraphPath.Model.PinClause

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
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.ConservationPrefix (SatBelow)
open AbsSat.GraphPath.Model.BranchRun (restrictLine embedded_of_pruned isValid_of_embedded)
open AbsSat.GraphPath.Model.BranchLines (sent sendToW_eq advance_inv insert_src key_unique embedded_refl)
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Rel Embedded mem_bounds)
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep soundAt_join soundAt_initSeed soundAt_review)
open AbsSat.GraphPath.Model.SendDistrib (embedded_trans mem_of_embedded)
open AbsSat.GraphPath.Model.PinHistory (branchLine branchLine_succ branchLine_inv branchLine_emb mem_restrict
  pinIds_branch chain_pins Good good_of_minv good_filterAllAgg embedded_pin pruned_pinOneByOne dstep_of
  topPin_key mem_branch_top)
open AbsSat.GraphPath.Model.BranchCompat (pinOneByOne)

variable (φ : Cnf)

-- ============================================================
-- Exactness towards any set of steps, line by line
-- ============================================================

/-- Every step. -/
def Full : Int → Prop := fun _ => True

/-- Every state of a line has its entries towards the steps of `L` on paths. -/
def LineSoundL (L : Int → Prop) (line : PureLine) : Prop := ∀ kv ∈ line, SoundAt L kv.2

theorem lineSoundL_insertPure (L : Int → Prop) (acc : PureLine) (key : NodeId) (g : GPathM)
    (hacc : LineSoundL L acc) (hg : SoundAt L g) : LineSoundL L (insertPure acc key g) := by
  rintro ⟨d, B⟩ hB
  rcases insert_src acc key g d B hB with ⟨_, hB'⟩ | ⟨hB', _⟩
  · rcases hB' with rfl | ⟨e, he, rfl⟩
    · exact hg
    · unfold doJoin
      split
      · next hok => exact soundAt_join _ e g hok (hacc (key, e) he) hg
      · exact hacc (key, e) he
  · exact hacc (d, B) hB'

theorem lineSoundL_init (L : Int → Prop) : LineSoundL L (pureInit φ) := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d.step = 0) → ∀ acc : PureLine, LineSoundL L acc →
      LineSoundL L (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (lineSoundL_insertPure L acc x _ h (soundAt_initSeed _ x "" (hx x List.mem_cons_self)))
  exact main _ (fun d hd => mapNodes_step φ 0 d hd) [] (fun _ h => absurd h List.not_mem_nil)

-- ============================================================
-- One pin commutes with the history, at one line
-- ============================================================

/-- **One pin commutes with the history at line `m`**, for every branch. -/
def PC1At (m : Nat) : Prop :=
  ∀ (P : List NodeId), ∀ kv ∈ branchLine φ P m, ∀ r : NodeId, 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    isValid (filterAllAgg kv.2 [r]) = true →
    ∃ kv' ∈ branchLine φ (P ++ [r]) m, kv'.1 = kv.1 ∧ Embedded (filterAllAgg kv.2 [r]) kv'.2

/-- Several pins, one at a time, at one line. -/
theorem pinOne_at (hwf : WF φ) (m : Nat) (h1 : PC1At φ m) :
    ∀ (rs : List NodeId), (∀ r ∈ rs, 0 ≤ r.step ∧ r.step ≤ m ∧ r.step < litBlock φ) →
      ∀ (P : List NodeId) (X : GPathM) (kv : NodeId × GPathM), kv ∈ branchLine φ P m → Good X →
        Embedded X kv.2 → isValid (pinOneByOne X rs) = true →
        ∃ kv' ∈ branchLine φ (P ++ rs) m, kv'.1 = kv.1 ∧ Embedded (pinOneByOne X rs) kv'.2 := by
  intro rs
  induction rs with
  | nil => intro _ P X kv hkv _ e _; exact ⟨kv, by rw [List.append_nil]; exact hkv, rfl, e⟩
  | cons r rest ih =>
    intro hrs P X kv hkv hX e hv
    have hmk : MInv φ kv.2 := (branchLine_inv φ hwf P m).2 kv hkv
    have hv1 : isValid (filterAllAgg X [r]) = true := by
      have hg := good_filterAllAgg hX [r]
      exact isValid_of_embedded (embedded_of_pruned (pruned_pinOneByOne rest _) hg.rc.nodup
        (embedded_refl _)) hv
    have e1 := embedded_pin X kv.2 [r] e hX (good_of_minv φ hmk) hv1
    have hvk := isValid_of_embedded e1 hv1
    obtain ⟨h0, hle, hlt⟩ := hrs r List.mem_cons_self
    obtain ⟨kv1, hkv1, hk1, e2⟩ := h1 P kv hkv r h0 hle hlt hvk
    obtain ⟨kv', hkv', hk', e3⟩ := ih (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')) (P ++ [r])
      (filterAllAgg X [r]) kv1 hkv1 (good_filterAllAgg hX [r]) (embedded_trans e1 e2) hv
    refine ⟨kv', ?_, by rw [hk', hk1], e3⟩
    rw [show P ++ r :: rest = P ++ [r] ++ rest by simp]; exact hkv'

/-- **A clause row's three pins commute with the history, at one line.** -/
theorem pc3_at (hwf : WF φ) (m : Nat) (h1 : PC1At φ m) (P : List NodeId) (kv : NodeId × GPathM)
    (hkv : kv ∈ branchLine φ P m) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hlb : litBlock φ < d.step) (hne : reqOfCnf φ d ≠ []) (hvA : isValid (filterAllAgg kv.2 (reqOfCnf φ d)) = true)
    (x q : PathNodeId) (hxq : Rel (filterAllAgg kv.2 (reqOfCnf φ d)) x q) :
    ∃ kv' ∈ branchLine φ (P ++ reqOfCnf φ d) m, kv'.1 = kv.1 ∧ Rel kv'.2 x q := by
  have hl := branchLine_inv φ hwf P m
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmk : MInv φ kv.2 := hl.2 kv hkv
  have hdstep := dstep_of φ m kv hsok d hd
  obtain ⟨j, hj, hjs⟩ := ClauseReview.clause_of_row φ d hlb hne
  have hreqs := reqOfCnf_clause φ d j φ.clauses[j] hj (List.getElem?_eq_getElem hj) hjs
  have hr : ∀ r ∈ reqOfCnf φ d, 0 ≤ r.step ∧ r.step ≤ m ∧ r.step < litBlock φ := by
    intro r hr
    have hlt := RunInhabited.reqOfCnf_lit φ hwf d r hr
    refine ⟨?_, by rw [hdstep] at hlb; omega, hlt⟩
    rw [hreqs] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (show 0 ≤ Lit.step _; unfold Lit.step; split <;> omega)
  rw [hreqs] at hvA hxq hr ⊢
  obtain ⟨hvS, eAS, _⟩ := SeqPin.seq_eq_all kv.2 hmk.rctx hmk.smp hmk.pms hmk.sn _ _ hvA
  obtain ⟨kv', hkv', hk, e⟩ := pinOne_at φ hwf m h1 _ hr P kv.2 kv hkv (good_of_minv φ hmk) (embedded_refl _) hvS
  have eA := embedded_trans eAS e
  obtain ⟨n, hn, hqn, hqm⟩ := hxq
  obtain ⟨n', hn', hown, _⟩ := eA.node x n hn
  exact ⟨kv', hkv', hk, n', hn', hown q hqn hqm, mem_of_embedded eA hqm⟩

-- ============================================================
-- Every send of an exact line is exact, towards every step
-- ============================================================

/-- **A send of a branch is exact**, given that the line is exact and one pin commutes at that line. -/
theorem send_sound_full (hwf : WF φ) (m : Nat) (hE : ∀ Q, LineSoundL Full (branchLine φ Q m))
    (hC : PC1At φ m) (P : List NodeId) (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hval : isValid (sent φ kv.2 d) = true) :
    SoundAt Full (sent φ kv.2 d) := by
  have hl := branchLine_inv φ hwf P m
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmkv : MInv φ kv.2 := hl.2 kv hkv
  have ht : SoundAt Full kv.2 := hE P kv hkv
  have hdstep := dstep_of φ m kv hsok d hd
  refine RunInhabited.soundAt_sent_ofL φ Full trivial m kv hsok hmkv d hd hval (fun hvW => ?_)
  refine WeakNoop.soundAt_weak_sendL φ Full hwf m kv hsok hmkv d hd hvW (fun hvA => ?_)
  rcases reqOfCnf_shape φ d with h | h | ⟨c, _, hlb, h⟩
  · rw [h] at hvA ⊢; exact soundAt_review _ kv.2 hmkv.rctx.nodup ht
  · rw [h] at hvA ⊢
    exact ClausePins.soundAt_pin_topL φ Full m kv hsok hmkv ht _ (by show d.step - 1 = (m : Int); omega) hvA
  · -- the clause row: the entry is an entry of the branch with the row's pins
    have hne : reqOfCnf φ d ≠ [] := by rw [h]; exact List.cons_ne_nil _ _
    have hRA : ReadableAgg (filterAllAgg kv.2 (reqOfCnf φ d)) := ⟨kv.2, _, hmkv.rctx, rfl⟩
    have ctxA := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRA) hvA
    have rcA := RCtx_of_readableAgg _ hRA
    have hprA : Pruned kv.2 (filterAllAgg kv.2 (reqOfCnf φ d)) := pruned_filterAllAgg _ _
    intro x n hx hx0 hx1 q hq0 hq1 hL hqn
    have hqm : Mem (filterAllAgg kv.2 (reqOfCnf φ d)) q := by
      obtain ⟨nq, hnq, hnqid⟩ := ctxA.gn q (ctxA.ownGow x n hx q hqn hq0 hq1)
      exact ⟨nq, by rw [← hnqid]; exact node?_of_mem rcA.nodup nq hnq⟩
    obtain ⟨kv', hkv', hkey, n', hn', hqn', _⟩ :=
      pc3_at φ hwf m hC P kv hkv d hd hlb hne hvA x q ⟨n, hx, hqn, hqm⟩
    have hl' := branchLine_inv φ hwf (P ++ reqOfCnf φ d) m
    have hs' : kv'.2.current_step = (m : Int) + 1 := (hl'.1.2 kv' hkv').step
    have hsA : (filterAllAgg kv.2 (reqOfCnf φ d)).current_step = (m : Int) + 1 := by
      rw [hprA.step_eq, hsok.step]
    obtain ⟨sel, hsc, hsx, hsq⟩ := hE (P ++ reqOfCnf φ d) kv' hkv' x n' hn' hx0
      (by rw [hs', ← hsA]; exact hx1) q hq0 (by rw [hs', ← hsA]; exact hq1) trivial hqn'
    obtain ⟨kv'', hkv'', hkey', he⟩ := branchLine_emb φ hwf P (reqOfCnf φ d) m kv' hkv'
    have h1 : (kv.1, kv''.2) ∈ branchLine φ P m := by rw [← hkey, ← hkey']; exact hkv''
    have hkk : kv''.2 = kv.2 := key_unique _ hl.1.1 kv.1 _ _ h1 hkv
    rw [hkk] at he
    have hsc' := SeqPin.chainSound_of_embedded he hmkv.smp sel hsc
    have hpins := chain_pins (P ++ reqOfCnf φ d) kv'.2
      (by rw [hs']; exact pinIds_branch φ hwf _ m kv' hkv') sel hsc
    exact ⟨sel, ChainSound_filterAllAgg kv.2 (reqOfCnf φ d) sel hsc' (fun r hr h0 h1 =>
      hpins r (List.mem_append_right _ hr) h0 (by rw [hs', ← hsok.step]; exact h1)), hsx, hsq⟩

/-- **The advanced line of an exact branch line is exact.** -/
theorem adv_sound_full (hwf : WF φ) (m : Nat) (hE : ∀ Q, LineSoundL Full (branchLine φ Q m))
    (hC : PC1At φ m) (P : List NodeId) : LineSoundL Full (pureAdvanceW φ (branchLine φ P m)) := by
  refine advance_inv φ (LineSoundL Full) _ ?_ (fun _ h => absurd h List.not_mem_nil)
  intro kv hkv d hd acc hacc
  rw [sendToW_eq]
  split
  · next hval => exact lineSoundL_insertPure Full acc d _ hacc (send_sound_full φ hwf m hE hC P kv hkv d hd hval)
  · exact hacc

-- ============================================================
-- The only hypothesis left: one flip
-- ============================================================

open AbsSat.GraphPath.Model.PinVar (canon Agrees glue FlipAt PathAt path_facts pathAt_of_flip pinJoinAt_of_paths)
open AbsSat.GraphPath.Model.PinHistory (PinIdsBelow)
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.AggFixpoint (aggOk_reviewAgg)

/-- **One flip, at line `m`.** For each entry `x → v` of a pinned, reviewed union by key, some assignment
whose branch passes `x`, `v`, the key and the branch's pins **still satisfies every clause below the top
once the pinned variable takes its pinned value**. -/
def FlipSatAt (m : Nat) : Prop :=
  ∀ (P : List NodeId) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    ∀ p J, (p, J) ∈ pureAdvanceW φ (branchLine φ P m) → isValid (filterAllAgg J [r]) = true →
      ∀ x v, Rel (filterAllAgg J [r]) x v →
        ∃ b₁ : Assign, canon φ b₁ x.id.step = x ∧ canon φ b₁ v.id.step = v ∧
          selOfAssign φ b₁ ((m : Int) + 1) = p ∧ Agrees φ P b₁ ((m : Int) + 1) ∧
          ∀ b : Assign, selOfAssign φ b r.step = r → SatBelow φ (glue b₁ b (r.step / 2).toNat) ((m : Int) + 2)

/-- A path's assignment passes the path's nodes. -/
theorem canon_of_path (b : Assign) (s : Int → PathNodeId) (K : Int)
    (hb : ∀ k, 0 ≤ k → k < K → (s k).id = selOfAssign φ b k ∧
      (s k).parent_id = (if k = 0 then none else some (selOfAssign φ b (k - 1))))
    (k : Int) (h0 : 0 ≤ k) (h1 : k < K) : canon φ b k = s k := by
  obtain ⟨hi, hp⟩ := hb k h0 h1
  exact RunNoBorrow.pid_ext hi.symm hp.symm

/-- **The pairs come from exactness.** With the union exact, the flip is `FlipAt`. -/
theorem flipAt_of_sat (hwf : WF φ) (m : Nat)
    (hE : ∀ P, LineSoundL Full (pureAdvanceW φ (branchLine φ P m))) (hF : FlipSatAt φ m) :
    FlipAt φ m := by
  intro P r h0r hrm hrl p J hJ hvX x v hxv
  obtain ⟨b₁, hx1, hv1, hp1, hP1, hsat⟩ := hF P r h0r hrm hrl p J hJ hvX x v hxv
  have hl := branchLine_inv φ hwf P m
  have hadv := ReaderAggRun.LineInv_pureAdvanceW φ hwf m _ hl
  have hsJ : StateOkF φ ((m : Int) + 1) (p, J) := hadv.1.2 _ hJ
  have hmJ : MInv φ J := hadv.2 _ hJ
  have hcsJ : J.current_step = (m : Int) + 2 := by rw [hsJ.step]; omega
  have hle : (m : Int) + 2 ≤ stepCount φ := by
    have := PinVar.lt_of_mapNodes φ _ p hsJ.onMap; omega
  have hsound : SoundAt Full J := hE P _ hJ
  have hpinsJ : PinIdsBelow P ((m : Int) + 1) J :=
    PinHistory.pinIds_advance φ P m _ hl (pinIds_branch φ hwf P m) _ hJ
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
  have real : ∀ a b, Rel X a b → Realizes J a b := by
    intro a b hab
    obtain ⟨n, hn, hb, hbm⟩ := hab
    obtain ⟨n0, hn0, hid, hown, _⟩ := prX.nodes_derived n (List.mem_of_find?_eq_some hn)
    have hJa : J.node? a = some n0 := by
      rw [← node?_id_eq X a n hn, hid]; exact node?_of_mem hmJ.rctx.nodup n0 hn0
    have ha := (supX.dom a b ⟨n, hn, hb, hbm⟩).1
    have hb' := (supX.dom a b ⟨n, hn, hb, hbm⟩).2
    exact hsound a n0 hJa (bnd a ha).1 (by rw [hcsJ]; exact (bnd a ha).2) b (bnd b hb').1
      (by rw [hcsJ]; exact (bnd b hb').2) trivial (hown b hb)
  have pinN : ∀ a, Mem X a → ∃ ρ, Rel X a ρ ∧ ρ.id = r ∧ ρ.id.step = r.step := by
    intro a ha
    obtain ⟨ρ, har, hρs⟩ := supX.cov a ha r.step h0r (by rw [hcsX]; omega)
    exact ⟨ρ, har, cleanX ρ (supX.gow ρ (supX.dom a ρ har).2) hρs, hρs⟩
  have hxm := (supX.dom x v hxv).1
  have hvm := (supX.dom x v hxv).2
  obtain ⟨ρx, hxρ, hρx, hρxs⟩ := pinN x hxm
  obtain ⟨ρv, hvρ, hρv, hρvs⟩ := pinN v hvm
  obtain ⟨s2, hs2, hs2x, hs2r⟩ := real x ρx hxρ
  obtain ⟨s3, hs3, hs3v, hs3r⟩ := real v ρv hvρ
  obtain ⟨b₂, hb2, hb2p, hb2P⟩ := path_facts φ hwf P m p J hsJ hmJ hpinsJ hle s2 hs2
  obtain ⟨b₃, hb3, _, _⟩ := path_facts φ hwf P m p J hsJ hmJ hpinsJ hle s3 hs3
  have hr2 : selOfAssign φ b₂ r.step = r := by
    rw [← (hb2 r.step h0r (by omega)).1, ← hρxs, hs2r, hρx]
  have hr3 : selOfAssign φ b₃ r.step = r := by
    rw [← (hb3 r.step h0r (by omega)).1, ← hρvs, hs3r, hρv]
  refine ⟨b₁, b₂, b₃, ⟨hx1, hv1, hp1, hP1⟩, ⟨?_, hr2, hb2p, hb2P⟩, ⟨?_, hr3⟩, hsat b₂ hr2⟩
  · rw [canon_of_path φ b₂ s2 _ hb2 x.id.step (bnd x hxm).1 (bnd x hxm).2, hs2x]
  · rw [canon_of_path φ b₃ s3 _ hb3 v.id.step (bnd v hvm).1 (bnd v hvm).2, hs3v]

-- ============================================================
-- The joint induction
-- ============================================================

open AbsSat.GraphPath.Model.PinSend (PinJoinAt pinned_source_valid pin_send)

/-- **One advance, at one line and one branch**, from the union by key at that line. -/
theorem advance_at (hwf : WF φ) (m : Nat) (hJ : PinJoinAt φ m) (P : List NodeId) (r : NodeId)
    (h0 : 0 ≤ r.step) (h1 : r.step ≤ m) (hlb : r.step < litBlock φ)
    (H : ∀ kv ∈ branchLine φ P m, isValid (filterAllAgg kv.2 [r]) = true →
      ∃ kv' ∈ branchLine φ (P ++ [r]) m, kv'.1 = kv.1 ∧ Embedded (filterAllAgg kv.2 [r]) kv'.2) :
    ∀ kv ∈ pureAdvanceW φ (branchLine φ P m), isValid (filterAllAgg kv.2 [r]) = true →
      ∃ kv' ∈ pureAdvanceW φ (branchLine φ (P ++ [r]) m), kv'.1 = kv.1 ∧
        Embedded (filterAllAgg kv.2 [r]) kv'.2 := by
  intro kv hkv hv
  have hl := branchLine_inv φ hwf P m
  have hl' := branchLine_inv φ hwf (P ++ [r]) m
  obtain ⟨⟨kv0, hkv0, hd0, hs0, hy0⟩, hZ⟩ := hJ P r h0 h1 hlb kv.1 kv.2 hkv hv
  generalize branchLine φ P m = L at hl H hkv hkv0 hZ
  generalize branchLine φ (P ++ [r]) m = L' at hl' H ⊢
  have side : ∀ kvi ∈ L, kv.1 ∈ mapSons φ kvi.1.step kvi.1.index → isValid (sent φ kvi.2 kv.1) = true →
      isValid (filterAllAgg (sent φ kvi.2 kv.1) [r]) = true →
      ∃ J', (kv.1, J') ∈ pureAdvanceW φ L' ∧ Embedded (filterAllAgg (sent φ kvi.2 kv.1) [r]) J' := by
    intro kvi hkvi hdi hsi hyi
    have hsok := hl.1.2 kvi hkvi
    have hvG := pinned_source_valid φ hwf m kvi.1 kvi.2 hsok (hl.2 kvi hkvi) r kv.1 hdi hsi hyi
    obtain ⟨kv', hkv', hk, e0⟩ := H kvi hkvi hvG
    have hsB : StateOkF φ m (kvi.1, kv'.2) := by rw [← hk]; exact hl'.1.2 kv' hkv'
    obtain ⟨hvB, e⟩ := pin_send φ hwf m kvi.1 kvi.2 kv'.2 hsok (hl.2 kvi hkvi) hsB (hl'.2 kv' hkv') r e0
      kv.1 hdi hsi hyi
    obtain ⟨J', hJ', hg⟩ := BranchLines.full_reach φ hwf m L' hl' kv' hkv' kv.1 (by rw [hk]; exact hdi) hvB
    exact ⟨J', hJ', BranchRun.embedded_of_grown e hg⟩
  obtain ⟨J', hJ', _⟩ := side kv0 hkv0 hd0 hs0 hy0
  have hl2 := ReaderAggRun.LineInv_pureAdvanceW φ hwf m L' hl'
  refine ⟨(kv.1, J'), hJ', rfl, hZ J' (hl2.1.2 _ hJ') (hl2.2 _ hJ') ?_⟩
  intro kvi hkvi hdi hsi hyi
  obtain ⟨J'', hJ'', e⟩ := side kvi hkvi hdi hsi hyi
  rw [key_unique _ hl2.1.1 kv.1 J'' J' hJ'' hJ'] at e
  exact e

/-- A pin at the top step is the key, and the branch keeps that state. -/
theorem top_case (hwf : WF φ) (P : List NodeId) (m : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ branchLine φ P m)
    (r : NodeId) (hr : r.step = m) (hv : isValid (filterAllAgg kv.2 [r]) = true) :
    ∃ kv' ∈ branchLine φ (P ++ [r]) m, kv'.1 = kv.1 ∧ Embedded (filterAllAgg kv.2 [r]) kv'.2 := by
  have hl := branchLine_inv φ hwf P m
  have hmk : MInv φ kv.2 := hl.2 kv hkv
  have hk := topPin_key φ m kv (hl.1.2 kv hkv) hmk r hr hv
  exact ⟨kv, mem_branch_top φ P m r hr kv hkv hk.symm, rfl,
    embedded_of_pruned (pruned_filterAllAgg _ _) hmk.rctx.nodup (embedded_refl _)⟩

/-- **The joint induction.** Under the flip in the clause stage, at every line, every branch is exact
towards every step, and one pin commutes with the history. -/
theorem joint (hwf : WF φ) (hF : ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 → FlipSatAt φ m) :
    ∀ m : Nat, (∀ P, LineSoundL Full (branchLine φ P m)) ∧ PC1At φ m := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun P kv hkv => ?_, fun P kv hkv r h0 h1 _ hv => top_case φ hwf P 0 kv hkv r (by omega) hv⟩
    unfold branchLine at hkv
    exact lineSoundL_init φ Full kv (mem_restrict (show kv ∈ restrictLine P 0 (pureInit φ) from hkv)).1
  | succ m ih =>
    obtain ⟨hE, hC⟩ := ih
    have hadvE : ∀ P, LineSoundL Full (pureAdvanceW φ (branchLine φ P m)) :=
      fun P => adv_sound_full φ hwf m hE hC P
    refine ⟨fun P kv hkv => ?_, fun P kv hkv r h0 h1 hlb hv => ?_⟩
    · rw [branchLine_succ] at hkv
      exact hadvE P kv (mem_restrict hkv).1
    · by_cases hrt : r.step = ((m + 1 : Nat) : Int)
      · exact top_case φ hwf P (m + 1) kv hkv r hrt hv
      · have hJm : PinJoinAt φ m := by
          by_cases hst : (m : Int) + 1 < litBlock φ
          · exact PinVar.pinJoinVar φ hwf m hst
          · exact pinJoinAt_of_paths φ hwf m
              (pathAt_of_flip φ m (flipAt_of_sat φ hwf m hadvE (hF m (by omega))))
        have hkv' := hkv
        rw [branchLine_succ] at hkv'
        obtain ⟨hA', hpass⟩ := mem_restrict hkv'
        obtain ⟨kv', hkv'', hk, e⟩ := advance_at φ hwf m hJm P r h0 (by push_cast at h1 hrt; omega) hlb
          (fun kv0 hkv0 hv0 => hC P kv0 hkv0 r h0 (by push_cast at h1 hrt; omega) hlb hv0) kv hA' hv
        refine ⟨kv', ?_, hk, e⟩
        rw [branchLine_succ]
        refine List.mem_filter.mpr ⟨hkv'', List.all_eq_true.mpr fun r' hr' => ?_⟩
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
        rcases List.mem_append.mp hr' with h | h
        · rcases hpass r' h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by rw [hk]; exact h')
        · rw [List.mem_singleton.mp h]; exact Or.inl (by push_cast at hrt ⊢; omega)

/-- **The verdict, under the flip in the clause stage alone.** -/
theorem sat_of_flipSat (hwf : WF φ) (hF : ∀ m : Nat, litBlock φ ≤ (m : Int) + 1 → FlipSatAt φ m)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ := by
  have hE := (joint φ hwf hF (stepCount φ - 1).toNat).1 []
  rw [PinHistory.branchLine_nil] at hE
  refine RunInhabited.sat_of_lineSound φ hwf (fun kv' hkv' => ?_) kv hkv hv
  intro x n hx hx0 hx1 q hq0 hq1 _ hqn
  exact hE kv' hkv' x n hx hx0 hx1 q hq0 hq1 trivial hqn

/-- info: 'AbsSat.GraphPath.Model.PinClause.sat_of_flipSat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_flipSat

end AbsSat.GraphPath.Model.PinClause
