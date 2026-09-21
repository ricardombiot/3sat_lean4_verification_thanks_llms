-- lean_project/AbsSat/GraphPath/Model/BranchLines.lean
import AbsSat.GraphPath.Model.BranchRun

/-!
# A branch of the machine sits, line by line, inside the whole machine

`BranchRun` proves that a branch state stays inside the corresponding state of the whole construction
through every operation of **one send**. A line of the Improves driver performs many sends, in order,
and joins the ones that reach the same map node; the branch performs only some of them, and its keys
may arrive in a different order. This module does the line-level induction, order-free:

* `advance_inv`, `advance_reach` — the two ways to reason about `pureAdvanceW`: an invariant of every
  send, and a property that one send establishes and every later send keeps.
* `insert_grows`, `insert_new`, `insert_src` — what `insertPure` does to an entry: an old entry only
  grows (`Grown`), the inserted state grows into its entry, and every entry is the old one, the
  inserted state, or their join.
* **`embedded_send`** — a send of a branch state sits inside the same send of the whole state, which
  is then valid too (the state-level lemmas of `BranchRun`).
* `full_reach` — on the whole line, every valid send grows into the entry of its map node.
* `branch_union` — on the branch line, the entry of a map node sits inside any state that contains
  every branch send to that node (joins of contained states stay contained).
* **`lineEmb_advance`** — so every entry of the branch's next line sits inside the entry with the same
  key of the whole next line.
* **`branchRun_embedded`** — **the branch run's final line keeps the machine's invariants (`MInv` on
  every state) and sits inside `pureRunW`**, key by key.
-/

namespace AbsSat.GraphPath.Model.BranchLines

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_sendToW LineInv_pureAdvanceW LineInv_init
  MInv_sent)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF LineOkF StateOkF_sent Fsac prunes_Fsac
  okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.BranchRun

variable (φ : Cnf)

-- ============================================================
-- Folds
-- ============================================================

theorem foldl_inv {α β : Type} (f : α → β → α) (I : α → Prop) :
    ∀ (l : List β), (∀ a b, b ∈ l → I a → I (f a b)) → ∀ a, I a → I (l.foldl f a) := by
  intro l
  induction l with
  | nil => intro _ a h; exact h
  | cons b rest ih =>
    intro hf a ha
    exact ih (fun a' b' hb' ha' => hf a' b' (List.mem_cons_of_mem _ hb') ha') _ (hf a b List.mem_cons_self ha)

theorem foldl_reach {α β : Type} (f : α → β → α) (I R : α → Prop) (x : β) :
    ∀ (l : List β), x ∈ l → (∀ a b, b ∈ l → I a → I (f a b)) →
      (∀ a b, b ∈ l → I a → R a → R (f a b)) → (∀ a, I a → R (f a x)) →
      ∀ a, I a → R (l.foldl f a) := by
  intro l
  induction l with
  | nil => intro hx; cases hx
  | cons b rest ih =>
    intro hx hI hR hmk a ha
    simp only [List.foldl_cons]
    have hI' : ∀ a b, b ∈ rest → I a → I (f a b) := fun a b hb => hI a b (List.mem_cons_of_mem _ hb)
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hboth := foldl_inv f (fun a => I a ∧ R a) rest
        (fun a b hb h => ⟨hI a b (List.mem_cons_of_mem _ hb) h.1, hR a b (List.mem_cons_of_mem _ hb) h.1 h.2⟩)
        (f a x) ⟨hI a x List.mem_cons_self ha, hmk a ha⟩
      exact hboth.2
    · exact ih hx' hI' (fun a b hb => hR a b (List.mem_cons_of_mem _ hb)) hmk _ (hI a b List.mem_cons_self ha)

/-- An invariant of every send is an invariant of the line advance. -/
theorem advance_inv (I : PureLine → Prop) (L : PureLine)
    (h : ∀ kv ∈ L, ∀ d ∈ mapSons φ kv.1.step kv.1.index, ∀ acc, I acc → I (sendToW φ kv.2 acc d))
    (h0 : I []) : I (pureAdvanceW φ L) := by
  unfold pureAdvanceW sendAllW
  exact foldl_inv _ I L (fun a kv hkv ha => foldl_inv _ I _ (fun a d hd ha => h kv hkv d hd a ha) a ha) [] h0

/-- A property one send establishes and every send keeps holds after the line advance. -/
theorem advance_reach (I R : PureLine → Prop) (L : PureLine)
    (hI : ∀ kv ∈ L, ∀ d ∈ mapSons φ kv.1.step kv.1.index, ∀ acc, I acc → I (sendToW φ kv.2 acc d))
    (hR : ∀ kv ∈ L, ∀ d ∈ mapSons φ kv.1.step kv.1.index, ∀ acc, I acc → R acc → R (sendToW φ kv.2 acc d))
    (kv₀ : NodeId × GPathM) (hkv₀ : kv₀ ∈ L) (d₀ : NodeId) (hd₀ : d₀ ∈ mapSons φ kv₀.1.step kv₀.1.index)
    (hmk : ∀ acc, I acc → R (sendToW φ kv₀.2 acc d₀)) (h0 : I []) : R (pureAdvanceW φ L) := by
  unfold pureAdvanceW sendAllW
  refine foldl_reach _ I R kv₀ L hkv₀ ?_ ?_ ?_ [] h0
  · intro a kv hkv ha
    exact foldl_inv _ I _ (fun a d hd ha => hI kv hkv d hd a ha) a ha
  · intro a kv hkv ha hr
    exact (foldl_inv _ (fun a => I a ∧ R a) _ (fun a d hd h => ⟨hI kv hkv d hd a h.1, hR kv hkv d hd a h.1 h.2⟩)
      a ⟨ha, hr⟩).2
  · intro a ha
    exact foldl_reach _ I R d₀ _ hd₀ (fun a d hd => hI kv₀ hkv₀ d hd a) (fun a d hd => hR kv₀ hkv₀ d hd a)
      hmk a ha

-- ============================================================
-- insertPure
-- ============================================================

theorem key_unique : ∀ (line : PureLine), (line.map (·.1)).Nodup →
    ∀ d A B, (d, A) ∈ line → (d, B) ∈ line → A = B := by
  intro line
  induction line with
  | nil => intro _ d A B h; cases h
  | cons e rest ih =>
    intro hnd d A B hA hB
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hA with hA | hA <;> rcases List.mem_cons.mp hB with hB | hB
    · rw [← hA] at hB; exact (Prod.mk.inj hB).2.symm
    · exact absurd ⟨(d, B), hB, by rw [← hA]⟩ hnd.1
    · exact absurd ⟨(d, A), hA, by rw [← hB]⟩ hnd.1
    · exact ih hnd.2 d A B hA hB

theorem insert_grows (line : PureLine) (key : NodeId) (g : GPathM) (hnd : (line.map (·.1)).Nodup)
    (d : NodeId) (J : GPathM) (h : (d, J) ∈ line) :
    ∃ J', (d, J') ∈ insertPure line key g ∧ Grown J J' := by
  unfold insertPure
  cases hf : line.find? (fun kv => kv.1 == key) with
  | none => exact ⟨J, List.mem_append_left _ h, Grown.refl J⟩
  | some e =>
    simp only
    by_cases hdk : d = key
    · have he : e ∈ line := List.mem_of_find?_eq_some hf
      have hek : e.1 = key := eq_of_beq (List.find?_some (p := fun kv : NodeId × GPathM => kv.1 == key) hf)
      have heJ : e.2 = J := key_unique line hnd d e.2 J (by rw [hdk, ← hek]; exact he) h
      refine ⟨doJoin e.2 g, List.mem_map.mpr ⟨(d, J), h, by simp [hdk]⟩, ?_⟩
      rw [heJ]
      unfold doJoin
      split
      · exact grown_join_left J g
      · exact Grown.refl J
    · exact ⟨J, List.mem_map.mpr ⟨(d, J), h, by simp [hdk]⟩, Grown.refl J⟩

theorem insert_new (line : PureLine) (key : NodeId) (g : GPathM)
    (hok : ∀ e, (key, e) ∈ line → okJoin e g = true) :
    ∃ J', (key, J') ∈ insertPure line key g ∧ Grown g J' := by
  unfold insertPure
  cases hf : line.find? (fun kv => kv.1 == key) with
  | none => exact ⟨g, List.mem_append_right _ List.mem_cons_self, Grown.refl g⟩
  | some e =>
    simp only
    have he : e ∈ line := List.mem_of_find?_eq_some hf
    have hek : e.1 = key := eq_of_beq (List.find?_some (p := fun kv : NodeId × GPathM => kv.1 == key) hf)
    have hok' := hok e.2 (by rw [← hek]; exact he)
    refine ⟨doJoin e.2 g, List.mem_map.mpr ⟨e, he, by simp [hek]⟩, ?_⟩
    simp only [doJoin, hok', if_pos]
    exact grown_join_right e.2 g hok'

theorem insert_src (line : PureLine) (key : NodeId) (g : GPathM) (d : NodeId) (B : GPathM)
    (h : (d, B) ∈ insertPure line key g) :
    (d = key ∧ (B = g ∨ ∃ e, (key, e) ∈ line ∧ B = doJoin e g)) ∨ ((d, B) ∈ line ∧ d ≠ key) := by
  unfold insertPure at h
  cases hf : line.find? (fun kv => kv.1 == key) with
  | none =>
    rw [hf] at h
    rcases List.mem_append.mp h with h | h
    · right
      refine ⟨h, fun hdk => ?_⟩
      have := List.find?_eq_none.mp hf (d, B) h
      simp [hdk] at this
    · have := List.mem_singleton.mp h
      exact Or.inl ⟨(Prod.mk.inj this).1, Or.inl (Prod.mk.inj this).2⟩
  | some e =>
    rw [hf] at h
    have he : e ∈ line := List.mem_of_find?_eq_some hf
    have hek : e.1 = key := eq_of_beq (List.find?_some (p := fun kv : NodeId × GPathM => kv.1 == key) hf)
    obtain ⟨⟨xd, xB⟩, hx, hxeq⟩ := List.mem_map.mp h
    by_cases hxk : xd = key
    · simp only [hxk, beq_self_eq_true, if_true] at hxeq
      exact Or.inl ⟨(Prod.mk.inj hxeq).1.symm, Or.inr ⟨e.2, by rw [← hek]; exact he, (Prod.mk.inj hxeq).2.symm⟩⟩
    · have hne : (xd == key) = false := beq_false_of_ne hxk
      simp only [hne] at hxeq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxeq
      exact Or.inr ⟨hx, hxk⟩

-- ============================================================
-- One send
-- ============================================================

/-- The state one send produces. -/
abbrev sent (g : GPathM) (d : NodeId) : GPathM :=
  upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d ""

theorem sendToW_eq (g : GPathM) (acc : PureLine) (d : NodeId) :
    sendToW φ g acc d = if isValid (sent φ g d) then insertPure acc d (sent φ g d) else acc := rfl

theorem mem_of_hasNode {g : GPathM} (hnd : NodupIds g) {q : PathNodeId} (h : GownersNodes.HasNode g q) :
    Mem g q := by
  obtain ⟨m, hm, hmid⟩ := h
  exact ⟨m, by rw [← hmid]; exact node?_of_mem hnd m hm⟩

theorem own_mem {g : GPathM} (hm : MInv φ g) : ∀ x m, g.node? x = some m → ∀ q ∈ m.owners, Mem g q :=
  fun _ m hx q hq => mem_of_hasNode hm.rctx.nodup (hm.own m (List.mem_of_find?_eq_some hx) q hq)

/-- **A send of a branch state sits inside the same send of the whole state**, which is valid. -/
theorem embedded_send (k : Int) (kvb kvf : NodeId × GPathM) (hsb : StateOkF φ k kvb)
    (hsf : StateOkF φ k kvf) (hmb : MInv φ kvb.2) (hmf : MInv φ kvf.2) (hkey : kvf.1 = kvb.1)
    (he : Embedded kvb.2 kvf.2) (d : NodeId) (hd : d ∈ mapSons φ kvb.1.step kvb.1.index)
    (hv : isValid (sent φ kvb.2 d) = true) :
    Embedded (sent φ kvb.2 d) (sent φ kvf.2 d) ∧ isValid (sent φ kvf.2 d) = true := by
  have hWe := embedded_filterWeakAll (weakReqOfCnf φ d) kvb.2 kvf.2 he
  have hwnb := (filterWeakAll_frame (weakReqOfCnf φ d) kvb.2).1
  have hwnf := (filterWeakAll_frame (weakReqOfCnf φ d) kvf.2).1
  have hframe : ∀ (l : List NodeId) (g : GPathM), (l.foldl filterRequire g).nodes = g.nodes := by
    intro l
    induction l with
    | nil => intro g; rfl
    | cons r rs ih => intro g; exact ih (filterRequire g r)
  have hvF : isValid (filterAllAgg (filterWeakAll kvb.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) = true := by
    by_cases h : isValid (filterAllAgg (filterWeakAll kvb.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) = true
    · exact h
    · exfalso
      have heq : sent φ kvb.2 d = filterAllAgg (filterWeakAll kvb.2 (weakReqOfCnf φ d)) (reqOfCnf φ d) := by
        simp only [sent, upFilteringWeak, GPathM.up]
        rw [if_neg h]
      rw [heq] at hv
      exact h hv
  have hRFb : ReadableAgg (filterAllAgg (filterWeakAll kvb.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) :=
    ⟨filterWeakAll kvb.2 (weakReqOfCnf φ d), (reqOfCnf φ d), ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmb.rctx, rfl⟩
  have hsW : Sons.SMP (filterWeakAll kvb.2 (weakReqOfCnf φ d)) := by unfold Sons.SMP; rw [hwnb]; exact hmb.smp
  have hnW : Parents.NotRoot (filterWeakAll kvb.2 (weakReqOfCnf φ d)) := by
    unfold Parents.NotRoot; rw [hwnb]; exact hmb.rctx.shape.notroot
  have hpW : Sons.PMS (filterWeakAll kvb.2 (weakReqOfCnf φ d)) := by unfold Sons.PMS; rw [hwnb]; exact hmb.pms
  have hnS : Sons.SN (filterWeakAll kvb.2 (weakReqOfCnf φ d)) := by
    unfold Sons.SN GownersNodes.HasNode; rw [hwnb]; exact hmb.sn
  have hsmpG : Sons.SMP ((reqOfCnf φ d).foldl filterRequire (filterWeakAll kvf.2 (weakReqOfCnf φ d))) := by
    unfold Sons.SMP; rw [hframe, hwnf]; exact hmf.smp
  have hnrG : Parents.NotRoot ((reqOfCnf φ d).foldl filterRequire (filterWeakAll kvf.2 (weakReqOfCnf φ d))) := by
    unfold Parents.NotRoot; rw [hframe, hwnf]; exact hmf.rctx.shape.notroot
  have hndW : NodupIds (filterWeakAll kvb.2 (weakReqOfCnf φ d)) := by
    unfold NodupIds; rw [hwnb]; exact hmb.rctx.nodup
  have hFe := embedded_filterAllAgg (filterWeakAll kvb.2 (weakReqOfCnf φ d)) (filterWeakAll kvf.2 (weakReqOfCnf φ d)) (reqOfCnf φ d) hWe hndW hRFb hvF
    (AnchoredSurvive.SMP_filterAllAgg _ hsW hnW _) (AggInvariants.PMS_filterAllAgg _ _ hpW)
    (AggInvariants.SN_filterAllAgg _ _ hnS) hsmpG hnrG
  have rcFb := RCtx_of_readableAgg _ hRFb
  have hkf : ReaderAgg.Keeps kvf.2 (filterAllAgg (filterWeakAll kvf.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) :=
    ReaderAgg.Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have hkb : ReaderAgg.Keeps kvb.2 (filterAllAgg (filterWeakAll kvb.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) :=
    ReaderAgg.Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have rcFf := ReaderAgg.RCtx_of_keeps hkf hmf.rctx
  have hmp : (filterAllAgg (filterWeakAll kvb.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)).map_parent =
      (filterAllAgg (filterWeakAll kvf.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)).map_parent := by
    rw [hkb.1.map_parent_eq, hkf.1.map_parent_eq, hsb.par, hsf.par, hkey]
  have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kvb hsb d hd hv
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hsok.onMap
  have hdF : d.step = (filterAllAgg (filterWeakAll kvb.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)).current_step := by
    rw [hkb.1.step_eq, hsb.step, hdstep]
  have hup := embedded_up _ _ d "" hFe hvF hmp hdF rcFb.below rcFf.below rcFb.shape.pbelow
    rcFb.nodup rcFb.gn rcFb.ownb
  exact ⟨hup, isValid_of_embedded hup hv⟩

-- ============================================================
-- The whole line, and the branch line
-- ============================================================

theorem lineInv_nil (k : Int) : LineInv φ k [] :=
  ⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

/-- **On the whole line, a valid send grows into the entry of its map node.** -/
theorem full_reach (hwf : WF φ) (k : Int) (L : PureLine) (hl : LineInv φ k L) (kv : NodeId × GPathM)
    (hkv : kv ∈ L) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hv : isValid (sent φ kv.2 d) = true) :
    ∃ J, (d, J) ∈ pureAdvanceW φ L ∧ Grown (sent φ kv.2 d) J := by
  refine advance_reach φ (LineInv φ (k + 1)) (fun acc => ∃ J, (d, J) ∈ acc ∧ Grown (sent φ kv.2 d) J) L
    (fun kv' hkv' d' hd' acc ha => LineInv_sendToW φ hwf k kv' (hl.1.2 kv' hkv') (hl.2 kv' hkv') d' hd' acc ha)
    ?_ kv hkv d hd ?_ (lineInv_nil φ (k + 1))
  · intro kv' _ d' _ acc ha hr
    obtain ⟨J, hJ, hg⟩ := hr
    rw [sendToW_eq]
    split
    · obtain ⟨J', hJ', hg'⟩ := insert_grows acc d' _ ha.1.1 d J hJ
      exact ⟨J', hJ', Grown.trans hg hg'⟩
    · exact ⟨J, hJ, hg⟩
  · intro acc ha
    rw [sendToW_eq, if_pos hv]
    exact insert_new acc d _ (fun e he => okJoin_of_stateOkF φ (k + 1) d e _ (ha.1.2 (d, e) he)
      (StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv (hl.1.2 kv hkv) d hd hv))

/-- **On the branch line, the entry of a map node sits inside any state containing every branch send to
that node.** -/
theorem branch_union (hwf : WF φ) (k : Int) (L : PureLine) (hl : LineInv φ k L) (d : NodeId) (J : GPathM)
    (hH : ∀ kv ∈ L, d ∈ mapSons φ kv.1.step kv.1.index → isValid (sent φ kv.2 d) = true →
      Embedded (sent φ kv.2 d) J) :
    ∀ B, (d, B) ∈ pureAdvanceW φ L → Embedded B J := by
  have main := advance_inv φ (fun acc => LineInv φ (k + 1) acc ∧ ∀ B, (d, B) ∈ acc → Embedded B J) L ?_
    ⟨lineInv_nil φ (k + 1), fun B hB => absurd hB List.not_mem_nil⟩
  · exact main.2
  intro kv hkv d' hd' acc ⟨ha, hr⟩
  refine ⟨LineInv_sendToW φ hwf k kv (hl.1.2 kv hkv) (hl.2 kv hkv) d' hd' acc ha, ?_⟩
  intro B hB
  rw [sendToW_eq] at hB
  split at hB
  · next hv =>
    rcases insert_src acc d' _ d B hB with ⟨hdd, hB'⟩ | ⟨hB', _⟩
    · subst hdd
      have hS := hH kv hkv hd' hv
      rcases hB' with rfl | ⟨e, he, rfl⟩
      · exact hS
      · have hse := ha.1.2 (d, e) he
        have hss := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv (hl.1.2 kv hkv) d hd' hv
        have hok := okJoin_of_stateOkF φ (k + 1) d e _ hse hss
        have hme : MInv φ e := ha.2 (d, e) he
        have hms := MInv_sent φ hwf k kv (hl.1.2 kv hkv) (hl.2 kv hkv) d hd' hv
        have hok' : okJoin e (sent φ kv.2 d) = true := hok
        unfold doJoin
        rw [if_pos hok']
        exact embedded_join_same e _ J (hr e he) hS (own_mem φ hme) (own_mem φ hms)
          hme.rctx.shape.pn hms.rctx.shape.pn hme.rctx.nodup hms.rctx.nodup
    · exact hr B hB'
  · exact hr B hB

/-- Every entry of the next line comes from some valid send to its map node. -/
theorem advance_origin (L : PureLine) :
    ∀ d B, (d, B) ∈ pureAdvanceW φ L →
      ∃ kv ∈ L, d ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 d) = true := by
  have main := advance_inv φ (fun acc => ∀ d B, (d, B) ∈ acc →
      ∃ kv ∈ L, d ∈ mapSons φ kv.1.step kv.1.index ∧ isValid (sent φ kv.2 d) = true) L ?_
    (fun d B h => absurd h List.not_mem_nil)
  · exact main
  intro kv hkv d' hd' acc hr d B hB
  rw [sendToW_eq] at hB
  split at hB
  · next hv =>
    rcases insert_src acc d' _ d B hB with ⟨hdd, _⟩ | ⟨hB', _⟩
    · rw [hdd]; exact ⟨kv, hkv, hd', hv⟩
    · exact hr d B hB'
  · exact hr d B hB

/-- A branch line sits inside a whole line, key by key. -/
def LineEmb (Lb Lf : PureLine) : Prop := ∀ kv ∈ Lb, ∃ kv' ∈ Lf, kv'.1 = kv.1 ∧ Embedded kv.2 kv'.2

/-- **The line step**: the next branch line sits inside the next whole line. -/
theorem lineEmb_advance (hwf : WF φ) (k : Int) (Lb Lf : PureLine) (hlb : LineInv φ k Lb)
    (hlf : LineInv φ k Lf) (he : LineEmb Lb Lf) : LineEmb (pureAdvanceW φ Lb) (pureAdvanceW φ Lf) := by
  rintro ⟨d, B⟩ hB
  obtain ⟨kvb, hkvb, hd, hv⟩ := advance_origin φ Lb d B hB
  obtain ⟨kvf, hkvf, hkey, hemb⟩ := he kvb hkvb
  have hdf : d ∈ mapSons φ kvf.1.step kvf.1.index := by rw [hkey]; exact hd
  obtain ⟨_, hvf⟩ := embedded_send φ k kvb kvf (hlb.1.2 kvb hkvb) (hlf.1.2 kvf hkvf) (hlb.2 kvb hkvb)
    (hlf.2 kvf hkvf) hkey hemb d hd hv
  obtain ⟨J, hJ, _⟩ := full_reach φ hwf k Lf hlf kvf hkvf d hdf hvf
  have hnd := (LineInv_pureAdvanceW φ hwf k Lf hlf).1.1
  refine ⟨(d, J), hJ, rfl, branch_union φ hwf k Lb hlb d J ?_ B hB⟩
  intro kvb' hkvb' hd' hv'
  obtain ⟨kvf', hkvf', hkey', hemb'⟩ := he kvb' hkvb'
  obtain ⟨hes', hvf'⟩ := embedded_send φ k kvb' kvf' (hlb.1.2 kvb' hkvb') (hlf.1.2 kvf' hkvf')
    (hlb.2 kvb' hkvb') (hlf.2 kvf' hkvf') hkey' hemb' d hd' hv'
  obtain ⟨J', hJ', hg'⟩ := full_reach φ hwf k Lf hlf kvf' hkvf' d (by rw [hkey']; exact hd') hvf'
  have hJJ := key_unique _ hnd d J J' hJ hJ'
  rw [hJJ]
  exact embedded_of_grown hes' hg'

theorem lineEmb_restrict (P : List NodeId) (k : Int) (Lb Lf : PureLine) (he : LineEmb Lb Lf) :
    LineEmb (restrictLine P k Lb) Lf :=
  fun kv hkv => he kv (List.mem_filter.mp hkv).1

theorem lineInv_restrict (P : List NodeId) (k k' : Int) (L : PureLine) (hl : LineInv φ k L) :
    LineInv φ k (restrictLine P k' L) := by
  refine ⟨⟨?_, fun kv hkv => hl.1.2 kv (List.mem_filter.mp hkv).1⟩, fun kv hkv => hl.2 kv (List.mem_filter.mp hkv).1⟩
  exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) hl.1.1

theorem embedded_refl (g : GPathM) : Embedded g g :=
  ⟨rfl, fun _ h => h, fun _ m hm => ⟨m, hm, fun _ hq _ => hq, fun _ hq _ => hq⟩⟩

theorem branchSteps_embedded (hwf : WF φ) (P : List NodeId) :
    ∀ (n : Nat) (k : Int) (Lb Lf : PureLine), LineInv φ k Lb → LineInv φ k Lf → LineEmb Lb Lf →
      LineInv φ (k + n) (branchSteps φ P n k Lb) ∧ LineEmb (branchSteps φ P n k Lb) (pureStepsW φ n Lf) := by
  intro n
  induction n with
  | zero => intro k Lb Lf hlb _ he; simpa [branchSteps, pureStepsW] using And.intro hlb he
  | succ n ih =>
    intro k Lb Lf hlb hlf he
    have h := ih (k + 1) (restrictLine P (k + 1) (pureAdvanceW φ Lb)) (pureAdvanceW φ Lf)
      (lineInv_restrict φ P (k + 1) (k + 1) _ (LineInv_pureAdvanceW φ hwf k Lb hlb))
      (LineInv_pureAdvanceW φ hwf k Lf hlf)
      (lineEmb_restrict P (k + 1) _ _ (lineEmb_advance φ hwf k Lb Lf hlb hlf he))
    have hcast : k + 1 + (n : Int) = k + ((n + 1 : Nat) : Int) := by omega
    rw [hcast] at h
    exact h

/-- **The branch run keeps the machine's invariants on every state, and sits inside `pureRunW`, key by
key.** -/
theorem branchRun_embedded (hwf : WF φ) (P : List NodeId) :
    LineInv φ (stepCount φ - 1) (branchRun φ P) ∧ LineEmb (branchRun φ P) (pureRunW φ) := by
  have hpos := ConservationCore.stepCount_pos φ
  have h0 := LineInv_init φ hwf
  have h := branchSteps_embedded φ hwf P (stepCount φ - 1).toNat 0 (restrictLine P 0 (pureInit φ)) (pureInit φ)
    (lineInv_restrict φ P 0 0 _ h0) h0
    (fun kv hkv => ⟨kv, (List.mem_filter.mp hkv).1, rfl, embedded_refl kv.2⟩)
  have hcast : (0 : Int) + (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  rw [hcast] at h
  exact h

/-- info: 'AbsSat.GraphPath.Model.BranchLines.branchRun_embedded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms branchRun_embedded

end AbsSat.GraphPath.Model.BranchLines
