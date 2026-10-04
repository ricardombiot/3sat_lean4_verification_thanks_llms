-- lean_project/AbsSat/GraphPath/Model/BranchCompat.lean
import AbsSat.GraphPath.Model.BranchLines

/-!
# A branch agrees with its pins, and survives them inside the whole machine

`BranchLines.branchRun_embedded`: every state of the branch of the pins `P` sits inside the state with
the same key of the whole machine. To carry it through the reader's pins, `survives_of_embedded` asks
the branch to **agree with the pins**: on the step of a pin `r ∈ P`, every node carries `r`. This
module proves it and draws the consequence.

## The compatibility invariant

* `Compat P g` — every node of `g` on the step of a pin `r ∈ P` carries `r`.
* `KeyShape P d g` — the shape of an entry of key `d` before the line is restricted: its nodes on
  `d`'s step carry `d`, and on the step of any other pin they carry that pin.
* A send to `d` adds exactly one node, carrying `d` on the new step, and keeps nodes of the sending
  state, which lie below (`keyShape_sent`); joins only gather nodes (`keyShape_doJoin`); so every entry
  of a line advance has `KeyShape` (`advance_keyShape`), and the restriction of the line keeps only
  keys that agree with the pin of the new step, which turns `KeyShape` into `Compat`
  (`compat_restrict`).
* **`branchRun_compat`** — every state of the branch run agrees with its pins.

## Through the reader's pins

* `embedded_pin` — a valid reader-kind state that agrees with the pins and sits inside `G` still sits
  inside the pinned `G`.
* **`reader_pins_valid_of_branch`** — if a final state of the branch of `P` is valid after one
  aggressive review, then the final state of the whole machine with the same key stays **valid under
  every sequence of pins taken from `P`**, pinned one at a time as the reader does.
-/

namespace AbsSat.GraphPath.Model.BranchCompat

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
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_pureAdvanceW LineInv_init)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF StateOkF_sent Fsac prunes_Fsac)
open AbsSat.GraphPath.Model.AnchoredSurvive
open AbsSat.GraphPath.Model.AggFixpoint
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchLines

variable (φ : Cnf)

/-- Every node on the step of a pin carries that pin. -/
def Compat (P : List NodeId) (g : GPathM) : Prop :=
  ∀ r ∈ P, ∀ p, Mem g p → p.id.step = r.step → p.id = r

/-- The shape of an entry of key `d`, before its line is restricted. -/
def KeyShape (P : List NodeId) (d : NodeId) (g : GPathM) : Prop :=
  (∀ p, Mem g p → p.id.step = d.step → p.id = d) ∧
    (∀ r ∈ P, r.step ≠ d.step → ∀ p, Mem g p → p.id.step = r.step → p.id = r)

theorem mem_join {B₁ B₂ : GPathM} {p : PathNodeId} (h : Mem (join B₁ B₂) p) : Mem B₁ p ∨ Mem B₂ p := by
  obtain ⟨m, hm⟩ := h
  rcases join_node?_source B₁ B₂ p m hm with h | h
  · exact Or.inl (Option.isSome_iff_exists.mp h)
  · exact Or.inr (Option.isSome_iff_exists.mp h)

theorem keyShape_doJoin (P : List NodeId) (d : NodeId) (e g : GPathM) (he : KeyShape P d e)
    (hg : KeyShape P d g) : KeyShape P d (doJoin e g) := by
  unfold doJoin
  split
  · refine ⟨fun p hp hs => ?_, fun r hr hne p hp hs => ?_⟩
    · rcases mem_join hp with hp | hp
      · exact he.1 p hp hs
      · exact hg.1 p hp hs
    · rcases mem_join hp with hp | hp
      · exact he.2 r hr hne p hp hs
      · exact hg.2 r hr hne p hp hs
  · exact he

/-- **A send to `d` from a compatible state has the key shape of `d`.** -/
theorem keyShape_sent (P : List NodeId) (g : GPathM) (d : NodeId) (hc : Compat P g)
    (hbelow : ∀ p, Mem g p → p.id.step < d.step) (hv : isValid (sent φ g d) = true) :
    KeyShape P d (sent φ g d) := by
  have hk : Keeps g (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) :=
    Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have hvF : isValid (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) = true := by
    by_cases h : isValid (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) = true
    · exact h
    · exfalso
      have heq : sent φ g d = filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d) := by
        simp only [sent, upFilteringWeak, GPathM.up]
        rw [if_neg h]
      rw [heq] at hv
      exact h hv
  have heq : sent φ g d = addNode (filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) d "" := by
    simp only [sent, upFilteringWeak, GPathM.up]
    rw [if_pos hvF]
  rw [heq]
  refine ⟨fun p hp hs => ?_, fun r hr hne p hp hs => ?_⟩
  · rcases mem_addNode hp with hrow | hpF
    · exact mapId_of_mem_newRowIds _ d p hrow
    · have := hbelow p (mem_of_pruned hk.1 hpF)
      omega
  · rcases mem_addNode hp with hrow | hpF
    · exact absurd (by rw [← mapId_of_mem_newRowIds _ d p hrow]; exact hs.symm) hne
    · exact hc r hr p (mem_of_pruned hk.1 hpF) hs

/-- The nodes of a line state lie below its current step, which is one past the line. -/
theorem below_of_lineInv (k : Int) (L : PureLine) (hl : LineInv φ k L) (kv : NodeId × GPathM) (hkv : kv ∈ L) :
    ∀ p, Mem kv.2 p → p.id.step < k + 1 := by
  rintro p ⟨m, hm⟩
  have hmem := List.mem_of_find?_eq_some hm
  rw [← node?_id_eq _ p m hm, ← (hl.1.2 kv hkv).step]
  exact (hl.2 kv hkv).rctx.below m hmem

/-- **Every entry of a line advance from compatible states has its key shape.** -/
theorem advance_keyShape (P : List NodeId) (k : Int) (L : PureLine) (hl : LineInv φ k L)
    (hc : ∀ kv ∈ L, Compat P kv.2) : ∀ d B, (d, B) ∈ pureAdvanceW φ L → KeyShape P d B := by
  have main := advance_inv φ (fun acc => ∀ d B, (d, B) ∈ acc → KeyShape P d B) L ?_
    (fun d B h => absurd h List.not_mem_nil)
  · exact main
  intro kv hkv d' hd' acc hr d B hB
  rw [sendToW_eq] at hB
  split at hB
  · next hv =>
    have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv (hl.1.2 kv hkv) d' hd' hv
    have hdstep : d'.step = k + 1 := mapNodes_step φ (k + 1) d' hsok.onMap
    have hS := keyShape_sent φ P kv.2 d' (hc kv hkv)
      (fun p hp => by rw [hdstep]; exact below_of_lineInv φ k L hl kv hkv p hp) hv
    rcases insert_src acc d' _ d B hB with ⟨hdd, hB'⟩ | ⟨hB', _⟩
    · subst hdd
      rcases hB' with rfl | ⟨e, he, rfl⟩
      · exact hS
      · exact keyShape_doJoin P d e _ (hr d e he) hS
    · exact hr d B hB'
  · exact hr d B hB

/-- **Restricting a line turns the key shape into compatibility.** -/
theorem compat_restrict (P : List NodeId) (k : Int) (L : PureLine) (hl : LineInv φ k L)
    (hks : ∀ d B, (d, B) ∈ L → KeyShape P d B) : ∀ kv ∈ restrictLine P k L, Compat P kv.2 := by
  rintro ⟨d, B⟩ hkv r hr p hp hs
  obtain ⟨hmem, hall⟩ := List.mem_filter.mp hkv
  have hdk : d.step = k := mapNodes_step φ k d (hl.1.2 (d, B) hmem).onMap
  have hrk := List.all_eq_true.mp hall r hr
  have hshape := hks d B hmem
  by_cases hrd : r.step = d.step
  · have hne : (r.step != k) = false := by simp [hrd, hdk]
    simp only [hne, Bool.false_or] at hrk
    have hdr : d = r := eq_of_beq hrk
    rw [← hdr]
    exact hshape.1 p hp (by rw [hs, hrd])
  · exact hshape.2 r hr hrd p hp hs

theorem keyShape_initSeed (P : List NodeId) (d : NodeId) : KeyShape P d (GPathM.initSeed d "") := by
  have hmem : ∀ p, Mem (GPathM.initSeed d "") p → p = { id := d, parent_id := none } := by
    rintro p ⟨m, hm⟩
    have hmm := List.mem_of_find?_eq_some hm
    rw [initSeed_nodes] at hmm
    rw [← node?_id_eq _ p m hm, List.mem_singleton.mp hmm]
  refine ⟨fun p hp _ => by rw [hmem p hp], fun r _ hne p hp hs => ?_⟩
  exfalso
  rw [hmem p hp] at hs
  exact hne hs.symm

theorem init_keyShape (P : List NodeId) : ∀ d B, (d, B) ∈ pureInit φ → KeyShape P d B := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId) (acc : PureLine), (∀ d B, (d, B) ∈ acc → KeyShape P d B) →
      ∀ d B, (d, B) ∈ l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc →
        KeyShape P d B := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      refine ih _ ?_
      intro d B hB
      rcases insert_src acc x _ d B hB with ⟨hdd, hB'⟩ | ⟨hB', _⟩
      · subst hdd
        rcases hB' with rfl | ⟨e, he, rfl⟩
        · exact keyShape_initSeed P d
        · exact keyShape_doJoin P d e _ (h d e he) (keyShape_initSeed P d)
      · exact h d B hB'
  exact main _ [] (fun d B h => absurd h List.not_mem_nil)

theorem branchSteps_compat (hwf : WF φ) (P : List NodeId) :
    ∀ (n : Nat) (k : Int) (Lb : PureLine), LineInv φ k Lb → (∀ kv ∈ Lb, Compat P kv.2) →
      ∀ kv ∈ branchSteps φ P n k Lb, Compat P kv.2 := by
  intro n
  induction n with
  | zero => intro k Lb _ hc; exact hc
  | succ n ih =>
    intro k Lb hl hc
    have hl' := LineInv_pureAdvanceW φ hwf k Lb hl
    exact ih (k + 1) _ (lineInv_restrict φ P (k + 1) (k + 1) _ hl')
      (compat_restrict φ P (k + 1) _ hl' (advance_keyShape φ P k Lb hl hc))

/-- **Every state of the branch run agrees with its pins.** -/
theorem branchRun_compat (hwf : WF φ) (P : List NodeId) : ∀ kv ∈ branchRun φ P, Compat P kv.2 := by
  have h0 := LineInv_init φ hwf
  exact branchSteps_compat φ hwf P _ 0 _ (lineInv_restrict φ P 0 0 _ h0)
    (compat_restrict φ P 0 _ h0 (init_keyShape φ P))

-- ============================================================
-- Through the reader's pins
-- ============================================================

theorem mem_foldl_filterRequire_of (reqs : List NodeId) :
    ∀ (g : GPathM) (q : PathNodeId), q ∈ g.gowners → (∀ r ∈ reqs, q.id.step ≠ r.step ∨ q.id = r) →
      q ∈ (reqs.foldl filterRequire g).gowners := by
  induction reqs with
  | nil => intro g q hq _; exact hq
  | cons r rs ih =>
    intro g q hq hall
    simp only [List.foldl_cons]
    refine ih _ q ?_ (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr'))
    refine List.mem_filter.mpr ⟨hq, ?_⟩
    rcases hall r List.mem_cons_self with h | h
    · simp [h]
    · simp [h]

theorem foldl_filterRequire_frame (reqs : List NodeId) :
    ∀ g : GPathM, (reqs.foldl filterRequire g).nodes = g.nodes ∧
      (reqs.foldl filterRequire g).current_step = g.current_step := by
  induction reqs with
  | nil => intro g; exact ⟨rfl, rfl⟩
  | cons r rs ih => intro g; exact ih (filterRequire g r)

/-- **A valid reader-kind state that agrees with the pins stays inside the pinned outer state.** -/
theorem embedded_pin (B G : GPathM) (reqs : List NodeId) (h : Embedded B G) (a : AdjacentOwners.Adj B)
    (hok : AggOk B) (hsmp : Sons.SMP B) (hc : Compat reqs B) (hsmpG : Sons.SMP G)
    (hnrG : Parents.NotRoot G) : Embedded B (filterAllAgg G reqs) := by
  obtain ⟨hfn, hfs⟩ := foldl_filterRequire_frame reqs G
  have hnode : ∀ p, (reqs.foldl filterRequire G).node? p = G.node? p := by
    intro p; simp only [GPathM.node?, hfn]
  have memB : ∀ p ∈ B.gowners, Mem B p := by
    intro p hp
    obtain ⟨m, hm, hmid⟩ := a.rc.gn p hp
    exact ⟨m, by rw [← hmid]; exact node?_of_mem a.rc.nodup m hm⟩
  have h1 : Embedded B (reqs.foldl filterRequire G) := by
    refine ⟨h.step.trans hfs.symm, fun p hp => ?_, fun p m hm => ?_⟩
    · refine mem_foldl_filterRequire_of reqs G p (h.gow p hp) (fun r hr => ?_)
      by_cases hs : p.id.step = r.step
      · exact Or.inr (hc r hr p (memB p hp) hs)
      · exact Or.inl hs
    · rw [hnode]; exact h.node p m hm
  have sup := sup_of_embedded B _ a hok hsmp h1
  have hsmpF : Sons.SMP (reqs.foldl filterRequire G) := by unfold Sons.SMP; rw [hfn]; exact hsmpG
  have hnrF : Parents.NotRoot (reqs.foldl filterRequire G) := by unfold Parents.NotRoot; rw [hfn]; exact hnrG
  have hA := AOk_filterAllAgg (reqs.foldl filterRequire G) ⟨sup, hsmpF, hnrF⟩ []
    (fun r hr => absurd hr List.not_mem_nil)
  change AOk (filterAllAgg G reqs) _ _ at hA
  refine ⟨h.step.trans (pruned_filterAllAgg G reqs).step_eq.symm, fun p hp => hA.sup.gow p (memB p hp), ?_⟩
  intro x m hm
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hA.sup.node x ⟨m, hm⟩)
  have hmem := List.mem_of_find?_eq_some hm
  have hid := node?_id_eq _ x m hm
  refine ⟨n, hn, fun q hq hqm => hA.sup.own x q n ⟨m, hm, hq, hqm⟩ hn, fun q hq hqm => ?_⟩
  obtain ⟨mq, hmq⟩ := hqm
  have hxq : x ∈ mq.owners := by
    have hson : m.id ∈ mq.sons := hsmp m hmem q hq mq (List.mem_of_find?_eq_some hmq) (node?_id_eq _ q mq hmq)
    rw [hid] at hson
    exact (a.links q mq hmq).2 x hson
  have hstep : q.id.step + 1 = x.id.step := by
    have := a.rc.shape.pbelow m hmem q hq
    rw [hid] at this
    omega
  exact hA.sup.link x q n ⟨m, hm, (a.links x m hm).1 q hq, ⟨mq, hmq⟩⟩ ⟨mq, hmq, hxq, ⟨m, hm⟩⟩ hstep hn

/-- The reader's way of pinning: one pin at a time, each with the whole aggressive review. -/
def pinOneByOne (g : GPathM) (qs : List NodeId) : GPathM :=
  qs.foldl (fun g q => filterAllAgg g [q]) g

/-- A valid state inside `G` that agrees with `P` stays inside through every one-by-one pinning by pins
of `P`, and keeps the pinned state valid. -/
theorem inside_pinOneByOne (B : GPathM) (a : AdjacentOwners.Adj B) (hok : AggOk B) (hsmp : Sons.SMP B)
    (hvB : isValid B = true) (P : List NodeId) (hc : Compat P B) :
    ∀ (qs : List NodeId) (G : GPathM), (∀ q ∈ qs, q ∈ P) → ReadableAgg G → Sons.SMP G → Embedded B G →
      Embedded B (pinOneByOne G qs) ∧ isValid (pinOneByOne G qs) = true := by
  intro qs
  induction qs with
  | nil => intro G _ _ _ h; exact ⟨h, isValid_of_embedded h hvB⟩
  | cons q rest ih =>
    intro G hq hR hs h
    have hcq : Compat [q] B := fun r hr p hp hps => by
      rw [List.mem_singleton.mp hr] at hps ⊢
      exact hc q (hq q List.mem_cons_self) p hp hps
    have hnr := (RCtx_of_readableAgg G hR).shape.notroot
    have h' := embedded_pin B G [q] h a hok hsmp hcq hs hnr
    exact ih (filterAllAgg G [q]) (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))
      (ReadableAgg_filterAllAgg G hR [q]) (SMP_filterAllAgg G hs hnr [q]) h'

/-- **A valid branch keeps the whole machine's state valid under every one-by-one pinning by its pins.**
If a final state of the branch of `P` is valid after one aggressive review, the final state of the
whole machine with the same key, reviewed, stays valid however the reader pins it with pins of `P`. -/
theorem reader_pins_valid_of_branch (hwf : WF φ) (P : List NodeId) (kv : NodeId × GPathM)
    (hkv : kv ∈ branchRun φ P) (hv : isValid (filterAllAgg kv.2 []) = true) :
    ∃ kv' ∈ pureRunW φ, kv'.1 = kv.1 ∧
      ∀ qs, (∀ q ∈ qs, q ∈ P) → isValid (pinOneByOne (filterAllAgg kv'.2 []) qs) = true := by
  obtain ⟨hinv, hemb⟩ := branchRun_embedded φ hwf P
  obtain ⟨kv', hkv', hkey, he⟩ := hemb kv hkv
  have mb := hinv.2 kv hkv
  have mf := (ReaderAggRun.pureRunW_state φ hwf kv' hkv').1
  have hRB : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], mb.rctx, rfl⟩
  have hRG : ReadableAgg (filterAllAgg kv'.2 []) := ⟨kv'.2, [], mf.rctx, rfl⟩
  have hsB := SMP_filterAllAgg kv.2 mb.smp mb.rctx.shape.notroot []
  have hpB := AggInvariants.PMS_filterAllAgg kv.2 [] mb.pms
  have hnB := AggInvariants.SN_filterAllAgg kv.2 [] mb.sn
  have heBG := embedded_filterAllAgg kv.2 kv'.2 [] he mb.rctx.nodup hRB hv hsB hpB hnB mf.smp
    mf.rctx.shape.notroot
  have a := AdjacentOwners.adj_of_readable _ hRB hv hpB hnB
  have hok : AggOk (filterAllAgg kv.2 []) := aggOk_reviewAgg _ hv
  have hcB : Compat P (filterAllAgg kv.2 []) := fun r hr p hp hs =>
    branchRun_compat φ hwf P kv hkv r hr p (mem_of_pruned (pruned_filterAllAgg kv.2 []) hp) hs
  refine ⟨kv', hkv', hkey, fun qs hqs => ?_⟩
  exact (inside_pinOneByOne _ a hok hsB hv P hcB qs _ hqs hRG
    (SMP_filterAllAgg kv'.2 mf.smp mf.rctx.shape.notroot []) heBG).2

/-- info: 'AbsSat.GraphPath.Model.BranchCompat.reader_pins_valid_of_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reader_pins_valid_of_branch

end AbsSat.GraphPath.Model.BranchCompat
