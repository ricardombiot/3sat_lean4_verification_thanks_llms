-- lean_project/AbsSat/GraphPath/Model/Hereditary.lean
import AbsSat.GraphPath.Model.BranchReader

/-!
# Hereditary pin validity: the invariant to build up along the construction

The author's view: the machine builds the set of partial paths step by step, and every node the reader
can still choose belongs to a path that survives. As an invariant of a single state:

* `Fw g C` — the state `g` under the constraints `C` (each a weak filter: at a step, the allowed map
  nodes; a pin is the weak filter allowing one node), followed by the whole aggressive review.
* **`HPV g`** (hereditary pin validity) — whenever `g` is valid under `C`, adding as a pin any global
  owner still alive keeps it valid.

This module proves the reader's side: **`sat_of_hpv`** — a valid final state of the Improves machine
with `HPV` gives a model. The reader's state (pins one at a time) and `Fw` (constraints at once) are
related both ways through the embedding tools:

* `embedded_of_aok` — a reader-kind state whose tables survived as a support relation sits inside;
* `embedded_weak` — a valid reader-kind state that respects weak constraints stays inside the
  constrained state;
* `reader_inside_Fw` — the reader's state after pins `P` sits inside `Fw G P`, which is valid;
* `pin_valid_of_Fw` — if `Fw G (P ++ [q])` is valid, pinning `q` in the reader's state is valid.

What is left is to build `HPV` up along the construction (seed, sends, joins).
-/

namespace AbsSat.GraphPath.Model.Hereditary

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.AnchoredSurvive
open AbsSat.GraphPath.Model.AggFixpoint
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchCompat
open AbsSat.GraphPath.Model.BranchReader
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice)

/-- Constraints: at a step, the allowed map nodes. -/
abbrev Cons := List (Int × List NodeId)

/-- A pin as a constraint. -/
def pinC (q : NodeId) : Int × List NodeId := (q.step, [q])

/-- The state under constraints, reviewed. -/
def Fw (g : GPathM) (C : Cons) : GPathM := filterAllAgg (filterWeakAll g C) []

/-- **Hereditary pin validity.** -/
def HPV (g : GPathM) : Prop :=
  ∀ C : Cons, isValid (Fw g C) = true → ∀ q ∈ (Fw g C).gowners, isValid (Fw g (C ++ [pinC q.id])) = true

/-- Every node of `B` on a constrained step carries an allowed map node. -/
def WCompat (C : Cons) (B : GPathM) : Prop :=
  ∀ e ∈ C, ∀ p, Mem B p → p.id.step = e.1 → p.id ∈ e.2

/-- The nodes of a valid reader-kind state are its global owners. -/
theorem gowner_of_mem (B : GPathM) (a : AdjacentOwners.Adj B) {p : PathNodeId} (h : Mem B p) :
    p ∈ B.gowners := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨h0, h1⟩ := mem_bounds B a ⟨m, hm⟩
  exact (List.mem_filter.mp (Pinned.mem_ownersAt_gowners B a.ctx p m hm h0 h1)).1

/-- A reader-kind state whose tables survived as a support relation of `G'` sits inside `G'`. -/
theorem embedded_of_aok (B G' : GPathM) (a : AdjacentOwners.Adj B) (hsmp : Sons.SMP B)
    (hA : AOk G' (Mem B) (Rel B)) (hstep : B.current_step = G'.current_step) : Embedded B G' := by
  refine ⟨hstep, fun p hp => ?_, ?_⟩
  · obtain ⟨m, hm, hmid⟩ := a.rc.gn p hp
    exact hA.sup.gow p ⟨m, by rw [← hmid]; exact node?_of_mem a.rc.nodup m hm⟩
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
  have hs : q.id.step + 1 = x.id.step := by
    have := a.rc.shape.pbelow m hmem q hq
    rw [hid] at this
    omega
  exact hA.sup.link x q n ⟨m, hm, (a.links x m hm).1 q hq, ⟨mq, hmq⟩⟩ ⟨mq, hmq, hxq, ⟨m, hm⟩⟩ hs hn

/-- **A valid reader-kind state that respects weak constraints stays inside the constrained state.** -/
theorem embedded_weak (B G : GPathM) (C : Cons) (h : Embedded B G) (a : AdjacentOwners.Adj B)
    (hok : AggOk B) (hsmp : Sons.SMP B) (hc : WCompat C B) (hsmpG : Sons.SMP G)
    (hnrG : Parents.NotRoot G) : Embedded B (Fw G C) := by
  obtain ⟨hfn, hfs, _⟩ := filterWeakAll_frame C G
  have h1 : Embedded B (filterWeakAll G C) := by
    refine ⟨h.step.trans hfs.symm, fun p hp => ?_, fun p m hm => ?_⟩
    · refine (mem_filterWeakAll C G p).mpr ⟨h.gow p hp, fun e he hs => ?_⟩
      obtain ⟨m, hm, hmid⟩ := a.rc.gn p hp
      exact hc e he p ⟨m, by rw [← hmid]; exact node?_of_mem a.rc.nodup m hm⟩ hs
    · have hnode : (filterWeakAll G C).node? p = G.node? p := by simp only [GPathM.node?, hfn]
      rw [hnode]; exact h.node p m hm
  have sup := sup_of_embedded B _ a hok hsmp h1
  have hsF : Sons.SMP (filterWeakAll G C) := by unfold Sons.SMP; rw [hfn]; exact hsmpG
  have hnF : Parents.NotRoot (filterWeakAll G C) := by unfold Parents.NotRoot; rw [hfn]; exact hnrG
  have hA := AOk_filterAllAgg (filterWeakAll G C) ⟨sup, hsF, hnF⟩ [] (fun r hr => absurd hr List.not_mem_nil)
  exact embedded_of_aok B _ a hsmp hA
    (h.step.trans (hfs.symm.trans (pruned_filterAllAgg (filterWeakAll G C) []).step_eq.symm))

-- ============================================================
-- The reader's state against `Fw`
-- ============================================================

/-- Global owners after one-by-one pinning agree with every pin. -/
theorem gowners_pinOneByOne : ∀ (P : List NodeId) (g : GPathM),
    ∀ q ∈ (pinOneByOne g P).gowners, ∀ r ∈ P, q.id.step = r.step → q.id = r := by
  intro P
  induction P with
  | nil => intro g q _ r hr; cases hr
  | cons r0 rest ih =>
    intro g q hq r hr hs
    rcases List.mem_cons.mp hr with rfl | hr'
    · have hpr : Pruned (filterAllAgg g [r]) (pinOneByOne (filterAllAgg g [r]) rest) := by
        have main : ∀ (l : List NodeId) (x : GPathM), Pruned x (pinOneByOne x l) := by
          intro l
          induction l with
          | nil => intro x; exact Pruned.refl x
          | cons y ys ihl => intro x; exact Pruned.trans (pruned_filterAllAgg x [y]) (ihl _)
        exact main rest _
      exact ReaderAggRun.filterAllAgg_cleans g [r] r List.mem_cons_self q (hpr.gowners_sub q hq) hs
    · exact ih (filterAllAgg g [r0]) q hq r hr' hs

theorem pruned_pinOneByOne : ∀ (P : List NodeId) (g : GPathM), Pruned g (pinOneByOne g P) := by
  intro P
  induction P with
  | nil => intro g; exact Pruned.refl g
  | cons y ys ih => intro g; exact Pruned.trans (pruned_filterAllAgg g [y]) (ih _)

theorem embedded_of_pruned_self {G B : GPathM} (hpr : Pruned G B) (hnd : NodupIds G) : Embedded B G :=
  embedded_of_pruned hpr hnd (BranchLines.embedded_refl G)

/-- **The reader's state after pins `P` sits inside `Fw G P`, which is valid.** -/
theorem reader_inside_Fw (G : GPathM) (hR : ReadableAgg (filterAllAgg G [])) (hnd : NodupIds G)
    (hsmpG : Sons.SMP G) (hnrG : Parents.NotRoot G) (hpms : Sons.PMS G) (hsn : Sons.SN G)
    (P : List NodeId) (hv : isValid (pinOneByOne (filterAllAgg G []) P) = true) :
    Embedded (pinOneByOne (filterAllAgg G []) P) (Fw G (P.map pinC)) ∧
      isValid (Fw G (P.map pinC)) = true := by
  let g := pinOneByOne (filterAllAgg G []) P
  have hRg : ReadableAgg g := readable_pinOneByOne _ hR P
  have hpr : Pruned G g := Pruned.trans (pruned_filterAllAgg G []) (pruned_pinOneByOne P _)
  have hsmpg : Sons.SMP g := by
    have main : ∀ (l : List NodeId) (x : GPathM), ReadableAgg x → Sons.SMP x → Sons.SMP (pinOneByOne x l) := by
      intro l
      induction l with
      | nil => intro x _ h; exact h
      | cons y ys ih =>
        intro x hx h
        exact ih _ (ReadableAgg_filterAllAgg x hx [y]) (SMP_filterAllAgg x h (RCtx_of_readableAgg x hx).shape.notroot [y])
    exact main P _ hR (SMP_filterAllAgg G hsmpG hnrG [])
  have links : Sons.PMS g ∧ Sons.SN g := by
    have main : ∀ (l : List NodeId) (x : GPathM), Sons.PMS x → Sons.SN x →
        Sons.PMS (pinOneByOne x l) ∧ Sons.SN (pinOneByOne x l) := by
      intro l
      induction l with
      | nil => intro x h1 h2; exact ⟨h1, h2⟩
      | cons y ys ih =>
        intro x h1 h2
        exact ih _ (AggInvariants.PMS_filterAllAgg x [y] h1) (AggInvariants.SN_filterAllAgg x [y] h2)
    exact main P _ (AggInvariants.PMS_filterAllAgg G [] hpms) (AggInvariants.SN_filterAllAgg G [] hsn)
  have a := AdjacentOwners.adj_of_readable g hRg hv links.1 links.2
  have hok : AggOk g := by
    have form : ∀ (l : List NodeId) (x : GPathM), (∃ y reqs, x = filterAllAgg y reqs) →
        ∃ y reqs, pinOneByOne x l = filterAllAgg y reqs := by
      intro l
      induction l with
      | nil => intro x h; exact h
      | cons y ys ih => intro x _; exact ih _ ⟨x, [y], rfl⟩
    obtain ⟨y, reqs, hy⟩ := form P _ ⟨G, [], rfl⟩
    have hv' := hv
    change isValid (pinOneByOne (filterAllAgg G []) P) = true at hv'
    change AggOk (pinOneByOne (filterAllAgg G []) P)
    rw [hy] at hv' ⊢
    exact aggOk_reviewAgg _ hv'
  have hc : WCompat (P.map pinC) g := by
    intro e he p hp hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    have := gowners_pinOneByOne P _ p (gowner_of_mem g a hp) r hr hs
    rw [this]; exact List.mem_singleton_self r
  have hemb := embedded_weak g G (P.map pinC) (embedded_of_pruned_self hpr hnd) a hok hsmpg hc hsmpG hnrG
  exact ⟨hemb, isValid_of_embedded hemb hv⟩

/-- **If `Fw G (P ++ [q])` is valid, pinning `q` in the reader's state after `P` is valid.** -/
theorem pin_valid_of_Fw (φ : Cnf) (G : GPathM) (hmG : ReaderAggRun.MInv φ G) (P : List NodeId) (q : NodeId)
    (hv : isValid (Fw G ((P ++ [q]).map pinC)) = true) :
    isValid (filterAllAgg (pinOneByOne (filterAllAgg G []) P) [q]) = true := by
  let C := (P ++ [q]).map pinC
  have hwn := (filterWeakAll_frame C G).1
  have hRB : ReadableAgg (Fw G C) :=
    ⟨filterWeakAll G C, [], ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hmG.rctx, rfl⟩
  have hsW : Sons.SMP (filterWeakAll G C) := by unfold Sons.SMP; rw [hwn]; exact hmG.smp
  have hnW : Parents.NotRoot (filterWeakAll G C) := by unfold Parents.NotRoot; rw [hwn]; exact hmG.rctx.shape.notroot
  have hpW : Sons.PMS (filterWeakAll G C) := by unfold Sons.PMS; rw [hwn]; exact hmG.pms
  have hnS : Sons.SN (filterWeakAll G C) := by unfold Sons.SN GownersNodes.HasNode; rw [hwn]; exact hmG.sn
  have hsB := SMP_filterAllAgg _ hsW hnW []
  have a := AdjacentOwners.adj_of_readable _ hRB hv (AggInvariants.PMS_filterAllAgg _ [] hpW)
    (AggInvariants.SN_filterAllAgg _ [] hnS)
  have hok : AggOk (Fw G C) := aggOk_reviewAgg _ hv
  have hpr : Pruned G (Fw G C) :=
    Pruned.trans (ReaderAggRun.keeps_filterWeakAll G C).1 (pruned_filterAllAgg _ [])
  have hembG := embedded_of_pruned_self hpr hmG.rctx.nodup
  have hemb0 := embedded_pin (Fw G C) G [] hembG a hok hsB (fun r hr => absurd hr List.not_mem_nil)
    hmG.smp hmG.rctx.shape.notroot
  have hcomp : Compat (P ++ [q]) (Fw G C) := by
    intro r hr p hp hs
    have hg := gowner_of_mem _ a hp
    have hgW := (pruned_filterAllAgg (filterWeakAll G C) []).gowners_sub p hg
    have := ((mem_filterWeakAll C G p).mp hgW).2 (pinC r) (List.mem_map.mpr ⟨r, hr, rfl⟩) hs
    exact List.mem_singleton.mp this
  have hR0 : ReadableAgg (filterAllAgg G []) := ⟨G, [], hmG.rctx, rfl⟩
  have := (inside_pinOneByOne (Fw G C) a hok hsB hv (P ++ [q]) hcomp (P ++ [q]) (filterAllAgg G [])
    (fun r hr => hr) hR0 (SMP_filterAllAgg G hmG.smp hmG.rctx.shape.notroot []) hemb0).2
  rw [pinOneByOne_append] at this
  exact this

/-- **Soundness of the Improves verdict from hereditary pin validity of a final state.** -/
theorem sat_of_hpv (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) (hh : HPV kv.2) : Satisfiable φ := by
  have hm := (ReaderAggRun.pureRunW_state φ hwf kv hkv).1
  have hR₀ : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  have main : ∀ (m : Nat) (P : List NodeId), measure (pinOneByOne (filterAllAgg kv.2 []) P) ≤ m →
      isValid (pinOneByOne (filterAllAgg kv.2 []) P) = true → Inhabited (pinOneByOne (filterAllAgg kv.2 []) P) := by
    intro m
    induction m with
    | zero =>
      intro P hmeas hvP
      have hRP := readable_pinOneByOne _ hR₀ P
      match hch : hasChoice (pinOneByOne (filterAllAgg kv.2 []) P) with
      | false => exact Reader.inhabited_of_noChoice_readable _ (readable_of_readableAgg _ hRP) hvP hch
      | true =>
        obtain ⟨k, hkm, hck⟩ := List.any_eq_true.mp hch
        obtain ⟨q, hq, _⟩ := List.any_eq_true.mp hck
        exact absurd (measure_lt_of_choiceAt _ k hck q hq) (by omega)
    | succ m ih =>
      intro P hmeas hvP
      have hRP := readable_pinOneByOne _ hR₀ P
      match hch : hasChoice (pinOneByOne (filterAllAgg kv.2 []) P) with
      | false => exact Reader.inhabited_of_noChoice_readable _ (readable_of_readableAgg _ hRP) hvP hch
      | true =>
        obtain ⟨k, _, hck⟩ := List.any_eq_true.mp hch
        obtain ⟨q, hq, _⟩ := List.any_eq_true.mp hck
        have hlt := measure_lt_of_choiceAt _ k hck q hq
        obtain ⟨hemb, hvF⟩ := reader_inside_Fw kv.2 hR₀ hm.rctx.nodup hm.smp hm.rctx.shape.notroot hm.pms hm.sn
          P hvP
        have hqF : q ∈ (Fw kv.2 (P.map pinC)).gowners := hemb.gow q (List.mem_filter.mp hq).1
        have hvq := hh (P.map pinC) hvF q hqF
        have hvq' : isValid (Fw kv.2 ((P ++ [q.id]).map pinC)) = true := by
          rw [List.map_append]; exact hvq
        have hnext := pin_valid_of_Fw φ kv.2 hm P q.id hvq'
        have hm' : measure (pinOneByOne (filterAllAgg kv.2 []) (P ++ [q.id])) ≤ m := by
          rw [pinOneByOne_append]; omega
        obtain ⟨p, hp⟩ := ih (P ++ [q.id]) hm' (by rw [pinOneByOne_append]; exact hnext)
        rw [pinOneByOne_append] at hp
        exact ⟨p, denot_of_pruned (pruned_filterAllAgg _ [q.id]) (RCtx_of_readableAgg _ hRP).nodup p hp⟩
  obtain ⟨p, hp⟩ := main _ [] (Nat.le_refl _) hv
  exact ReaderAggRun.sat_of_denot_final φ hwf kv hkv p
    (denot_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup p hp)

/-- info: 'AbsSat.GraphPath.Model.Hereditary.sat_of_hpv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_hpv

end AbsSat.GraphPath.Model.Hereditary
