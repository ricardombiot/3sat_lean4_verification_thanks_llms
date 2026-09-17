-- lean_project/AbsSat/GraphPath/Model/HereditaryBuild.lean
import AbsSat.GraphPath.Model.Hereditary

/-!
# Building hereditary pin validity along the construction: seed and filters

`Hereditary.sat_of_hpv` reduces the Improves verdict to `HPV` on a final state. This module starts the
induction over the construction:

* `embedded_weak_pins` — the embedding through weak filters **and** pins, then the review.
* `filterWeakAll_append_noop` — a constraint every surviving global owner already meets changes nothing.
* **`hpv_initSeed`** — a seed has `HPV`: its only node is the only choice.
* `Fw_filter_inside` — the filtered state constrained by `C` sits inside the original constrained by
  `ws ++ reqs ++ C`, which is valid.
* `Fw_filter_valid` — and conversely for validity.
* **`hpv_filter`** — **the weak filter, the pins and the aggressive review keep `HPV`**: constraining the
  filtered state is, for validity and for the global owners that stay, constraining the original state
  by the filter's constraints followed by the new ones.

Left: UP (`addNode`) and joins.
-/

namespace AbsSat.GraphPath.Model.HereditaryBuild

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
open AbsSat.GraphPath.Model.Hereditary

/-- **The embedding through weak filters and pins, then the review.** -/
theorem embedded_weak_pins (B G : GPathM) (C : Cons) (reqs : List NodeId) (h : Embedded B G)
    (a : AdjacentOwners.Adj B) (hok : AggOk B) (hsmp : Sons.SMP B) (hc : WCompat C B)
    (hr : ∀ r ∈ reqs, ∀ p, Mem B p → p.id.step = r.step → p.id = r)
    (hsmpG : Sons.SMP G) (hnrG : Parents.NotRoot G) :
    Embedded B (filterAllAgg (filterWeakAll G C) reqs) := by
  obtain ⟨hfn, hfs, _⟩ := filterWeakAll_frame C G
  obtain ⟨hrn, hrs⟩ := foldl_filterRequire_frame reqs (filterWeakAll G C)
  have memB : ∀ p ∈ B.gowners, Mem B p := by
    intro p hp
    obtain ⟨m, hm, hmid⟩ := a.rc.gn p hp
    exact ⟨m, by rw [← hmid]; exact node?_of_mem a.rc.nodup m hm⟩
  have h1 : Embedded B (reqs.foldl filterRequire (filterWeakAll G C)) := by
    refine ⟨h.step.trans (hfs.symm.trans hrs.symm), fun p hp => ?_, fun p m hm => ?_⟩
    · refine mem_foldl_filterRequire_of reqs _ p ((mem_filterWeakAll C G p).mpr ⟨h.gow p hp,
        fun e he hs => hc e he p (memB p hp) hs⟩) (fun r hr' => ?_)
      by_cases hs : p.id.step = r.step
      · exact Or.inr (hr r hr' p (memB p hp) hs)
      · exact Or.inl hs
    · have hnode : (reqs.foldl filterRequire (filterWeakAll G C)).node? p = G.node? p := by
        simp only [GPathM.node?, hrn, hfn]
      rw [hnode]; exact h.node p m hm
  have sup := sup_of_embedded B _ a hok hsmp h1
  have hsF : Sons.SMP (reqs.foldl filterRequire (filterWeakAll G C)) := by
    unfold Sons.SMP; rw [hrn, hfn]; exact hsmpG
  have hnF : Parents.NotRoot (reqs.foldl filterRequire (filterWeakAll G C)) := by
    unfold Parents.NotRoot; rw [hrn, hfn]; exact hnrG
  have hA := AOk_filterAllAgg (reqs.foldl filterRequire (filterWeakAll G C)) ⟨sup, hsF, hnF⟩ []
    (fun r hr' => absurd hr' List.not_mem_nil)
  change AOk (filterAllAgg (filterWeakAll G C) reqs) _ _ at hA
  exact embedded_of_aok B _ a hsmp hA
    (h.step.trans (hfs.symm.trans (pruned_filterAllAgg (filterWeakAll G C) reqs).step_eq.symm))

/-- A constraint every surviving global owner already meets changes nothing. -/
theorem filterWeakAll_append_noop (g : GPathM) (C : Cons) (e : Int × List NodeId)
    (h : ∀ q ∈ (filterWeakAll g C).gowners, q.id.step = e.1 → q.id ∈ e.2) :
    filterWeakAll g (C ++ [e]) = filterWeakAll g C := by
  have happ : filterWeakAll g (C ++ [e]) = filterWeak (filterWeakAll g C) e := by
    simp [filterWeakAll, List.foldl_append]
  rw [happ]
  unfold filterWeak
  have hf : (filterWeakAll g C).gowners.filter (fun q => q.id.step != e.1 || e.2.contains q.id) =
      (filterWeakAll g C).gowners := by
    rw [List.filter_eq_self]
    intro q hq
    by_cases hs : q.id.step = e.1
    · simp [h q hq hs]
    · simp [hs]
  rw [hf]

/-- **A seed has hereditary pin validity.** -/
theorem hpv_initSeed (d : NodeId) : HPV (GPathM.initSeed d "") := by
  intro C hv q hq
  have hgw : ∀ x ∈ (filterWeakAll (GPathM.initSeed d "") C).gowners, x = { id := d, parent_id := none } := by
    intro x hx
    have hx' := ((mem_filterWeakAll C _ x).mp hx).1
    have hg : (GPathM.initSeed d "").gowners = [{ id := d, parent_id := none }] := by
      unfold GPathM.initSeed GPathM.up GPathM.addNode; simp [GPathM.empty, isValid, intRange]
    rw [hg] at hx'
    exact List.mem_singleton.mp hx'
  have hq' := hgw q ((pruned_filterAllAgg _ []).gowners_sub q hq)
  have hnoop := filterWeakAll_append_noop (GPathM.initSeed d "") C (pinC q.id) (fun x hx _ => by
    rw [hgw x hx, hq']; exact List.mem_singleton_self _)
  unfold Fw at hv ⊢
  rw [hnoop]
  exact hv

-- ============================================================
-- Filters
-- ============================================================

section
variable (φ : Cnf) (g : GPathM) (hm : ReaderAggRun.MInv φ g) (ws : Cons) (reqs : List NodeId)

/-- The state a send filters before its UP. -/
abbrev Filt : GPathM := filterAllAgg (filterWeakAll g ws) reqs

include hm in
theorem filt_facts : ReadableAgg (Filt g ws reqs) ∧ Sons.SMP (Filt g ws reqs) ∧ Sons.PMS (Filt g ws reqs) ∧
    Sons.SN (Filt g ws reqs) ∧ Reader.RCtx (Filt g ws reqs) := by
  have hwn := (filterWeakAll_frame ws g).1
  have hR : ReadableAgg (Filt g ws reqs) :=
    ⟨filterWeakAll g ws, reqs, ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  have hsW : Sons.SMP (filterWeakAll g ws) := by unfold Sons.SMP; rw [hwn]; exact hm.smp
  have hnW : Parents.NotRoot (filterWeakAll g ws) := by unfold Parents.NotRoot; rw [hwn]; exact hm.rctx.shape.notroot
  have hpW : Sons.PMS (filterWeakAll g ws) := by unfold Sons.PMS; rw [hwn]; exact hm.pms
  have hnS : Sons.SN (filterWeakAll g ws) := by unfold Sons.SN GownersNodes.HasNode; rw [hwn]; exact hm.sn
  exact ⟨hR, SMP_filterAllAgg _ hsW hnW reqs, AggInvariants.PMS_filterAllAgg _ reqs hpW,
    AggInvariants.SN_filterAllAgg _ reqs hnS, RCtx_of_readableAgg _ hR⟩

/-- A readable state constrained by `C` is again a readable state with its link invariants. -/
theorem Fw_facts (x : GPathM) (hR : Reader.RCtx x) (hs : Sons.SMP x) (hp : Sons.PMS x) (hn : Sons.SN x)
    (C : Cons) : ReadableAgg (Fw x C) ∧ Sons.SMP (Fw x C) ∧ Sons.PMS (Fw x C) ∧ Sons.SN (Fw x C) := by
  have hwn := (filterWeakAll_frame C x).1
  have hsW : Sons.SMP (filterWeakAll x C) := by unfold Sons.SMP; rw [hwn]; exact hs
  have hnW : Parents.NotRoot (filterWeakAll x C) := by unfold Parents.NotRoot; rw [hwn]; exact hR.shape.notroot
  have hpW : Sons.PMS (filterWeakAll x C) := by unfold Sons.PMS; rw [hwn]; exact hp
  have hnS : Sons.SN (filterWeakAll x C) := by unfold Sons.SN GownersNodes.HasNode; rw [hwn]; exact hn
  exact ⟨⟨filterWeakAll x C, [], ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hR, rfl⟩,
    SMP_filterAllAgg _ hsW hnW [], AggInvariants.PMS_filterAllAgg _ [] hpW, AggInvariants.SN_filterAllAgg _ [] hnS⟩

/-- The constraints of a send, as weak constraints. -/
def sendCons : Cons := ws ++ reqs.map pinC

include hm in
/-- **The filtered state constrained by `C` sits inside the original constrained by the send's
constraints and `C`, which is valid.** -/
theorem Fw_filter_inside (C : Cons) (hv : isValid (Fw (Filt g ws reqs) C) = true) :
    Embedded (Fw (Filt g ws reqs) C) (Fw g (sendCons ws reqs ++ C)) ∧
      isValid (Fw g (sendCons ws reqs ++ C)) = true := by
  obtain ⟨_, hsF, hpF, hnF, rcF⟩ := filt_facts φ g hm ws reqs
  obtain ⟨hRB, hsB, hpB, hnB⟩ := Fw_facts (Filt g ws reqs) rcF hsF hpF hnF C
  have a := AdjacentOwners.adj_of_readable _ hRB hv hpB hnB
  have hok : AggOk (Fw (Filt g ws reqs) C) := aggOk_reviewAgg _ hv
  have hpr : Pruned g (Fw (Filt g ws reqs) C) :=
    Pruned.trans (ReaderAggRun.keeps_filterWeakAll g ws).1 (Pruned.trans (pruned_filterAllAgg _ reqs)
      (Pruned.trans (ReaderAggRun.keeps_filterWeakAll _ C).1 (pruned_filterAllAgg _ [])))
  have hc : WCompat (sendCons ws reqs ++ C) (Fw (Filt g ws reqs) C) := by
    intro e he p hp hs
    have hg := gowner_of_mem _ a hp
    have hgC := (pruned_filterAllAgg (filterWeakAll (Filt g ws reqs) C) []).gowners_sub p hg
    have hCm := (mem_filterWeakAll C _ p).mp hgC
    have hgF := hCm.1
    have hgR : p ∈ (reqs.foldl filterRequire (filterWeakAll g ws)).gowners :=
      (pruned_reviewAgg _).gowners_sub p hgF
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · have hgW := (LocalContradiction.mem_foldl_filterRequire reqs _ p hgR).1
        exact ((mem_filterWeakAll ws g p).mp hgW).2 e he hs
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
        rcases (LocalContradiction.mem_foldl_filterRequire reqs _ p hgR).2 r hr with h | h
        · exact absurd hs h
        · rw [h]; exact List.mem_singleton_self r
    · exact hCm.2 e he hs
  have hemb := embedded_weak _ g _ (embedded_of_pruned_self hpr hm.rctx.nodup) a hok hsB hc hm.smp
    hm.rctx.shape.notroot
  exact ⟨hemb, isValid_of_embedded hemb hv⟩

include hm in
/-- **If the original constrained by the send's constraints and `C` is valid, so is the filtered state
constrained by `C`.** -/
theorem Fw_filter_valid (C : Cons)
    (hv : isValid (Fw g (sendCons ws reqs ++ C)) = true) : isValid (Fw (Filt g ws reqs) C) = true := by
  obtain ⟨_, hsF, _, _, rcF⟩ := filt_facts φ g hm ws reqs
  obtain ⟨hRB, hsB, hpB, hnB⟩ := Fw_facts g hm.rctx hm.smp hm.pms hm.sn (sendCons ws reqs ++ C)
  have a := AdjacentOwners.adj_of_readable _ hRB hv hpB hnB
  have hok : AggOk (Fw g (sendCons ws reqs ++ C)) := aggOk_reviewAgg _ hv
  have hpr : Pruned g (Fw g (sendCons ws reqs ++ C)) :=
    Pruned.trans (ReaderAggRun.keeps_filterWeakAll g _).1 (pruned_filterAllAgg _ [])
  have memG : ∀ p, Mem (Fw g (sendCons ws reqs ++ C)) p →
      ∀ e ∈ sendCons ws reqs ++ C, p.id.step = e.1 → p.id ∈ e.2 := by
    intro p hp e he hs
    have hg := gowner_of_mem _ a hp
    have hgW := (pruned_filterAllAgg (filterWeakAll g (sendCons ws reqs ++ C)) []).gowners_sub p hg
    exact ((mem_filterWeakAll _ g p).mp hgW).2 e he hs
  have hin := embedded_weak_pins _ g ws reqs (embedded_of_pruned_self hpr hm.rctx.nodup) a hok hsB
    (fun e he p hp hs => memG p hp e (List.mem_append_left _ (List.mem_append_left _ he)) hs)
    (fun r hr p hp hs => List.mem_singleton.mp (memG p hp (pinC r)
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))) hs))
    hm.smp hm.rctx.shape.notroot
  have hin2 := embedded_weak _ (Filt g ws reqs) C hin a hok hsB
    (fun e he p hp hs => memG p hp e (List.mem_append_right _ he) hs) hsF rcF.shape.notroot
  exact isValid_of_embedded hin2 hv

include hm in
/-- **The weak filter, the pins and the aggressive review keep hereditary pin validity.** -/
theorem hpv_filter (hh : HPV g) : HPV (Filt g ws reqs) := by
  intro C hv q hq
  obtain ⟨hemb, hvg⟩ := Fw_filter_inside φ g hm ws reqs C hv
  have hq' := hemb.gow q hq
  have h1 := hh (sendCons ws reqs ++ C) hvg q hq'
  rw [List.append_assoc] at h1
  exact Fw_filter_valid φ g hm ws reqs (C ++ [pinC q.id]) h1
end

/-- info: 'AbsSat.GraphPath.Model.HereditaryBuild.hpv_filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hpv_filter

end AbsSat.GraphPath.Model.HereditaryBuild
