-- lean_project/AbsSat/GraphPath/Model/HereditaryRun.lean
import AbsSat.GraphPath.Model.HereditaryUp

/-!
# Hereditary pin validity along the whole run, and the Improves verdict

The induction over the construction, assembled:

* seed — `HereditaryBuild.hpv_initSeed`;
* weak filter, pins and aggressive review — `HereditaryBuild.hpv_filter`;
* UP — `HereditaryUp.hpv_addNode`;
* **join** — `hpv_join`, under **`JoinSplit`**: when the joined state is constrained, every global owner
  that stays comes from one of the two sides constrained the same way (no borrowing at the join).
  The side that has it keeps hereditary validity and sits inside the join, so it survives the new pin.

Then `hpv_sent` (one send), `lineHPV_advance` (one line), `lineHPV_run` (the whole run), and:

* **`sat_of_joinSplit`** — **if every join the machine performs splits its choices between its two
  sides, a valid final state of the Improves machine gives a model of `φ`.**

`JoinSplit` is the one open condition; the probe `helly joins` measures it on the joins the driver
actually performs (report v128).
-/

namespace AbsSat.GraphPath.Model.HereditaryRun

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
  LineInv_insertPure MInv_sent MInv_join MInv_initSeed)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF StateOkF_sent Fsac prunes_Fsac okJoin_of_stateOkF
  stateOkF_initSeed)
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchLines
open AbsSat.GraphPath.Model.BranchCompat
open AbsSat.GraphPath.Model.Hereditary
open AbsSat.GraphPath.Model.HereditaryBuild
open AbsSat.GraphPath.Model.HereditaryUp

variable (φ : Cnf)

/-- **No borrowing at a join**: under any constraints, a global owner of the constrained join is a global
owner of one constrained side, which is valid. -/
def JoinSplit (g₁ g₂ : GPathM) : Prop :=
  ∀ C : Cons, isValid (Fw (join g₁ g₂) C) = true → ∀ q ∈ (Fw (join g₁ g₂) C).gowners,
    (isValid (Fw g₁ C) = true ∧ q ∈ (Fw g₁ C).gowners) ∨ (isValid (Fw g₂ C) = true ∧ q ∈ (Fw g₂ C).gowners)

/-- A side of a join, constrained and valid, stays valid inside the join under the same constraints. -/
theorem valid_in_join (g J : GPathM) (hg : Grown g J) (mg : MInv φ g) (mJ : MInv φ J) (C : Cons)
    (hv : isValid (Fw g C) = true) : isValid (Fw J C) = true := by
  obtain ⟨hRB, hsB, hpB, hnB⟩ := Fw_facts g mg.rctx mg.smp mg.pms mg.sn C
  have a := AdjacentOwners.adj_of_readable _ hRB hv hpB hnB
  have hok := AggFixpoint.aggOk_reviewAgg _ hv
  have hpr : Pruned g (Fw g C) := Pruned.trans (ReaderAggRun.keeps_filterWeakAll g C).1 (pruned_filterAllAgg _ [])
  have hemb := embedded_of_grown (embedded_of_pruned_self hpr mg.rctx.nodup) hg
  have hc : WCompat C (Fw g C) := by
    intro e he p hp hs
    have hgw := gowner_of_mem _ a hp
    exact ((mem_filterWeakAll C g p).mp ((pruned_filterAllAgg (filterWeakAll g C) []).gowners_sub p hgw)).2 e he hs
  exact isValid_of_embedded (embedded_weak _ J C hemb a hok hsB hc mJ.smp mJ.rctx.shape.notroot) hv

/-- **A join keeps hereditary pin validity when it splits its choices.** -/
theorem hpv_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (m₁ : MInv φ g₁) (m₂ : MInv φ g₂)
    (h₁ : HPV g₁) (h₂ : HPV g₂) (hs : JoinSplit g₁ g₂) : HPV (join g₁ g₂) := by
  have mJ := MInv_join φ g₁ g₂ hok m₁ m₂
  intro C hv q hq
  rcases hs C hv q hq with ⟨hv₁, hq₁⟩ | ⟨hv₂, hq₂⟩
  · exact valid_in_join φ g₁ _ (grown_join_left g₁ g₂) m₁ mJ _ (h₁ C hv₁ q hq₁)
  · exact valid_in_join φ g₂ _ (grown_join_right g₁ g₂ hok) m₂ mJ _ (h₂ C hv₂ q hq₂)

/-- **One send keeps hereditary pin validity.** -/
theorem hpv_sent (hwf : WF φ) (k : Int) (kv : NodeId × GPathM) (hkv : StateOkF φ k kv) (hm : MInv φ kv.2)
    (hh : HPV kv.2) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hv : isValid (sent φ kv.2 d) = true) : HPV (sent φ kv.2 d) := by
  let ws := weakReqOfCnf φ d
  let reqs := reqOfCnf φ d
  have hvF : isValid (Filt kv.2 ws reqs) = true := by
    by_cases h : isValid (Filt kv.2 ws reqs) = true
    · exact h
    · exfalso
      have heq : sent φ kv.2 d = Filt kv.2 ws reqs := by
        simp only [sent, upFilteringWeak, GPathM.up]
        rw [if_neg h]
      rw [heq] at hv
      exact h hv
  have heq : sent φ kv.2 d = addNode (Filt kv.2 ws reqs) d "" := by
    simp only [sent, upFilteringWeak, GPathM.up]
    rw [if_pos hvF]
  have hmA : MInv φ (sent φ kv.2 d) := MInv_sent φ hwf k kv hkv hm d hd hv
  rw [heq] at hmA ⊢
  obtain ⟨_, hsF, hpF, hnF, rcF⟩ := filt_facts φ kv.2 hm ws reqs
  have hk : Keeps kv.2 (Filt kv.2 ws reqs) :=
    Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have hmok : MachineOk (Filt kv.2 ws reqs) := MachineOk_of_pruned hk.1 hm.mok
  have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hv
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hsok.onMap
  have hdF : d.step = (Filt kv.2 ws reqs).current_step := by rw [hk.1.step_eq, hkv.step, hdstep]
  exact hpv_addNode _ d hdF rcF hsF hpF hnF hmok hmA.rctx hmA.smp hmA.pms hmA.sn
    (hpv_filter φ kv.2 hm ws reqs hh)

/-- Every join the machine can perform splits its choices. -/
def JoinsSplit : Prop :=
  ∀ g₁ g₂ : GPathM, MInv φ g₁ → MInv φ g₂ → okJoin g₁ g₂ = true → HPV g₁ → HPV g₂ → JoinSplit g₁ g₂

theorem hpv_doJoin (hjs : JoinsSplit φ) (k : Int) (key : NodeId) (e g : GPathM) (hse : StateOkF φ k (key, e))
    (hsg : StateOkF φ k (key, g)) (me : MInv φ e) (mg : MInv φ g) (he : HPV e) (hg : HPV g) :
    HPV (doJoin e g) := by
  have hok := okJoin_of_stateOkF φ k key e g hse hsg
  simp only [doJoin, hok, if_pos]
  exact hpv_join φ e g hok me mg he hg (hjs e g me mg hok he hg)

/-- **One line keeps hereditary pin validity.** -/
theorem lineHPV_advance (hwf : WF φ) (hjs : JoinsSplit φ) (k : Int) (L : PureLine) (hl : LineInv φ k L)
    (hh : ∀ kv ∈ L, HPV kv.2) : ∀ kv ∈ pureAdvanceW φ L, HPV kv.2 := by
  have main := advance_inv φ (fun acc => LineInv φ (k + 1) acc ∧ ∀ kv ∈ acc, HPV kv.2) L ?_
    ⟨lineInv_nil φ (k + 1), fun kv h => absurd h List.not_mem_nil⟩
  · exact main.2
  intro kv hkv d hd acc ⟨ha, hr⟩
  refine ⟨LineInv_sendToW φ hwf k kv (hl.1.2 kv hkv) (hl.2 kv hkv) d hd acc ha, ?_⟩
  rintro ⟨d', B⟩ hB
  rw [sendToW_eq] at hB
  split at hB
  · next hv =>
    have hS := hpv_sent φ hwf k kv (hl.1.2 kv hkv) (hl.2 kv hkv) (hh kv hkv) d hd hv
    rcases insert_src acc d _ d' B hB with ⟨hdd, hB'⟩ | ⟨hB', _⟩
    · subst hdd
      rcases hB' with rfl | ⟨e, he, rfl⟩
      · exact hS
      · have hss := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv (hl.1.2 kv hkv) d' hd hv
        exact hpv_doJoin φ hjs (k + 1) d' e _ (ha.1.2 (d', e) he) hss (ha.2 (d', e) he)
          (MInv_sent φ hwf k kv (hl.1.2 kv hkv) (hl.2 kv hkv) d' hd hv) (hr (d', e) he) hS
    · exact hr (d', B) hB'
  · exact hr (d', B) hB

theorem lineHPV_init (hwf : WF φ) (hjs : JoinsSplit φ) : ∀ kv ∈ pureInit φ, HPV kv.2 := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineInv φ 0 acc → (∀ kv ∈ acc, HPV kv.2) →
        ∀ kv ∈ l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc, HPV kv.2 := by
    intro l
    induction l with
    | nil => intro _ acc _ h; exact h
    | cons x xs ih =>
      intro hx acc hl hh
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      refine ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (LineInv_insertPure φ 0 acc x _ hl (stateOkF_initSeed φ x hx0) (MInv_initSeed φ hwf x hx0)) ?_
      rintro ⟨d, B⟩ hB
      rcases insert_src acc x _ d B hB with ⟨hdd, hB'⟩ | ⟨hB', _⟩
      · subst hdd
        rcases hB' with rfl | ⟨e, he, rfl⟩
        · exact hpv_initSeed d
        · exact hpv_doJoin φ hjs 0 d e _ (hl.1.2 (d, e) he) (stateOkF_initSeed φ d hx0) (hl.2 (d, e) he)
            (MInv_initSeed φ hwf d hx0) (hh (d, e) he) (hpv_initSeed d)
      · exact hh (d, B) hB'
  exact main _ (fun _ h => h) [] (lineInv_nil φ 0) (fun kv h => absurd h List.not_mem_nil)

theorem lineHPV_steps (hwf : WF φ) (hjs : JoinsSplit φ) :
    ∀ (n : Nat) (k : Int) (L : PureLine), LineInv φ k L → (∀ kv ∈ L, HPV kv.2) →
      ∀ kv ∈ pureStepsW φ n L, HPV kv.2 := by
  intro n
  induction n with
  | zero => intro k L _ hh; exact hh
  | succ n ih =>
    intro k L hl hh
    exact ih (k + 1) _ (LineInv_pureAdvanceW φ hwf k L hl) (lineHPV_advance φ hwf hjs k L hl hh)

/-- **The Improves verdict from joins that split their choices.** -/
theorem sat_of_joinSplit (hwf : WF φ) (hjs : JoinsSplit φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_hpv φ hwf kv hkv hv
    (lineHPV_steps φ hwf hjs _ 0 _ (LineInv_init φ hwf) (lineHPV_init φ hwf hjs) kv hkv)

/-- info: 'AbsSat.GraphPath.Model.HereditaryRun.sat_of_joinSplit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_joinSplit

end AbsSat.GraphPath.Model.HereditaryRun
