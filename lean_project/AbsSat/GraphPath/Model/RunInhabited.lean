-- lean_project/AbsSat/GraphPath/Model/RunInhabited.lean
import AbsSat.GraphPath.Model.LiveSolution

/-!
# The verdict by construction: every state the run keeps holds a partial path

The author's reading of the send: the machine pins the destination's requirements, reviews, and keeps
the state only if it is valid; a valid send contains at least one partially built path. This module
runs the proof along the machine's own construction, with the weakest invariant the send needs.

* **`SoundAt L g`** — every entry `(x, q)` of `g` whose owner `q` sits at a step of `L` lies on a path.
  With `L` the literal steps (where every pin falls) and step `0`, a valid state satisfying it holds a
  path: its step-0 global owner owns itself.
* **`soundAt_initSeed`**, **`soundAt_join`**, **`soundAt_addNode`** (no hypothesis) — the seed, the union
  and the `up` keep it.
* **`FilterSoundAt`** — the one step left: pinning and reviewing keeps it.
* **`run_soundAt`**, **`sat_of_soundAt`** — the whole run keeps it, and the verdict follows.

`FilterSoundAt` asks for less than full exactness (`FilterSlices`, v140): only the entries towards the
literal steps, which is where the pins act.
-/

namespace AbsSat.GraphPath.Model.RunInhabited

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
  LineInv_steps)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF StateOkF_sent Fsac prunes_Fsac)
open AbsSat.GraphPath.Model.BranchLines (sent sendToW_eq insert_src advance_inv lineInv_nil)
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes tablesSound_initSeed)
open AbsSat.GraphPath.Model.PickInduction (gowner_of_isValid)

-- ============================================================
-- The invariant
-- ============================================================

/-- Every entry towards a step of `L` lies on a path. -/
def SoundAt (L : Int → Prop) (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → 0 ≤ x.id.step → x.id.step < g.current_step →
    ∀ q, 0 ≤ q.id.step → q.id.step < g.current_step → L q.id.step → q ∈ n.owners → Realizes g x q

theorem soundAt_of_tablesSound {L : Int → Prop} {g : GPathM} (h : TablesSound g) : SoundAt L g :=
  fun x n hx hx0 hx1 q hq0 hq1 _ hqn => h x n hx hx0 hx1 q hq0 hq1 hqn

theorem soundAt_initSeed (L : Int → Prop) (d : NodeId) (title : String) (hd : d.step = 0) :
    SoundAt L (initSeed d title) :=
  soundAt_of_tablesSound (tablesSound_initSeed d title hd)

/-- **A union keeps it**: an entry comes from one side, and its path is a path of the union. -/
theorem soundAt_join (L : Int → Prop) (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : SoundAt L g₁) (h₂ : SoundAt L g₂) : SoundAt L (join g₁ g₂) := by
  have hs1 : (join g₁ g₂).current_step = g₁.current_step := (grown_join_left g₁ g₂).step_eq
  have hs2 : (join g₁ g₂).current_step = g₂.current_step := (grown_join_right g₁ g₂ hok).step_eq
  intro x n hx hx0 hx1 q hq0 hq1 hL hqn
  rcases join_owners_source g₁ g₂ x n hx q hqn with ⟨m, hm, hqm⟩ | ⟨m, hm, hqm⟩
  · obtain ⟨sel, hcs, hxs, hqs⟩ := h₁ x m hm hx0 (by rw [← hs1]; exact hx1) q hq0
      (by rw [← hs1]; exact hq1) hL hqm
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hcs, hxs, hqs⟩
  · obtain ⟨sel, hcs, hxs, hqs⟩ := h₂ x m hm hx0 (by rw [← hs2]; exact hx1) q hq0
      (by rw [← hs2]; exact hq1) hL hqm
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hcs, hxs, hqs⟩

theorem extend_old' (g : GPathM) (d : NodeId) (sel : Int → PathNodeId) {y : PathNodeId}
    (hy : y.id.step < g.current_step) (hsel : sel y.id.step = y) :
    extend g d sel y.id.step = y := by
  show (if y.id.step = g.current_step then newPid g d else sel y.id.step) = y
  rw [if_neg (show ¬(y.id.step = g.current_step) from by omega)]
  exact hsel

/-- **An `up` keeps it.** Old entries keep their paths, extended by the new node; the new node's entries
towards old global owners are realized by the path through each owner; and every entry towards the new
node, by the path through the old node — found through the node's owner at step `0`. -/
theorem soundAt_addNode (L : Int → Prop) (hL0 : L 0) (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (hnd : NodupIds g) (hv : isValid g = true)
    (hself : ∀ y m, g.node? y = some m → y ∈ m.owners)
    (hownBelow : ∀ y m, g.node? y = some m → ∀ w ∈ m.owners, w.id.step < g.current_step)
    (hgn : GownersNodes.GN g)
    (hcov0 : ∀ y m, g.node? y = some m → ∃ w ∈ m.owners, w.id.step = 0)
    (h : SoundAt L g) : SoundAt L (addNode g d title) := by
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  have hnp : (newPid g d).id.step = g.current_step := by simp only [newPid]; exact hd
  have hnodeA := addNode_node?_new g d title hd hbelow
  have hlift : ∀ (y q : PathNodeId), y.id.step < g.current_step → q.id.step < g.current_step →
      Realizes g y q → Realizes (addNode g d title) y q := by
    intro y q hy hq ⟨sel, hcs, hys, hqs⟩
    exact ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs,
      extend_old' g d sel hy hys, extend_old' g d sel hq hqs⟩
  have htop : ∀ (sel : Int → PathNodeId), extend g d sel (newPid g d).id.step = newPid g d := by
    intro sel; rw [hnp]; exact extend_top g d sel
  -- a path through any node of `g`, found through its owner at step 0
  have through : ∀ y m, g.node? y = some m → 0 ≤ y.id.step → y.id.step < g.current_step →
      ∃ sel, ChainSound g sel ∧ sel y.id.step = y := by
    intro y m hy hy0 hy1
    obtain ⟨w, hw, hws⟩ := hcov0 y m hy
    obtain ⟨sel, hcs, hys, _⟩ := h y m hy hy0 hy1 w (by omega) (by omega) (by rw [hws]; exact hL0) hw
    exact ⟨sel, hcs, hys⟩
  intro x n hx hx0 hx1 q hq0 hq1 hL hqn
  rw [hcsA] at hx1 hq1
  by_cases hxnew : x = newPid g d
  · subst hxnew
    rw [hnodeA] at hx
    have hn' : n = addOwner (newPid g d) (upNode g d title) := (Option.some_inj.mp hx).symm
    have how : n.owners = g.gowners ++ [newPid g d] := by rw [hn']; rfl
    have hqn' : q ∈ g.gowners ++ [newPid g d] := by rw [← how]; exact hqn
    rcases List.mem_append.mp hqn' with hgow | hnew
    · obtain ⟨mq, hmq, hmqid⟩ := hgn q hgow
      have hqnode : g.node? q = some mq := by rw [← hmqid]; exact node?_of_mem hnd mq hmq
      have hqstep : q.id.step < g.current_step := by
        have := hbelow mq hmq; rw [hmqid] at this; exact this
      obtain ⟨sel, hcs, _, hqs⟩ := h q mq hqnode hq0 hqstep q hq0 hqstep hL (hself q mq hqnode)
      exact ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, htop sel,
        extend_old' g d sel hqstep hqs⟩
    · have hqeq : q = newPid g d := List.mem_singleton.mp hnew
      subst hqeq
      obtain ⟨t, htg, hts⟩ := gowner_of_isValid g hv 0 (Int.le_refl _) hpos
      obtain ⟨mt, hmt, hmtid⟩ := hgn t htg
      have htnode : g.node? t = some mt := by rw [← hmtid]; exact node?_of_mem hnd mt hmt
      obtain ⟨sel, hcs, _⟩ := through t mt htnode (by rw [hts]; exact Int.le_refl _) (by rw [hts]; exact hpos)
      exact ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs, htop sel, htop sel⟩
  · have hold : ∃ m, g.node? x = some m := by
      have hnB : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hx
      have hid : n.id = x := node?_id_eq _ x n hx
      rw [addNode_nodes] at hnB
      rcases List.mem_append.mp hnB with hl | hr
      · obtain ⟨n₀, hn₀, heq⟩ := List.mem_map.mp hl
        have hid₀ : n₀.id = x := by rw [← hid, ← heq, upMap_id]
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_mem g n₀ hn₀)
        rw [hid₀] at hm
        exact ⟨m, hm⟩
      · exfalso
        have hsing : n = addOwner (newPid g d) (upNode g d title) := List.eq_of_mem_singleton hr
        rw [hsing] at hid
        exact hxnew (by rw [← hid]; rfl)
    obtain ⟨m, hm⟩ := hold
    have hxstep : x.id.step < g.current_step := by
      have hid := node?_id_eq g x m hm
      have := hbelow m (List.mem_of_find?_eq_some hm)
      rw [hid] at this
      exact this
    rw [addNode_node?_old g d title x m hm] at hx
    have hn' : n = upMap g d m := (Option.some_inj.mp hx).symm
    have how : n.owners = m.owners ++ [newPid g d] := by rw [hn']; exact upMap_owners g d m
    have hqn' : q ∈ m.owners ++ [newPid g d] := by rw [← how]; exact hqn
    rcases List.mem_append.mp hqn' with hq | hnew
    · have hqstep : q.id.step < g.current_step := hownBelow x m hm q hq
      exact hlift x q hxstep hqstep (h x m hm hx0 hxstep q hq0 hqstep hL hq)
    · have hqeq : q = newPid g d := List.mem_singleton.mp hnew
      subst hqeq
      obtain ⟨sel, hcs, hxs⟩ := through x m hm hx0 hxstep
      exact ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hcs,
        extend_old' g d sel hxstep hxs, htop sel⟩

-- ============================================================
-- The run
-- ============================================================

variable (φ : Cnf)

/-- The literal steps, and step `0`: where the pins fall. -/
def LitStep (s : Int) : Prop := s < litBlock φ ∨ s = 0

/-- **The one step left**: pinning and reviewing a state of the run keeps every entry towards a literal
step on a path. -/
def FilterSoundAt : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 → SoundAt (LitStep φ) kv.2 →
    ∀ (ws : List (Int × List NodeId)) (rq : List NodeId), (∀ r ∈ rq, LitStep φ r.step) →
      isValid (filterAllAgg (filterWeakAll kv.2 ws) rq) = true →
      SoundAt (LitStep φ) (filterAllAgg (filterWeakAll kv.2 ws) rq)

/-- The requirements of a map node sit at literal steps. -/
theorem reqOfCnf_lit (hwf : WF φ) (d : NodeId) : ∀ r ∈ reqOfCnf φ d, r.step < litBlock φ := by
  intro r hr
  unfold reqOfCnf at hr
  split at hr
  · exact absurd hr List.not_mem_nil
  · split at hr
    · split at hr
      · exact absurd hr List.not_mem_nil
      · rw [List.mem_singleton.mp hr]; show d.step - 1 < litBlock φ; omega
    · split at hr
      · exact absurd hr List.not_mem_nil
      · split at hr
        · exact absurd hr List.not_mem_nil
        · split at hr
          · exact absurd hr List.not_mem_nil
          · next c hc =>
            have hcm : c ∈ φ.clauses := by
              unfold clauseAt at hc; exact List.mem_of_getElem? hc
            obtain ⟨⟨h1, h2, h3⟩, _⟩ := hwf c hcm
            have lt : ∀ l : Lit, l.v < φ.nVars → l.step < litBlock φ := by
              intro l hl; unfold Lit.step litBlock; split <;> omega
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact lt _ h1
            · exact lt _ h2
            · exact lt _ h3

/-- Every node of a valid reviewed reader's state owns something at step 0. -/
theorem cov0 (F : GPathM) (hR : ReadableAgg F) (hv : isValid F = true) (hpos : 0 < F.current_step) :
    ∀ y m, F.node? y = some m → ∃ w ∈ m.owners, w.id.step = 0 := by
  have ctx := Reader.Ctx_of_readable F (readable_of_readableAgg F hR) hv
  intro y m hy
  have hok := owners_ok_of_isValidNode _ m (ctx.nodeval y m hy)
  simp only [List.all_eq_true] at hok
  have hent := hok 0 (mem_intRange (Int.le_refl _) (by omega))
  obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp hent
  exact ⟨z, hz, eq_of_beq hzs⟩

/-- **A send keeps it**: the filter by hypothesis, the `up` by `soundAt_addNode`. -/
theorem soundAt_sent (hwf : WF φ) (hF : FilterSoundAt φ) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) (hm : MInv φ kv.2) (ht : SoundAt (LitStep φ) kv.2)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hval : isValid (sent φ kv.2 d) = true) :
    SoundAt (LitStep φ) (sent φ kv.2 d) := by
  have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hsok.onMap
  have hk0 : 0 ≤ k := SliceInvariant.nonneg_of_mapNodes φ k kv.1 hkv.onMap
  obtain ⟨F, hFdef⟩ : ∃ F, F = filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d) :=
    ⟨_, rfl⟩
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
    exact ⟨_, _, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  have rcF := RCtx_of_readableAgg F hRF
  have ctxF := Reader.Ctx_of_readable F (readable_of_readableAgg F hRF) hvF
  have hstepF : F.current_step = k + 1 := by rw [hkF.1.step_eq, hkv.step]
  have heq : sent φ kv.2 d = addNode F d "" := by rw [hsentF]; unfold GPathM.up; rw [hvF]; rfl
  have hFs : SoundAt (LitStep φ) F := by
    rw [hFdef]; rw [hFdef] at hvF
    exact hF k kv hkv hm ht _ _ (fun r hr => Or.inl (reqOfCnf_lit φ hwf d r hr)) hvF
  rw [heq]
  refine soundAt_addNode (LitStep φ) (Or.inr rfl) F d "" (by rw [hstepF, hdstep]) (by rw [hstepF]; omega)
    rcF.below ?_ rcF.nodup hvF (fun y m hy => ctxF.self y m hy) ?_ rcF.gn
    (cov0 F hRF hvF (by rw [hstepF]; omega)) hFs
  · have hmo := hm.mok
    unfold MachineOk at hmo ⊢
    rw [hkF.1.step_eq, hkF.1.map_parent_eq]
    exact hmo
  · intro y m hy w hw
    have hmem : m ∈ F.nodes := List.mem_of_find?_eq_some hy
    obtain ⟨n₀, hn₀, _, hown₀, _⟩ := hkF.1.nodes_derived m hmem
    obtain ⟨m', hm', hm'id⟩ := hm.own n₀ hn₀ w (hown₀ w hw)
    rw [hkF.1.step_eq, ← hm'id]
    exact hm.rctx.below m' hm'

def LineSoundAt (L : PureLine) : Prop := ∀ kv ∈ L, SoundAt (LitStep φ) kv.2

theorem lineSoundAt_insertPure (acc : PureLine) (key : NodeId) (g : GPathM)
    (hacc : LineSoundAt φ acc) (hg : SoundAt (LitStep φ) g) : LineSoundAt φ (insertPure acc key g) := by
  rintro ⟨d, B⟩ hB
  rcases insert_src acc key g d B hB with ⟨_, hB'⟩ | ⟨hB', _⟩
  · rcases hB' with rfl | ⟨e, he, rfl⟩
    · exact hg
    · unfold doJoin
      split
      · next hok => exact soundAt_join _ e g hok (hacc (key, e) he) hg
      · exact hacc (key, e) he
  · exact hacc (d, B) hB'

theorem lineSoundAt_advance (hwf : WF φ) (hF : FilterSoundAt φ) (k : Int) (L : PureLine)
    (hl : LineInv φ k L) (hs : LineSoundAt φ L) : LineSoundAt φ (pureAdvanceW φ L) := by
  have main := advance_inv φ (fun acc => LineInv φ (k + 1) acc ∧ LineSoundAt φ acc) L ?_
    ⟨lineInv_nil φ (k + 1), fun _ h => absurd h List.not_mem_nil⟩
  · exact main.2
  intro kv hkv d hd acc ⟨ha, hsl⟩
  refine ⟨LineInv_sendToW φ hwf k kv (hl.1.2 kv hkv) (hl.2 kv hkv) d hd acc ha, ?_⟩
  rw [sendToW_eq]
  split
  · next hv =>
    exact lineSoundAt_insertPure φ acc d _ hsl
      (soundAt_sent φ hwf hF k kv (hl.1.2 kv hkv) (hl.2 kv hkv) (hs kv hkv) d hd hv)
  · exact hsl

theorem lineSoundAt_init : LineSoundAt φ (pureInit φ) := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d.step = 0) → ∀ acc : PureLine, LineSoundAt φ acc →
      LineSoundAt φ (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (lineSoundAt_insertPure φ acc x _ h (soundAt_initSeed _ x "" (hx x List.mem_cons_self)))
  exact main _ (fun d hd => mapNodes_step φ 0 d hd) [] (fun _ h => absurd h List.not_mem_nil)

theorem lineSoundAt_steps (hwf : WF φ) (hF : FilterSoundAt φ) :
    ∀ (n : Nat) (k : Int) (L : PureLine), LineInv φ k L → LineSoundAt φ L →
      LineSoundAt φ (pureStepsW φ n L) := by
  intro n
  induction n with
  | zero => intro _ L _ hs; exact hs
  | succ n ih =>
    intro k L hl hs
    exact ih (k + 1) _ (LineInv_pureAdvanceW φ hwf k L hl) (lineSoundAt_advance φ hwf hF k L hl hs)

/-- **Every state the run keeps satisfies the invariant**, given the filter step. -/
theorem run_soundAt (hwf : WF φ) (hF : FilterSoundAt φ) : LineSoundAt φ (pureRunW φ) :=
  lineSoundAt_steps φ hwf hF _ 0 (pureInit φ) (LineInv_init φ hwf) (lineSoundAt_init φ)

/-- **The verdict by construction.** If pinning and reviewing keeps the entries towards the literal
steps on paths, a valid reader's state holds a path, and the path is a model. -/
theorem sat_of_soundAt (hwf : WF φ) (hF : FilterSoundAt φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hl := (LineInv_steps φ hwf (stepCount φ - 1).toNat 0 (pureInit φ) (LineInv_init φ hwf))
  have hcast : (0 : Int) + (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by
    have := ConservationCore.stepCount_pos φ; omega
  rw [hcast] at hl
  have hsk := hl.1.2 kv hkv
  have hts := hF _ kv hsk hm (run_soundAt φ hwf hF kv hkv) [] [] (fun _ h => absurd h List.not_mem_nil) hv
  have hfw : filterWeakAll kv.2 [] = kv.2 := rfl
  rw [hfw] at hts
  have hRG : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  have rcG := RCtx_of_readableAgg _ hRG
  have ctxG := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRG) hv
  have hpos := ConservationCore.stepCount_pos φ
  have hcsG : (filterAllAgg kv.2 []).current_step = stepCount φ := by
    rw [(pruned_filterAllAgg kv.2 []).step_eq, hstep]
  obtain ⟨q, hq, hq0⟩ := gowner_of_isValid _ hv 0 (Int.le_refl _) (by rw [hcsG]; omega)
  obtain ⟨m, hmm, hmid⟩ := rcG.gn q hq
  have hqm : (filterAllAgg kv.2 []).node? q = some m := by rw [← hmid]; exact node?_of_mem rcG.nodup m hmm
  obtain ⟨sel, hcs, _, _⟩ := hts q m hqm (by omega) (by rw [hcsG]; omega) q (by omega)
    (by rw [hcsG]; omega) (Or.inr hq0) (ctxG.self q m hqm)
  exact NoDeadEndVerdict.sat_of_denotS φ hwf kv hkv ⟨_, sel, hcs, rfl⟩

/-- info: 'AbsSat.GraphPath.Model.RunInhabited.sat_of_soundAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_soundAt

end AbsSat.GraphPath.Model.RunInhabited
