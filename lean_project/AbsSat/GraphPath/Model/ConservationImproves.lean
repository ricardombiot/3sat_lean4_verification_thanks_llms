-- lean_project/AbsSat/GraphPath/Model/ConservationImproves.lean
import AbsSat.GraphPath.Model.PureDriverImproves

/-!
# Conservation for the improved machine: the weak filter never loses a solution

`Conservation` proves that `SatMachinePure` keeps every solution: along a
satisfying assignment's branch, the selection the assignment names stays a
sound chain of every state, and a chain inside the global owners makes the state
valid. `PureDriver` turns that into `pureRun_ne_nil`.

This module does the same for `PureDriverImproves`. The only new ingredient is
the weak filter, and it costs one lemma:

* `ChainSound_filterWeak` — `filterWeak` rewrites `gowners` only, so a sound
  chain survives it as soon as the chain's node at the entry's step is one of
  the entry's nodes;
* `weakReqOfCnf_sound` (in `CnfMapImproves`) — for a satisfying assignment it
  always is.

After the weak filter the state is a `Pruned` narrowing of the original, and
everything else is `Conservation`'s argument verbatim, run on the narrowed state.

## What changes in the bookkeeping

`AlongAssign` and `StateOk` carry `MapReachable`, whose `up` constructor is the
hard-requirement step: a weakly filtered state is not `MapReachable`. The only
things the conservation argument reads from reachability are that nodes lie
below the current step and `MachineOk`; both survive any pruning, `addNode`
and `join`. So here they are packaged as `ShapeOk`, and `AlongAssignW` /
`StateOkW` carry that instead.

## Result

`pureRunW_ne_nil`: for a well-formed satisfiable formula the improved run ends
with a non-empty line, and `pureRunW_full_state` gives the valid, inhabited
state parked at the assignment's final node. Unlike `PureDriver`, no
`0 < stepCount φ` hypothesis is needed: it always holds.
-/

namespace AbsSat.GraphPath.Model.ConservationImproves

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf weakReqOfCnf_sound)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit mem_insertPure
  mem_insertPure_of_ne key_inj isValid_of_grown insertPure_keys_some insertPure_keys_none
  isValid_initSeed)
open AbsSat.GraphPath.Model.PureDriverImproves

-- ============================================================
-- The weak filter is a pruning
-- ============================================================

theorem pruned_filterWeak (g : GPathM) (e : Int × List NodeId) : Pruned g (filterWeak g e) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n hn := ⟨n, hn, rfl, fun _ hq => hq, fun _ hp => hp⟩

theorem pruned_filterWeakAll (g : GPathM) (ws : List (Int × List NodeId)) :
    Pruned g (filterWeakAll g ws) :=
  pruned_foldl _ pruned_filterWeak ws g

-- ============================================================
-- A sound chain through the weak sets survives the weak filter
-- ============================================================

theorem ChainSound_filterWeak (g : GPathM) (e : Int × List NodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (he : ∀ k, 0 ≤ k → k < g.current_step → k = e.1 → (sel k).id ∈ e.2) :
    ChainSound (filterWeak g e) sel := by
  obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
  refine ⟨⟨hchain, howned, ?_⟩, hself, hson, hroot⟩
  intro k hlo hhi
  simp only [filterWeak, List.mem_filter]
  refine ⟨hgow k hlo hhi, ?_⟩
  have hstepk := (hchain.1 k hlo hhi).2
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem]
  by_cases hk : k = e.1
  · exact Or.inr (he k hlo hhi hk)
  · exact Or.inl (by rw [hstepk]; exact hk)

theorem ChainSound_filterWeakAll (ws : List (Int × List NodeId)) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      (∀ e ∈ ws, ∀ k, 0 ≤ k → k < g.current_step → k = e.1 → (sel k).id ∈ e.2) →
      ChainSound (filterWeakAll g ws) sel := by
  induction ws with
  | nil => intro g sel h _; exact h
  | cons e rest ih =>
    intro g sel h hws
    exact ih (filterWeak g e) sel (ChainSound_filterWeak g e sel h (hws e List.mem_cons_self))
      (fun e' he' => hws e' (List.mem_cons_of_mem _ he'))

-- ============================================================
-- The shape facts the conservation argument reads
-- ============================================================

/-- Nodes below the current step, and `MachineOk`: all `ChainSound_upFiltering`
asks of the state besides the chain. -/
def ShapeOk (g : GPathM) : Prop :=
  (∀ n ∈ g.nodes, n.id.id.step < g.current_step) ∧ MachineOk g

theorem ShapeOk_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : ShapeOk g) : ShapeOk g' :=
  ⟨Certifies.nodes_below_of_pruned hpr h.1, MachineOk_of_pruned hpr h.2⟩

theorem ShapeOk_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    ShapeOk (GPathM.initSeed d title) := by
  refine ⟨?_, Certifies.MachineOk_initSeed d title⟩
  intro n hn
  rw [initSeed_nodes] at hn
  rcases List.mem_singleton.mp hn with rfl
  rw [initSeed_current]
  show d.step < 1
  omega

theorem ShapeOk_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (h : ShapeOk g) : ShapeOk (addNode g d title) := by
  refine ⟨?_, MachineOk_addNode g d title h.2⟩
  intro n hn
  rw [addNode_current]
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with hmem | hmem
  · obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hmem
    have hid : n.id = m.id := by rw [← hEq]; exact upMap_id g d m
    rw [hid]
    have := h.1 m hm
    omega
  · rcases List.mem_singleton.mp hmem with rfl
    have hid : (addOwner (newPid g d) (upNode g d title)).id.id = d := rfl
    rw [hid]
    omega

theorem ShapeOk_upFilteringWeak (g : GPathM) (ws : List (Int × List NodeId))
    (reqs : List NodeId) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (h : ShapeOk g) :
    ShapeOk (upFilteringWeak g ws reqs d title) := by
  have hpr : Pruned g (filterAll (filterWeakAll g ws) reqs) :=
    Pruned.trans (pruned_filterWeakAll g ws) (pruned_filterAll _ reqs)
  have hf := ShapeOk_of_pruned hpr h
  simp only [upFilteringWeak, GPathM.up]
  split
  · exact ShapeOk_addNode _ d title (by rw [hpr.step_eq]; exact hd) hf
  · exact hf

theorem ShapeOk_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : ShapeOk g₁) (h₂ : ShapeOk g₂) : ShapeOk (join g₁ g₂) := by
  refine ⟨?_, Certifies.MachineOk_join g₁ g₂ h₁.2⟩
  have hcs₂ : g₂.current_step = g₁.current_step := (grown_join_right g₁ g₂ hok).step_eq.symm
  intro n hn
  show n.id.id.step < g₁.current_step
  rw [GownersNodes.join_nodes] at hn
  rcases List.mem_append.mp hn with hmem | hmem
  · obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hmem
    have hid : n.id = m.id := by
      rw [← hEq]
      cases g₂.node? m.id with
      | some q => rfl
      | none => rfl
    rw [hid]
    exact h₁.1 m hm
  · have := h₂.1 n (List.mem_filter.mp hmem).1
    omega

-- ============================================================
-- The branch of an assignment, through the improved machine
-- ============================================================

variable (φ : Cnf) (a : Assign)

/-- `Conservation.AlongAssign` with the improved `up`, and `ShapeOk` in place of
`MapReachable` for the branch a join brings in. -/
inductive AlongAssignW : GPathM → Prop where
  | seed (title : String) :
      AlongAssignW (GPathM.initSeed (selOfAssign φ a 0) title)
  | up (g : GPathM) (title : String) :
      AlongAssignW g →
      AlongAssignW (upFilteringWeak g
        (weakReqOfCnf φ (selOfAssign φ a g.current_step))
        (reqOfCnf φ (selOfAssign φ a g.current_step))
        (selOfAssign φ a g.current_step) title)
  | joinL (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₂ : ShapeOk g₂) :
      AlongAssignW g₁ → AlongAssignW (GPathM.join g₁ g₂)
  | joinR (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₁ : ShapeOk g₁) :
      AlongAssignW g₂ → AlongAssignW (GPathM.join g₁ g₂)

theorem shapeOk_of_alongW (g : GPathM) (h : AlongAssignW φ a g) : ShapeOk g := by
  induction h with
  | seed title => exact ShapeOk_initSeed _ title (selOfAssign_step φ a 0)
  | up g title _ ih =>
    exact ShapeOk_upFilteringWeak g _ _ _ title (selOfAssign_step φ a g.current_step) ih
  | joinL g₁ g₂ hok h₂ _ ih => exact ShapeOk_join g₁ g₂ hok ih h₂
  | joinR g₁ g₂ hok h₁ _ ih => exact ShapeOk_join g₁ g₂ hok h₁ ih

/-- **`Conservation`'s `up` step, on any pruning of the state.** If `gw` narrows
`g` and still carries the assignment's chain, the hard filter, the review and
`addNode` keep it, extended by the assignment's next node. -/
theorem chainSound_up_of_pruned (hwf : WF φ) (g gw : GPathM) (hpr : Pruned g gw)
    (hshape : ShapeOk g) (sel : Int → PathNodeId) (hselw : ChainSound gw sel)
    (hids : ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k)
    (title : String) :
    ∃ sel', ChainSound (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
          (selOfAssign φ a g.current_step) title) sel'
      ∧ (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
          (selOfAssign φ a g.current_step) title).current_step = g.current_step + 1
      ∧ ∀ k, 0 ≤ k → k < g.current_step + 1 → (sel' k).id = selOfAssign φ a k := by
  have hgs : gw.current_step = g.current_step := hpr.step_eq
  have hreqs : ∀ req ∈ reqOfCnf φ (selOfAssign φ a g.current_step),
      0 ≤ req.step → req.step < gw.current_step → (sel req.step).id = req := by
    intro req hreq hr0 hr1
    rw [hids req.step hr0 (by omega)]
    exact reqSat_selOfAssign φ hwf a g.current_step req hreq
  have hpf := pruned_filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))
  have hfil : ChainSound (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) sel :=
    ChainSound_filterAll gw _ sel hselw hreqs
  have hvalid : isValid (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) = true :=
    PickInduction.isValid_of_ChainG _ sel hfil.chain
  have hshf : ShapeOk (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) :=
    ShapeOk_of_pruned (Pruned.trans hpr hpf) hshape
  have hd : (selOfAssign φ a g.current_step).step
      = (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))).current_step := by
    rw [hpf.step_eq, hgs, selOfAssign_step]
  have hshapeEq : upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title
      = addNode (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) title := by
    simp only [upFiltering, GPathM.up, hvalid, if_pos]
  have hcur : (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title).current_step = g.current_step + 1 := by
    rw [hshapeEq, addNode_current, hpf.step_eq, hgs]
  refine ⟨extend (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
    (selOfAssign φ a g.current_step) sel, ?_, hcur, ?_⟩
  · exact ChainSound_upFiltering gw _ _ title hvalid hd hshf.1 hshf.2 sel hselw hreqs
  · intro k hk0 hk
    if he : k = g.current_step then
      have hextend : extend (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
          (selOfAssign φ a g.current_step) sel g.current_step
          = newPid (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
            (selOfAssign φ a g.current_step) := by
        simp only [extend, if_pos (hpf.step_eq.trans hgs).symm]
      rw [he, hextend]
      rfl
    else
      rw [extend_below (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) sel k (by rw [hpf.step_eq, hgs]; omega)]
      exact hids k hk0 (by omega)

/-- **The conservation law for the improved machine.** Along a satisfying
assignment's branch, the selection that assignment names is a sound chain of
every state, and its map ids are the assignment's own choices. -/
theorem chainSound_alongW (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignW φ a g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k := by
  induction h with
  | seed title =>
    refine ⟨fun _ => { id := selOfAssign φ a 0, parent_id := none }, ?_, ?_⟩
    · exact ChainSound_initSeed _ title (selOfAssign_step φ a 0)
    · intro k hlo hhi
      rw [initSeed_current] at hhi
      have : k = 0 := by omega
      subst this
      rfl
  | up g title hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    -- the weak filter keeps the chain: this is the whole new content
    have hweak : ∀ e ∈ weakReqOfCnf φ (selOfAssign φ a g.current_step),
        ∀ k, 0 ≤ k → k < g.current_step → k = e.1 → (sel k).id ∈ e.2 := by
      intro e he k hk0 hk hke
      rw [hids k hk0 hk, hke]
      exact weakReqOfCnf_sound φ a hsat g.current_step e he
    obtain ⟨sel', hs', hcur, hids'⟩ :=
      chainSound_up_of_pruned φ a hwf g _ (pruned_filterWeakAll g _)
        (shapeOk_of_alongW φ a g hal) sel (ChainSound_filterWeakAll _ g sel hsel hweak) hids title
    exact ⟨sel', hs', fun k hk0 hk => hids' k hk0 (lt_of_lt_of_eq hk hcur)⟩
  | joinL g₁ g₂ hok h₂ hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_left g₁ g₂).step_eq] at hk; exact hk)⟩
  | joinR g₁ g₂ hok h₁ hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_right g₁ g₂ hok).step_eq] at hk; exact hk)⟩

theorem isValid_alongW (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignW φ a g) :
    isValid g = true := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongW φ a hwf hsat g h
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

theorem inhabited_alongW (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignW φ a g) :
    AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongW φ a hwf hsat g h
  exact ⟨pathOf sel g, sel, hsel.chain.1, hsel.chain.2.1, rfl⟩

-- ============================================================
-- The driver: the line invariant
-- ============================================================

structure StateOkW (φ : Cnf) (k : Int) (kv : NodeId × GPathM) : Prop where
  onMap : kv.1 ∈ mapNodes φ k
  shape : ShapeOk kv.2
  step  : kv.2.current_step = k + 1
  par   : kv.2.map_parent = some kv.1
  valid : isValid kv.2 = true

def LineOkW (φ : Cnf) (k : Int) (line : PureLine) : Prop :=
  (line.map (·.1)).Nodup ∧ ∀ kv ∈ line, StateOkW φ k kv

theorem okJoin_of_stateOkW (k : Int) (key : NodeId) (e g : GPathM)
    (he : StateOkW φ k (key, e)) (hg : StateOkW φ k (key, g)) : okJoin e g = true := by
  simp only [okJoin, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨he.step.trans hg.step.symm, he.par.trans hg.par.symm⟩, he.valid⟩, hg.valid⟩

theorem stateOkW_doJoin (k : Int) (key : NodeId) (e g : GPathM)
    (he : StateOkW φ k (key, e)) (hg : StateOkW φ k (key, g)) :
    StateOkW φ k (key, doJoin e g) := by
  have hok := okJoin_of_stateOkW φ k key e g he hg
  simp only [doJoin, hok, if_pos]
  exact ⟨he.onMap, ShapeOk_join e g hok he.shape hg.shape, he.step, he.par,
    isValid_of_grown (grown_join_left e g) he.valid⟩

theorem LineOkW_insertPure (k : Int) (line : PureLine) (key : NodeId) (g : GPathM)
    (hl : LineOkW φ k line) (hg : StateOkW φ k (key, g)) :
    LineOkW φ k (insertPure line key g) := by
  obtain ⟨hnd, hall⟩ := hl
  cases hf : line.find? (fun x => x.1 == key) with
  | none =>
    have hnotin : ∀ (b : NodeId) (x : GPathM), (b, x) ∈ line → ¬ b = key := by
      intro b x hbx hbk
      have h := List.find?_eq_none.mp hf (b, x) hbx
      exact h (by simp only [hbk]; exact beq_iff_eq.mpr rfl)
    constructor
    · rw [insertPure_keys_none line key g hf]
      rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      simpa using hnotin
    · intro kv hkv
      simp only [insertPure, hf] at hkv
      rcases List.mem_append.mp hkv with h | h
      · exact hall kv h
      · rcases List.mem_singleton.mp h with rfl
        exact hg
  | some e =>
    have hekey : e.1 = key :=
      eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
    have hemem : e ∈ line := List.mem_of_find?_eq_some hf
    have hesok : StateOkW φ k (key, e.2) := by
      have h := hall e hemem
      rwa [← hekey]
    constructor
    · rw [insertPure_keys_some line key g e hf]; exact hnd
    · intro kv hkv
      simp only [insertPure, hf] at hkv
      obtain ⟨x, hx, hEq⟩ := List.mem_map.mp hkv
      cases hb : x.1 == key with
      | true =>
        have : kv = (key, doJoin e.2 g) := by rw [← hEq]; simp only [hb]; rfl
        rw [this]
        exact stateOkW_doJoin φ k key e.2 g hesok hg
      | false =>
        have : kv = x := by rw [← hEq]; simp only [hb]; rfl
        rw [this]
        exact hall x hx

-- ============================================================
-- The branch's entry
-- ============================================================

def CarriesW (k : Int) (line : PureLine) : Prop :=
  ∃ g, (selOfAssign φ a k, g) ∈ line ∧ AlongAssignW φ a g ∧ g.current_step = k + 1

theorem CarriesW_insertPure (k : Int) (line : PureLine)
    (key : NodeId) (g' : GPathM) (hl : LineOkW φ k line) (hg' : StateOkW φ k (key, g'))
    (hc : CarriesW φ a k line) : CarriesW φ a k (insertPure line key g') := by
  obtain ⟨g, hmem, hal, hcs⟩ := hc
  obtain ⟨hnd, hall⟩ := hl
  by_cases hkey : selOfAssign φ a k = key
  · subst hkey
    cases hf : line.find? (fun x => x.1 == selOfAssign φ a k) with
    | none =>
      exact absurd (List.find?_eq_none.mp hf _ hmem) (by simp)
    | some e =>
      have hemem : e ∈ line := List.mem_of_find?_eq_some hf
      have hekey : e.1 = selOfAssign φ a k :=
        eq_of_beq (List.find?_some
          (p := fun x : NodeId × GPathM => x.1 == selOfAssign φ a k) hf)
      have hee : e = (selOfAssign φ a k, g) :=
        key_inj line hnd e hemem (selOfAssign φ a k, g) hmem hekey
      have hesok : StateOkW φ k (selOfAssign φ a k, g) := by
        have h := hall e hemem
        rw [hee] at h
        exact h
      have hok : okJoin g g' = true :=
        okJoin_of_stateOkW φ k (selOfAssign φ a k) g g' hesok hg'
      refine ⟨join g g', ?_, AlongAssignW.joinL g g' hok hg'.shape hal, hcs⟩
      simp only [insertPure, hf, hee, doJoin, hok, if_pos]
      refine List.mem_map.mpr ⟨(selOfAssign φ a k, g), hmem, ?_⟩
      simp
  · exact ⟨g, mem_insertPure_of_ne line key _ g' g hkey hmem, hal, hcs⟩

theorem CarriesW_of_insertPure_at (k : Int) (line : PureLine)
    (g' : GPathM) (hl : LineOkW φ k line) (hg' : StateOkW φ k (selOfAssign φ a k, g'))
    (hal : AlongAssignW φ a g') :
    CarriesW φ a k (insertPure line (selOfAssign φ a k) g') := by
  obtain ⟨h, hmem, hcase⟩ := mem_insertPure line (selOfAssign φ a k) g'
  refine ⟨h, hmem, ?_, ?_⟩
  · rcases hcase with rfl | ⟨e, hem, rfl⟩
    · exact hal
    · have he : StateOkW φ k (selOfAssign φ a k, e) := hl.2 _ hem
      have hok := okJoin_of_stateOkW φ k _ e g' he hg'
      simp only [doJoin, hok, if_pos]
      exact AlongAssignW.joinR e g' hok he.shape hal
  · rcases hcase with rfl | ⟨e, hem, rfl⟩
    · exact hg'.step
    · have he : StateOkW φ k (selOfAssign φ a k, e) := hl.2 _ hem
      have hok := okJoin_of_stateOkW φ k _ e g' he hg'
      simp only [doJoin, hok, if_pos]
      rw [(grown_join_left e g').step_eq]
      exact he.step

-- ============================================================
-- One send
-- ============================================================

theorem isValid_filter_of_sentW (g : GPathM) (d : NodeId)
    (hval : isValid (upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    isValid (filterAll (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) = true := by
  by_cases h : isValid (filterAll (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)) = true
  · exact h
  · exfalso
    have he : upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
        = filterAll (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d) := by
      simp only [upFilteringWeak, GPathM.up, if_neg h]
    rw [he] at hval
    exact h hval

theorem StateOkW_sent (k : Int) (kv : NodeId × GPathM) (hkv : StateOkW φ k kv)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    StateOkW φ (k + 1) (d, upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") := by
  have hkey : kv.1.step = k := mapNodes_step φ k kv.1 hkv.onMap
  have hmk : (⟨k, kv.1.index⟩ : NodeId) ∈ mapNodes φ k := by
    have : (⟨k, kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix =>
        rw [hkv1] at hkey
        simp only at hkey ⊢
        rw [hkey]
    rw [this]; exact hkv.onMap
  have hd' : d ∈ mapNodes φ (k + 1) :=
    mapSons_subset φ k kv.1.index hmk d (by rw [← hkey]; exact hd)
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hd'
  have hfv := isValid_filter_of_sentW φ kv.2 d hval
  have hpr : Pruned kv.2 (filterAll (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) :=
    Pruned.trans (pruned_filterWeakAll _ _) (pruned_filterAll _ _)
  have hshape : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d ""
      = addNode (filterAll (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)) d "" := by
    simp only [upFilteringWeak, GPathM.up, hfv, if_pos]
  refine ⟨hd', ?_, ?_, ?_, hval⟩
  · exact ShapeOk_upFilteringWeak kv.2 _ _ d "" (by rw [hdstep, hkv.step]) hkv.shape
  · rw [hshape, addNode_current, hpr.step_eq, hkv.step]
  · rw [hshape]; rfl

theorem LineOkW_sendToW (k : Int) (kv : NodeId × GPathM) (hkv : StateOkW φ k kv)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (next : PureLine)
    (hn : LineOkW φ (k + 1) next) : LineOkW φ (k + 1) (sendToW φ kv.2 next d) := by
  simp only [sendToW]
  split
  · next hval => exact LineOkW_insertPure φ (k + 1) next d _ hn (StateOkW_sent φ k kv hkv d hd hval)
  · exact hn

theorem LineOkW_sendAllW (k : Int) (kv : NodeId × GPathM) (hkv : StateOkW φ k kv)
    (next : PureLine) (hn : LineOkW φ (k + 1) next) :
    LineOkW φ (k + 1) (sendAllW φ kv next) := by
  simp only [sendAllW]
  have : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, LineOkW φ (k + 1) acc → LineOkW φ (k + 1) (l.foldl (sendToW φ kv.2) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (LineOkW_sendToW φ k kv hkv x (hx x List.mem_cons_self) acc h)
  exact this _ (fun _ hd => hd) next hn

theorem LineOkW_pureAdvanceW (k : Int) (line : PureLine) (hl : LineOkW φ k line) :
    LineOkW φ (k + 1) (pureAdvanceW φ line) := by
  simp only [pureAdvanceW]
  obtain ⟨_, hall⟩ := hl
  have : ∀ (l : PureLine), (∀ kv ∈ l, StateOkW φ k kv) →
      ∀ acc, LineOkW φ (k + 1) acc →
        LineOkW φ (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (LineOkW_sendAllW φ k x (hx x List.mem_cons_self) acc h)
  exact this line hall [] ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

-- ============================================================
-- The branch through the two folds
-- ============================================================

theorem advance_targetW (hwf : WF φ) (hsat : Sat a φ)
    (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssignW φ a g) (hcs : g.current_step = k + 1) :
    selOfAssign φ a (k + 1)
        ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index
      ∧ AlongAssignW φ a (upFilteringWeak g (weakReqOfCnf φ (selOfAssign φ a (k + 1)))
          (reqOfCnf φ (selOfAssign φ a (k + 1))) (selOfAssign φ a (k + 1)) "")
      ∧ isValid (upFilteringWeak g (weakReqOfCnf φ (selOfAssign φ a (k + 1)))
          (reqOfCnf φ (selOfAssign φ a (k + 1))) (selOfAssign φ a (k + 1)) "") = true := by
  have hson : selOfAssign φ a (k + 1)
      ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index := by
    rw [selOfAssign_step]
    exact selOfAssign_son φ a hsat k h0 hk
  have hup : AlongAssignW φ a (upFilteringWeak g (weakReqOfCnf φ (selOfAssign φ a (k + 1)))
      (reqOfCnf φ (selOfAssign φ a (k + 1))) (selOfAssign φ a (k + 1)) "") := by
    have := AlongAssignW.up (φ := φ) (a := a) g "" hal
    rwa [hcs] at this
  exact ⟨hson, hup, isValid_alongW φ a hwf hsat _ hup⟩

theorem CarriesW_sendToW (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkW φ k kv) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (next : PureLine) (hn : LineOkW φ (k + 1) next) (hc : CarriesW φ a (k + 1) next) :
    CarriesW φ a (k + 1) (sendToW φ kv.2 next d) := by
  simp only [sendToW]
  split
  · next hval =>
      exact CarriesW_insertPure φ a (k + 1) next d _ hn (StateOkW_sent φ k kv hkv d hd hval) hc
  · exact hc

theorem sons_fold_monoW (k : Int) (kv : NodeId × GPathM) (hkv : StateOkW φ k kv) :
    ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, LineOkW φ (k + 1) acc → CarriesW φ a (k + 1) acc →
        LineOkW φ (k + 1) (l.foldl (sendToW φ kv.2) acc)
          ∧ CarriesW φ a (k + 1) (l.foldl (sendToW φ kv.2) acc) := by
  intro l
  induction l with
  | nil => intro _ acc h hc; exact ⟨h, hc⟩
  | cons x xs ih =>
    intro hx acc h hc
    simp only [List.foldl_cons]
    exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
      (LineOkW_sendToW φ k kv hkv x (hx x List.mem_cons_self) acc h)
      (CarriesW_sendToW φ a k kv hkv x (hx x List.mem_cons_self) acc h hc)

theorem CarriesW_sendAllW (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkW φ k kv) (next : PureLine) (hn : LineOkW φ (k + 1) next)
    (hc : CarriesW φ a (k + 1) next) : CarriesW φ a (k + 1) (sendAllW φ kv next) := by
  simp only [sendAllW]
  exact (sons_fold_monoW φ a k kv hkv _ (fun _ hd => hd) next hn hc).2

theorem sons_fold_establishW (hwf : WF φ) (hsat : Sat a φ)
    (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssignW φ a g) (hcs : g.current_step = k + 1)
    (hkv : StateOkW φ k (selOfAssign φ a k, g)) :
    ∀ (l : List NodeId),
      (∀ d ∈ l, d ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index) →
      selOfAssign φ a (k + 1) ∈ l →
      ∀ acc, LineOkW φ (k + 1) acc →
        LineOkW φ (k + 1) (l.foldl (sendToW φ g) acc)
          ∧ CarriesW φ a (k + 1) (l.foldl (sendToW φ g) acc) := by
  obtain ⟨hson, hup, hval⟩ := advance_targetW φ a hwf hsat k h0 hk g hal hcs
  intro l
  induction l with
  | nil => intro _ hd; exact absurd hd List.not_mem_nil
  | cons x xs ih =>
    intro hx hd acc h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hd with rfl | hd'
    · have hsend : sendToW φ g acc (selOfAssign φ a (k + 1))
          = insertPure acc (selOfAssign φ a (k + 1))
              (upFilteringWeak g (weakReqOfCnf φ (selOfAssign φ a (k + 1)))
                (reqOfCnf φ (selOfAssign φ a (k + 1))) (selOfAssign φ a (k + 1)) "") := by
        simp only [sendToW, hval, if_true]
      have hsok : StateOkW φ (k + 1) (selOfAssign φ a (k + 1),
          upFilteringWeak g (weakReqOfCnf φ (selOfAssign φ a (k + 1)))
            (reqOfCnf φ (selOfAssign φ a (k + 1))) (selOfAssign φ a (k + 1)) "") :=
        StateOkW_sent φ k (selOfAssign φ a k, g) hkv _ hson hval
      have hbase : LineOkW φ (k + 1) (sendToW φ g acc (selOfAssign φ a (k + 1)))
          ∧ CarriesW φ a (k + 1) (sendToW φ g acc (selOfAssign φ a (k + 1))) := by
        rw [hsend]
        exact ⟨LineOkW_insertPure φ (k + 1) acc _ _ h hsok,
          CarriesW_of_insertPure_at φ a (k + 1) acc _ h hsok hup⟩
      exact sons_fold_monoW φ a k (selOfAssign φ a k, g) hkv xs
        (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _ hbase.1 hbase.2
    · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
        (LineOkW_sendToW φ k (selOfAssign φ a k, g) hkv x (hx x List.mem_cons_self) acc h)

theorem outer_fold_monoW (k : Int) :
    ∀ (l : PureLine), (∀ kv ∈ l, StateOkW φ k kv) →
      ∀ acc, LineOkW φ (k + 1) acc → CarriesW φ a (k + 1) acc →
        LineOkW φ (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc)
          ∧ CarriesW φ a (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc) := by
  intro l
  induction l with
  | nil => intro _ acc h hc; exact ⟨h, hc⟩
  | cons x xs ih =>
    intro hx acc h hc
    simp only [List.foldl_cons]
    exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
      (LineOkW_sendAllW φ k x (hx x List.mem_cons_self) acc h)
      (CarriesW_sendAllW φ a k x (hx x List.mem_cons_self) acc h hc)

/-- **One improved driver step conserves the branch.** -/
theorem CarriesW_pureAdvanceW (hwf : WF φ) (hsat : Sat a φ)
    (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (line : PureLine) (hl : LineOkW φ k line) (hc : CarriesW φ a k line) :
    CarriesW φ a (k + 1) (pureAdvanceW φ line) := by
  obtain ⟨g, hmem, hal, hcs⟩ := hc
  have hkv : StateOkW φ k (selOfAssign φ a k, g) := hl.2 _ hmem
  simp only [pureAdvanceW]
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOkW φ k kv) →
      (selOfAssign φ a k, g) ∈ l →
      ∀ acc, LineOkW φ (k + 1) acc →
        LineOkW φ (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc)
          ∧ CarriesW φ a (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · have hbase : LineOkW φ (k + 1) (sendAllW φ (selOfAssign φ a k, g) acc)
            ∧ CarriesW φ a (k + 1) (sendAllW φ (selOfAssign φ a k, g) acc) := by
          simp only [sendAllW]
          exact sons_fold_establishW φ a hwf hsat k h0 hk g hal hcs hkv _
            (fun _ hdm => hdm)
            (by
              rw [selOfAssign_step]
              exact selOfAssign_son φ a hsat k h0 hk)
            acc h
        exact outer_fold_monoW φ a k xs (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) _
          hbase.1 hbase.2
      · exact ih (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) hd' _
          (LineOkW_sendAllW φ k x (hx x List.mem_cons_self) acc h)
  exact (main line hl.2 hmem [] ⟨by simp, by intro kv hkv'; exact absurd hkv' List.not_mem_nil⟩).2

-- ============================================================
-- The first line, and the whole run
-- ============================================================

theorem stateOkW_initSeed (d : NodeId) (hd : d ∈ mapNodes φ 0) :
    StateOkW φ 0 (d, GPathM.initSeed d "") := by
  have hstep : d.step = 0 := mapNodes_step φ 0 d hd
  refine ⟨hd, ShapeOk_initSeed d "" hstep, ?_, ?_, isValid_initSeed d "" hstep⟩
  · simp only [initSeed_current]; omega
  · rfl

theorem stepCount_pos : (0 : Int) < stepCount φ := by
  simp only [stepCount]; omega

theorem initW_ok (hsat : Sat a φ) : LineOkW φ 0 (pureInit φ) ∧ CarriesW φ a 0 (pureInit φ) := by
  have hsel : selOfAssign φ a 0 ∈ mapNodes φ 0 :=
    selOfAssign_onMap φ a hsat 0 (by omega) (stepCount_pos φ)
  simp only [pureInit]
  have mono : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineOkW φ 0 acc → CarriesW φ a 0 acc →
        LineOkW φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc)
          ∧ CarriesW φ a 0
            (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h hc; exact ⟨h, hc⟩
    | cons x xs ih =>
      intro hx acc h hc
      simp only [List.foldl_cons]
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (LineOkW_insertPure φ 0 acc x _ h (stateOkW_initSeed φ x (hx x List.mem_cons_self)))
        (CarriesW_insertPure φ a 0 acc x _ h
          (stateOkW_initSeed φ x (hx x List.mem_cons_self)) hc)
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) → selOfAssign φ a 0 ∈ l →
      ∀ acc, LineOkW φ 0 acc →
        LineOkW φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc)
          ∧ CarriesW φ a 0
            (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact mono xs (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
          (LineOkW_insertPure φ 0 acc _ _ h (stateOkW_initSeed φ _ hsel))
          (CarriesW_of_insertPure_at φ a 0 acc _ h (stateOkW_initSeed φ _ hsel)
            (AlongAssignW.seed ""))
      · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
          (LineOkW_insertPure φ 0 acc x _ h (stateOkW_initSeed φ x (hx x List.mem_cons_self)))
  exact main _ (fun _ hdm => hdm) hsel []
    ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem runW_ok (hwf : WF φ) (hsat : Sat a φ) :
    ∀ (n : Nat) (k : Int), 0 ≤ k → k + (n : Int) < stepCount φ →
      ∀ line, LineOkW φ k line → CarriesW φ a k line →
        LineOkW φ (k + (n : Int)) (pureStepsW φ n line)
          ∧ CarriesW φ a (k + (n : Int)) (pureStepsW φ n line) := by
  intro n
  induction n with
  | zero => intro k _ _ line hl hc; simpa using ⟨hl, hc⟩
  | succ m ih =>
    intro k h0 hk line hl hc
    have heq : k + ((m + 1 : Nat) : Int) = (k + 1) + (m : Int) := by omega
    rw [heq]
    simp only [pureStepsW]
    exact ih (k + 1) (by omega) (by omega) _
      (LineOkW_pureAdvanceW φ k line hl)
      (CarriesW_pureAdvanceW φ a hwf hsat k h0 (by omega) line hl hc)

/-- **The improved driver ends holding the branch.** -/
theorem pureRunW_carries (hwf : WF φ) (hsat : Sat a φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunW φ
      ∧ AlongAssignW φ a g ∧ g.current_step = stepCount φ := by
  have hzero := stepCount_pos φ
  obtain ⟨hl0, hc0⟩ := initW_ok φ a hsat
  have hcast : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  have h := runW_ok φ a hwf hsat (stepCount φ - 1).toNat 0 (by omega)
    (by omega) (pureInit φ) hl0 hc0
  have h0e : (0 : Int) + (stepCount φ - 1) = stepCount φ - 1 := by omega
  rw [hcast, h0e] at h
  obtain ⟨g, hmem, hal, hcs⟩ := h.2
  exact ⟨g, by simp only [pureRunW]; exact hmem, hal, by omega⟩

/-- **The improved machine loses no solution.** The state parked at a
satisfying assignment's final node spans the whole map, is valid, and denotes
something. -/
theorem pureRunW_full_state (hwf : WF φ) (hsat : Sat a φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunW φ
      ∧ g.current_step = stepCount φ
      ∧ isValid g = true
      ∧ AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨g, hmem, hal, hcs⟩ := pureRunW_carries φ a hwf hsat
  exact ⟨g, hmem, hcs, isValid_alongW φ a hwf hsat g hal, inhabited_alongW φ a hwf hsat g hal⟩

/-- **A satisfiable formula gets a non-empty last line.** -/
theorem pureRunW_ne_nil (hwf : WF φ) (h : Satisfiable φ) : pureRunW φ ≠ [] := by
  obtain ⟨b, hsat⟩ := h
  obtain ⟨g, hmem, _, _⟩ := pureRunW_carries φ b hwf hsat
  intro hnil
  rw [hnil] at hmem
  exact absurd hmem List.not_mem_nil

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ConservationImproves.chainSound_alongW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_alongW

/-- info: 'AbsSat.GraphPath.Model.ConservationImproves.pureRunW_full_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunW_full_state

/-- info: 'AbsSat.GraphPath.Model.ConservationImproves.pureRunW_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunW_ne_nil

end AbsSat.GraphPath.Model.ConservationImproves
