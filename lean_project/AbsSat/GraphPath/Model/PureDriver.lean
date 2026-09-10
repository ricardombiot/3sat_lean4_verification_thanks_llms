-- lean_project/AbsSat/GraphPath/Model/PureDriver.lean
import AbsSat.GraphPath.Model.Conservation

/-!
# The driver, over the arithmetic map

`MirrorTest.mirrorRun` is the machine's timeline loop, and it is written over
`GMap` — `Std.HashMap` underneath. Reasoning about it directly would drag
`Classical.choice` into every closure downstream, which is exactly what the
arithmetic model of the map was built to avoid.

So this is the same loop over `CnfMap`/`CnfSel`: `mapSons` in place of
`map_node.sons`, `reqOfCnf` in place of `destine_node.requires`, `mapNodes` in
place of `get_ids_step gmap 0`. One more layer of the same mirror pattern that
`GPathM` applies to `GPath` — the model is for proving, and a differential band
ties it to the thing that runs.

Titles are the one deliberate difference: the real driver copies the map node's
title into the graph, and nothing in `isValid`, `owners` or `denot` reads it, so
the model passes `""`. The band therefore compares keys, node counts and
validity, not titles.
-/

namespace AbsSat.GraphPath.Model.PureDriver

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.Conservation

/-- One timeline row: states keyed by the map node just visited. -/
abbrev PureLine := List (NodeId × GPathM)

/-- Mirror of `MirrorTest.insertGPath`: states arriving at the same map node
are merged. -/
def insertPure (line : PureLine) (key : NodeId) (g : GPathM) : PureLine :=
  match line.find? (fun kv => kv.1 == key) with
  | some (_, existing) =>
    line.map (fun kv => if kv.1 == key then (key, doJoin existing g) else kv)
  | none => line ++ [(key, g)]

/-- Send one state to one destination, keeping it only if the filter leaves it
valid. -/
def sendTo (φ : Cnf) (g : GPathM) (next : PureLine) (d : NodeId) : PureLine :=
  if isValid (upFiltering g (reqOfCnf φ d) d "") then
    insertPure next d (upFiltering g (reqOfCnf φ d) d "")
  else next

/-- Send one state to every son of its origin. -/
def sendAll (φ : Cnf) (kv : NodeId × GPathM) (next : PureLine) : PureLine :=
  (mapSons φ kv.1.step kv.1.index).foldl (sendTo φ kv.2) next

/-- Mirror of `MirrorTest.mirrorAdvance`: every state is sent to every son of
its origin, filtered by the destination's requirements, and kept only if the
result is still valid. -/
def pureAdvance (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv => sendAll φ kv next) []

def pureInit (φ : Cnf) : PureLine :=
  (mapNodes φ 0).foldl (fun line id => insertPure line id (initSeed id "")) []

def pureSteps (φ : Cnf) : Nat → PureLine → PureLine
  | 0, line => line
  | n + 1, line => pureSteps φ n (pureAdvance φ line)

/-- The whole run. An empty result is the UNSAT answer. -/
def pureRun (φ : Cnf) : PureLine := pureSteps φ (stepCount φ - 1).toNat (pureInit φ)

-- ============================================================
-- What one insert does
-- ============================================================

/-- After an insert there is an entry at the key, and its state is either the
one inserted or its join with what was already parked there. -/
theorem mem_insertPure (line : PureLine) (key : NodeId) (g : GPathM) :
    ∃ h, (key, h) ∈ insertPure line key g ∧
      (h = g ∨ ∃ e, (key, e) ∈ line ∧ h = doJoin e g) := by
  unfold insertPure
  cases hf : line.find? (fun kv => kv.1 == key) with
  | none => exact ⟨g, List.mem_append_right _ List.mem_cons_self, Or.inl rfl⟩
  | some kv =>
    have hmem : kv ∈ line := List.mem_of_find?_eq_some hf
    have hkey : kv.1 = key :=
      eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
    refine ⟨doJoin kv.2 g, ?_, Or.inr ⟨kv.2, by rw [← hkey]; exact hmem, rfl⟩⟩
    have : (key, doJoin kv.2 g)
        = (fun x : NodeId × GPathM => if x.1 == key then (key, doJoin kv.2 g) else x) kv := by
      simp only [hkey, beq_self_eq_true, if_pos]
    rw [this]
    exact List.mem_map_of_mem hmem

/-- An entry at a *different* key survives an insert. -/
theorem mem_insertPure_of_ne (line : PureLine) (key k' : NodeId) (g h : GPathM)
    (hne : k' ≠ key) (hmem : (k', h) ∈ line) : (k', h) ∈ insertPure line key g := by
  unfold insertPure
  cases hf : line.find? (fun kv => kv.1 == key) with
  | none => exact List.mem_append_left _ hmem
  | some kv =>
    have hnb : ¬ ((k' == key) = true) := fun hc => hne (eq_of_beq hc)
    have : (k', h)
        = (fun x : NodeId × GPathM => if x.1 == key then (key, doJoin kv.2 g) else x) (k', h) := by
      simp only
      rw [if_neg hnb]
    rw [this]
    exact List.mem_map_of_mem hmem

-- ============================================================
-- The edge the driver takes from the branch's state
-- ============================================================

/-- **The driver's own edge carries the branch forward.** From the state parked
at the assignment's node at step `k`, the son the driver is about to walk to is
the assignment's node at step `k+1`; the state it builds there is the branch's
next state; and it passes the validity guard, so the driver keeps it rather
than dropping it.

The three conjuncts are the three things `pureAdvance` needs at that point: the
destination is among `mapSons`, so the inner fold visits it; the result is
`AlongAssign`, so the conservation law still applies to it; and `isValid` holds,
so the `if` takes the inserting branch. -/
theorem advance_target (φ : Cnf) (a : Assign) (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssign φ a g) (hcs : g.current_step = k + 1) :
    selOfAssign φ a (k + 1)
        ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index
      ∧ AlongAssign φ a (upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
          (selOfAssign φ a (k + 1)) "")
      ∧ isValid (upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
          (selOfAssign φ a (k + 1)) "") = true := by
  have hson : selOfAssign φ a (k + 1)
      ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index := by
    rw [selOfAssign_step]
    exact selOfAssign_son φ a hsat k h0 hk
  have hup : AlongAssign φ a (upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
      (selOfAssign φ a (k + 1)) "") := by
    have := AlongAssign.up (φ := φ) (a := a) g "" (by omega) (by omega) hal
    rwa [hcs] at this
  exact ⟨hson, hup, isValid_along φ a hwf hsat hzero _ hup⟩

/-- info: 'AbsSat.GraphPath.Model.PureDriver.advance_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms advance_target

-- ============================================================
-- The line invariant
-- ============================================================

/-- Growing a graph cannot invalidate it: every step still has a global owner. -/
theorem isValid_of_grown {g g' : GPathM} (hgr : Grown g g') (h : isValid g = true) :
    isValid g' = true := by
  refine PickInduction.isValid_of_gowner _ ?_
  intro k hlo hhi
  rw [hgr.step_eq] at hhi
  obtain ⟨q, hq, hs⟩ := PickInduction.gowner_of_isValid g h k hlo hhi
  exact ⟨q, hgr.gowners_grown q hq, hs⟩

/-- What every state parked in a line at driver step `k` satisfies. The last
three fields are exactly what `okJoin` asks for, which is why two states
meeting at one key can always be merged. -/
structure StateOk (φ : Cnf) (k : Int) (kv : NodeId × GPathM) : Prop where
  onMap : kv.1 ∈ mapNodes φ k
  reach : MapReachable φ kv.2
  step  : kv.2.current_step = k + 1
  par   : kv.2.map_parent = some kv.1
  valid : isValid kv.2 = true

def LineOk (φ : Cnf) (k : Int) (line : PureLine) : Prop :=
  (line.map (·.1)).Nodup ∧ ∀ kv ∈ line, StateOk φ k kv

theorem okJoin_of_stateOk (φ : Cnf) (k : Int) (key : NodeId) (e g : GPathM)
    (he : StateOk φ k (key, e)) (hg : StateOk φ k (key, g)) : okJoin e g = true := by
  simp only [okJoin, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨he.step.trans hg.step.symm, he.par.trans hg.par.symm⟩, he.valid⟩, hg.valid⟩

theorem stateOk_doJoin (φ : Cnf) (k : Int) (key : NodeId) (e g : GPathM)
    (he : StateOk φ k (key, e)) (hg : StateOk φ k (key, g)) :
    StateOk φ k (key, doJoin e g) := by
  have hok := okJoin_of_stateOk φ k key e g he hg
  simp only [doJoin, hok, if_pos]
  exact ⟨he.onMap, MapReachable.join e g hok he.reach hg.reach, he.step, he.par,
    isValid_of_grown (grown_join_left e g) he.valid⟩

/-- Merging never changes a line's keys, and appending adds exactly one. -/
theorem insertPure_keys_some (line : PureLine) (key : NodeId) (g : GPathM) (kv : NodeId × GPathM)
    (hf : line.find? (fun x => x.1 == key) = some kv) :
    (insertPure line key g).map (·.1) = line.map (·.1) := by
  simp only [insertPure, hf, List.map_map]
  refine List.map_congr_left ?_
  intro x _
  simp only [Function.comp_def]
  cases hb : x.1 == key with
  | true => exact (eq_of_beq hb).symm
  | false => rfl

theorem insertPure_keys_none (line : PureLine) (key : NodeId) (g : GPathM)
    (hf : line.find? (fun x => x.1 == key) = none) :
    (insertPure line key g).map (·.1) = line.map (·.1) ++ [key] := by
  simp only [insertPure, hf, List.map_append]
  rfl

theorem LineOk_insertPure (φ : Cnf) (k : Int) (line : PureLine) (key : NodeId) (g : GPathM)
    (hl : LineOk φ k line) (hg : StateOk φ k (key, g)) :
    LineOk φ k (insertPure line key g) := by
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
    have hesok : StateOk φ k (key, e.2) := by
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
        exact stateOk_doJoin φ k key e.2 g hesok hg
      | false =>
        have : kv = x := by rw [← hEq]; simp only [hb]; rfl
        rw [this]
        exact hall x hx

-- ============================================================
-- The branch's entry, and that an insert never loses it
-- ============================================================

/-- Distinct keys make a line a function: an entry is determined by its key. -/
theorem key_inj : ∀ (line : PureLine), (line.map (·.1)).Nodup →
    ∀ x ∈ line, ∀ y ∈ line, x.1 = y.1 → x = y := by
  intro line
  induction line with
  | nil => intro _ x hx; exact absurd hx List.not_mem_nil
  | cons c cs ih =>
    intro hnd x hx y hy hk
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd (by rw [hk]; exact List.mem_map_of_mem hy') hnd.1
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd (by rw [← hk]; exact List.mem_map_of_mem hx') hnd.1
      · exact ih hnd.2 x hx' y hy' hk

/-- The line carries the branch: an entry at the assignment's node, holding a
state of the branch. -/
def Carries (φ : Cnf) (a : Assign) (k : Int) (line : PureLine) : Prop :=
  ∃ g, (selOfAssign φ a k, g) ∈ line ∧ AlongAssign φ a g ∧ g.current_step = k + 1

/-- **An insert never loses the branch.** If it lands elsewhere the entry is
untouched; if it lands on the branch's own key, the entry absorbs the newcomer
with a `join`, and `AlongAssign.joinL` covers exactly that. -/
theorem Carries_insertPure (φ : Cnf) (a : Assign) (k : Int) (line : PureLine)
    (key : NodeId) (g' : GPathM) (hl : LineOk φ k line) (hg' : StateOk φ k (key, g'))
    (hc : Carries φ a k line) : Carries φ a k (insertPure line key g') := by
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
      have hesok : StateOk φ k (selOfAssign φ a k, g) := by
        have h := hall e hemem
        rw [hee] at h
        exact h
      have hok : okJoin g g' = true :=
        okJoin_of_stateOk φ k (selOfAssign φ a k) g g' hesok hg'
      refine ⟨join g g', ?_, AlongAssign.joinL g g' hok hg'.reach hal, hcs⟩
      simp only [insertPure, hf, hee, doJoin, hok, if_pos]
      refine List.mem_map.mpr ⟨(selOfAssign φ a k, g), hmem, ?_⟩
      simp
  · exact ⟨g, mem_insertPure_of_ne line key _ g' g hkey hmem, hal, hcs⟩

-- ============================================================
-- One send, and the folds
-- ============================================================

/-- If the result of a send is valid, the filter it went through was too —
otherwise `up` would have returned the invalid graph unchanged. -/
theorem isValid_filterAll_of_sent (φ : Cnf) (g : GPathM) (d : NodeId)
    (hval : isValid (upFiltering g (reqOfCnf φ d) d "") = true) :
    isValid (filterAll g (reqOfCnf φ d)) = true := by
  by_cases h : isValid (filterAll g (reqOfCnf φ d)) = true
  · exact h
  · exfalso
    have he : upFiltering g (reqOfCnf φ d) d "" = filterAll g (reqOfCnf φ d) := by
      simp only [upFiltering, GPathM.up, if_neg h]
    rw [he] at hval
    exact h hval

/-- **A state the driver keeps satisfies the line invariant at the next step.** -/
theorem StateOk_sent (φ : Cnf) (k : Int) (kv : NodeId × GPathM) (hkv : StateOk φ k kv)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFiltering kv.2 (reqOfCnf φ d) d "") = true) :
    StateOk φ (k + 1) (d, upFiltering kv.2 (reqOfCnf φ d) d "") := by
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
  have hfv := isValid_filterAll_of_sent φ kv.2 d hval
  have hpr := pruned_filterAll kv.2 (reqOfCnf φ d)
  have hshape : upFiltering kv.2 (reqOfCnf φ d) d ""
      = addNode (filterAll kv.2 (reqOfCnf φ d)) d "" := by
    simp only [upFiltering, GPathM.up, hfv, if_pos]
  refine ⟨hd', ?_, ?_, ?_, hval⟩
  · exact MapReachable.up kv.2 d "" (by rw [hdstep, hkv.step]) (by rw [hdstep]; exact hd') hkv.reach
  · rw [hshape, addNode_current, hpr.step_eq, hkv.step]
  · rw [hshape]; rfl

/-- A property preserved by every step of a fold survives the fold. -/
theorem foldl_preserves {α : Type} (P : PureLine → Prop) (f : PureLine → α → PureLine)
    (hf : ∀ acc x, P acc → P (f acc x)) :
    ∀ (l : List α) (acc : PureLine), P acc → P (l.foldl f acc) := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x xs ih => intro acc h; simp only [List.foldl_cons]; exact ih _ (hf acc x h)

theorem LineOk_sendTo (φ : Cnf) (k : Int) (kv : NodeId × GPathM) (hkv : StateOk φ k kv)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (next : PureLine)
    (hn : LineOk φ (k + 1) next) : LineOk φ (k + 1) (sendTo φ kv.2 next d) := by
  simp only [sendTo]
  split
  · next hval => exact LineOk_insertPure φ (k + 1) next d _ hn (StateOk_sent φ k kv hkv d hd hval)
  · exact hn

theorem LineOk_sendAll (φ : Cnf) (k : Int) (kv : NodeId × GPathM) (hkv : StateOk φ k kv)
    (next : PureLine) (hn : LineOk φ (k + 1) next) :
    LineOk φ (k + 1) (sendAll φ kv next) := by
  simp only [sendAll]
  have : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, LineOk φ (k + 1) acc → LineOk φ (k + 1) (l.foldl (sendTo φ kv.2) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (LineOk_sendTo φ k kv hkv x (hx x List.mem_cons_self) acc h)
  exact this _ (fun _ hd => hd) next hn

theorem LineOk_pureAdvance (φ : Cnf) (k : Int) (line : PureLine) (hl : LineOk φ k line) :
    LineOk φ (k + 1) (pureAdvance φ line) := by
  simp only [pureAdvance]
  obtain ⟨_, hall⟩ := hl
  have : ∀ (l : PureLine), (∀ kv ∈ l, StateOk φ k kv) →
      ∀ acc, LineOk φ (k + 1) acc → LineOk φ (k + 1) (l.foldl (fun next kv => sendAll φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (LineOk_sendAll φ k x (hx x List.mem_cons_self) acc h)
  exact this line hall [] ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

-- ============================================================
-- The branch through the two folds
-- ============================================================

/-- **The branch's own insert.** When the destination is the assignment's node,
whatever ends up parked there is on the branch: either the newcomer itself, or
its join with the state already there — and `AlongAssign.joinR` covers exactly
that second case. -/
theorem Carries_of_insertPure_at (φ : Cnf) (a : Assign) (k : Int) (line : PureLine)
    (g' : GPathM) (hl : LineOk φ k line) (hg' : StateOk φ k (selOfAssign φ a k, g'))
    (hal : AlongAssign φ a g') :
    Carries φ a k (insertPure line (selOfAssign φ a k) g') := by
  obtain ⟨h, hmem, hcase⟩ := mem_insertPure line (selOfAssign φ a k) g'
  refine ⟨h, hmem, ?_, ?_⟩
  · rcases hcase with rfl | ⟨e, hem, rfl⟩
    · exact hal
    · have he : StateOk φ k (selOfAssign φ a k, e) := hl.2 _ hem
      have hok := okJoin_of_stateOk φ k _ e g' he hg'
      simp only [doJoin, hok, if_pos]
      exact AlongAssign.joinR e g' hok he.reach hal
  · rcases hcase with rfl | ⟨e, hem, rfl⟩
    · exact hg'.step
    · have he : StateOk φ k (selOfAssign φ a k, e) := hl.2 _ hem
      have hok := okJoin_of_stateOk φ k _ e g' he hg'
      simp only [doJoin, hok, if_pos]
      rw [(grown_join_left e g').step_eq]
      exact he.step

theorem Carries_sendTo (φ : Cnf) (a : Assign) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOk φ k kv) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (next : PureLine) (hn : LineOk φ (k + 1) next) (hc : Carries φ a (k + 1) next) :
    Carries φ a (k + 1) (sendTo φ kv.2 next d) := by
  simp only [sendTo]
  split
  · next hval =>
      exact Carries_insertPure φ a (k + 1) next d _ hn (StateOk_sent φ k kv hkv d hd hval) hc
  · exact hc

/-- The inner fold keeps a branch entry it already had. -/
theorem sons_fold_mono (φ : Cnf) (a : Assign) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOk φ k kv) :
    ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, LineOk φ (k + 1) acc → Carries φ a (k + 1) acc →
        LineOk φ (k + 1) (l.foldl (sendTo φ kv.2) acc)
          ∧ Carries φ a (k + 1) (l.foldl (sendTo φ kv.2) acc) := by
  intro l
  induction l with
  | nil => intro _ acc h hc; exact ⟨h, hc⟩
  | cons x xs ih =>
    intro hx acc h hc
    simp only [List.foldl_cons]
    exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
      (LineOk_sendTo φ k kv hkv x (hx x List.mem_cons_self) acc h)
      (Carries_sendTo φ a k kv hkv x (hx x List.mem_cons_self) acc h hc)

theorem Carries_sendAll (φ : Cnf) (a : Assign) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOk φ k kv) (next : PureLine) (hn : LineOk φ (k + 1) next)
    (hc : Carries φ a (k + 1) next) : Carries φ a (k + 1) (sendAll φ kv next) := by
  simp only [sendAll]
  exact (sons_fold_mono φ a k kv hkv _ (fun _ hd => hd) next hn hc).2

/-- **The inner fold creates the branch entry.** The son the driver walks to
from the assignment's node at step `k` is the assignment's node at step `k+1`;
`advance_target` says the guard lets it through, so the insert happens, and
`Carries_of_insertPure_at` says the result is on the branch. -/
theorem sons_fold_establish (φ : Cnf) (a : Assign) (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssign φ a g) (hcs : g.current_step = k + 1)
    (hkv : StateOk φ k (selOfAssign φ a k, g)) :
    ∀ (l : List NodeId),
      (∀ d ∈ l, d ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index) →
      selOfAssign φ a (k + 1) ∈ l →
      ∀ acc, LineOk φ (k + 1) acc →
        LineOk φ (k + 1) (l.foldl (sendTo φ g) acc)
          ∧ Carries φ a (k + 1) (l.foldl (sendTo φ g) acc) := by
  obtain ⟨hson, hup, hval⟩ := advance_target φ a hwf hsat hzero k h0 hk g hal hcs
  intro l
  induction l with
  | nil => intro _ hd; exact absurd hd List.not_mem_nil
  | cons x xs ih =>
    intro hx hd acc h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hd with rfl | hd'
    · have hsend : sendTo φ g acc (selOfAssign φ a (k + 1))
          = insertPure acc (selOfAssign φ a (k + 1))
              (upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
                (selOfAssign φ a (k + 1)) "") := by
        simp only [sendTo, hval, if_true]
      have hsok : StateOk φ (k + 1) (selOfAssign φ a (k + 1),
          upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
            (selOfAssign φ a (k + 1)) "") :=
        StateOk_sent φ k (selOfAssign φ a k, g) hkv _ hson hval
      have hbase : LineOk φ (k + 1) (sendTo φ g acc (selOfAssign φ a (k + 1)))
          ∧ Carries φ a (k + 1) (sendTo φ g acc (selOfAssign φ a (k + 1))) := by
        rw [hsend]
        exact ⟨LineOk_insertPure φ (k + 1) acc _ _ h hsok,
          Carries_of_insertPure_at φ a (k + 1) acc _ h hsok hup⟩
      exact sons_fold_mono φ a k (selOfAssign φ a k, g) hkv xs
        (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _ hbase.1 hbase.2
    · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
        (LineOk_sendTo φ k (selOfAssign φ a k, g) hkv x (hx x List.mem_cons_self) acc h)

/-- The outer fold keeps a branch entry it already had. -/
theorem outer_fold_mono (φ : Cnf) (a : Assign) (k : Int) :
    ∀ (l : PureLine), (∀ kv ∈ l, StateOk φ k kv) →
      ∀ acc, LineOk φ (k + 1) acc → Carries φ a (k + 1) acc →
        LineOk φ (k + 1) (l.foldl (fun next kv => sendAll φ kv next) acc)
          ∧ Carries φ a (k + 1) (l.foldl (fun next kv => sendAll φ kv next) acc) := by
  intro l
  induction l with
  | nil => intro _ acc h hc; exact ⟨h, hc⟩
  | cons x xs ih =>
    intro hx acc h hc
    simp only [List.foldl_cons]
    exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
      (LineOk_sendAll φ k x (hx x List.mem_cons_self) acc h)
      (Carries_sendAll φ a k x (hx x List.mem_cons_self) acc h hc)

/-- **One driver step conserves the branch.** -/
theorem Carries_pureAdvance (φ : Cnf) (a : Assign) (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (line : PureLine) (hl : LineOk φ k line) (hc : Carries φ a k line) :
    Carries φ a (k + 1) (pureAdvance φ line) := by
  obtain ⟨g, hmem, hal, hcs⟩ := hc
  have hkv : StateOk φ k (selOfAssign φ a k, g) := hl.2 _ hmem
  simp only [pureAdvance]
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOk φ k kv) →
      (selOfAssign φ a k, g) ∈ l →
      ∀ acc, LineOk φ (k + 1) acc →
        LineOk φ (k + 1) (l.foldl (fun next kv => sendAll φ kv next) acc)
          ∧ Carries φ a (k + 1) (l.foldl (fun next kv => sendAll φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · have hbase : LineOk φ (k + 1) (sendAll φ (selOfAssign φ a k, g) acc)
            ∧ Carries φ a (k + 1) (sendAll φ (selOfAssign φ a k, g) acc) := by
          simp only [sendAll]
          exact sons_fold_establish φ a hwf hsat hzero k h0 hk g hal hcs hkv _
            (fun _ hdm => hdm)
            (by
              rw [selOfAssign_step]
              exact selOfAssign_son φ a hsat k h0 hk)
            acc h
        exact outer_fold_mono φ a k xs (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) _
          hbase.1 hbase.2
      · exact ih (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) hd' _
          (LineOk_sendAll φ k x (hx x List.mem_cons_self) acc h)
  exact (main line hl.2 hmem [] ⟨by simp, by intro kv hkv'; exact absurd hkv' List.not_mem_nil⟩).2

/-- info: 'AbsSat.GraphPath.Model.PureDriver.Carries_pureAdvance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Carries_pureAdvance

-- ============================================================
-- The first line, and the whole run
-- ============================================================

theorem isValid_initSeed (d : NodeId) (title : String) (hstep : d.step = 0) :
    isValid (GPathM.initSeed d title) = true := by
  refine PickInduction.isValid_of_gowner _ ?_
  intro k hlo hhi
  rw [initSeed_current] at hhi
  refine ⟨{ id := d, parent_id := none }, ?_, ?_⟩
  · rw [Certifies.initSeed_gowners]; exact List.mem_cons_self ..
  · simp only [hstep]; omega

theorem stateOk_initSeed (φ : Cnf) (d : NodeId) (hd : d ∈ mapNodes φ 0) :
    StateOk φ 0 (d, GPathM.initSeed d "") := by
  have hstep : d.step = 0 := mapNodes_step φ 0 d hd
  refine ⟨hd, MapReachable.seed d "" hstep (by rw [hstep]; exact hd), ?_, ?_,
    isValid_initSeed d "" hstep⟩
  · simp only [initSeed_current]; omega
  · rfl

/-- **The first line is a line, and it carries every branch.** Every map node
of step 0 gets its own seed, and the assignment's node is one of them. -/
theorem init_ok (φ : Cnf) (a : Assign) (hsat : Sat a φ) (hzero : (0 : Int) < stepCount φ) :
    LineOk φ 0 (pureInit φ) ∧ Carries φ a 0 (pureInit φ) := by
  have hsel : selOfAssign φ a 0 ∈ mapNodes φ 0 := selOfAssign_onMap φ a hsat 0 (by omega) hzero
  simp only [pureInit]
  have mono : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineOk φ 0 acc → Carries φ a 0 acc →
        LineOk φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc)
          ∧ Carries φ a 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h hc; exact ⟨h, hc⟩
    | cons x xs ih =>
      intro hx acc h hc
      simp only [List.foldl_cons]
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (LineOk_insertPure φ 0 acc x _ h (stateOk_initSeed φ x (hx x List.mem_cons_self)))
        (Carries_insertPure φ a 0 acc x _ h
          (stateOk_initSeed φ x (hx x List.mem_cons_self)) hc)
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) → selOfAssign φ a 0 ∈ l →
      ∀ acc, LineOk φ 0 acc →
        LineOk φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc)
          ∧ Carries φ a 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact mono xs (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
          (LineOk_insertPure φ 0 acc _ _ h (stateOk_initSeed φ _ hsel))
          (Carries_of_insertPure_at φ a 0 acc _ h (stateOk_initSeed φ _ hsel)
            (AlongAssign.seed ""))
      · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
          (LineOk_insertPure φ 0 acc x _ h (stateOk_initSeed φ x (hx x List.mem_cons_self)))
  exact main _ (fun _ hdm => hdm) hsel []
    ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

/-- **The run conserves the branch, step after step.** -/
theorem run_ok (φ : Cnf) (a : Assign) (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) :
    ∀ (n : Nat) (k : Int), 0 ≤ k → k + (n : Int) < stepCount φ →
      ∀ line, LineOk φ k line → Carries φ a k line →
        LineOk φ (k + (n : Int)) (pureSteps φ n line)
          ∧ Carries φ a (k + (n : Int)) (pureSteps φ n line) := by
  intro n
  induction n with
  | zero => intro k _ _ line hl hc; simpa using ⟨hl, hc⟩
  | succ m ih =>
    intro k h0 hk line hl hc
    have heq : k + ((m + 1 : Nat) : Int) = (k + 1) + (m : Int) := by omega
    rw [heq]
    simp only [pureSteps]
    exact ih (k + 1) (by omega) (by omega) _
      (LineOk_pureAdvance φ k line hl)
      (Carries_pureAdvance φ a hwf hsat hzero k h0 (by omega) line hl hc)

/-- **The driver ends holding the branch.** For a satisfying assignment, the
last line of the run has an entry at that assignment's final map node, and the
state parked there was built along the assignment's branch — so it spans the
whole map and is valid.

This is the conservation law made operational: the driver is not asked to find
anything. The assignment names the path; every step of the driver either leaves
that path's state alone or merges another branch into it, and neither can
destroy it. -/
theorem pureRun_carries (φ : Cnf) (a : Assign) (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRun φ
      ∧ AlongAssign φ a g ∧ g.current_step = stepCount φ := by
  obtain ⟨hl0, hc0⟩ := init_ok φ a hsat hzero
  have hcast : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  have h := run_ok φ a hwf hsat hzero (stepCount φ - 1).toNat 0 (by omega)
    (by omega) (pureInit φ) hl0 hc0
  have h0e : (0 : Int) + (stepCount φ - 1) = stepCount φ - 1 := by omega
  rw [hcast, h0e] at h
  obtain ⟨g, hmem, hal, hcs⟩ := h.2
  exact ⟨g, by simp only [pureRun]; exact hmem, hal, by omega⟩

/-- The last line is not empty. -/
theorem pureRun_ne_nil (φ : Cnf) (hwf : WF φ) (hzero : (0 : Int) < stepCount φ)
    (h : Satisfiable φ) : pureRun φ ≠ [] := by
  obtain ⟨a, hsat⟩ := h
  obtain ⟨g, hmem, _, _⟩ := pureRun_carries φ a hwf hsat hzero
  intro hnil
  rw [hnil] at hmem
  exact absurd hmem List.not_mem_nil

/-- **What the driver ends up holding.** The state parked at the assignment's
final node spans the whole map, is valid, and denotes something. Reading a
solution out of it is `L7.sat_of_inhabited`; getting there for an *arbitrary*
state of the run — rather than one known to be on a branch — is the open
problem, not this theorem. -/
theorem pureRun_full_state (φ : Cnf) (a : Assign) (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRun φ
      ∧ g.current_step = stepCount φ
      ∧ isValid g = true
      ∧ AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨g, hmem, hal, hcs⟩ := pureRun_carries φ a hwf hsat hzero
  exact ⟨g, hmem, hcs, isValid_along φ a hwf hsat hzero g hal,
    inhabited_along φ a hwf hsat hzero g hal⟩

/-- info: 'AbsSat.GraphPath.Model.PureDriver.init_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms init_ok

/-- info: 'AbsSat.GraphPath.Model.PureDriver.run_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_ok

/-- info: 'AbsSat.GraphPath.Model.PureDriver.pureRun_carries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRun_carries

/-- info: 'AbsSat.GraphPath.Model.PureDriver.pureRun_full_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRun_full_state

/-- info: 'AbsSat.GraphPath.Model.PureDriver.pureRun_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRun_ne_nil

/-!
## What the driver theorem says, and what it does not

`pureRun_full_state` closes the loop this file opened: for a satisfying
assignment `a`, the last line of the driver's run has an entry at
`selOfAssign φ a (stepCount φ - 1)`, and the state parked there spans the whole
map, is valid, and denotes something.

The proof has two halves, and neither of them searches for anything.

* `advance_target` is the mathematical half, and it was already there: from the
  branch's state at step `k` the driver's own edge leads to the branch's state
  at step `k+1`, and the validity guard lets it through. That is the
  conservation law — the witness comes from the assignment, and the machine only
  has to not destroy it.
* Everything from `StateOk` down is bookkeeping about the list the driver
  carries. `LineOk` is the three invariants that make `insertPure` behave:
  distinct keys (so `find?` returns *our* entry), a common `current_step` and
  `map_parent` plus validity (so `okJoin` holds whenever two states meet at one
  key, and the merge is a real `join`), and `MapReachable` (so `AlongAssign`'s
  join constructors apply when our entry absorbs another branch). `Carries` is
  the branch's entry, and `Carries_insertPure` is the one step that matters: an
  insert elsewhere leaves it alone, an insert on top of it merges into it.

What this does **not** say:

* Nothing here claims the run is *small*. `pureAdvance` is a fold over the whole
  line, and the line can be as wide as `mapNodes` at that step. Complexity has
  no theorems in this development.
* Nothing here claims the converse. A non-empty last line does not yet imply
  `Satisfiable φ` — that direction goes through `Inhabited` and `sat_of_inhabited`
  for a *single* state, and `Inhabited` of an arbitrary state of the run is the
  open problem (`Supported`, no zombies), not something the driver settles.
* The executable driver is `MirrorTest.mirrorRun` over `GMap`, and its agreement
  with this one is measured, not proved: `lake exe cnfmap --driver` compares the
  two loops end to end, keys, node counts and validity.
-/

end AbsSat.GraphPath.Model.PureDriver
