import AbsSat.GraphPath.Model.ConservationCore
import AbsSat.GraphPath.Model.SacFilter

/-!
# Conservation, once, for any filter that keeps the branch

`ConservationImproves` proves the weak-filter machine loses no solution, and `ConservationPins` does
the same work again for the pin prune. A third filter — the conditioned one of `SacFilter` — would
mean a third copy, so this module does the argument once, for an arbitrary

```
F : NodeId → GPathM → GPathM
```

applied before the hard requirements, under two hypotheses:

* `hFpr` — the filtered state is a `Pruned` narrowing, so every shape fact survives;
* `hFcs` — a sound chain whose ids are the assignment's own choices survives the filter.

`chainSound_up_of_pruned` is already stated for an arbitrary narrowing, so the heart of the
conservation law needs nothing new; what the filter touches is the branch invariant and the driver
bookkeeping.

The weak filter satisfies `hFcs` through `weakReqOfCnf_sound`; the conditioned filter satisfies it
with no side condition at all (`SacFilter.ChainSound_filterACn`).

This slice covers the branch invariant and the chain results; the driver bookkeeping follows.
-/

namespace AbsSat.GraphPath.Model.ConservationFilter

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit mem_insertPure
  mem_insertPure_of_ne key_inj isValid_of_grown insertPure_keys_some insertPure_keys_none
  isValid_initSeed)
open AbsSat.GraphPath.Model.ConservationCore (ShapeOk ShapeOk_of_pruned ShapeOk_initSeed
  ShapeOk_addNode ShapeOk_join chainSound_up_of_prunedR stepCount_pos SelParent)
open AbsSat.GraphPath.Model.AggressiveReview (ReviewOk filterAllR upFilteringR pruned_filterAllR)

variable (φ : Cnf) (a : Assign) (F : NodeId → GPathM → GPathM) (R : GPathM → GPathM) [ReviewOk R]

/-- The filter, then the hard requirements and the review `R`, then `up`. -/
def upFilteringF (g : GPathM) (d : NodeId) (title : String) : GPathM :=
  upFilteringR R (F d g) (reqOfCnf φ d) d title

/-- What the filter has to keep: a narrowing that loses no branch chain. -/
abbrev PrunesF : Prop := ∀ d g, Pruned g (F d g)

/-- A sound chain that follows the assignment survives the filter at the node the assignment
picks. The weak filter needs `weakReqOfCnf_sound` for this; the conditioned filter needs nothing. -/
abbrev KeepsBranchF : Prop :=
  ∀ (d : NodeId) (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
    (∀ k, 0 ≤ k → k < g.current_step →
      (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k)) →
    d = selOfAssign φ a g.current_step → ChainSound (F d g) sel

-- ============================================================
-- Shape
-- ============================================================

theorem ShapeOk_upFilteringF (hFpr : PrunesF F) (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (h : ShapeOk g) : ShapeOk (upFilteringF φ F R g d title) := by
  have hpr : Pruned g (filterAllR R (F d g) (reqOfCnf φ d)) :=
    Pruned.trans (hFpr d g) (pruned_filterAllR R _ _)
  have hf := ShapeOk_of_pruned hpr h
  simp only [upFilteringF, upFilteringR, GPathM.up]
  split
  · exact ShapeOk_addNode _ d title (by rw [hpr.step_eq]; exact hd) hf
  · exact hf

-- ============================================================
-- The branch invariant
-- ============================================================

/-- The states the driver builds along the assignment's branch. -/
inductive AlongAssignF : GPathM → Prop where
  | seed (title : String) :
      AlongAssignF (GPathM.initSeed (selOfAssign φ a 0) title)
  | up (g : GPathM) (title : String) :
      AlongAssignF g →
      AlongAssignF (upFilteringF φ F R g (selOfAssign φ a g.current_step) title)
  | joinL (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₂ : ShapeOk g₂) :
      AlongAssignF g₁ → AlongAssignF (GPathM.join g₁ g₂)
  | joinR (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₁ : ShapeOk g₁) :
      AlongAssignF g₂ → AlongAssignF (GPathM.join g₁ g₂)

theorem shapeOk_of_alongF (hFpr : PrunesF F) (g : GPathM) (h : AlongAssignF φ a F R g) :
    ShapeOk g := by
  induction h with
  | seed title => exact ShapeOk_initSeed _ title (selOfAssign_step φ a 0)
  | up g title _ ih =>
    exact ShapeOk_upFilteringF φ F R hFpr g _ title (selOfAssign_step φ a g.current_step) ih
  | joinL g₁ g₂ hok h₂ _ ih => exact ShapeOk_join g₁ g₂ hok ih h₂
  | joinR g₁ g₂ hok h₁ _ ih => exact ShapeOk_join g₁ g₂ hok h₁ ih

-- ============================================================
-- The conservation law
-- ============================================================

/-- The map node the last `up` visited is a selected node. A filter that removes **nodes** needs
this to know the branch never contradicts its own pins. -/
theorem mapParent_alongF (hFpr : PrunesF F) (g : GPathM) (h : AlongAssignF φ a F R g) :
    g.map_parent = none ∨ ∃ j, g.map_parent = some (selOfAssign φ a j) := by
  induction h with
  | seed title =>
    unfold GPathM.initSeed GPathM.up
    rw [if_pos (by rfl : isValid empty = true)]
    exact Or.inr ⟨0, rfl⟩
  | up g title _ ih =>
    have hpr : Pruned g (filterAllR R (F (selOfAssign φ a g.current_step) g)
        (reqOfCnf φ (selOfAssign φ a g.current_step))) :=
      Pruned.trans (hFpr _ g) (pruned_filterAllR R _ _)
    simp only [upFilteringF, upFilteringR, GPathM.up]
    split
    · exact Or.inr ⟨g.current_step, rfl⟩
    · rw [hpr.map_parent_eq]
      exact ih
  | joinL g₁ g₂ _ _ _ ih => exact ih
  | joinR g₁ g₂ hok _ _ ih =>
    have hmp : g₁.map_parent = g₂.map_parent := by
      simp only [okJoin, Bool.and_eq_true, beq_iff_eq] at hok
      exact hok.1.1.2
    show g₁.map_parent = none ∨ ∃ j, g₁.map_parent = some (selOfAssign φ a j)
    rw [hmp]
    exact ih

/-- **The branch's chain survives every state the driver builds**, whatever the filter, as long as
it narrows and keeps the branch. -/
theorem chainSound_alongF (hwf : WF φ) (hFpr : PrunesF F) (hFcs : KeepsBranchF φ a F)
    (g : GPathM) (h : AlongAssignF φ a F R g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step →
        (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) := by
  induction h with
  | seed title =>
    refine ⟨fun _ => { id := selOfAssign φ a 0, parent_id := none }, ?_, ?_⟩
    · exact ChainSound_initSeed _ title (selOfAssign_step φ a 0)
    · intro k hlo hhi
      rw [initSeed_current] at hhi
      have hk : k = 0 := by omega
      subst hk
      exact ⟨rfl, Or.inl rfl⟩
  | up g title hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    obtain ⟨sel', hs', hcur, hids'⟩ :=
      chainSound_up_of_prunedR φ a R hwf g _ (hFpr _ g) (shapeOk_of_alongF φ a F R hFpr g hal)
        (mapParent_alongF φ a F R hFpr g hal) sel (hFcs _ g sel hsel hids rfl) hids title
    exact ⟨sel', hs', fun k hk0 hk => hids' k hk0 (lt_of_lt_of_eq hk hcur)⟩
  | joinL g₁ g₂ hok h₂ _ ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_left g₁ g₂).step_eq] at hk; exact hk)⟩
  | joinR g₁ g₂ hok h₁ _ ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_right g₁ g₂ hok).step_eq] at hk; exact hk)⟩

theorem isValid_alongF (hwf : WF φ) (hFpr : PrunesF F) (hFcs : KeepsBranchF φ a F)
    (g : GPathM) (h : AlongAssignF φ a F R g) : isValid g = true := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongF φ a F R hwf hFpr hFcs g h
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

theorem inhabited_alongF (hwf : WF φ) (hFpr : PrunesF F) (hFcs : KeepsBranchF φ a F)
    (g : GPathM) (h : AlongAssignF φ a F R g) : ∃ sel, ChainSound g sel := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongF φ a F R hwf hFpr hFcs g h
  exact ⟨sel, hsel⟩

-- ============================================================
-- The state is inhabited along the branch
-- ============================================================

theorem inhabitedM_alongF (hwf : WF φ) (hFpr : PrunesF F) (hFcs : KeepsBranchF φ a F)
    (g : GPathM) (h : AlongAssignF φ a F R g) : AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongF φ a F R hwf hFpr hFcs g h
  exact ⟨pathOf sel g, sel, hsel.chain.1, hsel.chain.2.1, rfl⟩

-- ============================================================
-- The driver
-- ============================================================

def sendToF (g : GPathM) (next : PureLine) (d : NodeId) : PureLine :=
  if isValid (upFilteringF φ F R g d "") then insertPure next d (upFilteringF φ F R g d "") else next

def sendAllF (kv : NodeId × GPathM) (next : PureLine) : PureLine :=
  (mapSons φ kv.1.step kv.1.index).foldl (sendToF φ F R kv.2) next

def pureAdvanceF (line : PureLine) : PureLine :=
  line.foldl (fun next kv => sendAllF φ F R kv next) []

def pureStepsF : Nat → PureLine → PureLine
  | 0, line => line
  | n + 1, line => pureStepsF n (pureAdvanceF φ F R line)

/-- The whole run with the filter. Empty means UNSAT. -/
def pureRunF : PureLine := pureStepsF φ F R (stepCount φ - 1).toNat (pureInit φ)

-- ============================================================
-- The line invariant
-- ============================================================

structure StateOkF (φ : Cnf) (k : Int) (kv : NodeId × GPathM) : Prop where
  onMap : kv.1 ∈ mapNodes φ k
  shape : ShapeOk kv.2
  step  : kv.2.current_step = k + 1
  par   : kv.2.map_parent = some kv.1
  valid : isValid kv.2 = true

def LineOkF (k : Int) (line : PureLine) : Prop :=
  (line.map (·.1)).Nodup ∧ ∀ kv ∈ line, StateOkF φ k kv

theorem okJoin_of_stateOkF (k : Int) (key : NodeId) (e g : GPathM)
    (he : StateOkF φ k (key, e)) (hg : StateOkF φ k (key, g)) : okJoin e g = true := by
  simp only [okJoin, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨he.step.trans hg.step.symm, he.par.trans hg.par.symm⟩, he.valid⟩, hg.valid⟩

theorem stateOkF_doJoin (k : Int) (key : NodeId) (e g : GPathM)
    (he : StateOkF φ k (key, e)) (hg : StateOkF φ k (key, g)) :
    StateOkF φ k (key, doJoin e g) := by
  have hok := okJoin_of_stateOkF φ k key e g he hg
  simp only [doJoin, hok, if_pos]
  exact ⟨he.onMap, ShapeOk_join e g hok he.shape hg.shape, he.step, he.par,
    isValid_of_grown (grown_join_left e g) he.valid⟩

theorem LineOkF_insertPure (k : Int) (line : PureLine) (key : NodeId) (g : GPathM)
    (hl : LineOkF φ k line) (hg : StateOkF φ k (key, g)) :
    LineOkF φ k (insertPure line key g) := by
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
    have hesok : StateOkF φ k (key, e.2) := by
      have h := hall e hemem
      rwa [← hekey]
    constructor
    · rw [insertPure_keys_some line key g e hf]; exact hnd
    · intro kv hkv
      simp only [insertPure, hf] at hkv
      obtain ⟨x, hx, hEq⟩ := List.mem_map.mp hkv
      cases hb : x.1 == key with
      | true =>
        have hx2 : kv = (key, doJoin e.2 g) := by rw [← hEq]; simp only [hb]; rfl
        rw [hx2]
        exact stateOkF_doJoin φ k key e.2 g hesok hg
      | false =>
        have hx2 : kv = x := by rw [← hEq]; simp only [hb]; rfl
        rw [hx2]
        exact hall x hx

-- ============================================================
-- The branch's entry
-- ============================================================

def CarriesF (k : Int) (line : PureLine) : Prop :=
  ∃ g, (selOfAssign φ a k, g) ∈ line ∧ AlongAssignF φ a F R g ∧ g.current_step = k + 1

omit [ReviewOk R] in
theorem CarriesF_insertPure (k : Int) (line : PureLine)
    (key : NodeId) (g' : GPathM) (hl : LineOkF φ k line) (hg' : StateOkF φ k (key, g'))
    (hc : CarriesF φ a F R k line) : CarriesF φ a F R k (insertPure line key g') := by
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
      have hesok : StateOkF φ k (selOfAssign φ a k, g) := by
        have h := hall e hemem
        rw [hee] at h
        exact h
      have hok : okJoin g g' = true :=
        okJoin_of_stateOkF φ k (selOfAssign φ a k) g g' hesok hg'
      refine ⟨join g g', ?_, AlongAssignF.joinL g g' hok hg'.shape hal, hcs⟩
      simp only [insertPure, hf, hee, doJoin, hok, if_pos]
      refine List.mem_map.mpr ⟨(selOfAssign φ a k, g), hmem, ?_⟩
      simp
  · exact ⟨g, mem_insertPure_of_ne line key _ g' g hkey hmem, hal, hcs⟩

omit [ReviewOk R] in
theorem CarriesF_of_insertPure_at (k : Int) (line : PureLine)
    (g' : GPathM) (hl : LineOkF φ k line) (hg' : StateOkF φ k (selOfAssign φ a k, g'))
    (hal : AlongAssignF φ a F R g') :
    CarriesF φ a F R k (insertPure line (selOfAssign φ a k) g') := by
  obtain ⟨h, hmem, hcase⟩ := mem_insertPure line (selOfAssign φ a k) g'
  refine ⟨h, hmem, ?_, ?_⟩
  · rcases hcase with rfl | ⟨e, hem, rfl⟩
    · exact hal
    · have he : StateOkF φ k (selOfAssign φ a k, e) := hl.2 _ hem
      have hok := okJoin_of_stateOkF φ k _ e g' he hg'
      simp only [doJoin, hok, if_pos]
      exact AlongAssignF.joinR e g' hok he.shape hal
  · rcases hcase with rfl | ⟨e, hem, rfl⟩
    · exact hg'.step
    · have he : StateOkF φ k (selOfAssign φ a k, e) := hl.2 _ hem
      have hok := okJoin_of_stateOkF φ k _ e g' he hg'
      simp only [doJoin, hok, if_pos]
      rw [(grown_join_left e g').step_eq]
      exact he.step

-- ============================================================
-- One send
-- ============================================================

omit [ReviewOk R] in
theorem isValid_filter_of_sentF (g : GPathM) (d : NodeId)
    (hval : isValid (upFilteringF φ F R g d "") = true) :
    isValid (filterAllR R (F d g) (reqOfCnf φ d)) = true := by
  by_cases h : isValid (filterAllR R (F d g) (reqOfCnf φ d)) = true
  · exact h
  · exfalso
    have he : upFilteringF φ F R g d "" = filterAllR R (F d g) (reqOfCnf φ d) := by
      simp only [upFilteringF, upFilteringR, GPathM.up, if_neg h]
    rw [he] at hval
    exact h hval

theorem StateOkF_sent (hFpr : PrunesF F) (k : Int) (kv : NodeId × GPathM) (hkv : StateOkF φ k kv)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringF φ F R kv.2 d "") = true) :
    StateOkF φ (k + 1) (d, upFilteringF φ F R kv.2 d "") := by
  have hkey : kv.1.step = k := mapNodes_step φ k kv.1 hkv.onMap
  have hmk : (⟨k, kv.1.index⟩ : NodeId) ∈ mapNodes φ k := by
    have hid : (⟨k, kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix =>
        rw [hkv1] at hkey
        simp only at hkey ⊢
        rw [hkey]
    rw [hid]; exact hkv.onMap
  have hd' : d ∈ mapNodes φ (k + 1) :=
    mapSons_subset φ k kv.1.index hmk d (by rw [← hkey]; exact hd)
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hd'
  have hfv := isValid_filter_of_sentF φ F R kv.2 d hval
  have hpr : Pruned kv.2 (filterAllR R (F d kv.2) (reqOfCnf φ d)) :=
    Pruned.trans (hFpr d kv.2) (pruned_filterAllR R _ _)
  have hshape : upFilteringF φ F R kv.2 d "" = addNode (filterAllR R (F d kv.2) (reqOfCnf φ d)) d "" := by
    simp only [upFilteringF, upFilteringR, GPathM.up, hfv, if_pos]
  refine ⟨hd', ?_, ?_, ?_, hval⟩
  · exact ShapeOk_upFilteringF φ F R hFpr kv.2 d "" (by rw [hdstep, hkv.step]) hkv.shape
  · rw [hshape, addNode_current, hpr.step_eq, hkv.step]
  · rw [hshape]; rfl

theorem LineOkF_sendToF (hFpr : PrunesF F) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (next : PureLine) (hn : LineOkF φ (k + 1) next) :
    LineOkF φ (k + 1) (sendToF φ F R kv.2 next d) := by
  simp only [sendToF]
  split
  · next hval =>
      exact LineOkF_insertPure φ (k + 1) next d _ hn (StateOkF_sent φ F R hFpr k kv hkv d hd hval)
  · exact hn

theorem LineOkF_sendAllF (hFpr : PrunesF F) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) (next : PureLine) (hn : LineOkF φ (k + 1) next) :
    LineOkF φ (k + 1) (sendAllF φ F R kv next) := by
  simp only [sendAllF]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, LineOkF φ (k + 1) acc → LineOkF φ (k + 1) (l.foldl (sendToF φ F R kv.2) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (LineOkF_sendToF φ F R hFpr k kv hkv x (hx x List.mem_cons_self) acc h)
  exact main _ (fun _ hd => hd) next hn

theorem LineOkF_pureAdvanceF (hFpr : PrunesF F) (k : Int) (line : PureLine)
    (hl : LineOkF φ k line) : LineOkF φ (k + 1) (pureAdvanceF φ F R line) := by
  simp only [pureAdvanceF]
  obtain ⟨_, hall⟩ := hl
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOkF φ k kv) →
      ∀ acc, LineOkF φ (k + 1) acc →
        LineOkF φ (k + 1) (l.foldl (fun next kv => sendAllF φ F R kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (LineOkF_sendAllF φ F R hFpr k x (hx x List.mem_cons_self) acc h)
  exact main line hall [] ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

-- ============================================================
-- The branch through the two folds
-- ============================================================

theorem advance_targetF (hwf : WF φ) (hsat : Sat a φ) (hFpr : PrunesF F)
    (hFcs : KeepsBranchF φ a F) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssignF φ a F R g) (hcs : g.current_step = k + 1) :
    selOfAssign φ a (k + 1)
        ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index
      ∧ AlongAssignF φ a F R (upFilteringF φ F R g (selOfAssign φ a (k + 1)) "")
      ∧ isValid (upFilteringF φ F R g (selOfAssign φ a (k + 1)) "") = true := by
  have hson : selOfAssign φ a (k + 1)
      ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index := by
    rw [selOfAssign_step]
    exact selOfAssign_son φ a hsat k h0 hk
  have hup : AlongAssignF φ a F R (upFilteringF φ F R g (selOfAssign φ a (k + 1)) "") := by
    have hu := AlongAssignF.up (φ := φ) (a := a) (F := F) g "" hal
    rwa [hcs] at hu
  exact ⟨hson, hup, isValid_alongF φ a F R hwf hFpr hFcs _ hup⟩

theorem CarriesF_sendToF (hFpr : PrunesF F) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (next : PureLine) (hn : LineOkF φ (k + 1) next) (hc : CarriesF φ a F R (k + 1) next) :
    CarriesF φ a F R (k + 1) (sendToF φ F R kv.2 next d) := by
  simp only [sendToF]
  split
  · next hval =>
      exact CarriesF_insertPure φ a F R (k + 1) next d _ hn
        (StateOkF_sent φ F R hFpr k kv hkv d hd hval) hc
  · exact hc

theorem sons_fold_monoF (hFpr : PrunesF F) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) :
    ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, LineOkF φ (k + 1) acc → CarriesF φ a F R (k + 1) acc →
        LineOkF φ (k + 1) (l.foldl (sendToF φ F R kv.2) acc)
          ∧ CarriesF φ a F R (k + 1) (l.foldl (sendToF φ F R kv.2) acc) := by
  intro l
  induction l with
  | nil => intro _ acc h hc; exact ⟨h, hc⟩
  | cons x xs ih =>
    intro hx acc h hc
    simp only [List.foldl_cons]
    exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
      (LineOkF_sendToF φ F R hFpr k kv hkv x (hx x List.mem_cons_self) acc h)
      (CarriesF_sendToF φ a F R hFpr k kv hkv x (hx x List.mem_cons_self) acc h hc)

theorem CarriesF_sendAllF (hFpr : PrunesF F) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) (next : PureLine) (hn : LineOkF φ (k + 1) next)
    (hc : CarriesF φ a F R (k + 1) next) : CarriesF φ a F R (k + 1) (sendAllF φ F R kv next) := by
  simp only [sendAllF]
  exact (sons_fold_monoF φ a F R hFpr k kv hkv _ (fun _ hd => hd) next hn hc).2

theorem sons_fold_establishF (hwf : WF φ) (hsat : Sat a φ) (hFpr : PrunesF F)
    (hFcs : KeepsBranchF φ a F) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssignF φ a F R g) (hcs : g.current_step = k + 1)
    (hkv : StateOkF φ k (selOfAssign φ a k, g)) :
    ∀ (l : List NodeId),
      (∀ d ∈ l, d ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index) →
      selOfAssign φ a (k + 1) ∈ l →
      ∀ acc, LineOkF φ (k + 1) acc →
        LineOkF φ (k + 1) (l.foldl (sendToF φ F R g) acc)
          ∧ CarriesF φ a F R (k + 1) (l.foldl (sendToF φ F R g) acc) := by
  obtain ⟨hson, hup, hval⟩ := advance_targetF φ a F R hwf hsat hFpr hFcs k h0 hk g hal hcs
  intro l
  induction l with
  | nil => intro _ hd; exact absurd hd List.not_mem_nil
  | cons x xs ih =>
    intro hx hd acc h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hd with rfl | hd'
    · have hsend : sendToF φ F R g acc (selOfAssign φ a (k + 1))
          = insertPure acc (selOfAssign φ a (k + 1))
              (upFilteringF φ F R g (selOfAssign φ a (k + 1)) "") := by
        simp only [sendToF, hval, if_true]
      have hsok : StateOkF φ (k + 1) (selOfAssign φ a (k + 1),
          upFilteringF φ F R g (selOfAssign φ a (k + 1)) "") :=
        StateOkF_sent φ F R hFpr k (selOfAssign φ a k, g) hkv _ hson hval
      have hbase : LineOkF φ (k + 1) (sendToF φ F R g acc (selOfAssign φ a (k + 1)))
          ∧ CarriesF φ a F R (k + 1) (sendToF φ F R g acc (selOfAssign φ a (k + 1))) := by
        rw [hsend]
        exact ⟨LineOkF_insertPure φ (k + 1) acc _ _ h hsok,
          CarriesF_of_insertPure_at φ a F R (k + 1) acc _ h hsok hup⟩
      exact sons_fold_monoF φ a F R hFpr k (selOfAssign φ a k, g) hkv xs
        (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _ hbase.1 hbase.2
    · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
        (LineOkF_sendToF φ F R hFpr k (selOfAssign φ a k, g) hkv x (hx x List.mem_cons_self) acc h)

theorem outer_fold_monoF (hFpr : PrunesF F) (k : Int) :
    ∀ (l : PureLine), (∀ kv ∈ l, StateOkF φ k kv) →
      ∀ acc, LineOkF φ (k + 1) acc → CarriesF φ a F R (k + 1) acc →
        LineOkF φ (k + 1) (l.foldl (fun next kv => sendAllF φ F R kv next) acc)
          ∧ CarriesF φ a F R (k + 1) (l.foldl (fun next kv => sendAllF φ F R kv next) acc) := by
  intro l
  induction l with
  | nil => intro _ acc h hc; exact ⟨h, hc⟩
  | cons x xs ih =>
    intro hx acc h hc
    simp only [List.foldl_cons]
    exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
      (LineOkF_sendAllF φ F R hFpr k x (hx x List.mem_cons_self) acc h)
      (CarriesF_sendAllF φ a F R hFpr k x (hx x List.mem_cons_self) acc h hc)

/-- **One driver step conserves the branch**, for any filter that narrows and keeps it. -/
theorem CarriesF_pureAdvanceF (hwf : WF φ) (hsat : Sat a φ) (hFpr : PrunesF F)
    (hFcs : KeepsBranchF φ a F) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (line : PureLine) (hl : LineOkF φ k line) (hc : CarriesF φ a F R k line) :
    CarriesF φ a F R (k + 1) (pureAdvanceF φ F R line) := by
  obtain ⟨g, hmem, hal, hcs⟩ := hc
  have hkv : StateOkF φ k (selOfAssign φ a k, g) := hl.2 _ hmem
  simp only [pureAdvanceF]
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOkF φ k kv) →
      (selOfAssign φ a k, g) ∈ l →
      ∀ acc, LineOkF φ (k + 1) acc →
        LineOkF φ (k + 1) (l.foldl (fun next kv => sendAllF φ F R kv next) acc)
          ∧ CarriesF φ a F R (k + 1) (l.foldl (fun next kv => sendAllF φ F R kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · have hbase : LineOkF φ (k + 1) (sendAllF φ F R (selOfAssign φ a k, g) acc)
            ∧ CarriesF φ a F R (k + 1) (sendAllF φ F R (selOfAssign φ a k, g) acc) := by
          simp only [sendAllF]
          exact sons_fold_establishF φ a F R hwf hsat hFpr hFcs k h0 hk g hal hcs hkv _
            (fun _ hdm => hdm)
            (by
              rw [selOfAssign_step]
              exact selOfAssign_son φ a hsat k h0 hk)
            acc h
        exact outer_fold_monoF φ a F R hFpr k xs (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) _
          hbase.1 hbase.2
      · exact ih (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) hd' _
          (LineOkF_sendAllF φ F R hFpr k x (hx x List.mem_cons_self) acc h)
  exact (main line hl.2 hmem [] ⟨by simp, by intro kv hkv'; exact absurd hkv' List.not_mem_nil⟩).2

-- ============================================================
-- The first line, and the whole run
-- ============================================================

theorem stateOkF_initSeed (d : NodeId) (hd : d ∈ mapNodes φ 0) :
    StateOkF φ 0 (d, GPathM.initSeed d "") := by
  have hstep : d.step = 0 := mapNodes_step φ 0 d hd
  refine ⟨hd, ShapeOk_initSeed d "" hstep, ?_, ?_, isValid_initSeed d "" hstep⟩
  · simp only [initSeed_current]; omega
  · rfl

omit [ReviewOk R] in
theorem initF_ok (hsat : Sat a φ) :
    LineOkF φ 0 (pureInit φ) ∧ CarriesF φ a F R 0 (pureInit φ) := by
  have hsel : selOfAssign φ a 0 ∈ mapNodes φ 0 :=
    selOfAssign_onMap φ a hsat 0 (by omega) (stepCount_pos φ)
  simp only [pureInit]
  have mono : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineOkF φ 0 acc → CarriesF φ a F R 0 acc →
        LineOkF φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc)
          ∧ CarriesF φ a F R 0
            (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h hc; exact ⟨h, hc⟩
    | cons x xs ih =>
      intro hx acc h hc
      simp only [List.foldl_cons]
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (LineOkF_insertPure φ 0 acc x _ h (stateOkF_initSeed φ x (hx x List.mem_cons_self)))
        (CarriesF_insertPure φ a F R 0 acc x _ h
          (stateOkF_initSeed φ x (hx x List.mem_cons_self)) hc)
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) → selOfAssign φ a 0 ∈ l →
      ∀ acc, LineOkF φ 0 acc →
        LineOkF φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc)
          ∧ CarriesF φ a F R 0
            (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact mono xs (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
          (LineOkF_insertPure φ 0 acc _ _ h (stateOkF_initSeed φ _ hsel))
          (CarriesF_of_insertPure_at φ a F R 0 acc _ h (stateOkF_initSeed φ _ hsel)
            (AlongAssignF.seed ""))
      · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
          (LineOkF_insertPure φ 0 acc x _ h (stateOkF_initSeed φ x (hx x List.mem_cons_self)))
  exact main _ (fun _ hdm => hdm) hsel []
    ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem runF_ok (hwf : WF φ) (hsat : Sat a φ) (hFpr : PrunesF F) (hFcs : KeepsBranchF φ a F) :
    ∀ (n : Nat) (k : Int), 0 ≤ k → k + (n : Int) < stepCount φ →
      ∀ line, LineOkF φ k line → CarriesF φ a F R k line →
        LineOkF φ (k + (n : Int)) (pureStepsF φ F R n line)
          ∧ CarriesF φ a F R (k + (n : Int)) (pureStepsF φ F R n line) := by
  intro n
  induction n with
  | zero => intro k _ _ line hl hc; simpa using ⟨hl, hc⟩
  | succ m ih =>
    intro k h0 hk line hl hc
    have heq : k + ((m + 1 : Nat) : Int) = (k + 1) + (m : Int) := by omega
    rw [heq]
    simp only [pureStepsF]
    exact ih (k + 1) (by omega) (by omega) _
      (LineOkF_pureAdvanceF φ F R hFpr k line hl)
      (CarriesF_pureAdvanceF φ a F R hwf hsat hFpr hFcs k h0 (by omega) line hl hc)

/-- **The driver ends holding the branch.** -/
theorem pureRunF_carries (hwf : WF φ) (hsat : Sat a φ) (hFpr : PrunesF F)
    (hFcs : KeepsBranchF φ a F) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunF φ F R
      ∧ AlongAssignF φ a F R g ∧ g.current_step = stepCount φ := by
  have hzero := stepCount_pos φ
  obtain ⟨hl0, hc0⟩ := initF_ok φ a F R hsat
  have hcast : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  have h := runF_ok φ a F R hwf hsat hFpr hFcs (stepCount φ - 1).toNat 0 (by omega)
    (by omega) (pureInit φ) hl0 hc0
  have h0e : (0 : Int) + (stepCount φ - 1) = stepCount φ - 1 := by omega
  rw [hcast, h0e] at h
  obtain ⟨g, hmem, hal, hcs⟩ := h.2
  exact ⟨g, by simp only [pureRunF]; exact hmem, hal, by omega⟩

/-- **The machine with the filter loses no solution.** -/
theorem pureRunF_full_state (hwf : WF φ) (hsat : Sat a φ) (hFpr : PrunesF F)
    (hFcs : KeepsBranchF φ a F) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunF φ F R
      ∧ g.current_step = stepCount φ
      ∧ isValid g = true
      ∧ AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨g, hmem, hal, hcs⟩ := pureRunF_carries φ a F R hwf hsat hFpr hFcs
  exact ⟨g, hmem, hcs, isValid_alongF φ a F R hwf hFpr hFcs g hal,
    inhabitedM_alongF φ a F R hwf hFpr hFcs g hal⟩

/-- **A satisfiable formula gets a non-empty last line.** -/
theorem pureRunF_ne_nil (hwf : WF φ) (hFpr : PrunesF F)
    (hFcs : ∀ b : Assign, Sat b φ → KeepsBranchF φ b F) (h : Satisfiable φ) :
    pureRunF φ F R ≠ [] := by
  obtain ⟨b, hsat⟩ := h
  obtain ⟨g, hmem, _, _⟩ := pureRunF_carries φ b F R hwf hsat hFpr (hFcs b hsat)
  intro hnil
  rw [hnil] at hmem
  exact absurd hmem List.not_mem_nil

-- ============================================================
-- The conditioned filter as an instance
-- ============================================================

open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf weakReqOfCnf_sound)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeakAll)
open AbsSat.GraphPath.Model.ConservationCore (pruned_filterWeakAll ChainSound_filterWeakAll)
open AbsSat.GraphPath.Model.SacFilter (filterACn pruned_filterACn ChainSound_filterACn)

/-- The weak filter of `CnfMapImproves`, then `n` passes of the conditioned filter. -/
def Fsac (n : Nat) (d : NodeId) (g : GPathM) : GPathM :=
  filterACn n (filterWeakAll g (weakReqOfCnf φ d))

theorem prunes_Fsac (n : Nat) : PrunesF (Fsac φ n) := fun _d g =>
  Pruned.trans (pruned_filterWeakAll g _) (pruned_filterACn n _)

/-- The branch survives both filters: the weak one by `weakReqOfCnf_sound`, the conditioned one for
free. -/
theorem keepsBranch_Fsac (hsat : Sat a φ) (n : Nat) : KeepsBranchF φ a (Fsac φ n) := by
  intro d g sel hsel hids hd
  refine ChainSound_filterACn n _ sel (ChainSound_filterWeakAll _ g sel hsel ?_)
  intro e he k hk0 hk hke
  rw [(hids k hk0 hk).1, hke]
  exact weakReqOfCnf_sound φ a hsat g.current_step e (by rw [← hd]; exact he)

/-- **The machine with the conditioned filter keeps the branch.** Along a satisfying assignment,
the selection it names is a sound chain of every state the driver builds, for any number of
conditioned passes. -/
theorem chainSound_alongSac (hwf : WF φ) (hsat : Sat a φ) (n : Nat) (g : GPathM)
    (h : AlongAssignF φ a (Fsac φ n) review g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step →
        (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) :=
  chainSound_alongF φ a _ review hwf (prunes_Fsac φ n) (keepsBranch_Fsac φ a hsat n) g h

theorem isValid_alongSac (hwf : WF φ) (hsat : Sat a φ) (n : Nat) (g : GPathM)
    (h : AlongAssignF φ a (Fsac φ n) review g) : isValid g = true :=
  isValid_alongF φ a _ review hwf (prunes_Fsac φ n) (keepsBranch_Fsac φ a hsat n) g h

/-- info: 'AbsSat.GraphPath.Model.ConservationFilter.chainSound_alongF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_alongF

/-- info: 'AbsSat.GraphPath.Model.ConservationFilter.chainSound_alongSac' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_alongSac

-- ============================================================
-- The conditioned machine
-- ============================================================

/-- The driver run with the weak filter followed by `n` conditioned passes. -/
def pureRunSac (n : Nat) : PureLine := pureRunF φ (Fsac φ n) review

/-- **The conditioned machine loses no solution.** -/
theorem pureRunSac_full_state (hwf : WF φ) (hsat : Sat a φ) (n : Nat) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunSac φ n
      ∧ g.current_step = stepCount φ
      ∧ isValid g = true
      ∧ AbsSat.GraphPath.Model.Inhabited g :=
  pureRunF_full_state φ a (Fsac φ n) review hwf hsat (prunes_Fsac φ n) (keepsBranch_Fsac φ a hsat n)

/-- **A satisfiable formula still gets a non-empty last line.** -/
theorem pureRunSac_ne_nil (hwf : WF φ) (n : Nat) (h : Satisfiable φ) : pureRunSac φ n ≠ [] :=
  pureRunF_ne_nil φ (Fsac φ n) review hwf (prunes_Fsac φ n)
    (fun b hb => keepsBranch_Fsac φ b hb n) h

/-- info: 'AbsSat.GraphPath.Model.ConservationFilter.pureRunSac_full_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunSac_full_state

/-- info: 'AbsSat.GraphPath.Model.ConservationFilter.pureRunSac_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunSac_ne_nil

end AbsSat.GraphPath.Model.ConservationFilter
