-- lean_project/AbsSat/GraphPath/Model/ConservationPrefix.lean
import AbsSat.GraphPath.Model.PairPins

/-!
# The machine loses no **partial** solution

`ConservationFilter` proves the machine loses no solution: along a satisfying assignment, every line
of the run holds, at the assignment's node, a state that carries the assignment's branch as a sound
chain. The satisfaction of the formula enters in three places only — the branch's nodes are on the map,
each is a son of the one before, and the weak requirements are sound — and each of them looks only at
the clauses whose step has been reached.

This module runs the same induction **up to a step `K`**, for an assignment that satisfies only the
clauses below `K` (`SatBelow`):

* **`selOfAssign_onMap_below`**, **`selOfAssign_son_below`**, **`weakReqOfCnf_sound_below`** — the three
  map facts from the clauses below the step.
* **`chainSound_alongF_below`** — the branch's chain survives every state along the assignment up to
  `K`.
* **`carries_below`** — the line of step `K - 1` holds, at the assignment's node, a state along the
  assignment; so (**`chain_below`**) the line holds the assignment's partial branch as a sound chain.

This is the prefix completeness the no-borrowing argument needs (v148): every requirement-satisfying
partial path is a path of the state at its top.
-/

namespace AbsSat.GraphPath.Model.ConservationPrefix

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.ConservationCore (ShapeOk stepCount_pos SelParent chainSound_up_of_prunedR)
open AbsSat.GraphPath.Model.AggressiveReview (ReviewOk filterAllR upFilteringR pruned_filterAllR)
open AbsSat.GraphPath.Model.ConservationFilter

-- ============================================================
-- The map facts from the clauses below a step
-- ============================================================

/-- The assignment satisfies every clause whose step is below `K`. -/
def SatBelow (φ : Cnf) (a : Assign) (K : Int) : Prop :=
  ∀ j (hj : j < φ.clauses.length), clauseStep φ j < K → SatClause a φ.clauses[j]

theorem satBelow_mono {φ : Cnf} {a : Assign} {K K' : Int} (h : SatBelow φ a K) (hK : K' ≤ K) :
    SatBelow φ a K' :=
  fun j hj hs => h j hj (by omega)

theorem selOfAssign_onMap_below (φ : Cnf) (a : Assign) (k : Int) (hs : SatBelow φ a (k + 1))
    (h0 : 0 ≤ k) (hk : k < stepCount φ) : selOfAssign φ a k ∈ mapNodes φ k := by
  rcases step_cases φ k with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | h | ⟨j, hjlt, rfl⟩ | h
  · omega
  · rw [selOfAssign_var φ a v hv,
      mapNodes_var φ _ (by simp only [varStep]; omega) (by simp only [varStep, litBlock]; omega)]
    cases hb : a v <;> simp [bit_true, bit_false]
  · rw [selOfAssign_neg φ a v hv,
      mapNodes_var φ _ (by simp only [negStep]; omega) (by simp only [negStep, litBlock]; omega)]
    cases hb : a v <;> simp [bit_true, bit_false]
  · rw [mapNodes_fusion1 φ _ h]
    have h0' : ¬ (k < 0) := by rw [h]; simp only [litBlock]; omega
    have h1' : ¬ (k < litBlock φ) := by rw [h]; omega
    have h2' : k ≤ litBlock φ := by rw [h]; omega
    simp only [selOfAssign, if_neg h0', if_neg h1', if_pos h2']
    exact List.mem_cons_self
  · have hj : φ.clauses[j]? = some φ.clauses[j] := List.getElem?_eq_getElem hjlt
    have hrlo := rowOf_pos a φ.clauses[j] (hs j hjlt (by omega))
    have hrhi := rowOf_le a φ.clauses[j]
    rw [selOfAssign_clause φ a j _ hjlt hj, mapNodes_clause φ j hjlt _ rfl]
    have hr : rowOf a φ.clauses[j] = 1 ∨ rowOf a φ.clauses[j] = 2 ∨ rowOf a φ.clauses[j] = 3
        ∨ rowOf a φ.clauses[j] = 4 ∨ rowOf a φ.clauses[j] = 5 ∨ rowOf a φ.clauses[j] = 6
        ∨ rowOf a φ.clauses[j] = 7 := by omega
    rcases hr with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> simp
  · rw [mapNodes_fusionTop φ _ h hk]
    have h0' : ¬ (k < 0) := by simp only [fusionTop] at h; omega
    have h1' : ¬ (k < litBlock φ) := by simp only [fusionTop, litBlock] at h ⊢; omega
    have h2' : ¬ (k ≤ litBlock φ) := by simp only [fusionTop, litBlock] at h ⊢; omega
    simp only [selOfAssign, if_neg h0', if_neg h1', if_neg h2', if_pos h]
    exact List.mem_cons_self

theorem selOfAssign_son_below (φ : Cnf) (a : Assign) (k : Int) (hs : SatBelow φ a (k + 2))
    (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ) :
    selOfAssign φ a (k + 1) ∈ mapSons φ k (selOfAssign φ a k).index := by
  by_cases hvar : k < litBlock φ ∧ k % 2 = 0
  · obtain ⟨hlt, hpar⟩ := hvar
    obtain ⟨v, hv, rfl⟩ : ∃ v, v < φ.nVars ∧ k = varStep v := by
      refine ⟨(k / 2).toNat, ?_, ?_⟩
      · simp only [litBlock] at hlt
        omega
      · simp only [varStep]
        omega
    have hnext : varStep v + 1 = negStep v := by simp only [varStep, negStep]
    simp only [selOfAssign_var φ a v hv, mapSons_var φ v hv, hnext,
      selOfAssign_neg φ a v hv, bit_not, List.mem_singleton]
  · rw [mapSons_other φ k _ h0 hvar]
    exact selOfAssign_onMap_below φ a (k + 1) (by
      intro j hj hjs; exact hs j hj (by omega)) (by omega) hk

open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf weakRows weakBefore mem_weakBefore sharesVar)
open AbsSat.GraphMap.CnfReducer (rowPairs pairsAgree allRows pairsAgree_rowOfAssign rowOfAssign_mem_allRows)

/-- The weak requirements of the branch's node at step `k` hold along the branch, from the clauses
below `k`. -/
theorem weakReqOfCnf_sound_below (φ : Cnf) (a : Assign) (k : Int) (hs : SatBelow φ a k) :
    ∀ e ∈ weakReqOfCnf φ (selOfAssign φ a k), selOfAssign φ a e.1 ∈ e.2 := by
  intro e he
  have hstep : (selOfAssign φ a k).step = k := selOfAssign_step φ a k
  by_cases hlo : k ≤ litBlock φ
  · simp [weakReqOfCnf, hstep, hlo] at he
  by_cases htop : fusionTop φ ≤ k
  · simp [weakReqOfCnf, hstep, hlo, htop] at he
  cases hc : clauseAt φ k with
  | none => simp [weakReqOfCnf, hstep, hlo, htop, hc] at he
  | some c =>
    have hjc : φ.clauses[(k - litBlock φ - 1).toNat]? = some c := by
      simpa only [clauseAt, litBlock] using hc
    have hjlt : (k - litBlock φ - 1).toNat < φ.clauses.length := by
      cases Nat.lt_or_ge (k - litBlock φ - 1).toNat φ.clauses.length with
      | inl h => exact h
      | inr h => rw [List.getElem?_eq_none h] at hjc; simp at hjc
    have hk : clauseStep φ (k - litBlock φ - 1).toNat = k := by
      simp only [clauseStep, litBlock] at hlo ⊢
      omega
    have hsel := selOfAssign_clause φ a _ c hjlt hjc
    rw [hk] at hsel
    rw [hsel] at he
    simp only [weakReqOfCnf, if_neg hlo, if_neg htop, hc] at he
    obtain ⟨j', c', hj', hc', _, rfl⟩ := mem_weakBefore φ c _ _ e he
    have hj'lt : j' < φ.clauses.length := by omega
    have hcc : φ.clauses[j'] = c' := by
      rw [List.getElem?_eq_getElem hj'lt] at hc'; exact Option.some.inj hc'
    have hsc : SatClause a c' := by
      rw [← hcc]
      have hlt : clauseStep φ j' < clauseStep φ (k - litBlock φ - 1).toNat := by
        unfold clauseStep; omega
      exact hs j' hj'lt (by rw [← hk]; exact hlt)
    show selOfAssign φ a (clauseStep φ j') ∈ _
    rw [selOfAssign_clause φ a j' c' hj'lt hc']
    exact List.mem_map.mpr ⟨rowOf a c',
      List.mem_filter.mpr ⟨rowOfAssign_mem_allRows a c' hsc, pairsAgree_rowOfAssign a c c'⟩, rfl⟩

-- ============================================================
-- The conservation law, below a step
-- ============================================================

section
variable (φ : Cnf) (a : Assign) (F : NodeId → GPathM → GPathM) (R : GPathM → GPathM) [ReviewOk R]

/-- A sound chain that follows the assignment survives the filter, for states up to step `K`. -/
abbrev KeepsBranchBelow (K : Int) : Prop :=
  ∀ (d : NodeId) (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
    (∀ k, 0 ≤ k → k < g.current_step →
      (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k)) →
    d = selOfAssign φ a g.current_step → g.current_step ≤ K → ChainSound (F d g) sel

theorem cs_upFilteringF (hFpr : PrunesF F) (g : GPathM) (d : NodeId) (title : String) :
    g.current_step ≤ (upFilteringF φ F R g d title).current_step ∧
      (upFilteringF φ F R g d title).current_step ≤ g.current_step + 1 := by
  have hpr : Pruned g (filterAllR R (F d g) (reqOfCnf φ d)) :=
    Pruned.trans (hFpr d g) (pruned_filterAllR R _ _)
  simp only [upFilteringF, upFilteringR, GPathM.up]
  split
  · rw [addNode_current, hpr.step_eq]; exact ⟨by omega, by omega⟩
  · rw [hpr.step_eq]; exact ⟨by omega, by omega⟩

/-- **The branch's chain survives every state along the assignment, up to `K`.** -/
theorem chainSound_alongF_below (hwf : WF φ) (hFpr : PrunesF F) (K : Int)
    (hFcs : KeepsBranchBelow φ a F K) (g : GPathM) (h : AlongAssignF φ a F R g) :
    g.current_step ≤ K → ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step →
        (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) := by
  induction h with
  | seed title =>
    intro _
    refine ⟨fun _ => { id := selOfAssign φ a 0, parent_id := none }, ?_, ?_⟩
    · exact ChainSound_initSeed _ title (selOfAssign_step φ a 0)
    · intro k hlo hhi
      rw [initSeed_current] at hhi
      have hk : k = 0 := by omega
      subst hk
      exact ⟨rfl, Or.inl rfl⟩
  | up g title hal ih =>
    intro hb
    have hle := (cs_upFilteringF φ F R hFpr g (selOfAssign φ a g.current_step) title).1
    obtain ⟨sel, hsel, hids⟩ := ih (by omega)
    obtain ⟨sel', hs', hcur, hids'⟩ :=
      chainSound_up_of_prunedR φ a R hwf g _ (hFpr _ g) (shapeOk_of_alongF φ a F R hFpr g hal)
        (mapParent_alongF φ a F R hFpr g hal) sel (hFcs _ g sel hsel hids rfl (by omega)) hids title
    exact ⟨sel', hs', fun k hk0 hk => hids' k hk0 (lt_of_lt_of_eq hk hcur)⟩
  | joinL g₁ g₂ hok h₂ _ ih =>
    intro hb
    rw [(grown_join_left g₁ g₂).step_eq] at hb
    obtain ⟨sel, hsel, hids⟩ := ih hb
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_left g₁ g₂).step_eq] at hk; exact hk)⟩
  | joinR g₁ g₂ hok h₁ _ ih =>
    intro hb
    rw [(grown_join_right g₁ g₂ hok).step_eq] at hb
    obtain ⟨sel, hsel, hids⟩ := ih hb
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_right g₁ g₂ hok).step_eq] at hk; exact hk)⟩

theorem isValid_alongF_below (hwf : WF φ) (hFpr : PrunesF F) (K : Int) (hFcs : KeepsBranchBelow φ a F K)
    (g : GPathM) (h : AlongAssignF φ a F R g) (hb : g.current_step ≤ K) : isValid g = true := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongF_below φ a F R hwf hFpr K hFcs g h hb
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

theorem advance_targetF_below (hwf : WF φ) (K : Int) (hs : SatBelow φ a K) (hFpr : PrunesF F)
    (hFcs : KeepsBranchBelow φ a F K) (k : Int) (hK : k + 2 ≤ K) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssignF φ a F R g) (hcs : g.current_step = k + 1) :
    selOfAssign φ a (k + 1)
        ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index
      ∧ AlongAssignF φ a F R (upFilteringF φ F R g (selOfAssign φ a (k + 1)) "")
      ∧ isValid (upFilteringF φ F R g (selOfAssign φ a (k + 1)) "") = true := by
  have hson : selOfAssign φ a (k + 1)
      ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index := by
    rw [selOfAssign_step]
    exact selOfAssign_son_below φ a k (satBelow_mono hs hK) h0 hk
  have hup : AlongAssignF φ a F R (upFilteringF φ F R g (selOfAssign φ a (k + 1)) "") := by
    have hu := AlongAssignF.up (φ := φ) (a := a) (F := F) g "" hal
    rwa [hcs] at hu
  have hle := (cs_upFilteringF φ F R hFpr g (selOfAssign φ a (k + 1)) "").2
  exact ⟨hson, hup, isValid_alongF_below φ a F R hwf hFpr K hFcs _ hup (by omega)⟩

theorem sons_fold_establishF_below (hwf : WF φ) (K : Int) (hs : SatBelow φ a K) (hFpr : PrunesF F)
    (hFcs : KeepsBranchBelow φ a F K) (k : Int) (hK : k + 2 ≤ K) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssignF φ a F R g) (hcs : g.current_step = k + 1)
    (hkv : StateOkF φ k (selOfAssign φ a k, g)) :
    ∀ (l : List NodeId),
      (∀ d ∈ l, d ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index) →
      selOfAssign φ a (k + 1) ∈ l →
      ∀ acc, LineOkF φ (k + 1) acc →
        LineOkF φ (k + 1) (l.foldl (sendToF φ F R g) acc)
          ∧ CarriesF φ a F R (k + 1) (l.foldl (sendToF φ F R g) acc) := by
  obtain ⟨hson, hup, hval⟩ := advance_targetF_below φ a F R hwf K hs hFpr hFcs k hK h0 hk g hal hcs
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

/-- One driver step conserves the branch, below `K`. -/
theorem CarriesF_pureAdvanceF_below (hwf : WF φ) (K : Int) (hs : SatBelow φ a K) (hFpr : PrunesF F)
    (hFcs : KeepsBranchBelow φ a F K) (k : Int) (hK : k + 2 ≤ K) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
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
          exact sons_fold_establishF_below φ a F R hwf K hs hFpr hFcs k hK h0 hk g hal hcs hkv _
            (fun _ hdm => hdm)
            (by
              rw [selOfAssign_step]
              exact selOfAssign_son_below φ a k (satBelow_mono hs hK) h0 hk)
            acc h
        exact outer_fold_monoF φ a F R hFpr k xs (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) _
          hbase.1 hbase.2
      · exact ih (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) hd' _
          (LineOkF_sendAllF φ F R hFpr k x (hx x List.mem_cons_self) acc h)
  exact (main line hl.2 hmem [] ⟨by simp, by intro kv hkv'; exact absurd hkv' List.not_mem_nil⟩).2

omit [ReviewOk R] in
theorem initF_ok_below (hs : SatBelow φ a 1) :
    LineOkF φ 0 (pureInit φ) ∧ CarriesF φ a F R 0 (pureInit φ) := by
  have hsel : selOfAssign φ a 0 ∈ mapNodes φ 0 :=
    selOfAssign_onMap_below φ a 0 (by simpa using hs) (by omega) (stepCount_pos φ)
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


theorem runF_ok_below (hwf : WF φ) (K : Int) (hs : SatBelow φ a K) (hFpr : PrunesF F)
    (hFcs : KeepsBranchBelow φ a F K) :
    ∀ (n : Nat) (k : Int), 0 ≤ k → k + (n : Int) < stepCount φ → k + (n : Int) + 1 ≤ K →
      ∀ line, LineOkF φ k line → CarriesF φ a F R k line →
        LineOkF φ (k + (n : Int)) (pureStepsF φ F R n line)
          ∧ CarriesF φ a F R (k + (n : Int)) (pureStepsF φ F R n line) := by
  intro n
  induction n with
  | zero => intro k _ _ _ line hl hc; simpa using ⟨hl, hc⟩
  | succ m ih =>
    intro k h0 hk hkK line hl hc
    have heq : k + ((m + 1 : Nat) : Int) = (k + 1) + (m : Int) := by omega
    rw [heq]
    simp only [pureStepsF]
    exact ih (k + 1) (by omega) (by omega) (by omega) _
      (LineOkF_pureAdvanceF φ F R hFpr k line hl)
      (CarriesF_pureAdvanceF_below φ a F R hwf K hs hFpr hFcs k (by omega) h0 (by omega) line hl hc)

/-- **The line of step `K - 1` holds the assignment's partial branch**, for an assignment that
satisfies the clauses below `K`. -/
theorem carries_below (hwf : WF φ) (K : Int) (hK1 : 1 ≤ K) (hK2 : K ≤ stepCount φ)
    (hs : SatBelow φ a K) (hFpr : PrunesF F) (hFcs : KeepsBranchBelow φ a F K) :
    ∃ g, (selOfAssign φ a (K - 1), g) ∈ pureStepsF φ F R (K - 1).toNat (pureInit φ)
      ∧ AlongAssignF φ a F R g ∧ g.current_step = K := by
  obtain ⟨hl0, hc0⟩ := initF_ok_below φ a F R (satBelow_mono hs hK1)
  have h := runF_ok_below φ a F R hwf K hs hFpr hFcs (K - 1).toNat 0 (by omega) (by omega) (by omega)
    (pureInit φ) hl0 hc0
  have hcast : (0 : Int) + (((K - 1).toNat : Nat) : Int) = K - 1 := by omega
  rw [hcast] at h
  obtain ⟨g, hmem, hal, hcs⟩ := h.2
  exact ⟨g, hmem, hal, by omega⟩

/-- **The machine loses no partial solution.** The state the run holds at step `K - 1`, at the
assignment's node, carries the assignment's partial branch as a sound chain. -/
theorem chain_below (hwf : WF φ) (K : Int) (hK1 : 1 ≤ K) (hK2 : K ≤ stepCount φ)
    (hs : SatBelow φ a K) (hFpr : PrunesF F) (hFcs : KeepsBranchBelow φ a F K) :
    ∃ g, (selOfAssign φ a (K - 1), g) ∈ pureStepsF φ F R (K - 1).toNat (pureInit φ)
      ∧ g.current_step = K ∧ ∃ sel, ChainSound g sel ∧
        ∀ k, 0 ≤ k → k < K → (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) := by
  obtain ⟨g, hmem, hal, hcs⟩ := carries_below φ a F R hwf K hK1 hK2 hs hFpr hFcs
  obtain ⟨sel, hsel, hids⟩ := chainSound_alongF_below φ a F R hwf hFpr K hFcs g hal (by omega)
  exact ⟨g, hmem, hcs, sel, hsel, fun k hk0 hk => hids k hk0 (by omega)⟩

end

-- ============================================================
-- The Improves machine
-- ============================================================

theorem keepsBranch_Fsac_below (φ : Cnf) (a : Assign) (K : Int) (hs : SatBelow φ a K) (n : Nat) :
    KeepsBranchBelow φ a (Fsac φ n) K := by
  intro d g sel hsel hids hd hle
  refine SacFilter.ChainSound_filterACn n _ sel (ConservationCore.ChainSound_filterWeakAll _ g sel hsel ?_)
  intro e he k hk0 hk hke
  rw [(hids k hk0 hk).1, hke]
  exact weakReqOfCnf_sound_below φ a g.current_step (satBelow_mono hs hle) e (by rw [← hd]; exact he)

/-- **The Improves machine loses no partial solution**: for an assignment satisfying the clauses
below `K`, the run's line at step `K - 1` holds, at the assignment's node, a state carrying the
assignment's partial branch as a sound chain. -/
theorem pureStepsW_chain_below (φ : Cnf) (a : Assign) (hwf : WF φ) (K : Int) (hK1 : 1 ≤ K)
    (hK2 : K ≤ stepCount φ) (hs : SatBelow φ a K) :
    ∃ g, (selOfAssign φ a (K - 1), g) ∈ PureDriverImproves.pureStepsW φ (K - 1).toNat (pureInit φ)
      ∧ g.current_step = K ∧ ∃ sel, ChainSound g sel ∧
        ∀ k, 0 ≤ k → k < K → (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) := by
  obtain ⟨g, hmem, hcs, rest⟩ := chain_below φ a (Fsac φ 0) AggressiveReview.reviewAgg hwf K hK1 hK2 hs
    (prunes_Fsac φ 0) (keepsBranch_Fsac_below φ a K hs 0)
  refine ⟨g, ?_, hcs, rest⟩
  rw [← ConservationImproves.steps_eq φ]
  exact hmem

/-- info: 'AbsSat.GraphPath.Model.ConservationPrefix.pureStepsW_chain_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureStepsW_chain_below

-- ============================================================
-- A requirement-satisfying path is the branch of the assignment it spells
-- ============================================================

section
open AbsSat.GraphPath.Model.CnfChain (decode)
open AbsSat.GraphPath.Model.MapReachable (ChainOnMap)

variable (φ : Cnf)

theorem nodeId_eta (d : NodeId) : d = ⟨d.step, d.index⟩ := by cases d; rfl

theorem bit_beq_one (i : Int) (h : i = 0 ∨ i = 1) : bit (i == 1) = i := by
  rcases h with rfl | rfl <;> rfl

theorem bit_not_beq_one (i : Int) (h : i = 0 ∨ i = 1) : bit (!((1 - i) == 1)) = i := by
  rcases h with rfl | rfl <;> rfl

theorem index01 (k : Int) (h0 : 0 ≤ k) (hk : k < litBlock φ) (d : NodeId) (hd : d ∈ mapNodes φ k) :
    d = ⟨k, d.index⟩ ∧ (d.index = 0 ∨ d.index = 1) := by
  rw [mapNodes_var φ k h0 hk] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

/-- **A literal's requirement fixes its truth value in the decoded assignment.** -/
theorem litBit (g : GPathM) (sel : Int → PathNodeId) (hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel)
    (hcm : ChainOnMap φ g sel) (l : Lit) (hl : l.v < φ.nVars) (hlt : l.step < g.current_step) (b : Int)
    (hb : (sel l.step).id = litReq l b) : bit (litVal (decode sel) l) = b := by
  have hlo : (0 : Int) ≤ l.step := by unfold Lit.step; split <;> omega
  have hblk : l.step < litBlock φ := by unfold Lit.step litBlock; split <;> omega
  have hon := hcm l.step hlo hlt
  obtain ⟨_, hb01⟩ := index01 φ l.step hlo hblk _ hon
  rw [hb] at hb01
  simp only [litReq] at hb01
  cases hp : l.pos with
  | true =>
    have hstep : l.step = 2 * (l.v : Int) := by unfold Lit.step; rw [hp]; simp
    have hidx : (sel (2 * (l.v : Int))).id.index = b := by rw [← hstep, hb]; rfl
    simp only [litVal, hp, decode, if_true, hidx]
    exact bit_beq_one b hb01
  | false =>
    have hstep : l.step = 2 * (l.v : Int) + 1 := by unfold Lit.step; rw [hp]; simp
    have hnegstep : (sel (2 * (l.v : Int) + 1)).id.step = negStep l.v := by
      rw [← hstep, hb]; simp only [litReq, negStep]; omega
    have hreqs := reqOfCnf_neg φ (sel (2 * (l.v : Int) + 1)).id l.v hl hnegstep
    have hnegidx : (sel (2 * (l.v : Int) + 1)).id.index = b := by rw [← hstep, hb]; rfl
    rw [hnegidx] at hreqs
    have hmem : ({ step := varStep l.v, index := 1 - b } : NodeId)
        ∈ reqOfCnf φ (sel (2 * (l.v : Int) + 1)).id := by rw [hreqs]; exact List.mem_cons_self
    have hsecond := hrs (2 * (l.v : Int) + 1) (by omega) (by rw [← hstep]; exact hlt) _ hmem
      (by simp only [varStep]; omega) (by simp only [varStep]; omega)
    have hidx : (sel (2 * (l.v : Int))).id.index = 1 - b := by
      have : (sel (varStep l.v)).id.index = 1 - b := by rw [hsecond]
      simpa only [varStep] using this
    simp only [litVal, hp, decode, hidx]
    exact bit_not_beq_one b hb01

theorem bits_row (r : Int) (h1 : 1 ≤ r) (h7 : r ≤ 7) : 4 * b1 r + 2 * b2 r + b3 r = r := by
  unfold b1 b2 b3; omega

/-- **A requirement-satisfying path on the map is the branch of the assignment it spells**, at every
step it covers. -/
theorem ids_of_reqSat (hwf : WF φ) (g : GPathM) (sel : Int → PathNodeId) (hchain : IsChain g sel)
    (hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel) (hcm : ChainOnMap φ g sel)
    (hgs : g.current_step ≤ stepCount φ)
    (k : Int) (h0 : 0 ≤ k) (hk : k < g.current_step) : (sel k).id = selOfAssign φ (decode sel) k := by
  have hon := hcm k h0 hk
  have hst := (hchain.1 k h0 hk).2
  rcases step_cases φ k with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | h | ⟨j, hjlt, rfl⟩ | h
  · omega
  · rw [selOfAssign_var φ _ v hv]
    obtain ⟨hid, h01⟩ := index01 φ _ h0 (by simp only [varStep, litBlock]; omega) _ hon
    rw [hid]
    show (⟨varStep v, (sel (varStep v)).id.index⟩ : NodeId) = ⟨varStep v, bit (decode sel v)⟩
    simp only [decode, varStep] at h01 ⊢
    rw [bit_beq_one _ h01]
  · rw [selOfAssign_neg φ _ v hv]
    obtain ⟨hid, h01⟩ := index01 φ _ h0 (by simp only [negStep, litBlock]; omega) _ hon
    have hreqs := reqOfCnf_neg φ (sel (negStep v)).id v hv hst
    have hmem : ({ step := varStep v, index := 1 - (sel (negStep v)).id.index } : NodeId)
        ∈ reqOfCnf φ (sel (negStep v)).id := by rw [hreqs]; exact List.mem_cons_self
    have hsecond := hrs (negStep v) h0 hk _ hmem (by simp only [varStep]; omega)
      (by simp only [varStep, negStep] at hk ⊢; omega)
    have hidx : (sel (2 * (v : Int))).id.index = 1 - (sel (negStep v)).id.index := by
      have : (sel (varStep v)).id.index = 1 - (sel (negStep v)).id.index := by rw [hsecond]
      simpa only [varStep] using this
    rw [hid]
    show (⟨negStep v, (sel (negStep v)).id.index⟩ : NodeId) = ⟨negStep v, bit (!(decode sel v))⟩
    simp only [decode, hidx]
    rw [bit_not_beq_one _ h01]
  · rw [mapNodes_fusion1 φ _ h] at hon
    rw [List.mem_singleton.mp hon]
    have h0' : ¬ (k < 0) := by rw [h]; simp only [litBlock]; omega
    have h1' : ¬ (k < litBlock φ) := by rw [h]; omega
    have h2' : k ≤ litBlock φ := by rw [h]; omega
    simp only [selOfAssign, if_neg h0', if_neg h1', if_pos h2']
  · have hc : φ.clauses[j]? = some φ.clauses[j] := List.getElem?_eq_getElem hjlt
    obtain ⟨⟨hv1, hv2, hv3⟩, _⟩ := hwf φ.clauses[j] (List.mem_of_getElem? hc)
    rw [selOfAssign_clause φ _ j _ hjlt hc]
    obtain ⟨hr1, hr7⟩ := index_range_of_clauseNode φ j hjlt _ hon
    have hreqs := reqOfCnf_clause φ (sel (clauseStep φ j)).id j _ hjlt hc hst
    have hlitlt : ∀ lt : Lit, lt.v < φ.nVars → lt.step < g.current_step := by
      intro lt hlt
      have : lt.step < litBlock φ := by unfold Lit.step litBlock; split <;> omega
      simp only [clauseStep, litBlock] at hk this ⊢; omega
    have hlitlo : ∀ lt : Lit, 0 ≤ lt.step := by intro lt; unfold Lit.step; split <;> omega
    have sat1 := hrs (clauseStep φ j) h0 hk _ (by rw [hreqs]; exact List.mem_cons_self)
      (hlitlo _) (hlitlt _ hv1)
    have sat2 := hrs (clauseStep φ j) h0 hk _ (by rw [hreqs]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      (hlitlo _) (hlitlt _ hv2)
    have sat3 := hrs (clauseStep φ j) h0 hk _
      (by rw [hreqs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hlitlo _) (hlitlt _ hv3)
    have e1 := litBit φ g sel hrs hcm _ hv1 (hlitlt _ hv1) _ sat1
    have e2 := litBit φ g sel hrs hcm _ hv2 (hlitlt _ hv2) _ sat2
    have e3 := litBit φ g sel hrs hcm _ hv3 (hlitlt _ hv3) _ sat3
    have hid : (sel (clauseStep φ j)).id = ⟨clauseStep φ j, (sel (clauseStep φ j)).id.index⟩ := by
      have := nodeId_eta (sel (clauseStep φ j)).id
      rw [hst] at this; exact this
    rw [hid]
    show (⟨clauseStep φ j, (sel (clauseStep φ j)).id.index⟩ : NodeId) = ⟨clauseStep φ j, rowOf _ _⟩
    simp only [rowOf, e1, e2, e3]
    rw [bits_row _ hr1 hr7]
  · rw [mapNodes_fusionTop φ _ h (by omega)] at hon
    rw [List.mem_singleton.mp hon]
    have h0' : ¬ (k < 0) := by simp only [fusionTop] at h; omega
    have h1' : ¬ (k < litBlock φ) := by simp only [fusionTop, litBlock] at h ⊢; omega
    have h2' : ¬ (k ≤ litBlock φ) := by simp only [fusionTop, litBlock] at h ⊢; omega
    simp only [selOfAssign, if_neg h0', if_neg h1', if_neg h2', if_pos h]

end

end AbsSat.GraphPath.Model.ConservationPrefix
