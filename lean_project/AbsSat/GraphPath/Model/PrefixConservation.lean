-- lean_project/AbsSat/GraphPath/Model/PrefixConservation.lean
import AbsSat.GraphPath.Model.PureDriver
import AbsSat.GraphPath.Model.Decision

/-!
# Conservation, by prefix

`Conservation.chainSound_along` keeps every **full** solution: along a
satisfying assignment's branch, its chain survives every state. The clause
filter's core (`ClauseFilter.FlipCore`) talks about states in the *middle* of a
run, where the right notion is not "satisfies φ" but "satisfies the clauses
seen so far". This module proves the law in that form.

The observation that makes it short: in the full law, satisfaction of the whole
formula is used in exactly one place — to know that the node the assignment
names at each step **exists on the map** (`selOfAssign_onMap`). And that only
depends on the clause *at that step*. So:

* `selOfAssign_onMap_of` — the named node is on the map as soon as the clause
  at that step (if any) is satisfied;
* `SatUpTo φ a K` — `a` satisfies every clause at a step `≤ K`;
* `chainSound_along_prefix` — along `a`'s branch, **as long as the run stays
  at or below step `K`**, `a`'s chain is a sound chain of every state, and the
  states are machine states (`MapReachable`). Validity again comes free from
  the chain.
-/

namespace AbsSat.GraphPath.Model.PrefixConservation

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.Conservation

/-- `a` satisfies every clause the machine has seen by step `K`. -/
def SatUpTo (φ : Cnf) (a : Assign) (K : Int) : Prop :=
  ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → clauseStep φ j ≤ K → SatClause a c

theorem satUpTo_of_sat (φ : Cnf) (a : Assign) (h : Sat a φ) (K : Int) : SatUpTo φ a K :=
  fun _ c hj _ => h c (List.mem_of_getElem? hj)

/-- **The named node is on the map as soon as the clause at its step is
satisfied** — `selOfAssign_onMap` with the whole formula replaced by one clause. -/
theorem selOfAssign_onMap_of (φ : Cnf) (a : Assign) (k : Int) (h0 : 0 ≤ k)
    (hk : k < stepCount φ)
    (hcl : ∀ (j : Nat) (c : Clause), φ.clauses[j]? = some c → clauseStep φ j = k → SatClause a c) :
    selOfAssign φ a k ∈ mapNodes φ k := by
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
    have hrlo := rowOf_pos a φ.clauses[j] (hcl j _ hj rfl)
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

/-- Up to step `K`, every node the assignment names is on the map. -/
theorem onMap_upTo (φ : Cnf) (a : Assign) (K : Int) (hs : SatUpTo φ a K) (k : Int)
    (h0 : 0 ≤ k) (hkK : k ≤ K) (hk : k < stepCount φ) : selOfAssign φ a k ∈ mapNodes φ k :=
  selOfAssign_onMap_of φ a k h0 hk (fun j c hj hjk => hs j c hj (by rw [hjk]; exact hkK))

/-- `upFiltering` never lowers the step. -/
theorem current_le_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String) :
    g.current_step ≤ (upFiltering g reqs d title).current_step := by
  unfold GPathM.upFiltering GPathM.up
  cases hv : isValid (filterAll g reqs) with
  | true =>
    rw [if_pos rfl]
    show g.current_step ≤ (filterAll g reqs).current_step + 1
    rw [(pruned_filterAll g reqs).step_eq]; omega
  | false => rw [if_neg Bool.false_ne_true, (pruned_filterAll g reqs).step_eq]; exact Int.le_refl _

/-- **Conservation, by prefix.** Along `a`'s branch, while the run has not gone
past step `K`, every state is a machine state and carries `a`'s chain — for any
`a` that satisfies the clauses seen by step `K`. -/
theorem chainSound_along_prefix (φ : Cnf) (a : Assign) (hwf : WF φ) (K : Int)
    (hs : SatUpTo φ a K) (g : GPathM) (h : AlongAssign φ a g) :
    g.current_step ≤ K + 1 →
      MapReachable φ g ∧ ∃ sel, ChainSound g sel ∧
        ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k := by
  induction h with
  | seed title =>
    intro hle
    rw [initSeed_current] at hle
    have h0K : 0 ≤ K := by omega
    have hsc : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
    have hon0 := onMap_upTo φ a K hs 0 (Int.le_refl 0) h0K hsc
    refine ⟨MapReachable.seed _ title (selOfAssign_step φ a 0)
      (by rw [selOfAssign_step]; exact hon0), ?_⟩
    refine ⟨fun _ => { id := selOfAssign φ a 0, parent_id := none }, ?_, ?_⟩
    · exact ChainSound_initSeed _ title (selOfAssign_step φ a 0)
    · intro k hlo hhi
      rw [initSeed_current] at hhi
      have : k = 0 := by omega
      subst this
      rfl
  | up g title hlo hhi hal ih =>
    intro hle
    have hgle : g.current_step ≤ K + 1 :=
      Int.le_trans (current_le_upFiltering g _ _ title) hle
    obtain ⟨hmr, sel, hsel, hids⟩ := ih hgle
    have hreach : Reachable (reqOfCnf φ) g := reachable_of_mapReachable φ hwf g hmr
    have hreqs : ∀ req ∈ reqOfCnf φ (selOfAssign φ a g.current_step),
        0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req := by
      intro req hreq hr0 hr1
      rw [hids req.step hr0 hr1]
      exact reqSat_selOfAssign φ hwf a g.current_step req hreq
    have hpr := pruned_filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step))
    have hfil : ChainSound (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step))) sel :=
      ChainSound_filterAll g _ sel hsel hreqs
    have hvalid : isValid (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
        = true := PickInduction.isValid_of_ChainG _ sel hfil.chain
    have hshape : upFiltering g (reqOfCnf φ (selOfAssign φ a g.current_step))
        (selOfAssign φ a g.current_step) title
        = addNode (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
          (selOfAssign φ a g.current_step) title := by
      simp only [upFiltering, GPathM.up, hvalid, if_pos]
    -- the chain made the filter valid, so the run did go up a step: `g` is at most at `K`
    have hgK : g.current_step ≤ K := by
      rw [hshape, addNode_current, hpr.step_eq] at hle; omega
    have hon : selOfAssign φ a g.current_step ∈ mapNodes φ g.current_step :=
      onMap_upTo φ a K hs _ hlo hgK hhi
    refine ⟨MapReachable.up g _ title (selOfAssign_step φ a g.current_step)
      (by rw [selOfAssign_step]; exact hon) hmr, ?_⟩
    have hd : (selOfAssign φ a g.current_step).step
        = (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step))).current_step := by
      rw [hpr.step_eq, selOfAssign_step]
    have hbelow := Certifies.nodes_below_of_pruned hpr (steps_below_current (reqOfCnf φ) hreach)
    have hmok := MachineOk_of_pruned hpr (Certifies.MachineOk_reachable (reqOfCnf φ) g hreach)
    refine ⟨extend (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
      (selOfAssign φ a g.current_step) sel, ?_, ?_⟩
    · exact ChainSound_upFiltering g _ _ title hvalid hd hbelow hmok sel hsel hreqs
    · intro k hk0 hk
      rw [hshape, addNode_current] at hk
      rw [hpr.step_eq] at hk
      if he : k = g.current_step then
        have hextend : extend (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
            (selOfAssign φ a g.current_step) sel g.current_step
            = newPid (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
              (selOfAssign φ a g.current_step) := by
          simp only [extend, if_pos hpr.step_eq.symm]
        rw [he, hextend]
        rfl
      else
        rw [extend_below (filterAll g (reqOfCnf φ (selOfAssign φ a g.current_step)))
          (selOfAssign φ a g.current_step) sel k (by rw [hpr.step_eq]; omega)]
        exact hids k hk0 (by omega)
  | joinL g₁ g₂ hok h₂ hal ih =>
    intro hle
    have hcs : (GPathM.join g₁ g₂).current_step = g₁.current_step :=
      (grown_join_left g₁ g₂).step_eq
    obtain ⟨hmr, sel, hsel, hids⟩ := ih (by rw [← hcs]; exact hle)
    exact ⟨MapReachable.join g₁ g₂ hok hmr h₂, sel, ChainSound_join_left g₁ g₂ sel hsel,
      fun k hk0 hk => hids k hk0 (by rw [hcs] at hk; exact hk)⟩
  | joinR g₁ g₂ hok h₁ hal ih =>
    intro hle
    have hcs : (GPathM.join g₁ g₂).current_step = g₂.current_step :=
      (grown_join_right g₁ g₂ hok).step_eq
    obtain ⟨hmr, sel, hsel, hids⟩ := ih (by rw [← hcs]; exact hle)
    exact ⟨MapReachable.join g₁ g₂ hok h₁ hmr, sel, ChainSound_join_right g₁ g₂ hok sel hsel,
      fun k hk0 hk => hids k hk0 (by rw [hcs] at hk; exact hk)⟩

/-- info: 'AbsSat.GraphPath.Model.PrefixConservation.chainSound_along_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_along_prefix


-- ============================================================
-- In the driver: the state at the assignment's key carries it
-- ============================================================

open AbsSat.GraphPath.Model.PureDriver

/-- `selOfAssign_son`, needing only the next node on the map. -/
theorem selOfAssign_son_of (φ : Cnf) (a : Assign) (k : Int) (h0 : 0 ≤ k)
    (hon : selOfAssign φ a (k + 1) ∈ mapNodes φ (k + 1)) :
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
    exact hon

theorem upFiltering_current_le (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String) :
    (upFiltering g reqs d title).current_step ≤ g.current_step + 1 := by
  unfold GPathM.upFiltering GPathM.up
  cases hv : isValid (filterAll g reqs) with
  | true =>
    rw [if_pos rfl]
    show (filterAll g reqs).current_step + 1 ≤ g.current_step + 1
    rw [(pruned_filterAll g reqs).step_eq]; exact Int.le_refl _
  | false =>
    rw [if_neg Bool.false_ne_true, (pruned_filterAll g reqs).step_eq]; omega

theorem isValid_along_prefix (φ : Cnf) (a : Assign) (hwf : WF φ) (K : Int)
    (hs : SatUpTo φ a K) (g : GPathM) (h : AlongAssign φ a g) (hle : g.current_step ≤ K + 1) :
    isValid g = true := by
  obtain ⟨_, sel, hsel, _⟩ := chainSound_along_prefix φ a hwf K hs g h hle
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

theorem advance_target_prefix (φ : Cnf) (a : Assign) (hwf : WF φ) (K : Int) (hs : SatUpTo φ a K)
    (k : Int) (h0 : 0 ≤ k) (hkK : k + 1 ≤ K) (hk : k + 1 < stepCount φ)
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
    exact selOfAssign_son_of φ a k h0 (onMap_upTo φ a K hs (k + 1) (by omega) hkK hk)
  have hup : AlongAssign φ a (upFiltering g (reqOfCnf φ (selOfAssign φ a (k + 1)))
      (selOfAssign φ a (k + 1)) "") := by
    have := AlongAssign.up (φ := φ) (a := a) g "" (by omega) (by omega) hal
    rwa [hcs] at this
  refine ⟨hson, hup, isValid_along_prefix φ a hwf K hs _ hup ?_⟩
  have := upFiltering_current_le g (reqOfCnf φ (selOfAssign φ a (k + 1)))
    (selOfAssign φ a (k + 1)) ""
  omega

theorem sons_fold_establish_prefix (φ : Cnf) (a : Assign) (hwf : WF φ) (K : Int)
    (hs : SatUpTo φ a K) (k : Int) (h0 : 0 ≤ k) (hkK : k + 1 ≤ K) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssign φ a g) (hcs : g.current_step = k + 1)
    (hkv : StateOk φ k (selOfAssign φ a k, g)) :
    ∀ (l : List NodeId),
      (∀ d ∈ l, d ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index) →
      selOfAssign φ a (k + 1) ∈ l →
      ∀ acc, LineOk φ (k + 1) acc →
        LineOk φ (k + 1) (l.foldl (sendTo φ g) acc)
          ∧ Carries φ a (k + 1) (l.foldl (sendTo φ g) acc) := by
  obtain ⟨hson, hup, hval⟩ := advance_target_prefix φ a hwf K hs k h0 hkK hk g hal hcs
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

theorem Carries_pureAdvance_prefix (φ : Cnf) (a : Assign) (hwf : WF φ) (K : Int)
    (hs : SatUpTo φ a K) (k : Int) (h0 : 0 ≤ k) (hkK : k + 1 ≤ K) (hk : k + 1 < stepCount φ)
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
          exact sons_fold_establish_prefix φ a hwf K hs k h0 hkK hk g hal hcs hkv _
            (fun _ hdm => hdm)
            (by
              rw [selOfAssign_step]
              exact selOfAssign_son_of φ a k h0
                (onMap_upTo φ a K hs (k + 1) (by omega) hkK hk))
            acc h
        exact PureDriver.outer_fold_mono φ a k xs
          (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) _ hbase.1 hbase.2
      · exact ih (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) hd' _
          (LineOk_sendAll φ k x (hx x List.mem_cons_self) acc h)
  exact (main line hl.2 hmem [] ⟨by simp, by intro kv hkv'; exact absurd hkv' List.not_mem_nil⟩).2

theorem Carries_pureInit_prefix (φ : Cnf) (a : Assign) (K : Int) (hs : SatUpTo φ a K)
    (hK : 0 ≤ K) (hzero : (0 : Int) < stepCount φ) : Carries φ a 0 (pureInit φ) := by
  have hsel : selOfAssign φ a 0 ∈ mapNodes φ 0 := onMap_upTo φ a K hs 0 (Int.le_refl 0) hK hzero
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
        Carries φ a 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact (mono xs (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
          (LineOk_insertPure φ 0 acc _ _ h (stateOk_initSeed φ _ hsel))
          (Carries_of_insertPure_at φ a 0 acc _ h (stateOk_initSeed φ _ hsel)
            (AlongAssign.seed ""))).2
      · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
          (LineOk_insertPure φ 0 acc x _ h (stateOk_initSeed φ x (hx x List.mem_cons_self)))
  exact main _ (fun _ hdm => hdm) hsel [] ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem pureSteps_succ (φ : Cnf) :
    ∀ (m : Nat) (line : PureLine),
      pureSteps φ (m + 1) line = pureAdvance φ (pureSteps φ m line) := by
  intro m
  induction m with
  | zero => intro line; rfl
  | succ n ih =>
    intro line
    show pureSteps φ (n + 1) (pureAdvance φ line) = pureAdvance φ (pureSteps φ (n + 1) line)
    rw [ih (pureAdvance φ line)]
    rfl

/-- **The driver conserves every prefix solution.** After `k` steps, for every
assignment satisfying the clauses seen by step `k`, the line has an entry at
that assignment's node for step `k`, built along its branch — and that state
carries the assignment's chain. -/
theorem pureSteps_carries_prefix (φ : Cnf) (a : Assign) (hwf : WF φ) (k : Nat)
    (hk : (k : Int) < stepCount φ) (hs : SatUpTo φ a k) :
    ∃ g, (selOfAssign φ a k, g) ∈ pureSteps φ k (pureInit φ)
      ∧ g.current_step = (k : Int) + 1
      ∧ ∃ sel, ChainSound g sel ∧
          ∀ j, 0 ≤ j → j < g.current_step → (sel j).id = selOfAssign φ a j := by
  have hzero : (0 : Int) < stepCount φ := by omega
  -- carry the branch step by step, staying below `k`
  have run : ∀ (n : Nat), n ≤ k →
      LineOk φ n (pureSteps φ n (pureInit φ)) ∧ Carries φ a n (pureSteps φ n (pureInit φ)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨Decision.LineOk_pureInit φ,
        Carries_pureInit_prefix φ a k hs (by omega) hzero⟩
    | succ m ih =>
      intro hm
      obtain ⟨hl, hc⟩ := ih (by omega)
      have hstep : pureSteps φ (m + 1) (pureInit φ) = pureAdvance φ (pureSteps φ m (pureInit φ)) :=
        pureSteps_succ φ m (pureInit φ)
      rw [hstep]
      have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by omega
      rw [hcast]
      exact ⟨LineOk_pureAdvance φ m _ hl,
        Carries_pureAdvance_prefix φ a hwf k hs m (by omega) (by omega) (by omega) _ hl hc⟩
  obtain ⟨_, g, hmem, hal, hcs⟩ := run k (Nat.le_refl k)
  obtain ⟨_, sel, hsel, hids⟩ :=
    chainSound_along_prefix φ a hwf k hs g hal (by rw [hcs]; omega)
  exact ⟨g, hmem, hcs, sel, hsel, hids⟩

/-- info: 'AbsSat.GraphPath.Model.PrefixConservation.pureSteps_carries_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureSteps_carries_prefix

end AbsSat.GraphPath.Model.PrefixConservation
