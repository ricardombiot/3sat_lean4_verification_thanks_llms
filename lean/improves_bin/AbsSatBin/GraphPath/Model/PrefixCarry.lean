-- lean/improves_bin/AbsSatBin/GraphPath/Model/PrefixCarry.lean
import AbsSatBin.GraphPath.Model.MapCert

/-!
# The machine carries every prefix that satisfies the clauses closed so far

`PureDriver.pureRun_carries` carries a **satisfying** assignment's branch through the whole run. `Sat`
enters in exactly one place (`CnfSelBin.pidOfAssign_not_prohibited`): the branch's window at the third
literal of a clause is not `000`. So the same proof carries, up to a step `T`, the branch of **any**
assignment whose windows before `T` are allowed (`PreSat φ a T`) — a partial solution.

* `chainSound_along_pre`: a state built along such a branch, up to `T`, holds its chain.
* `run_ok_pre`, `carries_pre`: the line at every step `t < T` holds, at the branch's map node, a state
  built along it — so the chain of the prefix is a certificate of that state (`cert_of_prefix`).

This is the routing tool for joins: a certificate of an earlier state that is a partial solution is
carried, by the machine itself, into the state of whatever key its own values lead to.
-/

namespace AbsSatBin.GraphPath.Model.PrefixCarry

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.Conservation
open AbsSatBin.GraphPath.Model.PureDriver

variable (φ : Cnf) (a : Assign)

/-- The branch's windows before `T` are allowed: the clauses closed before `T` are satisfied. -/
def PreSat (T : Int) : Prop := ∀ k, k < T → isProhibited φ (pidOfAssign φ a k) = false

theorem preSat_of_sat (hsat : Sat a φ) (T : Int) : PreSat φ a T :=
  fun k _ => pidOfAssign_not_prohibited φ a hsat k

theorem cs_upFiltering_le (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) : (upFiltering g reqs d title forb).current_step ≤ g.current_step + 1 := by
  by_cases hv : isValid (filterAll g reqs) = true
  · rw [current_step_upFiltering g reqs d title forb hv]; exact Int.le_refl _
  · have hpr := pruned_filterAll g reqs
    simp only [upFiltering, GPathM.up, hv, if_false, Bool.false_eq_true]
    rw [hpr.step_eq]; omega

theorem cs_upFiltering_ge (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String)
    (forb : PathNodeId → Bool) : g.current_step ≤ (upFiltering g reqs d title forb).current_step := by
  by_cases hv : isValid (filterAll g reqs) = true
  · rw [current_step_upFiltering g reqs d title forb hv]; omega
  · have hpr := pruned_filterAll g reqs
    simp only [upFiltering, GPathM.up, hv, if_false, Bool.false_eq_true]
    rw [hpr.step_eq]; exact Int.le_refl _

/-- **A state built along a prefix branch, up to `T`, holds the prefix's chain.** -/
theorem chainSound_along_pre (hbd : Bounded φ) (T : Int) (hwin : PreSat φ a T)
    (hzero : (0 : Int) < stepCount φ) (g : GPathM) (h : AlongAssign φ a g) (hT : g.current_step ≤ T) :
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
  | up g title hlo hhi hal ih =>
    have hTg : g.current_step ≤ T := Int.le_trans (cs_upFiltering_ge g _ _ title _) hT
    obtain ⟨sel, hsel, hids⟩ := ih hTg
    have hreach : Reachable (reqOf φ) (isProhibited φ) g :=
      reachable_of_mapReachable φ hbd g (mapReachable_of_alongAssign φ a hzero g hal)
    have hreqs : ∀ req ∈ reqOf φ (selOfAssign φ a g.current_step),
        0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req := by
      intro req hreq hr0 hr1
      rw [hids req.step hr0 hr1]
      exact reqSat_selOfAssign φ hbd a g.current_step req hreq
    have hpr := pruned_filterAll g (reqOf φ (selOfAssign φ a g.current_step))
    have hfil : ChainSound (filterAll g (reqOf φ (selOfAssign φ a g.current_step))) sel :=
      ChainSound_filterAll g _ sel hsel hreqs
    have hvalid : isValid (filterAll g (reqOf φ (selOfAssign φ a g.current_step))) = true :=
      PickInduction.isValid_of_ChainG _ sel hfil.chain
    have hlt : g.current_step < T := by
      have := current_step_upFiltering g (reqOf φ (selOfAssign φ a g.current_step))
        (selOfAssign φ a g.current_step) title (isProhibited φ) hvalid
      omega
    have hd : (selOfAssign φ a g.current_step).step
        = (filterAll g (reqOf φ (selOfAssign φ a g.current_step))).current_step := by
      rw [hpr.step_eq, selOfAssign_step]
    have hbelow := Certifies.nodes_below_of_pruned hpr
      (steps_below_current (reqOf φ) (isProhibited φ) hreach)
    have hmok := MachineOk_of_pruned hpr
      (Certifies.MachineOk_reachable (reqOf φ) (isProhibited φ) g hreach)
    have hf : isProhibited φ (extendPid (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) sel) = false := by
      have hpmp := ParentId.PMP_filterAll (reqOf φ) (isProhibited φ) g
        (reqOf φ (selOfAssign φ a g.current_step)) hreach
      have heq := extendPid_eq_pidOfAssign φ a _ sel hfil.chain.1 hpmp hsel.root_shape.1
        (by intro k hk0 hk; rw [hpr.step_eq] at hk; exact hids k hk0 hk) (by rw [hpr.step_eq]; exact hlo)
      rw [hpr.step_eq] at heq
      rw [heq]
      exact hwin _ hlt
    refine ⟨extend (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
      (selOfAssign φ a g.current_step) sel, ?_, ?_⟩
    · exact ChainSound_upFiltering g _ _ title _ hvalid hd hbelow hmok sel hsel hreqs hf
    · intro k hk0 hk
      rw [current_step_upFiltering g _ _ title _ hvalid] at hk
      if he : k = g.current_step then
        have hextend : extend (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
            (selOfAssign φ a g.current_step) sel g.current_step
            = extendPid (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
              (selOfAssign φ a g.current_step) sel := by
          simp only [extend, if_pos hpr.step_eq.symm]
        rw [he, hextend, extendPid_mapId]
      else
        rw [extend_below (filterAll g (reqOf φ (selOfAssign φ a g.current_step)))
          (selOfAssign φ a g.current_step) sel k (by rw [hpr.step_eq]; omega)]
        exact hids k hk0 (by omega)
  | joinL g₁ g₂ hok h₂ hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih (by have := (grown_join_left g₁ g₂).step_eq; omega)
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_left g₁ g₂).step_eq] at hk; exact hk)⟩
  | joinR g₁ g₂ hok h₁ hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih (by have := (grown_join_right g₁ g₂ hok).step_eq; omega)
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_right g₁ g₂ hok).step_eq] at hk; exact hk)⟩

theorem isValid_along_pre (hbd : Bounded φ) (T : Int) (hwin : PreSat φ a T)
    (hzero : (0 : Int) < stepCount φ) (g : GPathM) (h : AlongAssign φ a g) (hT : g.current_step ≤ T) :
    isValid g = true := by
  obtain ⟨sel, hsel, _⟩ := chainSound_along_pre φ a hbd T hwin hzero g h hT
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

theorem advance_target_pre (φ : Cnf) (a : Assign) (hwf : Bounded φ) (T : Int) (hwin : PreSat φ a T)
    (hzero : (0 : Int) < stepCount φ) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ) (hkT : k + 2 ≤ T)
    (g : GPathM) (hal : AlongAssign φ a g) (hcs : g.current_step = k + 1) :
    selOfAssign φ a (k + 1)
        ∈ sonsOfMap φ (selOfAssign φ a k)
      ∧ AlongAssign φ a (upFiltering g (reqOf φ (selOfAssign φ a (k + 1)))
          (selOfAssign φ a (k + 1)) "" (isProhibited φ))
      ∧ isValid (upFiltering g (reqOf φ (selOfAssign φ a (k + 1)))
          (selOfAssign φ a (k + 1)) "" (isProhibited φ)) = true := by
  have hson : selOfAssign φ a (k + 1)
      ∈ sonsOfMap φ (selOfAssign φ a k) := by
    exact selOfAssign_son φ a k h0 hk
  have hup : AlongAssign φ a (upFiltering g (reqOf φ (selOfAssign φ a (k + 1)))
      (selOfAssign φ a (k + 1)) "" (isProhibited φ)) := by
    have := AlongAssign.up (φ := φ) (a := a) g "" (by omega) (by omega) hal
    rwa [hcs] at this
  exact ⟨hson, hup, isValid_along_pre φ a hwf T hwin hzero _ hup
    (Int.le_trans (cs_upFiltering_le g _ _ _ _) (by omega))⟩

theorem sons_fold_establish_pre (φ : Cnf) (a : Assign) (hwf : Bounded φ) (T : Int) (hwin : PreSat φ a T)
    (hzero : (0 : Int) < stepCount φ) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ) (hkT : k + 2 ≤ T)
    (g : GPathM) (hal : AlongAssign φ a g) (hcs : g.current_step = k + 1)
    (hkv : StateOk φ k (selOfAssign φ a k, g)) :
    ∀ (l : List NodeId),
      (∀ d ∈ l, d ∈ sonsOfMap φ (selOfAssign φ a k)) →
      selOfAssign φ a (k + 1) ∈ l →
      ∀ acc, LineOk φ (k + 1) acc →
        LineOk φ (k + 1) (l.foldl (sendTo φ g) acc)
          ∧ Carries φ a (k + 1) (l.foldl (sendTo φ g) acc) := by
  obtain ⟨hson, hup, hval⟩ := advance_target_pre φ a hwf T hwin hzero k h0 hk hkT g hal hcs
  intro l
  induction l with
  | nil => intro _ hd; exact absurd hd List.not_mem_nil
  | cons x xs ih =>
    intro hx hd acc h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hd with rfl | hd'
    · have hsend : sendTo φ g acc (selOfAssign φ a (k + 1))
          = insertPure acc (selOfAssign φ a (k + 1))
              (upFiltering g (reqOf φ (selOfAssign φ a (k + 1)))
                (selOfAssign φ a (k + 1)) "" (isProhibited φ)) := by
        simp only [sendTo, hval, if_true]
      have hsok : StateOk φ (k + 1) (selOfAssign φ a (k + 1),
          upFiltering g (reqOf φ (selOfAssign φ a (k + 1)))
            (selOfAssign φ a (k + 1)) "" (isProhibited φ)) :=
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

theorem Carries_pureAdvance_pre (φ : Cnf) (a : Assign) (hwf : Bounded φ) (T : Int) (hwin : PreSat φ a T)
    (hzero : (0 : Int) < stepCount φ) (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ) (hkT : k + 2 ≤ T)
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
          exact sons_fold_establish_pre φ a hwf T hwin hzero k h0 hk hkT g hal hcs hkv _
            (fun _ hdm => hdm)
            (selOfAssign_son φ a k h0 hk)
            acc h
        exact outer_fold_mono φ a k xs (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) _
          hbase.1 hbase.2
      · exact ih (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) hd' _
          (LineOk_sendAll φ k x (hx x List.mem_cons_self) acc h)
  exact (main line hl.2 hmem [] ⟨by simp, by intro kv hkv'; exact absurd hkv' List.not_mem_nil⟩).2

theorem run_ok_pre (φ : Cnf) (a : Assign) (hwf : Bounded φ) (T : Int) (hwin : PreSat φ a T)
    (hzero : (0 : Int) < stepCount φ) :
    ∀ (n : Nat) (k : Int), 0 ≤ k → k + (n : Int) < stepCount φ → k + (n : Int) + 1 ≤ T →
      ∀ line, LineOk φ k line → Carries φ a k line →
        LineOk φ (k + (n : Int)) (pureSteps φ n line)
          ∧ Carries φ a (k + (n : Int)) (pureSteps φ n line) := by
  intro n
  induction n with
  | zero => intro k _ _ _ line hl hc; simpa using ⟨hl, hc⟩
  | succ m ih =>
    intro k h0 hk hkT line hl hc
    have heq : k + ((m + 1 : Nat) : Int) = (k + 1) + (m : Int) := by omega
    rw [heq]
    simp only [pureSteps]
    exact ih (k + 1) (by omega) (by omega) (by omega) _
      (LineOk_pureAdvance φ k line hl)
      (Carries_pureAdvance_pre φ a hwf T hwin hzero k h0 (by omega) (by omega) line hl hc)

/-- **The line at step `t < T` carries the prefix branch.** -/
theorem carries_pre (hbd : Bounded φ) (T : Int) (hwin : PreSat φ a T) (hzero : (0 : Int) < stepCount φ)
    (n : Nat) (hn : (n : Int) < stepCount φ) (hnT : (n : Int) + 1 ≤ T) :
    LineOk φ n (pureSteps φ n (pureInit φ)) ∧ Carries φ a n (pureSteps φ n (pureInit φ)) := by
  obtain ⟨hl0, hc0⟩ := init_ok φ a hzero
  have h := run_ok_pre φ a hbd T hwin hzero n 0 (by omega) (by omega) (by omega) (pureInit φ) hl0 hc0
  simpa using h

/-- **The prefix's chain is a certificate of the state at its map node**, at every step `t < T`. -/
theorem cert_of_prefix (hbd : Bounded φ) (T : Int) (hwin : PreSat φ a T) (hzero : (0 : Int) < stepCount φ)
    (n : Nat) (hn : (n : Int) < stepCount φ) (hnT : (n : Int) + 1 ≤ T) :
    ∃ g, (selOfAssign φ a n, g) ∈ pureSteps φ n (pureInit φ) ∧ g.current_step = n + 1 ∧
      ∃ sel, ChainSound g sel ∧ ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k := by
  obtain ⟨_, g, hmem, hal, hcs⟩ := carries_pre φ a hbd T hwin hzero n hn hnT
  exact ⟨g, hmem, hcs, chainSound_along_pre φ a hbd T hwin hzero g hal (by rw [hcs]; exact hnT)⟩

/-- info: 'AbsSatBin.GraphPath.Model.PrefixCarry.cert_of_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cert_of_prefix

end AbsSatBin.GraphPath.Model.PrefixCarry
