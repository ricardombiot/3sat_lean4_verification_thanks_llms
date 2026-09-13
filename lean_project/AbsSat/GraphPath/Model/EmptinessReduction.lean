-- lean_project/AbsSat/GraphPath/Model/EmptinessReduction.lean
import AbsSat.GraphPath.Model.SubsetSemantics
import AbsSat.GraphPath.Model.PartialPaths
import AbsSat.GraphPath.Model.KeyBranching
import AbsSat.SatMachine.PureProofs

/-!
# The emptiness test, reduced to one obligation per send

`SubsetSemantics` shows the operations are exact on subsets of partial paths: the
filter intersects, `up` extends, `join` holds the union. What the machine does not do
is look at the subset: it keeps a state when `isValid` holds on its owner tables.

* `isValid_of_denotS` — the easy direction: a non-empty subset makes the state valid.
* `SendExact φ` — the obligation, one send at a time: if a send's filter is valid, some
  path of the source subset goes through every pin. It asks for **one** path, not that
  every node lie on a chain, so it is weaker than `ClauseStepExact`.
* `lineAt_nonempty` — under `SendExact`, every state of every line of the driver holds
  a non-empty subset: seeds do, a kept send does (the obligation plus
  `denotS_upFiltering`), and a merge keeps its left part (`denotS_join_of_left`).
* `valid_iff_nonempty_of_SendExact` — so on the driver's lines, valid ⇔ non-empty.
* `soundness_of_SendExact`, `run_pure_decides_of_SendExact` — and the machine decides
  3SAT.

This is a sufficient condition, not an equivalence: the machine could be correct
without every single send being exact.
-/

namespace AbsSat.GraphPath.Model.EmptinessReduction

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.SubsetSemantics
open AbsSat.GraphPath.Model.PartialPaths
open AbsSat.SatMachine.PureSatMachine

/-- **The easy direction.** A state holding some path is valid: a sound chain puts a
global owner at every step. -/
theorem isValid_of_denotS (g : GPathM) (p : List NodeId) (h : denotS g p) : isValid g = true := by
  obtain ⟨sel, hs, _⟩ := h
  obtain ⟨hchain, _, hgow⟩ := hs.chain
  simp only [isValid, List.all_eq_true]
  intro k hk
  have h0 := mem_intRange_lower hk
  have h1 := mem_intRange_upper hk
  exact hasStepEntry_of_mem _ (sel k) k (hgow k h0 (by omega)) (hchain.1 k h0 (by omega)).2

/-- **The obligation, one send at a time.** Whenever a send's filter is valid, some
path of the (non-empty) source subset goes through every pin. -/
def SendExact (φ : Cnf) : Prop :=
  ∀ (g : GPathM) (d : NodeId), MapReachable φ g → isValid g = true → (∃ p, denotS g p) →
    d.step = g.current_step → d ∈ mapNodes φ d.step →
    isValid (filterAll g (reqOfCnf φ d)) = true →
    ∃ p, denotS g p ∧ ∀ req ∈ reqOfCnf φ d, 0 ≤ req.step → req.step < g.current_step → req ∈ p

theorem nonempty_insertPure (acc : PureLine) (key : NodeId) (g : GPathM)
    (hacc : ∀ kv ∈ acc, ∃ p, denotS kv.2 p) (hg : ∃ p, denotS g p) :
    ∀ kv ∈ insertPure acc key g, ∃ p, denotS kv.2 p := by
  intro kv hkv
  rcases KeyBranching.mem_insertPure_cases acc key g kv hkv with h | h | ⟨x, hx, _, h⟩
  · exact hacc kv h
  · rw [h]; exact hg
  · rw [h]
    obtain ⟨p, hp⟩ := hacc x hx
    refine ⟨p, ?_⟩
    show denotS (doJoin x.2 g) p
    unfold doJoin
    split
    · exact denotS_join_of_left x.2 g p hp
    · exact hp

theorem pureInit_nonempty (φ : Cnf) : ∀ kv ∈ pureInit φ, ∃ p, denotS kv.2 p := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d.step = 0) → ∀ acc : PureLine,
      (∀ kv ∈ acc, ∃ p, denotS kv.2 p) →
      ∀ kv ∈ l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc,
        ∃ p, denotS kv.2 p := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (nonempty_insertPure acc x _ h ⟨_, _, ChainSound_initSeed x "" (hx x List.mem_cons_self), rfl⟩)
  exact main _ (fun d hd => mapNodes_step φ 0 d hd) [] (fun _ h => absurd h List.not_mem_nil)

theorem sendTo_nonempty (φ : Cnf) (hwf : WF φ) (hex : SendExact φ) (k : Int)
    (kv : NodeId × GPathM) (hkv : StateOk φ k kv) (hne : ∃ p, denotS kv.2 p)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (next : PureLine) (hn : ∀ e ∈ next, ∃ p, denotS e.2 p) :
    ∀ e ∈ sendTo φ kv.2 next d, ∃ p, denotS e.2 p := by
  simp only [sendTo]
  split
  · next hval =>
    apply nonempty_insertPure next d _ hn
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
    have hdcs : d.step = kv.2.current_step := by rw [hdstep, hkv.step]
    obtain ⟨p, hp, hthrough⟩ :=
      hex kv.2 d hkv.reach hkv.valid hne hdcs (by rw [hdstep]; exact hd') hfv
    exact ⟨d :: p, (denotS_upFiltering (reqOfCnf φ) kv.2 (reachable_of_mapReachable φ hwf kv.2 hkv.reach)
      (reqOfCnf φ d) d "" hfv hdcs (d :: p)).mpr ⟨p, rfl, hp, hthrough⟩⟩
  · exact hn

theorem sendAll_nonempty (φ : Cnf) (hwf : WF φ) (hex : SendExact φ) (k : Int)
    (kv : NodeId × GPathM) (hkv : StateOk φ k kv) (hne : ∃ p, denotS kv.2 p)
    (acc : PureLine) (hacc : ∀ e ∈ acc, ∃ p, denotS e.2 p) :
    ∀ e ∈ sendAll φ kv acc, ∃ p, denotS e.2 p := by
  simp only [sendAll]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc : PureLine, (∀ e ∈ acc, ∃ p, denotS e.2 p) →
        ∀ e ∈ l.foldl (sendTo φ kv.2) acc, ∃ p, denotS e.2 p := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (sendTo_nonempty φ hwf hex k kv hkv hne x (hx x List.mem_cons_self) acc h)
  exact main _ (fun _ hd => hd) acc hacc

theorem pureAdvance_nonempty (φ : Cnf) (hwf : WF φ) (hex : SendExact φ) (k : Int)
    (line : PureLine) (hl : LineOk φ k line) (hne : ∀ kv ∈ line, ∃ p, denotS kv.2 p) :
    ∀ e ∈ pureAdvance φ line, ∃ p, denotS e.2 p := by
  simp only [pureAdvance]
  have main : ∀ (l : PureLine), (∀ kv ∈ l, kv ∈ line) → ∀ acc : PureLine,
      (∀ e ∈ acc, ∃ p, denotS e.2 p) →
        ∀ e ∈ l.foldl (fun next kv => sendAll φ kv next) acc, ∃ p, denotS e.2 p := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hxm := hx x List.mem_cons_self
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (sendAll_nonempty φ hwf hex k x (hl.2 x hxm) (hne x hxm) acc h)
  exact main line (fun _ h => h) [] (fun e he => absurd he List.not_mem_nil)

/-- **Under `SendExact`, every state the driver keeps holds a non-empty subset.** -/
theorem lineAt_nonempty (φ : Cnf) (hwf : WF φ) (hex : SendExact φ) :
    ∀ (k : Nat), ∀ kv ∈ lineAt φ k, ∃ p, denotS kv.2 p := by
  intro k
  induction k with
  | zero => exact pureInit_nonempty φ
  | succ k ih =>
    intro kv hkv
    have hkv' : kv ∈ pureAdvance φ (lineAt φ k) := by
      simpa [lineAt, AbsSat.SatMachine.PureProofs.pureSteps_succ'] using hkv
    exact pureAdvance_nonempty φ hwf hex k _ (lineAt_ok φ k) ih kv hkv'

/-- **On the driver's lines, valid ⇔ non-empty**, under `SendExact`. -/
theorem valid_iff_nonempty_of_SendExact (φ : Cnf) (hwf : WF φ) (hex : SendExact φ) (k : Nat)
    (kv : NodeId × GPathM) (hkv : kv ∈ lineAt φ k) :
    isValid kv.2 = true ↔ ∃ p, denotS kv.2 p :=
  ⟨fun _ => lineAt_nonempty φ hwf hex k kv hkv, fun ⟨p, hp⟩ => isValid_of_denotS kv.2 p hp⟩

/-- **`SendExact` makes the machine sound.** -/
theorem soundness_of_SendExact (φ : Cnf) (hwf : WF φ) (hex : SendExact φ)
    (h : pureRun φ ≠ []) : Satisfiable φ := by
  obtain ⟨kv, hkv⟩ := List.exists_mem_of_ne_nil _ h
  have hkv' : kv ∈ lineAt φ (stepCount φ - 1).toNat := hkv
  obtain ⟨p, sel, hs, hp⟩ := lineAt_nonempty φ hwf hex _ kv hkv'
  obtain ⟨hchain, howned, _⟩ := hs.chain
  exact (satisfiable_iff_Phi_nonempty φ hwf).mpr ⟨p, kv, hkv, sel, hchain, howned, hp⟩

/-- **`SendExact` makes the machine decide 3SAT.** -/
theorem run_pure_decides_of_SendExact (φ : Cnf) (hwf : WF φ) (hex : SendExact φ) :
    is_satisfiable (run_pure φ) = true ↔ Satisfiable φ :=
  ⟨fun h => soundness_of_SendExact φ hwf hex ((AbsSat.SatMachine.PureProofs.is_satisfiable_run_pure_iff φ).mp h),
   AbsSat.SatMachine.PureProofs.completeness_pure φ hwf⟩

/-- info: 'AbsSat.GraphPath.Model.EmptinessReduction.isValid_of_denotS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_of_denotS

/-- info: 'AbsSat.GraphPath.Model.EmptinessReduction.lineAt_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lineAt_nonempty

/-- info: 'AbsSat.GraphPath.Model.EmptinessReduction.valid_iff_nonempty_of_SendExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms valid_iff_nonempty_of_SendExact

/-- info: 'AbsSat.GraphPath.Model.EmptinessReduction.soundness_of_SendExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundness_of_SendExact

/-- info: 'AbsSat.GraphPath.Model.EmptinessReduction.run_pure_decides_of_SendExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_pure_decides_of_SendExact

end AbsSat.GraphPath.Model.EmptinessReduction
