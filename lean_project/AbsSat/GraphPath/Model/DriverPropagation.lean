-- lean_project/AbsSat/GraphPath/Model/DriverPropagation.lean
import AbsSat.GraphPath.Model.UnitPropagation
import AbsSat.GraphPath.Model.PureDriver

/-!
# The driver never carries a branch that unit propagation refutes

`UnitPropagation.invalid_filterAll_of_UPConflict` is about one filter. This module
reads it at the level of the driver (`PureDriver`, which `SatMachinePure` runs step
by step — `run_pure_eq_driver`).

When a state is sent to a map node `d`, `upFiltering` first applies `filterAll` with
`d`'s requirements. If unit propagation from those pins reaches a conflict, that
filter is invalid, `up` does not add the node, and `sendTo` keeps only valid results:

* `sendTo_of_refuted` — a refuted send leaves the next line exactly as it was;
* `pureAdvance_origin` — in the clause block, every entry of the next line was sent,
  from some state of the current line, by a send unit propagation does not refute.

The clause block is required: below it, variables the state has not reached yet have
no owners, and propagation would report conflicts that are not there.
-/

namespace AbsSat.GraphPath.Model.DriverPropagation

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.UnitPropagation

/-- Sending `g` to `d` is refuted: unit propagation from the pins `d` imposes, over
the clauses `g` has seen, reaches a conflict. -/
def SendRefuted (φ : Cnf) (g : GPathM) (d : NodeId) : Prop :=
  UPConflict φ (Present ((reqOfCnf φ d).foldl filterRequire g)) g.current_step

theorem upFiltering_invalid_of_refuted (φ : Cnf) (hwf : WF φ) (g : GPathM)
    (hmr : MapReachable φ g) (hlit : litBlock φ < g.current_step) (d : NodeId) (title : String)
    (h : SendRefuted φ g d) : isValid (upFiltering g (reqOfCnf φ d) d title) = false := by
  have hinv := invalid_filterAll_of_UPConflict φ hwf g hmr (reqOfCnf φ d) hlit h
  simp only [upFiltering, GPathM.up, hinv, Bool.false_eq_true, ↓reduceIte]

/-- **The driver drops a refuted branch.** If unit propagation refutes sending `g`
to `d`, the send leaves the next line unchanged. -/
theorem sendTo_of_refuted (φ : Cnf) (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g)
    (hlit : litBlock φ < g.current_step) (next : PureLine) (d : NodeId)
    (h : SendRefuted φ g d) : sendTo φ g next d = next := by
  have hup := upFiltering_invalid_of_refuted φ hwf g hmr hlit d "" h
  simp only [sendTo, hup, Bool.false_eq_true, ↓reduceIte]

/-- Some state of `line` sends to `key`, and unit propagation does not refute that
send. -/
def HasUnrefutedOrigin (φ : Cnf) (line : PureLine) (key : NodeId) : Prop :=
  ∃ kv ∈ line, key ∈ mapSons φ kv.1.step kv.1.index ∧ ¬ SendRefuted φ kv.2 key

theorem insertPure_key_mem (acc : PureLine) (key : NodeId) (g : GPathM)
    (e : NodeId × GPathM) (he : e ∈ insertPure acc key g) :
    (∃ e0 ∈ acc, e0.1 = e.1) ∨ e.1 = key := by
  have hk : e.1 ∈ (insertPure acc key g).map (·.1) := List.mem_map.mpr ⟨e, he, rfl⟩
  cases hf : acc.find? (fun x => x.1 == key) with
  | none =>
    rw [insertPure_keys_none acc key g hf] at hk
    rcases List.mem_append.mp hk with h | h
    · obtain ⟨e0, he0, h0⟩ := List.mem_map.mp h
      exact Or.inl ⟨e0, he0, h0⟩
    · exact Or.inr (List.mem_singleton.mp h)
  | some e1 =>
    rw [insertPure_keys_some acc key g e1 hf] at hk
    obtain ⟨e0, he0, h0⟩ := List.mem_map.mp hk
    exact Or.inl ⟨e0, he0, h0⟩

theorem sendTo_origin (φ : Cnf) (hwf : WF φ) (line : PureLine) (kv : NodeId × GPathM)
    (hkvmem : kv ∈ line) (hmr : MapReachable φ kv.2) (hlit : litBlock φ < kv.2.current_step)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (acc : PureLine) (hacc : ∀ e ∈ acc, HasUnrefutedOrigin φ line e.1) :
    ∀ e ∈ sendTo φ kv.2 acc d, HasUnrefutedOrigin φ line e.1 := by
  intro e he
  simp only [sendTo] at he
  split at he
  · next hval =>
    rcases insertPure_key_mem acc d _ e he with ⟨e0, he0, h0⟩ | hkey
    · rw [← h0]; exact hacc e0 he0
    · rw [hkey]
      refine ⟨kv, hkvmem, hd, fun href => ?_⟩
      have hinv := upFiltering_invalid_of_refuted φ hwf kv.2 hmr hlit d "" href
      rw [hinv] at hval
      exact Bool.false_ne_true hval
  · exact hacc e he

theorem sendAll_origin (φ : Cnf) (hwf : WF φ) (line : PureLine) (kv : NodeId × GPathM)
    (hkvmem : kv ∈ line) (hmr : MapReachable φ kv.2) (hlit : litBlock φ < kv.2.current_step)
    (acc : PureLine) (hacc : ∀ e ∈ acc, HasUnrefutedOrigin φ line e.1) :
    ∀ e ∈ sendAll φ kv acc, HasUnrefutedOrigin φ line e.1 := by
  simp only [sendAll]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, (∀ e ∈ acc, HasUnrefutedOrigin φ line e.1) →
        ∀ e ∈ l.foldl (sendTo φ kv.2) acc, HasUnrefutedOrigin φ line e.1 := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (sendTo_origin φ hwf line kv hkvmem hmr hlit x (hx x List.mem_cons_self) acc h)
  exact main _ (fun _ hd => hd) acc hacc

/-- **The driver never carries a branch that unit propagation refutes.** In the
clause block, every entry of the next line was sent to its key by some state of the
current line, through a send that unit propagation does not refute. -/
theorem pureAdvance_origin (φ : Cnf) (hwf : WF φ) (k : Int) (line : PureLine)
    (hl : LineOk φ k line) (hk : litBlock φ ≤ k) :
    ∀ e ∈ pureAdvance φ line, HasUnrefutedOrigin φ line e.1 := by
  simp only [pureAdvance]
  have main : ∀ (l : PureLine), (∀ kv ∈ l, kv ∈ line) →
      ∀ acc, (∀ e ∈ acc, HasUnrefutedOrigin φ line e.1) →
        ∀ e ∈ l.foldl (fun next kv => sendAll φ kv next) acc, HasUnrefutedOrigin φ line e.1 := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hxm := hx x List.mem_cons_self
      have hok := hl.2 x hxm
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (sendAll_origin φ hwf line x hxm hok.reach (by rw [hok.step]; omega) acc h)
  exact main line (fun _ h => h) [] (fun e he => absurd he List.not_mem_nil)

/-- info: 'AbsSat.GraphPath.Model.DriverPropagation.sendTo_of_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sendTo_of_refuted

/-- info: 'AbsSat.GraphPath.Model.DriverPropagation.pureAdvance_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureAdvance_origin

end AbsSat.GraphPath.Model.DriverPropagation
