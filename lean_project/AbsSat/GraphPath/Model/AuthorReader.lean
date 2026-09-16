-- lean_project/AbsSat/GraphPath/Model/AuthorReader.lean
import AbsSat.GraphPath.Model.PartialPaths
import AbsSat.GraphPath.Model.PickInduction
import AbsSat.GraphPath.Model.SubsetSemantics
import AbsSat.GraphPath.Model.Reader

/-!
# The author's reader, with a semantic invariant

`PathReader.read_step!` (Julia) reads the final state **bottom-up over the literal block**: at the
value step of each variable it pins one map node (`filter!` = `filterRequire` plus review to a
fixpoint) and throws if the graph becomes invalid. There is no backtracking.

Phantoms (pairwise-consistent selections anchored at the top that no chain extends, v111/v112) do
not enter here: the reader pins single nodes, and its invariant is semantic — the current state
contains a chain.

* **F0** `readFrom choose n v g` — the reader as a function. `choose` returns the map node to pin at
  the value step of variable `v`; the result is the list of pinned nodes, lowest first, or `none`
  if a pin leaves the graph invalid. `readAssign` turns that list into an assignment.
* **F1** `readFrom_chain` — a reader that pins the node a chain `sel` picks never fails and pins
  exactly `sel`'s nodes, because pinning a chain's own node keeps the chain (`ChainSound_filterAll`)
  and therefore validity.
* `chainRead_final` — on any final state, that reader returns a model of `φ`.
* `chainRead_of_satisfiable` — **for every satisfiable `φ`, some final state is read into a model
  without backtracking** by a reader guided by a chain. No open hypothesis.

* **F2** `authorChoice` is the author's own rule, `first(ids)`: the first node, in node order, that
  is still a global owner at the value step. `ValueOnChain g v` says that node lies on a chain of
  `g`; `AuthorReadable` asks it at every state the reader visits (`ValuesOnChains`, report v112).
  `pin_forces`: after a pin every chain goes through the pinned node. `readFrom_author`: under
  `AuthorReadable` the reader never fails and one chain of the starting state goes through every
  pin (chains of pinned states lift back with `ChainSound_of_pruned`).
* `authorRead_final` — **on a final state, under `AuthorReadable`, the author's reader reads a model
  of `φ` without backtracking.**

`AuthorReadable` is the only open hypothesis of the author's reader. It is a property of single
nodes (the picked value lies on a chain), not of selections, so the Helly gap behind phantoms does
not enter it.
-/

namespace AbsSat.GraphPath.Model.AuthorReader

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.PartialPaths
open AbsSat.GraphPath.Model.PrefixDecode
open AbsSat.GraphPath.Model.CnfChain
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.SubsetSemantics

-- ============================================================
-- F0: the reader
-- ============================================================

/-- **The reader.** At the value step of variable `v` it pins `choose g v`, reviews (inside
`filterAll`), and stops with `none` if the graph is no longer valid. -/
def readFrom (choose : GPathM → Nat → NodeId) : Nat → Nat → GPathM → Option (List NodeId)
  | 0, _, _ => some []
  | n + 1, v, g =>
    if isValid (filterAll g [choose g v]) then
      (readFrom choose n (v + 1) (filterAll g [choose g v])).map (choose g v :: ·)
    else none

/-- The assignment the pinned value nodes spell: variable `v` is true iff its node has index 1
(the reading `CnfChain.decode` uses). -/
def readAssign (ids : List NodeId) : Assign :=
  fun v => (ids.getD v { step := 0, index := 0 }).index == 1

-- ============================================================
-- F1: guided by a chain, the reader never fails
-- ============================================================

/-- Pin the node chain `sel` picks at the value step of `v`. -/
def chainChoice (sel : Int → PathNodeId) : GPathM → Nat → NodeId :=
  fun _ v => (sel (2 * (v : Int))).id

private theorem two_mul_lt (v n : Nat) (c : Int) (h : 2 * ((v + (n + 1) : Nat) : Int) ≤ c) :
    0 ≤ 2 * (v : Int) ∧ 2 * (v : Int) < c ∧ 2 * ((v + 1 + n : Nat) : Int) ≤ c :=
  ⟨by omega, by omega, by omega⟩

/-- **F1.** Guided by a chain of the current state, the reader pins exactly the chain's value nodes
and never meets an invalid graph. -/
theorem readFrom_chain (sel : Int → PathNodeId) :
    ∀ (n v : Nat) (g : GPathM), ChainSound g sel → 2 * ((v + n : Nat) : Int) ≤ g.current_step →
      readFrom (chainChoice sel) n v g =
        some ((List.range n).map (fun i => (sel (2 * ((v + i : Nat) : Int))).id)) := by
  intro n
  induction n with
  | zero => intro v g _ _; rfl
  | succ n ih =>
    intro v g hs hb
    obtain ⟨h0, hlt, hb'⟩ := two_mul_lt v n g.current_step hb
    have hstep : (sel (2 * (v : Int))).id.step = 2 * (v : Int) :=
      (hs.chain.1.1 (2 * (v : Int)) h0 hlt).2
    have hs' : ChainSound (filterAll g [(sel (2 * (v : Int))).id]) sel := by
      refine ChainSound_filterAll g _ sel hs ?_
      intro req hreq _ _
      rw [List.mem_singleton.mp hreq, hstep]
    have hv' := PickInduction.isValid_of_ChainG _ sel hs'.chain
    have hcs : (filterAll g [(sel (2 * (v : Int))).id]).current_step = g.current_step :=
      (pruned_filterAll g _).step_eq
    have hrec := ih (v + 1) _ hs' (by rw [hcs]; exact hb')
    show (if isValid (filterAll g [(sel (2 * (v : Int))).id]) = true then
        (readFrom (chainChoice sel) n (v + 1) (filterAll g [(sel (2 * (v : Int))).id])).map
          ((sel (2 * (v : Int))).id :: ·) else none) = _
    rw [if_pos hv', hrec, List.range_succ_eq_map]
    simp only [Option.map_some, List.map_cons, List.map_map, Nat.add_zero]
    congr 2
    refine List.map_congr_left (fun i _ => ?_)
    show (sel (2 * ((v + 1 + i : Nat) : Int))).id = (sel (2 * ((v + (i + 1) : Nat) : Int))).id
    rw [show v + 1 + i = v + (i + 1) from Nat.add_right_comm v 1 i]



/-- The assignment read from a chain's value nodes is the chain's own decoding, on every variable
of `φ`. -/
theorem readAssign_chain (sel : Int → PathNodeId) (n v : Nat) (hv : v < n) :
    readAssign ((List.range n).map (fun i => (sel (2 * ((0 + i : Nat) : Int))).id)) v =
      decode sel v := by
  simp only [readAssign, decode, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hv, Option.map_some, Option.getD_some]

-- ============================================================
-- On the final line
-- ============================================================

private theorem final_step (g : GPathM) (n : Nat) (s : Int) (hn : (n : Int) = s - 1)
    (h : g.current_step = (n : Int) + 1) : g.current_step - 1 = s - 1 ∧ g.current_step = s :=
  ⟨by omega, by omega⟩

private theorem stepCount_pos (φ : Cnf) : (0 : Int) < stepCount φ := by
  simp only [stepCount]
  omega

private theorem cast_pred (s : Int) (h : 0 < s) : (((s - 1).toNat : Nat) : Int) = s - 1 := by
  omega

private theorem nVars_bound (φ : Cnf) (c : Int) (h : c = stepCount φ) :
    2 * ((0 + φ.nVars : Nat) : Int) ≤ c := by
  subst h
  simp only [stepCount]
  omega

/-- Reading the value nodes of a chain of a final state spells a model of `φ`. -/
theorem sat_of_final_chain (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (sel : Int → PathNodeId) (hs : ChainSound kv.2 sel) :
    Sat (readAssign ((List.range φ.nVars).map (fun i => (sel (2 * ((0 + i : Nat) : Int))).id))) φ ∧
      2 * ((0 + φ.nVars : Nat) : Int) ≤ kv.2.current_step ∧ MapReachable φ kv.2 := by
  have hkv' : kv ∈ lineAt φ (stepCount φ - 1).toNat := hkv
  have hok := (lineAt_ok φ _).2 kv hkv'
  obtain ⟨hstep1, hstep⟩ := final_step kv.2 (stepCount φ - 1).toNat (stepCount φ)
    (cast_pred _ (stepCount_pos φ)) hok.step
  have hsat : Sat (decode sel) φ := by
    have h := satUpTo_of_chain φ hwf kv.2 hok.reach sel hs.chain.1 hs.chain.2.1
    rw [hstep1] at h
    exact sat_of_satUpTo_final φ _ h
  exact ⟨sat_congr_below φ hwf _ _ (fun i hi => (readAssign_chain sel φ.nVars i hi).symm) hsat,
    nVars_bound φ kv.2.current_step hstep, hok.reach⟩

/-- **On any final state, a reader guided by one of its chains reads a model of `φ`.** -/
theorem chainRead_final (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (sel : Int → PathNodeId) (hs : ChainSound kv.2 sel) :
    ∃ ids, readFrom (chainChoice sel) φ.nVars 0 kv.2 = some ids ∧ Sat (readAssign ids) φ := by
  obtain ⟨hsat, hb, _⟩ := sat_of_final_chain φ hwf kv hkv sel hs
  exact ⟨_, readFrom_chain sel φ.nVars 0 kv.2 hs hb, hsat⟩

/-- **For every satisfiable formula, some final state is read into a model without backtracking**,
by a reader that pins, at each value step, the node a chain of that state picks. -/
theorem chainRead_of_satisfiable (φ : Cnf) (hwf : WF φ) (h : Satisfiable φ) :
    ∃ kv ∈ pureRun φ, ∃ sel, ChainSound kv.2 sel ∧
      ∃ ids, readFrom (chainChoice sel) φ.nVars 0 kv.2 = some ids ∧ Sat (readAssign ids) φ := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨g, hmem, hal, _⟩ := pureRun_carries φ a hwf ha (stepCount_pos φ)
  obtain ⟨sel, hs, _⟩ := Conservation.chainSound_along φ a hwf ha (stepCount_pos φ) g hal
  exact ⟨_, hmem, sel, hs, chainRead_final φ hwf _ hmem sel hs⟩

-- ============================================================
-- F2: the author's own choice, first(ids)
-- ============================================================

/-- **The author's choice** (`first(ids)`): the first node, in node order, that is still a global
owner at the value step of `v`. -/
def authorChoice (g : GPathM) (v : Nat) : NodeId :=
  match (g.nodes.map (·.id)).find? (fun p => p.id.step == 2 * (v : Int) && g.gowners.contains p) with
  | some p => p.id
  | none => { step := 2 * (v : Int), index := 0 }

/-- **The one hypothesis per reader state**: the node the author picks lies on a chain. -/
def ValueOnChain (g : GPathM) (v : Nat) : Prop :=
  ∃ sel, ChainSound g sel ∧ (sel (2 * (v : Int))).id = authorChoice g v

/-- **`ValuesOnChains` along the author's reading.** At every state the reader visits, its pick lies
on a chain. The base case (a chain is left at the end) follows from the last step's hypothesis,
since pinning a chain's own node keeps the chain; it is stated so the induction can start at any
depth. -/
def AuthorReadable : Nat → Nat → GPathM → Prop
  | 0, _, g => ∃ sel, ChainSound g sel
  | n + 1, v, g => ValueOnChain g v ∧ AuthorReadable n (v + 1) (filterAll g [authorChoice g v])

/-- After pinning `d`, every chain passes through `d`: the global owners at `d`'s step name only `d`,
and the review only removes global owners. -/
theorem pin_forces (g : GPathM) (d : NodeId) (sel : Int → PathNodeId)
    (h : ChainSound (filterAll g [d]) sel) (h0 : 0 ≤ d.step) (h1 : d.step < g.current_step) :
    (sel d.step).id = d := by
  have hcs := (pruned_filterAll g [d]).step_eq
  have hlt : d.step < (filterAll g [d]).current_step := by rw [hcs]; exact h1
  have hgow : sel d.step ∈ (filterRequire g d).gowners :=
    (pruned_review (filterRequire g d)).gowners_sub _ (h.chain.2.2 d.step h0 hlt)
  have hstep := (h.chain.1.1 d.step h0 hlt).2
  simp only [filterRequire, List.mem_filter] at hgow
  obtain ⟨_, hc⟩ := hgow
  rw [hstep] at hc
  cases hb : ((sel d.step).id == d) with
  | true => exact eq_of_beq hb
  | false =>
    rw [hb] at hc
    simp only [bne_self_eq_false, Bool.false_or, Bool.false_eq_true] at hc

/-- **F2.** If every pick of the author's reading lies on a chain, the reading never fails, and
some chain of the starting state passes through every pinned node. -/
theorem readFrom_author :
    ∀ (n v : Nat) (g : GPathM), NodupIds g → Sons.SMP g → AuthorReadable n v g →
      2 * ((v + n : Nat) : Int) ≤ g.current_step →
      ∃ sel, ChainSound g sel ∧ readFrom authorChoice n v g =
        some ((List.range n).map (fun i => (sel (2 * ((v + i : Nat) : Int))).id)) := by
  intro n
  induction n with
  | zero =>
    intro v g _ _ h _
    obtain ⟨sel, hs⟩ := h
    exact ⟨sel, hs, rfl⟩
  | succ n ih =>
    intro v g hnd hsmp h hb
    obtain ⟨⟨sel0, hs0, hc0⟩, hrest⟩ := h
    obtain ⟨h0, hlt, hb'⟩ := two_mul_lt v n g.current_step hb
    have hstep : (sel0 (2 * (v : Int))).id.step = 2 * (v : Int) := (hs0.chain.1.1 _ h0 hlt).2
    have hdstep : (authorChoice g v).step = 2 * (v : Int) := by rw [← hc0, hstep]
    have hs0' : ChainSound (filterAll g [authorChoice g v]) sel0 := by
      refine ChainSound_filterAll g _ sel0 hs0 ?_
      intro req hreq _ _
      rw [List.mem_singleton.mp hreq, hdstep, hc0]
    have hv' := PickInduction.isValid_of_ChainG _ sel0 hs0'.chain
    have hcs := (pruned_filterAll g [authorChoice g v]).step_eq
    obtain ⟨sel, hs', hrec⟩ := ih (v + 1) _ (NodeIds.NodupIds_filterAll g hnd _)
      (Sons.SMP_filterAll g _ hsmp) hrest (by rw [hcs]; exact hb')
    have hpin := pin_forces g (authorChoice g v) sel hs' (by rw [hdstep]; exact h0)
      (by rw [hdstep]; exact hlt)
    rw [hdstep] at hpin
    refine ⟨sel, ChainSound_of_pruned (pruned_filterAll g _) hnd hsmp sel hs', ?_⟩
    show (if isValid (filterAll g [authorChoice g v]) = true then
        (readFrom authorChoice n (v + 1) (filterAll g [authorChoice g v])).map
          (authorChoice g v :: ·) else none) = _
    rw [if_pos hv', hrec, List.range_succ_eq_map]
    simp only [Option.map_some, List.map_cons, List.map_map, Nat.add_zero, hpin]
    congr 2
    refine List.map_congr_left (fun i _ => ?_)
    show (sel (2 * ((v + 1 + i : Nat) : Int))).id = (sel (2 * ((v + (i + 1) : Nat) : Int))).id
    rw [show v + 1 + i = v + (i + 1) from Nat.add_right_comm v 1 i]

/-- **The author's reader on a final state**: under `AuthorReadable`, it reads a model of `φ`
without backtracking. -/
theorem authorRead_final (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (h : AuthorReadable φ.nVars 0 kv.2) :
    ∃ ids, readFrom authorChoice φ.nVars 0 kv.2 = some ids ∧ Sat (readAssign ids) φ := by
  have hkv' : kv ∈ lineAt φ (stepCount φ - 1).toNat := hkv
  have hok := (lineAt_ok φ _).2 kv hkv'
  obtain ⟨_, hstep⟩ := final_step kv.2 (stepCount φ - 1).toNat (stepCount φ)
    (cast_pred _ (stepCount_pos φ)) hok.step
  have hb := nVars_bound φ kv.2.current_step hstep
  have hreach := reachable_of_mapReachable φ hwf kv.2 hok.reach
  obtain ⟨sel, hs, hread⟩ := readFrom_author φ.nVars 0 kv.2
    (Reader.NodupIds_reachable _ kv.2 hreach) (Sons.SMP_reachable _ kv.2 hreach) h hb
  exact ⟨_, hread, (sat_of_final_chain φ hwf kv hkv sel hs).1⟩

/-- info: 'AbsSat.GraphPath.Model.AuthorReader.readFrom_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readFrom_chain

/-- info: 'AbsSat.GraphPath.Model.AuthorReader.readAssign_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readAssign_chain

/-- info: 'AbsSat.GraphPath.Model.AuthorReader.chainRead_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainRead_final

/-- info: 'AbsSat.GraphPath.Model.AuthorReader.chainRead_of_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainRead_of_satisfiable

/-- info: 'AbsSat.GraphPath.Model.AuthorReader.readFrom_author' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readFrom_author

/-- info: 'AbsSat.GraphPath.Model.AuthorReader.authorRead_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms authorRead_final

end AbsSat.GraphPath.Model.AuthorReader
