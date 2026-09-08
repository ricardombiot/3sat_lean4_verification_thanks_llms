-- lean_project/AbsSat/GraphMap/MapReqs.lean
import AbsSat.GraphMap.GraphMap

/-!
**The map construction generates only 0/1/all constraints.**

A requirement pins one node at one step and says nothing about the steps it
does not mention. So for any node `d` and any step `j`, the set of step-`j`
nodes compatible with `d` is either *all of them* (no requirement at `j`) or
*exactly one* (a requirement at `j`). That is the **0/1/all** — implicational —
constraint class, and it is the class for which arc consistency decides
satisfiability (Cooper, Cohen & Jeavons 1994). See
`verificacion_inseguridad_autor_v12.md`.

Formally the property is `Functional`: **at most one requirement per step**.
Which is, verbatim, `Reachable.up`'s `hreqs_distinct` hypothesis — so proving
it of the construction is discharging that hypothesis from the map side, part
of what phase L7 owes.

**Why this is provable without a pure mirror.** `MapDocNode` and `MapColLines`
are already pure; the only `IO` in the construction is `register_var!`, which
writes the variable-name table and never touches a node. And `add_require!` is
called in exactly **five** places in the whole codebase — two in `add_var!`
(the negative variable block) and three in `add_gate_case!` (the clause node) —
matching the Julia original one for one:

    GraphMap.lean:81,87        graph_map.jl:86,91
    GraphMap.lean:143,144,145  graph_map.jl:156,157,158

So the two theorems below, `addVar_negBlock_ok` and `addGateCase_ok`, cover
every requirement set the construction can build. Nothing else adds one:
`link_nodes!` only touches parents and sons (`add_parent_requires`,
`add_son_requires`).

**The clause hypothesis is real, not bureaucratic.** `addGateCase_ok` needs the
three literal steps pairwise distinct. Two literals land on the same step iff
they are the same variable with the same polarity, so the hypothesis is *no
repeated literal within a clause*. `ImportCnf` neither normalises nor rejects
those, and `repeated_literal_not_functional` below exhibits the failure. The
machine still behaves correctly on such a clause — the filter empties that step
and the graph goes invalid — but the node falls outside `Reachable`, and so
outside everything proved about the model.

**Axiom closure.** This module is the first to reason about `Std.HashSet`
membership, and `Std.HashSet.mem_insert` is itself
`[propext, Classical.choice, Quot.sound]` in Std. So are the results here. That
is a Std dependency, not a project axiom — and it retro-justifies the plan's
decision (§6.1) to build the `GPathM` mirror on `List` rather than `HashMap`:
that choice is what keeps the mirror's closures at `[propext, Quot.sound]`.
-/

namespace AbsSat.GraphMap.MapReqs
open AbsSat.Utils.Alias
open AbsSat.Db.Map.Docs.MapDocNode

/-- `MapDocNode.new`, unambiguously. -/
abbrev mkNode : NodeId → String → MapDocNode := AbsSat.Db.Map.Docs.MapDocNode.new

/-- **0/1/all.** A requirement set is *functional* when it names at most one
node per step: for any step, the set either says nothing about it (the "all"
case — every node of that step stays compatible) or pins exactly one node (the
"1" case). The "0" case — two different requirements at the same step — is
what this rules out. -/
def Functional (rs : SetNodesId) : Prop :=
  ∀ r₁ ∈ rs, ∀ r₂ ∈ rs, r₁.step = r₂.step → r₁ = r₂

/-- Requirements point strictly backwards. -/
def Backward (n : MapDocNode) : Prop := ∀ r ∈ n.requires, r.step < n.id.step

def NodeOk (n : MapDocNode) : Prop := Functional n.requires ∧ Backward n

-- ============================================================
-- Requirements are untouched by everything except `add_require!`
-- ============================================================

theorem add_parent_requires (n : MapDocNode) (p : NodeId) :
    (add_parent! n p).requires = n.requires := rfl

theorem add_son_requires (n : MapDocNode) (s : NodeId) :
    (add_son! n s).requires = n.requires := rfl

theorem NodeOk_add_parent (n : MapDocNode) (p : NodeId) (h : NodeOk n) :
    NodeOk (add_parent! n p) := h

theorem NodeOk_add_son (n : MapDocNode) (s : NodeId) (h : NodeOk n) :
    NodeOk (add_son! n s) := h

/-- A node that has not been given any requirement yet. Both construction
sites start from one. -/
def NoReqs (n : MapDocNode) : Prop := ∀ q, q ∉ n.requires

theorem NoReqs_new (id : NodeId) (t : String) : NoReqs (mkNode id t) := by
  intro q; simp [mkNode, AbsSat.Db.Map.Docs.MapDocNode.new]

theorem NoReqs_add_parent (n : MapDocNode) (p : NodeId) (h : NoReqs n) :
    NoReqs (add_parent! n p) := h

theorem NodeOk_new (id : NodeId) (t : String) : NodeOk (mkNode id t) :=
  ⟨fun _ h₁ => absurd h₁ (NoReqs_new id t _), fun _ h => absurd h (NoReqs_new id t _)⟩

-- ============================================================
-- The two shapes the construction actually builds
-- ============================================================

theorem mem_requires_add (n : MapDocNode) (r q : NodeId) :
    q ∈ (add_require! n r).requires ↔ q = r ∨ q ∈ n.requires := by
  simp only [add_require!]
  constructor
  · intro h
    rcases Std.HashSet.mem_insert.mp h with h | h
    · exact Or.inl (eq_of_beq h).symm
    · exact Or.inr h
  · intro h
    refine Std.HashSet.mem_insert.mpr ?_
    rcases h with rfl | h
    · exact Or.inl (beq_iff_eq.mpr rfl)
    · exact Or.inr h

theorem add_require_id (n : MapDocNode) (r : NodeId) : (add_require! n r).id = n.id := rfl

/-- **The negative variable block**: one requirement. Functional for free — a
single requirement can never name two nodes at the same step. -/
theorem NodeOk_one (n : MapDocNode) (hn : NoReqs n) (r : NodeId)
    (hb : r.step < n.id.step) : NodeOk (add_require! n r) := by
  refine ⟨?_, ?_⟩
  · intro r₁ h₁ r₂ h₂ _
    rcases (mem_requires_add _ _ _).mp h₁ with rfl | h₁
    · rcases (mem_requires_add _ _ _).mp h₂ with rfl | h₂
      · rfl
      · exact absurd h₂ (hn _)
    · exact absurd h₁ (hn _)
  · intro r' h
    rcases (mem_requires_add _ _ _).mp h with rfl | h
    · exact hb
    · exact absurd h (hn _)

/-- **The clause block**: three requirements, one per literal. Functional
*exactly when* the three literals land on three different steps — which is
what a clause with no repeated same-polarity literal gives. -/
theorem NodeOk_three (n : MapDocNode) (hn : NoReqs n) (ra rb rc : NodeId)
    (hab : ra.step ≠ rb.step) (hac : ra.step ≠ rc.step) (hbc : rb.step ≠ rc.step)
    (ha : ra.step < n.id.step) (hb : rb.step < n.id.step) (hc : rc.step < n.id.step) :
    NodeOk (add_require! (add_require! (add_require! n ra) rb) rc) := by
  have hmem : ∀ q, q ∈ (add_require! (add_require! (add_require! n ra) rb) rc).requires →
      q = rc ∨ q = rb ∨ q = ra := by
    intro q hq
    rcases (mem_requires_add _ _ _).mp hq with rfl | hq
    · exact Or.inl rfl
    rcases (mem_requires_add _ _ _).mp hq with rfl | hq
    · exact Or.inr (Or.inl rfl)
    rcases (mem_requires_add _ _ _).mp hq with rfl | hq
    · exact Or.inr (Or.inr rfl)
    · exact absurd hq (hn _)
  refine ⟨?_, ?_⟩
  · intro r₁ h₁ r₂ h₂ hs
    rcases hmem r₁ h₁ with rfl | rfl | rfl <;> rcases hmem r₂ h₂ with rfl | rfl | rfl <;>
      first
        | rfl
        | (exact absurd hs.symm (by assumption))
        | (exact absurd hs (by assumption))
  · intro r h
    rcases hmem r h with rfl | rfl | rfl
    · exact hc
    · exact hb
    · exact ha

-- ============================================================
-- The construction's two sites, verbatim
-- ============================================================

/-- `add_var!`'s negative-block node (`GraphMap.lean:79-88`), for index `i`:
parent and requirement both point at `{var_step, 1-i}`, one step back. -/
theorem addVar_negBlock_ok (var_step : Step) (i : Int) (t : String) :
    NodeOk (add_require!
      (add_parent! (mkNode { step := var_step + 1, index := i } t)
        { step := var_step, index := 1 - i })
      { step := var_step, index := 1 - i }) :=
  NodeOk_one _ (NoReqs_add_parent _ _ (NoReqs_new _ _)) _
    (by simp only [add_parent!, mkNode, AbsSat.Db.Map.Docs.MapDocNode.new]; omega)

/-- `add_gate_case!`'s clause node (`GraphMap.lean:137-145`): three
requirements at the three literal steps. -/
theorem addGateCase_ok (gate_step step_a step_b step_c : Step)
    (index ia ib ic : Int) (t : String)
    (hab : step_a ≠ step_b) (hac : step_a ≠ step_c) (hbc : step_b ≠ step_c)
    (ha : step_a < gate_step) (hb : step_b < gate_step) (hc : step_c < gate_step) :
    NodeOk (add_require! (add_require! (add_require!
      (mkNode { step := gate_step, index := index } t)
      { step := step_a, index := ia })
      { step := step_b, index := ib })
      { step := step_c, index := ic }) :=
  NodeOk_three _ (NoReqs_new _ _) _ _ _ hab hac hbc ha hb hc

-- ============================================================
-- And the counterexample: a repeated same-polarity literal
-- ============================================================

/-- If a clause repeats a literal with the same polarity, two of its three
requirements land on the *same* step with different indices — the "0" case
that `Functional` rules out. The machine still behaves correctly (the filter
empties that step and the graph goes invalid) but such a node falls outside
`Reachable`'s `hreqs_distinct`, and so outside everything proved about the
model. -/
theorem repeated_literal_not_functional (gate_step : Step) (t : String) :
    ¬ Functional (add_require! (add_require!
        (mkNode { step := gate_step, index := 0 } t)
        { step := 0, index := 0 })
        { step := 0, index := 1 }).requires := by
  intro h
  have h0 : ({ step := 0, index := 0 } : NodeId) ∈
      (add_require! (add_require! (mkNode { step := gate_step, index := 0 } t)
        { step := 0, index := 0 }) { step := 0, index := 1 }).requires :=
    (mem_requires_add _ _ _).mpr (Or.inr ((mem_requires_add _ _ _).mpr (Or.inl rfl)))
  have h1 : ({ step := 0, index := 1 } : NodeId) ∈
      (add_require! (add_require! (mkNode { step := gate_step, index := 0 } t)
        { step := 0, index := 0 }) { step := 0, index := 1 }).requires :=
    (mem_requires_add _ _ _).mpr (Or.inl rfl)
  have hcontra := h _ h0 _ h1 rfl
  simp at hcontra

-- ============================================================
-- Axiom guards (Std's HashSet lemmas are classical; see above)
-- ============================================================

/-- info: 'AbsSat.GraphMap.MapReqs.addVar_negBlock_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms addVar_negBlock_ok

/-- info: 'AbsSat.GraphMap.MapReqs.addGateCase_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms addGateCase_ok

/-- info: 'AbsSat.GraphMap.MapReqs.repeated_literal_not_functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms repeated_literal_not_functional

end AbsSat.GraphMap.MapReqs
