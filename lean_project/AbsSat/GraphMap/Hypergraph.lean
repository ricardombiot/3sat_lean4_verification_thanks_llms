-- lean_project/AbsSat/GraphMap/Hypergraph.lean
import AbsSat.GraphMap.MapReqs

/-!
**Route E — the constraint hypergraph of a 3SAT map, and its acyclicity.**

`Link.lean` closed the CCJ route negatively: 0/1/all constraints are
majority-closed and so have *strict width 2*, which needs **path** consistency,
while the machine maintains something weaker. Route E asks whether a different
classical theorem applies instead — one that needs no path consistency at all:

> **Beeri–Fagin–Maier–Yannakakis (1983).** If the constraint hypergraph is
> α-**acyclic**, then pairwise (arc) consistency implies global consistency.

If the map's hypergraph were α-acyclic, arc consistency would decide, "no
zombies" would follow, and none of the width machinery would be needed. This
module builds the hypergraph and decides acyclicity, so the question is
answered by measurement rather than by argument.

## What the CSP is

The variables are the **steps** `0 … gmap.step - 1`; the domain of step `k` is
the set of map nodes at step `k`; and a node's `requires` are the constraints.
That is exactly the shape of `Denot.IsChain`: a selection of one node per step.

Two hypergraphs are built, because the choice matters and only one of them is
the honest one:

* `scopesByStep` — one edge per step, `{k} ∪ {r.step : r required by some node
  at k}`. **This is the hypergraph BFMY is about**: a constraint is one
  relation, and its scope is every variable it constrains.
* `scopesByNode` — one edge per *node*. Finer, hence smaller edges, hence more
  likely to reduce. It is **not** a valid decomposition of the constraints (a
  node's requirement set is one disjunct of a step's relation, not a
  constraint of its own), so it is only computed as the optimistic bound: if
  even this one is cyclic, the honest one certainly is.

## Deciding α-acyclicity: the GYO reduction

A hypergraph is α-acyclic iff repeatedly applying

1. **ear removal** — delete a vertex that occurs in only one edge, and
2. **subsumption** — delete an edge contained in another,

reduces it to nothing. What is left when the reduction stalls is the *cyclic
core*, and its size says how far from acyclic the map is.

## What a positive answer would have meant

It has to be said plainly, because it changes how to read the result:
α-acyclic CSPs are solvable in polynomial time. So a map whose hypergraph were
α-acyclic would put 3SAT in P **by a 1983 theorem** — route E would not be a
step towards the claim, it would *be* the claim. A negative answer therefore
refutes nothing about the algorithm; it only closes this particular proof
route, and says any proof of "no zombies" must come from the machine's
dynamics rather than from the static structure of the map.
-/

namespace AbsSat.GraphMap.Hypergraph

open AbsSat.Utils.Alias
open AbsSat.GraphMap.GraphMap
open AbsSat.Db.Map.Docs.MapDocNode

/-- One constraint scope: a set of steps, kept sorted and duplicate-free. -/
abbrev Edge := List Int
abbrev Hyper := List Edge

def insertSorted (v : Int) : Edge → Edge
  | [] => [v]
  | x :: xs => if v == x then x :: xs else if v < x then v :: x :: xs
               else x :: insertSorted v xs

def mkEdge (vs : List Int) : Edge := vs.foldl (fun acc v => insertSorted v acc) []

def subset (a b : Edge) : Bool := a.all (fun v => b.contains v)

/-- How many edges contain `v`. -/
def occurs (h : Hyper) (v : Int) : Nat := (h.filter (fun e => e.contains v)).length

/-- **Ear removal.** A vertex in only one edge constrains nothing else, so it
can be projected away. -/
def dropEars (h : Hyper) : Hyper :=
  h.map (fun e => e.filter (fun v => occurs h v > 1))

def dedupE (h : Hyper) : Hyper :=
  h.foldl (fun acc e => if acc.any (fun f => f == e) then acc else acc ++ [e]) []

/-- **Subsumption.** An edge contained in another adds no constraint of its
own. Empty edges go too. -/
def dropSubsumed (h : Hyper) : Hyper :=
  let h := (dedupE h).filter (fun e => !e.isEmpty)
  h.filter (fun e => !(h.any (fun f => f != e && subset e f)))

def gyoStep (h : Hyper) : Hyper := dropSubsumed (dropEars h)

/-- Iterate to the fixpoint. Every round removes at least one vertex
occurrence or one edge, so `h.length + h.flatten.length + 1` rounds suffice. -/
def gyoGo : Nat → Hyper → Hyper
  | 0, h => h
  | n + 1, h => let h' := gyoStep h; if h' == h then h else gyoGo n h'

def gyo (h : Hyper) : Hyper := gyoGo (h.length + h.flatten.length + 1) h

/-- The **cyclic core**: what the GYO reduction cannot remove. -/
def core (h : Hyper) : Hyper := gyo h

/-- **α-acyclicity**, decided. -/
def isAlphaAcyclic (h : Hyper) : Bool := (gyo h).isEmpty

/-- What route E would have needed of a map, stated for the record. -/
def AlphaAcyclicMap (h : Hyper) : Prop := gyo h = []

theorem alphaAcyclic_iff (h : Hyper) : AlphaAcyclicMap h ↔ isAlphaAcyclic h = true := by
  unfold AlphaAcyclicMap isAlphaAcyclic
  constructor
  · intro hh; rw [hh]; rfl
  · intro hh; exact List.isEmpty_iff.mp hh

-- ============================================================
-- Building the hypergraph of a real map
-- ============================================================

def stepsOf (gmap : GMap) : List Int := (List.range gmap.step.toNat).map (fun i => Int.ofNat i)

def nodesAt (gmap : GMap) (k : Int) : List MapDocNode :=
  (get_ids_step gmap k).toList.filterMap (fun id => get_node gmap id)

/-- One edge per node: `{its step} ∪ {steps its requirements name}`. The
optimistic hypergraph — finer than the constraints really are. -/
def scopesByNode (gmap : GMap) : Hyper :=
  (stepsOf gmap).flatMap (fun k =>
    (nodesAt gmap k).map (fun n => mkEdge (k :: n.requires.toList.map (·.step))))

/-- One edge per step, over every step any of its nodes constrains. **This is
the hypergraph BFMY is about.** -/
def scopesByStep (gmap : GMap) : Hyper :=
  (stepsOf gmap).filterMap (fun k =>
    let rs := (nodesAt gmap k).flatMap (fun n => n.requires.toList.map (·.step))
    if rs.isEmpty then none else some (mkEdge (k :: rs)))

structure Report where
  steps      : Nat
  edgesNode  : Nat
  coreNode   : Nat
  coreVertsN : Nat
  edgesStep  : Nat
  coreStep   : Nat
  coreVertsS : Nat
  acyclicN   : Bool
  acyclicS   : Bool

def verts (h : Hyper) : Nat := (mkEdge h.flatten).length

def analyse (gmap : GMap) : Report :=
  let hn := scopesByNode gmap
  let hs := scopesByStep gmap
  let cn := core hn
  let cs := core hs
  { steps := (stepsOf gmap).length,
    edgesNode := hn.length, coreNode := cn.length, coreVertsN := verts cn,
    edgesStep := hs.length, coreStep := cs.length, coreVertsS := verts cs,
    acyclicN := cn.isEmpty, acyclicS := cs.isEmpty }

-- ============================================================
-- Sanity checks on the reduction itself
-- ============================================================

section Examples

/-- A tree is acyclic. A triangle is the standard α-cycle. `{a,b,c},{b,c,d}`
is the classic case that is α-acyclic without its primal graph being acyclic —
which is what makes α-acyclicity the right notion here rather than "the
constraint graph is a forest". Kernel-checked, no `native_decide`. -/
example : isAlphaAcyclic [[1,2],[2,3],[3,4]] = true := by decide

example : isAlphaAcyclic [[1,2],[2,3],[1,3]] = false := by decide

example : isAlphaAcyclic [[1,2,3],[2,3,4]] = true := by decide

/-- **Where the cycle actually is, in map terms.** Two clause nodes (100, 101)
sharing two variable steps still reduce: the clause steps are ears, and what is
left of one edge is contained in the other. -/
example : isAlphaAcyclic [[1,2,3,100],[1,2,4,101]] = true := by decide

/-- Three clauses cycling over shared variable steps do not: after the clause
steps go, `{1,2,3}, {2,3,4}, {1,3,4}` has no ear and no containment. The cycle
is the shared-variable structure of the CNF, not an artefact of the
construction. -/
example : isAlphaAcyclic [[1,2,3,100],[2,3,4,101],[1,3,4,102]] = false := by decide

def run_tests : IO Unit := do
  assert! isAlphaAcyclic [[1,2],[2,3],[3,4]]
  assert! !(isAlphaAcyclic [[1,2],[2,3],[1,3]])
  assert! isAlphaAcyclic [[1,2,3],[2,3,4]]
  assert! (core [[1,2],[2,3],[1,3]]).length == 3
  assert! isAlphaAcyclic [[1,2,3,100],[1,2,4,101]]
  assert! !(isAlphaAcyclic [[1,2,3,100],[2,3,4,101],[1,3,4,102]])
  IO.println "All Hypergraph tests passed!"

#eval run_tests

end Examples

end AbsSat.GraphMap.Hypergraph
