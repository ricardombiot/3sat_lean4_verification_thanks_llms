-- lean_project/AbsSat/GraphPath/Model/Validate.lean
import AbsSat.GraphPath.Model.L6Search
import AbsSat.GraphPath.Model.Certificate
import AbsSat.GraphPath.Model.Verdict
import AbsSat.GraphPath.Model.MirrorTest
import AbsSat.GraphMap.ImportCnf
import AbsSat.Utils.ExhaustiveSolver
import AbsSat.SatMachine.DiffTest

/-!
**Checking the algorithm's validity directly, on real 3SAT maps.**

`diffTest` is a black-box check: it compares the verdict and the solution set
against a brute-force oracle. A zombie — a surviving node with no complete
co-owned chain — only shows up there if it happens to change one of those. It
can appear mid-run and be pruned later, and the end result is right by luck.

This module checks the open property *directly*, as an internal invariant, at
every state the machine holds:

> every node still in the graph lies on some complete co-owned chain.

**Since 2026-09-09 the check is itself verified.** Every certificate goes
through `Certificate.isCert`, and `Supported_of_zombiesOf_nil` below proves
that a clean run *is* `Supported g` — the open lemma L6 — for that graph. The
search that proposes the certificates stays untrusted: a bug in it can only
make the checker reject.

Two design points make the check independent of the thing being tested:

* the chain search here is a plain backtracking search over the graph, **not**
  the machine's own Reader — so "no chain" is not the algorithm judging
  itself;
* any chain the search finds is re-verified with `L6Search.isGoodChain`, which
  re-checks `IsChain` and `PairwiseOwned` from their definitions.

Run with `lake exe validate <file.cnf> ...`.
-/

namespace AbsSat.GraphPath.Model.Validate

open AbsSat.Utils.Alias
open AbsSat.GraphMap.GraphMap AbsSat.GraphMap.ImportCnf
open AbsSat.GraphPath.Model AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MirrorTest
open L6Search (ownersOfB isGoodChain)

/-- Can `c` be appended to `chosen` (most recent first)? Needs the parent link
to the previous step and mutual ownership with every earlier choice. -/
def compatible (g : GPathM) (chosen : List PathNodeId) (c : PathNodeId) : Bool :=
  (match chosen with
   | [] => true
   | p :: _ => match g.node? c with
               | some n => n.parents.contains p
               | none => false)
  && chosen.all (fun q => (ownersOfB g q).contains c && (ownersOfB g c).contains q)

/-- Backtracking search for a complete co-owned chain that passes through
`target`. Independent of the Reader. -/
partial def searchFrom (g : GPathM) (target : PathNodeId) (k : Int)
    (chosen : List PathNodeId) : Option (List PathNodeId) :=
  if k ≥ g.current_step then some chosen.reverse
  else
    let cands := if target.id.step == k then [target] else (g.line k).map (·.id)
    cands.findSome? (fun c =>
      if compatible g chosen c then searchFrom g target (k + 1) (c :: chosen) else none)

/-- The certificate the search proposes for `d`. **Untrusted**: the search is
`partial` and nothing is proved about it. Its output is only ever fed to
`Certificate.isCert`. -/
def certOf (g : GPathM) (d : PathNodeId) : List PathNodeId :=
  (searchFrom g d 0 []).getD []

/-- The **verified** acceptance test: the certificate is a complete co-owned
chain of exactly the right length, and it passes through `d` at `d`'s own step.
`Certificate.isCert_sound` proves this is `IsChain` + `PairwiseOwned` in the
sense of `Denot.lean`. -/
def certOk (g : GPathM) (d : PathNodeId) : Bool :=
  Certificate.isCert g (certOf g d) && ((certOf g d)[d.id.step.toNat]? == some d)

/-- A chain through `d`, accepted only if the verified checker says so. -/
def chainThrough (g : GPathM) (d : PathNodeId) : Option (List PathNodeId) :=
  if certOk g d then some (certOf g d) else none

/-- Nodes of `g` with no accepted certificate. Non-empty means the "no zombies"
invariant just failed on a real map. -/
def zombiesOf (g : GPathM) : List PathNodeId :=
  g.nodes.filterMap (fun n => if certOk g n.id then none else some n.id)

/-- **What a clean run of this checker means, formally.** Not "the search found
something" — `Supported g`, the open lemma L6, holds of that graph. -/
theorem Supported_of_zombiesOf_nil (g : GPathM) (h : zombiesOf g = []) : Supported g := by
  refine Certificate.Supported_of_checkSupported g (certOf g) (List.all_eq_true.mpr ?_)
  intro n hn
  have hf := List.filterMap_eq_nil_iff.mp h n hn
  show certOk g n.id = true
  cases hcond : certOk g n.id with
  | true => rfl
  | false => rw [hcond] at hf; simp at hf

-- ============================================================
-- The cheap half: certifying `Inhabited` (route D)
-- ============================================================

/-- One certificate for the whole graph, taken through whichever node comes
first. `Verdict.lean` shows this is the half of L6 the SAT/UNSAT verdict
consumes — and it costs one certificate, not one per node. -/
def inhabitCert (g : GPathM) : List PathNodeId :=
  match g.nodes with
  | [] => []
  | n :: _ => (searchFrom g n.id 0 []).getD []

def certifiedInhabited (g : GPathM) : Bool := Certificate.isCert g (inhabitCert g)

theorem Inhabited_of_certifiedInhabited (g : GPathM) (h : certifiedInhabited g = true) :
    AbsSat.GraphPath.Model.Inhabited g :=
  Certificate.Inhabited_of_isCert g (inhabitCert g) h

/-- info: 'AbsSat.GraphPath.Model.Validate.Supported_of_zombiesOf_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Supported_of_zombiesOf_nil

/-- info: 'AbsSat.GraphPath.Model.Validate.Inhabited_of_certifiedInhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_certifiedInhabited

/-- Walk the machine over a real map, checking every state.
Returns `(states, nodes, zombie states, zombie nodes, states with a certified
`Inhabited`)`. -/
partial def walk (gmap : GMap) (line : MirrorLine) (fuel : Nat)
    (acc : Nat × Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat × Nat :=
  if fuel = 0 || line.isEmpty then acc
  else
    let acc := line.foldl (fun (a : Nat × Nat × Nat × Nat × Nat) kv =>
      let g := kv.2
      if !isValid g then a else
        let zs := zombiesOf g
        (a.1 + 1, a.2.1 + g.nodes.length,
         a.2.2.1 + (if zs.isEmpty then 0 else 1), a.2.2.2.1 + zs.length,
         a.2.2.2.2 + (if certifiedInhabited g then 1 else 0))) acc
    walk gmap (mirrorAdvance gmap line) (fuel - 1) acc

def report (path : String) : IO Bool := do
  let gmap ← load_import! path
  let (states, nodes, zstates, znodes, inhab) :=
    walk gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0)
  IO.println s!"{path}"
  IO.println s!"  valid states checked={states}  nodes checked={nodes}"
  IO.println s!"  Inhabited certified in {inhab}/{states} state(s)"
  if znodes == 0 then
    IO.println s!"  Supported (no zombies) certified in {states}/{states} state(s) ✅"
    return true
  else
    IO.println s!"  ZOMBIES: {znodes} node(s) with no chain, across {zstates} state(s) ❌"
    return false

-- ============================================================
-- Randomised campaign
-- ============================================================

open AbsSat.SatMachine.DiffTest (Rng gen_cnf)

/-- Check one generated instance; returns `(ok, states, nodes)`. A failing
instance is written to `validate_failure_<k>.cnf` and is reproducible from the
`(seed, case)` pair. -/
def checkCnfText (cnf : String) (tmp : String) : IO (Bool × Nat × Nat × Nat) := do
  IO.FS.writeFile tmp cnf
  let gmap ← load_import! tmp
  let (states, nodes, _, znodes, inhab) := walk gmap (mirrorInit gmap) 1000 (0, 0, 0, 0, 0)
  pure (znodes == 0 && inhab == states, states, nodes, inhab)

/-- The same density regimes `diffTest` uses: mostly under-constrained, with
every third case past the ~4.26n phase transition so the UNSAT side gets real
coverage. -/
def runRandom (cases seed nvMin nvSpan : Nat) : IO UInt32 := do
  IO.println s!"--- no-zombies campaign: cases={cases} seed={seed} \
vars={nvMin}..{nvMin + nvSpan - 1} ---"
  let mut rng := Rng.ofSeed seed
  let mut failures := 0
  let mut states := 0
  let mut nodes := 0
  let mut inhab := 0
  for idx in [0:cases] do
    let (rng1, nv) := rng.below nvSpan
    let nVars := nvMin + nv
    let (rng2, nClauses) :=
      if idx % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := gen_cnf rng2 nVars nClauses
    rng := rng3
    let (ok, st, nd, ih) ← checkCnfText cnf "validate_tmp.cnf"
    inhab := inhab + ih
    states := states + st
    nodes := nodes + nd
    if !ok then
      failures := failures + 1
      IO.FS.writeFile s!"validate_failure_{idx}.cnf" cnf
      IO.println s!"  ZOMBIE at case {idx} (vars={nVars} clauses={nClauses}) \
-> validate_failure_{idx}.cnf"
  IO.println s!"--- {cases - failures}/{cases} clean; \
valid states={states} nodes checked={nodes} Inhabited certified={inhab} ---"
  if failures == 0 then
    IO.println "Supported and Inhabited hold — as theorems, on each state checked. ✅"
    pure 0
  else
    IO.println s!"{failures} instance(s) with zombies. ❌"
    pure 1

end AbsSat.GraphPath.Model.Validate
