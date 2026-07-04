-- lean_project/AbsSat/GraphPath/Model/GPathM.lean
import AbsSat.Utils.Alias

/-!
# `GPathM` — the pure mirror of `GPath`

Phase F1 of `docs/plans/espejo_gpathm_lema_L1.md`: a purely functional
(`IO.Ref`-free, `partial`-free) mirror of the executable Owners graph
(`AbsSat/GraphPath/GraphPath.lean`, post-2026-07-04 fixes), suitable for
proofs. Three deliberate representation changes, all specification-level
(observable filter results must match the executable — validated by the
three-way differential harness of phase F6 — but internals need not):

1. **Flat owners lists.** A `PathNodeId` already carries its step
   (`id.step`), so the per-step table of the executable is just an index:
   here `owners : List PathNodeId`, and "owners at step k" is a `filter`.
2. **Validity is derived, not stored.** `isValid` recomputes "every step
   below `current_step` has a global owner" instead of maintaining
   `valid`/`emptySteps` flags (whose desynchronization was exactly the bug
   fixed on 2026-07-04).
3. **Every pruning is a `List.filter`** (or removes whole elements), so
   monotonicity — pruned state ⊆ previous state — comes from generic
   `filter` lemmas rather than case analysis.

Sequencing differences with the executable (hash-order iteration, per-line
early breaks) can change *intermediate* states but not the review fixpoint
or the validity verdict, which is all later phases consume.
-/

namespace AbsSat.GraphPath.Model

open AbsSat.Utils.Alias

-- ============================================================
-- Structures
-- ============================================================

structure PNodeM where
  id      : PathNodeId
  title   : String
  parents : List PathNodeId
  sons    : List PathNodeId
  owners  : List PathNodeId
  deriving Repr, BEq

def PNodeM.weight (n : PNodeM) : Nat :=
  1 + n.parents.length + n.sons.length + n.owners.length

structure GPathM where
  nodes        : List PNodeM
  gowners      : List PathNodeId
  current_step : Int
  map_parent   : Option NodeId
  deriving Repr

namespace GPathM

def empty : GPathM :=
  { nodes := [], gowners := [], current_step := 0, map_parent := none }

-- ============================================================
-- Derived views
-- ============================================================

/-- Integer range `lo..hi` inclusive (empty when `lo > hi`). -/
def intRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map (fun i => lo + Int.ofNat i)

def ownersAt (owners : List PathNodeId) (k : Int) : List PathNodeId :=
  owners.filter (fun q => q.id.step == k)

def hasStepEntry (owners : List PathNodeId) (k : Int) : Bool :=
  owners.any (fun q => q.id.step == k)

def line (g : GPathM) (k : Int) : List PNodeM :=
  g.nodes.filter (fun n => n.id.id.step == k)

def node? (g : GPathM) (id : PathNodeId) : Option PNodeM :=
  g.nodes.find? (fun n => n.id == id)

/-- The graph is valid iff every step below `current_step` retains a global
owner — the derived form of the executable's `valid && emptySteps.isEmpty`. -/
def isValid (g : GPathM) : Bool :=
  (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry g.gowners k)

-- ============================================================
-- Owners algebra
-- ============================================================

/--
Intersect owners list `a` with `b`, faithful to Julia's `intersect!` /
the executable's `intersectStep`: entries of `a` at steps where `b` has *no*
entry at all are kept untouched; where `b` does have entries, only members of
`b` survive. The result is a `filter` of `a` (never grows).
-/
def intersectOwners (a b : List PathNodeId) : List PathNodeId :=
  a.filter (fun q => !hasStepEntry b q.id.step || b.contains q)

/-- Union of the owners of the given (existing) neighbor nodes. Duplicates are
harmless: this value is only ever the right argument of `intersectOwners`. -/
def unionOwnersOf (g : GPathM) (ids : List PathNodeId) : List PathNodeId :=
  ids.foldl (fun acc pid =>
    match g.node? pid with
    | some p => acc ++ p.owners
    | none => acc) []

-- ============================================================
-- Node validity (rules 1-4 of the executable's `is_valid_node`)
-- ============================================================

def isValidNode (g : GPathM) (n : PNodeM) : Bool :=
  let owners_ok :=
    (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry n.owners k)
  let is_root := n.id.parent_id.isNone
  let is_last := n.id.id.step == g.current_step - 1
  let have_parents := !n.parents.isEmpty
  let have_sons := !n.sons.isEmpty
  if is_root then
    if is_last then owners_ok else owners_ok && have_sons
  else if is_last then
    owners_ok && have_parents
  else
    owners_ok && have_parents && have_sons

-- ============================================================
-- Removal and update primitives
-- ============================================================

/-- Apply `f` to the first node matching `id` (the same first-match scan
`node?` performs, so the two stay aligned). Taking a uniform, weight-
non-increasing transformer instead of a replacement value is what makes the
measure lemmas of `Fuel.lean` independent of node-id uniqueness. -/
def updateAtGo (id : PathNodeId) (f : PNodeM → PNodeM) : List PNodeM → List PNodeM
  | [] => []
  | n :: ns => if n.id == id then f n :: ns else n :: updateAtGo id f ns

def updateAt (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM) : GPathM :=
  { g with nodes := updateAtGo id f g.nodes }

/-- Physically remove a node: drop it from the collection and from the global
owners, and unlink it from every remaining node's parents/sons — the mirror of
`remove_node_owner!` + `clean_links!` + the physical `filter!` removal. -/
def removeNode (g : GPathM) (id : PathNodeId) : GPathM :=
  let nodes := g.nodes.filter (fun n => n.id != id)
  let nodes := nodes.map (fun n =>
    { n with
      parents := n.parents.filter (fun p => p != id),
      sons := n.sons.filter (fun s => s != id) })
  { g with nodes := nodes, gowners := g.gowners.filter (fun q => q != id) }

-- ============================================================
-- Review pass (mirror of make_review_owners!'s body, one round)
-- ============================================================

/-- One `clean_invalid_nodes!` sweep over a snapshot of node ids: intersect
each node's owners with the global owners, then drop it if invalid. -/
def cleanInvalidGo (g : GPathM) : List PathNodeId → GPathM
  | [] => g
  | id :: rest =>
    match g.node? id with
    | none => cleanInvalidGo g rest
    | some d =>
      let gow := g.gowners
      let d := { d with owners := intersectOwners d.owners gow }
      let g := updateAt g id (fun n => { n with owners := intersectOwners n.owners gow })
      let g := if isValidNode g d then g else removeNode g id
      cleanInvalidGo g rest

def cleanInvalid (g : GPathM) : GPathM :=
  cleanInvalidGo g (g.nodes.map (·.id))

/-- Coherence review of one node against a neighbor selector (parents on the
top-down pass, sons on the bottom-up pass): intersect its owners with the
union of its neighbors' owners, dropping it if that leaves it invalid. -/
def reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some d =>
    if isValidNode g d then
      let uni := unionOwnersOf g (nb d)
      let d := { d with owners := intersectOwners d.owners uni }
      let g := updateAt g id (fun n => { n with owners := intersectOwners n.owners uni })
      if isValidNode g d then g else removeNode g id
    else
      removeNode g id

def reviewLine (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int) : GPathM :=
  ((g.line k).map (·.id)).foldl (fun g id => reviewNode g nb id) g

/-- Walk a list of steps, reviewing each line, stopping as soon as the graph
goes invalid (the executable's `break`). -/
def reviewSteps (g : GPathM) (nb : PNodeM → List PathNodeId) : List Int → GPathM
  | [] => g
  | k :: ks =>
    if isValid g then reviewSteps (reviewLine g nb k) nb ks else g

/-- Top-down: owners coherent with the union of the parents' owners. -/
def reviewParents (g : GPathM) : GPathM :=
  reviewSteps g (·.parents) (intRange 1 (g.current_step - 1))

/-- Bottom-up: owners coherent with the union of the sons' owners. -/
def reviewSons (g : GPathM) : GPathM :=
  reviewSteps g (·.sons) (intRange 1 (g.current_step - 2)).reverse

/-- One full round of `make_review_owners!`. -/
def reviewPass (g : GPathM) : GPathM :=
  reviewSons (reviewParents (cleanInvalid g))

-- ============================================================
-- Fuel-based review loop (termination lemmas live in Fuel.lean)
-- ============================================================

/-- Everything any review sub-operation can shrink, so any change to the
graph strictly decreases it. -/
def measure (g : GPathM) : Nat :=
  g.gowners.length + (g.nodes.map PNodeM.weight).sum

def reviewFuel : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    if isValid g then
      let g' := reviewPass g
      if measure g' < measure g then reviewFuel fuel g' else g'
    else
      g

/-- Iterate review passes to the fixpoint. `measure g + 1` units of fuel
always suffice (lemma F2.b, `Fuel.lean`). -/
def review (g : GPathM) : GPathM :=
  reviewFuel (measure g + 1) g

-- ============================================================
-- Filtering (mirror of filter_require! / filter!)
-- ============================================================

/-- Fix `req` as the only visitable map node of its step: every global owner
at that step that projects to a different map node is removed. -/
def filterRequire (g : GPathM) (req : NodeId) : GPathM :=
  { g with
    gowners := g.gowners.filter (fun q => q.id.step != req.step || q.id == req) }

def filterAll (g : GPathM) (reqs : List NodeId) : GPathM :=
  review (reqs.foldl filterRequire g)

-- ============================================================
-- UP (mirror of add_node! / do_up! / do_up_filtering!)
-- ============================================================

def addNode (g : GPathM) (d : NodeId) (title : String) : GPathM :=
  let pid : PathNodeId := { id := d, parent_id := g.map_parent }
  let parentIds :=
    if g.current_step > 0 then (g.line (g.current_step - 1)).map (·.id) else []
  let newNode : PNodeM :=
    { id := pid, title := title, parents := parentIds, sons := [],
      owners := g.gowners }
  let nodes := g.nodes.map (fun n =>
    if parentIds.contains n.id then { n with sons := n.sons ++ [pid] } else n)
  let nodes := nodes ++ [newNode]
  -- all_previous_nodes_are_owners_of_me!: the new id becomes an owner of
  -- every node, including the new node itself.
  let nodes := nodes.map (fun n => { n with owners := n.owners ++ [pid] })
  { nodes := nodes,
    gowners := g.gowners ++ [pid],
    current_step := g.current_step + 1,
    map_parent := some d }

def up (g : GPathM) (d : NodeId) (title : String) : GPathM :=
  if isValid g then addNode g d title else g

def upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String) : GPathM :=
  up (filterAll g reqs) d title

def initSeed (d : NodeId) (title : String) : GPathM :=
  up empty d title

-- ============================================================
-- Join (mirror of do_join!)
-- ============================================================

def mergeNode (a b : PNodeM) : PNodeM :=
  { a with
    parents := a.parents ++ b.parents.filter (fun p => !a.parents.contains p),
    sons := a.sons ++ b.sons.filter (fun s => !a.sons.contains s),
    owners := a.owners ++ b.owners.filter (fun q => !a.owners.contains q) }

def okJoin (g₁ g₂ : GPathM) : Bool :=
  g₁.current_step == g₂.current_step
    && g₁.map_parent == g₂.map_parent
    && isValid g₁ && isValid g₂

/-- Structural union: nodes with the same `PathNodeId` are merged fieldwise,
the rest are concatenated; global owners are unioned. Callers must respect
`okJoin` (the `Reachable.join` constructor does). -/
def join (g₁ g₂ : GPathM) : GPathM :=
  let nodes := g₁.nodes.map (fun n =>
    match g₂.node? n.id with
    | some m => mergeNode n m
    | none => n)
  let nodes := nodes ++ g₂.nodes.filter (fun m => (g₁.node? m.id).isNone)
  { g₁ with
    nodes := nodes,
    gowners := g₁.gowners ++ g₂.gowners.filter (fun q => !g₁.gowners.contains q) }

def doJoin (g₁ g₂ : GPathM) : GPathM :=
  if okJoin g₁ g₂ then join g₁ g₂ else g₁

end GPathM

-- ============================================================
-- Tests: the two 3-variable chains of the book (Figs. 1.14/1.15),
-- their join, and a requirement-directed filter across the join.
-- ============================================================

section Examples

open GPathM

private def nid (s i : Int) : NodeId := { step := s, index := i }

/-- Chain for assignment X=x, Y=y, Z=z over the 3-variable literal block:
value node at even steps, negation node (requiring the value) at odd steps,
fusion node at step 6. -/
private def chainOf (x y z : Int) : GPathM :=
  let g := initSeed (nid 0 x) s!"X={x}"
  let g := upFiltering g [nid 0 x] (nid 1 (1 - x)) s!"!X={1 - x}"
  let g := up g (nid 2 y) s!"Y={y}"
  let g := upFiltering g [nid 2 y] (nid 3 (1 - y)) s!"!Y={1 - y}"
  let g := up g (nid 4 z) s!"Z={z}"
  let g := upFiltering g [nid 4 z] (nid 5 (1 - z)) s!"!Z={1 - z}"
  up g (nid 6 0) "FusionNode"

def run_tests : IO Unit := do
  -- Single chain: 7 steps, one node per step, everyone owns everyone.
  let a := chainOf 0 0 0
  assert! isValid a
  assert! a.current_step == 7
  assert! a.nodes.length == 7
  assert! a.gowners.length == 7
  assert! a.nodes.all (fun n => n.owners.length == 7)

  -- A require that no surviving node matches invalidates the chain.
  let broken := filterAll a [nid 0 1]
  assert! !(isValid broken)

  -- Join of the X=0 and X=1 chains: distinct prefixes (steps 0-2, the step-2
  -- nodes differ by parent id), shared suffix (steps 3-6) merged by id.
  let b := chainOf 1 0 0
  assert! okJoin a b
  let j := join a b
  assert! isValid j
  assert! j.nodes.length == 10
  assert! j.gowners.length == 10
  assert! (j.line 3).length == 1  -- shared: same map parent k2.0

  -- Requirement-directed filter across the join: forcing X=1 prunes the
  -- whole X=0 prefix through the owners cascade and keeps the graph valid.
  let f := filterAll j [nid 0 1]
  assert! isValid f
  assert! f.nodes.length == 7
  assert! (f.line 0).map (·.id.id) == [nid 0 1]

  -- Clause-style UP over the join (requires X=1 and Y=0), the L1 scenario:
  -- the new node's owners at each required step point only at the required
  -- map node.
  let c := upFiltering j [nid 0 1, nid 2 0] (nid 7 3) "or0=100"
  assert! isValid c
  match c.node? { id := nid 7 3, parent_id := some (nid 6 0) } with
  | none => assert! false
  | some clause =>
    assert! (ownersAt clause.owners 0).all (fun q => q.id == nid 0 1)
    assert! (ownersAt clause.owners 2).all (fun q => q.id == nid 2 0)
    assert! !(ownersAt clause.owners 0).isEmpty

  IO.println "All GPathM tests passed!"

#eval run_tests

end Examples

end AbsSat.GraphPath.Model
