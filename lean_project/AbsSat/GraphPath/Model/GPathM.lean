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
  deriving Repr, DecidableEq

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

def unionStep (g : GPathM) (acc : List PathNodeId) (pid : PathNodeId) : List PathNodeId :=
  match g.node? pid with
  | some p => acc ++ p.owners
  | none => acc

theorem unionOwnersOf_eq (g : GPathM) (ids : List PathNodeId) :
    unionOwnersOf g ids = ids.foldl (unionStep g) [] := rfl

theorem mem_unionFold_acc (g : GPathM) (ids : List PathNodeId) :
    ∀ (acc : List PathNodeId) (q : PathNodeId), q ∈ acc → q ∈ ids.foldl (unionStep g) acc := by
  induction ids with
  | nil => intro acc q hq; exact hq
  | cons id rest ih =>
    intro acc q hq
    simp only [List.foldl_cons]
    refine ih _ q ?_
    simp only [unionStep]
    cases g.node? id
    · exact hq
    · exact List.mem_append_left _ hq

theorem mem_unionFold (g : GPathM) (ids : List PathNodeId) :
    ∀ (acc : List PathNodeId) (pid : PathNodeId) (p : PNodeM) (q : PathNodeId),
      pid ∈ ids → g.node? pid = some p → q ∈ p.owners →
      q ∈ ids.foldl (unionStep g) acc := by
  induction ids with
  | nil => intro _ _ _ _ hpid; exact absurd hpid List.not_mem_nil
  | cons id rest ih =>
    intro acc pid p q hpid hp hq
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hpid with rfl | hrest
    · refine mem_unionFold_acc g rest _ q ?_
      simp only [unionStep, hp]
      exact List.mem_append_right _ hq
    · exact ih _ pid p q hrest hp hq

theorem mem_unionFold_rev (g : GPathM) :
    ∀ (ids : List PathNodeId) (acc : List PathNodeId) (q : PathNodeId),
      q ∈ ids.foldl (unionStep g) acc →
      q ∈ acc ∨ ∃ pid ∈ ids, ∃ p, g.node? pid = some p ∧ q ∈ p.owners := by
  intro ids
  induction ids with
  | nil => intro acc q h; exact Or.inl h
  | cons id rest ih =>
    intro acc q h
    simp only [List.foldl_cons] at h
    rcases ih _ q h with hacc | ⟨pid, hpid, p, hp, hq⟩
    · cases hn : g.node? id with
      | none => simp only [unionStep, hn] at hacc; exact Or.inl hacc
      | some p =>
        simp only [unionStep, hn] at hacc
        rcases List.mem_append.mp hacc with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ⟨id, List.mem_cons_self .., p, hn, h2⟩
    · exact Or.inr ⟨pid, List.mem_cons_of_mem _ hpid, p, hp, hq⟩

/-- **And back**: everything in the union is owned by one of the neighbours. -/
theorem exists_owner_of_mem_unionOwnersOf (g : GPathM) (ids : List PathNodeId) (q : PathNodeId)
    (h : q ∈ unionOwnersOf g ids) :
    ∃ pid ∈ ids, ∃ p, g.node? pid = some p ∧ q ∈ p.owners := by
  rcases mem_unionFold_rev g ids [] q h with hnil | hres
  · exact absurd hnil List.not_mem_nil
  · exact hres

/-- An owner of any *existing* neighbour is in the neighbours' union. -/
theorem mem_unionOwnersOf (g : GPathM) (ids : List PathNodeId) (pid : PathNodeId)
    (p : PNodeM) (q : PathNodeId) (hpid : pid ∈ ids) (hp : g.node? pid = some p)
    (hq : q ∈ p.owners) : q ∈ unionOwnersOf g ids :=
  mem_unionFold g ids [] pid p q hpid hp hq

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
def updateAtGo (id : PathNodeId) (f : PNodeM → PNodeM) (nodes : List PNodeM) : List PNodeM :=
  nodes.map (fun n => match n.id == id with | true => f n | false => n)

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

/-- Keep only the links a node's own owners still allow. -/
def relinkSelf (n : PNodeM) : PNodeM :=
  { n with parents := n.parents.filter (fun p => n.owners.contains p),
           sons := n.sons.filter (fun s => n.owners.contains s) }

/-- Put new owners on a node and re-link against them. -/
def relink (ow : List PathNodeId) (n : PNodeM) : PNodeM :=
  relinkSelf { n with owners := ow }

/-- What the unlink does to every node. -/
def unlinkMap (n : PNodeM) (id : PathNodeId) (m : PNodeM) : PNodeM :=
  if m.id == id then
    { m with parents := m.parents.filter (fun p => n.owners.contains p),
             sons := m.sons.filter (fun s => n.owners.contains s) }
  else if n.owners.contains m.id then m
  else { m with parents := m.parents.filter (fun p => p != id),
                sons := m.sons.filter (fun s => s != id) }

/-- **Owners/links coherence** (mirror of `unlink_incompatible!`). Pruning a
node's owners can leave a parent or son that is no longer an owner — a
neighbour propagation has already ruled out. Such a link is stale: no chain
through this node can use it, so it goes, on both sides.

Without this the two ledgers drift: `removeNode` unlinks when a node is
*removed*, but the owners intersections only shrink `owners`. The drift was
measured at 37 stale parent links per ~328k, and the author identified it as a
bug (2026-09-09). Id- and owners-preserving, link-shrinking, so `Pruned` still
holds through it. -/
def unlinkIncompatible (g : GPathM) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some n => { g with nodes := g.nodes.map (unlinkMap n id) }

/-- One `clean_invalid_nodes!` sweep over a snapshot of node ids: intersect
each node's owners with the global owners, unlink what that leaves
incompatible, then drop the node if invalid. -/
def cleanInvalidGo (g : GPathM) : List PathNodeId → GPathM
  | [] => g
  | id :: rest =>
    match g.node? id with
    | none => cleanInvalidGo g rest
    | some d =>
      let gow := g.gowners
      let d := relink (intersectOwners d.owners gow) d
      let g := unlinkIncompatible
        (updateAt g id (fun n => { n with owners := intersectOwners n.owners gow })) id
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
      let d := relink (intersectOwners d.owners uni) d
      let g := unlinkIncompatible
        (updateAt g id (fun n => { n with owners := intersectOwners n.owners uni })) id
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

/-- Bottom-up: owners coherent with the union of the sons' owners, from
`current_step-2` down to **0**. The lower bound is 0, not 1: a step-0 node has
sons, and the parents pass' lower bound of 1 (a step-0 node has no parents) does
not transfer. See `verificacion_inseguridad_autor_v48.md`. -/
def reviewSons (g : GPathM) : GPathM :=
  reviewSteps g (·.sons) (intRange 0 (g.current_step - 2)).reverse

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

/-- **Shift of the identifier window** — Julia's `Alias.shift_path_id`:
`(gp, p, last) + d ↦ (p, last, d)`. The new identifier keeps two levels of the
branch that reaches it, which is what lets a *pair* of adjacent path nodes carry
*three* map ids. -/
def shiftPid (last : PathNodeId) (d : NodeId) : PathNodeId :=
  { id := d, parent_id := some last.id, gparent_id := last.parent_id }

/-- The ids of the last row — the candidate parents of the row `UP` is about to
add. Empty before anything has been visited. -/
def newParents (g : GPathM) : List PathNodeId :=
  if g.current_step > 0 then (g.line (g.current_step - 1)).map (·.id) else []

/-- Deduplication, written so that both `mem` and `Nodup` are one induction.
`List.eraseDups` would do the same job but core proves neither about it. -/
def dedupPids : List PathNodeId → List PathNodeId
  | [] => []
  | a :: as => a :: (dedupPids as).filter (fun x => x != a)

theorem mem_dedupPids : ∀ (l : List PathNodeId) (a : PathNodeId), a ∈ dedupPids l ↔ a ∈ l := by
  intro l
  induction l with
  | nil => intro a; exact Iff.rfl
  | cons b bs ih =>
    intro a
    simp only [dedupPids, List.mem_cons, List.mem_filter, ih, bne_iff_ne, ne_eq]
    constructor
    · rintro (rfl | ⟨h, _⟩)
      · exact Or.inl rfl
      · exact Or.inr h
    · rintro (rfl | h)
      · exact Or.inl rfl
      · by_cases hab : a = b
        · exact Or.inl hab
        · exact Or.inr ⟨h, hab⟩

theorem nodup_filter_aux {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons b bs ih =>
    intro h
    obtain ⟨hb, hbs⟩ := List.nodup_cons.mp h
    rw [List.filter_cons]
    split
    · exact List.nodup_cons.mpr ⟨fun hc => hb ((List.mem_filter.mp hc).1), ih hbs⟩
    · exact ih hbs

theorem nodup_dedupPids : ∀ (l : List PathNodeId), (dedupPids l).Nodup := by
  intro l
  induction l with
  | nil => exact List.nodup_nil
  | cons b bs ih =>
    simp only [dedupPids]
    refine List.nodup_cons.mpr ⟨?_, nodup_filter_aux _ ih⟩
    intro hc
    have := (List.mem_filter.mp hc).2
    simp at this

/-- **The identifiers of the row `UP` adds**: one per identifier the window shift
gives to the last row (`group_parents_by_shifted_id`). Nodes of the last row
that agree on *both* their map id and their parent's shift to the same
identifier and are merged into one node with several parents. Before anything
has been visited, the single root id. -/
def newRowIds (g : GPathM) (d : NodeId) : List PathNodeId :=
  if g.current_step > 0 then dedupPids ((newParents g).map (fun q => shiftPid q d))
  else [{ id := d, parent_id := none, gparent_id := none }]

/-- The nodes of the last row that shift to `pid`: exactly its parents. -/
def rowParents (g : GPathM) (d : NodeId) (pid : PathNodeId) : List PathNodeId :=
  (newParents g).filter (fun q => shiftPid q d == pid)

/-- **The owners of a new row node**: what its parents own, cut down to what is
still globally alive, and itself (`create_node_from_parents!`). It is *not*
`gowners`: a row node inherits only its own parents' ownership, so the `UP` is
by itself a step of pruning.

The cut is a plain `filter` against `gowners`, not `intersectOwners`. The two
agree on every state the machine builds — `intersectOwners` differs only by
keeping entries at steps where `gowners` says nothing, and a state whose
`gowners` is silent at a step below `current_step` is invalid, which is exactly
when `up` does not fire (and above `current_step` there are no owners to keep,
by `steps_below_current`). Choosing the plain filter buys
`rowOwners_mem_gowners_or_self` with no validity hypothesis, which several dozen
downstream lemmas would otherwise have to carry. -/
def rowOwners (g : GPathM) (d : NodeId) (pid : PathNodeId) : List PathNodeId :=
  (unionOwnersOf g (rowParents g d pid)).filter (fun q => g.gowners.contains q) ++ [pid]

def rowNode (g : GPathM) (d : NodeId) (title : String) (pid : PathNodeId) : PNodeM :=
  { id := pid, title := title, parents := rowParents g d pid, sons := [],
    owners := rowOwners g d pid }

def newRow (g : GPathM) (d : NodeId) (title : String) : List PNodeM :=
  (newRowIds g d).map (rowNode g d title)

/-- The row ids a pre-existing node becomes a parent of. -/
def gainedSons (g : GPathM) (d : NodeId) (n : PNodeM) : List PathNodeId :=
  (newRowIds g d).filter (fun pid => (rowParents g d pid).contains n.id)

/-- The row ids that own a pre-existing node — and so, by the symmetry of the
tables, that it gains as owners (`its_owners_are_owned_by_me!`). A node no row
node owns gains nothing, and the next review will find it without an owner at
the new step and drop it. -/
def gainedOwners (g : GPathM) (d : NodeId) (n : PNodeM) : List PathNodeId :=
  (newRowIds g d).filter (fun pid => (rowOwners g d pid).contains n.id)

def upSons (g : GPathM) (d : NodeId) (n : PNodeM) : PNodeM :=
  { n with sons := n.sons ++ gainedSons g d n }

def upOwners (g : GPathM) (d : NodeId) (n : PNodeM) : PNodeM :=
  { n with owners := n.owners ++ gainedOwners g d n }

/-- What `addNode` does to every pre-existing node. -/
def upMap (g : GPathM) (d : NodeId) (n : PNodeM) : PNodeM := upOwners g d (upSons g d n)

/-- **The `UP`** (`add_row!`). It adds a whole row, not a node: one node per
identifier the window shift gives to the last row. With a window of two every
node of the last row shifts to the same identifier (they all carry `map_parent`
— that is `ParentId.TL`), so the row is the single node the machine added before
the window existed. The name is kept because every lemma downstream is
`*_addNode`. -/
def addNode (g : GPathM) (d : NodeId) (title : String) : GPathM :=
  { nodes := g.nodes.map (upMap g d) ++ newRow g d title,
    gowners := g.gowners ++ newRowIds g d,
    current_step := g.current_step + 1,
    map_parent := some d }

-- ============================================================
-- Shape of the row (the lemmas every consumer of `addNode` needs)
-- ============================================================

theorem upMap_id (g : GPathM) (d : NodeId) (n : PNodeM) : (upMap g d n).id = n.id := rfl

theorem upMap_parents (g : GPathM) (d : NodeId) (n : PNodeM) :
    (upMap g d n).parents = n.parents := rfl

theorem upMap_sons (g : GPathM) (d : NodeId) (n : PNodeM) :
    (upMap g d n).sons = n.sons ++ gainedSons g d n := rfl

theorem upMap_owners (g : GPathM) (d : NodeId) (n : PNodeM) :
    (upMap g d n).owners = n.owners ++ gainedOwners g d n := rfl

theorem addNode_nodes (g : GPathM) (d : NodeId) (title : String) :
    (addNode g d title).nodes = g.nodes.map (upMap g d) ++ newRow g d title := rfl

theorem addNode_gowners (g : GPathM) (d : NodeId) (title : String) :
    (addNode g d title).gowners = g.gowners ++ newRowIds g d := rfl

theorem addNode_current (g : GPathM) (d : NodeId) (title : String) :
    (addNode g d title).current_step = g.current_step + 1 := rfl


/-- Every identifier of the row carries the map id the `UP` visited. -/
theorem mapId_of_mem_newRowIds (g : GPathM) (d : NodeId) (pid : PathNodeId)
    (h : pid ∈ newRowIds g d) : pid.id = d := by
  unfold newRowIds at h
  split at h
  · obtain ⟨q, _, hq⟩ := List.mem_map.mp ((mem_dedupPids _ _).mp h)
    rw [← hq]; rfl
  · rcases List.mem_singleton.mp h with rfl; rfl

theorem rowNode_id (g : GPathM) (d : NodeId) (title : String) (pid : PathNodeId) :
    (rowNode g d title pid).id = pid := rfl

theorem rowNode_owners (g : GPathM) (d : NodeId) (title : String) (pid : PathNodeId) :
    (rowNode g d title pid).owners = rowOwners g d pid := rfl

theorem rowNode_parents (g : GPathM) (d : NodeId) (title : String) (pid : PathNodeId) :
    (rowNode g d title pid).parents = rowParents g d pid := rfl

theorem rowNode_sons (g : GPathM) (d : NodeId) (title : String) (pid : PathNodeId) :
    (rowNode g d title pid).sons = [] := rfl

/-- The nodes of the row are exactly the row identifiers. -/
theorem mem_newRow_iff (g : GPathM) (d : NodeId) (title : String) (m : PNodeM) :
    m ∈ newRow g d title ↔ ∃ pid ∈ newRowIds g d, m = rowNode g d title pid := by
  constructor
  · intro h
    obtain ⟨pid, hpid, hm⟩ := List.mem_map.mp h
    exact ⟨pid, hpid, hm.symm⟩
  · rintro ⟨pid, hpid, rfl⟩
    exact List.mem_map.mpr ⟨pid, hpid, rfl⟩

/-- A node of the row sits at the new step. -/
theorem newRow_step (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (m : PNodeM) (hm : m ∈ newRow g d title) :
    m.id.id.step = g.current_step := by
  obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title m).mp hm
  rw [rowNode_id, mapId_of_mem_newRowIds g d pid hpid]
  exact hd

/-- **Every row identifier is the shift of a node of the last row.** -/
theorem exists_shift_of_mem_newRowIds (g : GPathM) (d : NodeId) (pid : PathNodeId)
    (hpos : 0 < g.current_step) (h : pid ∈ newRowIds g d) :
    ∃ q ∈ newParents g, pid = shiftPid q d := by
  unfold newRowIds at h
  rw [if_pos hpos] at h
  obtain ⟨q, hq, hqp⟩ := List.mem_map.mp ((mem_dedupPids _ pid).mp h)
  exact ⟨q, hq, hqp.symm⟩

/-- A row identifier above step 0 is never a root. -/
theorem parent_id_ne_none_of_mem_newRowIds (g : GPathM) (d : NodeId) (pid : PathNodeId)
    (hpos : 0 < g.current_step) (h : pid ∈ newRowIds g d) : pid.parent_id ≠ none := by
  obtain ⟨q, _, rfl⟩ := exists_shift_of_mem_newRowIds g d pid hpos h
  show (some q.id : Option NodeId) ≠ none
  simp

/-- **The row has no repeated identifier.** -/
theorem nodup_newRowIds (g : GPathM) (d : NodeId) : (newRowIds g d).Nodup := by
  unfold newRowIds
  split
  · exact nodup_dedupPids _
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- The seed row is a single root. -/
theorem newRowIds_of_zero (g : GPathM) (d : NodeId) (hz : ¬ 0 < g.current_step) :
    newRowIds g d = [{ id := d, parent_id := none, gparent_id := none }] := by
  unfold newRowIds; rw [if_neg hz]

/-- What an old node gains is a row identifier. -/
theorem gainedOwners_subset (g : GPathM) (d : NodeId) (n : PNodeM) (pid : PathNodeId)
    (h : pid ∈ gainedOwners g d n) : pid ∈ newRowIds g d := (List.mem_filter.mp h).1

theorem gainedSons_subset (g : GPathM) (d : NodeId) (n : PNodeM) (pid : PathNodeId)
    (h : pid ∈ gainedSons g d n) : pid ∈ newRowIds g d := (List.mem_filter.mp h).1

/-- A parent of a row node is a node of the last row. -/
theorem rowParents_subset (g : GPathM) (d : NodeId) (pid q : PathNodeId)
    (h : q ∈ rowParents g d pid) : q ∈ newParents g := (List.mem_filter.mp h).1

/-- **A candidate parent of the row sits on the top old step.** -/
theorem step_of_mem_newParents (g : GPathM) (hpos : 0 < g.current_step) (q : PathNodeId)
    (h : q ∈ newParents g) : q.id.step = g.current_step - 1 := by
  unfold newParents at h
  rw [if_pos hpos] at h
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h
  exact eq_of_beq (List.mem_filter.mp hn).2

/-- A parent of a row node shifts to it. -/
theorem shiftPid_of_mem_rowParents (g : GPathM) (d : NodeId) (pid q : PathNodeId)
    (h : q ∈ rowParents g d pid) : shiftPid q d = pid :=
  eq_of_beq (List.mem_filter.mp h).2

/-- A node of the last row shifts into the row. -/
theorem mem_newRowIds_of_mem_newParents (g : GPathM) (d : NodeId) (q : PathNodeId)
    (hpos : 0 < g.current_step) (h : q ∈ newParents g) : shiftPid q d ∈ newRowIds g d := by
  unfold newRowIds
  rw [if_pos hpos]
  exact (mem_dedupPids _ _).mpr (List.mem_map_of_mem h)

/-- And it is then one of the parents of the node it shifts to. -/
theorem mem_rowParents_of_mem_newParents (g : GPathM) (d : NodeId) (q : PathNodeId)
    (h : q ∈ newParents g) : q ∈ rowParents g d (shiftPid q d) :=
  List.mem_filter.mpr ⟨h, beq_iff_eq.mpr rfl⟩

/-- Membership in `intRange 0 (cs - 1)`. -/
theorem mem_intRange_zero (k cs : Int) (h0 : 0 ≤ k) (h1 : k < cs) :
    k ∈ intRange 0 (cs - 1) := by
  unfold intRange
  refine List.mem_map.mpr ⟨k.toNat, List.mem_range.mpr ?_, ?_⟩
  · omega
  · show (0 : Int) + Int.ofNat k.toNat = k
    rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg h0]
    omega

/-- **A row node's owner is a global owner, or the node itself.** -/
theorem rowOwners_mem_gowners_or_self (g : GPathM) (d : NodeId) (pid q : PathNodeId)
    (hq : q ∈ rowOwners g d pid) : q ∈ g.gowners ∨ q = pid := by
  unfold rowOwners at hq
  rcases List.mem_append.mp hq with hl | hr
  · exact Or.inl (by simpa using (List.mem_filter.mp hl).2)
  · exact Or.inr (List.mem_singleton.mp hr)

/-- A row node owns itself. -/
theorem self_mem_rowOwners (g : GPathM) (d : NodeId) (pid : PathNodeId) :
    pid ∈ rowOwners g d pid :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- **What a row node inherits.** Anything it owns other than itself is owned by
one of its parents *and* still globally alive. -/
theorem mem_rowOwners_iff (g : GPathM) (d : NodeId) (pid q : PathNodeId) :
    q ∈ rowOwners g d pid ↔
      (q ∈ unionOwnersOf g (rowParents g d pid) ∧ q ∈ g.gowners) ∨ q = pid := by
  unfold rowOwners
  rw [List.mem_append]
  constructor
  · rintro (hl | hr)
    · exact Or.inl ⟨(List.mem_filter.mp hl).1, by simpa using (List.mem_filter.mp hl).2⟩
    · exact Or.inr (List.mem_singleton.mp hr)
  · rintro (⟨h1, h2⟩ | rfl)
    · exact Or.inl (List.mem_filter.mpr ⟨h1, by simpa using h2⟩)
    · exact Or.inr (List.mem_singleton.mpr rfl)

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

  -- Join of the X=0 and X=1 chains. **Where the window shows.** With a window
  -- of two the two branches merged at step 3 (same map id, same map parent);
  -- with three they stay apart one step longer, because their step-3
  -- identifiers still disagree on the grandparent, and merge at step 4.
  let b := chainOf 1 0 0
  assert! okJoin a b
  let j := join a b
  assert! isValid j
  assert! j.nodes.length == 11
  assert! j.gowners.length == 11
  assert! (j.line 3).length == 2  -- apart: the grandparent still tells them apart
  assert! (j.line 4).length == 1  -- merged: window (k4.z, k3.1, k2.0) agrees

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
  match c.node? { id := nid 7 3, parent_id := some (nid 6 0), gparent_id := some (nid 5 1) } with
  | none => assert! false
  | some clause =>
    assert! (ownersAt clause.owners 0).all (fun q => q.id == nid 0 1)
    assert! (ownersAt clause.owners 2).all (fun q => q.id == nid 2 0)
    assert! !(ownersAt clause.owners 0).isEmpty

  IO.println "All GPathM tests passed!"

#eval run_tests

end Examples

end AbsSat.GraphPath.Model
