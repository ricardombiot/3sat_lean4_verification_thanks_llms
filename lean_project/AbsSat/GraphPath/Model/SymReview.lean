-- lean_project/AbsSat/GraphPath/Model/SymReview.lean
import AbsSat.GraphPath.Model.Reader

/-!
# The symmetric review

v63 caught `reviewNode` breaking ownership symmetry: 236 violations in a single
coherence pass, on the reader's own first step. This module asks whether the
review can be made symmetric, and what that buys.

## The idea

When a review drops `q` from `owners(p)`, what it is asserting is *no solution
goes through both `p` and `q`*. That sentence is symmetric, but the machine only
writes it down on one side. `symmetrize g id` writes down the other: after
`owners(id)` has shrunk, every node `m` that is no longer among `id`'s owners
loses `id` from its own table.

It cannot lose a solution. By the conservation law, if a solution's chain goes
through `id` and `m`, then `m ∈ owners(id)`; so for any `m` outside `owners(id)`
no sound chain uses the pair, and removing the mirror entry cannot break one
(`ChainSound_symmetrize` below).

## Where it goes

After **every** `updateAt` that shrinks one table — in the coherence review
(`reviewNodeSym`) and in the invalid sweep (`cleanInvalidGoSym`) — and before
the `unlinkIncompatible` that already follows it. That unlink removes exactly the
links the mirror step makes stale: those between `id` and nodes outside
`owners(id)`.

## The reader's pin

`pinOwners g r` is the reading as the author describes it: choosing `r` is
assuming all of `r`'s owners chosen, so the global owners become
`gowners ∩ owners(r)` — every step at once, not only `r`'s. The symmetric review
then does the cleaning: intersecting every table with the selected owners.

## What is proved here

* `OwnSymmetric_symmetrize_updateAt` — shrinking one table and mirroring keeps
  symmetry, with **no hypothesis** beyond symmetry itself (not
  `NodesAreGowners`, not validity, not full length).
* From it: `OwnSymmetric_reviewSym`, `OwnSymmetric_filterAllSym`,
  `OwnSymmetric_readStepSym`, and `OwnSymmetric_read` — **a read that starts
  symmetric is symmetric at every step**.
* `ChainSound_symmetrize` — the mirror step loses no solution; and through the
  whole review, `ChainSound_reviewSym`.
* `ChainSound_pinOwners`, `ChainSound_readStepSym` — **a reading step keeps
  every solution through the node it reads**.

## What is measured (`lake exe cnfmap`, `SymCampaign.lean`)

* `--symreview`: same verdicts as the original on 100 formulas, 0 lost
  solutions, 0 zombie verdicts; the original machine produces 132 symmetry
  violations along its runs and the symmetric one 0, joins and `addNode`
  included; 0 `PickValid` failures in 5,260 choices; every read certified.
* `--pinexact`: **choosing `r` keeps exactly `owners(r)`** — 0 of 195,167
  owner-nodes killed and 0 survivors outside, over 6,244 choices.
* `--triangle`: at every full-length state, every co-owned pair has a common
  owner at every step (0 gaps in ~197k pairs); at partial length, 9 gaps in
  over a million pairs, in both machines.
* `--selfsupport`: inside `owners(r)` every node keeps a parent and a son
  (0 failures), but ~1–2 % of table entries are not carried by such a link — so
  the tables do shrink after a pin, even though no node dies.

What is **not** proved: that choosing a node never kills one of its owners.
That is the no-zombie wall in its sharpest form, and it is where a proof now has
to go.
-/

namespace AbsSat.GraphPath.Model.SymReview

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- Definitions
-- ============================================================

/-- The mirror step: what one node's table no longer contains, it no longer
appears in. -/
def symMap (d : PNodeM) (id : PathNodeId) (m : PNodeM) : PNodeM :=
  if m.id == id || d.owners.contains m.id then m
  else { m with owners := m.owners.filter (fun q => q != id) }

def symmetrize (g : GPathM) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some d => { g with nodes := g.nodes.map (symMap d id) }

/-- `reviewNode`, with the mirror step between the intersection and the unlink. -/
def reviewNodeSym (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some d =>
    if isValidNode g d then
      let uni := unionOwnersOf g (nb d)
      let d := relink (intersectOwners d.owners uni) d
      let g := unlinkIncompatible (symmetrize
        (updateAt g id (fun n => { n with owners := intersectOwners n.owners uni })) id) id
      if isValidNode g d then g else removeNode g id
    else
      removeNode g id

/-- `cleanInvalidGo`, with the mirror step. -/
def cleanInvalidGoSym (g : GPathM) : List PathNodeId → GPathM
  | [] => g
  | id :: rest =>
    match g.node? id with
    | none => cleanInvalidGoSym g rest
    | some d =>
      let gow := g.gowners
      let d := relink (intersectOwners d.owners gow) d
      let g := unlinkIncompatible (symmetrize
        (updateAt g id (fun n => { n with owners := intersectOwners n.owners gow })) id) id
      let g := if isValidNode g d then g else removeNode g id
      cleanInvalidGoSym g rest

def cleanInvalidSym (g : GPathM) : GPathM :=
  cleanInvalidGoSym g (g.nodes.map (·.id))

def reviewLineSym (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int) : GPathM :=
  ((g.line k).map (·.id)).foldl (fun g id => reviewNodeSym g nb id) g

def reviewStepsSym (g : GPathM) (nb : PNodeM → List PathNodeId) : List Int → GPathM
  | [] => g
  | k :: ks =>
    if isValid g then reviewStepsSym (reviewLineSym g nb k) nb ks else g

def reviewParentsSym (g : GPathM) : GPathM :=
  reviewStepsSym g (·.parents) (intRange 1 (g.current_step - 1))

def reviewSonsSym (g : GPathM) : GPathM :=
  reviewStepsSym g (·.sons) (intRange 0 (g.current_step - 2)).reverse

def reviewPassSym (g : GPathM) : GPathM :=
  reviewSonsSym (reviewParentsSym (cleanInvalidSym g))

def reviewFuelSym : Nat → GPathM → GPathM
  | 0, g => g
  | fuel + 1, g =>
    if isValid g then
      let g' := reviewPassSym g
      if measure g' < measure g then reviewFuelSym fuel g' else g'
    else
      g

def reviewSym (g : GPathM) : GPathM :=
  reviewFuelSym (measure g + 1) g

def filterAllSym (g : GPathM) (reqs : List NodeId) : GPathM :=
  reviewSym (reqs.foldl filterRequire g)

def upFilteringSym (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String) : GPathM :=
  up (filterAllSym g reqs) d title

/-- The author's pin: choosing `r` assumes every owner of `r` chosen. -/
def pinOwners (g : GPathM) (r : PathNodeId) : GPathM :=
  match g.node? r with
  | none => g
  | some n => { g with gowners := g.gowners.filter (fun q => n.owners.contains q) }

/-- One reading step: pin by owners, then clean symmetrically. -/
def readStepSym (g : GPathM) (r : PathNodeId) : GPathM :=
  reviewSym (pinOwners g r)


-- ============================================================
-- Symmetry is carried by every symmetric operation, unconditionally
-- ============================================================

/-- `node?` through any id-preserving map of the node list. -/
theorem node?_of_map (g g' : GPathM) (F : PNodeM → PNodeM) (hF : ∀ n, (F n).id = n.id)
    (hnodes : g'.nodes = g.nodes.map F) (p : PathNodeId) :
    g'.node? p = (g.node? p).map F := by
  unfold node?
  rw [hnodes, List.find?_map]
  have : ((fun n : PNodeM => n.id == p) ∘ F) = (fun n => n.id == p) := by
    funext x; simp only [Function.comp_apply, hF]
  rw [this]

theorem symMap_id (d : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (symMap d id m).id = m.id := by
  unfold symMap; split <;> rfl

/-- The updated node, as a function. -/
def updMap (id : PathNodeId) (f : PNodeM → PNodeM) (n : PNodeM) : PNodeM :=
  match n.id == id with | true => f n | false => n

theorem updMap_id (id : PathNodeId) (f : PNodeM → PNodeM) (hf : ∀ n, (f n).id = n.id)
    (n : PNodeM) : (updMap id f n).id = n.id := by
  unfold updMap; split
  · exact hf n
  · rfl

theorem updateAt_nodes (g : GPathM) (id : PathNodeId) (f : PNodeM → PNodeM) :
    (updateAt g id f).nodes = g.nodes.map (updMap id f) := rfl

/-- **The core step.** Shrink one node's table, then mirror: symmetry survives,
with no hypothesis beyond symmetry itself. -/
theorem OwnSymmetric_symmetrize_updateAt (g : GPathM) (id : PathNodeId)
    (f : PNodeM → PNodeM) (hfid : ∀ n, (f n).id = n.id)
    (hfown : ∀ n, ∀ q ∈ (f n).owners, q ∈ n.owners)
    (h : Threaded.OwnSymmetric g) :
    Threaded.OwnSymmetric (symmetrize (updateAt g id f) id) := by
  have hU := updMap_id id f hfid
  have hg1 : ∀ p, (updateAt g id f).node? p = (g.node? p).map (updMap id f) :=
    node?_of_map g _ _ hU (updateAt_nodes g id f)
  cases hid : g.node? id with
  | none =>
    have hid1 : (updateAt g id f).node? id = none := by rw [hg1, hid]; rfl
    have hsym : symmetrize (updateAt g id f) id = updateAt g id f := by
      simp only [symmetrize, hid1]
    rw [hsym]
    refine Reader.OwnSymmetric_of_ownersEq g _ ?_ h
    intro p n' hp
    rw [hg1] at hp
    cases hpn : g.node? p with
    | none => rw [hpn] at hp; cases hp
    | some n =>
      rw [hpn] at hp
      injection hp with hp
      have hne : n.id ≠ id := by
        intro he
        have := node?_id_eq g p n hpn
        rw [← this, he] at hpn
        rw [hid] at hpn; cases hpn
      refine ⟨n, rfl, ?_⟩
      rw [← hp]
      unfold updMap
      rw [show (n.id == id) = false from by simp [hne]]
  | some d =>
    have hdid : d.id = id := node?_id_eq g id d hid
    have hd1 : (updateAt g id f).node? id = some (updMap id f d) := by rw [hg1, hid]; rfl
    have hud : updMap id f d = f d := by
      unfold updMap; rw [show (d.id == id) = true from beq_iff_eq.mpr hdid]
    have hnodes : (symmetrize (updateAt g id f) id).nodes
        = (updateAt g id f).nodes.map (symMap (updMap id f d) id) := by
      simp only [symmetrize, hd1]
    have hfin : ∀ p, (symmetrize (updateAt g id f) id).node? p
        = ((g.node? p).map (updMap id f)).map (symMap (updMap id f d) id) := by
      intro p
      rw [node?_of_map _ _ _ (symMap_id _ id) hnodes p, hg1]
    rw [hud] at hfin
    -- the owners of a surviving node, read off its original
    have hown : ∀ p n'', (symmetrize (updateAt g id f) id).node? p = some n'' →
        ∃ n, g.node? p = some n ∧ n.id = p ∧
          (p = id → n''.owners = (f n).owners) ∧
          (p ≠ id → (p ∈ (f d).owners → n''.owners = n.owners) ∧
                    (p ∉ (f d).owners → n''.owners = n.owners.filter (fun q => q != id))) := by
      intro p n'' hp
      rw [hfin] at hp
      cases hpn : g.node? p with
      | none => rw [hpn] at hp; cases hp
      | some n =>
        rw [hpn] at hp
        injection hp with hp
        have hnid : n.id = p := node?_id_eq g p n hpn
        refine ⟨n, rfl, hnid, ?_, ?_⟩
        · intro hpe
          rw [← hp]
          have hb : (n.id == id) = true := beq_iff_eq.mpr (hnid.trans hpe)
          have hun : updMap id f n = f n := by unfold updMap; rw [hb]
          rw [hun]; unfold symMap
          rw [if_pos (by rw [hfid, hb]; rfl)]
        · intro hpe
          have hb : (n.id == id) = false := by
            cases hc : n.id == id with
            | false => rfl
            | true => exact absurd ((beq_iff_eq.mp hc).symm.trans hnid |>.symm) hpe
          have hun : updMap id f n = n := by unfold updMap; rw [hb]
          constructor
          · intro hin
            rw [← hp, hun]; unfold symMap
            have hc : (f d).owners.contains n.id = true := by
              rw [hnid]; exact List.elem_eq_true_of_mem hin
            rw [if_pos (by rw [hc]; simp)]
          · intro hout
            rw [← hp, hun]; unfold symMap
            have hc : (f d).owners.contains n.id = false := by
              cases hcc : (f d).owners.contains n.id with
              | false => rfl
              | true => exact absurd (hnid ▸ List.mem_of_elem_eq_true hcc) hout
            rw [if_neg (by rw [hb, hc]; simp)]
    intro p n'' q m'' hp hq hqn
    obtain ⟨n, hn, hnid, hn1, hn2⟩ := hown p n'' hp
    obtain ⟨m, hm, hmid, hm1, hm2⟩ := hown q m'' hq
    if hpe : p = id then
      if hqe : q = id then
        subst hpe; subst hqe
        -- same node
        have : n'' = m'' := by rw [hp] at hq; injection hq
        rw [← this]; exact hqn
      else
        -- p = id, q ≠ id: q is in the shrunk table
        have hqf : q ∈ (f n).owners := by rw [← hn1 hpe]; exact hqn
        have hnd : n = d := by rw [hpe] at hn; rw [hn] at hid; injection hid
        rw [hnd] at hqf
        rw [(hm2 hqe).1 hqf]
        have hqd : q ∈ d.owners := hfown d q hqf
        rw [hpe]
        exact h id d q m hid hm hqd
    else
      if hqe : q = id then
        -- p ≠ id, q = id: p must be in the shrunk table, else id was filtered out
        have hmd : m = d := by rw [hqe] at hm; rw [hm] at hid; injection hid
        rw [hm1 hqe, hmd]
        if hin : p ∈ (f d).owners then exact hin
        else
          exfalso
          rw [(hn2 hpe).2 hin, hqe] at hqn
          have := (List.mem_filter.mp hqn).2
          simp at this
      else
        -- neither is id
        have hqn0 : q ∈ n.owners := by
          if hin : p ∈ (f d).owners then rw [← (hn2 hpe).1 hin]; exact hqn
          else rw [(hn2 hpe).2 hin] at hqn; exact (List.mem_filter.mp hqn).1
        have hpm : p ∈ m.owners := h p n q m hn hm hqn0
        if hin : q ∈ (f d).owners then rw [(hm2 hqe).1 hin]; exact hpm
        else
          rw [(hm2 hqe).2 hin]
          exact List.mem_filter.mpr ⟨hpm, by simp [hpe]⟩


theorem OwnSymmetric_unlinkIncompatible (g : GPathM) (id : PathNodeId)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (unlinkIncompatible g id) :=
  Reader.OwnSymmetric_of_ownersEq _ _ (Reader.ownersEq_unlinkIncompatible g id) h

theorem OwnSymmetric_removeNode (g : GPathM) (id : PathNodeId)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (removeNode g id) :=
  Reader.OwnSymmetric_of_ownersEq _ _ (Reader.ownersEq_removeNode g id) h

/-- The step both symmetric sweeps take: intersect one table with some list,
mirror, unlink. -/
theorem OwnSymmetric_symStep (g : GPathM) (id : PathNodeId) (B : List PathNodeId)
    (h : Threaded.OwnSymmetric g) :
    Threaded.OwnSymmetric (unlinkIncompatible (symmetrize
      (updateAt g id (fun n => { n with owners := intersectOwners n.owners B })) id) id) :=
  OwnSymmetric_unlinkIncompatible _ id
    (OwnSymmetric_symmetrize_updateAt g id _ (fun _ => rfl)
      (fun _ _ hq => (List.mem_filter.mp hq).1) h)

theorem OwnSymmetric_reviewNodeSym (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) (h : Threaded.OwnSymmetric g) :
    Threaded.OwnSymmetric (reviewNodeSym g nb id) := by
  simp only [reviewNodeSym]
  split
  · exact h
  · next d _ =>
    split
    · have h₁ := OwnSymmetric_symStep g id (unionOwnersOf g (nb d)) h
      split
      · exact h₁
      · exact OwnSymmetric_removeNode _ id h₁
    · exact OwnSymmetric_removeNode g id h

theorem OwnSymmetric_foldl_reviewNodeSym (nb : PNodeM → List PathNodeId) :
    ∀ (ids : List PathNodeId) (g : GPathM), Threaded.OwnSymmetric g →
      Threaded.OwnSymmetric (ids.foldl (fun g id => reviewNodeSym g nb id) g) := by
  intro ids
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    exact ih _ (OwnSymmetric_reviewNodeSym g nb id h)

theorem OwnSymmetric_reviewLineSym (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (reviewLineSym g nb k) :=
  OwnSymmetric_foldl_reviewNodeSym nb _ g h

theorem OwnSymmetric_reviewStepsSym (nb : PNodeM → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathM), Threaded.OwnSymmetric g →
      Threaded.OwnSymmetric (reviewStepsSym g nb ks) := by
  intro ks
  induction ks with
  | nil => intro g h; exact h
  | cons k rest ih =>
    intro g h
    simp only [reviewStepsSym]
    split
    · exact ih _ (OwnSymmetric_reviewLineSym g nb k h)
    · exact h

theorem OwnSymmetric_cleanInvalidGoSym :
    ∀ (ids : List PathNodeId) (g : GPathM), Threaded.OwnSymmetric g →
      Threaded.OwnSymmetric (cleanInvalidGoSym g ids) := by
  intro ids
  induction ids with
  | nil => intro g h; exact h
  | cons id rest ih =>
    intro g h
    simp only [cleanInvalidGoSym]
    split
    · exact ih g h
    · have h₁ := OwnSymmetric_symStep g id g.gowners h
      split
      · exact ih _ h₁
      · exact ih _ (OwnSymmetric_removeNode _ id h₁)

theorem OwnSymmetric_reviewPassSym (g : GPathM) (h : Threaded.OwnSymmetric g) :
    Threaded.OwnSymmetric (reviewPassSym g) :=
  OwnSymmetric_reviewStepsSym _ _ _
    (OwnSymmetric_reviewStepsSym _ _ _ (OwnSymmetric_cleanInvalidGoSym _ g h))

theorem OwnSymmetric_reviewFuelSym :
    ∀ (fuel : Nat) (g : GPathM), Threaded.OwnSymmetric g →
      Threaded.OwnSymmetric (reviewFuelSym fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [reviewFuelSym]
    split
    · split
      · exact ih _ (OwnSymmetric_reviewPassSym g h)
      · exact OwnSymmetric_reviewPassSym g h
    · exact h

/-- **The symmetric review keeps ownership symmetric.** No hypothesis but
symmetry itself: not `NodesAreGowners`, not validity, not full length. -/
theorem OwnSymmetric_reviewSym (g : GPathM) (h : Threaded.OwnSymmetric g) :
    Threaded.OwnSymmetric (reviewSym g) :=
  OwnSymmetric_reviewFuelSym _ g h

theorem OwnSymmetric_foldl_filterRequire :
    ∀ (reqs : List NodeId) (g : GPathM), Threaded.OwnSymmetric g →
      Threaded.OwnSymmetric (reqs.foldl filterRequire g) := by
  intro reqs
  induction reqs with
  | nil => intro g h; exact h
  | cons r rest ih =>
    intro g h
    exact ih _ (Reader.OwnSymmetric_filterRequire g r h)

theorem OwnSymmetric_filterAllSym (g : GPathM) (reqs : List NodeId)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (filterAllSym g reqs) :=
  OwnSymmetric_reviewSym _ (OwnSymmetric_foldl_filterRequire reqs g h)

/-- The owners-pin touches the global owners only. -/
theorem OwnSymmetric_pinOwners (g : GPathM) (r : PathNodeId)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (pinOwners g r) := by
  unfold pinOwners
  split
  · exact h
  · exact fun p n q m hp hq hqn => h p n q m hp hq hqn

/-- **One reading step keeps ownership symmetric** — pin by owners, clean
symmetrically. So a read that starts symmetric is symmetric at every step, which
is what v63 measured the original reader not to be. -/
theorem OwnSymmetric_readStepSym (g : GPathM) (r : PathNodeId)
    (h : Threaded.OwnSymmetric g) : Threaded.OwnSymmetric (readStepSym g r) :=
  OwnSymmetric_reviewSym _ (OwnSymmetric_pinOwners g r h)

/-- Any sequence of reading steps. -/
theorem OwnSymmetric_read (rs : List PathNodeId) :
    ∀ g : GPathM, Threaded.OwnSymmetric g →
      Threaded.OwnSymmetric (rs.foldl readStepSym g) := by
  induction rs with
  | nil => intro g h; exact h
  | cons r rest ih => intro g h; exact ih _ (OwnSymmetric_readStepSym g r h)

/-- info: 'AbsSat.GraphPath.Model.SymReview.OwnSymmetric_symmetrize_updateAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_symmetrize_updateAt

/-- info: 'AbsSat.GraphPath.Model.SymReview.OwnSymmetric_reviewSym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_reviewSym

/-- info: 'AbsSat.GraphPath.Model.SymReview.OwnSymmetric_filterAllSym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_filterAllSym

/-- info: 'AbsSat.GraphPath.Model.SymReview.OwnSymmetric_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OwnSymmetric_read


-- ============================================================
-- The mirror step loses no solution
-- ============================================================

theorem symmetrize_current (g : GPathM) (id : PathNodeId) :
    (symmetrize g id).current_step = g.current_step := by
  unfold symmetrize; split <;> rfl

theorem symmetrize_gowners (g : GPathM) (id : PathNodeId) :
    (symmetrize g id).gowners = g.gowners := by
  unfold symmetrize; split <;> rfl

theorem symmetrize_node? (g : GPathM) (id : PathNodeId) (d : PNodeM)
    (hd : g.node? id = some d) (p : PathNodeId) :
    (symmetrize g id).node? p = (g.node? p).map (symMap d id) :=
  node?_of_map g _ _ (symMap_id d id) (by simp only [symmetrize, hd]) p

theorem symMap_self (d : PNodeM) (id : PathNodeId) (m : PNodeM) (hm : m.id = id) :
    symMap d id m = m := by
  unfold symMap; rw [if_pos (by simp [hm])]

/-- The mirror step never touches the node it mirrors. -/
theorem symmetrize_node?_self (g : GPathM) (id : PathNodeId) :
    (symmetrize g id).node? id = g.node? id := by
  cases hid : g.node? id with
  | none => simp only [symmetrize, hid]
  | some d =>
    rw [symmetrize_node? g id d hid, hid]
    simp only [Option.map_some]
    rw [symMap_self d id d (node?_id_eq g id d hid)]

theorem symMap_parents (d : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (symMap d id m).parents = m.parents := by
  unfold symMap; split <;> rfl

theorem symMap_sons (d : PNodeM) (id : PathNodeId) (m : PNodeM) :
    (symMap d id m).sons = m.sons := by
  unfold symMap; split <;> rfl

/-- What the mirror keeps: everything but `id`, and `id` too wherever the node
is `id` itself or among `id`'s owners. -/
theorem mem_symMap_owners (d : PNodeM) (id : PathNodeId) (m : PNodeM) (q : PathNodeId)
    (hq : q ∈ m.owners) (hkeep : q ≠ id ∨ m.id = id ∨ m.id ∈ d.owners) :
    q ∈ (symMap d id m).owners := by
  unfold symMap
  split
  · exact hq
  · next hc =>
    refine List.mem_filter.mpr ⟨hq, ?_⟩
    rcases hkeep with hne | hmid | hin
    · simp [hne]
    · exact absurd (by simp [hmid]) hc
    · have hc2 : d.owners.contains m.id = true := List.elem_eq_true_of_mem hin
      exact absurd (by rw [hc2, Bool.or_true]) hc

/-- **The mirror step preserves a sound chain.** A chain entry it could remove
is `id` from the table of a node outside `owners(id)` — but a chain through
`id` has every other chain node inside `owners(id)` (`PairwiseOwned`), so no
chain entry is ever of that kind. -/
theorem ChainSound_symmetrize (g : GPathM) (id : PathNodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (symmetrize g id) sel := by
  cases hid : g.node? id with
  | none =>
    have : symmetrize g id = g := by simp only [symmetrize, hid]
    rw [this]; exact h
  | some d =>
    have hnode : ∀ pid n, g.node? pid = some n →
        (symmetrize g id).node? pid = some (symMap d id n) := by
      intro pid n hn; rw [symmetrize_node? g id d hid, hn]; rfl
    have hstep := symmetrize_current g id
    have hgowners := symmetrize_gowners g id
    obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro k hlo hhi
      rw [hstep] at hhi
      obtain ⟨hsome, hs⟩ := hchain.1 k hlo hhi
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨by rw [hnode _ n hn]; rfl, hs⟩
    · intro k hlo hhi
      rw [hstep] at hhi
      have hlink := hchain.2 k hlo hhi
      cases hn : g.node? (sel (k + 1)) with
      | none => rw [hn] at hlink; exact absurd hlink List.not_mem_nil
      | some n =>
        rw [hn] at hlink
        rw [hnode _ n hn]
        simpa [symMap_parents] using hlink
    · intro i j hi hj hi' hj' hne
      rw [hstep] at hi' hj'
      have hmem := howned i j hi hj hi' hj' hne
      simp only [ownersAt, List.mem_filter, ownersOf] at hmem ⊢
      obtain ⟨hown, hs⟩ := hmem
      refine ⟨?_, hs⟩
      cases hn : g.node? (sel j) with
      | none => rw [hn] at hown; exact absurd hown List.not_mem_nil
      | some n =>
        rw [hn] at hown
        rw [hnode _ n hn]
        refine mem_symMap_owners d id n (sel i) hown ?_
        if hsi : sel i = id then
          -- then `sel j` is among `id`'s owners, by the other half of the pair
          right; right
          have hback := howned j i hj hi hj' hi' (Ne.symm hne)
          simp only [ownersAt, List.mem_filter, ownersOf, hsi, hid] at hback
          rw [node?_id_eq g (sel j) n hn]
          exact hback.1
        else exact Or.inl hsi
    · intro k hlo hhi
      rw [hstep] at hhi
      rw [hgowners]
      exact hgow k hlo hhi
    · intro k hlo hhi
      rw [hstep] at hhi
      have hs := hself k hlo hhi
      simp only [ownersOf] at hs ⊢
      cases hn : g.node? (sel k) with
      | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
      | some n =>
        rw [hn] at hs
        rw [hnode _ n hn]
        refine mem_symMap_owners d id n (sel k) hs ?_
        if hsk : sel k = id then
          exact Or.inr (Or.inl ((node?_id_eq g (sel k) n hn).trans hsk))
        else exact Or.inl hsk
    · intro k hlo hhi
      rw [hstep] at hhi
      have hs := hson k hlo hhi
      simp only [sonsOf] at hs ⊢
      cases hn : g.node? (sel k) with
      | none => rw [hn] at hs; exact absurd hs List.not_mem_nil
      | some n =>
        rw [hn] at hs
        rw [hnode _ n hn]
        simpa [symMap_sons] using hs
    · exact ⟨hroot.1, fun k hk hk' => hroot.2 k hk (by rw [hstep] at hk'; exact hk')⟩

/-- info: 'AbsSat.GraphPath.Model.SymReview.ChainSound_symmetrize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_symmetrize


-- ------------------------------------------------------------
-- Through the whole symmetric review
-- ------------------------------------------------------------

theorem ChainSound_reviewNodeSym (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) (sel : Int → PathNodeId) (h : ChainSound g sel)
    (hwit : ∀ j, 0 ≤ j → j < g.current_step → sel j = id → ∀ d, g.node? id = some d →
      ∃ w, 0 ≤ w ∧ w < g.current_step ∧ sel w ∈ nb d) :
    ChainSound (reviewNodeSym g nb id) sel := by
  cases hid : g.node? id with
  | none => simpa [reviewNodeSym, hid] using h
  | some d =>
    have hd_id : d.id = id := node?_id_eq g id d hid
    have hB : ∀ j, 0 ≤ j → j < g.current_step → sel j = id →
        ∀ i, 0 ≤ i → i < g.current_step → sel i ∈ unionOwnersOf g (nb d) := by
      intro j hj hj' hsel i hi hi'
      obtain ⟨w, hw, hw', hwm⟩ := hwit j hj hj' hsel d hid
      exact chain_mem_unionOwnersOf g sel h (nb d) w hw hw' hwm i hi hi'
    let U := unionOwnersOf g (nb d)
    let G := unlinkIncompatible (symmetrize (updateAt g id (uniMap U)) id) id
    have hunl : ChainSound G sel :=
      ChainSound_unlinkIncompatible _ id sel
        (ChainSound_symmetrize _ id sel (ChainSound_updateAt_gen g id _ sel h hB))
    have hshape : reviewNodeSym g nb id =
        if isValidNode g d then
          (if isValidNode G (relink (intersectOwners d.owners U) d)
            then G else removeNode G id)
        else removeNode g id := by
      simp only [reviewNodeSym, hid]
      rfl
    rw [hshape]
    split
    · split
      · exact hunl
      · next hbad =>
        refine ChainSound_removeNode _ id sel hunl ?_
        intro k hlo hhi hk
        apply hbad
        have hnode0 : (symmetrize (updateAt g id (uniMap U)) id).node? id
            = some (uniMap U d) := by
          rw [symmetrize_node?_self, updateAt_node? g id _ (uniMap_id _) id d hid]
          rw [show (d.id == id) = true from beq_iff_eq.mpr hd_id]
        have hnode : G.node? (sel k) = some (relink (intersectOwners d.owners U) d) := by
          rw [hk]
          show (unlinkIncompatible (symmetrize (updateAt g id (uniMap U)) id) id).node? id = _
          rw [unlinkIncompatible_node? _ id _ hnode0 id _ hnode0]
          show some (unlinkMap (uniMap U d) id (uniMap U d)) = _
          unfold GPathM.unlinkMap
          rw [if_pos (show ((uniMap U d).id == id) = true from beq_iff_eq.mpr hd_id)]
          rfl
        exact isValidNode_of_chain _ sel hunl k _ hnode hlo hhi
    · next hbad =>
      refine ChainSound_removeNode g id sel h ?_
      intro k hlo hhi hk
      apply hbad
      have hnode : g.node? (sel k) = some d := by rw [hk]; exact hid
      exact isValidNode_of_chain g sel h k d hnode hlo hhi

theorem reviewNodeSym_current_step (g : GPathM) (nb : PNodeM → List PathNodeId)
    (id : PathNodeId) : (reviewNodeSym g nb id).current_step = g.current_step := by
  simp only [reviewNodeSym]
  split
  · rfl
  · split
    · split
      · rw [unlinkIncompatible_current, symmetrize_current]; rfl
      · show (unlinkIncompatible _ id).current_step = _
        rw [unlinkIncompatible_current, symmetrize_current]; rfl
    · rfl

theorem ChainSound_foldl_reviewNodeSym (nb : PNodeM → List PathNodeId) (k cs : Int)
    (hwit : ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel → g.current_step = cs →
      ∀ d, g.node? (sel k) = some d → ∃ w, 0 ≤ w ∧ w < g.current_step ∧ sel w ∈ nb d)
    (ids : List PathNodeId) (hids : ∀ id ∈ ids, id.id.step = k) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel → g.current_step = cs →
      ChainSound (ids.foldl (fun g id => reviewNodeSym g nb id) g) sel := by
  induction ids with
  | nil => intro g sel h _; simpa using h
  | cons id rest ih =>
    intro g sel h hcs
    simp only [List.foldl_cons]
    have hstep : id.id.step = k := hids id List.mem_cons_self
    have hone : ChainSound (reviewNodeSym g nb id) sel := by
      refine ChainSound_reviewNodeSym g nb id sel h ?_
      intro j hj hj' hsel d hd
      have hjk : j = k := by
        have := (h.chain.1.1 j hj hj').2
        rw [hsel] at this
        omega
      subst hjk
      exact hwit g sel h hcs d (by rw [hsel]; exact hd)
    exact ih (fun x hx => hids x (List.mem_cons_of_mem _ hx)) _ sel hone
      (by rw [reviewNodeSym_current_step]; exact hcs)

private theorem foldl_reviewNodeSym_current_step (nb : PNodeM → List PathNodeId)
    (ids : List PathNodeId) :
    ∀ g : GPathM, (ids.foldl (fun g id => reviewNodeSym g nb id) g).current_step
      = g.current_step := by
  induction ids with
  | nil => intro g; rfl
  | cons id rest ih =>
    intro g; simp only [List.foldl_cons]; rw [ih, reviewNodeSym_current_step]

theorem reviewLineSym_current_step (g : GPathM) (nb : PNodeM → List PathNodeId) (k : Int) :
    (reviewLineSym g nb k).current_step = g.current_step :=
  foldl_reviewNodeSym_current_step nb _ g

theorem ChainSound_reviewLineSym_parents (g : GPathM) (k : Int) (hk : 1 ≤ k)
    (hk2 : k < g.current_step) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (reviewLineSym g (·.parents) k) sel := by
  refine ChainSound_foldl_reviewNodeSym _ k g.current_step ?_ _ (line_ids_step g k) g sel h rfl
  intro g' sel' h' hcs d hd
  refine ⟨k - 1, by omega, by omega, ?_⟩
  have hrange : k - 1 + 1 < g'.current_step := by omega
  have hlink := h'.chain.1.2 (k - 1) (by omega) hrange
  rw [show k - 1 + 1 = k from by omega, hd] at hlink
  simpa using hlink

theorem ChainSound_reviewLineSym_sons (g : GPathM) (k : Int) (hk : 0 ≤ k)
    (hk2 : k + 1 < g.current_step) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (reviewLineSym g (·.sons) k) sel := by
  refine ChainSound_foldl_reviewNodeSym _ k g.current_step ?_ _ (line_ids_step g k) g sel h rfl
  intro g' sel' h' hcs d hd
  refine ⟨k + 1, by omega, by rw [hcs]; exact hk2, ?_⟩
  have hs := h'.son_link k hk (by rw [hcs]; exact hk2)
  simp only [sonsOf, hd] at hs
  exact hs

theorem ChainSound_reviewStepsSym_parents (ks : List Int) (cs : Int)
    (hks : ∀ k ∈ ks, 1 ≤ k ∧ k < cs) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel → g.current_step = cs →
      ChainSound (reviewStepsSym g (·.parents) ks) sel := by
  induction ks with
  | nil => intro g sel h _; simpa [reviewStepsSym] using h
  | cons k rest ih =>
    intro g sel h hcs
    obtain ⟨hk1, hk2⟩ := hks k List.mem_cons_self
    simp only [reviewStepsSym]
    split
    · exact ih (fun x hx => hks x (List.mem_cons_of_mem _ hx)) _ sel
        (ChainSound_reviewLineSym_parents g k hk1 (by rw [hcs]; exact hk2) sel h)
        (by rw [reviewLineSym_current_step]; exact hcs)
    · exact h

theorem ChainSound_reviewStepsSym_sons (ks : List Int) (cs : Int)
    (hks : ∀ k ∈ ks, 0 ≤ k ∧ k + 1 < cs) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel → g.current_step = cs →
      ChainSound (reviewStepsSym g (·.sons) ks) sel := by
  induction ks with
  | nil => intro g sel h _; simpa [reviewStepsSym] using h
  | cons k rest ih =>
    intro g sel h hcs
    obtain ⟨hk1, hk2⟩ := hks k List.mem_cons_self
    simp only [reviewStepsSym]
    split
    · exact ih (fun x hx => hks x (List.mem_cons_of_mem _ hx)) _ sel
        (ChainSound_reviewLineSym_sons g k hk1 (by rw [hcs]; exact hk2) sel h)
        (by rw [reviewLineSym_current_step]; exact hcs)
    · exact h

theorem ChainSound_reviewParentsSym (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (reviewParentsSym g) sel :=
  ChainSound_reviewStepsSym_parents _ g.current_step
    (fun k hk => ⟨mem_intRange_lower hk, by have := mem_intRange_upper hk; omega⟩) g sel h rfl

theorem ChainSound_reviewSonsSym (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (reviewSonsSym g) sel :=
  ChainSound_reviewStepsSym_sons _ g.current_step
    (fun k hk => by
      have hk' := List.mem_reverse.mp hk
      exact ⟨by have := mem_intRange_lower hk'; omega,
             by have := mem_intRange_upper hk'; omega⟩) g sel h rfl

theorem ChainSound_cleanInvalidGoSym (ids : List PathNodeId) :
    ∀ (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      ChainSound (cleanInvalidGoSym g ids) sel := by
  induction ids with
  | nil => intro g sel h; simpa [cleanInvalidGoSym] using h
  | cons id rest ih =>
    intro g sel h
    cases hid : g.node? id with
    | none => simp only [cleanInvalidGoSym, hid]; exact ih g sel h
    | some d =>
      have hd_id : d.id = id := node?_id_eq g id d hid
      let G := unlinkIncompatible (symmetrize (updateAt g id (gowMap g)) id) id
      have hunl : ChainSound G sel :=
        ChainSound_unlinkIncompatible _ id sel
          (ChainSound_symmetrize _ id sel (ChainSound_updateAt g id sel h))
      have hshape : cleanInvalidGoSym g (id :: rest) =
          cleanInvalidGoSym
            (if isValidNode G (relink (intersectOwners d.owners g.gowners) d)
              then G else removeNode G id) rest := by
        simp only [cleanInvalidGoSym, hid]
        rfl
      rw [hshape]
      apply ih
      split
      · exact hunl
      · next hbad =>
        refine ChainSound_removeNode _ id sel hunl ?_
        intro k hlo hhi hk
        apply hbad
        have hnode0 : (symmetrize (updateAt g id (gowMap g)) id).node? id
            = some (gowMap g d) := by
          rw [symmetrize_node?_self, updateAt_node? g id (gowMap g) (gowMap_id g) id d hid]
          simp only [gowMap]
          rw [show (d.id == id) = true from beq_iff_eq.mpr hd_id]
        have hnode : G.node? (sel k)
            = some (relink (intersectOwners d.owners g.gowners) d) := by
          rw [hk]
          show (unlinkIncompatible (symmetrize (updateAt g id (gowMap g)) id) id).node? id = _
          rw [unlinkIncompatible_node? _ id _ hnode0 id _ hnode0]
          show some (unlinkMap (gowMap g d) id (gowMap g d)) = _
          unfold GPathM.unlinkMap
          rw [if_pos (show ((gowMap g d).id == id) = true from by
            show (d.id == id) = true; exact beq_iff_eq.mpr hd_id)]
          rfl
        exact isValidNode_of_chain _ sel hunl k _ hnode hlo hhi

theorem ChainSound_reviewPassSym (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (reviewPassSym g) sel :=
  ChainSound_reviewSonsSym _ sel
    (ChainSound_reviewParentsSym _ sel (ChainSound_cleanInvalidGoSym _ g sel h))

theorem ChainSound_reviewFuelSym :
    ∀ (fuel : Nat) (g : GPathM) (sel : Int → PathNodeId), ChainSound g sel →
      ChainSound (reviewFuelSym fuel g) sel := by
  intro fuel
  induction fuel with
  | zero => intro g sel h; simpa [reviewFuelSym] using h
  | succ f ih =>
    intro g sel h
    simp only [reviewFuelSym]
    split
    · split
      · exact ih _ sel (ChainSound_reviewPassSym g sel h)
      · exact ChainSound_reviewPassSym g sel h
    · exact h

/-- **The symmetric review loses no solution.** Every sound chain of the input
is a sound chain of the output — the conservation law, for the new review. -/
theorem ChainSound_reviewSym (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel) : ChainSound (reviewSym g) sel :=
  ChainSound_reviewFuelSym _ g sel h

theorem ChainSound_filterAllSym (g : GPathM) (reqs : List NodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (hreq : ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    ChainSound (filterAllSym g reqs) sel :=
  ChainSound_reviewSym _ sel (ChainSound_foldl_filterRequire reqs g sel h hreq)

-- ------------------------------------------------------------
-- The reader's step
-- ------------------------------------------------------------

/-- **The owners-pin keeps every solution through the chosen node.** A sound
chain through `r` lies inside `owners(r)` — its other nodes by `PairwiseOwned`,
`r` itself by self-ownership — so intersecting the global owners with
`owners(r)` cannot cut it. -/
theorem ChainSound_pinOwners (g : GPathM) (r : PathNodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (hr : ∃ k, 0 ≤ k ∧ k < g.current_step ∧ sel k = r) :
    ChainSound (pinOwners g r) sel := by
  obtain ⟨kr, hkr0, hkr1, hkr⟩ := hr
  unfold pinOwners
  split
  · exact h
  · next n hn =>
    obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
    refine ⟨⟨hchain, howned, ?_⟩, hself, hson, hroot⟩
    intro k hlo hhi
    refine List.mem_filter.mpr ⟨hgow k hlo hhi, ?_⟩
    apply List.elem_eq_true_of_mem
    if hk : k = kr then
      subst hk
      have hs := hself k hlo hhi
      simp only [ownersOf, hkr, hn] at hs
      exact hkr ▸ hs
    else
      have hm := howned k kr hlo hkr0 hhi hkr1 hk
      simp only [ownersAt, List.mem_filter, ownersOf, hkr, hn] at hm
      exact hm.1

/-- **A reading step keeps every solution through the node it reads.** -/
theorem ChainSound_readStepSym (g : GPathM) (r : PathNodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (hr : ∃ k, 0 ≤ k ∧ k < g.current_step ∧ sel k = r) :
    ChainSound (readStepSym g r) sel :=
  ChainSound_reviewSym _ sel (ChainSound_pinOwners g r sel h hr)

/-- info: 'AbsSat.GraphPath.Model.SymReview.ChainSound_reviewSym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_reviewSym

/-- info: 'AbsSat.GraphPath.Model.SymReview.ChainSound_readStepSym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_readStepSym

end AbsSat.GraphPath.Model.SymReview
