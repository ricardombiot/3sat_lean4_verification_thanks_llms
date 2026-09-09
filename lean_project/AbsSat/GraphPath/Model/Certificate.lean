-- lean_project/AbsSat/GraphPath/Model/Certificate.lean
import AbsSat.GraphPath.Model.L6
import AbsSat.GraphPath.Model.L6Search

/-!
**Route C — the certifying algorithm.**

`Supported` ("no zombies", `L6.lean`) is open. This module proves the next
best thing: that the *check* for it is correct. Instead of

> every node of every reachable graph lies on a complete co-owned chain

it establishes

> if the checker accepts a graph together with a family of witnesses, then
> **that** graph satisfies `Supported`.

which turns each run of `lake exe validate` from empirical evidence into a
machine-checked fact about the instance it just examined. This is the pattern
verified SAT-proof checkers use: the search stays untrusted, the verification
is proved.

**What is trusted and what is not.** The search that *finds* the chains
(`Validate.searchFrom`) is `partial` and nothing here says a word about it —
it is a heuristic that produces candidates. Everything that decides whether a
candidate is believed goes through `isCert`, which is a plain `Bool` function
over `List`, and `isCert_sound` below proves that `isCert = true` really does
give an `IsChain` + `PairwiseOwned` selection in the sense of `Denot.lean`. So
a bug in the search can only make the checker *reject*; it cannot make it
accept a graph with a zombie.

**Why the length test matters.** `L6Search.isGoodChain` checks the chain
conditions at the indices the list happens to have. A short list would pass
vacuously at the missing steps, so `isCert` adds `sel.length = current_step`;
that is what lets the `Nat` indices of the checker line up with the `Int`
steps of the model over the whole range `[0, current_step)`.
-/

namespace AbsSat.GraphPath.Model.Certificate

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open L6Search (ownersOfB isGoodChain selections)

-- ============================================================
-- The three halves of `isGoodChain`, named
-- ============================================================

/-- Every index carries a real node, sitting at its own step. -/
def stepsOk (g : GPathM) (sel : List PathNodeId) : Bool :=
  (List.range sel.length).all (fun i =>
    match sel[i]? with
    | some p => (g.node? p).isSome && p.id.step == (i : Int)
    | none => false)

/-- Consecutive picks are linked parent → son. -/
def linksOk (g : GPathM) (sel : List PathNodeId) : Bool :=
  (List.range sel.length).all (fun i =>
    if i + 1 < sel.length then
      match sel[i]?, sel[i+1]? with
      | some p, some q => match g.node? q with
                          | some n => n.parents.contains p
                          | none => false
      | _, _ => false
    else true)

/-- Every pick owns every other pick. -/
def ownedOk (g : GPathM) (sel : List PathNodeId) : Bool :=
  let idxs := List.range sel.length
  idxs.all (fun i => idxs.all (fun j =>
    if i == j then true
    else match sel[i]?, sel[j]? with
      | some p, some q => (ownersOfB g q).contains p
      | _, _ => false))

theorem isGoodChain_eq (g : GPathM) (sel : List PathNodeId) :
    isGoodChain g sel = (stepsOk g sel && linksOk g sel && ownedOk g sel) := rfl

-- ============================================================
-- Certificates
-- ============================================================

/-- Read a certificate list as the total `Int → PathNodeId` selection the
model's `IsChain` / `PairwiseOwned` are stated over. -/
def selFun (sel : List PathNodeId) (dflt : PathNodeId) : Int → PathNodeId :=
  fun k => (sel[k.toNat]?).getD dflt

/-- **A certificate for `g`**: one node per step, of exactly the right length,
passing every chain condition. Decidable, and cheap — linear in the graph for
the first two conditions, quadratic in the number of steps for the third. -/
def isCert (g : GPathM) (sel : List PathNodeId) : Bool :=
  (sel.length == g.current_step.toNat) && isGoodChain g sel

theorem isCert_length {g : GPathM} {sel : List PathNodeId} (h : isCert g sel = true) :
    sel.length = g.current_step.toNat := by
  have h' := (Bool.and_eq_true _ _).mp h
  exact eq_of_beq h'.1

theorem isCert_good {g : GPathM} {sel : List PathNodeId} (h : isCert g sel = true) :
    stepsOk g sel = true ∧ linksOk g sel = true ∧ ownedOk g sel = true := by
  have h' := (Bool.and_eq_true _ _).mp h
  rw [isGoodChain_eq] at h'
  have h₂ := (Bool.and_eq_true _ _).mp h'.2
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  exact ⟨h₃.1, h₃.2, h₂.2⟩

-- ============================================================
-- Reading the three conditions back out at an `Int` step
-- ============================================================

theorem stepsOk_apply {g : GPathM} {sel : List PathNodeId} (h : stepsOk g sel = true)
    {i : Nat} (hi : i < sel.length) :
    (g.node? sel[i]).isSome = true ∧ sel[i].id.step = (i : Int) := by
  have hx := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [List.getElem?_eq_getElem hi] at hx
  have hx' := (Bool.and_eq_true _ _).mp hx
  exact ⟨hx'.1, eq_of_beq hx'.2⟩

theorem linksOk_apply {g : GPathM} {sel : List PathNodeId} (h : linksOk g sel = true)
    {i : Nat} (hi : i + 1 < sel.length) :
    ∃ n, g.node? sel[i+1] = some n ∧ n.parents.contains sel[i] = true := by
  have hi' : i < sel.length := by omega
  have hx := List.all_eq_true.mp h i (List.mem_range.mpr hi')
  rw [if_pos hi, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at hx
  have hx' : (match g.node? sel[i+1] with
              | some n => n.parents.contains sel[i]
              | none => false) = true := hx
  split at hx'
  case _ n heq => exact ⟨n, heq, hx'⟩
  case _ heq => simp at hx'

theorem ownedOk_apply {g : GPathM} {sel : List PathNodeId} (h : ownedOk g sel = true)
    {i j : Nat} (hi : i < sel.length) (hj : j < sel.length) (hne : i ≠ j) :
    (ownersOfB g sel[j]).contains sel[i] = true := by
  have hx := List.all_eq_true.mp
    (List.all_eq_true.mp h i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)
  rw [if_neg (by simpa using hne), List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj] at hx
  exact hx

-- ============================================================
-- The reflection lemma
-- ============================================================

theorem selFun_eq {sel : List PathNodeId} {dflt : PathNodeId} {k : Int}
    (hk : k.toNat < sel.length) : selFun sel dflt k = sel[k.toNat] := by
  unfold selFun
  rw [List.getElem?_eq_getElem hk]
  rfl

/-- **`isCert` really does certify a chain.** Everything the checker accepts is
a genuine `IsChain` + `PairwiseOwned` selection, in the sense of `Denot.lean` —
not in the sense of the checker's own code. -/
theorem isCert_sound (g : GPathM) (sel : List PathNodeId) (dflt : PathNodeId)
    (h : isCert g sel = true) :
    IsChain g (selFun sel dflt) ∧ PairwiseOwned g (selFun sel dflt) := by
  have hlen := isCert_length h
  obtain ⟨hs, hl, ho⟩ := isCert_good h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- every step carries a node, at its own step
    intro k hlo hhi
    have hk : k.toNat < sel.length := by rw [hlen]; omega
    rw [selFun_eq hk]
    obtain ⟨hsome, hstep⟩ := stepsOk_apply hs hk
    refine ⟨hsome, ?_⟩
    rw [hstep]; omega
  · -- consecutive picks are parent-linked
    intro k hlo hhi
    have hk1 : k.toNat + 1 < sel.length := by rw [hlen]; omega
    have hk : k.toNat < sel.length := by omega
    have hsucc : (k + 1).toNat = k.toNat + 1 := by omega
    obtain ⟨n, hnode, hpar⟩ := linksOk_apply hl hk1
    rw [selFun_eq hk, show selFun sel dflt (k + 1) = sel[k.toNat + 1] by
      rw [show ((k : Int) + 1) = ((k.toNat + 1 : Nat) : Int) by omega]
      exact selFun_eq (by omega)]
    rw [hnode]
    exact List.elem_iff.mp hpar
  · -- pairwise ownership, read at the right step
    intro i j hi0 hj0 hi hj hne
    have hi' : i.toNat < sel.length := by rw [hlen]; omega
    have hj' : j.toNat < sel.length := by rw [hlen]; omega
    have hne' : i.toNat ≠ j.toNat := by omega
    have hown := ownedOk_apply ho hi' hj' hne'
    obtain ⟨_, hstep⟩ := stepsOk_apply hs hi'
    rw [selFun_eq hi', selFun_eq hj']
    refine List.mem_filter.mpr ⟨List.elem_iff.mp hown, ?_⟩
    refine beq_iff_eq.mpr ?_
    rw [hstep]; omega

/-- A certificate that contains `pid` at `pid`'s own step is a chain *through*
`pid` — the shape `Supported` asks for. -/
theorem selFun_through {sel : List PathNodeId} {dflt pid : PathNodeId}
    (h : sel[pid.id.step.toNat]? = some pid) : selFun sel dflt pid.id.step = pid := by
  unfold selFun; rw [h]; rfl

-- ============================================================
-- The invariant, as a runnable check over a family of certificates
-- ============================================================

/-- The "no zombies" check: a `Bool` saying that every node of `g` comes with a
certificate placing it on a complete co-owned chain. Runs; and by
`Supported_of_checkSupported` its truth *is* `Supported g`. -/
def checkSupported (g : GPathM) (cert : PathNodeId → List PathNodeId) : Bool :=
  g.nodes.all (fun n =>
    isCert g (cert n.id) && ((cert n.id)[n.id.id.step.toNat]? == some n.id))

/-- **Route C, the theorem.** A graph the checker accepts satisfies `Supported`
— the open lemma L6 — for real. The certificates come from wherever; only
`checkSupported` is believed. -/
theorem Supported_of_checkSupported (g : GPathM) (cert : PathNodeId → List PathNodeId)
    (h : checkSupported g cert = true) : Supported g := by
  intro pid n hn
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = pid := node?_id_eq g pid n hn
  have hx := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp h n hmem)
  rw [hid] at hx
  obtain ⟨hchain, howned⟩ := isCert_sound g (cert pid) pid hx.1
  exact ⟨selFun (cert pid) pid, hchain, howned, selFun_through (eq_of_beq hx.2)⟩

-- ============================================================
-- One certificate is enough for `Inhabited`
-- ============================================================

/-- Any `PathNodeId`, to fill the steps a certificate does not name. Which
values these are never matters: `IsChain` and `PairwiseOwned` only ever look
inside `[0, current_step)`, where the certificate does name them. -/
def dfltPid : PathNodeId := { id := { step := 0, index := 0 }, parent_id := none }

/-- **`Inhabited` needs one certificate, not one per node.** A single accepted
chain proves the graph denotes something — which is the half of L6 the
SAT/UNSAT verdict actually consumes (`Verdict.lean`). -/
theorem Inhabited_of_isCert (g : GPathM) (sel : List PathNodeId)
    (h : isCert g sel = true) : AbsSat.GraphPath.Model.Inhabited g :=
  ⟨pathOf (selFun sel dfltPid) g, selFun sel dfltPid,
    (isCert_sound g sel dfltPid h).1, (isCert_sound g sel dfltPid h).2, rfl⟩

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.Certificate.isCert_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isCert_sound

/-- info: 'AbsSat.GraphPath.Model.Certificate.Supported_of_checkSupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Supported_of_checkSupported

/-- info: 'AbsSat.GraphPath.Model.Certificate.Inhabited_of_isCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inhabited_of_isCert

end AbsSat.GraphPath.Model.Certificate
