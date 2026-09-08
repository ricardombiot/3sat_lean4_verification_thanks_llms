-- lean_project/AbsSat/GraphPath/Model/ZeroOneAll.lean
import AbsSat.GraphPath.Model.ArcConsistency

/-!
Step (3) of `verificacion_inseguridad_autor_v12.md`'s strategy: the
mathematical core of why local consistency suffices for this map.

## A correction to v12, in the algorithm's favour

v12 says "in a 0/1/all network, arc consistency decides satisfiability". That
is imprecise. 0/1/all constraints are closed under the dual discriminator, a
**majority** polymorphism, and majority-closed languages have **strict width
2**: it is *pairwise* consistency — a table of allowed pairs — not arc
consistency on domains alone, that guarantees a global solution.

The correction favours the algorithm. `owners` is not a domain: it is a
*per-node, per-step* table, i.e. exactly a 2-consistency structure. The
machine has been maintaining the stronger invariant all along, which is the
one it needs. `PairwiseOwned` is named after the right thing.

## What is proved here

`helly`: **a family of 0/1/all supports that intersects pairwise intersects
globally.** A support is `none` ("all", no constraint) or `some a` ("1", pinned
to `a`); the "0" case is what `GraphMap.MapReqs.Functional` rules out of the
construction. If any support pins `a`, pairwise agreement forces every other
pinning support to pin `a` too, and the unpinned ones accept it.

That single fact is where the obstacle v11 identified dissolves. For arbitrary
constraints pairwise compatibility says nothing about global compatibility —
that is the Helly failure. For all-or-one supports it says everything.

`choose_at_step` is the same fact in the shape the greedy construction uses:
given already-chosen elements whose supports for one step agree pairwise, some
value at that step satisfies all of them at once. That is the inductive step
that turns pairwise consistency into a global chain.

`sat_supAt_of_mem` ties it back to the map: `MapReqs.Functional` — at most one
requirement per step — is exactly what makes a requirement list induce a
genuine 0/1/all support rather than one that silently reports only its first
entry.

## What is still missing

The greedy assembly over the step range, and — the real gap — the link to the
machine. `helly` is about supports; the machine's supports are the `owners`
tables, and using them requires `owners ⊆ support`: that the tables hold
nothing the map does not permit. `ArcConsistency.lean` states that inclusion
and it is still unproved. It has been the open half since v11, and it is now
the only thing between this file and "no zombies".
-/

namespace AbsSat.ZeroOneAll

/-- A **0/1/all support**: `none` allows everything ("all"), `some a` pins
exactly `a` ("1"). The "0" case — allowing nothing — is what
`GraphMap.MapReqs.Functional` rules out of the construction. -/
abbrev Sup (α : Type) := Option α

/-- `x` satisfies a support. -/
def Sat {α : Type} (s : Sup α) (x : α) : Prop :=
  match s with | none => True | some a => x = a

theorem Sat_none {α : Type} (x : α) : Sat none x := trivial

theorem Sat_some {α : Type} (a x : α) : Sat (some a) x ↔ x = a := Iff.rfl

/-- **The Helly property for 0/1/all supports.** A family of them that
intersects *pairwise* intersects *globally*.

This is the whole reason local consistency is enough here, and the exact point
at which the obstacle v11 identified dissolves: for arbitrary constraints,
pairwise compatibility says nothing about global compatibility; for supports
that are each "everything" or "one thing", it says everything. -/
theorem helly {α : Type} (a₀ : α) (ss : List (Sup α))
    (hpair : ∀ s₁ ∈ ss, ∀ s₂ ∈ ss, ∃ x, Sat s₁ x ∧ Sat s₂ x) :
    ∃ x, ∀ s ∈ ss, Sat s x := by
  induction ss with
  | nil => exact ⟨a₀, by intro s hs; exact absurd hs List.not_mem_nil⟩
  | cons s rest ih =>
    cases s with
    | none =>
      obtain ⟨x, hx⟩ := ih (fun s₁ h₁ s₂ h₂ =>
        hpair s₁ (List.mem_cons_of_mem _ h₁) s₂ (List.mem_cons_of_mem _ h₂))
      refine ⟨x, ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Sat_none x
      · exact hx t ht'
    | some a =>
      refine ⟨a, ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact rfl
      · cases t with
        | none => exact Sat_none a
        | some b =>
          obtain ⟨x, hx1, hx2⟩ :=
            hpair (some a) List.mem_cons_self (some b) (List.mem_cons_of_mem _ ht')
          exact hx1 ▸ hx2

/-- **The CCJ step.** Given a set of already-chosen elements whose supports for
one step intersect pairwise, some value at that step satisfies *all* of them.

This is the inductive step of the greedy construction that turns local
consistency into a global solution: it is exactly `helly`, applied to the
supports the chosen elements impose. -/
theorem choose_at_step {α β : Type} (a₀ : α) (chosen : List β) (S : β → Sup α)
    (hpair : ∀ d₁ ∈ chosen, ∀ d₂ ∈ chosen, ∃ x, Sat (S d₁) x ∧ Sat (S d₂) x) :
    ∃ x, ∀ d ∈ chosen, Sat (S d) x := by
  obtain ⟨x, hx⟩ := helly a₀ (chosen.map S) (by
    intro s₁ h₁ s₂ h₂
    obtain ⟨d₁, hd₁, rfl⟩ := List.mem_map.mp h₁
    obtain ⟨d₂, hd₂, rfl⟩ := List.mem_map.mp h₂
    exact hpair d₁ hd₁ d₂ hd₂)
  exact ⟨x, fun d hd => hx (S d) (List.mem_map_of_mem hd)⟩

-- ============================================================
-- Where the map's requirements enter
-- ============================================================

open AbsSat.Utils.Alias

/-- The support a requirement list imposes on one step: `none` where it names
nothing, `some r` where it names `r`. -/
def supAt (rs : List NodeId) (j : Step) : Sup NodeId := rs.find? (fun r => r.step == j)

/-- **`Functional` is exactly what makes `supAt` a 0/1/all support.** If the
requirement list names `r` at step `j`, and names at most one node per step,
then satisfying the support at `j` means *being* `r` — the "1" case. Without
`Functional` the list could name two different nodes at `j` and `supAt` would
silently report only the first. -/
theorem sat_supAt_of_mem (rs : List NodeId) (j : Step) (r : NodeId)
    (hr : r ∈ rs) (hstep : r.step = j)
    (hfun : ∀ r₁ ∈ rs, ∀ r₂ ∈ rs, r₁.step = r₂.step → r₁ = r₂)
    (x : NodeId) (hx : Sat (supAt rs j) x) : x = r := by
  cases hfind : rs.find? (fun r => r.step == j) with
  | none =>
    exact absurd (by rw [hstep]; exact beq_iff_eq.mpr rfl)
      (List.find?_eq_none.mp hfind r hr)
  | some r' =>
    have hr'_mem : r' ∈ rs := List.mem_of_find?_eq_some hfind
    have hp : (r'.step == j) = true := List.find?_some (p := fun r : NodeId => r.step == j) hfind
    have hr'_step : r'.step = j := eq_of_beq hp
    have : r' = r := hfun r' hr'_mem r hr (by rw [hr'_step, hstep])
    rw [supAt, hfind] at hx
    rw [hx, this]

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.ZeroOneAll.helly' depends on axioms: [propext] -/
#guard_msgs in
#print axioms helly

/-- info: 'AbsSat.ZeroOneAll.choose_at_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms choose_at_step

/-- info: 'AbsSat.ZeroOneAll.sat_supAt_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_supAt_of_mem

end AbsSat.ZeroOneAll
