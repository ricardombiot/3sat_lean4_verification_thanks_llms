-- lean_project/AbsSat/Cnf/FrontierDerive.lean
import AbsSat.Cnf.ClauseOrder

/-!
# Derived clause blocks: forgetting a variable by writing what the frontier remembers

Walking the clauses in the given order, the *frontier* after clause `k` is the set of
variables that occur both at or before `k` and after `k`. When a variable leaves the
frontier (its last occurrence is clause `k`), resolving on it between the clauses seen
so far that contain it with opposite signs produces exactly what the rest of the
formula still needs to know about it.

`derive` keeps the resolvents that are not tautologies, have at most three literals,
mention only frontier variables and are not subsumed by a clause already kept, and
inserts each one right after clause `k` as ordinary clause blocks:

* three literals — one clause;
* two literals `(a ∨ b)` — `(a ∨ b ∨ w)` and `(a ∨ b ∨ ¬w)` for a padding variable `w`,
  which together are equivalent to `(a ∨ b)`;
* one literal — four clauses over two padding variables;
* the empty resolvent — the eight sign patterns over three variables (the formula is
  refuted already).

When several variables leave the frontier at the same clause they are eliminated one at
a time; a resolvent that still mentions one of them is kept for further resolution but
not put on the map.

Every derived clause is implied by the formula, so the augmented formula has exactly the
same satisfying assignments (checked against brute force by `lake exe frontier-derive`).
The number of derived clauses is capped.

Measurement only: nothing here is proved yet.
-/

namespace AbsSat.Cnf.FrontierDerive

open AbsSat.Cnf
open AbsSat.Cnf.ClauseOrder (lits vars)

def negLit (l : Lit) : Lit := ⟨l.v, !l.pos⟩

/-- The resolvent of two literal sets on variable `v`, unless it is a tautology. -/
def resolve (v : Nat) (a b : List Lit) : Option (List Lit) :=
  let r := (a.filter (fun l => l.v != v) ++ b.filter (fun l => l.v != v)).eraseDups
  if r.any (fun l => r.contains (negLit l)) then none else some r

/-- Padding variables for a short resolvent: frontier variables first. -/
def padVars (frontier : List Nat) (nVars : Nat) (r : List Lit) (need : Nat) : List Nat :=
  ((frontier ++ List.range nVars).eraseDups.filter (fun w => !(r.any (·.v == w)))).take need

/-- The 3-clauses that together say `r`. Empty if there are not enough variables to pad. -/
def blocksOf (frontier : List Nat) (nVars : Nat) (r : List Lit) : List Clause :=
  let need := 3 - r.length
  let ws := padVars frontier nVars r need
  if ws.length < need then [] else
    let signs : List (List Bool) := (List.range (2 ^ need)).map (fun i =>
      (List.range need).map (fun j => (i / 2 ^ j) % 2 == 1))
    signs.filterMap (fun ss =>
      match r ++ (ws.zip ss).map (fun p => (⟨p.1, p.2⟩ : Lit)) with
      | [x, y, z] => some ⟨x, y, z⟩
      | _ => none)

structure Derived where
  cnf : Cnf
  /-- Resolvents kept. -/
  derived : Nat := 0
  /-- Clause blocks inserted for them. -/
  blocks : Nat := 0
  /-- The empty resolvent was derived. -/
  refuted : Bool := false
  /-- The cap stopped the preanalysis from keeping some resolvent. -/
  capped : Bool := false

def derive (φ : Cnf) (cap : Nat) : Derived := Id.run do
  let cs := φ.clauses
  let mut out : List Clause := []
  let mut pool : List (List Lit) := []
  let mut nDer := 0
  let mut nKept := 0
  let mut nBlocks := 0
  let mut refuted := false
  let mut capped := false
  for k in [0:cs.length] do
    let c := cs[k]!
    out := out ++ [c]
    pool := pool ++ [lits c]
    let pre := ((cs.take (k + 1)).flatMap vars).eraseDups
    let post := (cs.drop (k + 1)).flatMap vars
    let frontier := pre.filter post.contains
    let forgotten := (vars c).eraseDups.filter (fun v => !post.contains v)
    -- the forgotten variables are eliminated one at a time: a resolvent may still mention
    -- the ones not eliminated yet, and is then kept for resolution but not put on the map
    let mut pending := forgotten
    for v in forgotten do
      pending := pending.erase v
      let allowed := frontier ++ pending
      let posC := pool.filter (fun ls => ls.contains ⟨v, true⟩)
      let negC := pool.filter (fun ls => ls.contains ⟨v, false⟩)
      for a in posC do
        for b in negC do
          match resolve v a b with
          | none => pure ()
          | some r =>
            if r.length ≤ 3 && r.all (fun l => allowed.contains l.v)
                && !pool.any (fun p => p.all r.contains) then
              if nKept ≥ cap then
                capped := true
              else if r.all (fun l => frontier.contains l.v) then
                let bs := blocksOf frontier φ.nVars r
                if !bs.isEmpty then
                  out := out ++ bs
                  pool := pool ++ [r]
                  nKept := nKept + 1
                  nDer := nDer + 1
                  nBlocks := nBlocks + bs.length
                  if r.isEmpty then refuted := true
              else
                pool := pool ++ [r]
                nKept := nKept + 1
  return { cnf := { φ with clauses := out }, derived := nDer, blocks := nBlocks, refuted, capped }

-- ============================================================
-- Sanity: the example of the conversation
-- ============================================================

private def pos (v : Nat) : Lit := ⟨v, true⟩
private def neg (v : Nat) : Lit := ⟨v, false⟩

/-- `x1..x5` are `0..4`. -/
private def example4 : Cnf :=
  { nVars := 5,
    clauses := [⟨pos 0, pos 1, pos 2⟩, ⟨neg 0, pos 1, pos 3⟩, ⟨neg 1, pos 2, pos 4⟩,
                ⟨neg 2, neg 3, pos 4⟩] }

-- Forgetting x1 after C2 writes (x2 ∨ x3 ∨ x4); forgetting x2 after C3 writes (x3 ∨ x4 ∨ x5).
#guard (derive example4 100).derived == 2
#guard (derive example4 100).cnf.clauses ==
  [⟨pos 0, pos 1, pos 2⟩, ⟨neg 0, pos 1, pos 3⟩, ⟨pos 1, pos 2, pos 3⟩,
   ⟨neg 1, pos 2, pos 4⟩, ⟨pos 2, pos 3, pos 4⟩, ⟨neg 2, neg 3, pos 4⟩]

/-- `(x ∨ y ∨ z)` for all eight sign patterns: unsatisfiable; resolution empties it. -/
private def all8 : Cnf :=
  { nVars := 3,
    clauses := (List.range 8).map (fun i =>
      ⟨⟨0, i % 2 == 0⟩, ⟨1, (i / 2) % 2 == 0⟩, ⟨2, (i / 4) % 2 == 0⟩⟩) }

#guard (derive all8 100).refuted

end AbsSat.Cnf.FrontierDerive
