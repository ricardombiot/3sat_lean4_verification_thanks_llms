-- lean_project/AbsSat/Cnf/ClauseOrder.lean
import AbsSat.Cnf.Formula

/-!
# Clause orders for the weak requirements

The weak filter of a clause acts on the earlier clauses it shares a variable
with, so the order of the clauses decides how much it can prune. Two orders are
defined here, both permutations of the clauses (the variables keep their steps):

* `byFrequency` — each literal (`x` and `¬x` counted separately) is counted over
  the whole formula; a clause scores the sum of its three literals' counts; the
  highest scores go first. Ties keep the original order (`mergeSort` is stable).
* `byGreedy` — repeatedly place the clause linked (sharing a variable) with the
  most clauses already placed, ties broken by the frequency score.

`weakLinks` is the structural measure: for every clause, how many earlier clauses
share a variable with it — the number of weak entries the map will build.

Measurement only for now: nothing here is proved, and nothing feeds the machines
except through `lake exe improves-diff --order`.
-/

namespace AbsSat.Cnf.ClauseOrder

open AbsSat.Cnf

def lits (c : Clause) : List Lit := [c.l1, c.l2, c.l3]

def vars (c : Clause) : List Nat := [c.l1.v, c.l2.v, c.l3.v]

/-- How many times a literal occurs in the formula, polarity included. -/
def litCount (φ : Cnf) (l : Lit) : Nat :=
  (φ.clauses.map (fun c => (lits c).countP (· == l))).sum

def score (φ : Cnf) (c : Clause) : Nat := ((lits c).map (litCount φ)).sum

def byFrequency (φ : Cnf) : Cnf :=
  { φ with clauses := φ.clauses.mergeSort (fun a b => decide (score φ b ≤ score φ a)) }

/-- How many of `placed` share a variable with `c`. -/
def links (placed : List Clause) (c : Clause) : Nat :=
  placed.countP (fun p => (vars c).any (vars p).contains)

def lexGt (a b : Nat × Nat) : Bool := a.1 > b.1 || (a.1 == b.1 && a.2 > b.2)

def bestGo (key : Clause → Nat × Nat) : List Clause → Option Clause → Option Clause
  | [], b => b
  | c :: cs, none => bestGo key cs (some c)
  | c :: cs, some b => bestGo key cs (if lexGt (key c) (key b) then some c else some b)

def greedyGo (φ : Cnf) : Nat → List Clause → List Clause → List Clause
  | 0, placed, rest => placed ++ rest
  | fuel + 1, placed, rest =>
    match bestGo (fun c => (links placed c, score φ c)) rest none with
    | none => placed
    | some c => greedyGo φ fuel (placed ++ [c]) (rest.erase c)

def byGreedy (φ : Cnf) : Cnf :=
  { φ with clauses := greedyGo φ φ.clauses.length [] φ.clauses }

def weakLinksGo : List Clause → List Clause → Nat
  | [], _ => 0
  | c :: cs, placed => links placed c + weakLinksGo cs (placed ++ [c])

/-- For every clause, the earlier clauses sharing a variable with it, summed. -/
def weakLinks (φ : Cnf) : Nat := weakLinksGo φ.clauses []

-- ============================================================
-- Frontier: variables shared by the placed prefix and the rest
-- ============================================================

def varsOf (cs : List Clause) : List Nat := cs.flatMap vars

/-- Distinct variables that occur both in `placed` and in `rest`. -/
def frontier (placed rest : List Clause) : Nat :=
  ((varsOf placed).eraseDups).countP (fun v => (varsOf rest).contains v)

def bestBy (better : Clause → Clause → Bool) : List Clause → Option Clause → Option Clause
  | [], b => b
  | c :: cs, none => bestBy better cs (some c)
  | c :: cs, some b => bestBy better cs (if better c b then some c else some b)

/-- Greedy: place the clause leaving the smallest frontier; ties by most links
to the placed clauses, then by frequency score. -/
def minFrontGo (φ : Cnf) : Nat → List Clause → List Clause → List Clause
  | 0, placed, rest => placed ++ rest
  | fuel + 1, placed, rest =>
    let key := fun c => (frontier (placed ++ [c]) (rest.erase c), links placed c, score φ c)
    let better := fun c b =>
      let kc := key c
      let kb := key b
      kc.1 < kb.1 || (kc.1 == kb.1 && lexGt kc.2 kb.2)
    match bestBy better rest none with
    | none => placed
    | some c => minFrontGo φ fuel (placed ++ [c]) (rest.erase c)

def byMinFrontier (φ : Cnf) : Cnf :=
  { φ with clauses := minFrontGo φ φ.clauses.length [] φ.clauses }

/-- A deterministic pseudo-random permutation. -/
def shuffleGo (x : Nat) : Nat → List Clause → List Clause → List Clause
  | 0, placed, rest => placed ++ rest
  | fuel + 1, placed, rest =>
    let x' := (x * 1103515245 + 12345) % 2147483648
    match rest[(x' / 65536) % (max rest.length 1)]? with
    | none => placed ++ rest
    | some c => shuffleGo x' fuel (placed ++ [c]) (rest.erase c)

def shuffled (seed : Nat) (φ : Cnf) : Cnf :=
  { φ with clauses := shuffleGo seed φ.clauses.length [] φ.clauses }

/-- The frontier after each prefix: its maximum and its sum. -/
def frontierProfile (φ : Cnf) : Nat × Nat :=
  (List.range (φ.clauses.length + 1)).foldl (fun acc k =>
    let f := frontier (φ.clauses.take k) (φ.clauses.drop k)
    (max acc.1 f, acc.2 + f)) (0, 0)

-- ============================================================
-- Sanity
-- ============================================================

private def pos (v : Nat) : Lit := ⟨v, true⟩
private def neg (v : Nat) : Lit := ⟨v, false⟩

private def sample : Cnf :=
  { nVars := 6,
    clauses := [⟨pos 3, pos 4, pos 5⟩, ⟨pos 0, pos 1, pos 2⟩, ⟨pos 0, neg 1, pos 3⟩,
                ⟨pos 0, pos 1, neg 2⟩, ⟨neg 3, neg 4, neg 5⟩] }

-- `x0` is used three times and `x1`, `x3` twice: the three clauses scoring 6 go
-- first, in their original order, then 4, then 3.
#guard (byFrequency sample).clauses.map (score sample) == [6, 6, 6, 4, 3]
#guard (byFrequency sample).clauses.head? == some ⟨pos 0, pos 1, pos 2⟩

#guard (byFrequency sample).clauses.isPerm sample.clauses
#guard (byGreedy sample).clauses.isPerm sample.clauses
#guard (byMinFrontier sample).clauses.isPerm sample.clauses
#guard (shuffled 7 sample).clauses.isPerm sample.clauses

end AbsSat.Cnf.ClauseOrder
