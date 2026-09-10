-- lean_project/AbsSat/Cnf/Dimacs.lean
import AbsSat.Cnf.Formula

/-!
# DIMACS, parsed purely — mirroring `ImportCnf`'s line rules

`GraphMap.ImportCnf` reads a DIMACS file in `IO`. This is the same reader as a
pure function on the already-read lines, so the differential band can hand the
*same text* to both sides and compare the map they produce.

It is a mirror, not an improvement: it reproduces `ImportCnf`'s rules exactly,
including the ones that are arguably too lax.

* the header is matched as `_ :: "cnf" :: n :: _` — the token before `cnf` is
  never checked;
* lines starting with `c`, and blank lines, are skipped;
* reading stops at a line starting with `%` or `0`;
* a clause line has its `-` rewritten to `!`, is split on spaces with empty
  tokens dropped, and **the first three tokens are taken as the literals** —
  so `1 2 0` is read as the three literals `1`, `2`, `0`;
* a clause is **dropped** when it has fewer than three tokens, or when any
  literal names a variable outside `1..nVars`. That is what the executable does
  too: `get_step_var` returns `none`, `add_gate!` prints an error and returns
  the map unchanged, so the clause occupies no step. Literal `0` is dropped by
  exactly this rule.

DIMACS numbers variables from 1; `Cnf` numbers them from 0. The conversion
happens here and nowhere else.
-/

namespace AbsSat.Cnf.Dimacs

open AbsSat.Cnf

/-- One literal token, after `-` has been rewritten to `!`. `none` means the
executable would have dropped the whole clause. -/
def parseLit (nVars : Nat) (tok : String) : Option Lit :=
  let neg := tok.startsWith "!" || tok.startsWith "-"
  let body := if neg then tok.drop 1 else tok
  match body.toNat? with
  | none => none
  | some i => if 1 ≤ i && i ≤ nVars then some { v := i - 1, pos := !neg } else none

def parseClause (nVars : Nat) (line : String) : Option Clause :=
  let toks := (line.splitOn " ").filter (fun s => s.length > 0)
  match toks with
  | t1 :: t2 :: t3 :: _ =>
    match parseLit nVars t1, parseLit nVars t2, parseLit nVars t3 with
    | some l1, some l2, some l3 => some { l1 := l1, l2 := l2, l3 := l3 }
    | _, _, _ => none
  | _ => none

/-- `p cnf n m` → `n`. Mirrors `cnf_p!`'s pattern, which ignores the clause
count and never checks the first token. -/
def parseHeader (line : String) : Option Nat :=
  match (line.splitOn " ").filter (fun s => s.length > 0) with
  | _ :: "cnf" :: nStr :: _ => nStr.toNat?
  | _ => none

private def isComment (line : String) : Bool :=
  line.startsWith "c" || (line.splitOn " ").all (fun t => t.length == 0)

private def isStop (line : String) : Bool :=
  line.startsWith "%" || line.startsWith "0"

def parseGo (nVars : Nat) : List String → List Clause → List Clause
  | [], acc => acc.reverse
  | line :: rest, acc =>
    if isStop line then acc.reverse
    else if isComment line then parseGo nVars rest acc
    else
      match parseClause nVars line with
      | some c => parseGo nVars rest (c :: acc)
      | none => parseGo nVars rest acc

def parse (lines : List String) : Except String Cnf :=
  match lines.find? (fun l => !isComment l && !isStop l) with
  | none => .error "dimacs: no header line"
  | some header =>
    match parseHeader header with
    | none => .error s!"dimacs: bad header {header}"
    | some n =>
      let body := (lines.dropWhile (fun l => isComment l || decide (l ≠ header))).drop 1
      .ok { nVars := n, clauses := parseGo n body [] }

-- ============================================================
-- Well-formedness, decided
-- ============================================================

def clauseWfB (n : Nat) (c : Clause) : Bool :=
  decide (c.l1.v < n) && decide (c.l2.v < n) && decide (c.l3.v < n)
  && decide (c.l1.step ≠ c.l2.step) && decide (c.l1.step ≠ c.l3.step)
  && decide (c.l2.step ≠ c.l3.step)

def wfB (φ : Cnf) : Bool := φ.clauses.all (clauseWfB φ.nVars)

theorem clauseWfB_sound (n : Nat) (c : Clause) (h : clauseWfB n c = true) :
    Clause.WF n c := by
  simp only [clauseWfB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2⟩, h.1.1.2, h.1.2, h.2⟩

theorem wfB_sound (φ : Cnf) (h : wfB φ = true) : WF φ := by
  intro c hc
  exact clauseWfB_sound φ.nVars c (List.all_eq_true.mp h c hc)

/-- info: 'AbsSat.Cnf.Dimacs.wfB_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wfB_sound

end AbsSat.Cnf.Dimacs
