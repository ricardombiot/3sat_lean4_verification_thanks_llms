-- lean_project/AbsSat/SatMachine/ImprovesLoad.lean
import AbsSat.SatMachine.PureSatMachineImproves
import AbsSat.Cnf.BruteForce

/-! # Review load: `SatMachinePure` against `SatMachinePureImproves`

Measurement only — no theorems. For every send the reference driver performs
(state `g` from its own line, destination `d`), the same send is also filtered
the improved way, and both reviews are compared:

* **passes** — `reviewPass` rounds until the fixpoint, counted as `reviewFuel` runs them;
* **reviewDrop** — how much of `GPathM.measure` the review removes;
* **deadBeforeReview** — sends already invalid after the filters, which skip the review;
* **weakCut** — global owners removed by `filterWeakAll` itself;
* **sameReview** — both reviews end equally valid with the same number of global owners.

The two whole runs are also compared on their final lines: keys, and per state
the number of global owners and of nodes.
-/

namespace AbsSat.SatMachine.ImprovesLoad

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (mapSons)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.PureDriverImproves

def passes : Nat → GPathM → Nat
  | 0, _ => 0
  | fuel + 1, g =>
    if isValid g then
      let g' := reviewPass g
      if measure g' < measure g then 1 + passes fuel g' else 1
    else 0

structure Load where
  sends : Nat := 0
  weakSends : Nat := 0
  passesBase : Nat := 0
  passesWeak : Nat := 0
  dropBase : Nat := 0
  dropWeak : Nat := 0
  deadBase : Nat := 0
  deadWeak : Nat := 0
  weakCut : Nat := 0
  sameReview : Bool := true
  deriving Repr

def Load.add (s : Load) (φ : Cnf) (g : GPathM) (d : NodeId) : Load :=
  let ws := weakReqOfCnf φ d
  let reqs := reqOfCnf φ d
  let gw := filterWeakAll g ws
  let g0 := reqs.foldl filterRequire g
  let g0w := reqs.foldl filterRequire gw
  let r := review g0
  let rw := review g0w
  { sends := s.sends + 1
    weakSends := s.weakSends + (if ws.isEmpty then 0 else 1)
    passesBase := s.passesBase + passes (measure g0 + 1) g0
    passesWeak := s.passesWeak + passes (measure g0w + 1) g0w
    dropBase := s.dropBase + (measure g0 - measure r)
    dropWeak := s.dropWeak + (measure g0w - measure rw)
    deadBase := s.deadBase + (if isValid g0 then 0 else 1)
    deadWeak := s.deadWeak + (if isValid g0w then 0 else 1)
    weakCut := s.weakCut + (g.gowners.length - gw.gowners.length)
    sameReview := s.sameReview && isValid r == isValid rw &&
      (!isValid r || r.gowners.length == rw.gowners.length) }

/-- Walk the reference run, measuring every send both ways. -/
def load (φ : Cnf) : Load := Id.run do
  let mut line := pureInit φ
  let mut s : Load := {}
  for _ in [0:(stepCount φ - 1).toNat] do
    for kv in line do
      for d in mapSons φ kv.1.step kv.1.index do
        s := s.add φ kv.2 d
    line := pureAdvance φ line
  return s

/-- A line's shape: keys, and per state its global owners and nodes. -/
def shape (line : PureLine) : List (NodeId × Nat × Nat) :=
  line.map (fun kv => (kv.1, kv.2.gowners.length, kv.2.nodes.length))

def pct (a b : Nat) : String :=
  if a = 0 then "0%" else
    let d : Int := (b : Int) - (a : Int)
    s!"{if d > 0 then "+" else ""}{d * 100 / (a : Int)}%"

-- ============================================================
-- Deterministic random 3-CNF (distinct variables per clause)
-- ============================================================

def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

def randCnf (seed n m : Nat) : Cnf := Id.run do
  let mut x := seed
  let mut cs : List Clause := []
  for _ in [0:m] do
    let mut vs : List Nat := []
    for _ in [0:64] do
      if vs.length < 3 then
        x := lcg x
        let v := (x / 65536) % n
        if !vs.contains v then vs := vs ++ [v]
    let mut ls : List Lit := []
    for v in vs do
      x := lcg x
      ls := ls ++ [⟨v, (x / 65536) % 2 == 0⟩]
    let dflt : Lit := ⟨0, true⟩
    cs := cs ++ [⟨ls.getD 0 dflt, ls.getD 1 dflt, ls.getD 2 dflt⟩]
  return { nVars := n, clauses := cs }

end AbsSat.SatMachine.ImprovesLoad
