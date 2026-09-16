-- lean_project/AbsSat/GraphPath/Model/PureDriverImproves.lean
import AbsSat.GraphPath.Model.PureDriver
import AbsSat.GraphMap.CnfMapImproves
import AbsSat.Cnf.BruteForce
import AbsSat.GraphPath.Model.AggressiveReview

/-!
# The driver, fed the weak requirements

`PureDriver` sends a state to a map node `d` through
`upFiltering g (reqOfCnf φ d) d`. This driver makes two changes. Before the pins, the global
owners are first restricted by `CnfMapImproves.weakReqOfCnf`. And the review is the **aggressive
review** of `AggressiveReview` (the author's `agressive_consistence_filter!` inside the review loop),
which also drops owner pairs that no path can contain together:

    upFilteringWeak g ws reqs d = up (filterAllAgg (filterWeakAll g ws) reqs) d

`filterWeak` is `filterRequire` with a set in place of a single node: at the
entry's step a global owner survives only if its map node is one of the
entry's nodes; at every other step it is untouched. With no entries it is the
identity, so off the clause steps this driver differs from `PureDriver` only by its review
(`upFilteringWeak_nil`).

An empty weak set leaves its step with no global owner, `isValid` fails, and
`sendToW` drops the state — the early death, with nothing added for it.

**What is proved here.** The frame of the filter (it touches only `gowners`,
and exactly as `mem_filterWeakAll` says). The driver-level conservation — no solution is lost,
`pureRunW_ne_nil` — is `ConservationImproves`. The `#guard`s below compare the
verdict with `PureDriver` and with the brute-force oracle.
-/

namespace AbsSat.GraphPath.Model.PureDriverImproves

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (mapSons)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver

-- ============================================================
-- The weak filter
-- ============================================================

/-- Restrict the global owners at step `e.1` to the map nodes `e.2`. -/
def filterWeak (g : GPathM) (e : Int × List NodeId) : GPathM :=
  { g with gowners := g.gowners.filter (fun q => q.id.step != e.1 || e.2.contains q.id) }

def filterWeakAll (g : GPathM) (ws : List (Int × List NodeId)) : GPathM :=
  ws.foldl filterWeak g

/-- Weak filter first, then the hard requirements and the aggressive review, then UP. -/
def upFilteringWeak (g : GPathM) (ws : List (Int × List NodeId)) (reqs : List NodeId)
    (d : NodeId) (title : String) : GPathM :=
  up (AggressiveReview.filterAllAgg (filterWeakAll g ws) reqs) d title

-- ============================================================
-- The driver
-- ============================================================

def sendToW (φ : Cnf) (g : GPathM) (next : PureLine) (d : NodeId) : PureLine :=
  if isValid (upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d "") then
    insertPure next d (upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d "")
  else next

def sendAllW (φ : Cnf) (kv : NodeId × GPathM) (next : PureLine) : PureLine :=
  (mapSons φ kv.1.step kv.1.index).foldl (sendToW φ kv.2) next

def pureAdvanceW (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv => sendAllW φ kv next) []

def pureStepsW (φ : Cnf) : Nat → PureLine → PureLine
  | 0, line => line
  | n + 1, line => pureStepsW φ n (pureAdvanceW φ line)

/-- The whole run, from `PureDriver`'s own first line. Empty means UNSAT. -/
def pureRunW (φ : Cnf) : PureLine := pureStepsW φ (stepCount φ - 1).toNat (pureInit φ)

-- ============================================================
-- The frame of the filter
-- ============================================================

theorem filterWeakAll_nil (g : GPathM) : filterWeakAll g [] = g := rfl

theorem upFilteringWeak_nil (g : GPathM) (reqs : List NodeId) (d : NodeId) (title : String) :
    upFilteringWeak g [] reqs d title = up (AggressiveReview.filterAllAgg g reqs) d title := rfl

/-- The filter touches nothing but the global owners. -/
theorem filterWeakAll_frame (ws : List (Int × List NodeId)) :
    ∀ g : GPathM, (filterWeakAll g ws).nodes = g.nodes
      ∧ (filterWeakAll g ws).current_step = g.current_step
      ∧ (filterWeakAll g ws).map_parent = g.map_parent := by
  induction ws with
  | nil => intro g; exact ⟨rfl, rfl, rfl⟩
  | cons e ws ih =>
    intro g
    simp only [filterWeakAll, List.foldl_cons] at ih ⊢
    obtain ⟨h1, h2, h3⟩ := ih (filterWeak g e)
    exact ⟨h1, h2, h3⟩

/-- **Exactly what survives.** A global owner survives the weak filter iff it
was there, and at every step some entry names, its map node is one of that
entry's nodes. -/
theorem mem_filterWeakAll (ws : List (Int × List NodeId)) :
    ∀ (g : GPathM) (q : PathNodeId), q ∈ (filterWeakAll g ws).gowners ↔
      q ∈ g.gowners ∧ ∀ e ∈ ws, q.id.step = e.1 → q.id ∈ e.2 := by
  induction ws with
  | nil => intro g q; simp [filterWeakAll]
  | cons e ws ih =>
    intro g q
    simp only [filterWeakAll, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [filterWeak, List.mem_filter, List.mem_cons, Bool.or_eq_true, bne_iff_ne, ne_eq,
      List.contains_iff_mem]
    constructor
    · rintro ⟨⟨hq, he⟩, hws⟩
      refine ⟨hq, fun e' he' hs => ?_⟩
      rcases he' with rfl | he'
      · rcases he with hne | hmem
        · exact absurd hs hne
        · exact hmem
      · exact hws e' he' hs
    · rintro ⟨hq, hall⟩
      refine ⟨⟨hq, ?_⟩, fun e' he' hs => hall e' (Or.inr he') hs⟩
      by_cases hs : q.id.step = e.1
      · exact Or.inr (hall e (Or.inl rfl) hs)
      · exact Or.inl hs

-- ============================================================
-- Verdicts against `PureDriver` and the oracle
-- ============================================================

private def pos (v : Nat) : Lit := ⟨v, true⟩
private def neg (v : Nat) : Lit := ⟨v, false⟩

/-- Satisfiable; clauses share variables with both polarities. -/
private def sat3 : Cnf :=
  { nVars := 4,
    clauses := [⟨pos 0, pos 1, pos 2⟩, ⟨neg 0, pos 1, pos 3⟩, ⟨pos 0, neg 1, neg 2⟩,
                ⟨neg 1, neg 2, neg 3⟩] }

/-- Unsatisfiable: all eight sign patterns over three variables. -/
private def unsat3 : Cnf :=
  { nVars := 3,
    clauses := [⟨pos 0, pos 1, pos 2⟩, ⟨pos 0, pos 1, neg 2⟩, ⟨pos 0, neg 1, pos 2⟩,
                ⟨pos 0, neg 1, neg 2⟩, ⟨neg 0, pos 1, pos 2⟩, ⟨neg 0, pos 1, neg 2⟩,
                ⟨neg 0, neg 1, pos 2⟩, ⟨neg 0, neg 1, neg 2⟩] }

private def verdicts (φ : Cnf) : Bool × Bool × Bool :=
  (!(pureRunW φ).isEmpty, !(pureRun φ).isEmpty, !(bruteForceSat φ).isEmpty)

#guard verdicts sat3 == (true, true, true)
#guard verdicts unsat3 == (false, false, false)

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.PureDriverImproves.mem_filterWeakAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_filterWeakAll

end AbsSat.GraphPath.Model.PureDriverImproves
