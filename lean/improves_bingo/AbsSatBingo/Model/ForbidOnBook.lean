-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnBook.lean
import AbsSatBingo.Model.ForbidOn
import AbsSatBingo.Model.Bookkeeping
import AbsSatBingo.Model.ClosedReview
import AbsSatBingo.Model.SideLinks

/-!
# La contabilidad con `FORBID = :on` (`docs/plans/lean_forbid_on.md`, F3)

La regla de tríos solo hace dos cosas con el grafo: escribe tríos (cambia `trios`, que ningún invariante de
contabilidad mira) y quita aristas con `removeEdge`, seguido de la limpieza. Las dos son primitivas de `RevPrims`.
Así que **todo invariante `RevPrims` que no mira los tríos (`TrioBlind`) lo conserva también el review `:on`**
(`revPrimsOn_reviewOn`), y el filtro con él (`revPrimsOn_filterAllOn`). Los invariantes de siempre (`EdgesAlive`,
`NodupIds`, …) no miran `trios`, y su `TrioBlind` es la identidad.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

variable {P : GPathB → Prop}

/-- El invariante no mira los tríos. -/
def TrioBlind (P : GPathB → Prop) : Prop := ∀ g (T : List (PathNodeId × PathNodeId × PathNodeId)), P g → P { g with trios := T }

theorem revPrims_addTrios (hb : TrioBlind P) (g : GPathB) (i : Idx) (ts : List (PathNodeId × PathNodeId × PathNodeId))
    (hg : P g) : P (g.addTrios i ts).1 := by
  unfold addTrios
  exact hb _ _ hg

theorem revPrims_forbidRound (h : RevPrims P) (hb : TrioBlind P) (g : GPathB) (hg : P g) : P g.forbidRound.1 := by
  have h1 := revPrims_addTrios hb g (Idx.of g) (g.newTrios (Idx.of g)) hg
  unfold forbidRound
  simp only
  split
  · exact h1
  · exact revPrims_clean h _ (h.dirty _ _ (inv_foldl P (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) _
      (fun g' e _ hc => h.rmEdge _ _ _ hc) _ h1))

theorem revPrims_forbidFuel (h : RevPrims P) (hb : TrioBlind P) :
    ∀ (n : Nat) (g : GPathB), P g → P (forbidFuel n g) := by
  intro n
  induction n with
  | zero => intro g hg; exact hg
  | succ n ih =>
    intro g hg
    unfold forbidFuel
    split
    · simp only
      split
      · exact ih _ (revPrims_forbidRound h hb g hg)
      · exact revPrims_forbidRound h hb g hg
    · exact hg

theorem revPrims_forbidRule (h : RevPrims P) (hb : TrioBlind P) (g : GPathB) (hg : P g) : P g.forbidRule :=
  revPrims_forbidFuel h hb _ g hg

theorem revPrims_reviewPassOn (h : RevPrims P) (hb : TrioBlind P) (g : GPathB) (hg : P g) : P g.reviewPassOn := by
  have h1 := revPrims_forbidRule h hb _ (revPrims_cleanPair h g hg)
  have h2 := h.links _ h1
  have h3 : P g.cleanPair.forbidRule.pruneLinks.reviewParents := by
    unfold reviewParents; split
    · exact revPrims_reviewSteps h _ _ _ h2
    · exact h2
  have h4 : P g.cleanPair.forbidRule.pruneLinks.reviewParents.reviewSons := by
    unfold reviewSons; split
    · exact revPrims_reviewSteps h _ _ _ h3
    · exact h3
  exact h.links _ h4

/-- **Todo invariante que conservan la vuelta `:on` y la comprobación final lo conserva el review `:on`.** -/
theorem reviewFuelOn_pres (P : GPathB → Prop) (hpass : ∀ g, P g → P (reviewPassOn { g with dirty := false }))
    (hfin : ∀ g, P g → P (finalPass g)) : ∀ (n : Nat) (g : GPathB), P g → P (reviewFuelOn n g) := by
  intro n
  induction n with
  | zero => intro g hg; exact hg
  | succ n ih =>
    intro g hg
    unfold reviewFuelOn
    split
    · simp only
      split
      · exact ih _ (hpass g hg)
      · split
        · split
          · exact ih _ (hfin _ (hpass g hg))
          · exact hpass g hg
        · exact hpass g hg
    · exact hg

theorem revPrims_reviewOn (h : RevPrims P) (hb : TrioBlind P) (g : GPathB) (hg : P g) : P g.reviewOn :=
  reviewFuelOn_pres P (fun _ hh => revPrims_reviewPassOn h hb _ (h.dirty _ _ hh)) (fun g' hh => revPrims_finalPass h g' hh)
    _ g hg

theorem revPrims_filterAllOn (h : RevPrims P) (hb : TrioBlind P) (g : GPathB) (reqs : List NodeId) (hg : P g) :
    P (g.filterAllOn reqs) := by
  unfold filterAllOn
  apply revPrims_reviewOn h hb
  refine inv_foldl P filterRequire reqs (fun g' r _ hc => ?_) g hg
  unfold filterRequire
  split
  · exact h.dirty _ _ (inv_foldl P killVertex _ (fun g'' q _ hc' => h.kill _ _ hc') g' hc)
  · exact hc

-- Los invariantes de siempre no miran los tríos.

theorem trioBlind_edgesAlive : TrioBlind EdgesAlive := fun _ _ h => h
theorem trioBlind_nodupIds : TrioBlind NodupIds := fun _ _ h => h
theorem trioBlind_aboveZero : TrioBlind AboveZero := fun _ _ h => h
theorem trioBlind_linksStep : TrioBlind LinksStep := fun _ _ h => h
theorem trioBlind_below : TrioBlind Machine.Below := fun _ _ h => h
theorem trioBlind_linksInv : TrioBlind LinksInv := fun _ _ h => h
theorem trioBlind_aliveDocs : TrioBlind AliveDocs := fun _ _ h => h

end GPathB

end AbsSatBingo.Model
