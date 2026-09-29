-- lean/improves_bingo/AbsSatBingo/Model/Spine.lean
import AbsSatBingo.Model.ClosedReview

/-!
# La espina: el lector sin retroceso por caminos de documentos (primeras piezas)

Prototipo en Julia (`probe_pathreader.jl`): sobre el estado final, se fija una cima y se baja por padres; en cada paso
se toma el primer padre del último elegido que sea vecino de **todo** lo elegido. Sin retroceso, 28/28 instancias
SAT leídas correctamente.

Aquí, las piezas que el paso de la espina necesita en un estado cerrado (`ClosedState`, que la revisión garantiza por
`closedState_review`):

* **`forced_parent`**: si el último elegido `x` tiene un único padre vivo poseído `p`, todo vecino de `x` posee a `p`.
  Con un padre, el paso es forzado y nunca se atasca.
* **`two_helly`**: si cada par de elementos tiene un común entre dos candidatos `a`, `b`, uno de los dos sirve para
  todos (subconjuntos no vacíos de un conjunto de dos que se cortan dos a dos comparten un elemento).
* **`parent_for_chain`**: con como mucho dos padres vivos, el paso de la espina solo necesita **`ChainTrio`**: para cada
  par de elegidos, algún padre del último es vecino de los dos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- `p` es un padre de `x` (según su documento `n`) vivo y poseído por `x`. -/
def LiveParent (g : GPathB) (n : PNodeB) (x p : PathNodeId) : Prop := p ∈ n.parents ∧ p ∈ g.alive ∧ g.Adj x p

/-- **El paso forzado**: con un único padre vivo poseído, ese padre posee a todo vecino de `x`. -/
theorem forced_parent {g : GPathB} (hcl : ClosedState g) {x : PathNodeId} {n : PNodeB} (hn : g.node? x = some n)
    (hx1 : 1 ≤ x.id.step) (hx : x ∈ g.alive) {p : PathNodeId} (huniq : ∀ q, LiveParent g n x q → q = p)
    {w : PathNodeId} (hw : w ∈ g.alive) (hxw : g.Adj x w) (hne : x ≠ w) : g.Adj p w := by
  obtain ⟨q, hq, hxq, hqw⟩ := hcl.par (x := x) (w := w) ⟨hx, hw, hxw⟩ hne hn hx1
  have := huniq q ⟨hq, hxq.2.1, hxq.2.2⟩
  subst this
  exact hqw.2.2

/-- **Helly en un conjunto de dos**: si cada par tiene un común entre `a` y `b`, uno de los dos sirve para todos. -/
theorem two_helly {α β : Type} (P : α → β → Prop) (a b : α) (K : β → Prop)
    (hpair : ∀ w w', K w → K w' → (P a w ∧ P a w') ∨ (P b w ∧ P b w')) :
    (∀ w, K w → P a w) ∨ (∀ w, K w → P b w) := by
  refine Classical.byCases (p := ∀ w, K w → P a w) Or.inl (fun h => Or.inr ?_)
  intro w hw
  have ⟨w₀, hw₀, hna⟩ : ∃ w₀, K w₀ ∧ ¬ P a w₀ :=
    Classical.byContradiction fun hc => h fun w hw => Classical.byContradiction fun hn => hc ⟨w, hw, hn⟩
  rcases hpair w₀ w hw₀ hw with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact absurd h1 hna
  · exact h2

/-- **ChainTrio**: para cada par de elegidos, algún padre vivo del último elegido es vecino de los dos. -/
def ChainTrio (g : GPathB) (n : PNodeB) (x : PathNodeId) (K : PathNodeId → Prop) : Prop :=
  ∀ w w', K w → K w' → ∃ q, LiveParent g n x q ∧ g.Adj q w ∧ g.Adj q w'

/-- **El paso de la espina**: con como mucho dos padres vivos poseídos (`a`, `b`) y `ChainTrio`, hay un padre vivo
del último elegido que es vecino de todos los elegidos. -/
theorem parent_for_chain {g : GPathB} {x : PathNodeId} {n : PNodeB} {a b : PathNodeId}
    (htwo : ∀ q, LiveParent g n x q → q = a ∨ q = b) (hex : ∃ q, LiveParent g n x q)
    {K : PathNodeId → Prop} (htrio : ChainTrio g n x K) :
    ∃ p, LiveParent g n x p ∧ ∀ w, K w → g.Adj p w := by
  let P : PathNodeId → PathNodeId → Prop := fun q w => LiveParent g n x q ∧ g.Adj q w
  have hpair : ∀ w w', K w → K w' → (P a w ∧ P a w') ∨ (P b w ∧ P b w') := by
    intro w w' hw hw'
    obtain ⟨q, hq, hqw, hqw'⟩ := htrio w w' hw hw'
    rcases htwo q hq with rfl | rfl
    · exact Or.inl ⟨⟨hq, hqw⟩, ⟨hq, hqw'⟩⟩
    · exact Or.inr ⟨⟨hq, hqw⟩, ⟨hq, hqw'⟩⟩
  refine Classical.byCases (p := ∃ w, K w) (fun ⟨w₀, hw₀⟩ => ?_) (fun hK => ?_)
  · rcases two_helly P a b K hpair with h | h
    · exact ⟨a, (h w₀ hw₀).1, fun w hw => (h w hw).2⟩
    · exact ⟨b, (h w₀ hw₀).1, fun w hw => (h w hw).2⟩
  · obtain ⟨q, hq⟩ := hex
    exact ⟨q, hq, fun w hw => absurd ⟨w, hw⟩ hK⟩

/-- **Con un solo padre no hace falta `ChainTrio`**: en un estado cerrado, el único padre vivo poseído es vecino de
todos los vecinos de `x`. -/
theorem parent_for_chain_one {g : GPathB} (hcl : ClosedState g) {x : PathNodeId} {n : PNodeB}
    (hn : g.node? x = some n) (hx1 : 1 ≤ x.id.step) (hx : x ∈ g.alive) {p : PathNodeId}
    (hp : LiveParent g n x p) (huniq : ∀ q, LiveParent g n x q → q = p) {K : PathNodeId → Prop}
    (hK : ∀ w, K w → w ∈ g.alive ∧ g.Adj x w) :
    ∀ w, K w → g.Adj p w := by
  intro w hw
  by_cases hxw : x = w
  · subst hxw; exact (adj_symm _ _ _).mp hp.2.2
  · exact forced_parent hcl hn hx1 hx huniq (hK w hw).1 (hK w hw).2 hxw

end GPathB

end AbsSatBingo.Model
