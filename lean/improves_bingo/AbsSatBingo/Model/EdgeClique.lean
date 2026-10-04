-- lean/improves_bingo/AbsSatBingo/Model/EdgeClique.lean
import AbsSatBingo.Model.Grow
import AbsSatBingo.Model.SecInduction

/-!
# `EdgeClique`: todo lo vivo está en una camarilla válida

La frase del autor: el review de cada paso limpia los nodos incoherentes y deja únicamente las camarillas válidas.
**`EdgeClique g`**: toda pareja que se posee (toda arista, y todo nodo vivo por la reflexiva) está en una camarilla
llevada (`Carried`). Medido en Julia (`julia/improves_bingo/test_3sat/probe_edgeclique.jl`, espejo
`GraphPath.edge_clique_miss`): 0 aristas y 0 nodos sin cubrir en cada punto de la máquina.

Demostrado aquí:
* **`noDeadEnd_of_edgeClique`**: `EdgeClique` da `NoDeadEndAt` directamente (la camarilla de un vivo del paso con
  elección sobrevive al pin de su nodo del mapa, `carried_filterAll`).
* **`secPair_of_edgeClique`**: y también `SecPair` (la camarilla es una sección, `secClosed_of_carried`).
* **`edgeClique_doJoin`**: el join lo conserva (una camarilla de un lado lo es de la unión).

Plan (docs/plans/lean_bingo.md): el UP por herencia, y el único lema de fondo, `ReviewExact` (tras seleccionar `b`
y revisar, toda pareja está en una camarilla que pasa por `b`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

open Driver

/-- `y` y `w` están en una misma camarilla llevada. -/
def OnClique (g : GPathB) (y w : PathNodeId) : Prop :=
  ∃ S, Carried g S ∧ OnS g.current_step S y ∧ OnS g.current_step S w

/-- **`EdgeClique`**: toda pareja que se posee está en una camarilla llevada. -/
def EdgeClique (g : GPathB) : Prop := ∀ y w, g.Adj y w → OnClique g y w

theorem onClique_self {g : GPathB} (h : EdgeClique g) {q : PathNodeId} (hq : q ∈ g.alive) :
    ∃ S, Carried g S ∧ ∃ k, 0 ≤ k ∧ k < g.current_step ∧ S k = q := by
  obtain ⟨S, hc, hy, _⟩ := h q q (adj_refl g q hq)
  exact ⟨S, hc, hy⟩

-- ============================================================
-- Lo que da EdgeClique
-- ============================================================

/-- **`EdgeClique` da `NoDeadEndAt`**: en un paso con elección, el nodo del mapa de cualquier vivo deja un pin
válido. -/
theorem noDeadEnd_of_edgeClique {g : GPathB} (h : EdgeClique g) : NoDeadEndAt g := by
  intro k hk
  obtain ⟨q, _, hq, _, hqk, _, _⟩ := choiceAt_spec hk
  obtain ⟨S, hc, j, hj0, hj1, rfl⟩ := onClique_self h hq
  refine ⟨S j, hq, hqk, ?_⟩
  have hcar := carried_filterAll hc [(S j).id] (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    intro h0 h1
    rw [hc.step j hj0 hj1])
  exact isValid_of_carried hcar

/-- **`EdgeClique` da `SecPair`**: la camarilla de una arista elige un nodo en cada paso, y es una sección de él. -/
theorem secPair_of_edgeClique {g : GPathB} (h : EdgeClique g) : SecPair g := by
  intro k hk y w _ _ hyw _
  obtain ⟨S, hc, hy, hw⟩ := h y w hyw
  obtain ⟨q, _, hq, _, hqk, _, _⟩ := choiceAt_spec hk
  obtain ⟨S', hc', j, hj0, hj1, hS'⟩ := onClique_self h hq
  have hk0 : 0 ≤ k := by rw [← hqk, ← hS', hc'.step j hj0 hj1]; exact hj0
  have hk1 : k < g.current_step := by rw [← hqk, ← hS', hc'.step j hj0 hj1]; exact hj1
  refine ⟨(S k).id, _, hc.step k hk0 hk1, (secClosed_of_carried hc hk0 hk1).toSecClosed (hc.alive k hk0 hk1), hy, hw⟩

-- ============================================================
-- El join
-- ============================================================

/-- Lo que se posee en la unión se poseía en algún lado. -/
theorem adj_join_cases {g₁ g₂ : GPathB} {a b : PathNodeId} (h : (join g₁ g₂).Adj a b) :
    g₁.Adj a b ∨ g₂.Adj a b := by
  rw [adj_iff] at h
  rcases h with ⟨rfl, hal⟩ | ⟨e, he, hj⟩
  · rcases (alive_join g₁ g₂ a).mp hal with h1 | h2
    · exact Or.inl (adj_refl _ _ h1)
    · exact Or.inr (adj_refl _ _ h2)
  · simp only [join, List.mem_append, List.mem_filter] at he
    rcases he with h1 | ⟨h2, _⟩
    · exact Or.inl ((adj_iff _ _ _).mpr (Or.inr ⟨e, h1, hj⟩))
    · exact Or.inr ((adj_iff _ _ _).mpr (Or.inr ⟨e, h2, hj⟩))

/-- **El join conserva `EdgeClique`.** -/
theorem edgeClique_doJoin {g₁ g₂ : GPathB} (h₁ : EdgeClique g₁) (h₂ : EdgeClique g₂) :
    EdgeClique (doJoin g₁ g₂) := by
  unfold doJoin
  split
  · rename_i hok
    have hcs : g₁.current_step = g₂.current_step := by
      unfold okJoin at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      exact hok.1.1.1
    have hjs : (join g₁ g₂).current_step = g₁.current_step := rfl
    intro y w hyw
    rcases adj_join_cases hyw with ha | ha
    · obtain ⟨S, hc, hy, hw⟩ := h₁ y w ha
      exact ⟨S, carried_join_left hc, hjs ▸ hy, hjs ▸ hw⟩
    · obtain ⟨S, hc, hy, hw⟩ := h₂ y w ha
      exact ⟨S, carried_join_right hcs hc, by rw [hjs, hcs]; exact hy, by rw [hjs, hcs]; exact hw⟩
  · exact h₁

end GPathB

end AbsSatBingo.Model
