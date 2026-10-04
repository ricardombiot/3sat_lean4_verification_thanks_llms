-- lean/improves_bingo/AbsSatBingo/Model/SideDescent.lean
import AbsSatBingo.Model.UnionEquiv

/-!
# `SideEdges` por el estado fijado y el paso de los hijos

* **`sideEdges_of_pinClean`**: `SideEdges` se sigue de `PinClean`, que el review de la unión fijada en `b` no deje
  aristas de un solo lado (una estructura cerrada sobrevive al pin: `pinEdge_of_kernel`). Medido directamente:
  `probe_side_cut.jl`, 0 supervivientes de 513006 aristas vigiladas.
* **`son_step`** (el paso de la inducción descendente): si las parejas de la estructura por encima del paso `m` son
  de `e`, una pareja (x, z) con `x` en `m` y `z` por debajo o al lado da un hijo `s` de `x` en `e` con x–s y s–z
  aristas de `e` (la regla de hijos, `LinksInv`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- El review de la unión fijada en `b` no deja aristas que `e` no tenga. -/
def PinClean (u e : GPathB) (b : NodeId) : Prop :=
  ∀ y w, PinEdge (u.filterAll [b]) y w → e.Adj y w

theorem sideEdges_of_pinClean {u e : GPathB} {b : NodeId} (h : PinClean u e b) : SideEdges u e b := by
  intro V R hst ha y w hr
  exact h y w (pinEdge_of_kernel (P := [b]) ⟨V, R, hst, fun b' hb' => by
    rw [List.mem_singleton] at hb'; subst hb'; exact ha, hr⟩)

/-- Las parejas de la estructura por encima del paso `m` son posesiones de `e`. -/
def UpperClean (e : GPathB) (R : PathNodeId → PathNodeId → Prop) (m : Int) : Prop :=
  ∀ {y w}, R y w → m < y.id.step ∨ m < w.id.step → e.Adj y w

/-- **El paso de los hijos.** -/
theorem son_step {u e g : GPathB} (hu : IsUnion u e g) {V : PathNodeId → Prop}
    {R : PathNodeId → PathNodeId → Prop} {b : NodeId} (hst : SecStruct u V R) (ha : SecAgrees V b)
    (hb0 : 0 ≤ b.step) (hbc : b.step < e.current_step) (hoff : OffSide g b) (hle : LinksInv e)
    (hee : EdgesAlive e) (heg : EdgesAlive g) {m : Int} (hup : UpperClean e R m) {x z : PathNodeId}
    (hxz : R x z) (hne : x ≠ z) (hx : x.id.step = m) (hc : m + 1 < e.current_step) :
    ∃ n s, e.node? x = some n ∧ s ∈ n.sons ∧ e.Adj x s ∧ e.Adj s z ∧ s.id.step = m + 1 := by
  have hal : ∀ {y}, V y → y ∈ e.alive := fun hy => alive_side hu hst ha hb0 hbc hoff hee heg hy
  obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hu.docs (hst.alive (hst.dom hxz).1))
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hle.1 (hal (hst.dom hxz).1))
  obtain ⟨s, hs, hxs, hsz⟩ := hst.son hxz hne hnu (by rw [hu.step, hx]; exact hc)
  have hss : s.id.step = m + 1 := by
    have := (hu.compat nu (node?_mem hnu)).2 s hs
    rw [node?_id hnu] at this
    have := this.2.2; omega
  have h1 : e.Adj x s := hup hxs (Or.inr (by omega))
  have h2 : e.Adj s z := hup hsz (Or.inl (by omega))
  have hnid := node?_id hn
  have hl := link_side hle hu.compat (node?_mem hn) (node?_mem hnu) ((node?_id hnu).trans hnid.symm)
    (hal (hst.dom hxs).2) (hnid ▸ h1)
  exact ⟨n, s, hn, hl.2 hs, h1, h2, hss⟩

end GPathB

end AbsSatBingo.Model
