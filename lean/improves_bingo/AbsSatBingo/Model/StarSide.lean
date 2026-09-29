-- lean/improves_bingo/AbsSatBingo/Model/StarSide.lean
import AbsSatBingo.Model.StarLine

/-!
# `StarJoinDown` ⇐ una vuelta de trío en el lado de la cima (`TrioSideAt`)

En el join, la estrella de una cima `t` de la unión se baja al lado `L` donde vive `t`. El candidato explícito es
la vuelta de trío de `StarTrio.lean`, con las parejas que son a la vez de la estructura y del lado:

> `sideRel L R x w := R x w ∧ L.Adj x w`, y la estructura `{x ∈ V | sideRel L R x t}` con `trioRel L (sideRel L R) t`.

Medido (`julia/improves_bingo/test_3sat/probe_join_star_fix.jl`): el review del lado restringido a la estrella llega
exactamente a esa vuelta (mismas aristas, ningún nodo perdido).

**`TrioSideAt u L`**: esa estructura es cerrada en `L`. **`starJoinDown_of_trioSide`**: con `TopsApart` en los dos
lados, `TrioSideAt` en los dos da `StarJoinDown` (el testigo de `z` en la cima dentro de la estructura es `t`).
Veredicto: **`readerVerdict_iff_of_trioSide`**, bajo `TrioSideAt` y `SideEdgesAt` en los joins.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

/-- Las parejas de la estructura que también son del lado. -/
def sideRel (L : GPathB) (R : PathNodeId → PathNodeId → Prop) (x w : PathNodeId) : Prop := R x w ∧ L.Adj x w

/-- **La vuelta de trío en el lado es cerrada**, para toda cima de `u` viva en `L`. -/
def TrioSideAt (u L : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R →
    ∀ t, V t → t.id.step = u.current_step - 1 → t ∈ L.alive →
    SecStruct L (fun x => V x ∧ sideRel L R x t) (trioRel L (sideRel L R) t)

/-- Un lado: la vuelta de trío da la estructura que pide `StarJoinDown`. -/
theorem side_down {u L : GPathB} (hcs : L.current_step = u.current_step) (hpos : 0 < L.current_step)
    (hta : TopsApart L) (hT : TrioSideAt u L) {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (hst : SecStruct u V R) {t z : PathNodeId} (htV : V t) (hts : t.id.step = u.current_step - 1)
    (hzV : V z) (hzt : R z t) (hzL : L.Adj z t) (htL : t ∈ L.alive) :
    ∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
      SecStruct L V' R' ∧ V' z ∧ V' t ∧ R' z t ∧ ∀ y, V' y → V y := by
  have hS := hT V R hst t htV hts htL
  have hz' : V z ∧ sideRel L R z t := ⟨hzV, hzt, hzL⟩
  obtain ⟨r, hrs, hzr, _⟩ := hS.pair (hS.refl hz') (L.current_step - 1) (by omega) (by omega)
  have hrW := (hS.dom hzr).2
  have hrt : r = t := hta r t hrs (by rw [hts, hcs]) hrW.2.2
  subst hrt
  exact ⟨_, _, hS, hz', ⟨htV, hst.refl htV, adj_refl L _ htL⟩, hzr, fun y hy => hy.1⟩

/-- **`TrioSideAt` en los dos lados ⟹ `StarJoinDown`.** -/
theorem starJoinDown_of_trioSide {e g : GPathB} (hcs : e.current_step = g.current_step) (hpos : 0 < e.current_step)
    (htae : TopsApart e) (htag : TopsApart g) (heae : EdgesAlive e) (heag : EdgesAlive g)
    (hTe : TrioSideAt (join e g) e) (hTg : TrioSideAt (join e g) g) : StarJoinDown e g := by
  have hje : (join e g).current_step = e.current_step := rfl
  intro V R hst t htV hts z hzV hzt
  rcases adj_join_cases (hst.adj hzt) with h | h
  · obtain ⟨V', R', h1, h2, h3, h4, h5⟩ := side_down (L := e) hje.symm hpos htae hTe hst htV hts hzV hzt h (heae z t h).2
    exact ⟨V', R', Or.inl h1, h2, h3, h4, h5⟩
  · obtain ⟨V', R', h1, h2, h3, h4, h5⟩ :=
      side_down (L := g) (hje.trans hcs).symm (hcs ▸ hpos) htag hTg hst htV hts hzV hzt h (heag z t h).2
    exact ⟨V', R', Or.inr h1, h2, h3, h4, h5⟩

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- **Las hipótesis**: `TrioSideAt` en los dos lados y `SideEdgesAt` en cada join. -/
structure HypsTrioSide (φ : Cnf) : Prop where
  trio : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g →
    TrioSideAt (join e g) e ∧ TrioSideAt (join e g) g
  side : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g → SideEdgesAt e g (T - 2)

/-- **El veredicto del lector es la satisfacibilidad bajo `TrioSideAt` y `SideEdgesAt` en los joins.** -/
theorem readerVerdict_iff_of_trioSide {φ : Cnf} (hbd : Bounded φ) (H : HypsTrioSide φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_starJoinDown hbd ⟨fun T key e g hT he hg hke hkg =>
    have ht := H.trio T key e g hT he hg hke hkg
    starJoinDown_of_trioSide (he.step.trans hg.step.symm) (by rw [he.step]; omega) hke.1.2.1 hkg.1.2.1
      hke.1.1.2.2.2.1 hkg.1.1.2.2.2.1 ht.1 ht.2, H.side⟩

end SecLine

end AbsSatBingo.Model
