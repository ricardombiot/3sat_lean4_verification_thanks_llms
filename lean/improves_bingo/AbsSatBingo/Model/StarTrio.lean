-- lean/improves_bingo/AbsSatBingo/Model/StarTrio.lean
import AbsSatBingo.Model.StarNodes

/-!
# El punto fijo del review en la estrella de una cima: una vuelta de la regla de trío (`TrioStar`)

Dentro de una estructura cerrada `(V, R)` y para una cima `t`, la estrella es `W = {x ∈ V | R x t}`. El candidato
explícito para la estructura que pide `StarNodes` es una sola vuelta de la regla de trío:

> `trioRel x w`: `R x w`, los dos en la estrella, y en cada paso un testigo común `r` que también está en ella.

Medido (`julia/improves_bingo/test_3sat/probe_star_fixpoint.jl`): el review de `V` restringida a la estrella llega
exactamente a `trioRel` (mismas aristas, ningún nodo perdido) en todas las estrellas; la estrella tal cual (`R` entre
nodos de `W`) no es cerrada en un 4 % de los núcleos.

**`TrioStar u`**: `trioRel` es una estructura cerrada. **`starNodes_of_trioStar`**: `TrioStar ⟹ StarNodes`. Todo
nodo de la estrella entra: su pareja con `t` tiene testigos que `t` posee, luego en la estrella.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

/-- **Una vuelta de la regla de trío en la estrella de `t`.** -/
def trioRel (u : GPathB) (R : PathNodeId → PathNodeId → Prop) (t : PathNodeId) (x w : PathNodeId) : Prop :=
  R x w ∧ R x t ∧ R w t ∧
    ∀ l, 0 ≤ l → l < u.current_step → ∃ r, r.id.step = l ∧ R x r ∧ R w r ∧ R r t

/-- **La vuelta de trío es cerrada en la estrella de toda cima.** -/
def TrioStar (u : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R →
    ∀ t, V t → t.id.step = u.current_step - 1 → SecStruct u (fun x => V x ∧ R x t) (trioRel u R t)

/-- Un nodo de la estrella está relacionado consigo mismo en la vuelta de trío. -/
theorem trioRel_refl {u : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (hst : SecStruct u V R) {t z : PathNodeId} (hzt : R z t) : trioRel u R t z z := by
  refine ⟨hst.refl (hst.dom hzt).1, hzt, hzt, fun l h0 h1 => ?_⟩
  obtain ⟨r, hrl, hzr, htr⟩ := hst.pair hzt l h0 h1
  exact ⟨r, hrl, hzr, hzr, hst.symm htr⟩

/-- **`TrioStar ⟹ StarNodes`.** -/
theorem starNodes_of_trioStar {u : GPathB} (h : TrioStar u) : StarNodes u := by
  intro P V R hst ha t htV hts z hzV hzt
  refine ⟨fun x => V x ∧ R x t, trioRel u R t, h V R hst t htV hts, ?_, ⟨hzV, hzt⟩, ?_⟩
  · intro b hb y hy hys
    exact ha b hb hy.1 hys
  · rintro y ⟨hyV, hyt⟩
    exact ⟨hyV, Or.inr (hst.adj (hst.symm hyt))⟩

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- **Las hipótesis con la vuelta de trío**: `TrioStar` y `SideEdgesAt` en cada join. -/
structure HypsTrio (φ : Cnf) : Prop where
  trio : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvT e → SInvT g → TrioStar (join e g)
  side : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvT e → SInvT g → SideEdgesAt e g (T - 2)

/-- **El veredicto del lector es la satisfacibilidad bajo `TrioStar` y `SideEdgesAt` en los joins.** -/
theorem readerVerdict_iff_of_trioStar {φ : Cnf} (hbd : Bounded φ) (H : HypsTrio φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_starNodes hbd
    ⟨fun T key e g hT he hg hke hkg => starNodes_of_trioStar (H.trio T key e g hT he hg hke hkg), H.side⟩

end SecLine

end AbsSatBingo.Model
