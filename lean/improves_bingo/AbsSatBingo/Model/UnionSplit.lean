-- lean/improves_bingo/AbsSatBingo/Model/UnionSplit.lean
import AbsSatBingo.Model.KernelCliques

/-!
# Descomponer `KernelUnion`

`KernelUnion e g` (el núcleo de la unión es la unión de los núcleos) se sigue de dos propiedades de la unión en el
paso de origen `k` (el anterior a la cima, donde cada lado trae nodos de su propio nodo del mapa):

* **`SplitAt`**: el núcleo de la unión fijado en `P` se parte por el nodo del mapa de `k` (como `kernel_split`, pero
  en la unión, de la que aún no se sabe `KernelExact`);
* **`SidePinned`**: fijar la unión en un nodo del mapa de `k` da el núcleo de un lado fijado igual.

**`kernelUnion_of_split`** (demostrado). Medido en Julia (`test_3sat/probe_union_parts.jl`): la separación por el
origen y `SidePinned` valen; la versión fuerte, que los dos lados coincidan en la posesión entre nodos compartidos
(`SharedAgree`), es **falsa**, así que `SidePinned` no sale de una coincidencia de tablas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- El núcleo de `u` se parte por los nodos del mapa del paso `k`. -/
def SplitAt (u : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) y w, Kernel u P y w → ∃ b : NodeId, b.step = k ∧ Kernel u (P ++ [b]) y w

/-- Fijar `u` en un nodo del mapa del paso `k` da el núcleo de `e` o el de `g`, fijados igual. -/
def SidePinned (u e g : GPathB) (k : Int) : Prop :=
  ∀ b : NodeId, b.step = k →
    (∀ (P : List NodeId) y w, Kernel u (P ++ [b]) y w → Kernel e (P ++ [b]) y w) ∨
    (∀ (P : List NodeId) y w, Kernel u (P ++ [b]) y w → Kernel g (P ++ [b]) y w)

/-- Quitar un requisito del final agranda el núcleo. -/
theorem kernel_of_append {g : GPathB} {P Q : List NodeId} {y w : PathNodeId} (h : Kernel g (P ++ Q) y w) :
    Kernel g P y w := by
  obtain ⟨V, R, hst, ha, hr⟩ := h
  exact ⟨V, R, hst, fun b hb => ha b (List.mem_append_left _ hb), hr⟩

/-- **`KernelUnion` se sigue de `SplitAt` y `SidePinned`** en el paso de origen. -/
theorem kernelUnion_of_split {e g : GPathB} {k : Int} (hs : SplitAt (join e g) k)
    (hp : SidePinned (join e g) e g k) : KernelUnion e g := by
  intro P y w hk
  obtain ⟨b, hbk, hkb⟩ := hs P y w hk
  rcases hp b hbk with he | hg
  · exact Or.inl (kernel_of_append (he P y w hkb))
  · exact Or.inr (kernel_of_append (hg P y w hkb))

end GPathB

end AbsSatBingo.Model
