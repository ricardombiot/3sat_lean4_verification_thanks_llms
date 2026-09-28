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

**Mitad estructural de `SidePinned`** (demostrada, con `OffSide`: ningún vivo de `g` es de `b`): fijada en `b`, toda
estructura cerrada de la unión vive en `e` (`alive_left_of_pinned`) y sus parejas con nodos del paso de `b` son
posesiones de `e` (`adj_left_of_pinned`). **Lo que falta**: las parejas entre nodos compartidos de pasos inferiores
pueden venir de una arista que solo tiene `g`; la medida dice que el review de la unión fijada las corta todas.
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

-- ============================================================
-- La mitad estructural de `SidePinned`
-- ============================================================

/-- Ningún vivo de `g` es del nodo del mapa `b` (la separación por el origen, medida: `sep_bad` 0). -/
def OffSide (g : GPathB) (b : NodeId) : Prop := ∀ q ∈ g.alive, q.id ≠ b

/-- Una posesión de la unión que toca un nodo muerto en `g` viene de `e`. -/
theorem adj_left_of_dead {e g : GPathB} (hea : EdgesAlive g) {y r : PathNodeId} (hr : r ∉ g.alive)
    (h : (join e g).Adj y r) : e.Adj y r := by
  rcases adj_join_cases h with he | hg
  · exact he
  · exact absurd (hea y r hg).2 hr

/-- **Fijada en un nodo del mapa de `e`, toda estructura cerrada de la unión vive en `e`**: cada nodo tiene un
testigo del paso de `b` (regla de parejas con él mismo), ese testigo es de `b`, muerto en `g`, y la posesión que los
une viene de `e`. -/
theorem alive_left_of_pinned {e g : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    {b : NodeId} (hst : SecStruct (join e g) V R) (ha : SecAgrees V b) (hb0 : 0 ≤ b.step)
    (hbc : b.step < e.current_step) (hoff : OffSide g b) (hee : EdgesAlive e) (heg : EdgesAlive g)
    {y : PathNodeId} (hy : V y) : y ∈ e.alive := by
  obtain ⟨r, hrs, hyr, _⟩ := hst.pair (hst.refl hy) b.step hb0 hbc
  have hrid : r.id = b := ha (hst.dom hyr).2 hrs
  have hrg : r ∉ g.alive := fun h => hoff r h hrid
  exact (hee y r (adj_left_of_dead heg hrg (hst.adj hyr))).1

/-- Y toda pareja de la estructura con un nodo del paso `b.step` es una posesión de `e`. -/
theorem adj_left_of_pinned {e g : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    {b : NodeId} (hst : SecStruct (join e g) V R) (ha : SecAgrees V b) (hoff : OffSide g b) (heg : EdgesAlive g)
    {y r : PathNodeId} (hyr : R y r) (hrs : r.id.step = b.step) : e.Adj y r :=
  adj_left_of_dead heg (fun h => hoff r h (ha (hst.dom hyr).2 hrs)) (hst.adj hyr)

end GPathB

end AbsSatBingo.Model
