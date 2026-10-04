-- lean/improves_bingo/AbsSatBingo/Model/StarCore.lean
import AbsSatBingo.Model.LineStep

/-!
# El núcleo por parejas de la estrella de una cima (StarCore)

La estrella de una cima `t` en el núcleo de la familia fijado en `Q`: los `y` con `FamKernel F c Q t y`. Su **núcleo
por parejas** `StarCore` es la mayor relación dentro de esa estrella (y del núcleo) cerrada por parejas: la unión de
todas las relaciones `StarPairIn`. Es el testigo explícito de `TopStarF`: lo que calcula la regla de la estrella
(`julia/improves_bingo/src/graph_path/graph_path_star.jl`, que no corta nada) sin cortar parejas `y–z` del estado.

**`topStarF_of_starCore`**: si el núcleo por parejas conserva a la cima y cumple los enlaces (padres, hijos, `node`),
es una estructura cerrada de la familia, concuerda con `Q` y vive en la estrella: `TopStarF`. Medido
(`test_3sat/probe_starcore.jl`): sin fallos. **`pinFreeF_of_topStarF`**: con la contabilidad de la fila de la cima,
da `PinFreeF`, la única hipótesis de `readerVerdict_iff_of_pinFree`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

variable {F : GPathB → Prop} {c : Int} {Q : List NodeId} {t : PathNodeId}

/-- Una relación cerrada por parejas dentro del núcleo fijado en `Q` y de la estrella de `t` en él. -/
structure StarPairIn (F : GPathB → Prop) (c : Int) (Q : List NodeId) (t : PathNodeId)
    (R : PathNodeId → PathNodeId → Prop) : Prop where
  sub  : ∀ {y w}, R y w → FamKernel F c Q y w
  star : ∀ {y w}, R y w → FamKernel F c Q t y
  refl : ∀ {y w}, R y w → R y y
  symm : ∀ {y w}, R y w → R w y
  pair : ∀ {y w}, R y w → ∀ l, 0 ≤ l → l < c → ∃ r, r.id.step = l ∧ R y r ∧ R w r

/-- **El núcleo por parejas de la estrella de `t`**: la unión de las relaciones `StarPairIn`. -/
def StarCore (F : GPathB → Prop) (c : Int) (Q : List NodeId) (t : PathNodeId) (y w : PathNodeId) : Prop :=
  ∃ R, StarPairIn F c Q t R ∧ R y w

theorem starCore_starPairIn : StarPairIn F c Q t (StarCore F c Q t) where
  sub  := fun ⟨_, h, hr⟩ => h.sub hr
  star := fun ⟨_, h, hr⟩ => h.star hr
  refl := fun ⟨R, h, hr⟩ => ⟨R, h, h.refl hr⟩
  symm := fun ⟨R, h, hr⟩ => ⟨R, h, h.symm hr⟩
  pair := fun ⟨R, h, hr⟩ l h0 hl => by
    obtain ⟨r, hrl, h1, h2⟩ := h.pair hr l h0 hl
    exact ⟨r, hrl, ⟨R, h, h1⟩, ⟨R, h, h2⟩⟩

/-- Los enlaces de una relación en la familia: los campos `node`, `par` y `son` de `FamStruct` (con `V y := R y y`). -/
structure CoreLinks (F : GPathB → Prop) (c : Int) (R : PathNodeId → PathNodeId → Prop) : Prop where
  node : ∀ {y}, R y y → (y.parent_id.isNone = false → ∃ p, FPar F y p ∧ R y p) ∧
            (y.id.step ≠ c - 1 → ∃ s, FSon F y s ∧ R y s)
  par  : ∀ {x w}, R x w → x ≠ w → 1 ≤ x.id.step → ∃ p, FPar F x p ∧ R x p ∧ R p w
  son  : ∀ {x w}, R x w → x ≠ w → x.id.step + 1 < c → ∃ s, FSon F x s ∧ R x s ∧ R s w

/-- **`StarCoreH`** (medida, `test_3sat/probe_starcore.jl`): para una cima del núcleo fijado en `Q`, el núcleo por
parejas de su estrella la conserva y cumple los enlaces. -/
def StarCoreH (F : GPathB → Prop) (c : Int) : Prop :=
  ∀ (Q : List NodeId) (t : PathNodeId), t.id.step = c - 1 → FamKernel F c Q t t →
    StarCore F c Q t t t ∧ CoreLinks F c (StarCore F c Q t)

/-- **`TopStarF`**: `TopStarK` en familia. Una cima del núcleo fijado en `Q` está en una estructura cerrada de la
familia que concuerda con `Q` y vive en su estrella. -/
def TopStarF (F : GPathB → Prop) (c : Int) : Prop :=
  ∀ (Q : List NodeId) (t : PathNodeId), t.id.step = c - 1 → FamKernel F c Q t t →
    ∃ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), FamStruct F c V R ∧ (∀ b ∈ Q, SecAgrees V b) ∧
      V t ∧ ∀ y, V y → ∃ g, F g ∧ g.Adj t y

/-- El núcleo por parejas con sus enlaces es una estructura cerrada de la familia. -/
theorem famStruct_starCore (hl : CoreLinks F c (StarCore F c Q t)) :
    FamStruct F c (fun y => StarCore F c Q t y y) (StarCore F c Q t) := by
  have hp := (starCore_starPairIn : StarPairIn F c Q t (StarCore F c Q t))
  refine ⟨fun hy => ?_, fun hy => hy, fun h => hp.symm h, fun h => ⟨hp.refl h, hp.refl (hp.symm h)⟩,
    fun h => ?_, fun h => hp.pair h, fun hy => ?_, fun hy => hl.node hy, fun h hne hs => hl.par h hne hs,
    fun h hne hs => hl.son h hne hs⟩
  · obtain ⟨V, R, hst, _, hr⟩ := hp.sub hy; exact hst.alive (hst.dom hr).1
  · obtain ⟨V, R, hst, _, hr⟩ := hp.sub h; exact hst.adj hr
  · obtain ⟨V, R, hst, _, hr⟩ := hp.sub hy; exact hst.doc (hst.dom hr).1

/-- **`StarCoreH` ⇒ `TopStarF`**, con el núcleo por parejas de la estrella como testigo explícito. -/
theorem topStarF_of_starCore (h : StarCoreH F c) : TopStarF F c := by
  intro Q t hts hk
  obtain ⟨htt, hl⟩ := h Q t hts hk
  have hp := (starCore_starPairIn : StarPairIn F c Q t (StarCore F c Q t))
  refine ⟨_, _, famStruct_starCore hl, fun b hb y hy hys => ?_, htt, fun y hy => ?_⟩
  · obtain ⟨V, R, hst, ha, hr⟩ := hp.sub hy
    exact ha b hb (hst.dom hr).1 hys
  · obtain ⟨V, R, hst, _, hr⟩ := hp.star hy
    exact hst.adj hr

/-- **`TopStarF` ⇒ `PinFreeF`**, con la contabilidad de la fila: lo que la cima posee en la línea concuerda con los
requisitos de su fila (la cima solo vive en su estado, filtrado por `rq` al subir). -/
theorem pinFreeF_of_topStarF {rq : NodeId → List NodeId} {L : NodeId × GPathB → Prop}
    (hs : TopStarF (famOf L) c)
    (hag : ∀ (t y : PathNodeId), t.id.step = c - 1 → (∃ g, famOf L g ∧ g.Adj t y) →
      ∀ b ∈ rq t.id, y.id.step = b.step → y.id = b) : PinFreeF rq L c := by
  intro Q t hts hk
  obtain ⟨V, R, hst, ha, hvt, hstar⟩ := hs Q t hts hk
  refine ⟨V, R, hst, fun b hb => ?_, hst.refl hvt⟩
  rcases List.mem_append.mp hb with hb | hb
  · intro y hy hys
    exact hag t y hts (hstar y hy) b hb hys
  · exact ha b hb

end GPathB

end AbsSatBingo.Model
