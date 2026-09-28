-- lean/improves_bingo/AbsSatBingo/Model/SideAbsorb.lean
import AbsSatBingo.Model.SideCone

/-!
# `SidePinned` por `Absorb`: un argumento global

**`Absorb u e`**: la unión sin los nodos que solo vive en el otro lado (`restrictTo u e`), revisada, no posee nada que
`e` no posea. Es una sola igualdad de reviews por join y por lado, sin pins ni orígenes; medida en Julia
(`test_3sat/probe_absorb.jl`).

**`sideEdges_of_absorb`**: `Absorb` da `SideEdges` para todo origen `b` de `e`. Una estructura cerrada de la unión
que concuerda con `b` vive en `e` (`alive_side`); matar los nodos de fuera la conserva (`sec_killVertex`), el review
también (`secStruct_review`), y sus parejas son entonces posesiones del estado revisado, que `Absorb` lleva a `e`.
No hace falta la cascada pareja por pareja: el review hace el trabajo de una vez.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- La unión sin los vivos que `e` no tiene, marcada para revisar. -/
def restrictTo (u e : GPathB) : GPathB :=
  { (u.alive.filter (fun q => !e.alive.contains q)).foldl killVertex u with dirty := true }

/-- **`Absorb`**: revisar la unión restringida a los vivos de `e` no deja posesiones que `e` no tenga. -/
def Absorb (u e : GPathB) : Prop := ∀ y w, (restrictTo u e).review.Adj y w → e.Adj y w

/-- Una estructura cerrada que vive en `e` lo es de la unión restringida. -/
theorem secStruct_restrictTo {u e : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (hst : SecStruct u V R) (hal : ∀ {y}, V y → y ∈ e.alive) : SecStruct (restrictTo u e) V R := by
  unfold restrictTo
  apply sec_dirty
  refine inv_foldl (fun g' => SecStruct g' V R) killVertex _ ?_ u hst
  intro g' q hq hc
  refine sec_killVertex hc (fun hv => ?_)
  have h2 := (List.mem_filter.mp hq).2
  have h3 : e.alive.contains q = true := List.contains_iff_mem.mpr (hal hv)
  rw [h3] at h2
  exact absurd h2 (by decide)

/-- **`Absorb` da `SideEdges`.** -/
theorem sideEdges_of_absorb {u e g : GPathB} (hu : IsUnion u e g) {b : NodeId} (hb0 : 0 ≤ b.step)
    (hbc : b.step < e.current_step) (hoff : OffSide g b) (hee : EdgesAlive e) (heg : EdgesAlive g)
    (hab : Absorb u e) : SideEdges u e b := by
  intro V R hst ha y w hr
  have hal : ∀ {y}, V y → y ∈ e.alive := fun hy => alive_side hu hst ha hb0 hbc hoff hee heg hy
  exact hab y w ((secStruct_review (secStruct_restrictTo hst hal)).adj hr)

/-- **`SideEdgesAt` por `Absorb` en los dos lados.** -/
theorem sideEdgesAt_of_absorb {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hle : LinksInv e) (hlg : LinksInv g) (hee : EdgesAlive e)
    (heg : EdgesAlive g) (hae : Absorb (join e g) e) (hag : Absorb (join e g) g) : SideEdgesAt e g k := by
  intro b hb
  refine ⟨fun hoff => ?_, fun hoff => ?_⟩
  · exact sideEdges_of_absorb (isUnion_join_left hle hlg hee heg) (hb ▸ hk0) (hb ▸ hkc) hoff hee heg hae
  · exact sideEdges_of_absorb (isUnion_join_right hcs hle hlg hee heg) (hb ▸ hk0) (hcs ▸ hb ▸ hkc) hoff heg hee hag

end GPathB

end AbsSatBingo.Model
