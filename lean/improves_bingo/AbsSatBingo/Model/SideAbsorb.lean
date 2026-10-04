-- lean/improves_bingo/AbsSatBingo/Model/SideAbsorb.lean
import AbsSatBingo.Model.SideCone
import AbsSatBingo.Model.UnionEquiv

/-!
# `SidePinned` por `Absorb`: un argumento global

**`Absorb u e`**: la unión sin los nodos que solo vive en el otro lado (`restrictTo u e`), revisada, no posee nada que
`e` no posea. Es una sola igualdad de reviews por join y por lado, sin pins ni orígenes; medida en Julia
(`test_3sat/probe_absorb.jl`).

**`sideEdges_of_absorb`**: `Absorb` da `SideEdges` para todo origen `b` de `e`. Una estructura cerrada de la unión
que concuerda con `b` vive en `e` (`alive_side`); matar los nodos de fuera la conserva (`sec_killVertex`), el review
también (`secStruct_review`), y sus parejas son entonces posesiones del estado revisado, que `Absorb` lleva a `e`.
No hace falta la cascada pareja por pareja: el review hace el trabajo de una vez.

**`KAbsorb`** (la misma idea sin el review: toda estructura cerrada de la unión restringida tiene sus parejas en `e`)
también da `SideEdges` (`sideEdges_of_kAbsorb`). **`kAbsorb_of_kernelUnion`**: entre estados de nodos del mapa
distintos (cimas con ids distintos), `KAbsorb` se sigue de `KernelUnion` en el mismo paso, fijando en la cima. Es la
forma demostrable de «NoMix ⇒ GenAbsorb»: el intento de bajar un paso (NoMix en `T` ⇒ GenAbsorb en `T+1`) necesita
partir antes la estructura por la cima y por el origen del paso nuevo, que es `SplitAt` en el paso nuevo.
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

-- ============================================================
-- `Absorb` entre estados de nodos del mapa distintos, por `KernelUnion` del mismo paso
-- ============================================================

/-- `Absorb` a nivel de estructuras: toda estructura cerrada de la unión restringida tiene sus parejas en `e`. -/
def KAbsorb (u e : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct (restrictTo u e) V R →
    ∀ {y w}, R y w → e.Adj y w

theorem alive_restrictTo {u e : GPathB} {q : PathNodeId} (h : q ∈ (restrictTo u e).alive) : q ∈ e.alive := by
  unfold restrictTo at h
  have key : ∀ (l : List PathNodeId) (g : GPathB), (∀ q ∈ l, q ∉ e.alive → True) →
      q ∈ (l.foldl killVertex g).alive → q ∈ g.alive ∧ (q ∈ l → False) := by
    intro l
    induction l with
    | nil => intro g _ h; exact ⟨h, fun h => absurd h List.not_mem_nil⟩
    | cons a as ih =>
      intro g _ h
      obtain ⟨h1, h2⟩ := ih (g.killVertex a) (fun _ _ _ => trivial) h
      have ⟨h3, h4⟩ := List.mem_filter.mp h1
      refine ⟨h3, fun hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · simp at h4
      · exact h2 hm
  obtain ⟨hu, hn⟩ := key _ u (fun _ _ _ => trivial) h
  cases hc : e.alive.contains q with
  | true => exact List.contains_iff_mem.mp hc
  | false => exact (hn (List.mem_filter.mpr ⟨hu, by rw [hc]; rfl⟩)).elim

/-- Una estructura cerrada del estado restringido lo es del estado entero (matar vértices solo quita). -/
theorem secStruct_of_restrictTo {u e : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (hst : SecStruct (restrictTo u e) V R) : SecStruct u V R := by
  have hk : ∀ (l : List PathNodeId) (g : GPathB), Sub (l.foldl killVertex g) g ∧
      (l.foldl killVertex g).nodes = g.nodes := by
    intro l
    induction l with
    | nil => intro g; exact ⟨Sub.refl g, rfl⟩
    | cons a as ih =>
      intro g
      obtain ⟨h1, h2⟩ := ih (g.killVertex a)
      exact ⟨h1.trans (sub_killVertex g a), h2⟩
  obtain ⟨hs, hn⟩ := hk (u.alive.filter (fun q => !e.alive.contains q)) u
  have hnode : (restrictTo u e).node? = u.node? := by
    funext x; unfold node? restrictTo; dsimp only; rw [hn]
  refine ⟨fun hy => hs.alive _ (hst.alive hy), hst.refl, hst.symm, hst.dom, fun h => hs.adj _ _ (hst.adj h),
    fun h l h0 h1 => hst.pair h l h0 (by rw [show (restrictTo u e).current_step = u.current_step from hs.step]; exact h1),
    ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn', hp, hs'⟩ := hst.node hy
    rw [hnode] at hn'
    exact ⟨n, hn', hp, fun h => hs' (by rw [show (restrictTo u e).current_step = u.current_step from hs.step]; exact h)⟩
  · intro x w n hxw hne hn' h1
    rw [← hnode] at hn'
    exact hst.par hxw hne hn' h1
  · intro x w n hxw hne hn' h1
    rw [← hnode] at hn'
    exact hst.son hxw hne hn' (by rw [show (restrictTo u e).current_step = u.current_step from hs.step]; exact h1)

/-- **`KAbsorb` entre estados de nodos del mapa distintos se sigue de `KernelUnion` del mismo paso**: las cimas de
`S` son del nodo del mapa `d`, que `O` no tiene; una estructura de la unión restringida a `S` concuerda con `d`, y
fijada en `d` el núcleo de `O` está vacío. -/
theorem kAbsorb_of_kernelUnion {S O : GPathB} {d : NodeId} (hu : KernelUnion S O) (hd0 : 0 ≤ d.step)
    (hdc : d.step < S.current_step) (htop : ∀ q ∈ S.alive, q.id.step = d.step → q.id = d)
    (hoff : OffSide O d) (hcs : S.current_step = O.current_step) : KAbsorb (join S O) S := by
  intro V R hst y w hr
  have hag : SecAgrees V d := fun hq hs => htop _ (alive_restrictTo (hst.alive hq)) hs
  have hk : Kernel (join S O) [d] y w :=
    ⟨V, R, secStruct_of_restrictTo hst, fun b hb => by rw [List.mem_singleton] at hb; subst hb; exact hag, hr⟩
  rcases hu [d] y w hk with h | h
  · obtain ⟨V', R', hst', _, hr'⟩ := h
    exact hst'.adj hr'
  · exact (kernel_empty_of_off (P := []) hoff hd0 (hcs ▸ hdc) h).elim

/-- `KAbsorb` da `SideEdges` (como `Absorb`, sin pasar por el review). -/
theorem sideEdges_of_kAbsorb {u e g : GPathB} (hu : IsUnion u e g) {b : NodeId} (hb0 : 0 ≤ b.step)
    (hbc : b.step < e.current_step) (hoff : OffSide g b) (hee : EdgesAlive e) (heg : EdgesAlive g)
    (hab : KAbsorb u e) : SideEdges u e b := by
  intro V R hst ha y w hr
  have hal : ∀ {y}, V y → y ∈ e.alive := fun hy => alive_side hu hst ha hb0 hbc hoff hee heg hy
  exact hab V R (secStruct_restrictTo hst hal) hr

end GPathB

end AbsSatBingo.Model
