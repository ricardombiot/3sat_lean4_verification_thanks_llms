-- lean/improves_bingo/AbsSatBingo/Model/SecSplitParts.lean
import AbsSatBingo.Model.SecExactLine

/-!
# `SecSplit` por partes

`KernelUnion` se descompone en el paso de origen `k = T - 2` (`kernelUnion_of_sideEdges`) en `SplitAt` (el núcleo de
la unión se parte por los nodos del mapa de `k`), `SepAt` (ningún nodo del mapa de `k` está vivo en los dos lados) y
`SideEdgesAt` (fijada en un origen, las parejas de la unión son del lado que lo tiene). De las tres, **solo `SplitAt`
habla de cada pareja**; `SidePinned` ya es por estructuras.

Para `SecSplit` basta la versión de existencia de `SplitAt`:

> **`SplitSat u k`**: si una estructura cerrada no vacía de `u` concuerda con `P`, hay un nodo del mapa `b` del paso
> `k` y una estructura cerrada no vacía de `u` que concuerda con `P` y con `b`.

* `SplitAt ⟹ SplitSat` (`splitSat_of_splitAt`);
* **`SplitSat` + `SidePinned` ⟹ `SecSplit`** (`secSplit_of_splitSat`);
* el veredicto del lector bajo `SplitSat`, `SepAt`, `SideEdgesAt` y `AvoidSat` (`readerVerdict_iff_of_secParts`).

`SplitSat` es la pregunta del lector hecha en la unión: si algo sobrevive a `P`, algún pin del paso de origen deja
algo vivo.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

/-- **La versión de existencia de `SplitAt`.** -/
def SplitSat (u : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct u V R → (∀ b ∈ P, SecAgrees V b) → (∃ y, V y) →
    ∃ b : NodeId, b.step = k ∧ ∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
      SecStruct u V' R' ∧ (∀ c ∈ P ++ [b], SecAgrees V' c) ∧ ∃ y, V' y

theorem splitSat_of_splitAt {u : GPathB} {k : Int} (hs : SplitAt u k) : SplitSat u k := by
  intro P V R hst ha ⟨y, hy⟩
  obtain ⟨b, hbk, V', R', h1, h2, h3⟩ := hs P y y ⟨V, R, hst, ha, hst.refl hy⟩
  exact ⟨b, hbk, V', R', h1, h2, y, (h1.dom h3).1⟩

/-- **`SplitSat` + `SidePinned` ⟹ `SecSplit`.** -/
theorem secSplit_of_splitSat {e g : GPathB} {k : Int} (hs : SplitSat (join e g) k)
    (hp : SidePinned (join e g) e g k) : SecSplit e g := by
  intro P V R hst ha hne
  by_cases hok : okJoin e g = true
  · have hj : doJoin e g = join e g := by unfold doJoin; rw [if_pos hok]
    rw [hj] at hst
    obtain ⟨b, hbk, V', R', h1, h2, y, hy⟩ := hs P V R hst ha hne
    have hk : Kernel (join e g) (P ++ [b]) y y := ⟨V', R', h1, h2, h1.refl hy⟩
    have sub : ∀ {W : PathNodeId → Prop}, (∀ c ∈ P ++ [b], SecAgrees W c) → ∀ c ∈ P, SecAgrees W c :=
      fun h c hc => h c (List.mem_append_left _ hc)
    rcases hp b hbk with he | hg
    · obtain ⟨V'', R'', h1', h2', h3'⟩ := he P y y hk
      exact Or.inl ⟨V'', R'', h1', sub h2', y, (h1'.dom h3').1⟩
    · obtain ⟨V'', R'', h1', h2', h3'⟩ := hg P y y hk
      exact Or.inr ⟨V'', R'', h1', sub h2', y, (h1'.dom h3').1⟩
  · have hj : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [hj] at hst
    exact Or.inl ⟨V, R, hst, ha, hne⟩

/-- **La versión de existencia de `SidePinned`**: fijada la unión en un nodo del mapa `b` de `k`, una estructura
cerrada no vacía que concuerda con `P ++ [b]` da **alguna** en un lado (no necesariamente la misma). -/
def SideSat (u e g : GPathB) (k : Int) : Prop :=
  ∀ b : NodeId, b.step = k → ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct u V R → (∀ c ∈ P ++ [b], SecAgrees V c) → (∃ y, V y) →
    (∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct e V' R' ∧ (∀ c ∈ P ++ [b], SecAgrees V' c) ∧ ∃ y, V' y) ∨
    (∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct g V' R' ∧ (∀ c ∈ P ++ [b], SecAgrees V' c) ∧ ∃ y, V' y)

theorem sideSat_of_sidePinned {u e g : GPathB} {k : Int} (hp : SidePinned u e g k) : SideSat u e g k := by
  intro b hb P V R hst ha ⟨y, hy⟩
  have hk : Kernel u (P ++ [b]) y y := ⟨V, R, hst, ha, hst.refl hy⟩
  rcases hp b hb with he | hg
  · obtain ⟨V', R', h1, h2, h3⟩ := he P y y hk
    exact Or.inl ⟨V', R', h1, h2, y, (h1.dom h3).1⟩
  · obtain ⟨V', R', h1, h2, h3⟩ := hg P y y hk
    exact Or.inr ⟨V', R', h1, h2, y, (h1.dom h3).1⟩

/-- **`SplitSat` + `SideSat` ⟹ `SecSplit`.** -/
theorem secSplit_of_splitSat_sideSat {e g : GPathB} {k : Int} (hs : SplitSat (join e g) k)
    (hp : SideSat (join e g) e g k) : SecSplit e g := by
  intro P V R hst ha hne
  by_cases hok : okJoin e g = true
  · have hj : doJoin e g = join e g := by unfold doJoin; rw [if_pos hok]
    rw [hj] at hst
    obtain ⟨b, hbk, V', R', h1, h2, h3⟩ := hs P V R hst ha hne
    have sub : ∀ {W : PathNodeId → Prop}, (∀ c ∈ P ++ [b], SecAgrees W c) → ∀ c ∈ P, SecAgrees W c :=
      fun h c hc => h c (List.mem_append_left _ hc)
    rcases hp b hbk P V' R' h1 h2 h3 with ⟨V'', R'', h1', h2', h3'⟩ | ⟨V'', R'', h1', h2', h3'⟩
    · exact Or.inl ⟨V'', R'', h1', sub h2', h3'⟩
    · exact Or.inr ⟨V'', R'', h1', sub h2', h3'⟩
  · have hj : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [hj] at hst
    exact Or.inl ⟨V, R, hst, ha, hne⟩

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- **Las hipótesis por partes, en su versión de existencia**: solo `split` cambia (`SplitSat` en lugar de
`SplitAt`). -/
structure HypsSecParts (φ : Cnf) : Prop where
  split : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SplitSat (join e g) (T - 2)
  sep   : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SepAt e g (T - 2)
  side  : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SideEdgesAt e g (T - 2)
  skip  : SkipHyp φ

theorem hypsSec_of_parts {φ : Cnf} (H : HypsSecParts φ) : HypsSec φ := by
  refine ⟨fun T key e g hT he hg hke hkg => ?_, H.skip⟩
  have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
  exact secSplit_of_splitSat (H.split T key e g hT he hg hke hkg)
    (sidePinned_of_sideEdges (by omega) (by rw [he.step]; omega) hcs hke.2.2.2.2.2.2 hkg.2.2.2.2.2.2
      hke.2.2.1 hkg.2.2.1 (H.sep T key e g hT he hg hke hkg) (H.side T key e g hT he hg hke hkg))

/-- **El veredicto del lector es la satisfacibilidad bajo `SplitSat`, `SepAt`, `SideEdgesAt` y `AvoidSat`.** -/
theorem readerVerdict_iff_of_secParts {φ : Cnf} (hbd : Bounded φ) (H : HypsSecParts φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_secSplit hbd (hypsSec_of_parts H)

end SecLine

end AbsSatBingo.Model
