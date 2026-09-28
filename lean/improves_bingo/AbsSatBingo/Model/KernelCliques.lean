-- lean/improves_bingo/AbsSatBingo/Model/KernelCliques.lean
import AbsSatBingo.Model.KernelSkip

/-!
# `KernelExact` es «el núcleo son las camarillas»

* **`secStruct_of_carried`**: toda camarilla llevada es una estructura cerrada por las reglas.
* **`kernel_of_clique`**: por eso, dos nodos de una camarilla que pasa por `P` están siempre en el núcleo fijado en
  `P`.
* **`kernelExact_iff`**: `KernelExact` es la inclusión contraria. El núcleo fijado en `P` son exactamente las parejas
  que comparten una camarilla que pasa por `P`.
* **`kernel_split`**: con `KernelExact`, el núcleo fijado en `P` es la unión de los núcleos fijados además en cada
  nodo del mapa de cualquier paso (la frase de la escalera: el núcleo es la unión de sus fijaciones).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

variable {S : Int → PathNodeId}

/-- **Toda camarilla llevada es una estructura cerrada.** -/
theorem secStruct_of_carried {g : GPathB} (hc : Carried g S) :
    SecStruct g (OnS g.current_step S) (fun y w => OnS g.current_step S y ∧ OnS g.current_step S w) := by
  refine ⟨fun ⟨k, h0, h1, he⟩ => he ▸ hc.alive k h0 h1, fun hy => ⟨hy, hy⟩, fun ⟨hy, hw⟩ => ⟨hw, hy⟩,
    fun h => h, fun ⟨hy, hw⟩ => hc.adj_on hy hw, ?_, ?_, ?_, ?_⟩
  · rintro y w ⟨hy, hw⟩ l hl0 hl1
    exact ⟨S l, hc.step l hl0 hl1, ⟨hy, ⟨l, hl0, hl1, rfl⟩⟩, ⟨hw, ⟨l, hl0, hl1, rfl⟩⟩⟩
  · rintro y ⟨k, h0, h1, rfl⟩
    obtain ⟨n, hn, hp, hs⟩ := hc.node k h0 h1
    refine ⟨n, hn, fun hr => ?_, fun hl => ?_⟩
    · have hk : 0 < k := by
        rcases Int.lt_or_eq_of_le h0 with h | h
        · exact h
        · subst h; rw [hc.root (by omega)] at hr; cases hr
      exact ⟨S (k - 1), hp hk, ⟨k, h0, h1, rfl⟩, ⟨k - 1, by omega, by omega, rfl⟩⟩
    · have hk : k + 1 < g.current_step := by
        have := hc.step k h0 h1; omega
      exact ⟨S (k + 1), hs hk, ⟨k, h0, h1, rfl⟩, ⟨k + 1, by omega, hk, rfl⟩⟩
  · rintro x w n ⟨⟨k, h0, h1, rfl⟩, hw⟩ _ hn hx1
    obtain ⟨n', hn', hp, _⟩ := hc.node k h0 h1
    rw [hn] at hn'; cases hn'
    have hk : 0 < k := by have := hc.step k h0 h1; omega
    exact ⟨S (k - 1), hp hk, ⟨⟨k, h0, h1, rfl⟩, ⟨k - 1, by omega, by omega, rfl⟩⟩,
      ⟨⟨k - 1, by omega, by omega, rfl⟩, hw⟩⟩
  · rintro x w n ⟨⟨k, h0, h1, rfl⟩, hw⟩ _ hn hx1
    obtain ⟨n', hn', _, hs⟩ := hc.node k h0 h1
    rw [hn] at hn'; cases hn'
    have hk : k + 1 < g.current_step := by have := hc.step k h0 h1; omega
    exact ⟨S (k + 1), hs hk, ⟨⟨k, h0, h1, rfl⟩, ⟨k + 1, by omega, hk, rfl⟩⟩,
      ⟨⟨k + 1, by omega, hk, rfl⟩, hw⟩⟩

/-- La selección concuerda con cada requisito de `P`: sus nodos en el paso del requisito son de él. -/
theorem secAgrees_of_agrees {g : GPathB} (hc : Carried g S) {r : NodeId} (ha : Agrees g.current_step S r) :
    SecAgrees (OnS g.current_step S) r := by
  rintro y ⟨k, h0, h1, rfl⟩ hys
  have hk : k = r.step := by rw [← hc.step k h0 h1]; exact hys
  subst hk
  exact ha h0 h1

/-- **Dos nodos de una camarilla por `P` están en el núcleo fijado en `P`.** -/
theorem kernel_of_clique {g : GPathB} {P : List NodeId} (hc : Carried g S)
    (ha : ∀ r ∈ P, Agrees g.current_step S r) {y w : PathNodeId} (hy : OnS g.current_step S y)
    (hw : OnS g.current_step S w) : Kernel g P y w :=
  ⟨_, _, secStruct_of_carried hc, fun r hr => secAgrees_of_agrees hc (ha r hr), hy, hw⟩

/-- Dos nodos comparten una camarilla que pasa por `P`. -/
def CliquePair (g : GPathB) (P : List NodeId) (y w : PathNodeId) : Prop :=
  ∃ S, Carried g S ∧ (∀ r ∈ P, Agrees g.current_step S r) ∧ OnS g.current_step S y ∧ OnS g.current_step S w

/-- **`KernelExact` es «el núcleo son las camarillas»**: el núcleo fijado en `P` son exactamente las parejas que
comparten una camarilla que pasa por `P`. -/
theorem kernelExact_iff {g : GPathB} : KernelExact g ↔ ∀ P y w, Kernel g P y w ↔ CliquePair g P y w := by
  constructor
  · intro hk P y w
    exact ⟨hk P y w, fun ⟨S, hc, ha, hy, hw⟩ => kernel_of_clique hc ha hy hw⟩
  · intro h P y w hk
    exact (h P y w).mp hk

/-- **Con `KernelExact`, el núcleo es la unión de sus fijaciones en cualquier paso.** -/
theorem kernel_split {g : GPathB} (hk : KernelExact g) {P : List NodeId} {y w : PathNodeId}
    (hker : Kernel g P y w) {k : Int} (hk0 : 0 ≤ k) (hk1 : k < g.current_step) :
    ∃ b : NodeId, b.step = k ∧ Kernel g (P ++ [b]) y w := by
  obtain ⟨S, hc, ha, hy, hw⟩ := hk P y w hker
  refine ⟨(S k).id, hc.step k hk0 hk1, kernel_of_clique hc ?_ hy hw⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact ha r hr
  · rw [List.mem_singleton] at hr
    subst hr
    intro h0 h1
    rw [hc.step k hk0 hk1]

end GPathB

end AbsSatBingo.Model
