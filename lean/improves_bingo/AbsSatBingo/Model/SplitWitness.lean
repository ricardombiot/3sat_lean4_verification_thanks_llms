-- lean/improves_bingo/AbsSatBingo/Model/SplitWitness.lean
import AbsSatBingo.Model.UnionEquiv

/-!
# `SplitAt` por testigos, y la unión de estructuras cerradas

* **`secStruct_iUnion`**: la unión de una familia de estructuras cerradas es cerrada. Así, las parejas que sobreviven
  a algún pin del origen forman una estructura cerrada (`SplitKernel`), y `SplitAt` dice que es todo el núcleo.
* **`WitSplit`**: `SplitAt` eligiendo el origen entre los testigos de la pareja (un nodo del paso de origen que el
  núcleo empareja con los dos). Medido (`test_3sat/probe_splitat.jl`): `SplitAt` sin fallos; **algún** testigo
  común siempre sirve, pero **no cualquiera** (unas pocas parejas por mil fallan con algún testigo).
* `splitAt_of_witSplit`, y `witSplit_of_kernelUnion`: con los lados exactos, `KernelUnion` da `WitSplit` (el testigo
  es el nodo del origen de la camarilla del lado). `WitSplit` es la forma de `SplitAt` que habría que demostrar.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- **La unión de estructuras cerradas es cerrada.** -/
theorem secStruct_iUnion {g : GPathB} {ι : Type} {V : ι → PathNodeId → Prop}
    {R : ι → PathNodeId → PathNodeId → Prop} (h : ∀ i, SecStruct g (V i) (R i)) :
    SecStruct g (fun y => ∃ i, V i y) (fun y w => ∃ i, R i y w) := by
  refine ⟨fun ⟨i, hy⟩ => (h i).alive hy, fun ⟨i, hy⟩ => ⟨i, (h i).refl hy⟩, fun ⟨i, hr⟩ => ⟨i, (h i).symm hr⟩,
    fun ⟨i, hr⟩ => ⟨⟨i, ((h i).dom hr).1⟩, ⟨i, ((h i).dom hr).2⟩⟩, fun ⟨i, hr⟩ => (h i).adj hr, ?_, ?_, ?_, ?_⟩
  · intro y w ⟨i, hr⟩ l h0 h1
    obtain ⟨r, hrs, h1, h2⟩ := (h i).pair hr l h0 h1
    exact ⟨r, hrs, ⟨i, h1⟩, ⟨i, h2⟩⟩
  · intro y ⟨i, hy⟩
    obtain ⟨n, hn, hp, hs⟩ := (h i).node hy
    refine ⟨n, hn, fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨p, hp', hr⟩ := hp hk; exact ⟨p, hp', ⟨i, hr⟩⟩
    · obtain ⟨s, hs', hr⟩ := hs hk; exact ⟨s, hs', ⟨i, hr⟩⟩
  · intro x w n ⟨i, hr⟩ hne hn h1
    obtain ⟨p, hp, h1, h2⟩ := (h i).par hr hne hn h1
    exact ⟨p, hp, ⟨i, h1⟩, ⟨i, h2⟩⟩
  · intro x w n ⟨i, hr⟩ hne hn h1
    obtain ⟨s, hs, h1, h2⟩ := (h i).son hr hne hn h1
    exact ⟨s, hs, ⟨i, h1⟩, ⟨i, h2⟩⟩

/-- Las parejas que sobreviven a algún pin del paso `k` (tras `P`). -/
def SplitKernel (u : GPathB) (P : List NodeId) (k : Int) (y w : PathNodeId) : Prop :=
  ∃ b : NodeId, b.step = k ∧ Kernel u (P ++ [b]) y w

/-- **`SplitKernel` es una estructura cerrada** (la unión de las de cada pin), que concuerda con `P`. -/
theorem splitKernel_closed (u : GPathB) (P : List NodeId) (k : Int) :
    ∃ V, SecStruct u V (SplitKernel u P k) ∧ ∀ b ∈ P, SecAgrees V b := by
  -- la familia: una estructura por cada (b, estructura cerrada que concuerda con P ++ [b])
  let ι := { x : NodeId × (PathNodeId → Prop) × (PathNodeId → PathNodeId → Prop) //
    x.1.step = k ∧ SecStruct u x.2.1 x.2.2 ∧ ∀ b ∈ P ++ [x.1], SecAgrees x.2.1 b }
  have hU := secStruct_iUnion (g := u) (V := fun i : ι => i.1.2.1) (R := fun i : ι => i.1.2.2) (fun i => i.2.2.1)
  refine ⟨fun y => ∃ i : ι, i.1.2.1 y, ?_, ?_⟩
  · have heq : SplitKernel u P k = fun y w => ∃ i : ι, i.1.2.2 y w := by
      funext y w
      apply propext
      constructor
      · rintro ⟨b, hb, V, R, hst, ha, hr⟩
        exact ⟨⟨(b, V, R), hb, hst, ha⟩, hr⟩
      · rintro ⟨⟨⟨b, V, R⟩, hb, hst, ha⟩, hr⟩
        exact ⟨b, hb, V, R, hst, ha, hr⟩
    rw [heq]; exact hU
  · intro b hb y ⟨i, hy⟩ hs
    exact i.2.2.2 b (List.mem_append_left _ hb) hy hs

/-- **`SplitAt` por testigos**: la pareja se conserva fijando el origen de alguno de sus testigos en el núcleo. -/
def WitSplit (u : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) y w, Kernel u P y w →
    ∃ r : PathNodeId, r.id.step = k ∧ Kernel u P y r ∧ Kernel u P w r ∧ Kernel u (P ++ [r.id]) y w

theorem splitAt_of_witSplit {u : GPathB} {k : Int} (h : WitSplit u k) : SplitAt u k := by
  intro P y w hk
  obtain ⟨r, hr, _, _, h'⟩ := h P y w hk
  exact ⟨r.id, hr, h'⟩

/-- El núcleo de un lado exacto da testigo: el nodo de la camarilla en el paso `k`. -/
theorem wit_of_exact {g : GPathB} (hk : KernelExact g) {P : List NodeId} {y w : PathNodeId}
    (hker : Kernel g P y w) {k : Int} (hk0 : 0 ≤ k) (hk1 : k < g.current_step) :
    ∃ r : PathNodeId, r.id.step = k ∧ Kernel g P y r ∧ Kernel g P w r ∧ Kernel g (P ++ [r.id]) y w := by
  obtain ⟨S, hc, ha, hy, hw⟩ := hk P y w hker
  have hr : OnS g.current_step S (S k) := ⟨k, hk0, hk1, rfl⟩
  refine ⟨S k, hc.step k hk0 hk1, kernel_of_clique hc ha hy hr, kernel_of_clique hc ha hw hr, ?_⟩
  refine kernel_of_clique hc ?_ hy hw
  intro r' hr'
  rcases List.mem_append.mp hr' with hr' | hr'
  · exact ha r' hr'
  · rw [List.mem_singleton] at hr'
    subst hr'
    intro _ _
    rw [hc.step k hk0 hk1]

/-- **Con los lados exactos, `KernelUnion` da `WitSplit`.** -/
theorem witSplit_of_kernelUnion {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hke : KernelExact e) (hkg : KernelExact g) (hu : KernelUnion e g) :
    WitSplit (join e g) k := by
  intro P y w h
  rcases hu P y w h with h | h
  · obtain ⟨r, hr, h1, h2, h3⟩ := wit_of_exact hke h hk0 hkc
    exact ⟨r, hr, kernel_join_left h1, kernel_join_left h2, kernel_join_left h3⟩
  · obtain ⟨r, hr, h1, h2, h3⟩ := wit_of_exact hkg h hk0 (hcs ▸ hkc)
    exact ⟨r, hr, kernel_join_right hcs h1, kernel_join_right hcs h2, kernel_join_right hcs h3⟩

end GPathB

end AbsSatBingo.Model
