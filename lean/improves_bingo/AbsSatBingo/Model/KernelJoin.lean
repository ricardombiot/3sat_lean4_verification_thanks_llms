-- lean/improves_bingo/AbsSatBingo/Model/KernelJoin.lean
import AbsSatBingo.Model.KernelUp

/-!
# El join conserva `KernelExact` bajo `KernelUnion`, y la contabilidad `LinksStep` / `Below`

* **`kernelExact_doJoin`**: si el núcleo de la unión es la unión de los núcleos de los dos lados (`KernelUnion`,
  **hipótesis**; medida en `julia/improves_bingo/test_3sat/probe_kernelunion.jl`), el join conserva `KernelExact`:
  la camarilla de cada lado lo es de la unión.
* `LinksStep` (los enlaces van al paso de al lado) y `Below` (todo por debajo de la cima) a través del review, el
  filtro, la fila nueva y el join.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

open Machine (Below)

/-- **Hipótesis**: el núcleo de la unión, fijado en `P`, es la unión de los de cada lado. -/
def KernelUnion (g₁ g₂ : GPathB) : Prop :=
  ∀ (P : List NodeId) y w, Kernel (join g₁ g₂) P y w → Kernel g₁ P y w ∨ Kernel g₂ P y w

/-- **El join conserva `KernelExact`** bajo `KernelUnion`. -/
theorem kernelExact_doJoin {g₁ g₂ : GPathB} (h₁ : KernelExact g₁) (h₂ : KernelExact g₂)
    (hu : KernelUnion g₁ g₂) : KernelExact (doJoin g₁ g₂) := by
  unfold doJoin
  split
  · rename_i hok
    have hcs : g₁.current_step = g₂.current_step := by
      unfold okJoin at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      exact hok.1.1.1
    have hjs : (join g₁ g₂).current_step = g₁.current_step := rfl
    intro P y w hk
    rcases hu P y w hk with hk1 | hk2
    · obtain ⟨S, hc, ha, hy, hw⟩ := h₁ P y w hk1
      exact ⟨S, carried_join_left hc, by rw [hjs]; exact ha, by rw [hjs]; exact hy, by rw [hjs]; exact hw⟩
    · obtain ⟨S, hc, ha, hy, hw⟩ := h₂ P y w hk2
      exact ⟨S, carried_join_right hcs hc, by rw [hjs, hcs]; exact ha, by rw [hjs, hcs]; exact hy,
        by rw [hjs, hcs]; exact hw⟩
  · exact h₁

-- ============================================================
-- LinksStep
-- ============================================================

theorem revPrims_linksStep : RevPrims LinksStep := by
  refine ⟨fun g id hg => hg, fun g x w hg => hg, ?_, fun g b hg => hg, ?_⟩
  · intro g id hg n hn
    simp only [removeNode, killVertex, List.mem_map, List.mem_filter] at hn
    obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hn
    have := hg m hm
    exact ⟨fun p hp => this.1 p (List.mem_filter.mp hp).1, fun s hs => this.2 s (List.mem_filter.mp hs).1⟩
  · intro g hg n hn
    unfold pruneLinks at hn
    split at hn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      have := hg m hm
      exact ⟨fun p hp => this.1 p (List.mem_filter.mp hp).1, fun s hs => this.2 s (List.mem_filter.mp hs).1⟩
    · exact hg n hn

theorem linksStep_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hg : LinksStep g) (hd : d.step = g.current_step) : LinksStep (g.addNode d title forb) := by
  intro n hn
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have := hg m hm
    refine ⟨this.1, fun s hs => ?_⟩
    rcases List.mem_append.mp hs with hs | hs
    · exact this.2 s hs
    · obtain ⟨hsn, hp⟩ := gained_new hs
      obtain ⟨_, _, _, hstep⟩ := step_of_newParents hp
      rw [newRow_step hd hsn]
      show g.current_step = m.id.id.step + 1
      omega
  · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp hn
    refine ⟨fun p hp => ?_, fun s hs => by cases hs⟩
    obtain ⟨_, _, _, hstep⟩ := step_of_newParents (rowParents_sub hp)
    show p.id.step + 1 = pid.id.step
    rw [newRow_step hd hpid]; omega

theorem linksStep_join {g₁ g₂ : GPathB} (h₁ : LinksStep g₁) (h₂ : LinksStep g₂) : LinksStep (join g₁ g₂) := by
  intro n hn
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have hm1 := h₁ m hm
    split
    · rename_i m' hm'
      have hm2 := h₂ m' (node?_mem hm')
      have hid : m'.id = m.id := node?_id hm'
      refine ⟨fun p hp => ?_, fun s hs => ?_⟩
      · simp only [mergeNode, List.mem_append, List.mem_filter] at hp
        rcases hp with hp | ⟨hp, _⟩
        · exact hm1.1 p hp
        · show p.id.step + 1 = m.id.id.step
          rw [← hid]; exact hm2.1 p hp
      · simp only [mergeNode, List.mem_append, List.mem_filter] at hs
        rcases hs with hs | ⟨hs, _⟩
        · exact hm1.2 s hs
        · show s.id.step = m.id.id.step + 1
          rw [← hid]; exact hm2.2 s hs
    · exact hm1
  · exact h₂ n (List.mem_filter.mp hn).1

-- ============================================================
-- Below
-- ============================================================

theorem revPrims_below : RevPrims Below := by
  refine ⟨fun g id hg => hg, fun g x w hg => hg, ?_, fun g b hg => hg, ?_⟩
  · intro g id hg n hn
    simp only [removeNode, killVertex, List.mem_map, List.mem_filter] at hn
    obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hn
    exact hg m hm
  · intro g hg n hn
    rw [(pruneLinks_graph g).2.2]
    unfold pruneLinks at hn
    split at hn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      exact hg m hm
    · exact hg n hn

theorem below_join {g₁ g₂ : GPathB} (h₁ : Below g₁) (h₂ : Below g₂) (hcs : g₁.current_step = g₂.current_step) :
    Below (join g₁ g₂) := by
  intro n hn
  show n.id.id.step < g₁.current_step
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have := h₁ m hm
    split <;> exact this
  · rw [hcs]; exact h₂ n (List.mem_filter.mp hn).1

end GPathB

end AbsSatBingo.Model
