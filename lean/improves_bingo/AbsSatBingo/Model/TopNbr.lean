-- lean/improves_bingo/AbsSatBingo/Model/TopNbr.lean
import AbsSatBingo.Model.TopExact

/-!
# Los vecinos de una cima: `TopsApart` y `TopNbr`

* **`TopsApart`**: dos cimas distintas no se poseen.
* **`TopNbr`**: en el paso de origen, una cima solo posee a sus padres (nodos cuyo id es su `parent_id`).

Los conservan el review y la selección (`RevPrims`), el join (con el mismo paso) y la fila nueva: una cima nueva
posee lo que poseen sus padres, y en el paso de sus padres un padre solo se posee a sí mismo (`TopsApart`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Machine (Below mapId_of_mem_shiftRowIds)

def TopsApart (g : GPathB) : Prop :=
  ∀ y w, y.id.step = g.current_step - 1 → w.id.step = g.current_step - 1 → g.Adj y w → y = w

theorem revPrims_topsApart : RevPrims TopsApart := by
  refine ⟨fun g id hg y w h1 h2 h => hg y w h1 h2 ((sub_killVertex g id).adj _ _ h),
    fun g x w' hg y w h1 h2 h => hg y w h1 h2 ((sub_removeEdge g x w').adj _ _ h),
    fun g id hg y w h1 h2 h => hg y w h1 h2 ((sub_removeNode g id).adj _ _ h),
    fun g b hg => hg, fun g hg y w h1 h2 h => ?_⟩
  have ⟨ha, he, hs⟩ := pruneLinks_graph g
  have hadj : g.pruneLinks.adjb y w = g.adjb y w := by unfold adjb isAlive hasEdge; rw [ha, he]
  exact hg y w (hs ▸ h1) (hs ▸ h2) (by unfold Adj; rw [← hadj]; exact h)

theorem revPrims_topNbr : RevPrims TopNbr := by
  refine ⟨fun g id hg t y h1 h2 h => hg t y h1 h2 ((sub_killVertex g id).adj _ _ h),
    fun g x w' hg t y h1 h2 h => hg t y h1 h2 ((sub_removeEdge g x w').adj _ _ h),
    fun g id hg t y h1 h2 h => hg t y h1 h2 ((sub_removeNode g id).adj _ _ h),
    fun g b hg => hg, fun g hg t y h1 h2 h => ?_⟩
  have ⟨ha, he, hs⟩ := pruneLinks_graph g
  have hadj : g.pruneLinks.adjb t y = g.adjb t y := by unfold adjb isAlive hasEdge; rw [ha, he]
  exact hg t y (hs ▸ h1) (hs ▸ h2) (by unfold Adj; rw [← hadj]; exact h)

theorem topsApart_join {e g : GPathB} (he : TopsApart e) (hg : TopsApart g) (hcs : e.current_step = g.current_step) :
    TopsApart (join e g) := by
  intro y w h1 h2 h
  have hj : (join e g).current_step = e.current_step := rfl
  rcases adj_join_cases h with h | h
  · exact he y w (hj ▸ h1) (hj ▸ h2) h
  · exact hg y w (hcs ▸ hj ▸ h1) (hcs ▸ hj ▸ h2) h

theorem topNbr_join {e g : GPathB} (he : TopNbr e) (hg : TopNbr g) (hcs : e.current_step = g.current_step) :
    TopNbr (join e g) := by
  intro t y h1 h2 h
  have hj : (join e g).current_step = e.current_step := rfl
  rcases adj_join_cases h with h | h
  · exact he t y (hj ▸ h1) (hj ▸ h2) h
  · exact hg t y (hcs ▸ hj ▸ h1) (hcs ▸ hj ▸ h2) h

theorem topsApart_doJoin {e g : GPathB} (he : TopsApart e) (hg : TopsApart g) : TopsApart (doJoin e g) := by
  unfold doJoin; split
  · rename_i hok
    unfold okJoin at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    exact topsApart_join he hg hok.1.1.1
  · exact he

theorem topNbr_doJoin {e g : GPathB} (he : TopNbr e) (hg : TopNbr g) : TopNbr (doJoin e g) := by
  unfold doJoin; split
  · rename_i hok
    unfold okJoin at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    exact topNbr_join he hg hok.1.1.1
  · exact he

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

theorem topsApart_addNode (hdocs : AliveDocs g) (hb : Below g) (hea : EdgesAlive g) :
    TopsApart (g.addNode d title forb) := by
  intro y w h1 h2 h
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  exact adj_addNode_new hdocs hb hea (by omega) (by omega) h

/-- **Una cima nueva solo posee, en el paso de sus padres, a sus padres.** -/
theorem topNbr_addNode (hdocs : AliveDocs g) (hb : Below g) (hea : EdgesAlive g) (hta : TopsApart g)
    (hd : d.step = g.current_step) : TopNbr (g.addNode d title forb) := by
  intro t y h1 h2 h
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  rw [hcs] at h1 h2
  rw [adj_iff] at h
  rcases h with ⟨rfl, _⟩ | ⟨e, he, hj⟩
  · omega
  · rcases List.mem_append.mp he with hold | hnew
    · -- una arista vieja une vivos viejos, por debajo del paso de la cima nueva
      have hold' : g.Adj t y := (adj_iff g t y).mpr (Or.inr ⟨e, hold, hj⟩)
      have := alive_below hdocs hb (hea t y hold').1
      omega
    · obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp hnew
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
      have hps := newRow_step hd hpid
      have ⟨hw1, hw2⟩ := List.mem_filter.mp hw'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw2
      obtain ⟨_, hsup⟩ := hw2
      obtain ⟨p, hp, hpw⟩ := List.any_eq_true.mp hsup
      -- la arista es (pid, w'), y t es pid (el de la fila nueva)
      have hpt : pid = t ∧ w' = y := by
        rcases hj with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact ⟨e1, e2⟩
        · exfalso
          have e1 : pid = y := e1
          rw [← e1] at h2; omega
      obtain ⟨rfl, rfl⟩ := hpt
      -- el padre p está en la cima vieja; posee a w', de la cima vieja: son el mismo
      obtain ⟨_, _, _, hpst⟩ := step_of_newParents (rowParents_sub hp)
      have hpeq : p = w' := hta p w' hpst (by omega) hpw
      subst hpeq
      have hsh : shiftPid p d = pid := beq_iff_eq.mp (List.mem_filter.mp hp).2
      rw [← hsh]
      rfl

end GPathB

end AbsSatBingo.Model
