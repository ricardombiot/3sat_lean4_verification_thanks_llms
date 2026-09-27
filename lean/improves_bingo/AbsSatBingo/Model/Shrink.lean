-- lean/improves_bingo/AbsSatBingo/Model/Shrink.lean
import AbsSatBingo.Model.Ops

/-!
# El review solo borra (fase L5)

`Shrinks h g`: `h` está por debajo de `g` (`Sub`) y su medida no es mayor. Se demuestra para cada operación del
review y para `filterAll`: es la condición `defl` que el marco de reglas (L6) pide a toda regla, y la medida que
no sube es la que acota las vueltas del lector.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- `h` solo ha borrado respecto a `g`, y su medida no es mayor. -/
def Shrinks (h g : GPathB) : Prop := Sub h g ∧ h.measure ≤ g.measure

theorem Shrinks.refl (g : GPathB) : Shrinks g g := ⟨Sub.refl g, Nat.le_refl _⟩

theorem Shrinks.trans {a b c : GPathB} (hab : Shrinks a b) (hbc : Shrinks b c) : Shrinks a c :=
  ⟨hab.1.trans hbc.1, Nat.le_trans hab.2 hbc.2⟩

/-- Cambiar `dirty` no cambia nada de lo que se mide. -/
theorem shrinks_dirty (g : GPathB) (b : Bool) : Shrinks { g with dirty := b } g :=
  ⟨⟨rfl, rfl, fun _ h => h, fun _ _ h => h, fun n hn => ⟨n, hn, rfl, fun _ h => h, fun _ h => h⟩⟩, Nat.le_refl _⟩

theorem shrinks_of_dirty {h g : GPathB} (b : Bool) (hs : Shrinks h g) : Shrinks { h with dirty := b } g :=
  (shrinks_dirty h b).trans hs

theorem shrinks_removeEdge (g : GPathB) (x w : PathNodeId) : Shrinks (g.removeEdge x w) g :=
  ⟨sub_removeEdge g x w, measure_removeEdge_le g x w⟩

theorem shrinks_killVertex (g : GPathB) (id : PathNodeId) : Shrinks (g.killVertex id) g :=
  ⟨sub_killVertex g id, measure_killVertex_le g id⟩

theorem shrinks_removeNode (g : GPathB) (id : PathNodeId) : Shrinks (g.removeNode id) g :=
  ⟨sub_removeNode g id, measure_removeNode_le g id⟩

/-- Un `foldl` de pasos que solo borran solo borra. -/
theorem shrinks_foldl {α : Type} (f : GPathB → α → GPathB) (hf : ∀ g a, Shrinks (f g a) g) :
    ∀ (l : List α) (g : GPathB), Shrinks (l.foldl f g) g := by
  intro l
  induction l with
  | nil => intro g; exact Shrinks.refl g
  | cons a as ih => intro g; exact (ih (f g a)).trans (hf g a)

-- ============================================================
-- Filtro y purga
-- ============================================================

theorem shrinks_filterRequire (g : GPathB) (req : NodeId) : Shrinks (g.filterRequire req) g := by
  unfold filterRequire
  split
  · exact shrinks_of_dirty _ (shrinks_foldl _ shrinks_killVertex _ _)
  · exact Shrinks.refl g

theorem shrinks_purgeStep (g : GPathB) (id : PathNodeId) : Shrinks (g.purgeStep id) g := by
  unfold purgeStep
  split
  · exact Shrinks.refl g
  · split
    · exact Shrinks.refl g
    · exact shrinks_of_dirty _ (shrinks_removeNode g id)

theorem shrinks_purgeRound (g : GPathB) : Shrinks g.purgeRound g :=
  shrinks_foldl _ shrinks_purgeStep _ _

theorem shrinks_purgeFuel : ∀ (n : Nat) (g : GPathB), Shrinks (purgeFuel n g) g := by
  intro n
  induction n with
  | zero => intro g; exact Shrinks.refl g
  | succ n ih =>
    intro g
    simp only [purgeFuel]
    split
    · split
      · exact (ih _).trans (shrinks_purgeRound g)
      · exact shrinks_purgeRound g
    · exact Shrinks.refl g

theorem shrinks_clean (g : GPathB) : Shrinks g.clean g := shrinks_purgeFuel _ _

-- ============================================================
-- Parejas
-- ============================================================

theorem shrinks_pairSweep (g : GPathB) : Shrinks g.pairSweep.1 g := by
  unfold pairSweep
  exact shrinks_foldl _ (fun h (e : PathNodeId × PathNodeId) => shrinks_removeEdge h e.1 e.2) _ _

theorem shrinks_pairFuel : ∀ (n : Nat) (g : GPathB), Shrinks (pairFuel n g) g := by
  intro n
  induction n with
  | zero => intro g; exact Shrinks.refl g
  | succ n ih =>
    intro g
    simp only [pairFuel]
    split
    · split
      · exact (ih _).trans ((shrinks_clean _).trans (shrinks_of_dirty _ (shrinks_pairSweep g)))
      · exact Shrinks.refl g
    · exact Shrinks.refl g

theorem shrinks_cleanPair (g : GPathB) : Shrinks g.cleanPair g :=
  (shrinks_pairFuel _ _).trans (shrinks_clean g)

-- ============================================================
-- Enlaces caducados
-- ============================================================

theorem shrinks_pruneLinks (g : GPathB) : Shrinks g.pruneLinks g := by
  unfold pruneLinks
  split
  · refine ⟨⟨rfl, rfl, fun _ h => h, fun _ _ h => h, ?_⟩, ?_⟩
    · intro n hn
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      exact ⟨m, hm, rfl, fun _ h => (List.mem_filter.mp h).1, fun _ h => (List.mem_filter.mp h).1⟩
    · simp only [measure, List.map_map]
      have := sum_map_le_of_le (PNodeB.weight ∘ fun n =>
        { n with parents := n.parents.filter (g.linkOk n.id), sons := n.sons.filter (g.linkOk n.id) })
        PNodeB.weight g.nodes (fun n _ => by
          simp only [Function.comp, PNodeB.weight]
          have := List.length_filter_le (g.linkOk n.id) n.parents
          have := List.length_filter_le (g.linkOk n.id) n.sons
          omega)
      omega
  · exact Shrinks.refl g

-- ============================================================
-- Las pasadas
-- ============================================================

theorem shrinks_cutSupport (g : GPathB) (x : PathNodeId) (sup : List PathNodeId) :
    Shrinks (g.cutSupport x sup).1 g :=
  shrinks_foldl _ (fun h w => shrinks_removeEdge h x w) _ _

theorem shrinks_cutStep (sel : PNodeB → List PathNodeId) (g : GPathB) (n : PNodeB) :
    Shrinks (cutStep sel g n) g := by
  unfold cutStep
  split
  · dsimp only
    split
    · exact shrinks_of_dirty _ (shrinks_cutSupport g n.id _)
    · exact shrinks_cutSupport g n.id _
  · exact Shrinks.refl g

theorem shrinks_reviewNode (sel : PNodeB → List PathNodeId) (g : GPathB) (id : PathNodeId) :
    Shrinks (reviewNode sel g id) g := by
  unfold reviewNode
  split
  · exact Shrinks.refl g
  · rename_i n _
    show Shrinks (if (cutStep sel g n).isValidNode n then cutStep sel g n
      else { (cutStep sel g n).removeNode id with dirty := true }) g
    split
    · exact shrinks_cutStep sel g n
    · exact (shrinks_of_dirty _ (shrinks_removeNode _ id)).trans (shrinks_cutStep sel g n)

theorem shrinks_reviewLine (sel : PNodeB → List PathNodeId) (g : GPathB) (k : Int) :
    Shrinks (reviewLine sel g k) g :=
  shrinks_foldl _ (shrinks_reviewNode sel) _ _

theorem shrinks_reviewSteps (sel : PNodeB → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathB), Shrinks (reviewSteps sel g ks) g := by
  intro ks
  induction ks with
  | nil => intro g; exact Shrinks.refl g
  | cons k ks ih =>
    intro g
    simp only [reviewSteps]
    split
    · exact (ih _).trans (shrinks_reviewLine sel g k)
    · exact shrinks_reviewLine sel g k

theorem shrinks_reviewParents (g : GPathB) : Shrinks g.reviewParents g := by
  unfold reviewParents; split
  · exact shrinks_reviewSteps _ _ _
  · exact Shrinks.refl g

theorem shrinks_reviewSons (g : GPathB) : Shrinks g.reviewSons g := by
  unfold reviewSons; split
  · exact shrinks_reviewSteps _ _ _
  · exact Shrinks.refl g

-- ============================================================
-- El review
-- ============================================================

theorem shrinks_reviewPass (g : GPathB) : Shrinks g.reviewPass g :=
  (shrinks_pruneLinks _).trans ((shrinks_reviewSons _).trans ((shrinks_reviewParents _).trans
    ((shrinks_pruneLinks _).trans (shrinks_cleanPair g))))

theorem shrinks_reviewFuel : ∀ (n : Nat) (g : GPathB), Shrinks (reviewFuel n g) g := by
  intro n
  induction n with
  | zero => intro g; exact Shrinks.refl g
  | succ n ih =>
    intro g
    simp only [reviewFuel]
    split
    · exact (ih _).trans ((shrinks_reviewPass _).trans (shrinks_dirty g false))
    · exact Shrinks.refl g

theorem shrinks_review (g : GPathB) : Shrinks g.review g := shrinks_reviewFuel _ _

/-- **El filtro con su review solo borra.** -/
theorem shrinks_filterAll (g : GPathB) (reqs : List NodeId) : Shrinks (g.filterAll reqs) g :=
  (shrinks_review _).trans (shrinks_foldl _ shrinks_filterRequire _ _)

end GPathB

end AbsSatBingo.Model
