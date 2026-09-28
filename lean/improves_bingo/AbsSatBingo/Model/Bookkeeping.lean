-- lean/improves_bingo/AbsSatBingo/Model/Bookkeeping.lean
import AbsSatBingo.Model.Kernel

/-!
# Contabilidad: predicados que el review y el filtro conservan

Un combinador genérico (`RevPrims`): todo predicado que conservan las primitivas del review (matar un vértice,
quitar una arista, quitar un nodo, cambiar `dirty`, podar enlaces) lo conservan el review entero
(`revPrims_review`) y el filtro (`revPrims_filterAll`). Instancias: `EdgesAlive` (las posesiones unen vivos) y
`NodupIds` (un documento por id), con la fila nueva (`addNode`) y el join aparte.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange dedupPids nodup_dedupPids mem_dedupPids)

namespace GPathB

/-- Lo que las primitivas del review conservan. -/
structure RevPrims (P : GPathB → Prop) : Prop where
  kill   : ∀ g id, P g → P (g.killVertex id)
  rmEdge : ∀ g x w, P g → P (g.removeEdge x w)
  rmNode : ∀ g id, P g → P (g.removeNode id)
  dirty  : ∀ g (b : Bool), P g → P { g with dirty := b }
  links  : ∀ g, P g → P g.pruneLinks

variable {P : GPathB → Prop}

theorem revPrims_purgeStep (h : RevPrims P) (g : GPathB) (id : PathNodeId) (hg : P g) : P (g.purgeStep id) := by
  unfold purgeStep
  split
  · exact hg
  · split
    · exact hg
    · exact h.dirty _ _ (h.rmNode _ _ hg)

theorem revPrims_purgeFuel (h : RevPrims P) : ∀ (n : Nat) (g : GPathB), P g → P (purgeFuel n g) := by
  intro n
  induction n with
  | zero => intro g hg; exact hg
  | succ n ih =>
    intro g hg
    have hr : P g.purgeRound := inv_foldl P purgeStep _ (fun g' a _ hc => revPrims_purgeStep h g' a hc) g hg
    simp only [purgeFuel]
    split
    · split
      · exact ih _ hr
      · exact hr
    · exact hg

theorem revPrims_clean (h : RevPrims P) (g : GPathB) (hg : P g) : P g.clean := revPrims_purgeFuel h _ _ hg

theorem revPrims_pairFuel (h : RevPrims P) : ∀ (n : Nat) (g : GPathB), P g → P (pairFuel n g) := by
  intro n
  induction n with
  | zero => intro g hg; exact hg
  | succ n ih =>
    intro g hg
    have hs : P g.pairSweep.1 := by
      unfold pairSweep
      exact inv_foldl P (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) _
        (fun g' e _ hc => h.rmEdge _ _ _ hc) g hg
    simp only [pairFuel]
    split
    · split
      · exact ih _ (revPrims_clean h _ (h.dirty _ _ hs))
      · exact hg
    · exact hg

theorem revPrims_cleanPair (h : RevPrims P) (g : GPathB) (hg : P g) : P g.cleanPair :=
  revPrims_pairFuel h _ _ (revPrims_clean h _ hg)

theorem revPrims_cutStep (h : RevPrims P) (sel : PNodeB → List PathNodeId) (g : GPathB) (n : PNodeB) (hg : P g) :
    P (cutStep sel g n) := by
  have hc : P (cutSupport g n.id (sel n)).1 := by
    unfold cutSupport
    exact inv_foldl P (fun h w => h.removeEdge n.id w) _ (fun g' w _ hc => h.rmEdge _ _ _ hc) g hg
  unfold cutStep
  by_cases hv : g.isValidNode n = true
  · by_cases hr : (cutSupport g n.id (sel n)).2 = true
    · have heq : cutStep sel g n = { (cutSupport g n.id (sel n)).1 with dirty := true } := by
        simp [cutStep, hv, hr]
      unfold cutStep at heq; rw [heq]; exact h.dirty _ _ hc
    · have heq : cutStep sel g n = (cutSupport g n.id (sel n)).1 := by simp [cutStep, hv, hr]
      unfold cutStep at heq; rw [heq]; exact hc
  · rw [if_neg hv]; exact hg

theorem revPrims_reviewNode (h : RevPrims P) (sel : PNodeB → List PathNodeId) (g : GPathB) (id : PathNodeId)
    (hg : P g) : P (reviewNode sel g id) := by
  unfold reviewNode
  split
  · exact hg
  · rename_i n _
    have hc := revPrims_cutStep h sel g n hg
    show P (if (cutStep sel g n).isValidNode n then cutStep sel g n
      else { (cutStep sel g n).removeNode id with dirty := true })
    split
    · exact hc
    · exact h.dirty _ _ (h.rmNode _ _ hc)

theorem revPrims_reviewSteps (h : RevPrims P) (sel : PNodeB → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathB), P g → P (reviewSteps sel g ks) := by
  intro ks
  induction ks with
  | nil => intro g hg; exact hg
  | cons k ks ih =>
    intro g hg
    have h1 : P (reviewLine sel g k) := by
      unfold reviewLine
      exact inv_foldl P (reviewNode sel) _ (fun g' a _ hc => revPrims_reviewNode h sel g' a hc) g hg
    simp only [reviewSteps]
    split
    · exact ih _ h1
    · exact h1

theorem revPrims_reviewPass (h : RevPrims P) (g : GPathB) (hg : P g) : P g.reviewPass := by
  have h1 := revPrims_cleanPair h g hg
  have h2 := h.links _ h1
  have h3 : P g.cleanPair.pruneLinks.reviewParents := by
    unfold reviewParents; split
    · exact revPrims_reviewSteps h _ _ _ h2
    · exact h2
  have h4 : P g.cleanPair.pruneLinks.reviewParents.reviewSons := by
    unfold reviewSons; split
    · exact revPrims_reviewSteps h _ _ _ h3
    · exact h3
  exact h.links _ h4

theorem revPrims_review (h : RevPrims P) (g : GPathB) (hg : P g) : P g.review := by
  unfold review
  generalize g.measure + 1 = n
  induction n generalizing g with
  | zero => exact hg
  | succ n ih =>
    simp only [reviewFuel]
    split
    · exact ih _ (revPrims_reviewPass h _ (h.dirty _ _ hg))
    · exact hg

theorem revPrims_filterAll (h : RevPrims P) (g : GPathB) (reqs : List NodeId) (hg : P g) : P (g.filterAll reqs) := by
  unfold filterAll
  apply revPrims_review h
  refine inv_foldl P filterRequire reqs (fun g' r _ hc => ?_) g hg
  unfold filterRequire
  split
  · exact h.dirty _ _ (inv_foldl P killVertex _ (fun g'' q _ hc' => h.kill _ _ hc') g' hc)
  · exact hc

-- ============================================================
-- EdgesAlive
-- ============================================================

theorem ne_of_joins {e : PathNodeId × PathNodeId} {y w id : PathNodeId}
    (hj : (e.1 = y ∧ e.2 = w) ∨ (e.1 = w ∧ e.2 = y)) (h1 : ¬ e.1 = id) (h2 : ¬ e.2 = id) : y ≠ id ∧ w ≠ id := by
  rcases hj with ⟨a, b⟩ | ⟨a, b⟩
  · exact ⟨a ▸ h1, b ▸ h2⟩
  · exact ⟨b ▸ h2, a ▸ h1⟩

theorem edgesAlive_killVertex {g : GPathB} (hg : EdgesAlive g) (id : PathNodeId) : EdgesAlive (g.killVertex id) := by
  intro y w hyw
  rw [adj_iff] at hyw
  rcases hyw with ⟨rfl, hal⟩ | ⟨e, he, hj⟩
  · exact ⟨hal, hal⟩
  · have ⟨he1, he2⟩ := List.mem_filter.mp he
    obtain ⟨hy, hw⟩ := hg y w ((adj_iff g y w).mpr (Or.inr ⟨e, he1, hj⟩))
    simp only [touches, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at he2
    obtain ⟨hy', hw'⟩ := ne_of_joins hj he2.1 he2.2
    exact ⟨List.mem_filter.mpr ⟨hy, bne_iff_ne.mpr hy'⟩, List.mem_filter.mpr ⟨hw, bne_iff_ne.mpr hw'⟩⟩

theorem revPrims_edgesAlive : RevPrims EdgesAlive := by
  refine ⟨fun g id hg => edgesAlive_killVertex hg id, ?_, ?_, ?_, ?_⟩
  · intro g x w' hg y w hyw
    have := hg y w ((sub_removeEdge g x w').adj _ _ hyw)
    exact this
  · intro g id hg y w hyw
    exact edgesAlive_killVertex hg id y w hyw
  · intro g b hg; exact hg
  · intro g hg y w hyw
    have ⟨ha, he, _⟩ := pruneLinks_graph g
    have hadj : g.pruneLinks.adjb y w = g.adjb y w := by unfold adjb isAlive hasEdge; rw [ha, he]
    have := hg y w (by unfold Adj; rw [← hadj]; exact hyw)
    rw [ha]; exact this

-- ============================================================
-- NodupIds
-- ============================================================

theorem nodupIds_of_sublist {g h : GPathB} (hs : (h.nodes.map (·.id)).Sublist (g.nodes.map (·.id)))
    (hg : NodupIds g) : NodupIds h := List.Nodup.sublist hs hg

theorem revPrims_nodupIds : RevPrims NodupIds := by
  refine ⟨fun g id hg => hg, fun g x w hg => hg, ?_, fun g b hg => hg, ?_⟩
  · intro g id hg
    unfold NodupIds removeNode killVertex
    dsimp only
    rw [List.map_map]
    have : ((·.id) ∘ unlinkAll id) = (·.id : PNodeB → PathNodeId) := by funext n; rfl
    rw [this]
    exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) hg
  · intro g hg
    unfold NodupIds pruneLinks
    split
    · dsimp only
      rw [List.map_map]
      exact hg
    · exact hg

-- ============================================================
-- La fila nueva y el join
-- ============================================================

theorem edgesAlive_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hg : EdgesAlive g) : EdgesAlive (g.addNode d title forb) := by
  have hal : ∀ q ∈ g.alive, q ∈ (g.addNode d title forb).alive := fun q hq => List.mem_append_left _ hq
  intro y w hyw
  rw [adj_iff] at hyw
  rcases hyw with ⟨rfl, h⟩ | ⟨e, he, hj⟩
  · exact ⟨h, h⟩
  · rcases List.mem_append.mp he with hold | hnew
    · obtain ⟨hy, hw⟩ := hg y w ((adj_iff g y w).mpr (Or.inr ⟨e, hold, hj⟩))
      exact ⟨hal y hy, hal w hw⟩
    · obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp hnew
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
      have hp : pid ∈ (g.addNode d title forb).alive := List.mem_append_right _ hpid
      have hw'' : w' ∈ (g.addNode d title forb).alive := hal w' (List.mem_filter.mp hw').1
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact ⟨hp, hw''⟩
      · rw [← h1, ← h2]; exact ⟨hw'', hp⟩

theorem edgesAlive_join {g₁ g₂ : GPathB} (h₁ : EdgesAlive g₁) (h₂ : EdgesAlive g₂) : EdgesAlive (join g₁ g₂) := by
  intro y w hyw
  rcases adj_join_cases hyw with ha | ha
  · obtain ⟨hy, hw⟩ := h₁ y w ha
    exact ⟨(alive_join g₁ g₂ y).mpr (Or.inl hy), (alive_join g₁ g₂ w).mpr (Or.inl hw)⟩
  · obtain ⟨hy, hw⟩ := h₂ y w ha
    exact ⟨(alive_join g₁ g₂ y).mpr (Or.inr hy), (alive_join g₁ g₂ w).mpr (Or.inr hw)⟩

theorem edgesAlive_doJoin {g₁ g₂ : GPathB} (h₁ : EdgesAlive g₁) (h₂ : EdgesAlive g₂) : EdgesAlive (doJoin g₁ g₂) := by
  unfold doJoin; split
  · exact edgesAlive_join h₁ h₂
  · exact h₁

theorem nodupIds_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hg : NodupIds g) (hb : Machine.Below g) (hd : d.step = g.current_step) : NodupIds (g.addNode d title forb) := by
  unfold NodupIds addNode
  dsimp only
  rw [List.map_append, List.map_map, List.map_map]
  have h1 : ((·.id) ∘ fun n : PNodeB => { n with sons := n.sons ++ g.gainedSons d forb n }) =
      (·.id : PNodeB → PathNodeId) := by funext n; rfl
  have h2 : ((·.id) ∘ g.rowNode d title) = (id : PathNodeId → PathNodeId) := by funext q; rfl
  rw [h1, h2, List.map_id]
  refine List.nodup_append.mpr ⟨hg, ?_, ?_⟩
  · exact List.Nodup.sublist List.filter_sublist (by
      unfold shiftRowIds; split
      · exact nodup_dedupPids _
      · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
  · intro a ha b hb' hab
    subst hab
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
    have hlt := hb n hn
    have hid := Machine.mapId_of_mem_shiftRowIds (List.mem_filter.mp hb').1
    rw [hid, hd] at hlt
    exact Int.lt_irrefl _ hlt

theorem join_ids (g₁ g₂ : GPathB) : (join g₁ g₂).nodes.map (·.id) =
    g₁.nodes.map (·.id) ++ (g₂.nodes.filter (fun m => (g₁.node? m.id).isNone)).map (·.id) := by
  unfold join
  dsimp only
  rw [List.map_append]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro n _
  simp only [Function.comp]
  split <;> rfl

theorem nodupIds_join {g₁ g₂ : GPathB} (h₁ : NodupIds g₁) (h₂ : NodupIds g₂) : NodupIds (join g₁ g₂) := by
  unfold NodupIds
  rw [join_ids]
  refine List.nodup_append.mpr ⟨h₁, List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h₂, ?_⟩
  intro a ha b hb hab
  subst hab
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
  obtain ⟨m, hm, hmid⟩ := List.mem_map.mp hb
  have hnone := (List.mem_filter.mp hm).2
  rw [hmid] at hnone
  have := node?_of_nodup h₁ hn
  simp [this] at hnone

theorem nodupIds_doJoin {g₁ g₂ : GPathB} (h₁ : NodupIds g₁) (h₂ : NodupIds g₂) : NodupIds (doJoin g₁ g₂) := by
  unfold doJoin; split
  · exact nodupIds_join h₁ h₂
  · exact h₁

end GPathB

end AbsSatBingo.Model
