-- lean/improves_bingo/AbsSatBingo/Model/Reader.lean
import AbsSatBingo.Model.Keeps
import AbsSatBingo.Model.Driver

/-!
# El lector no se queda sin salida si no hay zombis (fase L6, parte 3)

**`readG_isSome_of_noZombie`**: si todo estado válido que el lector visita lleva una camarilla (`NoZombie`), el
lector termina. Es la completitud del lector reducida a una sola hipótesis sobre los estados, que es la que las
reglas nuevas sobre aristas tienen que hacer demostrable.

El argumento: en un estado válido con elección en el paso `k`, la camarilla que lleva tiene un nodo vivo en `k`;
fijar su nodo de mapa conserva la camarilla (`carried_filterAll`), así que el pin deja el estado válido y
`tryPins` encuentra alguno. Para el combustible: todo vivo tiene documento (`AliveDocs`, que el filtro conserva),
así que el pin en un paso con elección mata a alguien y la medida baja estrictamente.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

-- ============================================================
-- Todo vivo tiene documento
-- ============================================================

def AliveDocs (g : GPathB) : Prop := ∀ q ∈ g.alive, ∃ n ∈ g.nodes, n.id = q

theorem aliveDocs_dirty {g : GPathB} (h : AliveDocs g) (b : Bool) : AliveDocs { g with dirty := b } := h

theorem aliveDocs_killVertex {g : GPathB} (h : AliveDocs g) (id : PathNodeId) : AliveDocs (g.killVertex id) :=
  fun q hq => h q (List.mem_filter.mp hq).1

theorem aliveDocs_removeEdge {g : GPathB} (h : AliveDocs g) (x w : PathNodeId) : AliveDocs (g.removeEdge x w) := h

theorem aliveDocs_removeNode {g : GPathB} (h : AliveDocs g) (id : PathNodeId) : AliveDocs (g.removeNode id) := by
  intro q hq
  have hq' := List.mem_filter.mp hq
  obtain ⟨n, hn, rfl⟩ := h q hq'.1
  exact ⟨unlinkAll id n, List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hn, hq'.2⟩, rfl⟩, rfl⟩

theorem aliveDocs_foldl {α : Type} (f : GPathB → α → GPathB) (hf : ∀ g a, AliveDocs g → AliveDocs (f g a)) :
    ∀ (l : List α) (g : GPathB), AliveDocs g → AliveDocs (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons a as ih => intro g h; exact ih _ (hf g a h)

theorem aliveDocs_filterRequire {g : GPathB} (h : AliveDocs g) (req : NodeId) :
    AliveDocs (g.filterRequire req) := by
  unfold filterRequire
  split
  · exact aliveDocs_dirty (aliveDocs_foldl _ (fun _ a h => aliveDocs_killVertex h a) _ _ h) _
  · exact h

theorem aliveDocs_purgeStep {g : GPathB} (h : AliveDocs g) (id : PathNodeId) : AliveDocs (g.purgeStep id) := by
  unfold purgeStep
  split
  · exact h
  · split
    · exact h
    · exact aliveDocs_dirty (aliveDocs_removeNode h id) _

theorem aliveDocs_purgeFuel : ∀ (n : Nat) (g : GPathB), AliveDocs g → AliveDocs (purgeFuel n g) := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    have hr : AliveDocs g.purgeRound := aliveDocs_foldl _ (fun _ a h => aliveDocs_purgeStep h a) _ _ h
    simp only [purgeFuel]
    split
    · split
      · exact ih _ hr
      · exact hr
    · exact h

theorem aliveDocs_clean {g : GPathB} (h : AliveDocs g) : AliveDocs g.clean := aliveDocs_purgeFuel _ _ h

theorem aliveDocs_pairFuel : ∀ (n : Nat) (g : GPathB), AliveDocs g → AliveDocs (pairFuel n g) := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    have hs : AliveDocs g.pairSweep.1 := by
      unfold pairSweep
      exact aliveDocs_foldl _ (fun _ (e : PathNodeId × PathNodeId) h => aliveDocs_removeEdge h e.1 e.2) _ _ h
    simp only [pairFuel]
    split
    · split
      · exact ih _ (aliveDocs_clean (aliveDocs_dirty hs _))
      · exact h
    · exact h

theorem aliveDocs_pruneLinks {g : GPathB} (h : AliveDocs g) : AliveDocs g.pruneLinks := by
  unfold pruneLinks
  split
  · intro q hq
    obtain ⟨n, hn, rfl⟩ := h q hq
    exact ⟨_, List.mem_map.mpr ⟨n, hn, rfl⟩, rfl⟩
  · exact h

theorem aliveDocs_reviewNode {g : GPathB} (h : AliveDocs g) (sel : PNodeB → List PathNodeId) (id : PathNodeId) :
    AliveDocs (reviewNode sel g id) := by
  have hc : ∀ n, AliveDocs (cutStep sel g n) := by
    intro n q hq
    have hs := (shrinks_cutStep sel g n).1.alive q hq
    obtain ⟨m, hm, hmid⟩ := h q hs
    exact ⟨m, by rw [nodes_cutStep]; exact hm, hmid⟩
  unfold reviewNode
  split
  · exact h
  · rename_i n _
    show AliveDocs (if (cutStep sel g n).isValidNode n then cutStep sel g n
      else { (cutStep sel g n).removeNode id with dirty := true })
    split
    · exact hc n
    · exact aliveDocs_dirty (aliveDocs_removeNode (hc n) id) _

theorem aliveDocs_reviewSteps (sel : PNodeB → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathB), AliveDocs g → AliveDocs (reviewSteps sel g ks) := by
  intro ks
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    have hl : AliveDocs (reviewLine sel g k) :=
      aliveDocs_foldl _ (fun _ a h => aliveDocs_reviewNode h sel a) _ _ h
    simp only [reviewSteps]
    split
    · exact ih _ hl
    · exact hl

theorem aliveDocs_reviewPass {g : GPathB} (h : AliveDocs g) : AliveDocs g.reviewPass := by
  have h1 : AliveDocs g.cleanPair := aliveDocs_pairFuel _ _ (aliveDocs_clean h)
  have h2 := aliveDocs_pruneLinks h1
  have h3 : AliveDocs g.cleanPair.pruneLinks.reviewParents := by
    unfold reviewParents; split
    · exact aliveDocs_reviewSteps _ _ _ h2
    · exact h2
  have h4 : AliveDocs g.cleanPair.pruneLinks.reviewParents.reviewSons := by
    unfold reviewSons; split
    · exact aliveDocs_reviewSteps _ _ _ h3
    · exact h3
  exact aliveDocs_pruneLinks h4

theorem aliveDocs_finalPass {g : GPathB} (h : AliveDocs g) : AliveDocs g.finalPass := by
  have h1 : AliveDocs g.forcedParents := by
    unfold forcedParents; split
    · exact aliveDocs_reviewSteps _ _ _ h
    · exact h
  have h2 : AliveDocs g.forcedParents.forcedSons := by
    unfold forcedSons; split
    · exact aliveDocs_reviewSteps _ _ _ h1
    · exact h1
  exact aliveDocs_pruneLinks h2

theorem aliveDocs_review {g : GPathB} (h : AliveDocs g) : AliveDocs g.review :=
  reviewFuel_pres AliveDocs (fun _ hh => aliveDocs_reviewPass (aliveDocs_dirty hh _))
    (fun _ hh => aliveDocs_finalPass hh) _ g h

theorem aliveDocs_filterAll {g : GPathB} (h : AliveDocs g) (reqs : List NodeId) :
    AliveDocs (g.filterAll reqs) :=
  aliveDocs_review (aliveDocs_foldl _ (fun _ a h => aliveDocs_filterRequire h a) _ _ h)

-- ============================================================
-- Un pin en un paso con elección baja la medida
-- ============================================================

theorem alive_foldl_killVertex :
    ∀ (l : List PathNodeId) (g : GPathB), (l.foldl killVertex g).alive = g.alive.filter (fun q => !l.contains q) := by
  intro l
  induction l with
  | nil =>
    intro g
    simp only [List.foldl_nil]
    symm
    apply List.filter_eq_self.mpr
    intro q _
    simp
  | cons a as ih =>
    intro g
    simp only [List.foldl_cons, ih, killVertex, List.filter_filter]
    congr 1
    funext q
    cases hqa : q == a <;> simp_all [bne]

theorem edges_foldl_killVertex_le :
    ∀ (l : List PathNodeId) (g : GPathB), (l.foldl killVertex g).edges.length ≤ g.edges.length := by
  intro l
  induction l with
  | nil => intro g; exact Nat.le_refl _
  | cons a as ih => intro g; exact Nat.le_trans (ih _) (List.length_filter_le _ _)

theorem nodes_foldl_killVertex :
    ∀ (l : List PathNodeId) (g : GPathB), (l.foldl killVertex g).nodes = g.nodes := by
  intro l
  induction l with
  | nil => intro g; rfl
  | cons a as ih => intro g; exact ih _

theorem measure_foldl_killVertex_le :
    ∀ (l : List PathNodeId) (g : GPathB), (l.foldl killVertex g).measure ≤ g.measure :=
  fun l g => (shrinks_foldl _ shrinks_killVertex l g).2

/-- Fijar `req` cuando algún vivo del paso tiene documento y es de otro nodo de mapa baja la medida. -/
theorem measure_filterRequire_lt {g : GPathB} (hv : g.isValid = true) (h : AliveDocs g) {req : NodeId}
    {r : PathNodeId} (hr : r ∈ g.alive) (hrs : r.id.step = req.step) (hrid : r.id ≠ req) :
    (g.filterRequire req).measure < g.measure := by
  unfold filterRequire
  rw [if_pos hv]
  dsimp only
  generalize hvict : ((g.line req.step).map (·.id)).filter (fun q => q.id != req) = victims
  have hrv : r ∈ victims := by
    rw [← hvict]
    obtain ⟨n, hn, rfl⟩ := h r hr
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hn, by simp [hrs]⟩, rfl⟩, ?_⟩
    exact bne_iff_ne.mpr hrid
  have hfold : (victims.foldl killVertex g).measure < g.measure := by
    have hal := alive_foldl_killVertex victims g
    have hlt : (victims.foldl killVertex g).alive.length < g.alive.length := by
      rw [hal]
      exact List.length_filter_lt_length_iff_exists.mpr ⟨r, hr, by simp [hrv]⟩
    have hed := edges_foldl_killVertex_le victims g
    have hnd := nodes_foldl_killVertex victims g
    unfold measure
    rw [hnd]
    omega
  show ({ victims.foldl killVertex g with dirty := _ } : GPathB).measure < g.measure
  exact hfold

-- ============================================================
-- El lector
-- ============================================================

open Driver

/-- Los estados que visita el lector a partir de `g₀`: el de partida revisado, y cualquier pin de uno visitado. -/
inductive Visited (g₀ : GPathB) : GPathB → Prop
  | start : Visited g₀ (reviewAll g₀)
  | pin {h : GPathB} (q : PathNodeId) : Visited g₀ h → Visited g₀ (h.filterAll [q.id])

/-- **Ningún zombi**: todo estado válido lleva una camarilla. -/
def NoZombie (g : GPathB) : Prop := g.isValid = true → ∃ S, Carried g S

theorem measure_pos_of_mem {g : GPathB} {q : PathNodeId} (hq : q ∈ g.alive) : 0 < g.measure := by
  unfold measure
  have : 0 < g.alive.length := List.length_pos_of_mem hq
  omega

theorem choiceAt_spec {g : GPathB} {k : Int} (h : choiceAt g k = true) :
    ∃ q r, q ∈ g.alive ∧ r ∈ g.alive ∧ q.id.step = k ∧ r.id.step = k ∧ q.id ≠ r.id := by
  unfold choiceAt at h
  obtain ⟨q, hq, hr⟩ := List.any_eq_true.mp h
  obtain ⟨r, hr', hne⟩ := List.any_eq_true.mp hr
  have hq' := List.mem_filter.mp hq
  have hr'' := List.mem_filter.mp hr'
  exact ⟨q, r, hq'.1, hr''.1, by simpa using hq'.2, by simpa using hr''.2, bne_iff_ne.mp hne⟩

theorem readLoop_isSome (g₀ : GPathB) (hnz : ∀ h, Visited g₀ h → NoZombie h) :
    ∀ (n : Nat) (h : GPathB), Visited g₀ h → h.isValid = true → AliveDocs h → h.measure ≤ n →
      (readLoop n h).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro h _ _ _ hm
    simp only [readLoop]
    cases hc : hasChoice h
    · rfl
    · exfalso
      unfold hasChoice at hc
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hc
      obtain ⟨q, _, hq, _⟩ := choiceAt_spec hk
      have := measure_pos_of_mem hq
      omega
  | succ n ih =>
    intro h hvis hv hdocs hm
    simp only [readLoop]
    split
    · rfl
    · rename_i k hk
      have hck := List.find?_some hk
      have hkr := intRange_bounds (List.mem_of_find?_eq_some hk)
      obtain ⟨S, hS⟩ := hnz h hvis hv
      -- el pin del nodo de la selección deja el estado válido
      have hpin : (tryPins h k).isSome = true := by
        unfold tryPins
        apply List.findSome?_isSome_iff.mpr
        refine ⟨S k, List.mem_filter.mpr ⟨hS.alive k hkr.1 (by omega), by simp [hS.step k hkr.1 (by omega)]⟩, ?_⟩
        have hc := carried_filterAll hS [(S k).id] (by
          intro r hr
          rw [List.mem_singleton] at hr
          subst hr
          intro _ _
          rw [hS.step k hkr.1 (by omega)])
        simp [isValid_of_carried hc]
      obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp hpin
      rw [hh']
      simp only
      -- lo que se fijó
      unfold tryPins at hh'
      obtain ⟨q, hq, hqf⟩ := List.exists_of_findSome?_eq_some hh'
      have hqk := List.mem_filter.mp hq
      dsimp only at hqf
      split at hqf
      · rename_i hvq
        cases hqf
        refine ih _ (Visited.pin q hvis) hvq (aliveDocs_filterAll hdocs _) ?_
        -- la medida baja: otro vivo del paso es de otro nodo de mapa
        obtain ⟨a, b, ha, hb, has, hbs, hab⟩ := choiceAt_spec hck
        have hqs : q.id.step = k := by simpa using hqk.2
        have hlt : (h.filterRequire q.id).measure < h.measure := by
          by_cases haq : a.id = q.id
          · exact measure_filterRequire_lt hv hdocs hb (by rw [hbs, hqs])
              (fun hbq => hab (haq.trans hbq.symm))
          · exact measure_filterRequire_lt hv hdocs ha (by rw [has, hqs]) haq
        have hrev := (shrinks_review (h.filterRequire q.id)).2
        show (review ([q.id].foldl filterRequire h)).measure ≤ n
        simp only [List.foldl_cons, List.foldl_nil]
        omega
      · exact absurd hqf (by simp)

/-- **La completitud del lector, reducida a `NoZombie`.** Si el estado de partida revisado es válido, todo vivo
tiene documento y ningún estado que el lector visita es un zombi, el lector termina. -/
theorem readG_isSome_of_noZombie (g₀ : GPathB) (hv : (reviewAll g₀).isValid = true) (hdocs : AliveDocs g₀)
    (hnz : ∀ h, Visited g₀ h → NoZombie h) : (readG g₀).isSome = true := by
  unfold readG
  simp only [hv, if_true]
  exact readLoop_isSome g₀ hnz _ _ Visited.start hv (aliveDocs_review (aliveDocs_dirty hdocs _)) (Nat.le_refl _)

end GPathB

end AbsSatBingo.Model
