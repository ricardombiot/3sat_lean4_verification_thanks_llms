-- lean/improves_bingo/AbsSatBingo/Model/ReviewClean.lean
import AbsSatBingo.Model.Shrink
import AbsSatBingo.Model.Carried

/-!
# El review termina cerrado por parejas

**`pairClosed_review`**: si el review entra con algo que revisar (`dirty`) y sale válido y sin `dirty`, el estado
está cerrado por parejas (`PairClosed`: cada arista entre vivos comparte vecino en cada paso). Es lo que Julia da por
construcción con `pair_consistency_after_clean!` hasta su punto fijo.

El argumento:
* `dirty` solo se enciende (`*_dirty` de cada operación de la vuelta): si una vuelta termina sin `dirty`, ninguna de
  sus operaciones lo encendió;
* así, las pasadas de padres e hijos no corrieron, y los enlaces no tocan vivos ni aristas: el estado final tiene los
  vivos y las aristas de la salida de `cleanPair` (`reviewPass_clean`);
* y `cleanPair` sin `dirty` es el caso en el que la regla de parejas no encontró ninguna arista mala
  (`pairOk_of_cleanPair`).

La salida sin `dirty` es la suficiencia del combustible, **demostrada** (`review_exits_clean`, v200 paso 2): cada
operación que enciende `dirty` borra algo que existía (`StrictDirty`), así que `measure + 1` vueltas bastan. Con
ella, `pairClosed_review'`: el review que entra con algo que revisar y sale válido deja el estado cerrado por
parejas, sin hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

-- ============================================================
-- PairClosed
-- ============================================================

/-- **Cerrado por parejas**: cada arista entre dos vivos distintos comparte vecino vivo en cada paso. -/
def PairClosed (h : GPathB) : Prop :=
  ∀ y w, y ≠ w → y ∈ h.alive → w ∈ h.alive → h.Adj y w → h.pairOk y w = true

theorem commonAt_comm (g : GPathB) (x w : PathNodeId) (k : Int) : g.commonAt x w k = g.commonAt w x k := by
  unfold commonAt
  congr 1
  funext z
  cases g.adjb x z <;> cases g.adjb w z <;> simp

theorem pairOk_comm (g : GPathB) (x w : PathNodeId) : g.pairOk x w = g.pairOk w x := by
  unfold pairOk
  have : g.commonAt x w = g.commonAt w x := funext (commonAt_comm g x w)
  rw [this]

/-- Una pareja buena da la reflexiva: `x` tiene vecino en cada paso. -/
theorem pairOk_self_of {g : GPathB} {x w : PathNodeId} (h : g.pairOk x w = true) : g.pairOk x x = true := by
  unfold pairOk at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have hc := h k hk
  unfold commonAt at hc ⊢
  obtain ⟨z, hz, hzc⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true] at hzc
  exact List.any_eq_true.mpr ⟨z, hz, by simp [hzc.1.1, hzc.1.2]⟩

/-- Si todas las aristas pasan la regla, el estado está cerrado por parejas. -/
theorem pairClosed_of_edges {g : GPathB} (h : ∀ e ∈ g.edges, g.pairOk e.1 e.2 = true) : PairClosed g := by
  intro y w hne _ _ ha
  rw [adj_iff] at ha
  rcases ha with ⟨rfl, _⟩ | ⟨e, he, hj⟩
  · exact absurd rfl hne
  · rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact h e he
    · rw [pairOk_comm, ← h1, ← h2]; exact h e he

-- ============================================================
-- dirty solo se enciende
-- ============================================================

/-- `f` no apaga `dirty`. -/
def KeepsDirty (f : GPathB → GPathB) : Prop := ∀ g, g.dirty = true → (f g).dirty = true

theorem keepsDirty_foldl {α : Type} (f : GPathB → α → GPathB) (hf : ∀ a, KeepsDirty (fun g => f g a)) :
    ∀ (l : List α), KeepsDirty (fun g => l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons a as ih => intro g h; exact ih _ (hf a g h)

theorem keepsDirty_removeEdge (x w : PathNodeId) : KeepsDirty (fun g => g.removeEdge x w) := fun _ h => h
theorem keepsDirty_killVertex (id : PathNodeId) : KeepsDirty (fun g => g.killVertex id) := fun _ h => h
theorem keepsDirty_removeNode (id : PathNodeId) : KeepsDirty (fun g => g.removeNode id) := fun _ h => h

theorem keepsDirty_purgeStep (id : PathNodeId) : KeepsDirty (fun g => g.purgeStep id) := by
  intro g h
  simp only [purgeStep]
  split
  · exact h
  · split
    · exact h
    · rfl

theorem keepsDirty_purgeRound : KeepsDirty purgeRound := by
  intro g h
  exact keepsDirty_foldl purgeStep keepsDirty_purgeStep _ g h

theorem keepsDirty_purgeFuel : ∀ (n : Nat), KeepsDirty (purgeFuel n) := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [purgeFuel]
    split
    · split
      · exact ih _ (keepsDirty_purgeRound g h)
      · exact keepsDirty_purgeRound g h
    · exact h

theorem keepsDirty_clean : KeepsDirty clean := fun g h => keepsDirty_purgeFuel _ g h

theorem keepsDirty_pairFuel : ∀ (n : Nat), KeepsDirty (pairFuel n) := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [pairFuel]
    split
    · split
      · exact ih _ (keepsDirty_clean _ rfl)
      · exact h
    · exact h

theorem keepsDirty_pruneLinks : KeepsDirty pruneLinks := by
  intro g h
  unfold pruneLinks
  split
  · simp [h]
  · exact h

theorem keepsDirty_cutStep (sel : PNodeB → List PathNodeId) (n : PNodeB) : KeepsDirty (fun g => cutStep sel g n) := by
  intro g h
  have hc : (cutSupport g n.id (sel n)).1.dirty = true := by
    unfold cutSupport
    exact keepsDirty_foldl (fun h w => h.removeEdge n.id w) (fun w => keepsDirty_removeEdge _ _) _ g h
  unfold cutStep
  by_cases hv : g.isValidNode n = true
  · by_cases hr : (cutSupport g n.id (sel n)).2 = true
    · simp [hv, hr]
    · simp [hv, hr, hc]
  · simp [hv, h]

theorem keepsDirty_reviewNode (sel : PNodeB → List PathNodeId) (id : PathNodeId) :
    KeepsDirty (fun g => reviewNode sel g id) := by
  intro g h
  simp only [reviewNode]
  split
  · exact h
  · split
    · exact keepsDirty_cutStep sel _ g h
    · rfl

theorem keepsDirty_reviewLine (sel : PNodeB → List PathNodeId) (k : Int) :
    KeepsDirty (fun g => reviewLine sel g k) := by
  intro g h
  exact keepsDirty_foldl (reviewNode sel) (keepsDirty_reviewNode sel) _ g h

theorem keepsDirty_reviewSteps (sel : PNodeB → List PathNodeId) :
    ∀ (ks : List Int), KeepsDirty (fun g => reviewSteps sel g ks) := by
  intro ks
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    simp only [reviewSteps]
    have h1 := keepsDirty_reviewLine sel k g h
    split
    · exact ih _ h1
    · exact h1

theorem keepsDirty_reviewParents : KeepsDirty reviewParents := by
  intro g h
  unfold reviewParents
  split
  · exact keepsDirty_reviewSteps _ _ g h
  · exact h

theorem keepsDirty_reviewSons : KeepsDirty reviewSons := by
  intro g h
  unfold reviewSons
  split
  · exact keepsDirty_reviewSteps _ _ g h
  · exact h

-- ============================================================
-- Una vuelta sin dirty
-- ============================================================

theorem reviewParents_of_clean {g : GPathB} (h : g.dirty = false) : g.reviewParents = g := by
  unfold reviewParents; simp [h]

theorem reviewSons_of_clean {g : GPathB} (h : g.dirty = false) : g.reviewSons = g := by
  unfold reviewSons; simp [h]

/-- Los enlaces no tocan el grafo de owners. -/
theorem pruneLinks_graph (g : GPathB) :
    g.pruneLinks.alive = g.alive ∧ g.pruneLinks.edges = g.edges ∧ g.pruneLinks.current_step = g.current_step := by
  unfold pruneLinks
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem not_dirty_of {f : GPathB → GPathB} (hf : KeepsDirty f) {g : GPathB} (h : (f g).dirty = false) :
    g.dirty = false := by
  cases hg : g.dirty
  · rfl
  · rw [hf g hg] at h; cases h

/-- **Una vuelta que termina sin `dirty`** deja los vivos, las aristas y los pasos de su `cleanPair`, y ese
`cleanPair` terminó sin `dirty`. -/
theorem reviewPass_clean {g : GPathB} (h : g.reviewPass.dirty = false) :
    g.cleanPair.dirty = false ∧ g.reviewPass.alive = g.cleanPair.alive ∧
      g.reviewPass.edges = g.cleanPair.edges ∧ g.reviewPass.current_step = g.cleanPair.current_step := by
  unfold reviewPass at h ⊢
  have h3 := not_dirty_of keepsDirty_pruneLinks h
  have h2 := not_dirty_of keepsDirty_reviewSons h3
  have h1 := not_dirty_of keepsDirty_reviewParents h2
  have h0 := not_dirty_of keepsDirty_pruneLinks h1
  rw [reviewParents_of_clean h1, reviewSons_of_clean h1]
  obtain ⟨a1, e1, s1⟩ := pruneLinks_graph g.cleanPair.pruneLinks
  obtain ⟨a0, e0, s0⟩ := pruneLinks_graph g.cleanPair
  exact ⟨h0, a1.trans a0, e1.trans e0, s1.trans s0⟩

theorem cleanPair_eq (g : GPathB) : g.cleanPair = pairFuel (g.clean.measure + 1) g.clean := rfl

/-- `pairFuel` que sale válido y sin `dirty` no quitó nada: devuelve su entrada y la vuelta no halló aristas malas. -/
theorem pairFuel_clean (n : Nat) (g₀ : GPathB) (hd : (pairFuel (n + 1) g₀).dirty = false)
    (hv : (pairFuel (n + 1) g₀).isValid = true) : pairFuel (n + 1) g₀ = g₀ ∧ g₀.pairSweep.2 = false := by
  by_cases hv₀ : g₀.isValid = true
  · by_cases hb : g₀.pairSweep.2 = true
    · have he : pairFuel (n + 1) g₀ = pairFuel n (clean { g₀.pairSweep.1 with dirty := true }) := by
        simp [pairFuel, hv₀, hb]
      rw [he, keepsDirty_pairFuel _ _ (keepsDirty_clean _ rfl)] at hd
      cases hd
    · have he : pairFuel (n + 1) g₀ = g₀ := by simp [pairFuel, hv₀, hb]
      exact ⟨he, by simpa using hb⟩
  · have he : pairFuel (n + 1) g₀ = g₀ := by simp [pairFuel, hv₀]
    rw [he] at hv
    exact absurd hv hv₀

theorem pairOk_of_sweep {g₀ : GPathB} (hb : g₀.pairSweep.2 = false) :
    ∀ e ∈ g₀.edges, g₀.pairOk e.1 e.2 = true := by
  intro e he
  simp only [pairSweep, Bool.not_eq_false', List.isEmpty_iff, List.filter_eq_nil_iff] at hb
  simpa using hb e he

/-- **`cleanPair` sin `dirty` y válido**: la regla de parejas no encontró ninguna arista mala. -/
theorem pairOk_of_cleanPair {g : GPathB} (hd : g.cleanPair.dirty = false) (hv : g.cleanPair.isValid = true) :
    ∀ e ∈ g.cleanPair.edges, g.cleanPair.pairOk e.1 e.2 = true := by
  rw [cleanPair_eq] at hd hv ⊢
  obtain ⟨he, hb⟩ := pairFuel_clean _ _ hd hv
  rw [he]
  exact pairOk_of_sweep hb

theorem isValid_congr {g h : GPathB} (ha : h.alive = g.alive) (hs : h.current_step = g.current_step) :
    h.isValid = g.isValid := by
  unfold isValid; rw [ha, hs]

theorem pairClosed_congr {g h : GPathB} (ha : h.alive = g.alive) (he : h.edges = g.edges)
    (hs : h.current_step = g.current_step) (hg : PairClosed g) : PairClosed h := by
  have hadj : ∀ x w, h.adjb x w = g.adjb x w := by
    intro x w; unfold adjb isAlive hasEdge; rw [ha, he]
  have hpair : ∀ x w, h.pairOk x w = g.pairOk x w := by
    intro x w
    unfold pairOk commonAt
    rw [hs, ha]
    simp only [hadj]
  intro y w hne hy hw hyw
  rw [hpair]
  have hyw' : g.Adj y w := by unfold Adj; rw [← hadj]; exact hyw
  exact hg y w hne (ha ▸ hy) (ha ▸ hw) hyw'

/-- Una vuelta que termina válida y sin `dirty` deja el estado cerrado por parejas. -/
theorem pairClosed_reviewPass {g : GPathB} (hd : g.reviewPass.dirty = false) (hv : g.reviewPass.isValid = true) :
    PairClosed g.reviewPass := by
  obtain ⟨hc, ha, he, hs⟩ := reviewPass_clean hd
  have hvc : g.cleanPair.isValid = true := by rw [← isValid_congr ha hs]; exact hv
  exact pairClosed_congr ha he hs (pairClosed_of_edges (pairOk_of_cleanPair hc hvc))

-- ============================================================
-- El review
-- ============================================================

theorem reviewFuel_of_clean {g : GPathB} (h : g.dirty = false) : ∀ n, reviewFuel n g = g := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [reviewFuel, h]

theorem pairClosed_reviewFuel :
    ∀ (n : Nat) (g : GPathB), g.dirty = true → (reviewFuel n g).isValid = true → (reviewFuel n g).dirty = false →
      PairClosed (reviewFuel n g) := by
  intro n
  induction n with
  | zero => intro g hd _ hc; simp only [reviewFuel] at hc; rw [hd] at hc; cases hc
  | succ n ih =>
    intro g hd hv hc
    simp only [reviewFuel] at hv hc ⊢
    split at hv
    · rename_i hvd
      simp only [hvd, if_true] at hc ⊢
      cases hp : (reviewPass { g with dirty := false }).dirty
      · rw [reviewFuel_of_clean hp] at hv hc ⊢
        exact pairClosed_reviewPass hp hv
      · exact ih _ hp hv hc
    · rename_i hvd
      simp [hv, hd] at hvd

/-- **El review deja el estado cerrado por parejas**, si entra con algo que revisar y sale válido y sin `dirty`. -/
theorem pairClosed_review {g : GPathB} (hd : g.dirty = true) (hv : g.review.isValid = true)
    (hc : g.review.dirty = false) : PairClosed g.review :=
  pairClosed_reviewFuel _ g hd hv hc

-- ============================================================
-- El combustible basta: encender dirty baja la medida
-- ============================================================

/-- Si `f` enciende `dirty` (entra apagado y sale encendido), la medida baja estrictamente. -/
def StrictDirty (f : GPathB → GPathB) : Prop :=
  ∀ g, g.dirty = false → (f g).dirty = true → (f g).measure < g.measure

theorem strictDirty_comp {f₁ f₂ : GPathB → GPathB} (h₁ : StrictDirty f₁) (h₂ : StrictDirty f₂)
    (s₁ : ∀ g, (f₁ g).measure ≤ g.measure) (s₂ : ∀ g, (f₂ g).measure ≤ g.measure) :
    StrictDirty (fun g => f₂ (f₁ g)) := by
  intro g hg hd
  cases hf : (f₁ g).dirty
  · exact Nat.lt_of_lt_of_le (h₂ _ hf hd) (s₁ g)
  · exact Nat.lt_of_le_of_lt (s₂ _) (h₁ g hg hf)

theorem measure_foldl_le {α : Type} (f : GPathB → α → GPathB) (s : ∀ g a, (f g a).measure ≤ g.measure) :
    ∀ (l : List α) (g : GPathB), (l.foldl f g).measure ≤ g.measure := by
  intro l
  induction l with
  | nil => intro g; exact Nat.le_refl _
  | cons a as ih => intro g; exact Nat.le_trans (ih _) (s g a)

theorem strictDirty_foldl {α : Type} (f : GPathB → α → GPathB) (h : ∀ a, StrictDirty (fun g => f g a))
    (s : ∀ g a, (f g a).measure ≤ g.measure) : ∀ (l : List α), StrictDirty (fun g => l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g hg hd; simp only [List.foldl_nil] at hd; rw [hg] at hd; cases hd
  | cons a as ih =>
    exact strictDirty_comp (h a) ih (fun g => s g a) (fun g => measure_foldl_le f s as g)

theorem dirty_foldl_removeEdge (x : PathNodeId) :
    ∀ (l : List PathNodeId) (g : GPathB), (l.foldl (fun h w => h.removeEdge x w) g).dirty = g.dirty ∧
      (l.foldl (fun h w => h.removeEdge x w) g).nodes = g.nodes := by
  intro l
  induction l with
  | nil => intro g; exact ⟨rfl, rfl⟩
  | cons a as ih => intro g; exact ih _

theorem measure_foldl_removeEdge_le (x : PathNodeId) (l : List PathNodeId) (g : GPathB) :
    (l.foldl (fun h w => h.removeEdge x w) g).measure ≤ g.measure :=
  measure_foldl_le _ (fun g w => measure_removeEdge_le g x w) l g

theorem strictDirty_purgeStep (id : PathNodeId) : StrictDirty (fun g => g.purgeStep id) := by
  intro g hg hd
  simp only [purgeStep] at hd ⊢
  split at hd
  · rw [hg] at hd; cases hd
  · rename_i n hn
    split at hd
    · rw [hg] at hd; cases hd
    · rename_i hval
      simp only [hval]
      exact measure_removeNode_lt g id ⟨n, node?_mem hn, node?_id hn⟩

theorem strictDirty_purgeRound : StrictDirty purgeRound := by
  intro g hg hd
  exact strictDirty_foldl purgeStep strictDirty_purgeStep (fun g id => (shrinks_purgeStep g id).2) _ g hg hd

theorem strictDirty_purgeFuel : ∀ (n : Nat), StrictDirty (purgeFuel n) := by
  intro n
  induction n with
  | zero => intro g hg hd; simp only [purgeFuel] at hd; rw [hg] at hd; cases hd
  | succ n ih =>
    intro g hg hd
    simp only [purgeFuel] at hd ⊢
    split at hd
    · rename_i hv
      simp only [hv, if_true] at ⊢
      split at hd
      · rename_i hlt
        simp only [hlt, if_true]
        exact strictDirty_comp strictDirty_purgeRound ih (fun g => (shrinks_purgeRound g).2)
          (fun g => (shrinks_purgeFuel n g).2) g hg hd
      · rename_i hlt
        simp only [hlt]
        exact strictDirty_purgeRound g hg hd
    · rw [hg] at hd; cases hd

theorem strictDirty_clean : StrictDirty clean := by
  intro g hg hd; exact strictDirty_purgeFuel _ g hg hd

/-- Quitar una lista no vacía de aristas que existen baja la medida. -/
theorem measure_pairSweep_lt {g : GPathB} (hb : g.pairSweep.2 = true) : g.pairSweep.1.measure < g.measure := by
  simp only [pairSweep] at hb ⊢
  generalize hbad : g.edges.filter (fun e => !g.pairOk e.1 e.2) = bad at hb ⊢
  cases bad with
  | nil => simp at hb
  | cons e rest =>
    have hmem : e ∈ g.edges.filter (fun e => !g.pairOk e.1 e.2) := by rw [hbad]; exact List.mem_cons_self
    have he : e ∈ g.edges := (List.mem_filter.mp hmem).1
    have hj : g.hasEdge e.1 e.2 = true := List.any_eq_true.mpr ⟨e, he, by simp [joins]⟩
    simp only [List.foldl_cons]
    have h1 := measure_foldl_le (fun (h : GPathB) (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2)
      (fun g e => measure_removeEdge_le g e.1 e.2) rest (g.removeEdge e.1 e.2)
    exact Nat.lt_of_le_of_lt h1 (measure_removeEdge_lt g e.1 e.2 hj)

theorem strictDirty_pairFuel : ∀ (n : Nat), StrictDirty (pairFuel n) := by
  intro n
  induction n with
  | zero => intro g hg hd; simp only [pairFuel] at hd; rw [hg] at hd; cases hd
  | succ n ih =>
    intro g hg hd
    by_cases hv : g.isValid = true
    · by_cases hb : g.pairSweep.2 = true
      · have he : pairFuel (n + 1) g = pairFuel n (clean { g.pairSweep.1 with dirty := true }) := by
          simp [pairFuel, hv, hb]
        rw [he]
        have h1 := (shrinks_pairFuel n (clean { g.pairSweep.1 with dirty := true })).2
        have h2 := (shrinks_clean { g.pairSweep.1 with dirty := true }).2
        have h3 := measure_pairSweep_lt hb
        exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_le_of_lt h2 h3)
      · have he : pairFuel (n + 1) g = g := by simp [pairFuel, hv, hb]
        rw [he, hg] at hd; cases hd
    · have he : pairFuel (n + 1) g = g := by simp [pairFuel, hv]
      rw [he, hg] at hd; cases hd

theorem strictDirty_cleanPair : StrictDirty cleanPair := by
  intro g hg hd
  rw [cleanPair_eq] at hd ⊢
  cases hc : g.clean.dirty
  · exact Nat.lt_of_lt_of_le (strictDirty_pairFuel _ _ hc hd) (shrinks_clean g).2
  · exact Nat.lt_of_le_of_lt (shrinks_pairFuel _ _).2 (strictDirty_clean g hg hc)

theorem strictDirty_pruneLinks : StrictDirty pruneLinks := by
  intro g hg hd
  unfold pruneLinks at hd ⊢
  split at hd
  · rename_i hv
    simp only [hv, if_true]
    simp only [hg, Bool.false_or, decide_eq_true_eq] at hd
    unfold measure
    dsimp only
    omega
  · rw [hg] at hd; cases hd

theorem cutStep_nodes (sel : PNodeB → List PathNodeId) (g : GPathB) (n : PNodeB) :
    (cutStep sel g n).nodes = g.nodes := by
  have hn : (cutSupport g n.id (sel n)).1.nodes = g.nodes := by
    unfold cutSupport; exact (dirty_foldl_removeEdge _ _ _).2
  by_cases hv : g.isValidNode n = true
  · by_cases hr : (cutSupport g n.id (sel n)).2 = true
    · simp [cutStep, hv, hr, hn]
    · simp [cutStep, hv, hr, hn]
  · simp [cutStep, hv]

theorem strictDirty_cutStep (sel : PNodeB → List PathNodeId) (n : PNodeB) : StrictDirty (fun g => cutStep sel g n) := by
  intro g hg hd
  change (cutStep sel g n).dirty = true at hd
  show (cutStep sel g n).measure < g.measure
  by_cases hv : g.isValidNode n = true
  · by_cases hr : (cutSupport g n.id (sel n)).2 = true
    · have heq : cutStep sel g n = { (cutSupport g n.id (sel n)).1 with dirty := true } := by
        simp [cutStep, hv, hr]
      rw [heq]
      show (cutSupport g n.id (sel n)).1.measure < g.measure
      unfold cutSupport at hr ⊢
      dsimp only at hr ⊢
      generalize hdrop : g.alive.filter
        (fun w => w != n.id && g.adjb n.id w && !(sel n).any (fun p => g.adjb p w)) = drop at hr ⊢
      cases drop with
      | nil => simp at hr
      | cons w rest =>
        have hw : w ∈ g.alive.filter
            (fun w => w != n.id && g.adjb n.id w && !(sel n).any (fun p => g.adjb p w)) := by
          rw [hdrop]; exact List.mem_cons_self
        have hwc := (List.mem_filter.mp hw).2
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hwc
        obtain ⟨⟨hne, hadj⟩, _⟩ := hwc
        have he : g.hasEdge n.id w = true := by
          unfold adjb at hadj
          have : (n.id == w) = false := beq_false_of_ne (Ne.symm hne)
          simpa [this] using hadj
        simp only [List.foldl_cons]
        exact Nat.lt_of_le_of_lt (measure_foldl_removeEdge_le n.id rest _) (measure_removeEdge_lt g n.id w he)
    · have heq : cutStep sel g n = (cutSupport g n.id (sel n)).1 := by simp [cutStep, hv, hr]
      rw [heq] at hd
      unfold cutSupport at hd
      rw [(dirty_foldl_removeEdge _ _ _).1, hg] at hd; cases hd
  · have heq : cutStep sel g n = g := by simp [cutStep, hv]
    rw [heq, hg] at hd; cases hd

theorem strictDirty_reviewNode (sel : PNodeB → List PathNodeId) (id : PathNodeId) :
    StrictDirty (fun g => reviewNode sel g id) := by
  intro g hg hd
  simp only [reviewNode] at hd ⊢
  split at hd
  · rw [hg] at hd; cases hd
  · rename_i n hn
    split at hd
    · rename_i hval
      simp only [hval, if_true]
      exact strictDirty_cutStep sel n g hg hd
    · rename_i hval
      simp only [hval]
      have hex : ∃ m ∈ (cutStep sel g n).nodes, m.id = id := by
        rw [cutStep_nodes]; exact ⟨n, node?_mem hn, node?_id hn⟩
      exact Nat.lt_of_lt_of_le (measure_removeNode_lt _ id hex) (shrinks_cutStep sel g n).2

theorem strictDirty_reviewLine (sel : PNodeB → List PathNodeId) (k : Int) :
    StrictDirty (fun g => reviewLine sel g k) := by
  intro g hg hd
  exact strictDirty_foldl (reviewNode sel) (strictDirty_reviewNode sel)
    (fun g id => (shrinks_reviewNode sel g id).2) _ g hg hd

theorem strictDirty_reviewParents : StrictDirty reviewParents := by
  intro g hg hd
  rw [reviewParents_of_clean hg, hg] at hd; cases hd

theorem strictDirty_reviewSons : StrictDirty reviewSons := by
  intro g hg hd
  rw [reviewSons_of_clean hg, hg] at hd; cases hd

theorem strictDirty_reviewPass : StrictDirty reviewPass := by
  have c1 := strictDirty_comp strictDirty_cleanPair strictDirty_pruneLinks (fun g => (shrinks_cleanPair g).2)
    (fun g => (shrinks_pruneLinks g).2)
  have c2 := strictDirty_comp c1 strictDirty_reviewParents
    (fun g => Nat.le_trans (shrinks_pruneLinks _).2 (shrinks_cleanPair g).2) (fun g => (shrinks_reviewParents g).2)
  have c3 := strictDirty_comp c2 strictDirty_reviewSons
    (fun g => Nat.le_trans (shrinks_reviewParents _).2 (Nat.le_trans (shrinks_pruneLinks _).2 (shrinks_cleanPair g).2))
    (fun g => (shrinks_reviewSons g).2)
  have c4 := strictDirty_comp c3 strictDirty_pruneLinks
    (fun g => Nat.le_trans (shrinks_reviewSons _).2 (Nat.le_trans (shrinks_reviewParents _).2
      (Nat.le_trans (shrinks_pruneLinks _).2 (shrinks_cleanPair g).2))) (fun g => (shrinks_pruneLinks g).2)
  exact c4

/-- Con más combustible que la medida, el review que sale válido sale sin `dirty`. -/
theorem reviewFuel_exits_clean :
    ∀ (n : Nat) (g : GPathB), g.measure < n → (reviewFuel n g).isValid = true → (reviewFuel n g).dirty = false := by
  intro n
  induction n with
  | zero => intro g hm; omega
  | succ n ih =>
    intro g hm hv
    simp only [reviewFuel] at hv ⊢
    split at hv
    · rename_i hvd
      simp only [hvd, if_true]
      cases hp : (reviewPass { g with dirty := false }).dirty
      · rw [reviewFuel_of_clean hp]; exact hp
      · have hlt := strictDirty_reviewPass { g with dirty := false } rfl hp
        have hm' : (reviewPass { g with dirty := false }).measure < n := by
          have : ({ g with dirty := false } : GPathB).measure = g.measure := rfl
          omega
        exact ih _ hm' hv
    · rename_i hvd
      simp only [hvd]
      simp only [hv, Bool.true_and, Bool.not_eq_true] at hvd
      exact hvd

/-- **El review que sale válido sale sin `dirty`** (antes `ReviewExitsClean`, abierto): `measure + 1` vueltas
bastan, porque cada vuelta que enciende `dirty` borra algo. -/
theorem review_exits_clean (g : GPathB) (hv : g.review.isValid = true) : g.review.dirty = false :=
  reviewFuel_exits_clean _ g (Nat.lt_succ_self _) hv

/-- **El review deja el estado cerrado por parejas**, si entra con algo que revisar y sale válido. -/
theorem pairClosed_review' {g : GPathB} (hd : g.dirty = true) (hv : g.review.isValid = true) :
    PairClosed g.review :=
  pairClosed_review hd hv (review_exits_clean g hv)

end GPathB

end AbsSatBingo.Model
