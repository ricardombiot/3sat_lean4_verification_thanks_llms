-- lean/improves_bingo/AbsSatBingo/Model/Keeps.lean
import AbsSatBingo.Model.Carried

/-!
# El review conserva las camarillas llevadas (fase L6, parte 2)

Cada regla del review conserva `Carried`, y con ellas el review entero (`carried_review`) y el filtro por
requisitos que **concuerdan** con la selección (`carried_filterAll`). Por qué, regla a regla:

* **purga**: un nodo de la selección es válido (`isValidNode_of_carried`), así que la purga no lo toca;
* **parejas**: dos nodos de la selección comparten, en cada paso, el nodo de la selección de ese paso;
* **enlaces**: los enlaces de la selección unen nodos que se poseen;
* **pasadas**: el padre (o el hijo) de la selección de un nodo de la selección posee a todos los demás;
* **filtro**: solo mata nodos de otro nodo de mapa en el paso del requisito.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

variable {S : Int → PathNodeId}

-- ============================================================
-- El paso actual no cambia
-- ============================================================

theorem step_of_shrinks {h g : GPathB} (hs : Shrinks h g) : h.current_step = g.current_step := hs.1.step

-- ============================================================
-- Filtro por requisito
-- ============================================================

/-- El requisito `req` concuerda con la selección: en su paso, la selección está en `req`. -/
def Agrees (cs : Int) (S : Int → PathNodeId) (req : NodeId) : Prop :=
  0 ≤ req.step → req.step < cs → (S req.step).id = req

theorem carried_filterRequire {g : GPathB} (h : Carried g S) {req : NodeId} (ha : Agrees g.current_step S req) :
    Carried (g.filterRequire req) S := by
  unfold filterRequire
  split
  · dsimp only
    apply carried_dirty
    refine (carried_foldl (cs := g.current_step) killVertex _ ?_ g h rfl).1
    intro g' q hq hc hcs
    refine ⟨carried_killVertex hc ?_, hcs⟩
    rw [hcs]
    rintro ⟨k, hk0, hk1, rfl⟩
    obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
    obtain ⟨n, hn, hnid⟩ := List.mem_map.mp hq1
    have hstep := (List.mem_filter.mp hn).2
    rw [hnid] at hstep
    have hk : k = req.step := by rw [← h.step k hk0 hk1]; simpa using hstep
    subst hk
    have := ha hk0 hk1
    simp [this] at hq2
  · exact h

-- ============================================================
-- La purga
-- ============================================================

theorem carried_purgeStep {g : GPathB} (h : Carried g S) (id : PathNodeId) : Carried (g.purgeStep id) S := by
  unfold purgeStep
  split
  · exact h
  · rename_i n hn
    split
    · exact h
    · rename_i hv
      exact carried_dirty (carried_removeNode h (not_onS_of_invalid h hn (by simpa using hv))) _

theorem carried_purgeRound {g : GPathB} (h : Carried g S) : Carried g.purgeRound S :=
  (carried_foldl (cs := g.current_step) purgeStep _
    (fun g' a _ hc hcs => ⟨carried_purgeStep hc a, (step_of_shrinks (shrinks_purgeStep g' a)).trans hcs⟩)
    g h rfl).1

theorem carried_purgeFuel : ∀ (n : Nat) (g : GPathB), Carried g S → Carried (purgeFuel n g) S := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [purgeFuel]
    split
    · split
      · exact ih _ (carried_purgeRound h)
      · exact carried_purgeRound h
    · exact h

theorem carried_clean {g : GPathB} (h : Carried g S) : Carried g.clean S := carried_purgeFuel _ _ h

-- ============================================================
-- Parejas
-- ============================================================

/-- Dos nodos de la selección cumplen la regla de parejas. -/
theorem pairOk_of_onS {g : GPathB} (h : Carried g S) {x w : PathNodeId}
    (hx : OnS g.current_step S x) (hw : OnS g.current_step S w) : g.pairOk x w = true := by
  unfold pairOk
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨h0, h1⟩ := intRange_bounds hk
  have hsk : OnS g.current_step S (S k) := ⟨k, h0, by omega, rfl⟩
  unfold commonAt
  refine List.any_eq_true.mpr ⟨S k, h.alive k h0 (by omega), ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨by simp [h.step k h0 (by omega)], h.adj_on hx hsk⟩, h.adj_on hw hsk⟩

theorem carried_pairSweep {g : GPathB} (h : Carried g S) : Carried g.pairSweep.1 S := by
  unfold pairSweep
  dsimp only
  refine (carried_foldl (cs := g.current_step) (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) _
    ?_ g h rfl).1
  intro g' e he hc hcs
  refine ⟨carried_removeEdge hc ?_, hcs⟩
  rw [hcs]
  rintro ⟨hx, hw⟩
  have := (List.mem_filter.mp he).2
  rw [pairOk_of_onS h hx hw] at this
  exact Bool.noConfusion this

theorem carried_pairFuel : ∀ (n : Nat) (g : GPathB), Carried g S → Carried (pairFuel n g) S := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [pairFuel]
    split
    · split
      · exact ih _ (carried_clean (carried_dirty (carried_pairSweep h) _))
      · exact h
    · exact h

theorem carried_cleanPair {g : GPathB} (h : Carried g S) : Carried g.cleanPair S :=
  carried_pairFuel _ _ (carried_clean h)

-- ============================================================
-- Enlaces caducados
-- ============================================================

theorem carried_pruneLinks {g : GPathB} (h : Carried g S) : Carried g.pruneLinks S := by
  unfold pruneLinks
  split
  · refine ⟨h.step, h.alive, h.adj, h.root, ?_⟩
    intro k hk0 (hk1 : k < g.current_step)
    obtain ⟨n, hn, hp, hs⟩ := h.node k hk0 hk1
    have hid := node?_id hn
    let f : PNodeB → PNodeB := fun n =>
      { n with parents := n.parents.filter (g.linkOk n.id), sons := n.sons.filter (g.linkOk n.id) }
    refine ⟨f n, ?_, ?_, ?_⟩
    · show List.find? _ (g.nodes.map f) = _
      rw [find?_map_id f (fun _ => rfl)]
      show (g.node? (S k)).map f = _
      rw [hn]; rfl
    · intro hk
      refine List.mem_filter.mpr ⟨hp hk, ?_⟩
      obtain ⟨m, hm, _, _⟩ := h.node (k - 1) (by omega) (by omega)
      unfold linkOk
      rw [hm, hid]
      simp only [Option.isSome_some, Bool.true_and]
      exact h.adj k (k - 1) hk0 hk1 (by omega) (by omega)
    · intro hk
      refine List.mem_filter.mpr ⟨hs hk, ?_⟩
      obtain ⟨m, hm, _, _⟩ := h.node (k + 1) (by omega) hk
      unfold linkOk
      rw [hm, hid]
      simp only [Option.isSome_some, Bool.true_and]
      exact h.adj k (k + 1) hk0 hk1 (by omega) hk
  · exact h

-- ============================================================
-- Las pasadas
-- ============================================================

theorem nodes_foldl_removeEdge (x : PathNodeId) :
    ∀ (l : List PathNodeId) (g : GPathB), (l.foldl (fun h w => h.removeEdge x w) g).nodes = g.nodes := by
  intro l
  induction l with
  | nil => intro g; rfl
  | cons a as ih => intro g; exact ih _

theorem nodes_cutStep (sel : PNodeB → List PathNodeId) (g : GPathB) (n : PNodeB) :
    (cutStep sel g n).nodes = g.nodes := by
  unfold cutStep cutSupport
  split
  · dsimp only
    split
    · exact nodes_foldl_removeEdge _ _ _
    · exact nodes_foldl_removeEdge _ _ _
  · rfl

/-- El corte de un nodo cuyo selector contiene un nodo de la selección (si él es de la selección). -/
theorem carried_cutStep {g : GPathB} (h : Carried g S) (sel : PNodeB → List PathNodeId) (n : PNodeB)
    (hsel : OnS g.current_step S n.id → ∃ p ∈ sel n, OnS g.current_step S p) :
    Carried (cutStep sel g n) S := by
  unfold cutStep cutSupport
  split
  · dsimp only
    have hfold := (carried_foldl (cs := g.current_step) (fun h w => h.removeEdge n.id w)
      (g.alive.filter (fun w => w != n.id && g.adjb n.id w && !(sel n).any (fun p => g.adjb p w)))
      (fun g' w hw hc hcs => by
        refine ⟨carried_removeEdge hc ?_, hcs⟩
        rw [hcs]
        rintro ⟨hx, hw'⟩
        obtain ⟨p, hp, hpS⟩ := hsel hx
        have := (List.mem_filter.mp hw).2
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at this
        exact absurd (h.adj_on hpS hw') (by simpa [Adj] using this.2 p hp))
      g h rfl).1
    split
    · exact carried_dirty hfold _
    · exact hfold
  · exact h

theorem carried_reviewNode {g : GPathB} (h : Carried g S) (sel : PNodeB → List PathNodeId) (id : PathNodeId)
    (hsel : ∀ n, g.node? id = some n → OnS g.current_step S id → ∃ p ∈ sel n, OnS g.current_step S p) :
    Carried (reviewNode sel g id) S := by
  unfold reviewNode
  split
  · exact h
  · rename_i n hn
    have hid := node?_id hn
    have hc : Carried (cutStep sel g n) S := carried_cutStep h sel n (by rw [hid]; exact hsel n hn)
    have hstep : (cutStep sel g n).current_step = g.current_step :=
      step_of_shrinks (shrinks_cutStep sel g n)
    show Carried (if (cutStep sel g n).isValidNode n then cutStep sel g n
      else { (cutStep sel g n).removeNode id with dirty := true }) S
    split
    · exact hc
    · rename_i hv
      have hn' : (cutStep sel g n).node? id = some n := by
        show List.find? _ (cutStep sel g n).nodes = _
        rw [nodes_cutStep]; exact hn
      exact carried_dirty (carried_removeNode hc (not_onS_of_invalid hc hn' (by simpa using hv))) _

/-- Lo que una pasada pide a su selector en el paso `k`. -/
def SelOk (S : Int → PathNodeId) (sel : PNodeB → List PathNodeId) (k : Int) : Prop :=
  ∀ g : GPathB, Carried g S → ∀ id n, id.id.step = k → g.node? id = some n →
    OnS g.current_step S id → ∃ p ∈ sel n, OnS g.current_step S p

theorem carried_reviewLine {g : GPathB} (h : Carried g S) (sel : PNodeB → List PathNodeId) (k : Int)
    (hsel : SelOk S sel k) : Carried (reviewLine sel g k) S := by
  unfold reviewLine
  refine (carried_foldl (cs := g.current_step) (reviewNode sel) _ ?_ g h rfl).1
  intro g' id hid hc hcs
  refine ⟨carried_reviewNode hc sel id ?_, (step_of_shrinks (shrinks_reviewNode sel g' id)).trans hcs⟩
  intro n hn hon
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hid
  have hstep := (List.mem_filter.mp hm).2
  exact hsel g' hc m.id n (by simpa using hstep) hn hon

theorem carried_reviewSteps (sel : PNodeB → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathB), Carried g S → (∀ k ∈ ks, SelOk S sel k) →
      Carried (reviewSteps sel g ks) S := by
  intro ks
  induction ks with
  | nil => intro g h _; exact h
  | cons k ks ih =>
    intro g h hsel
    simp only [reviewSteps]
    have h1 := carried_reviewLine h sel k (hsel k (List.mem_cons_self ..))
    split
    · exact ih _ h1 (fun k' hk' => hsel k' (List.mem_cons_of_mem _ hk'))
    · exact h1

/-- En la pasada de padres (pasos `≥ 1`), el padre de la selección está entre los padres. -/
theorem selOk_parents (k : Int) (hk : 1 ≤ k) : SelOk S (·.parents) k := by
  intro g h id n hid hn hon
  obtain ⟨j, hj0, hj1, rfl⟩ := hon
  have hj : j = k := by rw [← hid, h.step j hj0 hj1]
  subst hj
  obtain ⟨n', hn', hp, _⟩ := h.node j hj0 hj1
  rw [hn] at hn'; cases hn'
  exact ⟨S (j - 1), hp (by omega), ⟨j - 1, by omega, by omega, rfl⟩⟩

/-- En la pasada de hijos (pasos `≤ current_step - 2`), el hijo de la selección está entre los hijos. -/
theorem selOk_sons (cs k : Int) (hk : k + 1 < cs) : ∀ {g : GPathB}, g.current_step = cs →
    ∀ id n, id.id.step = k → g.node? id = some n → Carried g S →
      OnS g.current_step S id → ∃ p ∈ n.sons, OnS g.current_step S p := by
  intro g hcs id n hid hn h hon
  obtain ⟨j, hj0, hj1, rfl⟩ := hon
  have hj : j = k := by rw [← hid, h.step j hj0 hj1]
  subst hj
  obtain ⟨n', hn', _, hs⟩ := h.node j hj0 hj1
  rw [hn] at hn'; cases hn'
  exact ⟨S (j + 1), hs (by omega), ⟨j + 1, by omega, by omega, rfl⟩⟩

theorem carried_reviewParents {g : GPathB} (h : Carried g S) : Carried g.reviewParents S := by
  unfold reviewParents
  split
  · exact carried_reviewSteps _ _ g h (fun k hk => selOk_parents k (intRange_bounds hk).1)
  · exact h

/-- La pasada de hijos, sobre gpaths con el mismo paso actual (los pasos se fijan al empezar). -/
theorem carried_reviewSteps_sons (cs : Int) :
    ∀ (ks : List Int) (g : GPathB), Carried g S → g.current_step = cs → (∀ k ∈ ks, k + 1 < cs) →
      Carried (reviewSteps (·.sons) g ks) S := by
  intro ks
  induction ks with
  | nil => intro g h _ _; exact h
  | cons k ks ih =>
    intro g h hcs hks
    simp only [reviewSteps]
    have hk := hks k (List.mem_cons_self ..)
    have h1 : Carried (reviewLine (·.sons) g k) S := by
      unfold reviewLine
      refine (carried_foldl (cs := cs) (reviewNode (·.sons)) _ ?_ g h hcs).1
      intro g' id hid hc hcs'
      refine ⟨carried_reviewNode hc _ id ?_, (step_of_shrinks (shrinks_reviewNode _ g' id)).trans hcs'⟩
      intro n hn hon
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hid
      have hstep := (List.mem_filter.mp hm).2
      exact selOk_sons cs k hk hcs' m.id n (by simpa using hstep) hn hc hon
    have hcs1 : (reviewLine (·.sons) g k).current_step = cs :=
      (step_of_shrinks (shrinks_reviewLine _ g k)).trans hcs
    split
    · exact ih _ h1 hcs1 (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
    · exact h1

theorem carried_reviewSons {g : GPathB} (h : Carried g S) : Carried g.reviewSons S := by
  unfold reviewSons
  split
  · refine carried_reviewSteps_sons g.current_step _ g h rfl ?_
    intro k hk
    have := (intRange_bounds (List.mem_reverse.mp hk)).2
    omega
  · exact h

-- ============================================================
-- El review y el filtro
-- ============================================================

theorem carried_reviewPass {g : GPathB} (h : Carried g S) : Carried g.reviewPass S :=
  carried_pruneLinks (carried_reviewSons (carried_reviewParents (carried_pruneLinks (carried_cleanPair h))))

theorem carried_reviewFuel : ∀ (n : Nat) (g : GPathB), Carried g S → Carried (reviewFuel n g) S := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [reviewFuel]
    split
    · exact ih _ (carried_reviewPass (carried_dirty h _))
    · exact h

/-- **El review conserva toda camarilla llevada.** -/
theorem carried_review {g : GPathB} (h : Carried g S) : Carried g.review S := carried_reviewFuel _ _ h

/-- **El filtro por requisitos que concuerdan con la selección, con su review, la conserva.** -/
theorem carried_filterAll {g : GPathB} (h : Carried g S) (reqs : List NodeId)
    (ha : ∀ r ∈ reqs, Agrees g.current_step S r) : Carried (g.filterAll reqs) S := by
  unfold filterAll
  apply carried_review
  refine (carried_foldl (cs := g.current_step) filterRequire reqs ?_ g h rfl).1
  intro g' r hr hc hcs
  refine ⟨carried_filterRequire hc (by rw [hcs]; exact ha r hr), ?_⟩
  exact (step_of_shrinks (shrinks_filterRequire g' r)).trans hcs

end GPathB

end AbsSatBingo.Model
