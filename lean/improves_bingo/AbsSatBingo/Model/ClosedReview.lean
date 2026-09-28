-- lean/improves_bingo/AbsSatBingo/Model/ClosedReview.lean
import AbsSatBingo.Model.KernelJoin

/-!
# El review deja el estado cerrado (`closed`, antes hipótesis)

Con la comprobación final del review (`finalPass`, informe v201 §5), el review solo sale cuando una vuelta completa
con todas las reglas no cambia nada. De ahí, **`closedState_review`**: el estado que deja está cerrado por las
reglas (`ClosedState`):

* **apoyo**: las pasadas forzadas de padres e hijos no cortaron nada, así que cada nodo válido tiene, para cada
  vecino, un padre (y un hijo) que lo posee (`reviewSteps_clean`);
* **documentos válidos**: esas pasadas no eliminaron a nadie;
* **enlaces**: la poda final no cambió nada, así que todo enlace es válido (`pruneLinks_clean`);
* **parejas**: `pairClosed_reviewPass`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

open Machine (Below)

-- ============================================================
-- Una pasada que no cambia nada
-- ============================================================

/-- `n` tiene apoyo en `sel n`: cada vecino vivo suyo lo posee alguien de `sel n`. -/
def Supp (sel : PNodeB → List PathNodeId) (g : GPathB) (n : PNodeB) : Prop :=
  ∀ w ∈ g.alive, w ≠ n.id → g.adjb n.id w = true → ∃ q ∈ sel n, g.adjb q w = true

theorem reviewNode_clean (sel : PNodeB → List PathNodeId) (g : GPathB) (id : PathNodeId)
    (hd : (reviewNode sel g id).dirty = false) :
    reviewNode sel g id = g ∧ ∀ n, g.node? id = some n → g.isValidNode n = true ∧ Supp sel g n := by
  cases hn : g.node? id with
  | none =>
    refine ⟨?_, fun n h => by cases h⟩
    unfold reviewNode; rw [hn]
  | some n =>
    by_cases hv : g.isValidNode n = true
    · by_cases hr : (cutSupport g n.id (sel n)).2 = true
      · exfalso
        have hcut : cutStep sel g n = { (cutSupport g n.id (sel n)).1 with dirty := true } := by
          simp [cutStep, hv, hr]
        have : (reviewNode sel g id).dirty = true := by
          unfold reviewNode; rw [hn]; dsimp only; rw [hcut]; split <;> rfl
        rw [this] at hd; cases hd
      · have hr' : (cutSupport g n.id (sel n)).2 = false := by simpa using hr
        have hempty : g.alive.filter (fun w => w != n.id && g.adjb n.id w && !(sel n).any (fun p => g.adjb p w)) = [] := by
          unfold cutSupport at hr'
          simpa [List.isEmpty_iff] using hr'
        have hcut : cutStep sel g n = g := by
          have h1 : cutStep sel g n = (cutSupport g n.id (sel n)).1 := by simp [cutStep, hv, hr]
          rw [h1]; unfold cutSupport; dsimp only; rw [hempty]; rfl
        refine ⟨?_, fun m hm => ?_⟩
        · unfold reviewNode; rw [hn]; dsimp only; rw [hcut]; simp [hv]
        · cases hm
          refine ⟨hv, fun w hw hne hadj => ?_⟩
          have h1 := List.filter_eq_nil_iff.mp hempty w hw
          have hany : (sel n).any (fun p => g.adjb p w) = true := by
            cases ha : (sel n).any (fun p => g.adjb p w)
            · exfalso
              apply h1
              simp [hne, hadj, ha]
            · rfl
          exact List.any_eq_true.mp hany
    · exfalso
      have hv' : g.isValidNode n = false := by simpa using hv
      have hcut : cutStep sel g n = g := by simp [cutStep, hv']
      have : (reviewNode sel g id).dirty = true := by
        unfold reviewNode; rw [hn]; dsimp only; rw [hcut]; simp [hv']
      rw [this] at hd; cases hd

theorem reviewLine_foldl_clean (sel : PNodeB → List PathNodeId) :
    ∀ (l : List PathNodeId) (g : GPathB), (l.foldl (reviewNode sel) g).dirty = false →
      l.foldl (reviewNode sel) g = g ∧
        ∀ id ∈ l, ∀ n, g.node? id = some n → g.isValidNode n = true ∧ Supp sel g n := by
  intro l
  induction l with
  | nil => intro g _; exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | cons a as ih =>
    intro g hd
    simp only [List.foldl_cons] at hd ⊢
    have h1 : (reviewNode sel g a).dirty = false := by
      cases hr : (reviewNode sel g a).dirty
      · rfl
      · have := keepsDirty_foldl (reviewNode sel) (keepsDirty_reviewNode sel) as _ hr
        rw [this] at hd; cases hd
    obtain ⟨he, hall⟩ := reviewNode_clean sel g a h1
    rw [he] at hd ⊢
    obtain ⟨he', hall'⟩ := ih g hd
    exact ⟨he', fun id hid n hn => by
      rcases List.mem_cons.mp hid with rfl | hid
      · exact hall n hn
      · exact hall' id hid n hn⟩

/-- **Una pasada que no enciende `dirty` no cambia nada**, y todo documento que miró es válido y tiene apoyo. -/
theorem reviewSteps_clean (sel : PNodeB → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathB), g.isValid = true → (reviewSteps sel g ks).dirty = false →
      reviewSteps sel g ks = g ∧
        ∀ k ∈ ks, ∀ m ∈ g.line k, ∀ n, g.node? m.id = some n → g.isValidNode n = true ∧ Supp sel g n := by
  intro ks
  induction ks with
  | nil => intro g _ _; exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | cons k ks ih =>
    intro g hv hd
    have hl : (reviewLine sel g k).dirty = false := by
      cases hr : (reviewLine sel g k).dirty
      · rfl
      · exfalso
        have : (reviewSteps sel g (k :: ks)).dirty = true := by
          simp only [reviewSteps]
          split
          · exact keepsDirty_reviewSteps sel ks _ hr
          · exact hr
        rw [this] at hd; cases hd
    have hfold := reviewLine_foldl_clean sel ((g.line k).map (·.id)) g (by unfold reviewLine at hl; exact hl)
    have he : reviewLine sel g k = g := by unfold reviewLine; exact hfold.1
    have hstep : reviewSteps sel g (k :: ks) = reviewSteps sel g ks := by
      simp only [reviewSteps, he, hv, if_true]
    rw [hstep] at hd ⊢
    obtain ⟨he', hall'⟩ := ih g hv hd
    refine ⟨he', fun k' hk' m hm n hn => ?_⟩
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hfold.2 m.id (List.mem_map.mpr ⟨m, hm, rfl⟩) n hn
    · exact hall' k' hk' m hm n hn

-- ============================================================
-- Los enlaces que la poda no cambia
-- ============================================================

theorem eq_of_le_of_not_lt_sum {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ g a) → ¬ ((l.map f).sum < (l.map g).sum) → ∀ a ∈ l, f a = g a := by
  intro l
  induction l with
  | nil => intro _ _ a h; cases h
  | cons b bs ih =>
    intro hle hnot a ha
    simp only [List.map_cons, List.sum_cons] at hnot
    have hb := hle b (List.mem_cons_self ..)
    have hs := sum_map_le_of_le f g bs (fun x hx => hle x (List.mem_cons_of_mem _ hx))
    rcases List.mem_cons.mp ha with rfl | ha'
    · omega
    · exact ih (fun x hx => hle x (List.mem_cons_of_mem _ hx)) (by omega) a ha'

theorem all_of_filter_length {α : Type} {p : α → Bool} {l : List α} (h : (l.filter p).length = l.length) :
    ∀ x ∈ l, p x = true := by
  intro x hx
  cases hpx : p x
  · exfalso
    have := (List.length_filter_lt_length_iff_exists (p := p) (l := l)).mpr ⟨x, hx, by simp [hpx]⟩
    omega
  · rfl

/-- **Una poda de enlaces que no enciende `dirty`**: todo enlace es válido. -/
theorem pruneLinks_clean {g : GPathB} (hv : g.isValid = true) (hg : g.dirty = false)
    (hd : g.pruneLinks.dirty = false) :
    ∀ n ∈ g.nodes, (∀ q ∈ n.parents, g.linkOk n.id q = true) ∧ (∀ q ∈ n.sons, g.linkOk n.id q = true) := by
  unfold pruneLinks at hd
  rw [if_pos hv] at hd
  dsimp only at hd
  simp only [hg, Bool.false_or, decide_eq_false_iff_not, List.map_map] at hd
  let f : PNodeB → PNodeB := fun n =>
    { n with parents := n.parents.filter (g.linkOk n.id), sons := n.sons.filter (g.linkOk n.id) }
  have hle : ∀ a ∈ g.nodes, (PNodeB.weight ∘ f) a ≤ PNodeB.weight a := by
    intro a _
    simp only [Function.comp, f, PNodeB.weight]
    have := List.length_filter_le (g.linkOk a.id) a.parents
    have := List.length_filter_le (g.linkOk a.id) a.sons
    omega
  have heq := eq_of_le_of_not_lt_sum (PNodeB.weight ∘ f) PNodeB.weight g.nodes hle hd
  intro n hn
  have hw := heq n hn
  simp only [Function.comp, f, PNodeB.weight] at hw
  have h1 := List.length_filter_le (g.linkOk n.id) n.parents
  have h2 := List.length_filter_le (g.linkOk n.id) n.sons
  exact ⟨all_of_filter_length (by omega), all_of_filter_length (by omega)⟩

-- ============================================================
-- La comprobación final que no cambia nada
-- ============================================================

theorem keepsDirty_forcedParents : KeepsDirty forcedParents := by
  intro g h
  unfold forcedParents; split
  · exact keepsDirty_reviewSteps _ _ g h
  · exact h

theorem keepsDirty_forcedSons : KeepsDirty forcedSons := by
  intro g h
  unfold forcedSons; split
  · exact keepsDirty_reviewSteps _ _ g h
  · exact h

/-- **Una comprobación final que no enciende `dirty`**: todo documento de los pasos que mira es válido y tiene
apoyo por padres (pasos `1 … cs-1`) y por hijos (pasos `0 … cs-2`), y todo enlace es válido. -/
theorem finalPass_clean {p : GPathB} (hv : p.isValid = true) (hpd : p.dirty = false)
    (hf : (finalPass p).dirty = false) :
    (∀ k ∈ intRange 1 (p.current_step - 1), ∀ m ∈ p.line k, ∀ n, p.node? m.id = some n →
        p.isValidNode n = true ∧ Supp (·.parents) p n) ∧
    (∀ k ∈ (intRange 0 (p.current_step - 2)).reverse, ∀ m ∈ p.line k, ∀ n, p.node? m.id = some n →
        p.isValidNode n = true ∧ Supp (·.sons) p n) ∧
    (∀ n ∈ p.nodes, (∀ q ∈ n.parents, p.linkOk n.id q = true) ∧ (∀ q ∈ n.sons, p.linkOk n.id q = true)) := by
  unfold finalPass at hf
  have h2 := not_dirty_of keepsDirty_pruneLinks hf
  have h1 := not_dirty_of keepsDirty_forcedSons h2
  have hfp : p.forcedParents = reviewSteps (·.parents) p (intRange 1 (p.current_step - 1)) := by
    unfold forcedParents; rw [if_pos hv]
  have hfs : p.forcedSons = reviewSteps (·.sons) p (intRange 0 (p.current_step - 2)).reverse := by
    unfold forcedSons; rw [if_pos hv]
  rw [hfp] at h1
  obtain ⟨hep, hpar⟩ := reviewSteps_clean _ _ p hv h1
  rw [hfp, hep] at h2
  rw [hfs] at h2
  obtain ⟨hes, hson⟩ := reviewSteps_clean _ _ p hv h2
  rw [hfp, hep, hfs, hes] at hf
  exact ⟨hpar, hson, pruneLinks_clean hv hpd hf⟩

-- ============================================================
-- Validez y enlaces
-- ============================================================

theorem parents_of_valid {g : GPathB} {n : PNodeB} (h : g.isValidNode n = true)
    (hr : n.id.parent_id.isNone = false) : n.parents ≠ [] := by
  unfold isValidNode at h
  simp only [hr, Bool.false_eq_true, if_false] at h
  intro hp
  rw [hp] at h
  split at h <;> simp at h

theorem sons_of_valid {g : GPathB} {n : PNodeB} (h : g.isValidNode n = true)
    (hl : n.id.id.step ≠ g.current_step - 1) : n.sons ≠ [] := by
  unfold isValidNode at h
  have hl' : (n.id.id.step == g.current_step - 1) = false := beq_false_of_ne hl
  simp only [hl', Bool.false_eq_true, if_false] at h
  intro hs
  rw [hs] at h
  split at h <;> simp at h

/-- Todo documento está en un paso `≥ 0`. -/
def AboveZero (g : GPathB) : Prop := ∀ n ∈ g.nodes, 0 ≤ n.id.id.step

-- ============================================================
-- El estado que deja una vuelta limpia con comprobación final limpia está cerrado
-- ============================================================

theorem closedState_of_exit {p : GPathB} (hv : p.isValid = true) (hpd : p.dirty = false)
    (hf : (finalPass p).dirty = false) (hpc : PairClosed p) (hda : DocsAlive p) (had : AliveDocs p)
    (hnd : NodupIds p) (hb : Below p) (hz : AboveZero p) (hcs : 2 ≤ p.current_step) : ClosedState p := by
  obtain ⟨hpar, hson, hlinks⟩ := finalPass_clean hv hpd hf
  -- el documento de un vivo
  have hdoc : ∀ {y}, y ∈ p.alive → ∃ m, p.node? y = some m ∧ m ∈ p.nodes ∧ m.id = y := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := had y hy
    exact ⟨m, node?_of_nodup hnd hm, hm, rfl⟩
  -- lo que da la comprobación final a un documento, según su paso
  have hcheck : ∀ {m}, m ∈ p.nodes →
      (1 ≤ m.id.id.step → p.isValidNode m = true ∧ Supp (·.parents) p m) ∧
      (m.id.id.step + 1 < p.current_step → p.isValidNode m = true ∧ Supp (·.sons) p m) := by
    intro m hm
    have hml : ∀ k, m.id.id.step = k → m ∈ p.line k := fun k hk =>
      List.mem_filter.mpr ⟨hm, by simp [hk]⟩
    have hlt := hb m hm
    have hge := hz m hm
    have hn := node?_of_nodup hnd hm
    refine ⟨fun h1 => hpar _ (mem_intRange h1 (by omega)) m (hml _ rfl) m hn,
      fun h1 => hson _ (List.mem_reverse.mpr (mem_intRange hge (by omega))) m (hml _ rfl) m hn⟩
  have hvalid : ∀ {m}, m ∈ p.nodes → p.isValidNode m = true := by
    intro m hm
    have hlt := hb m hm
    by_cases h1 : 1 ≤ m.id.id.step
    · exact ((hcheck hm).1 h1).1
    · exact ((hcheck hm).2 (by omega)).1
  -- un enlace lleva a un vivo que se posee
  have hlink : ∀ {m q}, m ∈ p.nodes → p.linkOk m.id q = true → q ∈ p.alive ∧ p.adjb m.id q = true := by
    intro m q _ hl
    unfold linkOk at hl
    obtain ⟨hs, ha⟩ := Bool.and_eq_true_iff.mp hl
    obtain ⟨mq, hmq⟩ := Option.isSome_iff_exists.mp hs
    refine ⟨?_, ha⟩
    rw [← node?_id hmq]
    exact hda mq (node?_mem hmq)
  refine ⟨fun hy => hy, fun hy => ⟨hy, hy, adj_refl _ _ hy⟩, fun ⟨hy, hw, ha⟩ => ⟨hw, hy, (adj_symm _ _ _).mp ha⟩,
    fun ⟨hy, hw, _⟩ => ⟨hy, hw⟩, fun ⟨_, _, ha⟩ => ha, ?_, ?_, ?_, ?_⟩
  · -- parejas
    rintro y w ⟨hy, hw, ha⟩ l hl0 hl1
    by_cases hyw : y = w
    · subst hyw
      obtain ⟨m, _, hm, rfl⟩ := hdoc hy
      have hok := ownersOk_of_isValidNode (hvalid hm)
      unfold ownersOk at hok
      have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hok).2 l (mem_intRange hl0 (by omega))
      obtain ⟨r, hr, hrc⟩ := List.any_eq_true.mp this
      simp only [Bool.and_eq_true, beq_iff_eq] at hrc
      exact ⟨r, hrc.1, ⟨hy, hr, hrc.2⟩, ⟨hy, hr, hrc.2⟩⟩
    · have hok := hpc y w hyw hy hw ha
      unfold pairOk at hok
      have := List.all_eq_true.mp hok l (mem_intRange hl0 (by omega))
      unfold commonAt at this
      obtain ⟨r, hr, hrc⟩ := List.any_eq_true.mp this
      simp only [Bool.and_eq_true, beq_iff_eq] at hrc
      exact ⟨r, hrc.1.1, ⟨hy, hr, hrc.1.2⟩, ⟨hw, hr, hrc.2⟩⟩
  · -- enlaces
    intro y hy
    obtain ⟨m, hmn, hm, hmid⟩ := hdoc hy
    have hval := hvalid hm
    refine ⟨m, hmn, fun hr => ?_, fun hl => ?_⟩
    · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (parents_of_valid hval (by rw [hmid]; exact hr))
      obtain ⟨hqa, hqadj⟩ := hlink hm ((hlinks m hm).1 q hq)
      exact ⟨q, hq, hy, hqa, by rw [← hmid]; exact hqadj⟩
    · obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (sons_of_valid hval (by rw [hmid]; exact hl))
      obtain ⟨hsa, hsadj⟩ := hlink hm ((hlinks m hm).2 s hs)
      exact ⟨s, hs, hy, hsa, by rw [← hmid]; exact hsadj⟩
  · -- apoyo de los padres
    rintro x w n ⟨hx, hw, ha⟩ hxw hn hx1
    have hm := node?_mem hn
    have hnid := node?_id hn
    obtain ⟨_, hsupp⟩ := (hcheck hm).1 (by rw [hnid]; exact hx1)
    obtain ⟨q, hq, hqw⟩ := hsupp w hw (by rw [hnid]; exact Ne.symm hxw) (by rw [hnid]; exact ha)
    obtain ⟨hqa, hqadj⟩ := hlink hm ((hlinks n hm).1 q hq)
    exact ⟨q, hq, ⟨hx, hqa, by rw [← hnid]; exact hqadj⟩, ⟨hqa, hw, hqw⟩⟩
  · -- apoyo de los hijos
    rintro x w n ⟨hx, hw, ha⟩ hxw hn hx1
    have hm := node?_mem hn
    have hnid := node?_id hn
    obtain ⟨_, hsupp⟩ := (hcheck hm).2 (by rw [hnid]; exact hx1)
    obtain ⟨q, hq, hqw⟩ := hsupp w hw (by rw [hnid]; exact Ne.symm hxw) (by rw [hnid]; exact ha)
    obtain ⟨hqa, hqadj⟩ := hlink hm ((hlinks n hm).2 q hq)
    exact ⟨q, hq, ⟨hx, hqa, by rw [← hnid]; exact hqadj⟩, ⟨hqa, hw, hqw⟩⟩

-- ============================================================
-- La salida del review
-- ============================================================

/-- **El review que entra con algo que revisar y sale válido y sin `dirty`** devuelve una vuelta limpia (desde un
estado sin `dirty`) cuya comprobación final no cambió nada. -/
theorem reviewFuel_exit :
    ∀ (n : Nat) (g : GPathB), g.dirty = true → (reviewFuel n g).isValid = true → (reviewFuel n g).dirty = false →
      ∃ g₁ : GPathB, g₁.dirty = false ∧ reviewFuel n g = g₁.reviewPass ∧ g₁.reviewPass.dirty = false ∧
        g₁.reviewPass.isValid = true ∧ (finalPass g₁.reviewPass).dirty = false := by
  intro n
  induction n with
  | zero => intro g hd _ hc; rw [reviewFuel.eq_1, hd] at hc; cases hc
  | succ n ih =>
    intro g hd hv hc
    by_cases h : (g.isValid && g.dirty) = true
    · cases hpd : (reviewPass { g with dirty := false }).dirty
      · by_cases hvp : (reviewPass { g with dirty := false }).isValid = true
        · cases hfd : (finalPass (reviewPass { g with dirty := false })).dirty
          · rw [reviewFuel_done h hpd hvp hfd]
            exact ⟨_, rfl, rfl, hpd, hvp, hfd⟩
          · rw [reviewFuel_final h hpd hvp hfd] at hv hc ⊢
            exact ih _ hfd hv hc
        · rw [reviewFuel_invalid h hpd hvp] at hv; exact absurd hv hvp
      · rw [reviewFuel_pass h hpd] at hv hc ⊢
        exact ih _ hpd hv hc
    · rw [reviewFuel_skip h] at hc; rw [hd] at hc; cases hc

-- ============================================================
-- AboveZero
-- ============================================================

theorem revPrims_aboveZero : RevPrims AboveZero := by
  refine ⟨fun g id hg => hg, fun g x w hg => hg, ?_, fun g b hg => hg, ?_⟩
  · intro g id hg n hn
    simp only [removeNode, killVertex, List.mem_map, List.mem_filter] at hn
    obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hn
    exact hg m hm
  · intro g hg n hn
    unfold pruneLinks at hn
    split at hn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      exact hg m hm
    · exact hg n hn

theorem aboveZero_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hg : AboveZero g) (hd : 0 ≤ d.step) : AboveZero (g.addNode d title forb) := by
  intro n hn
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    exact hg m hm
  · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp hn
    show 0 ≤ pid.id.step
    rw [Machine.mapId_of_mem_shiftRowIds (List.mem_filter.mp hpid).1]; exact hd

theorem aboveZero_join {g₁ g₂ : GPathB} (h₁ : AboveZero g₁) (h₂ : AboveZero g₂) : AboveZero (join g₁ g₂) := by
  intro n hn
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have := h₁ m hm
    split <;> exact this
  · exact h₂ n (List.mem_filter.mp hn).1

-- ============================================================
-- closed: el review deja el estado cerrado
-- ============================================================

/-- **El review que entra con algo que revisar y sale válido deja el estado cerrado** (antes la hipótesis
`closed`). -/
theorem closedState_review {g : GPathB} (hd : g.dirty = true) (hv : g.review.isValid = true)
    (had : AliveDocs g) (hnd : NodupIds g) (hb : Below g) (hz : AboveZero g) (hcs : 2 ≤ g.current_step) :
    ClosedState g.review := by
  have hc := review_exits_clean g hv
  obtain ⟨g₁, hg₁, he, hpd, hvp, hfd⟩ := reviewFuel_exit _ g hd hv hc
  have heq : g.review = g₁.reviewPass := he
  have had' := aliveDocs_review had
  have hnd' := revPrims_review revPrims_nodupIds g hnd
  have hb' := revPrims_review revPrims_below g hb
  have hz' := revPrims_review revPrims_aboveZero g hz
  have hcs' : g.review.current_step = g.current_step := (shrinks_review g).1.step
  rw [heq] at had' hnd' hb' hz' hcs' ⊢
  exact closedState_of_exit hvp hpd hfd (pairClosed_reviewPass hpd hvp) (docsAlive_reviewPass hg₁ hpd hvp)
    had' hnd' hb' hz' (by omega)

end GPathB

end AbsSatBingo.Model
