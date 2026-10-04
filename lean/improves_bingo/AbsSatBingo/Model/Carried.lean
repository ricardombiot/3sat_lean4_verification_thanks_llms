-- lean/improves_bingo/AbsSatBingo/Model/Carried.lean
import AbsSatBingo.Model.Shrink

/-!
# Camarillas llevadas (fase L6, parte 1)

`Carried g S`: la selección `S` (un nodo por paso `0 … current_step-1`) está **viva en `g`**: sus nodos viven,
se poseen dos a dos, y los consecutivos están enlazados. Es la forma, puramente combinatoria, en que un estado lleva
una solución: no habla de la fórmula. El marco de reglas pide a toda regla que conserve `Carried` (`Rule.keeps`), y
con eso sale la completitud del lector bajo `NoZombie` (`Reader.lean`).

Aquí: la definición, que todo nodo de una camarilla llevada es válido (`isValidNode_of_carried`), y qué
primitivas la conservan.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

-- ============================================================
-- intRange (copias locales de lean/improves_bin: Filter, PickInduction)
-- ============================================================

theorem mem_intRange {lo hi k : Int} (h1 : lo ≤ k) (h2 : k ≤ hi) : k ∈ intRange lo hi := by
  simp only [intRange, List.mem_map, List.mem_range]
  refine ⟨(k - lo).toNat, by omega, ?_⟩
  have htn : ((k - lo).toNat : Int) = k - lo := Int.toNat_of_nonneg (by omega)
  simp only [Int.ofNat_eq_natCast, htn]
  omega

theorem intRange_bounds {lo hi k : Int} (h : k ∈ intRange lo hi) : lo ≤ k ∧ k ≤ hi := by
  simp only [intRange, List.mem_map, List.mem_range, Int.ofNat_eq_natCast] at h
  obtain ⟨i, hi', rfl⟩ := h
  exact ⟨by omega, by omega⟩

-- ============================================================
-- node?
-- ============================================================

theorem node?_id {g : GPathB} {x : PathNodeId} {n : PNodeB} (h : g.node? x = some n) : n.id = x := by
  have := List.find?_some h
  simpa using this

theorem node?_mem {g : GPathB} {x : PathNodeId} {n : PNodeB} (h : g.node? x = some n) : n ∈ g.nodes :=
  List.mem_of_find?_eq_some h

/-- `node?` a través de un `map` que conserva los ids. -/
theorem find?_map_id (f : PNodeB → PNodeB) (hf : ∀ n, (f n).id = n.id) (x : PathNodeId) :
    ∀ l : List PNodeB, (l.map f).find? (fun n => n.id == x) = (l.find? (fun n => n.id == x)).map f := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.find?_cons, hf]
    split <;> simp_all

/-- `node?` tras eliminar otro nodo: el mismo documento, sin enlaces al eliminado. -/
theorem find?_removeNode (id x : PathNodeId) (hx : x ≠ id) :
    ∀ l : List PNodeB, ((l.filter (fun n => n.id != id)).map (unlinkAll id)).find? (fun n => n.id == x) =
      (l.find? (fun n => n.id == x)).map (unlinkAll id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.filter_cons]
    by_cases ha : a.id = id
    · have hax : (a.id == x) = false := by
        rw [ha]; exact beq_false_of_ne (Ne.symm hx)
      simp only [ha, bne_self_eq_false, Bool.false_eq_true, if_false, ih, List.find?_cons]
      rw [← ha, hax]
    · have hne : (a.id != id) = true := bne_iff_ne.mpr ha
      simp only [hne, if_true, List.map_cons, List.find?_cons, ih]
      have hid : (unlinkAll id a).id = a.id := rfl
      rw [hid]
      split <;> rfl

theorem node?_removeNode {g : GPathB} {id x : PathNodeId} (hx : x ≠ id) :
    (g.removeNode id).node? x = (g.node? x).map (unlinkAll id) :=
  find?_removeNode id x hx g.nodes

-- ============================================================
-- La camarilla llevada
-- ============================================================

/-- `x` es un nodo de la selección, en un paso `0 … cs-1`. -/
def OnS (cs : Int) (S : Int → PathNodeId) (x : PathNodeId) : Prop :=
  ∃ k, 0 ≤ k ∧ k < cs ∧ S k = x

/-- **La selección `S` está viva en `g`.** -/
structure Carried (g : GPathB) (S : Int → PathNodeId) : Prop where
  step  : ∀ k, 0 ≤ k → k < g.current_step → (S k).id.step = k
  alive : ∀ k, 0 ≤ k → k < g.current_step → S k ∈ g.alive
  adj   : ∀ k l, 0 ≤ k → k < g.current_step → 0 ≤ l → l < g.current_step → g.Adj (S k) (S l)
  root  : 0 < g.current_step → (S 0).parent_id = none
  node  : ∀ k, 0 ≤ k → k < g.current_step → ∃ n, g.node? (S k) = some n ∧
            (0 < k → S (k - 1) ∈ n.parents) ∧ (k + 1 < g.current_step → S (k + 1) ∈ n.sons)

theorem Carried.adj_on {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) {x w : PathNodeId}
    (hx : OnS g.current_step S x) (hw : OnS g.current_step S w) : g.Adj x w := by
  obtain ⟨k, hk0, hk1, rfl⟩ := hx
  obtain ⟨l, hl0, hl1, rfl⟩ := hw
  exact h.adj k l hk0 hk1 hl0 hl1

/-- Un nodo llevado es un nodo de la selección en su propio paso. -/
theorem Carried.onS_step {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) {x : PathNodeId}
    (hx : OnS g.current_step S x) : S x.id.step = x := by
  obtain ⟨k, hk0, hk1, rfl⟩ := hx
  rw [h.step k hk0 hk1]

/-- **Todo gpath que lleva una selección es válido.** -/
theorem isValid_of_carried {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) : g.isValid = true := by
  unfold isValid
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨h0, h1⟩ := intRange_bounds hk
  exact List.any_eq_true.mpr ⟨S k, h.alive k h0 (by omega), by simp [h.step k h0 (by omega)]⟩

/-- La tabla de un nodo de la selección es válida: vive y posee al nodo de la selección de cada paso. -/
theorem ownersOk_of_carried {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) (k : Int)
    (hk0 : 0 ≤ k) (hk1 : k < g.current_step) : g.ownersOk (S k) = true := by
  unfold ownersOk isAlive
  rw [Bool.and_eq_true]
  refine ⟨List.contains_iff_mem.mpr (h.alive k hk0 hk1), ?_⟩
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨h0, h1⟩ := intRange_bounds hl
  unfold hasNeighborAt
  exact List.any_eq_true.mpr ⟨S l, h.alive l h0 (by omega), by
    rw [Bool.and_eq_true]
    exact ⟨by simp [h.step l h0 (by omega)], h.adj k l hk0 hk1 h0 (by omega)⟩⟩

/-- **Todo nodo de una camarilla llevada es válido.** -/
theorem isValidNode_of_carried {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) (k : Int)
    (hk0 : 0 ≤ k) (hk1 : k < g.current_step) {n : PNodeB} (hn : g.node? (S k) = some n) :
    g.isValidNode n = true := by
  have hid := node?_id hn
  obtain ⟨n', hn', hpar, hson⟩ := h.node k hk0 hk1
  rw [hn] at hn'
  cases hn'
  have hok : g.ownersOk n.id = true := by rw [hid]; exact ownersOk_of_carried h k hk0 hk1
  have hpar' : 0 < k → n.parents.isEmpty = false := fun hk => by
    cases hp : n.parents with
    | nil => rw [hp] at hpar; exact absurd (hpar hk) List.not_mem_nil
    | cons _ _ => rfl
  have hson' : k + 1 < g.current_step → n.sons.isEmpty = false := fun hk => by
    cases hs : n.sons with
    | nil => rw [hs] at hson; exact absurd (hson hk) List.not_mem_nil
    | cons _ _ => rfl
  have hstep : n.id.id.step = k := by rw [hid]; exact h.step k hk0 hk1
  unfold isValidNode
  simp only
  by_cases hroot : n.id.parent_id.isNone = true
  · rw [if_pos hroot]
    by_cases hlast : (n.id.id.step == g.current_step - 1) = true
    · rw [if_pos hlast]; exact hok
    · rw [if_neg hlast]
      have : k + 1 < g.current_step := by
        rw [hstep] at hlast; simp at hlast; omega
      simp [hok, hson' this]
  · rw [if_neg hroot]
    have hk : 0 < k := by
      rcases Int.lt_or_eq_of_le hk0 with hlt | heq
      · exact hlt
      · subst heq
        exfalso; apply hroot
        rw [hid, h.root (by omega)]; rfl
    by_cases hlast : (n.id.id.step == g.current_step - 1) = true
    · rw [if_pos hlast]; simp [hok, hpar' hk]
    · rw [if_neg hlast]
      have : k + 1 < g.current_step := by
        rw [hstep] at hlast; simp at hlast; omega
      simp [hok, hpar' hk, hson' this]

/-- La otra cara: un nodo inválido no es de la selección. -/
theorem not_onS_of_invalid {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) {id : PathNodeId}
    {n : PNodeB} (hn : g.node? id = some n) (hv : g.isValidNode n = false) : ¬ OnS g.current_step S id := by
  rintro ⟨k, hk0, hk1, rfl⟩
  rw [isValidNode_of_carried h k hk0 hk1 hn] at hv
  exact Bool.noConfusion hv

-- ============================================================
-- Las primitivas
-- ============================================================

theorem adj_killVertex_of {g : GPathB} {id a b : PathNodeId} (h : g.Adj a b) (ha : a ≠ id) (hb : b ≠ id) :
    (g.killVertex id).Adj a b := by
  rw [adj_iff] at h ⊢
  rcases h with ⟨rfl, hal⟩ | ⟨e, he, hj⟩
  · exact Or.inl ⟨rfl, List.mem_filter.mpr ⟨hal, bne_iff_ne.mpr ha⟩⟩
  · refine Or.inr ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, hj⟩
    simp only [touches, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨ha, hb⟩
    · rw [h1, h2]; exact ⟨hb, ha⟩

theorem carried_killVertex {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) {id : PathNodeId}
    (hid : ¬ OnS g.current_step S id) : Carried (g.killVertex id) S := by
  have hne : ∀ k, 0 ≤ k → k < g.current_step → S k ≠ id := fun k h0 h1 he => hid ⟨k, h0, h1, he⟩
  exact ⟨h.step, fun k h0 h1 => List.mem_filter.mpr ⟨h.alive k h0 h1, bne_iff_ne.mpr (hne k h0 h1)⟩,
    fun k l h0 h1 h2 h3 => adj_killVertex_of (h.adj k l h0 h1 h2 h3) (hne k h0 h1) (hne l h2 h3),
    h.root, h.node⟩

theorem carried_removeNode {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) {id : PathNodeId}
    (hid : ¬ OnS g.current_step S id) : Carried (g.removeNode id) S := by
  have hk := carried_killVertex h hid
  have hne : ∀ k, 0 ≤ k → k < g.current_step → S k ≠ id := fun k h0 h1 he => hid ⟨k, h0, h1, he⟩
  refine ⟨hk.step, hk.alive, hk.adj, hk.root, ?_⟩
  intro k h0 (h1 : k < g.current_step)
  obtain ⟨n, hn, hp, hs⟩ := h.node k h0 h1
  refine ⟨unlinkAll id n, ?_, ?_, ?_⟩
  · rw [node?_removeNode (hne k h0 h1), hn]; rfl
  · intro hk'
    exact List.mem_filter.mpr ⟨hp hk', bne_iff_ne.mpr (hne (k - 1) (by omega) (by omega))⟩
  · intro (hk' : k + 1 < g.current_step)
    exact List.mem_filter.mpr ⟨hs hk', bne_iff_ne.mpr (hne (k + 1) (by omega) hk')⟩

theorem not_or_not_of_not_and {p q : Prop} [Decidable p] (h : ¬ (p ∧ q)) : ¬ p ∨ ¬ q := by
  by_cases hp : p
  · exact Or.inr (fun hq => h ⟨hp, hq⟩)
  · exact Or.inl hp

theorem adj_removeEdge_of {g : GPathB} {x w a b : PathNodeId} (h : g.Adj a b)
    (h1 : ¬ (a = x ∧ b = w)) (h2 : ¬ (a = w ∧ b = x)) : (g.removeEdge x w).Adj a b := by
  rw [adj_iff] at h ⊢
  rcases h with ⟨rfl, hal⟩ | ⟨e, he, hj⟩
  · exact Or.inl ⟨rfl, hal⟩
  · refine Or.inr ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, hj⟩
    simp only [joins, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq]
    rcases hj with ⟨he1, he2⟩ | ⟨he1, he2⟩ <;> rw [he1, he2]
    · exact ⟨not_or_not_of_not_and h1, not_or_not_of_not_and h2⟩
    · exact ⟨not_or_not_of_not_and (fun ⟨hb, ha⟩ => h2 ⟨ha, hb⟩),
        not_or_not_of_not_and (fun ⟨hb, ha⟩ => h1 ⟨ha, hb⟩)⟩

/-- Quitar una arista que no une dos nodos de la selección conserva la camarilla. -/
theorem carried_removeEdge {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) {x w : PathNodeId}
    (hxw : ¬ (OnS g.current_step S x ∧ OnS g.current_step S w)) : Carried (g.removeEdge x w) S := by
  refine ⟨h.step, h.alive, ?_, h.root, h.node⟩
  intro k l h0 h1 h2 h3
  apply adj_removeEdge_of (h.adj k l h0 h1 h2 h3)
  · rintro ⟨rfl, rfl⟩; exact hxw ⟨⟨k, h0, h1, rfl⟩, ⟨l, h2, h3, rfl⟩⟩
  · rintro ⟨rfl, rfl⟩; exact hxw ⟨⟨l, h2, h3, rfl⟩, ⟨k, h0, h1, rfl⟩⟩

theorem carried_dirty {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) (b : Bool) :
    Carried { g with dirty := b } S := ⟨h.step, h.alive, h.adj, h.root, h.node⟩

/-- Un `foldl` de pasos que conservan la camarilla y el paso actual `cs` los conserva. -/
theorem carried_foldl {α : Type} {S : Int → PathNodeId} {cs : Int} (f : GPathB → α → GPathB) (l : List α)
    (hf : ∀ g a, a ∈ l → Carried g S → g.current_step = cs → Carried (f g a) S ∧ (f g a).current_step = cs) :
    ∀ g, Carried g S → g.current_step = cs → Carried (l.foldl f g) S ∧ (l.foldl f g).current_step = cs := by
  induction l with
  | nil => intro g h hc; exact ⟨h, hc⟩
  | cons a as ih =>
    intro g h hc
    obtain ⟨h1, h2⟩ := hf g a (List.mem_cons_self ..) h hc
    exact ih (fun g' a' ha' => hf g' a' (List.mem_cons_of_mem _ ha')) _ h1 h2

end GPathB

end AbsSatBingo.Model
