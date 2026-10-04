-- lean/improves_bingo/AbsSatBingo/Model/Grow.lean
import AbsSatBingo.Model.Keeps

/-!
# El join conserva y el UP alarga las camarillas llevadas (fase L6b, parte 1)

A nivel de grafo, sin la fórmula:

* **join** — una camarilla llevada por cualquiera de los dos lados la lleva la unión (`carried_join_left`,
  `carried_join_right`);
* **UP** — si `g` lleva `S` en los pasos `0 … c-1`, el id `S c` es de la fila nueva y tiene por padre a `S (c-1)`,
  la fila nueva la lleva en `0 … c` (`carried_addNode`), y el `up` también (`carried_up`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids)

namespace GPathB

variable {S : Int → PathNodeId}

-- ============================================================
-- Utilidades de listas
-- ============================================================

theorem hasEdge_adj {g : GPathB} {x w : PathNodeId} (h : g.hasEdge x w = true) : g.Adj x w := by
  unfold Adj adjb; simp [h]

theorem find?_filter_of {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = true → q a = true) → (l.filter q).find? p = l.find? p := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [List.filter_cons]
    by_cases hp : p a = true
    · have hq := h a (List.mem_cons_self ..) hp
      simp [hq, hp]
    · by_cases hq : q a = true
      · simp [hq, hp, ih']
      · simp [hq, hp, ih']

theorem find?_beq_self (x : PathNodeId) : ∀ l : List PathNodeId, x ∈ l → l.find? (· == x) = some x := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons a as ih =>
    intro h
    rw [List.find?_cons]
    by_cases hax : a = x
    · subst hax; simp
    · have : (a == x) = false := beq_false_of_ne hax
      rw [this]
      exact ih ((List.mem_cons.mp h).resolve_left (Ne.symm hax))

-- ============================================================
-- El join
-- ============================================================

theorem alive_join (g₁ g₂ : GPathB) (q : PathNodeId) :
    q ∈ (join g₁ g₂).alive ↔ q ∈ g₁.alive ∨ q ∈ g₂.alive := by
  simp only [join, List.mem_append, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases h1 : q ∈ g₁.alive
      · exact Or.inl h1
      · exact Or.inr ⟨h, Bool.eq_false_iff.mpr (fun hc => h1 (List.contains_iff_mem.mp hc))⟩

theorem adj_join_left {g₁ g₂ : GPathB} {a b : PathNodeId} (h : g₁.Adj a b) : (join g₁ g₂).Adj a b :=
  adj_mono (fun q hq => (alive_join g₁ g₂ q).mpr (Or.inl hq))
    (fun _ he => List.mem_append_left _ he) a b h

theorem adj_join_right {g₁ g₂ : GPathB} {a b : PathNodeId} (h : g₂.Adj a b) : (join g₁ g₂).Adj a b := by
  rw [adj_iff] at h
  rcases h with ⟨rfl, hal⟩ | ⟨e, he, hj⟩
  · exact adj_refl _ _ ((alive_join g₁ g₂ a).mpr (Or.inr hal))
  · by_cases h1 : g₁.hasEdge e.1 e.2 = true
    · apply adj_join_left
      rcases hj with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · rw [h1', h2'] at h1; exact hasEdge_adj h1
      · rw [h1', h2', hasEdge_comm] at h1; exact hasEdge_adj h1
    · rw [adj_iff]
      refine Or.inr ⟨e, List.mem_append_right _ (List.mem_filter.mpr ⟨he, by simpa using h1⟩), hj⟩

theorem node?_join (g₁ g₂ : GPathB) (x : PathNodeId) :
    (join g₁ g₂).node? x =
      ((g₁.node? x).map (fun n => match g₂.node? n.id with | some m => mergeNode n m | none => n)).or
      ((g₂.nodes.filter (fun m => (g₁.node? m.id).isNone)).find? (fun n => n.id == x)) := by
  show List.find? _ (_ ++ _) = _
  rw [List.find?_append, find?_map_id]
  · rfl
  · intro n; split <;> rfl

theorem carried_join_left {g₁ g₂ : GPathB} (h : Carried g₁ S) : Carried (join g₁ g₂) S := by
  refine ⟨h.step, fun k h0 h1 => (alive_join g₁ g₂ _).mpr (Or.inl (h.alive k h0 h1)),
    fun k l h0 h1 h2 h3 => adj_join_left (h.adj k l h0 h1 h2 h3), h.root, ?_⟩
  intro k h0 (h1 : k < g₁.current_step)
  obtain ⟨n, hn, hp, hs⟩ := h.node k h0 h1
  rw [node?_join, hn]
  simp only [Option.map_some, Option.some_or]
  refine ⟨_, rfl, ?_, ?_⟩
  · intro hk; split
    · exact List.mem_append_left _ (hp hk)
    · exact hp hk
  · intro hk; split
    · exact List.mem_append_left _ (hs hk)
    · exact hs hk

theorem mem_merge_parents {a b : PNodeB} {p : PathNodeId} (h : p ∈ b.parents) : p ∈ (mergeNode a b).parents := by
  simp only [mergeNode, List.mem_append, List.mem_filter, Bool.not_eq_true']
  by_cases hp : p ∈ a.parents
  · exact Or.inl hp
  · exact Or.inr ⟨h, Bool.eq_false_iff.mpr (fun hc => hp (List.contains_iff_mem.mp hc))⟩

theorem mem_merge_sons {a b : PNodeB} {p : PathNodeId} (h : p ∈ b.sons) : p ∈ (mergeNode a b).sons := by
  simp only [mergeNode, List.mem_append, List.mem_filter, Bool.not_eq_true']
  by_cases hp : p ∈ a.sons
  · exact Or.inl hp
  · exact Or.inr ⟨h, Bool.eq_false_iff.mpr (fun hc => hp (List.contains_iff_mem.mp hc))⟩

theorem carried_join_right {g₁ g₂ : GPathB} (hcs : g₁.current_step = g₂.current_step) (h : Carried g₂ S) :
    Carried (join g₁ g₂) S := by
  have hcs' : (join g₁ g₂).current_step = g₂.current_step := hcs
  refine ⟨fun k h0 h1 => h.step k h0 (hcs' ▸ h1),
    fun k h0 h1 => (alive_join g₁ g₂ _).mpr (Or.inr (h.alive k h0 (hcs' ▸ h1))),
    fun k l h0 h1 h2 h3 => adj_join_right (h.adj k l h0 (hcs' ▸ h1) h2 (hcs' ▸ h3)),
    fun hc => h.root (hcs' ▸ hc), ?_⟩
  intro k h0 h1
  have h1 : k < g₂.current_step := hcs' ▸ h1
  obtain ⟨m, hm, hp, hs⟩ := h.node k h0 h1
  have hmid := node?_id hm
  rw [node?_join]
  cases hn : g₁.node? (S k) with
  | some n =>
    have hnid := node?_id hn
    simp only [Option.map_some, Option.some_or]
    rw [hnid, hm]
    refine ⟨_, rfl, fun hk => mem_merge_parents (hp hk), fun hk => mem_merge_sons (hs (hcs' ▸ hk))⟩
  | none =>
    simp only [Option.map_none, Option.none_or]
    rw [find?_filter_of]
    · exact ⟨m, hm, hp, fun hk => hs (hcs' ▸ hk)⟩
    · intro a _ ha
      have : a.id = S k := by simpa using ha
      rw [this, hn]; rfl

theorem carried_doJoin_left {g₁ g₂ : GPathB} (h : Carried g₁ S) : Carried (doJoin g₁ g₂) S := by
  unfold doJoin; split
  · exact carried_join_left h
  · exact h

theorem carried_doJoin_right {g₁ g₂ : GPathB} (hok : okJoin g₁ g₂ = true) (h : Carried g₂ S) :
    Carried (doJoin g₁ g₂) S := by
  unfold doJoin
  rw [if_pos hok]
  unfold okJoin at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact carried_join_right hok.1.1.1 h

-- ============================================================
-- El UP
-- ============================================================

theorem find?_newRow {g : GPathB} {d : NodeId} {title : String} {ids : List PathNodeId} {x : PathNodeId}
    (hx : x ∈ ids) : (ids.map (g.rowNode d title)).find? (fun n => n.id == x) = some (g.rowNode d title x) := by
  rw [List.find?_map]
  have : ((fun n => n.id == x) ∘ g.rowNode d title) = (· == x) := by funext q; rfl
  rw [this, find?_beq_self x ids hx]; rfl

/-- **La fila nueva alarga la camarilla**: si `g` la lleva en `0 … c-1`, `S c` es de la fila y su padre es
`S (c-1)`, y todo documento está por debajo de `c`, la fila la lleva en `0 … c`. -/
theorem carried_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (h : Carried g S) (hnew : S g.current_step ∈ g.newRowIds d forb)
    (hpar : 0 < g.current_step → S (g.current_step - 1) ∈ g.rowParents d (S g.current_step))
    (hstep : (S g.current_step).id.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hroot : (S 0).parent_id = none) :
    Carried (g.addNode d title forb) S := by
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  have halive : ∀ q ∈ g.alive, q ∈ (g.addNode d title forb).alive := fun q hq => List.mem_append_left _ hq
  have hedge : ∀ e ∈ g.edges, e ∈ (g.addNode d title forb).edges := fun e he => List.mem_append_left _ he
  -- la arista nueva de `S c` a cada `S l` anterior
  have hnewadj : ∀ l, 0 ≤ l → l < g.current_step → (g.addNode d title forb).Adj (S g.current_step) (S l) := by
    intro l h0 h1
    rw [adj_iff]
    refine Or.inr ⟨(S g.current_step, S l), List.mem_append_right _ ?_, Or.inl ⟨rfl, rfl⟩⟩
    refine List.mem_flatMap.mpr ⟨S g.current_step, hnew, List.mem_map.mpr ⟨S l, ?_, rfl⟩⟩
    refine List.mem_filter.mpr ⟨h.alive l h0 h1, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨by rw [h.step l h0 h1, hstep]; simpa using h1, ?_⟩
    exact List.any_eq_true.mpr ⟨S (g.current_step - 1), hpar (by omega),
      h.adj (g.current_step - 1) l (by omega) (by omega) h0 h1⟩
  refine ⟨?_, ?_, ?_, fun _ => hroot, ?_⟩
  · intro k h0 h1
    rw [hcs] at h1
    rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h1) with hk | rfl
    · exact h.step k h0 hk
    · exact hstep
  · intro k h0 h1
    rw [hcs] at h1
    rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h1) with hk | rfl
    · exact halive _ (h.alive k h0 hk)
    · exact List.mem_append_right _ hnew
  · intro k l h0 h1 h2 h3
    rw [hcs] at h1 h3
    rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h1) with hk | rfl <;>
      rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h3) with hl | rfl
    · exact adj_mono halive hedge _ _ (h.adj k l h0 hk h2 hl)
    · exact (adj_symm _ _ _).mp (hnewadj k h0 hk)
    · exact hnewadj l h2 hl
    · exact adj_refl _ _ (List.mem_append_right _ hnew)
  · intro k h0 h1
    rw [hcs] at h1
    let f : PNodeB → PNodeB := fun n => { n with sons := n.sons ++ g.gainedSons d forb n }
    have hnodes : (g.addNode d title forb).nodes = g.nodes.map f ++ (g.newRowIds d forb).map (g.rowNode d title) :=
      rfl
    rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h1) with hk | rfl
    · obtain ⟨n, hn, hp, hs⟩ := h.node k h0 hk
      have hnid := node?_id hn
      refine ⟨f n, ?_, hp, ?_⟩
      · show List.find? _ (g.addNode d title forb).nodes = _
        rw [hnodes, List.find?_append, find?_map_id f (fun _ => rfl)]
        show ((g.node? (S k)).map f).or _ = _
        rw [hn]; rfl
      · intro hk'
        rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp hk') with hk'' | heq
        · exact List.mem_append_left _ (hs hk'')
        · have hkc : k = g.current_step - 1 := by omega
          refine List.mem_append_right _ (List.mem_filter.mpr ⟨?_, ?_⟩)
          · rw [heq]; exact hnew
          · rw [heq, hnid, hkc]
            exact List.contains_iff_mem.mpr (hpar (by omega))
    · refine ⟨g.rowNode d title (S g.current_step), ?_, ?_, ?_⟩
      · show List.find? _ (g.addNode d title forb).nodes = _
        rw [hnodes, List.find?_append, find?_map_id f (fun _ => rfl)]
        have hnone : g.node? (S g.current_step) = none := by
          apply List.find?_eq_none.mpr
          intro n hn hid
          have := hbelow n hn
          rw [show n.id = S g.current_step by simpa using hid, hstep] at this
          omega
        show ((g.node? (S g.current_step)).map f).or _ = _
        rw [hnone, Option.map_none, Option.none_or]
        exact find?_newRow hnew
      · intro hk; exact hpar hk
      · intro hk; omega

/-- **El `up` alarga la camarilla** (la fila y el review, que la conserva). -/
theorem carried_up {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (h : Carried g S) (hnew : S g.current_step ∈ g.newRowIds d forb)
    (hpar : 0 < g.current_step → S (g.current_step - 1) ∈ g.rowParents d (S g.current_step))
    (hstep : (S g.current_step).id.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hroot : (S 0).parent_id = none) :
    Carried (g.up d title forb) S := by
  unfold up
  rw [if_pos (isValid_of_carried h)]
  exact carried_review (carried_addNode h hnew hpar hstep hbelow hroot)

end GPathB

end AbsSatBingo.Model
