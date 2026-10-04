-- lean/improves_bingo/AbsSatBingo/Model/EdgeCliqueUp.lean
import AbsSatBingo.Model.EdgeClique

/-!
# El UP conserva `EdgeClique`

La fila nueva (`addNode`) no rompe «todo lo vivo está en una camarilla»: cada camarilla se alarga con el hijo de su
nodo de la cima (`carried_addNode`), y las parejas nuevas vienen de un padre cuya camarilla se alarga con el nodo
nuevo. Sin ventanas saltadas el UP no corre el review (entra sin `dirty`), así que **`edgeClique_up`**.

Medido en Julia (`probe_secpair_ops.jl`, `probe_edgeclique.jl`): tras `add_row!`, sin review, 0 fallos; el review del
UP no corre nunca en el corpus.

Hipótesis de contabilidad (valen en los estados revisados de la máquina): no se salta ninguna ventana
(`skipsWindow = false`), todo documento está vivo (lo deja la purga), los documentos están por debajo de la cima, y el
nodo del mapa de la fila es el del paso siguiente.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

variable {S : Int → PathNodeId}

-- ============================================================
-- Selecciones que coinciden por debajo
-- ============================================================

theorem carried_congr {g : GPathB} {S' : Int → PathNodeId} (h : Carried g S)
    (hS : ∀ k, 0 ≤ k → k < g.current_step → S' k = S k) : Carried g S' := by
  refine ⟨fun k h0 h1 => by rw [hS k h0 h1]; exact h.step k h0 h1,
    fun k h0 h1 => by rw [hS k h0 h1]; exact h.alive k h0 h1,
    fun k l h0 h1 h2 h3 => by rw [hS k h0 h1, hS l h2 h3]; exact h.adj k l h0 h1 h2 h3,
    fun hc => by rw [hS 0 (Int.le_refl 0) hc]; exact h.root hc, ?_⟩
  intro k h0 h1
  obtain ⟨n, hn, hp, hs⟩ := h.node k h0 h1
  refine ⟨n, by rw [hS k h0 h1]; exact hn, fun hk => ?_, fun hk => ?_⟩
  · rw [hS (k - 1) (by omega) (by omega)]; exact hp hk
  · rw [hS (k + 1) (by omega) hk]; exact hs hk

/-- La selección alargada con `n` en el paso `c`. -/
def extSel (S : Int → PathNodeId) (c : Int) (n : PathNodeId) : Int → PathNodeId :=
  fun k => if k = c then n else S k

theorem onS_extSel {c : Int} {n y : PathNodeId} (hy : OnS c S y) : OnS (c + 1) (extSel S c n) y := by
  obtain ⟨k, h0, h1, rfl⟩ := hy
  exact ⟨k, h0, by omega, by simp [extSel, show k ≠ c by omega]⟩

theorem onS_extSel_new {c : Int} (hc : 0 ≤ c) (n : PathNodeId) : OnS (c + 1) (extSel S c n) n :=
  ⟨c, hc, by omega, by simp [extSel]⟩

-- ============================================================
-- La fila nueva
-- ============================================================

theorem mem_newParents {g : GPathB} (hpos : 0 < g.current_step) {n : PNodeB} (hn : n ∈ g.nodes)
    (hs : n.id.id.step = g.current_step - 1) : n.id ∈ g.newParents := by
  unfold newParents
  rw [if_pos hpos]
  exact List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hn, by simp [hs]⟩, rfl⟩

theorem step_of_newParents {g : GPathB} {q : PathNodeId} (hq : q ∈ g.newParents) :
    ∃ n ∈ g.nodes, n.id = q ∧ q.id.step = g.current_step - 1 := by
  unfold newParents at hq
  split at hq
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
    have := (List.mem_filter.mp hn).2
    exact ⟨n, (List.mem_filter.mp hn).1, rfl, by simpa using this⟩
  · cases hq

/-- Sin ventanas saltadas, el hijo de un padre candidato está en la fila y el padre es suyo. -/
theorem son_in_row {g : GPathB} {d : NodeId} {forb : PathNodeId → Bool} (hpos : 0 < g.current_step)
    (hskip : g.skipsWindow d forb = false) {q : PathNodeId} (hq : q ∈ g.newParents) :
    shiftPid q d ∈ g.newRowIds d forb ∧ q ∈ g.rowParents d (shiftPid q d) := by
  have hmem : shiftPid q d ∈ g.shiftRowIds d := by
    unfold shiftRowIds
    rw [if_pos hpos, mem_dedupPids]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  refine ⟨List.mem_filter.mpr ⟨hmem, ?_⟩, List.mem_filter.mpr ⟨hq, by simp⟩⟩
  unfold skipsWindow at hskip
  have := List.any_eq_false.mp hskip _ hmem
  simp [this]

/-- Cada nodo de la fila viene de un padre candidato, y es de `d`. -/
theorem parent_of_row {g : GPathB} {d : NodeId} {forb : PathNodeId → Bool} (hpos : 0 < g.current_step)
    {n : PathNodeId} (hn : n ∈ g.newRowIds d forb) : ∃ q ∈ g.rowParents d n, n = shiftPid q d := by
  have h1 := (List.mem_filter.mp hn).1
  unfold shiftRowIds at h1
  rw [if_pos hpos, mem_dedupPids] at h1
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h1
  exact ⟨q, List.mem_filter.mpr ⟨hq, by simp⟩, rfl⟩

theorem rowParents_sub {g : GPathB} {d : NodeId} {n q : PathNodeId} (hq : q ∈ g.rowParents d n) :
    q ∈ g.newParents := (List.mem_filter.mp hq).1

/-- **Alargar una camarilla con un nodo de la fila** cuyo padre es su nodo de la cima. -/
theorem carried_extSel {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (h : Carried g S) (hpos : 0 < g.current_step) {n : PathNodeId} (hn : n ∈ g.newRowIds d forb)
    (hp : S (g.current_step - 1) ∈ g.rowParents d n) (hd : d.step = g.current_step)
    (hbelow : ∀ m ∈ g.nodes, m.id.id.step < g.current_step) :
    Carried (g.addNode d title forb) (extSel S g.current_step n) := by
  have hc : Carried g (extSel S g.current_step n) :=
    carried_congr h (fun k _ h1 => by simp [extSel, show k ≠ g.current_step by omega])
  have hsc : extSel S g.current_step n g.current_step = n := by simp [extSel]
  have hsc1 : extSel S g.current_step n (g.current_step - 1) = S (g.current_step - 1) := by
    simp [extSel, show g.current_step - 1 ≠ g.current_step by omega]
  have hs0 : extSel S g.current_step n 0 = S 0 := by simp [extSel, show (0 : Int) ≠ g.current_step by omega]
  obtain ⟨q, _, hnq⟩ := parent_of_row hpos hn
  refine carried_addNode hc (by rw [hsc]; exact hn) (fun _ => by rw [hsc, hsc1]; exact hp)
    (by rw [hsc, hnq]; exact hd) hbelow (by rw [hs0]; exact h.root hpos)

/-- El nodo de la selección en la cima es un padre candidato. -/
theorem top_newParents {g : GPathB} (h : Carried g S) (hpos : 0 < g.current_step) :
    S (g.current_step - 1) ∈ g.newParents := by
  obtain ⟨m, hm, _, _⟩ := h.node (g.current_step - 1) (by omega) (by omega)
  have hid := node?_id hm
  rw [← hid]
  exact mem_newParents hpos (node?_mem hm) (by rw [hid, h.step _ (by omega) (by omega)])

/-- Un nodo de la selección en el paso `c - 1` es su nodo de la cima. -/
theorem top_of_onS {g : GPathB} (h : Carried g S) {q : PathNodeId} (hq : OnS g.current_step S q)
    (hs : q.id.step = g.current_step - 1) : S (g.current_step - 1) = q := by
  obtain ⟨k, h0, h1, rfl⟩ := hq
  rw [h.step k h0 h1] at hs
  rw [hs]

-- ============================================================
-- EdgeClique en la fila
-- ============================================================

/-- Una pareja vieja en camarilla lo sigue estando tras la fila. -/
theorem onClique_addNode_old {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hpos : 0 < g.current_step) (hskip : g.skipsWindow d forb = false) (hd : d.step = g.current_step)
    (hbelow : ∀ m ∈ g.nodes, m.id.id.step < g.current_step) {y w : PathNodeId} (hyw : OnClique g y w) :
    OnClique (g.addNode d title forb) y w := by
  obtain ⟨S, hc, hy, hw⟩ := hyw
  obtain ⟨hn, hp⟩ := son_in_row (d := d) (forb := forb) hpos hskip (top_newParents hc hpos)
  exact ⟨_, carried_extSel (title := title) hc hpos hn hp hd hbelow, onS_extSel hy, onS_extSel hw⟩

/-- Un nodo nuevo, con un vecino que su padre `q` posee en camarilla. -/
theorem onClique_addNode_new {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hpos : 0 < g.current_step) (hd : d.step = g.current_step)
    (hbelow : ∀ m ∈ g.nodes, m.id.id.step < g.current_step) {n q w : PathNodeId}
    (hn : n ∈ g.newRowIds d forb) (hq : q ∈ g.rowParents d n) (hqw : OnClique g q w) :
    OnClique (g.addNode d title forb) n w := by
  obtain ⟨S, hc, hqS, hw⟩ := hqw
  obtain ⟨_, _, _, hqs⟩ := step_of_newParents (rowParents_sub hq)
  have htop := top_of_onS hc hqS hqs
  exact ⟨_, carried_extSel (title := title) hc hpos hn (by rw [htop]; exact hq) hd hbelow,
    onS_extSel_new (by omega) n, onS_extSel hw⟩

theorem onClique_symm {g : GPathB} {y w : PathNodeId} (h : OnClique g y w) : OnClique g w y := by
  obtain ⟨S, hc, hy, hw⟩ := h
  exact ⟨S, hc, hw, hy⟩

/-- **La fila nueva conserva `EdgeClique`** (sin ventanas saltadas, con todo documento vivo y por debajo de la
cima). -/
theorem edgeClique_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (h : EdgeClique g) (hpos : 0 < g.current_step) (hskip : g.skipsWindow d forb = false)
    (hd : d.step = g.current_step) (hbelow : ∀ m ∈ g.nodes, m.id.id.step < g.current_step)
    (hdocs : ∀ m ∈ g.nodes, m.id ∈ g.alive) : EdgeClique (g.addNode d title forb) := by
  -- un padre candidato está vivo y en camarilla consigo mismo
  have hpar : ∀ {q}, q ∈ g.newParents → OnClique g q q := by
    intro q hq
    obtain ⟨m, hm, rfl, _⟩ := step_of_newParents hq
    exact h _ _ (adj_refl g _ (hdocs m hm))
  intro y w hyw
  rw [adj_iff] at hyw
  rcases hyw with ⟨rfl, hal⟩ | ⟨e, he, hj⟩
  · -- la reflexiva: un vivo viejo o un nodo nuevo
    rcases List.mem_append.mp hal with hold | hnew
    · exact onClique_addNode_old hpos hskip hd hbelow (h y y (adj_refl g y hold))
    · obtain ⟨q, hq, _⟩ := parent_of_row hpos hnew
      have := onClique_addNode_new (title := title) hpos hd hbelow hnew hq (hpar (rowParents_sub hq))
      obtain ⟨S, hc, hn, _⟩ := this
      exact ⟨S, hc, hn, hn⟩
  · rcases List.mem_append.mp he with hold | hnew
    · -- una arista vieja
      have ha : g.Adj y w := (adj_iff g y w).mpr (Or.inr ⟨e, hold, hj⟩)
      exact onClique_addNode_old hpos hskip hd hbelow (h y w ha)
    · -- una arista nueva (pid, w'): w' lo posee un padre de pid
      obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp hnew
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
      obtain ⟨_, hany⟩ := Bool.and_eq_true_iff.mp (List.mem_filter.mp hw').2
      obtain ⟨q, hq, hqw⟩ := List.any_eq_true.mp hany
      have hc := onClique_addNode_new (title := title) hpos hd hbelow hpid hq (h q w' hqw)
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hc
      · rw [← h1, ← h2]; exact onClique_symm hc

/-- **El UP conserva `EdgeClique`**: sin ventanas saltadas y sobre un estado sin `dirty`, el review del UP no
corre. -/
theorem edgeClique_up {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (h : EdgeClique g) (hpos : 0 < g.current_step) (hskip : g.skipsWindow d forb = false)
    (hd : d.step = g.current_step) (hbelow : ∀ m ∈ g.nodes, m.id.id.step < g.current_step)
    (hdocs : ∀ m ∈ g.nodes, m.id ∈ g.alive) (hclean : g.dirty = false) :
    EdgeClique (g.up d title forb) := by
  unfold up
  split
  · have hnd : (g.addNode d title forb).dirty = false := by
      show (g.dirty || g.skipsWindow d forb) = false
      rw [hclean, hskip]; rfl
    unfold review
    rw [reviewFuel_of_clean hnd]
    exact edgeClique_addNode h hpos hskip hd hbelow hdocs
  · exact h

end GPathB

end AbsSatBingo.Model
