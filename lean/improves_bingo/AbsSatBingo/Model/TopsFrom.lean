-- lean/improves_bingo/AbsSatBingo/Model/TopsFrom.lean
import AbsSatBingo.Model.StarLocal

/-!
# De dónde vienen las cimas: `TopsFrom` y `TopsSep`

* **`TopsFrom g A`**: toda cima viva de `g` tiene como `parent_id` un nodo del mapa de `A`.
* La fila nueva: las cimas de `f.addNode d` vienen de los ids de las cimas de `f` (`topsFrom_addNode`); si `f` tiene
  un solo nodo del mapa en su cima (su clave), vienen de ese.
* La conservan la selección y el review (`RevPrims`) y el join (con la unión de los conjuntos).
* **`topsSep_of_from`**: si las cimas de los dos lados vienen de conjuntos disjuntos, ninguna está en los dos.

Lo que falta para `TopsSep` en la máquina es de la línea: que las llegadas a un mismo nodo del mapa vengan de
emisores distintos (cada estado de la línea envía una vez a cada hijo).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Machine (Below mapId_of_mem_shiftRowIds)

def TopsFrom (g : GPathB) (A : NodeId → Prop) : Prop :=
  ∀ t ∈ g.alive, t.id.step = g.current_step - 1 → ∃ a, A a ∧ t.parent_id = some a

theorem revPrims_topsFrom (A : NodeId → Prop) : RevPrims (fun g => TopsFrom g A) := by
  refine ⟨fun g id hg t ht h1 => hg t (sub_killVertex g id |>.alive t ht) h1,
    fun g x w hg t ht h1 => hg t ht h1,
    fun g id hg t ht h1 => hg t (sub_removeNode g id |>.alive t ht) h1,
    fun g b hg => hg, fun g hg t ht h1 => ?_⟩
  have ⟨ha, _, hs⟩ := pruneLinks_graph g
  exact hg t (ha ▸ ht) (hs ▸ h1)

theorem topsFrom_join {e g : GPathB} {A B : NodeId → Prop} (he : TopsFrom e A) (hg : TopsFrom g B)
    (hcs : e.current_step = g.current_step) : TopsFrom (join e g) (fun a => A a ∨ B a) := by
  intro t ht h1
  have hj : (join e g).current_step = e.current_step := rfl
  rcases (alive_join e g t).mp ht with h | h
  · obtain ⟨a, ha, hp⟩ := he t h (hj ▸ h1); exact ⟨a, Or.inl ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := hg t h (hcs ▸ hj ▸ h1); exact ⟨a, Or.inr ha, hp⟩

/-- Los documentos de la cima de `g` son todos del nodo del mapa `k` (un estado de la línea en la clave `k`). -/
def TopDocsId (g : GPathB) (k : NodeId) : Prop := ∀ n ∈ g.nodes, n.id.id.step = g.current_step - 1 → n.id.id = k

theorem topsSep_of_from {e g : GPathB} {A B : NodeId → Prop} (he : TopsFrom e A) (hg : TopsFrom g B)
    (hcs : e.current_step = g.current_step) (hdis : ∀ a, A a → B a → False) : TopsSep e g := by
  intro t h1 hte htg
  obtain ⟨a, ha, hpa⟩ := he t hte h1
  obtain ⟨b, hb, hpb⟩ := hg t htg (hcs ▸ h1)
  rw [hpa] at hpb
  cases hpb
  exact hdis a ha hb

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **Las cimas de la fila nueva vienen de la clave del estado de partida.** -/
theorem topsFrom_addNode (hdocs : AliveDocs g) (hb : Below g) (hd : d.step = g.current_step)
    (hpos : 0 < g.current_step) {k : NodeId} (hk : TopDocsId g k) :
    TopsFrom (g.addNode d title forb) (fun a => a = k) := by
  intro t ht h1
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  rcases alive_addNode_cases (title := title) hdocs hb hd ht with ⟨_, h⟩ | ⟨hn, _⟩
  · omega
  · obtain ⟨q, hq, rfl⟩ := parent_of_row hpos hn
    obtain ⟨n, hn', hnq, hqs⟩ := step_of_newParents (rowParents_sub hq)
    refine ⟨q.id, ?_, rfl⟩
    rw [← hnq]
    exact hk n hn' (by rw [hnq]; exact hqs)

/-- La fila nueva tiene sus documentos de cima en el nodo del mapa `d`. -/
theorem topDocsId_addNode (hb : Below g) : TopDocsId (g.addNode d title forb) d := by
  intro n hn h1
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  rcases List.mem_append.mp hn with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    have := hb m hm
    have h2 : m.id.id.step = g.current_step + 1 - 1 := h1
    omega
  · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp h
    exact mapId_of_mem_shiftRowIds (List.mem_filter.mp hpid).1

-- ============================================================
-- (A) La subida por el UP
-- ============================================================

/-- **(A) La subida**: si el padre `p` de una cima nueva `t` está en el núcleo del estado de partida fijado en `P`
(y `P` fija en el paso nuevo, como mucho, el nodo del mapa de la fila), `t` está en el núcleo del UP fijado igual:
la camarilla de `p` (por `TopExact`) se alarga con `t`. -/
theorem kernel_addNode_of_parent (hk : TopExact g) (hb : Below g) (hpos : 0 < g.current_step)
    (hd : d.step = g.current_step) {P : List NodeId} {p t : PathNodeId} (hp : p ∈ g.rowParents d t)
    (ht : t ∈ g.newRowIds d forb) (hP : ∀ r ∈ P, r.step = g.current_step → r = d) (hker : Kernel g P p p) :
    Kernel (g.addNode d title forb) P t t := by
  obtain ⟨_, _, _, hps⟩ := step_of_newParents (rowParents_sub hp)
  obtain ⟨S, hc, hag, hpS⟩ := hk P p hps hker
  have htop := top_of_onS hc hpS hps
  obtain ⟨hc', hag', _, hn'⟩ := extend_through (title := title) hc hpos hb hd hag hP ht (by rw [htop]; exact hp)
  exact kernel_of_clique hc' hag' hn' hn'

/-- **(A) con el review**: lo mismo en el estado revisado `review (addNode g d)`, que es el UP de la máquina. -/
theorem kernel_up_of_parent (hk : TopExact g) (hb : Below g) (hpos : 0 < g.current_step)
    (hd : d.step = g.current_step) {P : List NodeId} {p t : PathNodeId} (hp : p ∈ g.rowParents d t)
    (ht : t ∈ g.newRowIds d forb) (hP : ∀ r ∈ P, r.step = g.current_step → r = d) (hker : Kernel g P p p) :
    Kernel (g.addNode d title forb).review P t t := by
  obtain ⟨V, R, hst, ha, hr⟩ := kernel_addNode_of_parent (title := title) hk hb hpos hd hp ht hP hker
  exact ⟨V, R, secStruct_review hst, ha, hr⟩

end GPathB

end AbsSatBingo.Model
