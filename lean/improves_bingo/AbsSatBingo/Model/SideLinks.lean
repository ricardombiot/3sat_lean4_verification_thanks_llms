-- lean/improves_bingo/AbsSatBingo/Model/SideLinks.lean
import AbsSatBingo.Model.UnionSplit
import AbsSatBingo.Model.Bookkeeping
import AbsSatBingo.Model.KernelUp

/-!
# Los enlaces completos (`LinksInv`)

Un enlace padre/hijo solo une nodos compatibles por sus ids (`Compat p y`: `y` es un desplazamiento de `p`), y todo
par compatible de vivos que se poseen está enlazado (`LinksComplete`). Lo conservan el review (`RevPrims`), la
fila nueva y el join. Sirve para pasar las reglas de enlace de una estructura cerrada de la unión a un lado.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (shiftPid)

namespace GPathB

open Machine (Below mapId_of_mem_shiftRowIds aliveDocs_addNode aliveDocs_join)

/-- `y` puede ser hijo de `p`: sus ids encajan como un desplazamiento de la ventana. -/
def Compat (p y : PathNodeId) : Prop :=
  y.parent_id = some p.id ∧ y.gparent_id = p.parent_id ∧ p.id.step + 1 = y.id.step

/-- Los enlaces solo unen nodos compatibles. -/
def LinksCompat (g : GPathB) : Prop :=
  ∀ n ∈ g.nodes, (∀ p ∈ n.parents, Compat p n.id) ∧ (∀ s ∈ n.sons, Compat n.id s)

/-- Todo par compatible de vivos que se poseen está enlazado. -/
def LinksComplete (g : GPathB) : Prop :=
  ∀ n ∈ g.nodes, ∀ p ∈ g.alive, g.Adj n.id p → (Compat p n.id → p ∈ n.parents) ∧ (Compat n.id p → p ∈ n.sons)

def LinksInv (g : GPathB) : Prop := AliveDocs g ∧ LinksComplete g ∧ LinksCompat g

theorem linksInv_of_sub_same_nodes {g h : GPathB} (hs : Sub h g) (hn : h.nodes = g.nodes) (hg : LinksInv g) :
    LinksInv h := by
  obtain ⟨hd, hc, hk⟩ := hg
  refine ⟨fun q hq => ?_, fun n hnm p hp ha => ?_, fun n hnm => ?_⟩
  · -- los vivos de `h` son de `g`
    obtain ⟨m, hm, rfl⟩ := hd q (hs.alive q hq); exact ⟨m, hn ▸ hm, rfl⟩
  · exact hc n (hn ▸ hnm) p (hs.alive p hp) (hs.adj _ _ ha)
  · exact hk n (hn ▸ hnm)

theorem node?_isSome_of_mem {g : GPathB} {n : PNodeB} (hn : n ∈ g.nodes) : (g.node? n.id).isSome = true := by
  unfold node?
  rw [List.find?_isSome]
  exact ⟨n, hn, by simp⟩

theorem revPrims_linksInv : RevPrims LinksInv := by
  refine ⟨fun g id hg => linksInv_of_sub_same_nodes (sub_killVertex g id) rfl hg,
    fun g x w hg => linksInv_of_sub_same_nodes (sub_removeEdge g x w) rfl hg, ?_,
    fun g b hg => hg, ?_⟩
  · intro g id hg
    obtain ⟨hd, hc, hk⟩ := hg
    have hs := sub_removeNode g id
    refine ⟨aliveDocs_removeNode hd id, ?_, ?_⟩
    · intro n hn p hp ha
      simp only [removeNode, killVertex, List.mem_map, List.mem_filter] at hn
      obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hn
      have hpid : p ≠ id := by
        have := (List.mem_filter.mp hp).2; simpa using this
      obtain ⟨h1, h2⟩ := hc m hm p (hs.alive p hp) (hs.adj _ _ ha)
      refine ⟨fun hcp => List.mem_filter.mpr ⟨h1 hcp, bne_iff_ne.mpr hpid⟩,
        fun hcp => List.mem_filter.mpr ⟨h2 hcp, bne_iff_ne.mpr hpid⟩⟩
    · intro n hn
      simp only [removeNode, killVertex, List.mem_map, List.mem_filter] at hn
      obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hn
      obtain ⟨h1, h2⟩ := hk m hm
      exact ⟨fun p hp => h1 p (List.mem_filter.mp hp).1, fun s hs => h2 s (List.mem_filter.mp hs).1⟩
  · intro g hg
    obtain ⟨hd, hc, hk⟩ := hg
    unfold pruneLinks
    split
    · refine ⟨fun q hq => ?_, fun n hn p hp ha => ?_, fun n hn => ?_⟩
      · obtain ⟨m, hm, rfl⟩ := hd q hq
        exact ⟨_, List.mem_map.mpr ⟨m, hm, rfl⟩, rfl⟩
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
        obtain ⟨h1, h2⟩ := hc m hm p hp ha
        have hlk : g.linkOk m.id p = true := by
          obtain ⟨q, hq, hqid⟩ := hd p hp
          unfold linkOk
          rw [← hqid, node?_isSome_of_mem hq]
          exact Bool.and_eq_true_iff.mpr ⟨rfl, hqid ▸ ha⟩
        exact ⟨fun hcp => List.mem_filter.mpr ⟨h1 hcp, hlk⟩, fun hcp => List.mem_filter.mpr ⟨h2 hcp, hlk⟩⟩
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
        obtain ⟨h1, h2⟩ := hk m hm
        exact ⟨fun p hp => h1 p (List.mem_filter.mp hp).1, fun s hs => h2 s (List.mem_filter.mp hs).1⟩
    · exact ⟨hd, hc, hk⟩

-- ============================================================
-- La fila nueva
-- ============================================================

theorem shiftPid_of_compat {q pid : PathNodeId} {d : NodeId} (hc : Compat q pid) (hid : pid.id = d) :
    shiftPid q d = pid := by
  obtain ⟨h1, h2, _⟩ := hc
  cases pid
  simp only at h1 h2 hid
  subst hid; rw [h1, h2]; rfl

theorem compat_of_shiftPid {q pid : PathNodeId} {d : NodeId} (h : shiftPid q d = pid) (hq : q.id.step + 1 = d.step) :
    Compat q pid := by
  subst h
  exact ⟨rfl, rfl, hq⟩

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

theorem compat_rowParents (hd : d.step = g.current_step) {pid q : PathNodeId} (hq : q ∈ g.rowParents d pid) :
    Compat q pid := by
  have ⟨h1, h2⟩ := List.mem_filter.mp hq
  obtain ⟨_, _, _, hs⟩ := step_of_newParents h1
  refine compat_of_shiftPid (beq_iff_eq.mp h2) ?_
  have hds := hd
  have hpos : 0 < g.current_step := by
    unfold newParents at h1; split at h1
    · assumption
    · simp at h1
  omega

theorem linksInv_addNode (hg : LinksInv g) (hb : Below g) (hz : AboveZero g) (hd : d.step = g.current_step) :
    LinksInv (g.addNode d title forb) := by
  obtain ⟨hdocs, hc, hk⟩ := hg
  refine ⟨aliveDocs_addNode hdocs, ?_, ?_⟩
  · intro n hn p hp ha
    rcases alive_addNode_cases hdocs hb hd hp with ⟨hpo, hps⟩ | ⟨hpn, hps⟩
    · rcases List.mem_append.mp hn with hn | hn
      · -- nodo viejo, vivo viejo
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
        have hms := hb m hm
        obtain ⟨h1, h2⟩ := hc m hm p hpo (adj_addNode_old hd hms hps ha)
        exact ⟨h1, fun hcp => List.mem_append_left _ (h2 hcp)⟩
      · -- nodo nuevo, vivo viejo: solo puede ser su padre
        obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp hn
        have hpids := newRow_step hd hpid
        refine ⟨fun hcp => ?_, fun hcp => ?_⟩
        · show p ∈ g.rowParents d pid
          obtain ⟨m, hm, rfl⟩ := hdocs p hpo
          have h3 : m.id.id.step + 1 = pid.id.step := hcp.2.2
          have hpos : 0 < g.current_step := by have := hz m hm; omega
          refine List.mem_filter.mpr ⟨mem_newParents hpos hm (by omega), ?_⟩
          exact beq_iff_eq.mpr (shiftPid_of_compat hcp (mapId_of_mem_shiftRowIds (List.mem_filter.mp hpid).1))
        · exfalso; have h3 : pid.id.step + 1 = p.id.step := hcp.2.2; omega
    · rcases List.mem_append.mp hn with hn | hn
      · -- nodo viejo, vivo nuevo: solo puede ser su hijo
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
        have hms := hb m hm
        refine ⟨fun hcp => ?_, fun hcp => ?_⟩
        · exfalso; have h3 : p.id.step + 1 = m.id.id.step := hcp.2.2; omega
        · show p ∈ m.sons ++ g.gainedSons d forb m
          have h3 : m.id.id.step + 1 = p.id.step := hcp.2.2
          have hpos : 0 < g.current_step := by have := hz m hm; omega
          have hmp := mem_newParents hpos hm (by omega)
          refine List.mem_append_right _ (List.mem_filter.mpr ⟨hpn, List.contains_iff_mem.mpr ?_⟩)
          refine List.mem_filter.mpr ⟨hmp, beq_iff_eq.mpr ?_⟩
          exact shiftPid_of_compat hcp (mapId_of_mem_shiftRowIds (List.mem_filter.mp hpn).1)
      · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp hn
        have hpids := newRow_step hd hpid
        have hps' := newRow_step hd hpn
        refine ⟨fun hcp => ?_, fun hcp => ?_⟩
        · exfalso; have h3 : p.id.step + 1 = pid.id.step := hcp.2.2; omega
        · exfalso; have h3 : pid.id.step + 1 = p.id.step := hcp.2.2; omega
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      obtain ⟨h1, h2⟩ := hk m hm
      refine ⟨h1, fun s hs => ?_⟩
      rcases List.mem_append.mp hs with hs | hs
      · exact h2 s hs
      · have ⟨hs1, hs2⟩ := List.mem_filter.mp hs
        exact compat_rowParents hd (List.contains_iff_mem.mp hs2)
    · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp hn
      exact ⟨fun p hp => compat_rowParents hd hp, fun s hs => by simp [rowNode] at hs⟩

-- ============================================================
-- El join
-- ============================================================

theorem node?_isSome_of_alive {g : GPathB} (hd : AliveDocs g) {q : PathNodeId} (hq : q ∈ g.alive) :
    (g.node? q).isSome = true := by
  obtain ⟨n, hn, rfl⟩ := hd q hq
  exact node?_isSome_of_mem hn

theorem mem_merge_parents_left {a b : PNodeB} {p : PathNodeId} (h : p ∈ a.parents) : p ∈ (mergeNode a b).parents :=
  List.mem_append_left _ h

theorem mem_merge_sons_left {a b : PNodeB} {p : PathNodeId} (h : p ∈ a.sons) : p ∈ (mergeNode a b).sons :=
  List.mem_append_left _ h

theorem merge_parents_cases {a b : PNodeB} {p : PathNodeId} (h : p ∈ (mergeNode a b).parents) :
    p ∈ a.parents ∨ p ∈ b.parents := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.mp h).1

theorem merge_sons_cases {a b : PNodeB} {p : PathNodeId} (h : p ∈ (mergeNode a b).sons) :
    p ∈ a.sons ∨ p ∈ b.sons := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.mp h).1

/-- Los nodos de la unión: uno de `e` (fundido con el de `g` si `g` lo tiene) o uno de `g` que `e` no tiene. -/
theorem mem_join_nodes {e g : GPathB} {n : PNodeB} (hn : n ∈ (join e g).nodes) :
    (∃ m ∈ e.nodes, g.node? m.id = none ∧ n = m) ∨
    (∃ m ∈ e.nodes, ∃ m', g.node? m.id = some m' ∧ n = mergeNode m m') ∨
    (n ∈ g.nodes ∧ e.node? n.id = none) := by
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    cases hg : g.node? m.id with
    | none => exact Or.inl ⟨m, hm, hg, by simp⟩
    | some m' => exact Or.inr (Or.inl ⟨m, hm, m', hg, by simp⟩)
  · have ⟨h1, h2⟩ := List.mem_filter.mp hn
    exact Or.inr (Or.inr ⟨h1, Option.isNone_iff_eq_none.mp h2⟩)

theorem linksInv_join {e g : GPathB} (he : LinksInv e) (hg : LinksInv g) (hee : EdgesAlive e)
    (heg : EdgesAlive g) : LinksInv (join e g) := by
  obtain ⟨hde, hce, hke⟩ := he
  obtain ⟨hdg, hcg, hkg⟩ := hg
  refine ⟨aliveDocs_join hde hdg, ?_, ?_⟩
  · intro n hn p _ ha
    rcases adj_join_cases ha with ha | ha
    · -- la posesión es de `e`: el nodo es de `e`
      have ⟨hy, hp⟩ := hee _ _ ha
      rcases mem_join_nodes hn with ⟨m, hm, _, rfl⟩ | ⟨m, hm, m', _, rfl⟩ | ⟨_, hnone⟩
      · exact hce n hm p hp ha
      · obtain ⟨h1, h2⟩ := hce m hm p hp ha
        exact ⟨fun hc => mem_merge_parents_left (h1 hc), fun hc => mem_merge_sons_left (h2 hc)⟩
      · have := node?_isSome_of_alive hde hy; rw [hnone] at this; simp at this
    · -- la posesión es de `g`: el nodo es de `g`
      have ⟨hy, hp⟩ := heg _ _ ha
      rcases mem_join_nodes hn with ⟨m, hm, hnone, rfl⟩ | ⟨m, hm, m', hm', rfl⟩ | ⟨hn', _⟩
      · have := node?_isSome_of_alive hdg hy; rw [hnone] at this; simp at this
      · have hid := node?_id hm'
        have hmem := node?_mem hm'
        obtain ⟨h1, h2⟩ := hcg m' hmem p hp (hid ▸ ha)
        refine ⟨fun hc => mem_merge_parents (h1 (hid ▸ hc)), fun hc => mem_merge_sons (h2 (hid ▸ hc))⟩
      · exact hcg n hn' p hp ha
  · intro n hn
    rcases mem_join_nodes hn with ⟨m, hm, _, rfl⟩ | ⟨m, hm, m', hm', rfl⟩ | ⟨hn', _⟩
    · exact hke n hm
    · have hid := node?_id hm'
      obtain ⟨h1, h2⟩ := hke m hm
      obtain ⟨h1', h2'⟩ := hkg m' (node?_mem hm')
      refine ⟨fun p hp => ?_, fun s hs => ?_⟩
      · rcases merge_parents_cases hp with hp | hp
        · exact h1 p hp
        · have := h1' p hp; rw [hid] at this; exact this
      · rcases merge_sons_cases hs with hs | hs
        · exact h2 s hs
        · have := h2' s hs; rw [hid] at this; exact this
    · exact hkg n hn'

-- ============================================================
-- `SidePinned` se reduce a las parejas
-- ============================================================

/-- `u` es una unión de `e` y `g` vista desde `e` (el join lo es desde los dos lados). -/
structure IsUnion (u e g : GPathB) : Prop where
  step   : u.current_step = e.current_step
  adj    : ∀ {y w}, u.Adj y w → e.Adj y w ∨ g.Adj y w
  docs   : AliveDocs u
  compat : LinksCompat u

theorem isUnion_join_left {e g : GPathB} (hle : LinksInv e) (hlg : LinksInv g) (hee : EdgesAlive e)
    (heg : EdgesAlive g) : IsUnion (join e g) e g :=
  have h := linksInv_join hle hlg hee heg
  ⟨rfl, adj_join_cases, h.1, h.2.2⟩

theorem isUnion_join_right {e g : GPathB} (hcs : e.current_step = g.current_step) (hle : LinksInv e)
    (hlg : LinksInv g) (hee : EdgesAlive e) (heg : EdgesAlive g) : IsUnion (join e g) g e :=
  have h := linksInv_join hle hlg hee heg
  ⟨hcs, fun ha => (adj_join_cases ha).symm, h.1, h.2.2⟩

/-- **Lo que queda de `SidePinned`**: fijada en `b`, las parejas de toda estructura cerrada de la unión son
posesiones del lado `e`. -/
def SideEdges (u e : GPathB) (b : NodeId) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R → SecAgrees V b →
    ∀ {y w}, R y w → e.Adj y w

/-- Fijada en un nodo del mapa muerto en `g`, toda estructura cerrada de la unión vive en `e`. -/
theorem alive_side {u e g : GPathB} (hu : IsUnion u e g) {V : PathNodeId → Prop}
    {R : PathNodeId → PathNodeId → Prop} {b : NodeId} (hst : SecStruct u V R) (ha : SecAgrees V b)
    (hb0 : 0 ≤ b.step) (hbc : b.step < e.current_step) (hoff : OffSide g b) (hee : EdgesAlive e)
    (heg : EdgesAlive g) {y : PathNodeId} (hy : V y) : y ∈ e.alive := by
  obtain ⟨r, hrs, hyr, _⟩ := hst.pair (hst.refl hy) b.step hb0 (hu.step ▸ hbc)
  have hrg : r ∉ g.alive := fun h => hoff r h (ha (hst.dom hyr).2 hrs)
  rcases hu.adj (hst.adj hyr) with h | h
  · exact (hee y r h).1
  · exact absurd (heg y r h).2 hrg

/-- Un enlace de la unión hacia un vivo de `e` que `e` posee es un enlace de `e`. -/
theorem link_side {u e : GPathB} (he : LinksInv e) (hku : LinksCompat u) {n nu : PNodeB}
    (hn : n ∈ e.nodes) (hnu : nu ∈ u.nodes) (hid : nu.id = n.id) {p : PathNodeId} (hp : p ∈ e.alive)
    (ha : e.Adj n.id p) : (p ∈ nu.parents → p ∈ n.parents) ∧ (p ∈ nu.sons → p ∈ n.sons) := by
  obtain ⟨h1, h2⟩ := he.2.1 n hn p hp ha
  obtain ⟨k1, k2⟩ := hku nu hnu
  exact ⟨fun hq => h1 (hid ▸ k1 p hq), fun hq => h2 (hid ▸ k2 p hq)⟩

/-- **Con `SideEdges`, toda estructura cerrada de la unión que concuerda con `b` es una estructura de `e`**
(con la separación, los enlaces completos y las posesiones entre vivos). -/
theorem secStruct_side {u e g : GPathB} (hu : IsUnion u e g) {V : PathNodeId → Prop}
    {R : PathNodeId → PathNodeId → Prop} {b : NodeId} (hst : SecStruct u V R) (ha : SecAgrees V b)
    (hb0 : 0 ≤ b.step) (hbc : b.step < e.current_step) (hoff : OffSide g b) (hle : LinksInv e)
    (hee : EdgesAlive e) (heg : EdgesAlive g) (hse : SideEdges u e b) : SecStruct e V R := by
  have hal : ∀ {y}, V y → y ∈ e.alive := fun hy => alive_side hu hst ha hb0 hbc hoff hee heg hy
  have hadj : ∀ {y w}, R y w → e.Adj y w := fun h => hse V R hst ha h
  have hnode : ∀ {x}, V x → ∃ nu, u.node? x = some nu := fun hx =>
    Option.isSome_iff_exists.mp (node?_isSome_of_alive hu.docs (hst.alive hx))
  have hstep := hu.step
  refine ⟨hal, hst.refl, hst.symm, hst.dom, hadj, fun h l h0 h1 => hst.pair h l h0 (hstep ▸ h1), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hle.1 (hal hy))
    obtain ⟨nu, hnu, hpar, hson⟩ := hst.node hy
    have hnid := node?_id hn
    have hl : ∀ {p}, R y p → (p ∈ nu.parents → p ∈ n.parents) ∧ (p ∈ nu.sons → p ∈ n.sons) := fun {p} hyp =>
      link_side hle hu.compat (node?_mem hn) (node?_mem hnu) ((node?_id hnu).trans hnid.symm)
        (hal (hst.dom hyp).2) (hnid ▸ hadj hyp)
    refine ⟨n, hn, fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨p, hp, hyp⟩ := hpar hk; exact ⟨p, (hl hyp).1 hp, hyp⟩
    · obtain ⟨s, hs, hys⟩ := hson (hstep ▸ hk); exact ⟨s, (hl hys).2 hs, hys⟩
  · intro x w n hxw hne hn h1
    obtain ⟨nu, hnu⟩ := hnode (hst.dom hxw).1
    obtain ⟨p, hp, hxp, hpw⟩ := hst.par hxw hne hnu h1
    have hnid := node?_id hn
    exact ⟨p, (link_side hle hu.compat (node?_mem hn) (node?_mem hnu) ((node?_id hnu).trans hnid.symm)
      (hal (hst.dom hxp).2) (hnid ▸ hadj hxp)).1 hp, hxp, hpw⟩
  · intro x w n hxw hne hn h1
    obtain ⟨nu, hnu⟩ := hnode (hst.dom hxw).1
    obtain ⟨s, hs, hxs, hsw⟩ := hst.son hxw hne hnu (hstep ▸ h1)
    have hnid := node?_id hn
    exact ⟨s, (link_side hle hu.compat (node?_mem hn) (node?_mem hnu) ((node?_id hnu).trans hnid.symm)
      (hal (hst.dom hxs).2) (hnid ▸ hadj hxs)).2 hs, hxs, hsw⟩

/-- El núcleo de la unión fijado en `b` es el de `e`, bajo `SideEdges`. -/
theorem kernel_side {u e g : GPathB} (hu : IsUnion u e g) {b : NodeId} (hb0 : 0 ≤ b.step)
    (hbc : b.step < e.current_step) (hoff : OffSide g b) (hle : LinksInv e) (hee : EdgesAlive e)
    (heg : EdgesAlive g) (hse : SideEdges u e b) {P : List NodeId} {y w : PathNodeId}
    (hk : Kernel u (P ++ [b]) y w) : Kernel e (P ++ [b]) y w := by
  obtain ⟨V, R, hst, hag, hr⟩ := hk
  have ha : SecAgrees V b := hag b (List.mem_append_right _ (List.mem_singleton_self b))
  exact ⟨V, R, secStruct_side hu hst ha hb0 hbc hoff hle hee heg hse, hag, hr⟩

/-- Separación por el origen: ningún nodo del mapa del paso `k` está vivo en los dos lados. -/
def SepAt (e g : GPathB) (k : Int) : Prop := ∀ b : NodeId, b.step = k → OffSide g b ∨ OffSide e b

/-- Las parejas de la unión fijada en un nodo del mapa de `k` son del lado que lo tiene. -/
def SideEdgesAt (e g : GPathB) (k : Int) : Prop :=
  ∀ b : NodeId, b.step = k → (OffSide g b → SideEdges (join e g) e b) ∧ (OffSide e b → SideEdges (join e g) g b)

/-- **`SidePinned` ⇐ separación + `SideEdgesAt`** (con los enlaces completos). -/
theorem sidePinned_of_sideEdges {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hle : LinksInv e) (hlg : LinksInv g) (hee : EdgesAlive e)
    (heg : EdgesAlive g) (hsep : SepAt e g k) (hse : SideEdgesAt e g k) : SidePinned (join e g) e g k := by
  intro b hb
  rcases hsep b hb with hoff | hoff
  · exact Or.inl (fun P y w h => kernel_side (isUnion_join_left hle hlg hee heg) (hb ▸ hk0) (hb ▸ hkc) hoff hle
      hee heg ((hse b hb).1 hoff) h)
  · exact Or.inr (fun P y w h => kernel_side (isUnion_join_right hcs hle hlg hee heg) (hb ▸ hk0)
      (hcs ▸ hb ▸ hkc) hoff hlg heg hee ((hse b hb).2 hoff) h)

/-- **`KernelUnion` ⇐ `SplitAt` + separación + `SideEdgesAt`.** -/
theorem kernelUnion_of_sideEdges {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hle : LinksInv e) (hlg : LinksInv g) (hee : EdgesAlive e)
    (heg : EdgesAlive g) (hs : SplitAt (join e g) k) (hsep : SepAt e g k) (hse : SideEdgesAt e g k) :
    KernelUnion e g :=
  kernelUnion_of_split hs (sidePinned_of_sideEdges hk0 hkc hcs hle hlg hee heg hsep hse)

end GPathB

end AbsSatBingo.Model
