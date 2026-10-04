-- lean/improves_bingo/AbsSatBingo/Model/KernelSkip.lean
import AbsSatBingo.Model.ClosedReview

/-!
# La fila nueva con ventana saltada: `skip` se reduce a `AvoidExact`

Con una ventana prohibida, la fila nueva no tiene hijo para los nodos de la cima cuya ventana está prohibida, y una
camarilla que acabe en ellos no se alarga. La prueba del UP (`KernelUp.lean`) vale igual salvo en el caso de dos
nodos viejos, que necesita una camarilla del estado anterior **con cima de hijo permitido**:

* **`AvoidExact g d forb`** (hipótesis): toda pareja de una estructura cerrada de `g` que concuerda con `P` y cuyos
  nodos de la cima tienen todos hijo permitido está en una camarilla de `g` por `P` con cima de hijo permitido.
  Sin ventana saltada es consecuencia de `KernelExact` (`avoidExact_of_noSkip`). Con ventana saltada es una
  propiedad de unión: evitar la ventana (⟨c-1,0⟩, ⟨c-2,0⟩) es la unión de dos pins, y `AvoidExact` pide que el
  núcleo de esa unión sea la unión de los núcleos, la misma forma que `KernelUnion` en el join.
* **`kernelExact_addNode_gen`**: `KernelExact` y `AvoidExact` dan `KernelExact` en la fila nueva, con o sin salto.

Contabilidad nueva: `TopNoSons` (los documentos de la cima aún no tienen hijos).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Machine (Below mapId_of_mem_shiftRowIds)

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- Los documentos de la cima aún no tienen hijos. -/
def TopNoSons (g : GPathB) : Prop := ∀ n ∈ g.nodes, n.id.id.step + 1 = g.current_step → n.sons = []

/-- Los nodos de la cima de `V` tienen hijo permitido. -/
def GoodTops (g : GPathB) (d : NodeId) (forb : PathNodeId → Bool) (V : PathNodeId → Prop) : Prop :=
  ∀ q, V q → q.id.step = g.current_step - 1 → forb (shiftPid q d) = false

/-- **Hipótesis**: una estructura cerrada con cimas de hijo permitido tiene sus parejas en camarillas con cima de
hijo permitido. -/
def AvoidExact (g : GPathB) (d : NodeId) (forb : PathNodeId → Bool) : Prop :=
  ∀ (P : List NodeId) y w (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct g V R → (∀ b ∈ P, SecAgrees V b) → GoodTops g d forb V → R y w →
    ∃ S, Carried g S ∧ (∀ r ∈ P, Agrees g.current_step S r) ∧ OnS g.current_step S y ∧ OnS g.current_step S w ∧
      forb (shiftPid (S (g.current_step - 1)) d) = false

/-- El hijo de un padre candidato cuya ventana está permitida está en la fila. -/
theorem son_in_row_of (hpos : 0 < g.current_step) {q : PathNodeId} (hq : q ∈ g.newParents)
    (hf : forb (shiftPid q d) = false) :
    shiftPid q d ∈ g.newRowIds d forb ∧ q ∈ g.rowParents d (shiftPid q d) := by
  have hmem : shiftPid q d ∈ g.shiftRowIds d := by
    unfold shiftRowIds
    rw [if_pos hpos, mem_dedupPids]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  exact ⟨List.mem_filter.mpr ⟨hmem, by simp [hf]⟩, List.mem_filter.mpr ⟨hq, by simp⟩⟩

/-- **Sin ventana saltada, `AvoidExact` sale de `KernelExact`.** -/
theorem avoidExact_of_noSkip (hk : KernelExact g) (hpos : 0 < g.current_step)
    (hskip : g.skipsWindow d forb = false) : AvoidExact g d forb := by
  intro P y w V R hst ha _ hr
  obtain ⟨S, hc, hag, hy, hw⟩ := hk P y w ⟨V, R, hst, ha, hr⟩
  refine ⟨S, hc, hag, hy, hw, ?_⟩
  have hmem : shiftPid (S (g.current_step - 1)) d ∈ g.shiftRowIds d := by
    unfold shiftRowIds
    rw [if_pos hpos, mem_dedupPids]
    exact List.mem_map.mpr ⟨_, top_newParents hc hpos, rfl⟩
  unfold skipsWindow at hskip
  exact List.any_eq_false.mp hskip _ hmem |> fun h => by simpa using h

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- **La fila nueva conserva `KernelExact`**, con o sin ventana saltada, bajo `AvoidExact`. -/
theorem kernelExact_addNode_gen (hk : KernelExact g) (hav : AvoidExact g d forb) (hdocs : AliveDocs g)
    (hb : Below g) (hls : LinksStep g) (hea : EdgesAlive g) (htop0 : TopNoSons g) (hpos : 0 < g.current_step)
    (hd : d.step = g.current_step) : KernelExact (g.addNode d title forb) := by
  intro P y w ⟨V, R, hst, ha, hr⟩
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  have hdown := secStruct_addNode_down (title := title) (forb := forb) hdocs hb hls hd hst
  -- lo que P fija en el paso nuevo es d (en cuanto V tiene un nodo en él)
  have hP : ∀ q, V q → q.id.step = g.current_step → ∀ r ∈ P, r.step = g.current_step → r = d := by
    intro q hq hqs r hr' hrs
    have hqd : q.id = d := by
      rcases alive_addNode_cases (title := title) hdocs hb hd (hst.alive hq) with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact mapId_of_mem_shiftRowIds (List.mem_filter.mp h).1
    rw [← hqd]
    exact (ha r hr' hq (by rw [hqs, hrs])).symm
  -- un nodo de V en el paso nuevo, desde cualquier pareja (el testigo de la regla de parejas)
  have htop : ∀ {a b}, R a b → ∀ r ∈ P, r.step = g.current_step → r = d := by
    intro a b hab
    obtain ⟨q, hqs, haq, _⟩ := hst.pair hab g.current_step (by omega) (by rw [hcs]; omega)
    exact hP q (hst.dom haq).2 hqs
  -- una pareja vieja de R está en una camarilla del estado anterior que concuerda con P
  have hold : ∀ {a b}, R a b → a.id.step < g.current_step → b.id.step < g.current_step →
      ∃ S, Carried g S ∧ (∀ r ∈ P, Agrees g.current_step S r) ∧ OnS g.current_step S a ∧ OnS g.current_step S b := by
    intro a b hab h1 h2
    exact hk P a b ⟨_, _, hdown, fun r hr' q hq hqs => ha r hr' hq.1 hqs, hab, h1, h2⟩
  -- un nodo nuevo `n` y un padre suyo `p` con `R p b`: la camarilla de (p, b) alargada con `n`
  have hnew : ∀ {n p b}, n ∈ g.newRowIds d forb → p ∈ g.rowParents d n → R n p → R p b →
      b.id.step < g.current_step →
      ∃ S, Carried (g.addNode d title forb) S ∧ (∀ r ∈ P, Agrees (g.addNode d title forb).current_step S r) ∧
        OnS (g.addNode d title forb).current_step S n ∧ OnS (g.addNode d title forb).current_step S b := by
    intro n p b hn hp hnp hpb hbs
    obtain ⟨_, _, _, hps⟩ := step_of_newParents (rowParents_sub hp)
    obtain ⟨S, hc, hag, hpS, hbS⟩ := hold hpb (by omega) hbs
    have htop' := top_of_onS hc hpS hps
    obtain ⟨hc', hag', hon, hn'⟩ := extend_through (title := title) hc hpos hb hd hag (htop hnp) hn
      (by rw [htop']; exact hp)
    exact ⟨_, hc', hag', hn', hon b hbS⟩
  -- los casos
  have hy := hst.alive (hst.dom hr).1
  have hw := hst.alive (hst.dom hr).2
  rcases alive_addNode_cases (title := title) hdocs hb hd hy with ⟨_, hys⟩ | ⟨hyn, hys⟩ <;>
    rcases alive_addNode_cases (title := title) hdocs hb hd hw with ⟨_, hws⟩ | ⟨hwn, hws⟩
  · -- dos viejos: una camarilla del estado anterior con cima de hijo permitido (AvoidExact), alargada
    have hgood : GoodTops g d forb (fun q => V q ∧ q.id.step < g.current_step) := by
      rintro q ⟨hq, _⟩ hqs
      obtain ⟨m, hm, _, hson⟩ := hst.node hq
      obtain ⟨s, hs, _⟩ := hson (by rw [hcs]; omega)
      rw [node?_addNode_old (title := title) hd (by omega)] at hm
      cases hn : g.node? q with
      | none => rw [hn] at hm; cases hm
      | some n =>
        rw [hn] at hm; cases hm
        have hnid := node?_id hn
        have hsons : n.sons = [] := htop0 n (node?_mem hn) (by rw [hnid]; omega)
        simp only [withGained, hsons, List.nil_append] at hs
        have ⟨hs1, hs2⟩ := List.mem_filter.mp hs
        have hqp := List.contains_iff_mem.mp hs2
        rw [hnid] at hqp
        have hsh : shiftPid q d = s := by simpa using (List.mem_filter.mp hqp).2
        rw [hsh]
        simpa using (List.mem_filter.mp hs1).2
    obtain ⟨S, hc, hag, hyS, hwS, hf⟩ := hav P y w _ _ hdown
      (fun r hr' q hq hqs => ha r hr' hq.1 hqs) hgood ⟨hr, hys, hws⟩
    obtain ⟨hn, hp⟩ := son_in_row_of (d := d) (forb := forb) hpos (top_newParents hc hpos) hf
    obtain ⟨hc', hag', hon, _⟩ := extend_through (title := title) hc hpos hb hd hag (htop hr) hn hp
    exact ⟨_, hc', hag', hon y hyS, hon w hwS⟩
  · -- y viejo, w nuevo
    have hne : w ≠ y := fun h => by rw [h] at hws; omega
    have hm := node?_addNode_new (title := title) hb hd hwn
    obtain ⟨p, hp, hwp, hpy⟩ := hst.par (hst.symm hr) hne hm (by rw [hws]; omega)
    obtain ⟨S, hc, hag, hwS, hyS⟩ := hnew hwn hp hwp hpy hys
    exact ⟨S, hc, hag, hyS, hwS⟩
  · -- y nuevo, w viejo
    have hne : y ≠ w := fun h => by rw [h] at hys; omega
    have hm := node?_addNode_new (title := title) hb hd hyn
    obtain ⟨p, hp, hyp, hpw⟩ := hst.par hr hne hm (by rw [hys]; omega)
    exact hnew hyn hp hyp hpw hws
  · -- dos nuevos: son el mismo, y la camarilla de su padre se alarga con él
    have heq := adj_addNode_new (title := title) (forb := forb) hdocs hb hea hys hws (hst.adj hr)
    subst heq
    obtain ⟨m, hm, hpar, _⟩ := hst.node (hst.dom hr).1
    rw [node?_addNode_new (title := title) hb hd hyn] at hm
    cases hm
    obtain ⟨q, _, hq⟩ := parent_of_row hpos hyn
    have hroot : y.parent_id.isNone = false := by rw [hq]; rfl
    obtain ⟨p, hp, hyp⟩ := hpar hroot
    have hps : p.id.step < g.current_step := by
      obtain ⟨_, _, _, h⟩ := step_of_newParents (rowParents_sub hp); omega
    obtain ⟨S, hc, hag, hyS, _⟩ := hnew hyn hp hyp (hst.refl (hst.dom hyp).2) hps
    exact ⟨S, hc, hag, hyS, hyS⟩

-- ============================================================
-- TopNoSons
-- ============================================================

theorem revPrims_topNoSons : RevPrims TopNoSons := by
  refine ⟨fun g id hg => hg, fun g x w hg => hg, ?_, fun g b hg => hg, ?_⟩
  · intro g id hg n hn hs
    simp only [removeNode, killVertex, List.mem_map, List.mem_filter] at hn
    obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hn
    have := hg m hm hs
    simp [unlinkAll, this]
  · intro g hg n hn hs
    rw [(pruneLinks_graph g).2.2] at hs
    unfold pruneLinks at hn
    split at hn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      have := hg m hm hs
      simp [this]
    · exact hg n hn hs

theorem topNoSons_addNode (hb : Below g) : TopNoSons (g.addNode d title forb) := by
  intro n hn hs
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have := hb m hm
    rw [hcs] at hs
    exact absurd hs (by show ¬ (m.id.id.step + 1 = g.current_step + 1); omega)
  · obtain ⟨pid, _, rfl⟩ := List.mem_map.mp hn
    rfl

theorem topNoSons_join {g₁ g₂ : GPathB} (h₁ : TopNoSons g₁) (h₂ : TopNoSons g₂)
    (hcs : g₁.current_step = g₂.current_step) : TopNoSons (join g₁ g₂) := by
  intro n hn hs
  have hjs : (join g₁ g₂).current_step = g₁.current_step := rfl
  rw [hjs] at hs
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have hs : m.id.id.step + 1 = g₁.current_step := by split at hs <;> exact hs
    split
    · rename_i m' hm'
      have hid : m'.id = m.id := node?_id hm'
      have e1 := h₁ m hm hs
      have e2 := h₂ m' (node?_mem hm') (by rw [hid, ← hcs]; exact hs)
      simp [mergeNode, e1, e2]
    · exact h₁ m hm hs
  · exact h₂ n (List.mem_filter.mp hn).1 (by rw [← hcs]; exact hs)

end GPathB

end AbsSatBingo.Model
