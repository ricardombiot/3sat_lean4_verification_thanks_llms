-- lean/improves_bingo/AbsSatBingo/Model/KernelUp.lean
import AbsSatBingo.Model.Bookkeeping

/-!
# La fila nueva conserva `KernelExact` (sin ventana saltada)

Una estructura cerrada de la fila nueva, restringida a los pasos viejos, es una estructura cerrada del estado
anterior (`kernel_addNode_down`). Así, cada pareja del núcleo de la fila nueva fijado en `P` tiene su camarilla:
* dos nodos viejos: la del estado anterior, alargada con el hijo de su cima;
* un nodo nuevo `n` y otro `w`: por el apoyo, un padre `p` de `n` con `R n p` y `R p w`; la camarilla de `(p, w)`
  se alarga con `n` (y la reflexiva de `n`, con la de `(p, p)`).

Contabilidad (hipótesis): `AliveDocs`, `Below` (todo por debajo de la cima), `LinksStep` (los padres de un documento
están en el paso anterior y sus hijos en el siguiente), sin ventana saltada, y `d` en el paso nuevo.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Machine (Below mapId_of_mem_shiftRowIds)

/-- Los enlaces van al paso de al lado. -/
def LinksStep (g : GPathB) : Prop :=
  ∀ n ∈ g.nodes, (∀ p ∈ n.parents, p.id.step + 1 = n.id.id.step) ∧ (∀ s ∈ n.sons, s.id.step = n.id.id.step + 1)

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

theorem alive_below (hd : AliveDocs g) (hb : Below g) {q : PathNodeId} (hq : q ∈ g.alive) :
    q.id.step < g.current_step := by
  obtain ⟨n, hn, rfl⟩ := hd q hq
  exact hb n hn

theorem newRow_step (hd : d.step = g.current_step) {q : PathNodeId} (hq : q ∈ g.newRowIds d forb) :
    q.id.step = g.current_step := by
  rw [mapId_of_mem_shiftRowIds (List.mem_filter.mp hq).1, hd]

theorem alive_addNode_cases (hdocs : AliveDocs g) (hb : Below g) (hd : d.step = g.current_step) {q : PathNodeId}
    (hq : q ∈ (g.addNode d title forb).alive) :
    (q ∈ g.alive ∧ q.id.step < g.current_step) ∨ (q ∈ g.newRowIds d forb ∧ q.id.step = g.current_step) := by
  rcases List.mem_append.mp hq with h | h
  · exact Or.inl ⟨h, alive_below hdocs hb h⟩
  · exact Or.inr ⟨h, newRow_step hd h⟩

/-- Entre nodos viejos, la fila nueva no añade posesiones. -/
theorem adj_addNode_old (hd : d.step = g.current_step) {y w : PathNodeId} (hy : y.id.step < g.current_step)
    (hw : w.id.step < g.current_step) (h : (g.addNode d title forb).Adj y w) : g.Adj y w := by
  rw [adj_iff] at h ⊢
  rcases h with ⟨rfl, hal⟩ | ⟨e, he, hj⟩
  · rcases List.mem_append.mp hal with h | h
    · exact Or.inl ⟨rfl, h⟩
    · rw [newRow_step hd h] at hy; exact absurd hy (Int.lt_irrefl _)
  · rcases List.mem_append.mp he with h | h
    · exact Or.inr ⟨e, h, hj⟩
    · exfalso
      obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp h
      obtain ⟨w', _, rfl⟩ := List.mem_map.mp he'
      have hs := newRow_step hd hpid
      rcases hj with ⟨h1, _⟩ | ⟨h2, _⟩
      · have e : pid = y := h1
        subst e; omega
      · have e : pid = w := h2
        subst e; omega

/-- Dos nodos nuevos distintos no se poseen. -/
theorem adj_addNode_new (hdocs : AliveDocs g) (hb : Below g) (hea : EdgesAlive g) {y w : PathNodeId}
    (hy : y.id.step = g.current_step) (hw : w.id.step = g.current_step) (h : (g.addNode d title forb).Adj y w) :
    y = w := by
  rw [adj_iff] at h
  rcases h with ⟨rfl, _⟩ | ⟨e, he, hj⟩
  · rfl
  · exfalso
    rcases List.mem_append.mp he with h | h
    · have hold : g.Adj y w := (adj_iff g y w).mpr (Or.inr ⟨e, h, hj⟩)
      -- una arista vieja une vivos viejos: por debajo de la cima
      have := alive_below hdocs hb (hea y w hold).1
      omega
    · obtain ⟨pid, _, he'⟩ := List.mem_flatMap.mp h
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
      have hlt := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hw').2).1
      simp only [decide_eq_true_eq] at hlt
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 : pid = y := h1
        have e2 : w' = w := h2
        subst e1; subst e2; omega
      · have e1 : pid = w := h1
        have e2 : w' = y := h2
        subst e1; subst e2; omega

-- ============================================================
-- Los documentos en la fila nueva
-- ============================================================

/-- El documento viejo con los hijos ganados. -/
def withGained (g : GPathB) (d : NodeId) (forb : PathNodeId → Bool) (n : PNodeB) : PNodeB :=
  { n with sons := n.sons ++ g.gainedSons d forb n }

theorem node?_addNode_old (hd : d.step = g.current_step) {y : PathNodeId}
    (hy : y.id.step < g.current_step) :
    (g.addNode d title forb).node? y = (g.node? y).map (g.withGained d forb) := by
  show List.find? _ (g.nodes.map (g.withGained d forb) ++ (g.newRowIds d forb).map (g.rowNode d title)) = _
  rw [List.find?_append, find?_map_id (g.withGained d forb) (fun _ => rfl)]
  change (Option.map (g.withGained d forb) (g.node? y)).or _ = _
  cases hn : g.node? y with
  | some n => rfl
  | none =>
    rw [Option.map_none, Option.none_or]
    apply List.find?_eq_none.mpr
    intro m hm hid
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have := newRow_step hd hq
    have hq' : q = y := by simpa [rowNode] using hid
    rw [hq'] at this; omega

theorem node?_addNode_new (hb : Below g) (hd : d.step = g.current_step) {y : PathNodeId}
    (hy : y ∈ g.newRowIds d forb) : (g.addNode d title forb).node? y = some (g.rowNode d title y) := by
  show List.find? _ (g.nodes.map (g.withGained d forb) ++ (g.newRowIds d forb).map (g.rowNode d title)) = _
  rw [List.find?_append, find?_map_id (g.withGained d forb) (fun _ => rfl)]
  change (Option.map (g.withGained d forb) (g.node? y)).or _ = _
  have hnone : g.node? y = none := by
    apply List.find?_eq_none.mpr
    intro n hn hid
    have := hb n hn
    rw [show n.id = y by simpa using hid, newRow_step hd hy] at this
    omega
  rw [hnone, Option.map_none, Option.none_or]
  exact find?_newRow hy

theorem gained_new {n : PNodeB} {s : PathNodeId} (hs : s ∈ g.gainedSons d forb n) :
    s ∈ g.newRowIds d forb ∧ n.id ∈ g.newParents := by
  have ⟨h1, h2⟩ := List.mem_filter.mp hs
  exact ⟨h1, rowParents_sub (List.contains_iff_mem.mp h2)⟩

-- ============================================================
-- Bajar una estructura cerrada al estado anterior
-- ============================================================

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- **Una estructura cerrada de la fila nueva, restringida a los pasos viejos, es cerrada en el estado anterior.** -/
theorem secStruct_addNode_down (hdocs : AliveDocs g) (hb : Below g) (hls : LinksStep g)
    (hd : d.step = g.current_step) (hst : SecStruct (g.addNode d title forb) V R) :
    SecStruct g (fun q => V q ∧ q.id.step < g.current_step)
      (fun y w => R y w ∧ y.id.step < g.current_step ∧ w.id.step < g.current_step) := by
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  -- un nodo viejo de V está vivo en el estado anterior
  have halive : ∀ {q}, V q → q.id.step < g.current_step → q ∈ g.alive := by
    intro q hq hqs
    rcases alive_addNode_cases (title := title) hdocs hb hd (hst.alive hq) with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · omega
  -- el documento viejo de un nodo viejo de V
  have hdoc : ∀ {q m}, q.id.step < g.current_step → (g.addNode d title forb).node? q = some m →
      ∃ n, g.node? q = some n ∧ m = g.withGained d forb n := by
    intro q m hqs hm
    rw [node?_addNode_old (title := title) hd hqs] at hm
    cases hn : g.node? q with
    | none => rw [hn] at hm; cases hm
    | some n => rw [hn] at hm; cases hm; exact ⟨n, rfl, rfl⟩
  -- los enlaces de un documento viejo están en pasos viejos
  have hpar_old : ∀ {q n p}, g.node? q = some n → p ∈ n.parents → p.id.step < g.current_step := by
    intro q n p hn hp
    have := (hls n (node?_mem hn)).1 p hp
    have := hb n (node?_mem hn)
    omega
  have hson_old : ∀ {q n s}, g.node? q = some n → s ∈ n.sons → q.id.step + 1 < g.current_step →
      s.id.step < g.current_step := by
    intro q n s hn hs hq
    have := (hls n (node?_mem hn)).2 s hs
    rw [node?_id hn] at this
    omega
  -- un hijo ganado solo lo tiene un documento de la cima
  have hgained : ∀ {q n s}, g.node? q = some n → s ∈ g.gainedSons d forb n → q.id.step + 1 = g.current_step := by
    intro q n s hn hs
    obtain ⟨_, hp⟩ := gained_new hs
    obtain ⟨_, _, hid, hstep⟩ := step_of_newParents hp
    rw [node?_id hn] at hstep
    omega
  refine ⟨fun ⟨hq, hqs⟩ => halive hq hqs, fun ⟨hq, hqs⟩ => ⟨hst.refl hq, hqs, hqs⟩,
    fun ⟨hr, h1, h2⟩ => ⟨hst.symm hr, h2, h1⟩, fun ⟨hr, h1, h2⟩ => ⟨⟨(hst.dom hr).1, h1⟩, ⟨(hst.dom hr).2, h2⟩⟩,
    fun ⟨hr, h1, h2⟩ => adj_addNode_old (title := title) (forb := forb) hd h1 h2 (hst.adj hr), ?_, ?_, ?_, ?_⟩
  · -- parejas: los testigos de los pasos viejos son viejos
    rintro y w ⟨hr, h1, h2⟩ l hl0 hl1
    obtain ⟨r, hrl, hyr, hwr⟩ := hst.pair hr l hl0 (by rw [hcs]; omega)
    exact ⟨r, hrl, ⟨hyr, h1, by omega⟩, ⟨hwr, h2, by omega⟩⟩
  · -- enlaces
    rintro y ⟨hy, hys⟩
    obtain ⟨m, hm, hp, hs⟩ := hst.node hy
    obtain ⟨n, hn, rfl⟩ := hdoc hys hm
    refine ⟨n, hn, fun hr => ?_, fun hl => ?_⟩
    · obtain ⟨p, hpm, hyp⟩ := hp hr
      exact ⟨p, hpm, hyp, hys, hpar_old hn hpm⟩
    · obtain ⟨s, hsm, hys'⟩ := hs (by rw [hcs]; omega)
      rcases List.mem_append.mp hsm with hs1 | hs2
      · have hlt : y.id.step + 1 < g.current_step := by
          rcases Int.lt_or_eq_of_le (show y.id.step + 1 ≤ g.current_step by omega) with h | h
          · exact h
          · exact absurd (by omega : y.id.step = g.current_step - 1) hl
        exact ⟨s, hs1, hys', hys, hson_old hn hs1 hlt⟩
      · exact absurd (by have := hgained hn hs2; omega : y.id.step = g.current_step - 1) hl
  · -- apoyo de los padres
    rintro x w n ⟨hr, h1, h2⟩ hxw hn hx1
    have hm := node?_addNode_old (title := title) (forb := forb) hd h1
    rw [hn] at hm
    obtain ⟨p, hpm, hxp, hpw⟩ := hst.par hr hxw hm hx1
    have hpo := hpar_old hn hpm
    exact ⟨p, hpm, ⟨hxp, h1, hpo⟩, ⟨hpw, hpo, h2⟩⟩
  · -- apoyo de los hijos
    rintro x w n ⟨hr, h1, h2⟩ hxw hn hx1
    have hm := node?_addNode_old (title := title) (forb := forb) hd h1
    rw [hn] at hm
    obtain ⟨s, hsm, hxs, hsw⟩ := hst.son hr hxw hm (by rw [hcs]; omega)
    rcases List.mem_append.mp hsm with hs1 | hs2
    · have hso := hson_old hn hs1 hx1
      exact ⟨s, hs1, ⟨hxs, h1, hso⟩, ⟨hsw, hso, h2⟩⟩
    · exact absurd (hgained hn hs2) (by omega)

-- ============================================================
-- KernelExact en la fila nueva
-- ============================================================

/-- Alargar una camarilla que concuerda con `P` con un nodo de la fila, si lo que `P` fija en el paso nuevo es `d`. -/
theorem extend_through {S : Int → PathNodeId} {P : List NodeId} (hc : Carried g S) (hpos : 0 < g.current_step)
    (hb : Below g) (hd : d.step = g.current_step) (ha : ∀ r ∈ P, Agrees g.current_step S r)
    (hP : ∀ r ∈ P, r.step = g.current_step → r = d) {n : PathNodeId} (hn : n ∈ g.newRowIds d forb)
    (hp : S (g.current_step - 1) ∈ g.rowParents d n) :
    Carried (g.addNode d title forb) (extSel S g.current_step n) ∧
      (∀ r ∈ P, Agrees (g.addNode d title forb).current_step (extSel S g.current_step n) r) ∧
      (∀ q, OnS g.current_step S q → OnS (g.addNode d title forb).current_step (extSel S g.current_step n) q) ∧
      OnS (g.addNode d title forb).current_step (extSel S g.current_step n) n := by
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  refine ⟨carried_extSel hc hpos hn hp hd hb, ?_, fun q hq => by rw [hcs]; exact onS_extSel hq, ?_⟩
  · intro r hr h0 h1
    rw [hcs] at h1
    rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h1) with hlt | heq
    · have := ha r hr h0 hlt
      simp only [extSel, show r.step ≠ g.current_step by omega, if_false]
      exact this
    · simp only [extSel, heq, if_true]
      rw [mapId_of_mem_shiftRowIds (List.mem_filter.mp hn).1, hP r hr heq]
  · rw [hcs]; exact onS_extSel_new (by omega) n

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- **La fila nueva conserva `KernelExact`** (sin ventana saltada). -/
theorem kernelExact_addNode (hk : KernelExact g) (hdocs : AliveDocs g) (hb : Below g) (hls : LinksStep g)
    (hea : EdgesAlive g) (hpos : 0 < g.current_step) (hskip : g.skipsWindow d forb = false)
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
  · -- dos viejos: la camarilla del estado anterior, alargada con el hijo de su cima
    obtain ⟨S, hc, hag, hyS, hwS⟩ := hold hr hys hws
    obtain ⟨hn, hp⟩ := son_in_row (d := d) (forb := forb) hpos hskip (top_newParents hc hpos)
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

end GPathB

end AbsSatBingo.Model
