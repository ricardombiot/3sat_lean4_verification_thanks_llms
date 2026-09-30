-- lean/improves_bingo/AbsSatBingo/Model/LiveCommute.lean
import AbsSatBingo.Model.LiveUp

/-!
# Filtrar y subir conmutan (a nivel de estructuras cerradas)

`probe_pinstable.jl`: fijar requisitos `R` después del UP da el mismo grafo que fijarlos antes (junto a los del UP).
Aquí la pieza de Lean que lo explica:

* **`secStruct_addNode_lift`**: una estructura cerrada de la fila nueva sobre `Y` cuya parte vieja es cerrada en `X`
  es cerrada en la fila nueva sobre `X`. Los nodos nuevos no dependen del estado: son desplazamientos de sus padres,
  y los padres de la estructura están en `X`.

Con `secStruct_addNode_down` (bajar) y los filtros (`secStruct_filterAll_list`), las estructuras cerradas pasan de
un orden al otro en los dos sentidos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Machine (Below mapId_of_mem_shiftRowIds)

variable {X Y : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **Un nodo nuevo con un padre que sigue vivo en `X` es también de la fila sobre `X`.** -/
theorem row_transfer (hcs : X.current_step = Y.current_step) (hdocsX : AliveDocs X) {t p : PathNodeId}
    (ht : t ∈ Y.newRowIds d forb) (hp : p ∈ Y.rowParents d t) (hpa : p ∈ X.alive) :
    t ∈ X.newRowIds d forb ∧ p ∈ X.rowParents d t := by
  have hpY := rowParents_sub hp
  have hpos : 0 < Y.current_step := by
    unfold newParents at hpY; split at hpY
    · assumption
    · cases hpY
  obtain ⟨_, _, _, hstep⟩ := step_of_newParents hpY
  obtain ⟨m, hm, hmid⟩ := hdocsX p hpa
  have hpX : p ∈ X.newParents := by
    rw [← hmid]; exact mem_newParents (by omega) hm (by rw [hmid, hstep, hcs])
  have hsh := (List.mem_filter.mp hp).2
  have heq : shiftPid p d = t := by simpa using hsh
  refine ⟨List.mem_filter.mpr ⟨?_, (List.mem_filter.mp ht).2⟩, List.mem_filter.mpr ⟨hpX, hsh⟩⟩
  unfold shiftRowIds
  rw [if_pos (by omega)]
  exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨p, hpX, heq⟩)

/-- Un nodo nuevo es el desplazamiento de cualquier nodo compatible con él. -/
theorem shift_of_compat {p s : PathNodeId} (hc : Compat p s) (hs : s.id = d) : shiftPid p d = s := by
  obtain ⟨h1, h2, _⟩ := hc
  cases s
  simp_all [shiftPid]

theorem newRow_id {t : PathNodeId} (ht : t ∈ Y.newRowIds d forb) : t.id = d :=
  mapId_of_mem_shiftRowIds (List.mem_filter.mp ht).1

/-- Un nodo nuevo tiene padre en su id (si el paso es positivo). -/
theorem newRow_parentSome (hpos : 0 < Y.current_step) {t : PathNodeId} (ht : t ∈ Y.newRowIds d forb) :
    t.parent_id.isNone = false := by
  have hs := (List.mem_filter.mp ht).1
  unfold shiftRowIds at hs
  rw [if_pos hpos] at hs
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp ((mem_dedupPids _ _).mp hs)
  rfl

/-- **Subir una estructura cerrada de la fila sobre `Y` a la fila sobre `X`**, si su parte vieja es cerrada en `X`. -/
theorem secStruct_addNode_lift {W : PathNodeId → Prop} {Rl : PathNodeId → PathNodeId → Prop}
    (hcs : X.current_step = Y.current_step) (hpos : 0 < Y.current_step)
    (hdX : d.step = X.current_step) (hdY : d.step = Y.current_step)
    (hdocsX : AliveDocs X) (hbX : Below X) (hliX : LinksInv X)
    (hdocsY : AliveDocs Y) (hbY : Below Y) (heaY : EdgesAlive Y) (hlsY : LinksStep Y) (hkY : LinksCompat Y)
    (hU : SecStruct (Y.addNode d title forb) W Rl)
    (hX : SecStruct X (fun q => W q ∧ q.id.step < Y.current_step)
      (fun y w => Rl y w ∧ y.id.step < Y.current_step ∧ w.id.step < Y.current_step)) :
    SecStruct (X.addNode d title forb) W Rl := by
  have hWcase : ∀ {q}, W q → (q ∈ Y.alive ∧ q.id.step < Y.current_step) ∨
      (q ∈ Y.newRowIds d forb ∧ q.id.step = Y.current_step) :=
    fun hq => alive_addNode_cases hdocsY hbY hdY (hU.alive hq)
  have hXa : ∀ {q}, W q → q.id.step < Y.current_step → q ∈ X.alive := fun hq hs => hX.alive ⟨hq, hs⟩
  have hXadj : ∀ {y w}, Rl y w → y.id.step < Y.current_step → w.id.step < Y.current_step → X.Adj y w :=
    fun hr h1 h2 => hX.adj ⟨hr, h1, h2⟩
  have hnodeY : ∀ {t}, t ∈ Y.newRowIds d forb →
      (Y.addNode d title forb).node? t = some (Y.rowNode d title t) := fun ht => node?_addNode_new hbY hdY ht
  have hnodeX : ∀ {t}, t ∈ X.newRowIds d forb →
      (X.addNode d title forb).node? t = some (X.rowNode d title t) := fun ht => node?_addNode_new hbX hdX ht
  have hpstep : ∀ {t p}, p ∈ Y.rowParents d t → p.id.step = Y.current_step - 1 := by
    intro t p hp
    obtain ⟨_, _, _, h⟩ := step_of_newParents (rowParents_sub hp)
    exact h
  have htopPar : ∀ {t}, W t → t ∈ Y.newRowIds d forb → ∃ p ∈ Y.rowParents d t, Rl t p := by
    intro t hW ht
    obtain ⟨n, hn, hp, _⟩ := hU.node hW
    rw [hnodeY ht] at hn; cases hn
    exact hp (newRow_parentSome hpos ht)
  have hparX : ∀ {t p}, t ∈ Y.newRowIds d forb → p ∈ Y.rowParents d t → W p → p ∈ X.rowParents d t :=
    fun ht hp hpW => (row_transfer hcs hdocsX ht hp (hXa hpW (by rw [hpstep hp]; omega))).2
  have htopX : ∀ {t}, W t → t ∈ Y.newRowIds d forb → t ∈ X.newRowIds d forb := by
    intro t hW ht
    obtain ⟨p, hp, htp⟩ := htopPar hW ht
    exact (row_transfer hcs hdocsX ht hp (hXa (hU.dom htp).2 (by rw [hpstep hp]; omega))).1
  have holdX : ∀ {y}, y.id.step < Y.current_step →
      (X.addNode d title forb).node? y = (X.node? y).map (X.withGained d forb) :=
    fun hy => node?_addNode_old hdX (by omega)
  have holdY : ∀ {y}, y.id.step < Y.current_step →
      (Y.addNode d title forb).node? y = (Y.node? y).map (Y.withGained d forb) :=
    fun hy => node?_addNode_old hdY hy
  -- el documento viejo de `Y`
  have hdocY : ∀ {y m'}, y.id.step < Y.current_step → (Y.addNode d title forb).node? y = some m' →
      ∃ m, Y.node? y = some m ∧ m' = Y.withGained d forb m := by
    intro y m' hy hm'
    rw [holdY hy] at hm'
    cases hm : Y.node? y with
    | none => rw [hm] at hm'; cases hm'
    | some m => rw [hm] at hm'; cases hm'; exact ⟨m, rfl, rfl⟩
  have hdocX : ∀ {y n}, y.id.step < Y.current_step → (X.addNode d title forb).node? y = some n →
      ∃ n0, X.node? y = some n0 ∧ n = X.withGained d forb n0 := by
    intro y n hy hn
    rw [holdX hy] at hn
    cases hm : X.node? y with
    | none => rw [hm] at hn; cases hn
    | some m => rw [hm] at hn; cases hn; exact ⟨m, rfl, rfl⟩
  -- los hijos de un documento viejo de `Y`: un paso más arriba
  have hsonStep : ∀ {y m s}, Y.node? y = some m → s ∈ (Y.withGained d forb m).sons → s.id.step = y.id.step + 1 := by
    intro y m s hm hs
    rcases List.mem_append.mp hs with h | h
    · have := (hlsY m (node?_mem hm)).2 s h; rwa [node?_id hm] at this
    · obtain ⟨hsn, hp⟩ := gained_new h
      obtain ⟨_, _, hid, hst⟩ := step_of_newParents hp
      rw [newRow_step hdY hsn, ← node?_id hm]; omega
  -- un hijo nuevo de un nodo viejo, en `Y`, es un hijo ganado en `X`
  have hgainX : ∀ {y s n0 m}, W y → y.id.step < Y.current_step → W s → s.id.step = Y.current_step →
      X.node? y = some n0 → Y.node? y = some m → s ∈ (Y.withGained d forb m).sons →
      s ∈ X.gainedSons d forb n0 := by
    intro y s n0 m hy hys hs hss hn0 hm hsm
    have hsnew : s ∈ Y.newRowIds d forb := by
      rcases hWcase hs with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact h
    have hyrp : y ∈ Y.rowParents d s := by
      rcases List.mem_append.mp hsm with h | h
      · have hc := (hkY m (node?_mem hm)).2 s h
        rw [node?_id hm] at hc
        have hsh := shift_of_compat hc (newRow_id hsnew)
        have hyP : y ∈ Y.newParents := by
          rw [← node?_id hm]; exact mem_newParents hpos (node?_mem hm) (by rw [node?_id hm]; have := hc.2.2; omega)
        exact List.mem_filter.mpr ⟨hyP, by simp [hsh]⟩
      · have := (List.mem_filter.mp h).2
        rw [node?_id hm] at this
        exact List.contains_iff_mem.mp this
    obtain ⟨hsX, hyX⟩ := row_transfer hcs hdocsX hsnew hyrp (hXa hy hys)
    refine List.mem_filter.mpr ⟨hsX, ?_⟩
    rw [node?_id hn0]
    exact List.contains_iff_mem.mpr hyX
  -- la arista de un nodo nuevo a uno viejo
  have hadjTop : ∀ {t w}, Rl t w → t ∈ Y.newRowIds d forb → t.id.step = Y.current_step →
      w.id.step < Y.current_step → (X.addNode d title forb).Adj t w := by
    intro t w hr ht hts hws
    have hne : t ≠ w := fun e => by rw [e] at hts; omega
    obtain ⟨p, hp, htp, hpw⟩ := hU.par hr hne (hnodeY ht) (by omega)
    have hpW := (hU.dom htp).2
    exact adj_addNode_row (htopX (hU.dom hr).1 ht) (hXa (hU.dom hr).2 hws) (by omega) (hparX ht hp hpW)
      (hXadj hpw (by rw [hpstep hp]; omega) hws)
  refine ⟨fun hq => ?_, hU.refl, hU.symm, hU.dom, fun {y w} hr => ?_, fun hr l h0 h1 => ?_, ?_, ?_, ?_⟩
  · rcases hWcase hq with ⟨_, hs⟩ | ⟨ht, _⟩
    · exact List.mem_append_left _ (hXa hq hs)
    · exact List.mem_append_right _ (htopX hq ht)
  · have hy := (hU.dom hr).1
    have hw := (hU.dom hr).2
    rcases hWcase hy with ⟨_, hys⟩ | ⟨hyt, hyT⟩ <;> rcases hWcase hw with ⟨_, hws⟩ | ⟨hwt, hwT⟩
    · exact adj_addNode_mono (hXadj hr hys hws)
    · exact (adj_symm _ _ _).mp (hadjTop (hU.symm hr) hwt hwT hys)
    · exact hadjTop hr hyt hyT hws
    · have := adj_addNode_new hdocsY hbY heaY hyT hwT (hU.adj hr)
      subst this
      exact adj_refl _ _ (List.mem_append_right _ (htopX hy hyt))
  · have h1' : l < X.current_step + 1 := h1
    exact hU.pair hr l h0 (by show l < Y.current_step + 1; omega)
  · intro y hy
    rcases hWcase hy with ⟨_, hys⟩ | ⟨hyt, hyT⟩
    · obtain ⟨n0, hn0, hp, hs⟩ := hX.node ⟨hy, hys⟩
      refine ⟨X.withGained d forb n0, by rw [holdX hys, hn0]; rfl, fun hr => ?_, fun hl => ?_⟩
      · obtain ⟨p, hpn, hyp⟩ := hp hr
        exact ⟨p, hpn, hyp.1⟩
      · by_cases hlt : y.id.step ≠ X.current_step - 1
        · obtain ⟨s, hsn, hys'⟩ := hs hlt
          exact ⟨s, List.mem_append_left _ hsn, hys'.1⟩
        · obtain ⟨m', hm', _, hsU⟩ := hU.node hy
          obtain ⟨m, hm, rfl⟩ := hdocY hys hm'
          obtain ⟨s, hsm, hys'⟩ := hsU (by show y.id.step ≠ Y.current_step + 1 - 1; omega)
          have hss := hsonStep hm hsm
          exact ⟨s, List.mem_append_right _ (hgainX hy hys (hU.dom hys').2 (by omega) hn0 hm hsm), hys'⟩
    · refine ⟨X.rowNode d title y, hnodeX (htopX hy hyt), fun _ => ?_, fun hl => ?_⟩
      · obtain ⟨p, hp, hyp⟩ := htopPar hy hyt
        exact ⟨p, hparX hyt hp (hU.dom hyp).2, hyp⟩
      · exact absurd (by show y.id.step = X.current_step + 1 - 1; omega) hl
  · intro x w n hr hne hn hx1
    have hx := (hU.dom hr).1
    rcases hWcase hx with ⟨_, hxs⟩ | ⟨hxt, _⟩
    · obtain ⟨n0, hn0, rfl⟩ := hdocX hxs hn
      rcases hWcase (hU.dom hr).2 with ⟨_, hws⟩ | ⟨_, hwT⟩
      · obtain ⟨p, hpn, hxp, hpw⟩ := hX.par ⟨hr, hxs, hws⟩ hne hn0 hx1
        exact ⟨p, hpn, hxp.1, hpw.1⟩
      · obtain ⟨m', hm', _, _⟩ := hU.node hx
        obtain ⟨m, hm, rfl⟩ := hdocY hxs hm'
        obtain ⟨p, hpm, hxp, hpw⟩ := hU.par hr hne hm' hx1
        have hc := (hkY m (node?_mem hm)).1 p hpm
        rw [node?_id hm] at hc
        have hps : p.id.step < Y.current_step := by have := hc.2.2; omega
        have hpX := hXa (hU.dom hxp).2 hps
        have hadj : X.Adj n0.id p := by rw [node?_id hn0]; exact hXadj hxp hxs hps
        refine ⟨p, ?_, hxp, hpw⟩
        exact (hliX.2.1 n0 (node?_mem hn0) p hpX hadj).1 (by rw [node?_id hn0]; exact hc)
    · rw [hnodeX (htopX hx hxt)] at hn
      cases hn
      obtain ⟨p, hp, hxp, hpw⟩ := hU.par hr hne (hnodeY hxt) hx1
      exact ⟨p, hparX hxt hp (hU.dom hxp).2, hxp, hpw⟩
  · intro x w n hr hne hn hx1
    have hx := (hU.dom hr).1
    have hxs : x.id.step < Y.current_step := by
      have : x.id.step + 1 < X.current_step + 1 := hx1
      omega
    obtain ⟨n0, hn0, rfl⟩ := hdocX hxs hn
    obtain ⟨m', hm', _, _⟩ := hU.node hx
    obtain ⟨m, hm, rfl⟩ := hdocY hxs hm'
    obtain ⟨s, hsm, hxs', hsw⟩ := hU.son hr hne hm' (by show x.id.step + 1 < Y.current_step + 1; omega)
    have hss := hsonStep hm hsm
    have hsW := (hU.dom hxs').2
    by_cases hsT : s.id.step < Y.current_step
    · have hsold : s ∈ m.sons := by
        rcases List.mem_append.mp hsm with h | h
        · exact h
        · rw [newRow_step hdY (gained_new h).1] at hsT; omega
      have hc := (hkY m (node?_mem hm)).2 s hsold
      rw [node?_id hm] at hc
      have hadj : X.Adj n0.id s := by rw [node?_id hn0]; exact hXadj hxs' hxs hsT
      have hsn : s ∈ n0.sons :=
        (hliX.2.1 n0 (node?_mem hn0) s (hXa hsW hsT) hadj).2 (by rw [node?_id hn0]; exact hc)
      exact ⟨s, List.mem_append_left _ hsn, hxs', hsw⟩
    · exact ⟨s, List.mem_append_right _ (hgainX hx hxs hsW (by omega) hn0 hm hsm), hxs', hsw⟩

end GPathB

end AbsSatBingo.Model
