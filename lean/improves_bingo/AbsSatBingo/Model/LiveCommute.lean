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
un orden al otro en los dos sentidos (`secStruct_move`):

* **`filter_up_commute`**: `A' = filtro(up(filtro(g, reqs)), R)` y `B = up(filtro(g, reqs ++ R))`, con `R` por
  debajo de la cima y los dos cerrados, tienen los mismos vivos y las mismas aristas entre vivos;
* **`liveExt_congr`**: `LiveExt` solo depende de vivos, aristas y compatibilidad de ids (con `LinksInv`);
* **`liveExt_arrival_pinned`**: con **`PinStable`** (`LiveExt` tras cualquier filtro) en el remitente, la llegada
  cumple `LiveExt` tras cualquier filtro por debajo de su cima. El pin del UP deja de ser una hipótesis: queda dentro
  del invariante reforzado.

Hipótesis que quedan en este paso: que `A'` y `B` sean cerrados, y los invariantes de enlaces y documentos de la línea
(`RowOk`, `UpOk`).
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

-- ============================================================
-- Mover una estructura cerrada de un orden al otro
-- ============================================================

/-- **Mover una estructura cerrada** de un estado `S` por debajo de la fila sobre `Z` (un filtro de `g`) al UP sobre
otro filtro `g.filterAll P`: se baja a `Z` (`secStruct_addNode_down`), a `g`, se filtra por `P` y se sube
(`secStruct_addNode_lift`). -/
theorem secStruct_move {g S Z : GPathB} {P : List NodeId} {W : PathNodeId → Prop}
    {Rl : PathNodeId → PathNodeId → Prop} (hS : SecStruct S W Rl) (hsub : Sub S (Z.addNode d title forb))
    (hZg : Sub Z g) (hndg : NodupIds g)
    (hagP : ∀ b ∈ P, SecAgrees (fun q => W q ∧ q.id.step < Z.current_step) b)
    (hpos : 0 < Z.current_step) (hdZ : d.step = Z.current_step)
    (hdocsZ : AliveDocs Z) (hbZ : Below Z) (heaZ : EdgesAlive Z) (hlsZ : LinksStep Z) (hkZ : LinksCompat Z)
    (hndZ : NodupIds (Z.addNode d title forb))
    (hvX : (g.filterAll P).isValid = true) (hdocsX : AliveDocs (g.filterAll P)) (hbX : Below (g.filterAll P))
    (hliX : LinksInv (g.filterAll P)) :
    SecStruct ((g.filterAll P).up d title forb) W Rl := by
  have hU := secStruct_of_sub hsub hndZ hS
  have hdown := secStruct_addNode_down hdocsZ hbZ hlsZ hdZ hU
  have hg := secStruct_of_sub hZg hndg hdown
  have hX := secStruct_filterAll_list hg P hagP
  have hcs : (g.filterAll P).current_step = Z.current_step := by
    rw [(shrinks_filterAll g P).1.step, hZg.step]
  have hlift := secStruct_addNode_lift (X := g.filterAll P) (Y := Z) (title := title) (forb := forb) hcs hpos
    (by rw [hcs]; exact hdZ) hdZ hdocsX hbX hliX hdocsZ hbZ heaZ hlsZ hkZ hU hX
  unfold up
  rw [if_pos hvX]
  exact secStruct_review hlift

-- ============================================================
-- La conmutación
-- ============================================================

theorem sub_up_addNode {Z : GPathB} (hv : Z.isValid = true) : Sub (Z.up d title forb) (Z.addNode d title forb) := by
  unfold up; rw [if_pos hv]; exact (shrinks_review _).1

/-- Lo que la conmutación pide de un filtro `Z` del remitente para subir y bajar estructuras por su fila. -/
structure RowOk (Z : GPathB) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : Prop where
  valid : Z.isValid = true
  docs  : AliveDocs Z
  below : Below Z
  edges : EdgesAlive Z
  lstep : LinksStep Z
  links : LinksInv Z
  nodup : NodupIds (Z.addNode d title forb)
  ddocs : AliveDocs (Z.up d title forb)

/-- **Filtrar después del UP y antes dan el mismo estado** (mismos vivos, mismas aristas entre vivos), si los dos
resultados son cerrados: `A' = filtro(up(filtro(g, reqs)), R)` y `B = up(filtro(g, reqs ++ R))`, con `R` por debajo
de la cima. -/
theorem filter_up_commute {g : GPathB} {reqs R : List NodeId} (hndg : NodupIds g) (hdocsg : AliveDocs g)
    (hpos : 0 < g.current_step) (hd : d.step = g.current_step) (hR : ∀ b ∈ R, b.step < g.current_step)
    (hY : RowOk (g.filterAll reqs) d title forb) (hX : RowOk (g.filterAll (reqs ++ R)) d title forb)
    (hvA : (((g.filterAll reqs).up d title forb).filterAll R).isValid = true)
    (hcA : ClosedState (((g.filterAll reqs).up d title forb).filterAll R))
    (hcB : ClosedState ((g.filterAll (reqs ++ R)).up d title forb)) :
    (∀ q, q ∈ (((g.filterAll reqs).up d title forb).filterAll R).alive ↔
      q ∈ ((g.filterAll (reqs ++ R)).up d title forb).alive) ∧
    (∀ y w, y ∈ (((g.filterAll reqs).up d title forb).filterAll R).alive →
      w ∈ (((g.filterAll reqs).up d title forb).filterAll R).alive →
      ((((g.filterAll reqs).up d title forb).filterAll R).Adj y w ↔
        ((g.filterAll (reqs ++ R)).up d title forb).Adj y w)) := by
  have hcsY : (g.filterAll reqs).current_step = g.current_step := (shrinks_filterAll g reqs).1.step
  have hcsX : (g.filterAll (reqs ++ R)).current_step = g.current_step := (shrinks_filterAll g _).1.step
  have hsubA : Sub (((g.filterAll reqs).up d title forb).filterAll R) ((g.filterAll reqs).addNode d title forb) :=
    (shrinks_filterAll _ R).1.trans (sub_up_addNode hY.valid)
  have hsubB : Sub ((g.filterAll (reqs ++ R)).up d title forb) ((g.filterAll (reqs ++ R)).addNode d title forb) :=
    sub_up_addNode hX.valid
  -- A' → B
  have h1 := secStruct_move (P := reqs ++ R) hcA hsubA (shrinks_filterAll g reqs).1 hndg
    (fun b hb q ⟨hq, hqs⟩ hqb => by
      rcases List.mem_append.mp hb with hb | hb
      · have hq' := hsubA.alive q hq
        rcases alive_addNode_cases hY.docs hY.below (by rw [hcsY]; exact hd) hq' with ⟨hqY, _⟩ | ⟨_, h⟩
        · exact pinned_filterAll_list hdocsg reqs hY.valid b hb q hqY hqb
        · omega
      · exact pinned_filterAll_list hY.ddocs R hvA b hb q hq hqb)
    (by rw [hcsY]; exact hpos) (by rw [hcsY]; exact hd) hY.docs hY.below hY.edges hY.lstep hY.links.2.2 hY.nodup
    hX.valid hX.docs hX.below hX.links
  -- B → A'
  have h2 := secStruct_move (P := reqs) hcB hsubB (shrinks_filterAll g _).1 hndg
    (fun b hb q ⟨hq, hqs⟩ hqb => by
      have hq' := hsubB.alive q hq
      rcases alive_addNode_cases hX.docs hX.below (by rw [hcsX]; exact hd) hq' with ⟨hqX, _⟩ | ⟨_, h⟩
      · exact pinned_filterAll_list hdocsg (reqs ++ R) hX.valid b (List.mem_append_left _ hb) q hqX hqb
      · omega)
    (by rw [hcsX]; exact hpos) (by rw [hcsX]; exact hd) hX.docs hX.below hX.edges hX.lstep hX.links.2.2 hX.nodup
    hY.valid hY.docs hY.below hY.links
  have h2' := secStruct_filterAll_list h2 R (fun b hb q hq hqb => by
    have hq' := hsubB.alive q hq
    rcases alive_addNode_cases hX.docs hX.below (by rw [hcsX]; exact hd) hq' with ⟨hqX, _⟩ | ⟨_, h⟩
    · exact pinned_filterAll_list hdocsg (reqs ++ R) hX.valid b (List.mem_append_right _ hb) q hqX hqb
    · have := hR b hb; rw [hcsX] at h; omega)
  refine ⟨fun q => ⟨fun hq => h1.alive hq, fun hq => h2'.alive hq⟩, fun y w hy hw => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · exact h1.adj ⟨hy, hw, ha⟩
  · exact h2'.adj ⟨h1.alive hy, h1.alive hw, ha⟩

-- ============================================================
-- LiveExt solo depende de vivos, aristas y compatibilidad
-- ============================================================

/-- Una cadena viva pasa a otro estado con los mismos vivos (al menos) y las mismas aristas entre ellos: los enlaces
de una cadena unen vecinos compatibles, y `LinksComplete` los tiene todos. -/
theorem liveChain_transfer {A B : GPathB} {F : Trios} (hcs : A.current_step = B.current_step)
    (halive : ∀ q ∈ A.alive, q ∈ B.alive) (hadj : ∀ y w, y ∈ A.alive → w ∈ A.alive → A.Adj y w → B.Adj y w)
    (hkA : LinksCompat A) (hliB : LinksInv B) {C : Int → PathNodeId} {j : Int} (hC : LiveChain A F C j) :
    LiveChain B F C j := by
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c ha hab hbc hc =>
    hC.live a b c ha hab hbc (by rw [hcs]; exact hc)⟩
  · obtain ⟨hs, ha⟩ := hC.chain.node k h1 (by rw [hcs]; exact h2); exact ⟨hs, halive _ ha⟩
  · exact hadj _ _ (hC.chain.node k h1 (by rw [hcs]; exact h2)).2 (hC.chain.node l h3 (by rw [hcs]; exact h4)).2
      (hC.chain.adj k l h1 (by rw [hcs]; exact h2) h3 (by rw [hcs]; exact h4))
  · obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 (by rw [hcs]; exact h2)
    have hc := (hkA n (node?_mem hn)).1 _ hp
    rw [node?_id hn] at hc
    have hka := (hC.chain.node k (by omega) (by rw [hcs]; exact h2)).2
    have hk1 := (hC.chain.node (k - 1) (by omega) (by rw [hcs]; omega)).2
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hliB.1 (halive _ hka))
    have hab : B.Adj m.id (C (k - 1)) := by
      rw [node?_id hm]
      exact hadj _ _ hka hk1 (hC.chain.adj k (k - 1) (by omega) (by rw [hcs]; exact h2) (by omega) (by rw [hcs]; omega))
    refine ⟨m, hm, (hliB.2.1 m (node?_mem hm) _ (halive _ hk1) hab).1 ?_⟩
    rw [node?_id hm]; exact hc

/-- **`LiveExt` pasa entre dos estados con los mismos vivos y las mismas aristas entre vivos.** -/
theorem liveExt_congr {A B : GPathB} {F : Trios} (hcs : A.current_step = B.current_step)
    (halive : ∀ q, q ∈ A.alive ↔ q ∈ B.alive)
    (hadj : ∀ y w, y ∈ A.alive → w ∈ A.alive → (A.Adj y w ↔ B.Adj y w))
    (hliA : LinksInv A) (hliB : LinksInv B) (hext : LiveExt B F) : LiveExt A F := by
  intro C j hC hj1 hjt
  have hCB := liveChain_transfer hcs (fun q hq => (halive q).mp hq) (fun y w hy hw h => (hadj y w hy hw).mp h)
    hliA.2.2 hliB hC
  obtain ⟨C', hC', hag⟩ := hext C j hCB hj1 (by rw [← hcs]; exact hjt)
  refine ⟨C', liveChain_transfer hcs.symm (fun q hq => (halive q).mpr hq) (fun y w hy hw h => ?_)
    hliB.2.2 hliA hC', hag⟩
  exact (hadj y w ((halive y).mpr hy) ((halive w).mpr hw)).mpr h

-- ============================================================
-- PinStable: LiveExt tras cualquier filtro, a través del UP
-- ============================================================

/-- **`PinStable g`**: tras fijar cualquier lista de requisitos, el estado que queda (si es válido) cumple `LiveExt`
para alguna relación de tríos sin degenerar y por debajo de su paso. Refuerza `LiveExt` para que la inducción pase por
los filtros del UP (y por los pins del lector). -/
def PinStable (g : GPathB) : Prop :=
  ∀ R : List NodeId, (g.filterAll R).isValid = true →
    ∃ F, LiveExt (g.filterAll R) F ∧ FBelow F (g.filterAll R).current_step ∧ NoDeg F

theorem step_up {Z : GPathB} (hv : Z.isValid = true) : (Z.up d title forb).current_step = Z.current_step + 1 := by
  unfold up; rw [if_pos hv]; exact (shrinks_review _).1.step

/-- Los invariantes que pide `liveExt_up` de un filtro del remitente. -/
structure UpOk (Z : GPathB) : Prop where
  docs  : AliveDocs Z
  below : Below Z
  dalive : DocsAlive Z
  links : LinksInv Z
  zero  : AboveZero Z
  nodup : NodupIds Z
  root  : RootNone Z

/-- **El UP conserva `LiveExt` tras cualquier filtro por debajo de la cima**, si el remitente es `PinStable`: el
estado de la llegada filtrado por `R` es (en vivos y aristas) el UP sobre el filtro por `reqs ++ R`
(`filter_up_commute`), y ese cumple `LiveExt` (`liveExt_up`). -/
theorem liveExt_arrival_pinned {g : GPathB} {reqs R : List NodeId} (hps : PinStable g)
    (hndg : NodupIds g) (hdocsg : AliveDocs g) (hpos : 0 < g.current_step) (hd : d.step = g.current_step)
    (hR : ∀ b ∈ R, b.step < g.current_step)
    (hY : RowOk (g.filterAll reqs) d title forb) (hX : RowOk (g.filterAll (reqs ++ R)) d title forb)
    (hXu : UpOk (g.filterAll (reqs ++ R)))
    (hvA : (((g.filterAll reqs).up d title forb).filterAll R).isValid = true)
    (hcA : ClosedState (((g.filterAll reqs).up d title forb).filterAll R))
    (hcB : ClosedState ((g.filterAll (reqs ++ R)).up d title forb))
    (hliA : LinksInv (((g.filterAll reqs).up d title forb).filterAll R))
    (hliB : LinksInv ((g.filterAll (reqs ++ R)).up d title forb)) :
    ∃ F, LiveExt (((g.filterAll reqs).up d title forb).filterAll R) F := by
  obtain ⟨F, hext, hB, hnF⟩ := hps (reqs ++ R) hX.valid
  have hcsX : (g.filterAll (reqs ++ R)).current_step = g.current_step := (shrinks_filterAll g _).1.step
  have hcsY : (g.filterAll reqs).current_step = g.current_step := (shrinks_filterAll g _).1.step
  have hupB := liveExt_up (title := title) (forb := forb) hext hX.valid hXu.docs hXu.below hXu.dalive hXu.links
    hXu.zero hXu.nodup hXu.root (by rw [hcsX]; exact hd) hB hnF
  obtain ⟨halive, hadj⟩ := filter_up_commute hndg hdocsg hpos hd hR hY hX hvA hcA hcB
  refine ⟨_, liveExt_congr ?_ halive hadj hliA hliB hupB⟩
  rw [(shrinks_filterAll _ R).1.step, step_up hY.valid, step_up hX.valid, hcsX, hcsY]

end GPathB

end AbsSatBingo.Model
