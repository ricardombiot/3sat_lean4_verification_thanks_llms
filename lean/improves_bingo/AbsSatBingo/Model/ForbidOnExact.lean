-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnExact.lean
import AbsSatBingo.Model.ForbidOnNoPin

/-!
# La exactitud por niveles en la cima: un invariante sin listas de pins

`TopAt g R` pide, para **toda** lista `R` de requisitos futuros, que las cimas vivas del estado fijado estén en una
camarilla. Aquí el invariante habla solo del estado actual, por niveles:

* **`TopCT g`** (nivel 1, `ForbidOnNoPin`): toda cima viva está en una camarilla que esquiva los tríos;
* **`TopEdge g`** (nivel 2): toda arista viva de una cima está en una camarilla;
* **`TopTri g`** (nivel 3): todo triángulo sin prohibir con una cima está en una camarilla.

Operación por operación:

| operación | nivel 2 | nivel 3 |
|---|---|---|
| join | `topEdge_joinOn` (una arista es de un lado) | `topTri_joinOn` (un triángulo sin prohibir en la unión no lo corta algún lado: `tF_joinOn_of_cut`) |
| UP | `topEdge_upOn` (un padre posee al vecino) | `topTri_upOn` (un padre sostiene la cara: `upOn_face_parent`) |
| filtro de un requisito | `topEdge_filterAllOn`, **desde el nivel 3 de antes**: el testigo bueno de la arista en el paso fijado (`trioGood_low`) da un triángulo sin prohibir | **hipótesis** (`HTriKeep`) |

y el nivel 1 tras el filtro sale del nivel 2 de antes (`topAt_of_topEdge`): la cima tiene un vecino en el paso fijado.

**La escalera.** El veredicto cuelga del nivel 1, y cada nivel de hipótesis da el de abajo:

`HypsPinTetra` ⟹ `HypsTriKeep` (nivel 3) ⟹ `HypsEdgeKeep` (nivel 2) ⟹ `HypsNodeKeep` (nivel 1) ⟹ veredicto

donde «nivel k» es: el filtro de cada llegada de la máquina conserva la propiedad de nivel k. Son enunciados sobre un
estado y un requisito, sin lados ni listas de pins; el UP y el join están demostrados en los tres niveles
(`OpsP`, `lInvP_advance`). `PinTetra` es la forma de cuatro nodos de lo que le falta al nivel 3: el testigo bueno de
un triángulo de cima en el paso fijado forma un tetraedro que puede no estar en ninguna camarilla.

Veredictos: `spineVerdictOn_iff_of_nodeKeep`, `_of_edgeKeep`, `_of_triKeep`, `_of_triFlt`, `_of_pinTetra`.

**Dónde empieza la dificultad.** Un filtro cuyo requisito está en el paso de la cima no consume nivel
(`ct_filter_of_topReq`). En la parte de variables todos los requisitos son así (`reqOf_step_pre`) y no hay ventanas
prohibidas, así que los tres niveles valen sin hipótesis hasta la fusión central (`lInvX_pre`) y las hipótesis solo
hacen falta en las líneas de cláusula (`HypsNodeKeepC`, `spineVerdictOn_iff_of_nodeKeepC`). Los dos primeros filtros
lejanos (las copias de los dos primeros literales de la primera cláusula) consumen un nivel cada uno, y por eso toda
cima viva está en una camarilla, sin hipótesis, hasta justo antes de la primera ventana prohibida
(`topCT_before_first_window`). No está formalizado lo más fuerte: que sin ventanas prohibidas las copias no consumen
nivel nunca (haría falta el invariante semántico «vecinos ⟺ ventanas compatibles» para la máquina `:on`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- Los niveles
-- ============================================================

/-- **`TopEdge`**: toda arista viva de una cima está en una camarilla que esquiva los tríos (con `w = t`, la cima
sola). -/
def TopEdge (g : GPathB) : Prop :=
  ∀ t ∈ g.alive, t.id.step = g.current_step - 1 → ∀ w, g.Adj t w →
    ∃ D, CT g D ∧ D (g.current_step - 1) = t ∧ D w.id.step = w

/-- **`TopTri`**: todo triángulo sin prohibir con una cima está en una camarilla que esquiva los tríos. -/
def TopTri (g : GPathB) : Prop :=
  ∀ t ∈ g.alive, t.id.step = g.current_step - 1 → ∀ u w, g.Adj t u → g.Adj t w → g.Adj u w →
    t ≠ u → t ≠ w → u ≠ w → ¬ TF g t u w →
    ∃ D, CT g D ∧ D (g.current_step - 1) = t ∧ D u.id.step = u ∧ D w.id.step = w

theorem topCT_of_topEdge {g : GPathB} (h : TopEdge g) : TopCT g := by
  intro t ht hts
  obtain ⟨D, hD, hDt, _⟩ := h t ht hts t (adj_refl _ _ ht)
  exact ⟨D, hD, hDt⟩

-- ============================================================
-- El join
-- ============================================================

/-- **El join conserva `TopEdge`**: una arista de la unión es de un lado. -/
theorem topEdge_joinOn {A B : GPathB} (hA : TopEdge A) (hB : TopEdge B) (hnsA : NoSelf A) (hnsB : NoSelf B)
    (heA : EdgesAlive A) (heB : EdgesAlive B) (hcs : A.current_step = B.current_step) : TopEdge (joinOn A B) := by
  intro t _ hts w htw
  rw [step_joinOn] at hts ⊢
  obtain ⟨T', hT⟩ := joinOn_eq A B
  have htw' : (join A B).Adj t w := by rw [hT] at htw; exact htw
  rcases adj_join_cases htw' with h | h
  · obtain ⟨D, hD, h1, h2⟩ := hA t (heA t w h).1 hts w h
    exact ⟨D, ct_joinOn_left hD hnsB, h1, h2⟩
  · obtain ⟨D, hD, h1, h2⟩ := hB t (heB t w h).1 (by rw [← hcs]; exact hts) w h
    exact ⟨D, ct_joinOn_right hcs hD hnsA, by rw [hcs]; exact h1, h2⟩

/-- **El join conserva `TopTri`**: un triángulo que la unión no prohíbe no lo corta alguno de los lados. -/
theorem topTri_joinOn {A B : GPathB} (hA : TopTri A) (hB : TopTri B) (hnsA : NoSelf A) (hnsB : NoSelf B)
    (heA : EdgesAlive A) (heB : EdgesAlive B) (hcs : A.current_step = B.current_step) : TopTri (joinOn A B) := by
  intro t _ hts u w htu htw huw ntu ntw nuw hn
  rw [step_joinOn] at hts ⊢
  have side : ∀ {g : GPathB}, ¬ SideForbids g (TF g) t u w → (g.Adj t u ∧ g.Adj t w ∧ g.Adj u w) ∧ ¬ TF g t u w :=
    fun hs => ⟨Classical.byContradiction (fun h => hs (Or.inl h)), fun h => hs (Or.inr h)⟩
  by_cases sA : SideForbids A (TF A) t u w
  · have sB : ¬ SideForbids B (TF B) t u w :=
      fun s => hn (tF_joinOn_of_cut heA heB htu htw huw ntu ntw nuw sA s)
    obtain ⟨⟨a1, a2, a3⟩, nf⟩ := side sB
    obtain ⟨D, hD, h1, h2, h3⟩ := hB t (heB t u a1).1 (by rw [← hcs]; exact hts) u w a1 a2 a3 ntu ntw nuw nf
    exact ⟨D, ct_joinOn_right hcs hD hnsA, by rw [hcs]; exact h1, h2, h3⟩
  · obtain ⟨⟨a1, a2, a3⟩, nf⟩ := side sA
    obtain ⟨D, hD, h1, h2, h3⟩ := hA t (heA t u a1).1 hts u w a1 a2 a3 ntu ntw nuw nf
    exact ⟨D, ct_joinOn_left hD hnsB, h1, h2, h3⟩

-- ============================================================
-- El filtro: cada nivel sale del siguiente
-- ============================================================

/-- **Nivel 1 tras un pin, desde el nivel 2**: una cima viva del estado fijado en un requisito tiene un vecino vivo
en el paso fijado; la arista ya estaba, y su camarilla cumple el requisito. -/
theorem topAt_of_topEdge {E : GPathB} {reqs : List NodeId} (hE : SInvB E) (hlen : reqs.length ≤ 1)
    (he : TopEdge E) : TopAt E reqs := by
  have hsub := sub_pinOn E reqs
  intro hv t ht hts
  have htE := hsub.alive t ht
  have self := he t htE hts t (adj_refl _ _ htE)
  match reqs, hlen, hv, ht, hsub with
  | [], _, _, _, _ =>
    obtain ⟨D, hD, hDt, _⟩ := self
    exact ⟨D, ct_pinOn hD [] (fun r hr => absurd hr List.not_mem_nil), hDt⟩
  | [r], _, hv, ht, hsub =>
    by_cases hr : 0 ≤ r.step ∧ r.step < E.current_step
    · by_cases htop : r.step = E.current_step - 1
      · -- el requisito está en el paso de la cima: la cima es del requisito
        obtain ⟨D, hD, hDt, _⟩ := self
        refine ⟨D, ct_pinOn hD [r] (fun r' hr' _ _ => ?_), hDt⟩
        rw [List.mem_singleton] at hr'; subst hr'
        rw [htop, hDt]
        exact pinned_pinOn hE.docs hv r' (List.mem_singleton_self _) t ht (by rw [hts, htop])
      · have hcl : ClosedState (E.pinOn [r]) := closedState_pinOn hE hv (by omega)
        obtain ⟨w, hws, htw, _⟩ := hcl.pair (hcl.refl ht) r.step hr.1 (by rw [step_pinOn]; exact hr.2)
        obtain ⟨D, hD, hDt, hDw⟩ := he t htE hts w (hsub.adj _ _ htw.2.2)
        refine ⟨D, ct_pinOn hD [r] (fun r' hr' _ _ => ?_), hDt⟩
        rw [List.mem_singleton] at hr'; subst hr'
        rw [← hws, hDw]
        exact pinned_pinOn hE.docs hv r' (List.mem_singleton_self _) w htw.2.1 hws
    · obtain ⟨D, hD, hDt, _⟩ := self
      refine ⟨D, ct_pinOn hD [r] (fun r' hr' h0 h1 => ?_), hDt⟩
      rw [List.mem_singleton] at hr'; subst hr'
      exact absurd ⟨h0, h1⟩ hr

/-- **El filtro conserva `TopCT`**, desde `TopEdge` de la entrada. -/
theorem topCT_filter_of_topEdge {E : GPathB} {reqs : List NodeId} (hE : SInvB E) (hvE : E.isValid = true)
    (hlen : reqs.length ≤ 1) (he : TopEdge E) (hvY : (E.filterAllOn reqs).isValid = true) :
    TopCT (E.filterAllOn reqs) :=
  topCT_filterAllOn hE hvE hlen (topCT_of_topEdge he) (topAt_of_topEdge hE hlen he) hvY

/-- **Nivel 2 tras un pin, desde el nivel 3**: una arista viva `t–w` del estado fijado en un requisito tiene, en el
punto fijo de la regla, un testigo bueno `s` en el paso fijado; el triángulo `(t, w, s)` estaba sin prohibir en la
entrada, y su camarilla cumple el requisito. -/
theorem topEdgeAt_of_topTri {E : GPathB} {reqs : List NodeId} (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E)
    (hlen : reqs.length ≤ 1) (he : TopEdge E) (h3 : TopTri E) (hv : (E.pinOn reqs).isValid = true) :
    TopEdge (E.pinOn reqs) := by
  have hsub := sub_pinOn E reqs
  intro t ht hts w htw
  rw [step_pinOn] at hts ⊢
  have htE := hsub.alive t ht
  have base := he t htE hts w (hsub.adj _ _ htw)
  match reqs, hlen, hv, ht, htw, hsub with
  | [], _, _, _, _, _ =>
    obtain ⟨D, hD, hDt, hDw⟩ := base
    exact ⟨D, ct_pinOn hD [] (fun r hr => absurd hr List.not_mem_nil), hDt, hDw⟩
  | [r], _, hv, ht, htw, hsub =>
    have pinned := pinned_pinOn hE.docs hv r (List.mem_singleton_self _)
    have hih : SInvB (E.pinOn [r]) := sInvB_pinOn hE [r]
    have hwa : w ∈ (E.pinOn [r]).alive := (hih.edges t w htw).2
    by_cases hr : 0 ≤ r.step ∧ r.step < E.current_step
    · -- la camarilla de la entrada sirve si pasa por un nodo del requisito en su paso
      have close : ∀ D, CT E D → D r.step ∈ (E.pinOn [r]).alive → (D r.step).id.step = r.step →
          CT (E.pinOn [r]) D := by
        intro D hD hal hst
        refine ct_pinOn hD [r] (fun r' hr' _ _ => ?_)
        rw [List.mem_singleton] at hr'; subst hr'
        exact pinned _ hal hst
      by_cases hwt : w = t
      · obtain ⟨D, hD, hDt⟩ := topAt_of_topEdge (reqs := [r]) hE (by simp) he hv t ht hts
        exact ⟨D, hD, hDt, by rw [hwt, hts]; exact hDt⟩
      · have hf : FixClosed (E.pinOn [r]) :=
          fixClosed_reviewOn (g := { [r].foldl filterRequire E with dirty := true }) rfl hv
        have hg := trioGood_low hf (noDegT_pinOn hns hndt [r]) (Int.le_refl _)
        have hlt : ∀ {q : PathNodeId}, q ∈ (E.pinOn [r]).alive → q.id.step < (E.pinOn [r]).current_step :=
          fun hq => alive_below hih.docs hih.below hq
        have hR : LowR (E.pinOn [r]) (E.pinOn [r]).current_step t w := ⟨⟨ht, hwa, htw⟩, hlt ht, hlt hwa⟩
        obtain ⟨s, hss, hts', hws', hor⟩ := hg.edge hR (Ne.symm hwt) r.step hr.1 (by rw [step_pinOn]; exact hr.2)
        have hsa : s ∈ (E.pinOn [r]).alive := hts'.1.2.1
        by_cases hst : s = t
        · obtain ⟨D, hD, hDt, hDw⟩ := base
          have e : D r.step = t := by rw [← hss, hst, hts]; exact hDt
          exact ⟨D, close D hD (by rw [e]; exact ht) (by rw [e, ← hst]; exact hss), hDt, hDw⟩
        · by_cases hsw : s = w
          · obtain ⟨D, hD, hDt, hDw⟩ := base
            have e : D r.step = w := by rw [← hss, hsw]; exact hDw
            exact ⟨D, close D hD (by rw [e]; exact hwa) (by rw [e, ← hsw]; exact hss), hDt, hDw⟩
          · have hnT : ¬ TF (E.pinOn [r]) t w s := by
              rcases hor with h | h | h
              · exact absurd h hst
              · exact absurd h hsw
              · exact h
            have hnE : ¬ TF E t w s := fun hf' => hnT (tF_mono (trios_grow_pinOn E [r]) htw hf')
            obtain ⟨D, hD, hDt, hDw, hDs⟩ := h3 t htE hts w s (hsub.adj _ _ htw) (hsub.adj _ _ hts'.1.2.2)
              (hsub.adj _ _ hws'.1.2.2) (Ne.symm hwt) (Ne.symm hst) (Ne.symm hsw) hnE
            have e : D r.step = s := by rw [← hss]; exact hDs
            exact ⟨D, close D hD (by rw [e]; exact hsa) (by rw [e]; exact hss), hDt, hDw⟩
    · obtain ⟨D, hD, hDt, hDw⟩ := base
      refine ⟨D, ct_pinOn hD [r] (fun r' hr' h0 h1 => ?_), hDt, hDw⟩
      rw [List.mem_singleton] at hr'; subst hr'
      exact absurd ⟨h0, h1⟩ hr

/-- **El filtro conserva `TopEdge`**, desde `TopTri` de la entrada. -/
theorem topEdge_filterAllOn {E : GPathB} {reqs : List NodeId} (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E)
    (hvE : E.isValid = true) (hlen : reqs.length ≤ 1) (he : TopEdge E) (h3 : TopTri E)
    (hvY : (E.filterAllOn reqs).isValid = true) : TopEdge (E.filterAllOn reqs) := by
  cases hd : (reqs.foldl filterRequire E).dirty
  · -- el filtro no mata a nadie: la camarilla de la entrada cumple los requisitos
    intro t ht hts w htw
    rw [step_filterAllOn] at hts ⊢
    have hsh := (shrinks_filterAllOn E reqs).1
    obtain ⟨D, hD, hDt, hDw⟩ := he t (hsh.alive t ht) hts w (hsh.adj _ _ htw)
    refine ⟨D, ct_filterAllOn hD reqs ?_, hDt, hDw⟩
    intro r hr h0 h1
    have hr' : reqs = [r] := by
      match reqs, hlen, hr with
      | [x], _, hr => rw [List.mem_singleton] at hr; rw [hr]
    subst hr'
    have hd' : (E.filterRequire r).dirty = false := hd
    obtain ⟨n, hn, hnid⟩ := hE.docs (D r.step) (hD.1.alive r.step h0 h1)
    have hline : n ∈ E.line r.step := by
      unfold line
      refine List.mem_filter.mpr ⟨hn, ?_⟩
      rw [hnid, hD.1.step r.step h0 h1]
      simp
    have := filterRequire_noVictims hvE hd' n hline
    rw [hnid] at this
    exact this
  · -- el filtro mata algo: el estado filtrado es el fijado
    have e : E.filterAllOn reqs = E.pinOn reqs := by
      unfold filterAllOn pinOn
      congr 1
      generalize reqs.foldl filterRequire E = F at hd
      cases F
      simp_all
    rw [e] at hvY ⊢
    exact topEdgeAt_of_topTri hE hns hndt hlen he h3 hvY

-- ============================================================
-- El filtro en el nivel 3: lo que falta, en su forma de cuatro nodos
-- ============================================================

/-- **`PinTetra E r`**: un tetraedro `(t, u, w, s)` del estado fijado en `r`, con `t` cima, `s` en el paso del
requisito y sus cuatro caras sin prohibir, deja una camarilla de la entrada por `t`, `u` y `w` que cumple el requisito
(no hace falta que pase por `s`). Es lo único que el punto fijo de la regla no da: el testigo bueno del triángulo
`(t, u, w)` en el paso fijado existe, pero el tetraedro que forma puede no estar en ninguna camarilla. -/
def PinTetra (E : GPathB) (r : NodeId) : Prop :=
  ∀ t ∈ E.alive, t.id.step = E.current_step - 1 → ∀ u w s, s.id.step = r.step →
    (E.pinOn [r]).Adj t u → (E.pinOn [r]).Adj t w → (E.pinOn [r]).Adj u w →
    (E.pinOn [r]).Adj t s → (E.pinOn [r]).Adj u s → (E.pinOn [r]).Adj w s →
    t ≠ u → t ≠ w → u ≠ w → s ≠ t → s ≠ u → s ≠ w →
    ¬ TF (E.pinOn [r]) t u w → ¬ TF (E.pinOn [r]) t u s → ¬ TF (E.pinOn [r]) t w s → ¬ TF (E.pinOn [r]) u w s →
    ∃ D, CT E D ∧ D (E.current_step - 1) = t ∧ D u.id.step = u ∧ D w.id.step = w ∧ (D r.step).id = r

/-- **Nivel 3 tras un pin**, desde el nivel 3 de antes y `PinTetra`: el testigo bueno del triángulo en el paso fijado
(`trioGood_low`) o es uno de sus tres nodos, y basta el nivel 3 de la entrada, o forma el tetraedro de `PinTetra`. -/
theorem topTriAt_of_pinTetra {E : GPathB} {reqs : List NodeId} (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E)
    (hlen : reqs.length ≤ 1) (h3 : TopTri E) (h4 : ∀ r ∈ reqs, PinTetra E r)
    (hv : (E.pinOn reqs).isValid = true) : TopTri (E.pinOn reqs) := by
  have hsub := sub_pinOn E reqs
  intro t ht hts u w htu htw huw ntu ntw nuw hn
  rw [step_pinOn] at hts ⊢
  have htE := hsub.alive t ht
  have hnE : ¬ TF E t u w := fun hf' => hn (tF_mono (trios_grow_pinOn E reqs) htu hf')
  have base := h3 t htE hts u w (hsub.adj _ _ htu) (hsub.adj _ _ htw) (hsub.adj _ _ huw) ntu ntw nuw hnE
  match reqs, hlen, hv, ht, htu, htw, huw, hn, hsub, h4 with
  | [], _, _, _, _, _, _, _, _, _ =>
    obtain ⟨D, hD, hDt, hDu, hDw⟩ := base
    exact ⟨D, ct_pinOn hD [] (fun r hr => absurd hr List.not_mem_nil), hDt, hDu, hDw⟩
  | [r], _, hv, ht, htu, htw, huw, hn, hsub, h4 =>
    have pinned := pinned_pinOn hE.docs hv r (List.mem_singleton_self _)
    have hih : SInvB (E.pinOn [r]) := sInvB_pinOn hE [r]
    have hua : u ∈ (E.pinOn [r]).alive := (hih.edges t u htu).2
    have hwa : w ∈ (E.pinOn [r]).alive := (hih.edges t w htw).2
    by_cases hr : 0 ≤ r.step ∧ r.step < E.current_step
    · have agree : ∀ D : Int → PathNodeId, (D r.step).id = r → ∀ r' ∈ [r], Agrees E.current_step D r' := by
        intro D hD r' hr' _ _
        rw [List.mem_singleton] at hr'; subst hr'
        exact hD
      have hf : FixClosed (E.pinOn [r]) :=
        fixClosed_reviewOn (g := { [r].foldl filterRequire E with dirty := true }) rfl hv
      have hg := trioGood_low hf (noDegT_pinOn hns hndt [r]) (Int.le_refl _)
      have hlt : ∀ {q : PathNodeId}, q ∈ (E.pinOn [r]).alive → q.id.step < (E.pinOn [r]).current_step :=
        fun hq => alive_below hih.docs hih.below hq
      have R1 : LowR (E.pinOn [r]) (E.pinOn [r]).current_step t u := ⟨⟨ht, hua, htu⟩, hlt ht, hlt hua⟩
      have R2 : LowR (E.pinOn [r]) (E.pinOn [r]).current_step t w := ⟨⟨ht, hwa, htw⟩, hlt ht, hlt hwa⟩
      have R3 : LowR (E.pinOn [r]) (E.pinOn [r]).current_step u w := ⟨⟨hua, hwa, huw⟩, hlt hua, hlt hwa⟩
      obtain ⟨s, hss, hts', hus', hws', hor⟩ := hg.trio R1 R2 R3 ntu ntw nuw hn r.step hr.1
        (by rw [step_pinOn]; exact hr.2)
      have hsa : s ∈ (E.pinOn [r]).alive := hts'.1.2.1
      have hsid : s.id = r := pinned s hsa hss
      by_cases hst : s = t
      · obtain ⟨D, hD, hDt, hDu, hDw⟩ := base
        have e : D r.step = s := by rw [← hss, hst, hts]; exact hDt
        exact ⟨D, ct_pinOn hD [r] (agree D (by rw [e]; exact hsid)), hDt, hDu, hDw⟩
      · by_cases hsu : s = u
        · obtain ⟨D, hD, hDt, hDu, hDw⟩ := base
          have e : D r.step = s := by rw [← hss, hsu]; exact hDu
          exact ⟨D, ct_pinOn hD [r] (agree D (by rw [e]; exact hsid)), hDt, hDu, hDw⟩
        · by_cases hsw : s = w
          · obtain ⟨D, hD, hDt, hDu, hDw⟩ := base
            have e : D r.step = s := by rw [← hss, hsw]; exact hDw
            exact ⟨D, ct_pinOn hD [r] (agree D (by rw [e]; exact hsid)), hDt, hDu, hDw⟩
          · obtain ⟨n1, n2, n3⟩ : ¬ TF (E.pinOn [r]) t u s ∧ ¬ TF (E.pinOn [r]) t w s ∧ ¬ TF (E.pinOn [r]) u w s := by
              rcases hor with h | h | h | h
              · exact absurd h hst
              · exact absurd h hsu
              · exact absurd h hsw
              · exact h
            obtain ⟨D, hD, hDt, hDu, hDw, hDr⟩ := h4 r (List.mem_singleton_self _) t htE hts u w s hss htu htw huw
              hts'.1.2.2 hus'.1.2.2 hws'.1.2.2 ntu ntw nuw hst hsu hsw hn n1 n2 n3
            exact ⟨D, ct_pinOn hD [r] (agree D hDr), hDt, hDu, hDw⟩
    · obtain ⟨D, hD, hDt, hDu, hDw⟩ := base
      refine ⟨D, ct_pinOn hD [r] (fun r' hr' h0 h1 => ?_), hDt, hDu, hDw⟩
      rw [List.mem_singleton] at hr'; subst hr'
      exact absurd ⟨h0, h1⟩ hr

/-- **El filtro conserva `TopTri`**, bajo `PinTetra` de su requisito. -/
theorem topTri_filterAllOn {E : GPathB} {reqs : List NodeId} (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E)
    (hvE : E.isValid = true) (hlen : reqs.length ≤ 1) (h3 : TopTri E) (h4 : ∀ r ∈ reqs, PinTetra E r)
    (hvY : (E.filterAllOn reqs).isValid = true) : TopTri (E.filterAllOn reqs) := by
  cases hd : (reqs.foldl filterRequire E).dirty
  · -- el filtro no mata a nadie: la camarilla de la entrada cumple los requisitos
    intro t ht hts u w htu htw huw ntu ntw nuw hn
    rw [step_filterAllOn] at hts ⊢
    have hsh := (shrinks_filterAllOn E reqs).1
    have hnE : ¬ TF E t u w := fun hf' => hn (tF_mono (trios_grow_filterAllOn E reqs) htu hf')
    obtain ⟨D, hD, hDt, hDu, hDw⟩ := h3 t (hsh.alive t ht) hts u w (hsh.adj _ _ htu) (hsh.adj _ _ htw)
      (hsh.adj _ _ huw) ntu ntw nuw hnE
    refine ⟨D, ct_filterAllOn hD reqs ?_, hDt, hDu, hDw⟩
    intro r hr h0 h1
    have hr' : reqs = [r] := by
      match reqs, hlen, hr with
      | [x], _, hr => rw [List.mem_singleton] at hr; rw [hr]
    subst hr'
    have hd' : (E.filterRequire r).dirty = false := hd
    obtain ⟨n, hn', hnid⟩ := hE.docs (D r.step) (hD.1.alive r.step h0 h1)
    have hline : n ∈ E.line r.step := by
      unfold line
      refine List.mem_filter.mpr ⟨hn', ?_⟩
      rw [hnid, hD.1.step r.step h0 h1]
      simp
    have := filterRequire_noVictims hvE hd' n hline
    rw [hnid] at this
    exact this
  · have e : E.filterAllOn reqs = E.pinOn reqs := by
      unfold filterAllOn pinOn
      congr 1
      generalize reqs.foldl filterRequire E = F at hd
      cases F
      simp_all
    rw [e] at hvY ⊢
    exact topTriAt_of_pinTetra hE hns hndt hlen h3 h4 hvY

-- ============================================================
-- El UP
-- ============================================================

section Up

variable {Y : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- Un vecino viejo de un nodo de la fila lo posee uno de sus padres. -/
theorem rowParent_of_newAdj (hdocs : AliveDocs Y) (hb : Below Y) (hea : EdgesAlive Y) (hd : d.step = Y.current_step)
    {t r : PathNodeId} (ht : t ∈ Y.newRowIds d forb) (hr : r.id.step < Y.current_step)
    (h : (Y.addNode d title forb).Adj t r) : ∃ q ∈ Y.rowParents d t, Y.Adj q r := by
  have hts : t.id.step = Y.current_step := newRow_step hd ht
  rw [adj_iff] at h
  rcases h with ⟨rfl, _⟩ | ⟨e, he, hj⟩
  · omega
  · rcases List.mem_append.mp he with h1 | h1
    · have hold : Y.Adj t r := (adj_iff Y t r).mpr (Or.inr ⟨e, h1, hj⟩)
      have := alive_below hdocs hb (hea t r hold).1
      omega
    · obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp h1
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 : pid = t := h1
        have e2 : w' = r := h2
        subst e1; subst e2
        obtain ⟨_, hany⟩ := List.mem_filter.mp hw'
        obtain ⟨_, hany⟩ := Bool.and_eq_true_iff.mp hany
        obtain ⟨q, hq, hqw⟩ := List.any_eq_true.mp hany
        exact ⟨q, hq, hqw⟩
      · have e1 : pid = r := h1
        subst e1
        have := newRow_step hd hpid
        omega

/-- Una camarilla del remitente por un padre de la cima nueva `t` se alarga con `t`. -/
theorem ct_ext_top (hiY : SInvB Y) (htb : TB Y) (hd : d.step = Y.current_step) (hpos : 1 ≤ Y.current_step)
    {t q : PathNodeId} (htnew : t ∈ Y.newRowIds d forb) (hq : q ∈ Y.rowParents d t) {D : Int → PathNodeId}
    (hD : CT Y D) (hDq : D (Y.current_step - 1) = q) :
    CT (Y.upOn d title forb) (extSel D Y.current_step t) ∧ extSel D Y.current_step t Y.current_step = t ∧
      ∀ k, k ≠ Y.current_step → extSel D Y.current_step t k = D k := by
  have hS : CT Y (extSel D Y.current_step t) :=
    ct_congr hD (fun k _ h1 => by simp [extSel, show k ≠ Y.current_step by omega])
  have e0 : extSel D Y.current_step t Y.current_step = t := by simp [extSel]
  have e1 : extSel D Y.current_step t (Y.current_step - 1) = D (Y.current_step - 1) := by
    simp [extSel, show Y.current_step - 1 ≠ Y.current_step by omega]
  have e2 : extSel D Y.current_step t 0 = D 0 := by
    simp [extSel, show (0 : Int) ≠ Y.current_step by omega]
  exact ⟨ct_upOn hS htb (by rw [e0]; exact htnew) (fun _ => by rw [e0, e1, hDq]; exact hq)
    (by rw [e0]; exact newRow_step hd htnew) hiY.below (by rw [e2]; exact hD.1.root (by omega)), e0,
    fun k hk => by simp [extSel, hk]⟩

/-- **El UP conserva `TopEdge`**: el vecino de la cima nueva lo posee un padre suyo, cima del remitente. -/
theorem topEdge_upOn (hiY : SInvB Y) (htb : TB Y) (hda : DocsAlive Y) (hd : d.step = Y.current_step)
    (hpos : 1 ≤ Y.current_step) (hvY : Y.isValid = true) (he : TopEdge Y) : TopEdge (Y.upOn d title forb) := by
  intro t ht hts w htw
  have hsub := sub_upOn_addNode (d := d) (title := title) (forb := forb) hvY
  have hcsA : (Y.upOn d title forb).current_step = Y.current_step + 1 := by rw [hsub.step]; rfl
  have hiA : SInvB (Y.upOn d title forb) := sInvB_upOn hiY hd (by omega)
  have hts' : t.id.step = Y.current_step := by rw [hts, hcsA]; omega
  have htnew : t ∈ Y.newRowIds d forb := by
    rcases alive_addNode_cases (title := title) (forb := forb) hiY.docs hiY.below hd (hsub.alive t ht) with
      ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  by_cases hwt : w = t
  · obtain ⟨D, hD, hDt⟩ := topCT_upOn (title := title) (forb := forb) hiY htb hda hd hpos hvY (topCT_of_topEdge he)
      t ht hts
    exact ⟨D, hD, hDt, by rw [hwt, hts]; exact hDt⟩
  · have hwa : w ∈ (Y.upOn d title forb).alive := (hiA.edges t w htw).2
    have hwold : w.id.step < Y.current_step := by
      rcases alive_addNode_cases (title := title) (forb := forb) hiY.docs hiY.below hd (hsub.alive w hwa) with
        ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · exact absurd (adj_addNode_new (title := title) (forb := forb) hiY.docs hiY.below hiY.edges hts' h
          (hsub.adj _ _ htw)).symm hwt
    obtain ⟨q, hq, hqw⟩ := rowParent_of_newAdj (title := title) hiY.docs hiY.below hiY.edges hd htnew hwold
      (hsub.adj _ _ htw)
    obtain ⟨_, _, _, hqs⟩ := step_of_newParents (rowParents_sub hq)
    obtain ⟨D, hD, hDq, hDw⟩ := he q (hiY.edges q w hqw).1 hqs w hqw
    obtain ⟨hct, e0, eo⟩ := ct_ext_top (title := title) hiY htb hd hpos htnew hq hD hDq
    refine ⟨_, hct, by rw [hcsA, show Y.current_step + 1 - 1 = Y.current_step by omega]; exact e0, ?_⟩
    rw [eo _ (by omega)]; exact hDw

/-- **El UP conserva `TopTri`**: la cara de la cima nueva la sostiene un padre suyo en el remitente
(`upOn_face_parent`), y el triángulo del padre está en una camarilla que se alarga con la cima. -/
theorem topTri_upOn (hiY : SInvB Y) (htb : TB Y) (hd : d.step = Y.current_step) (hpos : 1 ≤ Y.current_step)
    (hvY : Y.isValid = true) (he : TopEdge Y) (h3 : TopTri Y) : TopTri (Y.upOn d title forb) := by
  intro t ht hts u w htu htw huw ntu ntw nuw hn
  have hsub := sub_upOn_addNode (d := d) (title := title) (forb := forb) hvY
  have hcsA : (Y.upOn d title forb).current_step = Y.current_step + 1 := by rw [hsub.step]; rfl
  have hiA : SInvB (Y.upOn d title forb) := sInvB_upOn hiY hd (by omega)
  have hts' : t.id.step = Y.current_step := by rw [hts, hcsA]; omega
  have htnew : t ∈ Y.newRowIds d forb := by
    rcases alive_addNode_cases (title := title) (forb := forb) hiY.docs hiY.below hd (hsub.alive t ht) with
      ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  have old : ∀ {q : PathNodeId}, (Y.upOn d title forb).Adj t q → t ≠ q →
      q ∈ (Y.upOn d title forb).alive ∧ q.id.step < Y.current_step := by
    intro q htq hne
    have hqa : q ∈ (Y.upOn d title forb).alive := (hiA.edges t q htq).2
    refine ⟨hqa, ?_⟩
    rcases alive_addNode_cases (title := title) (forb := forb) hiY.docs hiY.below hd (hsub.alive q hqa) with
      ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd (adj_addNode_new (title := title) (forb := forb) hiY.docs hiY.below hiY.edges hts' h
        (hsub.adj _ _ htq)) hne
  obtain ⟨hua, hus⟩ := old htu ntu
  obtain ⟨hwa, hws⟩ := old htw ntw
  obtain ⟨p, hp, hpu, hpw, huw', hnt⟩ := upOn_face_parent (title := title) (forb := forb) hiY hd hvY ht hts' hua hwa
    hus hws nuw htu htw huw hn
  obtain ⟨_, _, _, hps⟩ := step_of_newParents (rowParents_sub hp)
  have hpa : p ∈ Y.alive := (hiY.edges p u hpu).1
  have fin : ∀ D, CT Y D → D (Y.current_step - 1) = p → D u.id.step = u → D w.id.step = w →
      ∃ D', CT (Y.upOn d title forb) D' ∧ D' ((Y.upOn d title forb).current_step - 1) = t ∧
        D' u.id.step = u ∧ D' w.id.step = w := by
    intro D hD hDp hDu hDw
    obtain ⟨hct, e0, eo⟩ := ct_ext_top (title := title) hiY htb hd hpos htnew hp hD hDp
    refine ⟨_, hct, by rw [hcsA, show Y.current_step + 1 - 1 = Y.current_step by omega]; exact e0, ?_, ?_⟩
    · rw [eo _ (by omega)]; exact hDu
    · rw [eo _ (by omega)]; exact hDw
  by_cases hpu' : p = u
  · obtain ⟨D, hD, hDp, hDw⟩ := he p hpa hps w hpw
    exact fin D hD hDp (by rw [← hpu', hps]; exact hDp) hDw
  · by_cases hpw' : p = w
    · obtain ⟨D, hD, hDp, hDu⟩ := he p hpa hps u hpu
      exact fin D hD hDp hDu (by rw [← hpw', hps]; exact hDp)
    · have hnf : ¬ TF Y p u w := by
        intro hf
        have hd' := hf.2
        unfold deadTrio at hd'
        rw [Bool.and_eq_true] at hd'
        obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd'.2
        rw [hnt hpu' hpw' τ hτ] at hti
        cases hti
      obtain ⟨D, hD, hDp, hDu, hDw⟩ := h3 p hpa hps u w hpu hpw huw' hpu' hpw' nuw hnf
      exact fin D hD hDp hDu hDw

end Up

-- ============================================================
-- El invariante de línea
-- ============================================================

/-- **El invariante de niveles de la línea `:on`** del paso `T`: la contabilidad de siempre y, en cada entrada,
`TopEdge` y `TopTri` (del estado tal cual, sin pins). -/
structure LInvX (φ : Cnf) (T : Int) (line : Line) : Prop where
  on    : LineOn T line
  nodup : (line.map (·.1)).Nodup
  keys  : ∀ kv ∈ line, kv.1 ∈ mapNodes φ (T - 1)
  inv   : ∀ kv ∈ line, SInvB kv.2
  ndt   : ∀ kv ∈ line, NoDegT kv.2
  docs  : ∀ kv ∈ line, DocsAlive kv.2
  edge  : ∀ kv ∈ line, TopEdge kv.2
  tri   : ∀ kv ∈ line, TopTri kv.2

/-- **El caso base**: la semilla tiene un solo vivo, la raíz. -/
theorem lInvX_init (φ : Cnf) : LInvX φ 1 (initM .on φ) := by
  have h0 := lInvOn_init φ
  obtain ⟨hl, g, hf, hct⟩ := initOn_inv φ (fun _ => false)
  rw [initM_eq] at hf
  let d : NodeId := ⟨0, 0⟩
  have hg : g = initSeedOn d "" := by
    have := List.mem_of_find?_eq_some hf
    rw [List.mem_singleton] at this
    exact (Prod.mk.inj this).2
  subst hg
  have hmem : (d, initSeedOn d "") ∈ initM .on φ := by rw [initM_eq]; exact List.mem_singleton_self _
  have hstep : (initSeedOn d "").current_step = 1 := (hl _ hmem).1.step
  have hsub : Sub (initSeedOn d "") (GPathB.empty.addNode d "" (fun _ => false)) :=
    sub_upOn_addNode (g := GPathB.empty) (by rfl)
  have huniq : ∀ q ∈ (initSeedOn d "").alive, q = { id := ⟨0, 0⟩, parent_id := none, gparent_id := none } := by
    intro q hq
    have := hsub.alive q hq
    rw [seedRow_alive] at this
    exact List.mem_singleton.mp this
  have hea : EdgesAlive (initSeedOn d "") := (h0.inv _ hmem).edges
  have one : ∀ {t w : PathNodeId}, (initSeedOn d "").Adj t w → t = w :=
    fun h => (huniq _ (hea _ _ h).1).trans (huniq _ (hea _ _ h).2).symm
  have hS0 : ∀ t ∈ (initSeedOn d "").alive, pidOfAssign φ (fun _ => false) 0 = t := fun t ht =>
    (huniq _ (hct.1.alive 0 (Int.le_refl 0) (by rw [hstep]; omega))).trans (huniq t ht).symm
  refine ⟨h0.on, h0.nodup, h0.keys, h0.inv, h0.ndt, fun kv hkv => ((lineRaw_init φ) kv hkv).1, ?_, ?_⟩
  · rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    intro t ht hts w htw
    have e := hS0 t ht
    refine ⟨pidOfAssign φ (fun _ => false), hct, ?_, ?_⟩
    · show pidOfAssign φ (fun _ => false) ((initSeedOn d "").current_step - 1) = t
      rw [hstep]; exact e
    · have hts' : t.id.step = (initSeedOn d "").current_step - 1 := hts
      rw [← one htw, hts', hstep]; exact e
  · rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    intro t _ _ u w htu _ _ ntu
    exact absurd (one htu) ntu

/-- **`HTriKeep`**: en cada llegada de la línea, el filtro de su requisito conserva `TopTri` (dados `TopEdge` y
`TopTri` de la entrada). Un estado y un requisito: sin lados y sin listas de pins. -/
def HTriKeep (φ : Cnf) (line : Line) : Prop :=
  ∀ kv ∈ line, ∀ d, SendsOn φ kv d → TopEdge kv.2 → TopTri kv.2 → TopTri (kv.2.filterAllOn (reqOf φ d))

/-- Lo que se sabe de una llegada válida de una entrada de la línea, bajo `HTriKeep`. -/
theorem arrX_facts {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvX φ T line) (hk : HTriKeep φ line)
    {kv : NodeId × GPathB} (hkv : kv ∈ line) {d : NodeId} (hs : SendsOn φ kv d) :
    EntOn (T + 1) d (arrOn φ kv d) ∧ SInvB (arrOn φ kv d) ∧ NoDegT (arrOn φ kv d) ∧ DocsAlive (arrOn φ kv d) ∧
    TopEdge (arrOn φ kv d) ∧ TopTri (arrOn φ kv d) ∧ d ∈ mapNodes φ T := by
  have hent := h.on kv hkv
  have hok := hent.1
  have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
  have hi := h.inv kv hkv
  have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
  have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [step_filterAllOn]; exact hd
  have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
    valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
  have hiY := sInvB_filterAllOn hi (reqOf φ d)
  have htbY := tb_filterAllOn hent.2.2 (reqOf φ d)
  have hdaY := docsAlive_filterAllOn (h.docs kv hkv) (reqOf φ d) hvY
  have heY : TopEdge (kv.2.filterAllOn (reqOf φ d)) :=
    topEdge_filterAllOn hi hent.2.1 (h.ndt kv hkv) hok.valid (reqOf_length_le_one φ d) (h.edge kv hkv)
      (h.tri kv hkv) hvY
  have h3Y : TopTri (kv.2.filterAllOn (reqOf φ d)) := hk kv hkv d hs (h.edge kv hkv) (h.tri kv hkv)
  have hposY : 1 ≤ (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [hcsY]; exact hT
  refine ⟨entOn_upFilteringOn hent hs.1 hs.2,
    sInvB_upOn hiY hdY (by rw [hd, hok.step]; omega),
    noDegT_upOn (noSelf_filterAllOn hent.2.1 _) (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _),
    docsAlive_upOn hdaY hvY hs.2,
    topEdge_upOn hiY htbY hdaY hdY hposY hvY heY,
    topTri_upOn hiY htbY hdY hposY hvY heY h3Y, ?_⟩
  have hk' : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact h.keys kv hkv
  have := sonsOfMap_subset φ kv.1 hk' d hs.1
  rw [hok.key, show T - 1 + 1 = T by omega] at this
  exact this

/-- **El paso de la máquina `:on`**: el invariante de niveles pasa a la línea siguiente bajo `HTriKeep`. El join no
pide nada. -/
theorem lInvX_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvX φ T line)
    (hk : HTriKeep φ line) : LInvX φ (T + 1) (advanceM .on φ line) := by
  have hlen := line_cases h.nodup h.keys
  have ent : ∀ E ∈ advanceM .on φ line, SInvB E.2 ∧ NoDegT E.2 ∧ DocsAlive E.2 ∧ TopEdge E.2 ∧ TopTri E.2 ∧
      E.1 ∈ mapNodes φ T := by
    intro E hE
    rcases entry_shapeOn hlen h.nodup hE with ⟨kv, hkv, hs, he⟩ | ⟨a, ha, b, hb, _, hsa, hsb, he⟩
    · obtain ⟨_, hi, hn, hda, h2, h3, hm⟩ := arrX_facts hT h hk hkv hs
      rw [he]; exact ⟨hi, hn, hda, h2, h3, hm⟩
    · obtain ⟨ea, ia, _, da, a2, a3, hm⟩ := arrX_facts hT h hk ha hsa
      obtain ⟨eb, ib, _, db, b2, b3, _⟩ := arrX_facts hT h hk hb hsb
      have hcs : (arrOn φ a E.1).current_step = (arrOn φ b E.1).current_step := ea.1.step.trans eb.1.step.symm
      have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
        unfold doJoinOn okJoin
        rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
      rw [he, hjoin]
      exact ⟨sInvB_joinOn ia ib hcs, noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges, docsAlive_joinOn da db,
        topEdge_joinOn a2 b2 ea.2.1 eb.2.1 ia.edges ib.edges hcs,
        topTri_joinOn a3 b3 ea.2.1 eb.2.1 ia.edges ib.edges hcs, hm⟩
  exact ⟨lineOn_advance h.on, advanceOn_nodup φ line,
    fun E hE => by rw [show T + 1 - 1 = T by omega]; exact (ent E hE).2.2.2.2.2,
    fun E hE => (ent E hE).1, fun E hE => (ent E hE).2.1, fun E hE => (ent E hE).2.2.1,
    fun E hE => (ent E hE).2.2.2.1, fun E hE => (ent E hE).2.2.2.2.1⟩

/-- **La hipótesis**: en cada línea de la máquina `:on`, el filtro de cada llegada conserva `TopTri`. -/
def HypsTriKeep (φ : Cnf) : Prop := ∀ n : Nat, HTriKeep φ (stepsM .on φ n (initM .on φ))

theorem lInvX_steps {φ : Cnf} (H : HypsTriKeep φ) :
    ∀ n : Nat, LInvX φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => exact lInvX_init φ
  | succ n ih =>
    rw [stepsM_succ]
    have := lInvX_advance (by omega) ih (H n)
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

/-- La forma que se mide: `TopTri` en todos los remitentes filtrados (`TopTri` del estado tras el filtro de cada
llegada, sin condiciones). -/
def HypsTriFlt (φ : Cnf) : Prop :=
  ∀ n : Nat, ∀ kv ∈ stepsM .on φ n (initM .on φ), ∀ d, SendsOn φ kv d → TopTri (kv.2.filterAllOn (reqOf φ d))

theorem hypsTriKeep_of_flt {φ : Cnf} (H : HypsTriFlt φ) : HypsTriKeep φ :=
  fun n kv hkv d hs _ _ => H n kv hkv d hs

/-- `PinTetra` en las llegadas de una línea, para su requisito. -/
def HPinTetra (φ : Cnf) (line : Line) : Prop :=
  ∀ kv ∈ line, ∀ d, SendsOn φ kv d → TopEdge kv.2 → TopTri kv.2 → ∀ r ∈ reqOf φ d, PinTetra kv.2 r

theorem hTriKeep_of_pinTetra {φ : Cnf} {T : Int} {line : Line} (h : LInvX φ T line) (hp : HPinTetra φ line) :
    HTriKeep φ line :=
  fun kv hkv d hs he h3 => topTri_filterAllOn (h.inv kv hkv) (h.on kv hkv).2.1 (h.ndt kv hkv) (h.on kv hkv).1.valid
    (reqOf_length_le_one φ d) h3 (hp kv hkv d hs he h3) (valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2)

/-- **La hipótesis en su forma de cuatro nodos**: `PinTetra` en cada llegada de la máquina, para su requisito. -/
def HypsPinTetra (φ : Cnf) : Prop := ∀ n : Nat, HPinTetra φ (stepsM .on φ n (initM .on φ))

theorem lInvX_steps_pin {φ : Cnf} (H : HypsPinTetra φ) :
    ∀ n : Nat, LInvX φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => exact lInvX_init φ
  | succ n ih =>
    rw [stepsM_succ]
    have := lInvX_advance (by omega) ih (hTriKeep_of_pinTetra ih (H n))
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

theorem hypsTriKeep_of_pinTetra {φ : Cnf} (H : HypsPinTetra φ) : HypsTriKeep φ :=
  fun n => hTriKeep_of_pinTetra (lInvX_steps_pin H n) (H n)

/-- **Bajo `HypsTriKeep`, todo estado de la máquina es exacto en sus cimas hasta el nivel 3.** -/
theorem exact_of_triKeep {φ : Cnf} (H : HypsTriKeep φ) (n : Nat) :
    ∀ kv ∈ stepsM .on φ n (initM .on φ), TopCT kv.2 ∧ TopEdge kv.2 ∧ TopTri kv.2 :=
  fun kv hkv => ⟨topCT_of_topEdge ((lInvX_steps H n).edge kv hkv), (lInvX_steps H n).edge kv hkv,
    (lInvX_steps H n).tri kv hkv⟩

-- ============================================================
-- La escalera: un invariante de línea por nivel, y cada nivel da el de abajo
-- ============================================================

/-- El invariante de línea con una propiedad `P` de los estados (sin pins). -/
structure LInvP (P : GPathB → Prop) (φ : Cnf) (T : Int) (line : Line) : Prop where
  on    : LineOn T line
  nodup : (line.map (·.1)).Nodup
  keys  : ∀ kv ∈ line, kv.1 ∈ mapNodes φ (T - 1)
  inv   : ∀ kv ∈ line, SInvB kv.2
  ndt   : ∀ kv ∈ line, NoDegT kv.2
  docs  : ∀ kv ∈ line, DocsAlive kv.2
  p     : ∀ kv ∈ line, P kv.2

/-- `P` pasa el UP y el join de la máquina. -/
structure OpsP (P : GPathB → Prop) : Prop where
  up   : ∀ {Y : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}, SInvB Y → TB Y → DocsAlive Y →
           d.step = Y.current_step → 1 ≤ Y.current_step → Y.isValid = true → P Y → P (Y.upOn d title forb)
  join : ∀ {A B : GPathB}, P A → P B → NoSelf A → NoSelf B → EdgesAlive A → EdgesAlive B →
           A.current_step = B.current_step → P (joinOn A B)

theorem opsP_topCT : OpsP TopCT :=
  ⟨fun hiY htb hda hd hpos hvY h => topCT_upOn hiY htb hda hd hpos hvY h,
   fun hA hB hnsA hnsB _ _ hcs => topCT_joinOn hA hB hnsA hnsB hcs⟩

theorem opsP_topEdge : OpsP TopEdge :=
  ⟨fun hiY htb hda hd hpos hvY h => topEdge_upOn hiY htb hda hd hpos hvY h,
   fun hA hB hnsA hnsB heA heB hcs => topEdge_joinOn hA hB hnsA hnsB heA heB hcs⟩

/-- **El filtro de cada llegada de la línea conserva `P`.** -/
def HKeepP (P : GPathB → Prop) (φ : Cnf) (line : Line) : Prop :=
  ∀ kv ∈ line, ∀ d, SendsOn φ kv d → P kv.2 → P (kv.2.filterAllOn (reqOf φ d))

/-- **El paso de la máquina**: si `P` pasa el UP y el join, el invariante pasa a la línea siguiente cuando el filtro de
cada llegada conserva `P`. -/
theorem lInvP_advance {P : GPathB → Prop} (ops : OpsP P) {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line}
    (h : LInvP P φ T line) (hk : HKeepP P φ line) : LInvP P φ (T + 1) (advanceM .on φ line) := by
  have hlen := line_cases h.nodup h.keys
  have arr : ∀ kv ∈ line, ∀ d, SendsOn φ kv d →
      EntOn (T + 1) d (arrOn φ kv d) ∧ SInvB (arrOn φ kv d) ∧ NoDegT (arrOn φ kv d) ∧ DocsAlive (arrOn φ kv d) ∧
      P (arrOn φ kv d) ∧ d ∈ mapNodes φ T := by
    intro kv hkv d hs
    have hent := h.on kv hkv
    have hok := hent.1
    have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
    have hi := h.inv kv hkv
    have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
    have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [step_filterAllOn]; exact hd
    have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
      valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
    have hiY := sInvB_filterAllOn hi (reqOf φ d)
    have hdaY := docsAlive_filterAllOn (h.docs kv hkv) (reqOf φ d) hvY
    refine ⟨entOn_upFilteringOn hent hs.1 hs.2,
      sInvB_upOn hiY hdY (by rw [hd, hok.step]; omega),
      noDegT_upOn (noSelf_filterAllOn hent.2.1 _) (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _),
      docsAlive_upOn hdaY hvY hs.2,
      ops.up hiY (tb_filterAllOn hent.2.2 (reqOf φ d)) hdaY hdY (by rw [hcsY]; exact hT) hvY
        (hk kv hkv d hs (h.p kv hkv)), ?_⟩
    have hk' : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact h.keys kv hkv
    have := sonsOfMap_subset φ kv.1 hk' d hs.1
    rw [hok.key, show T - 1 + 1 = T by omega] at this
    exact this
  have ent : ∀ E ∈ advanceM .on φ line, SInvB E.2 ∧ NoDegT E.2 ∧ DocsAlive E.2 ∧ P E.2 ∧ E.1 ∈ mapNodes φ T := by
    intro E hE
    rcases entry_shapeOn hlen h.nodup hE with ⟨kv, hkv, hs, he⟩ | ⟨a, ha, b, hb, _, hsa, hsb, he⟩
    · obtain ⟨_, hi, hn, hda, hp, hm⟩ := arr kv hkv E.1 hs
      rw [he]; exact ⟨hi, hn, hda, hp, hm⟩
    · obtain ⟨ea, ia, _, da, pa, hm⟩ := arr a ha E.1 hsa
      obtain ⟨eb, ib, _, db, pb, _⟩ := arr b hb E.1 hsb
      have hcs : (arrOn φ a E.1).current_step = (arrOn φ b E.1).current_step := ea.1.step.trans eb.1.step.symm
      have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
        unfold doJoinOn okJoin
        rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
      rw [he, hjoin]
      exact ⟨sInvB_joinOn ia ib hcs, noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges, docsAlive_joinOn da db,
        ops.join pa pb ea.2.1 eb.2.1 ia.edges ib.edges hcs, hm⟩
  exact ⟨lineOn_advance h.on, advanceOn_nodup φ line,
    fun E hE => by rw [show T + 1 - 1 = T by omega]; exact (ent E hE).2.2.2.2,
    fun E hE => (ent E hE).1, fun E hE => (ent E hE).2.1, fun E hE => (ent E hE).2.2.1,
    fun E hE => (ent E hE).2.2.2.1⟩

theorem lInvP_steps {P : GPathB → Prop} (ops : OpsP P) {φ : Cnf} (h0 : LInvP P φ 1 (initM .on φ))
    (H : ∀ n : Nat, HKeepP P φ (stepsM .on φ n (initM .on φ))) :
    ∀ n : Nat, LInvP P φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [stepsM_succ]
    have := lInvP_advance ops (by omega) ih (H n)
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

theorem lInvP_edge_of_x {φ : Cnf} {T : Int} {line : Line} (h : LInvX φ T line) : LInvP TopEdge φ T line :=
  ⟨h.on, h.nodup, h.keys, h.inv, h.ndt, h.docs, h.edge⟩

theorem lInvP_node_of_edge {φ : Cnf} {T : Int} {line : Line} (h : LInvP TopEdge φ T line) : LInvP TopCT φ T line :=
  ⟨h.on, h.nodup, h.keys, h.inv, h.ndt, h.docs, fun kv hkv => topCT_of_topEdge (h.p kv hkv)⟩

/-- **Nivel 1**: el filtro de cada llegada conserva «toda cima viva está en una camarilla». -/
def HypsNodeKeep (φ : Cnf) : Prop := ∀ n : Nat, HKeepP TopCT φ (stepsM .on φ n (initM .on φ))

/-- **Nivel 2**: el filtro de cada llegada conserva «toda arista viva de una cima está en una camarilla». -/
def HypsEdgeKeep (φ : Cnf) : Prop := ∀ n : Nat, HKeepP TopEdge φ (stepsM .on φ n (initM .on φ))

theorem lInvP_node_steps {φ : Cnf} (H : HypsNodeKeep φ) :
    ∀ n : Nat, LInvP TopCT φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) :=
  lInvP_steps opsP_topCT (lInvP_node_of_edge (lInvP_edge_of_x (lInvX_init φ))) H

theorem lInvP_edge_steps {φ : Cnf} (H : HypsEdgeKeep φ) :
    ∀ n : Nat, LInvP TopEdge φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) :=
  lInvP_steps opsP_topEdge (lInvP_edge_of_x (lInvX_init φ)) H

/-- **Del nivel 2 al 1, sin hipótesis**: donde las entradas cumplen `TopEdge`, el filtro conserva `TopCT`. -/
theorem hKeep_node_of_edge {φ : Cnf} {T : Int} {line : Line} (h : LInvP TopEdge φ T line) : HKeepP TopCT φ line :=
  fun kv hkv d hs _ => topCT_filter_of_topEdge (h.inv kv hkv) (h.on kv hkv).1.valid (reqOf_length_le_one φ d)
    (h.p kv hkv) (valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2)

/-- **Del nivel 3 al 2, sin hipótesis**: donde las entradas cumplen `TopEdge` y `TopTri`, el filtro conserva
`TopEdge`. -/
theorem hKeep_edge_of_x {φ : Cnf} {T : Int} {line : Line} (h : LInvX φ T line) : HKeepP TopEdge φ line :=
  fun kv hkv d hs _ => topEdge_filterAllOn (h.inv kv hkv) (h.on kv hkv).2.1 (h.ndt kv hkv) (h.on kv hkv).1.valid
    (reqOf_length_le_one φ d) (h.edge kv hkv) (h.tri kv hkv)
    (valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2)

/-- **La escalera de hipótesis**: cada nivel da el de abajo. -/
theorem hypsNodeKeep_of_edgeKeep {φ : Cnf} (H : HypsEdgeKeep φ) : HypsNodeKeep φ :=
  fun n => hKeep_node_of_edge (lInvP_edge_steps H n)

theorem hypsEdgeKeep_of_triKeep {φ : Cnf} (H : HypsTriKeep φ) : HypsEdgeKeep φ :=
  fun n => hKeep_edge_of_x (lInvX_steps H n)

-- ============================================================
-- El filtro con el requisito en la cima no consume nivel
-- ============================================================

/-- **Un requisito en el paso de la cima no consume nivel**: una camarilla de la entrada por una cima que sobrevive al
filtro cumple el requisito sola, porque en el paso del requisito pasa por esa cima. -/
theorem ct_filter_of_topReq {E : GPathB} {reqs : List NodeId} (hE : SInvB E)
    (htr : ∀ r ∈ reqs, r.step = E.current_step - 1) (hvY : (E.filterAllOn reqs).isValid = true)
    {t : PathNodeId} (ht : t ∈ (E.filterAllOn reqs).alive) (hts : t.id.step = E.current_step - 1)
    {D : Int → PathNodeId} (hD : CT E D) (hDt : D (E.current_step - 1) = t) : CT (E.filterAllOn reqs) D := by
  refine ct_filterAllOn hD reqs (fun r hr _ _ => ?_)
  rw [htr r hr, hDt]
  have hs1 : Sub (E.filterAllOn reqs) (reqs.foldl filterRequire E) := (shrinks_reviewOn _).1
  exact pinned_foldl reqs E hE.docs (isValid_of_sub hs1 hvY) t (hs1.alive t ht) hr (by rw [hts, htr r hr])

/-- Con los requisitos en la cima, el filtro conserva los tres niveles sin pedir el de encima. -/
theorem topCT_filter_topReq {E : GPathB} {reqs : List NodeId} (hE : SInvB E)
    (htr : ∀ r ∈ reqs, r.step = E.current_step - 1) (h : TopCT E) (hvY : (E.filterAllOn reqs).isValid = true) :
    TopCT (E.filterAllOn reqs) := by
  intro t ht hts
  rw [step_filterAllOn] at hts ⊢
  obtain ⟨D, hD, hDt⟩ := h t ((shrinks_filterAllOn E reqs).1.alive t ht) hts
  exact ⟨D, ct_filter_of_topReq hE htr hvY ht hts hD hDt, hDt⟩

theorem topEdge_filter_topReq {E : GPathB} {reqs : List NodeId} (hE : SInvB E)
    (htr : ∀ r ∈ reqs, r.step = E.current_step - 1) (h : TopEdge E) (hvY : (E.filterAllOn reqs).isValid = true) :
    TopEdge (E.filterAllOn reqs) := by
  intro t ht hts w htw
  rw [step_filterAllOn] at hts ⊢
  have hsh := (shrinks_filterAllOn E reqs).1
  obtain ⟨D, hD, hDt, hDw⟩ := h t (hsh.alive t ht) hts w (hsh.adj _ _ htw)
  exact ⟨D, ct_filter_of_topReq hE htr hvY ht hts hD hDt, hDt, hDw⟩

theorem topTri_filter_topReq {E : GPathB} {reqs : List NodeId} (hE : SInvB E)
    (htr : ∀ r ∈ reqs, r.step = E.current_step - 1) (h : TopTri E) (hvY : (E.filterAllOn reqs).isValid = true) :
    TopTri (E.filterAllOn reqs) := by
  intro t ht hts u w htu htw huw ntu ntw nuw hn
  rw [step_filterAllOn] at hts ⊢
  have hsh := (shrinks_filterAllOn E reqs).1
  have hnE : ¬ TF E t u w := fun hf' => hn (tF_mono (trios_grow_filterAllOn E reqs) htu hf')
  obtain ⟨D, hD, hDt, hDu, hDw⟩ := h t (hsh.alive t ht) hts u w (hsh.adj _ _ htu) (hsh.adj _ _ htw)
    (hsh.adj _ _ huw) ntu ntw nuw hnE
  exact ⟨D, ct_filter_of_topReq hE htr hvY ht hts hD hDt, hDt, hDu, hDw⟩

-- ============================================================
-- Antes de la primera ventana prohibida, sin hipótesis
-- ============================================================

/-- Hasta la fusión central, el requisito de un nodo del mapa (si lo tiene) está en el paso anterior: el de la cima
del remitente. Los requisitos lejanos (las copias de literales) empiezan con las cláusulas. -/
theorem reqOf_step_pre {φ : Cnf} {d : NodeId} (hd : d.step ≤ midFusion φ) : ∀ r ∈ reqOf φ d, r.step = d.step - 1 := by
  intro r hr
  unfold reqOf at hr
  split at hr
  · simp at hr
  · split at hr
    · split at hr
      · simp at hr
      · rw [List.mem_singleton] at hr; rw [hr]
    · split at hr
      · simp at hr
      · omega

/-- **En la parte de variables el filtro conserva `TopTri`** (y con él los otros dos niveles): no hay ventanas
prohibidas ni requisitos lejanos. -/
theorem hTriKeep_pre {φ : Cnf} {T : Int} {line : Line} (h : LInvX φ T line) (hT : T ≤ midFusion φ) :
    HTriKeep φ line := by
  intro kv hkv d hs _ h3
  have hok := (h.on kv hkv).1
  have hd : d.step = T := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key]; omega
  exact topTri_filter_topReq (h.inv kv hkv)
    (fun r hr => by rw [reqOf_step_pre (by rw [hd]; exact hT) r hr, hd, hok.step]) h3
    (valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2)

/-- **Hasta la fusión central, los tres niveles valen sin hipótesis**: toda entrada de las líneas de la parte de
variables, y la de la fusión central, cumple `TopEdge` y `TopTri`. -/
theorem lInvX_pre (φ : Cnf) : ∀ n : Nat, (n : Int) ≤ midFusion φ →
    LInvX φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => intro _; exact lInvX_init φ
  | succ n ih =>
    intro hn
    have hn' : (n : Int) + 1 ≤ midFusion φ := by push_cast at hn; omega
    have hl := ih (by omega)
    rw [stepsM_succ]
    have := lInvX_advance (by omega) hl (hTriKeep_pre hl hn')
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

/-- **Las hipótesis solo hacen falta desde las cláusulas.** `HypsNodeKeepC`: el filtro de cada llegada conserva
`TopCT`, solo en las líneas posteriores a la fusión central. -/
def HypsNodeKeepC (φ : Cnf) : Prop :=
  ∀ n : Nat, midFusion φ < (n : Int) + 1 → HKeepP TopCT φ (stepsM .on φ n (initM .on φ))

theorem hypsNodeKeep_of_clause {φ : Cnf} (H : HypsNodeKeepC φ) : HypsNodeKeep φ := by
  intro n
  by_cases hn : midFusion φ < (n : Int) + 1
  · exact H n hn
  · have hl := lInvX_pre φ n (by omega)
    intro kv hkv d hs hc
    have hok := (hl.on kv hkv).1
    have hd : d.step = (n : Int) + 1 := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key]; omega
    exact topCT_filter_topReq (hl.inv kv hkv)
      (fun r hr => by rw [reqOf_step_pre (by rw [hd]; omega) r hr, hd, hok.step]) hc
      (valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2)

/-- **Sin hipótesis, toda cima viva está en una camarilla hasta justo antes de la primera ventana prohibida.** La
parte de variables deja los tres niveles (`lInvX_pre`); la llegada al primer literal de la primera cláusula es el
primer filtro lejano y consume uno (queda `TopEdge`); la llegada al segundo consume otro (queda `TopCT`). La línea
siguiente es la del tercer literal, donde entra la primera ventana prohibida. -/
theorem topCT_before_first_window (φ : Cnf) : ∀ n : Nat, (n : Int) ≤ midFusion φ + 2 →
    ∀ kv ∈ stepsM .on φ n (initM .on φ), TopCT kv.2 := by
  have hmid : 0 ≤ midFusion φ := by unfold midFusion; omega
  have edge1 : ∀ n : Nat, (n : Int) ≤ midFusion φ + 1 →
      LInvP TopEdge φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
    intro n hn
    by_cases h0 : (n : Int) ≤ midFusion φ
    · exact lInvP_edge_of_x (lInvX_pre φ n h0)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by
        intro e; subst e; exact h0 (by have := hmid; simp; omega))
      have hl := lInvX_pre φ m (by push_cast at hn; omega)
      rw [stepsM_succ]
      have := lInvP_advance opsP_topEdge (by omega) (lInvP_edge_of_x hl) (hKeep_edge_of_x hl)
      rw [show ((m + 1 : Nat) : Int) + 1 = (m : Int) + 1 + 1 by push_cast; omega]
      exact this
  intro n hn kv hkv
  by_cases h1 : (n : Int) ≤ midFusion φ + 1
  · exact topCT_of_topEdge ((edge1 n h1).p kv hkv)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by
      intro e; subst e; exact h1 (by have := hmid; simp; omega))
    have hl := edge1 m (by push_cast at hn; omega)
    rw [stepsM_succ] at hkv
    exact (lInvP_advance opsP_topCT (by omega) (lInvP_node_of_edge hl) (hKeep_node_of_edge hl)).p kv hkv

end GPathB

namespace MachineOn

open GPathB Driver Machine Struct

/-- **La espina con la regla activa decide la satisfacibilidad** bajo `HypsNodeKeep`: en cada llegada de la máquina,
tras el filtro de su requisito toda cima viva sigue en una camarilla. Es la hipótesis de nivel 1: un estado, un
requisito, solo nodos; sin lados y sin listas de pins. El UP y el join están demostrados. -/
theorem spineVerdictOn_iff_of_nodeKeep {φ : Cnf} (hbd : Bounded φ) (H : HypsNodeKeep φ) :
    SpineVerdictOn φ ↔ Satisfiable φ := by
  constructor
  · rintro ⟨kv, hkv, hval⟩
    obtain ⟨hlo, hls⟩ := lineOn_run_shape hbd
    have hent := hlo kv hkv
    have hsh := hls kv hkv
    have hsc : 2 ≤ stepCount φ := by unfold stepCount; omega
    have hcs0 : kv.2.current_step = stepCount φ := hent.1.step
    have hval' : (kv.2.pinOn []).isValid = true := hval
    have hcs : (kv.2.pinOn []).current_step = stepCount φ := (step_pinOn kv.2 []).trans hcs0
    obtain ⟨t, ht, hts⟩ := exists_alive_at hval' (k := stepCount φ - 1) (by omega) (by rw [hcs]; omega)
    have hl := lInvP_node_steps H (stepCount φ - 1).toNat
    obtain ⟨S, hS, _⟩ := hl.p kv hkv t ((sub_pinOn kv.2 []).alive t ht) (by rw [hts, hcs0])
    have hct : CT (kv.2.pinOn []) S := ct_pinOn hS [] (fun r hr => absurd hr List.not_mem_nil)
    have hstr : Struct φ (kv.2.pinOn []) :=
      struct_of_sub (sub_pinOn kv.2 []) ⟨hsh.2.2.1.pmp, hsh.2.2.1.gpmp, hsh.2.2.1.noforb, hsh.2.2.1.onmap,
        hsh.2.2.1.req⟩
    exact ⟨Decode.decode S, Decode.sat_of_carried hbd hstr hct.1 hcs⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hf, hct, _⟩ := run_carriesOn hbd a ha
    refine ⟨_, List.mem_of_find?_eq_some hf, ?_⟩
    exact isValid_of_carried (ct_reviewOn (ct_dirty hct true)).1

/-- **El veredicto con la hipótesis solo en las cláusulas** (`HypsNodeKeepC`): en la parte de variables el filtro
conserva los niveles sin hipótesis (`lInvX_pre`). -/
theorem spineVerdictOn_iff_of_nodeKeepC {φ : Cnf} (hbd : Bounded φ) (H : HypsNodeKeepC φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_nodeKeep hbd (hypsNodeKeep_of_clause H)

/-- **El veredicto bajo el nivel 2** (`HypsEdgeKeep`): el filtro de cada llegada conserva `TopEdge`. -/
theorem spineVerdictOn_iff_of_edgeKeep {φ : Cnf} (hbd : Bounded φ) (H : HypsEdgeKeep φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_nodeKeep hbd (hypsNodeKeep_of_edgeKeep H)

/-- **El veredicto bajo el nivel 3** (`HypsTriKeep`): el filtro de cada llegada conserva «todo triángulo sin prohibir
con una cima está en una camarilla». Los niveles 1 y 2 salen de él. -/
theorem spineVerdictOn_iff_of_triKeep {φ : Cnf} (hbd : Bounded φ) (H : HypsTriKeep φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_edgeKeep hbd (hypsEdgeKeep_of_triKeep H)

theorem spineVerdictOn_iff_of_triFlt {φ : Cnf} (hbd : Bounded φ) (H : HypsTriFlt φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_triKeep hbd (hypsTriKeep_of_flt H)

/-- **El veredicto bajo `PinTetra`**: la hipótesis en su forma de cuatro nodos. En cada llegada de la máquina, un
tetraedro del remitente fijado en el requisito, con cima, un nodo en el paso del requisito y las cuatro caras sin
prohibir, deja una camarilla de la entrada por la cara de la cima que cumple el requisito. -/
theorem spineVerdictOn_iff_of_pinTetra {φ : Cnf} (hbd : Bounded φ) (H : HypsPinTetra φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_triKeep hbd (hypsTriKeep_of_pinTetra H)

end MachineOn

end AbsSatBingo.Model
