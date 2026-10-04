-- lean/improves_bingo/AbsSatBingo/Model/StarLine.lean
import AbsSatBingo.Model.StarUp
import AbsSatBingo.Model.StarTrio

/-!
# `StarNodes` por inducción a lo largo de la línea

El invariante que se arrastra (**`StarInv`**) es `StarNodes` con la estrella relacionada con la cima en la propia
estructura y solo la cima en su paso (lo que pide `secStruct_addNode_star`):

> para toda estructura cerrada `(V, R)`, toda cima `t ∈ V` y todo `z ∈ V` con `R z t`, hay una estructura cerrada
> `(W, R')` con `z, t ∈ W ⊆ V`, todo `W` relacionado con `t` por `R'`, y en el paso de `t` solo `t`.

* **`starInv_single`** (base): un estado con un solo vivo.
* **`starInv_up`** (el UP): se baja `V` por el review, la fila (`secStruct_addNode_down`) y el filtro; el testigo de
  `z–t` en el paso anterior es un padre `p` de `t` (`TopsApart`); la hipótesis de inducción en `p` da `W₀`, que pasa
  el filtro (sus nodos concuerdan con los requisitos) y sube con `t` (`secStruct_addNode_star`) y el review.
* **`starInv_join`** (el join): bajo **`StarJoinDown`** — la estrella de una cima de la unión tiene, para cada nodo,
  una estructura cerrada de un solo lado que lo contiene con la cima — se aplica la hipótesis del lado y se levanta.

Medido (`julia/improves_bingo/test_3sat/probe_join_down.jl`): restringir el lado de la cima a su estrella y revisar
conserva todos los nodos de la estrella (0 fallos), así que la estructura del lado existe y relaciona `z` con `t`.

Veredicto: **`readerVerdict_iff_of_starJoinDown`**, bajo `StarJoinDown` y `SideEdgesAt` en los joins.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Machine (Below)

/-- **El invariante de la estrella.** -/
def StarInv (u : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R →
    ∀ t, V t → t.id.step = u.current_step - 1 → ∀ z, V z → R z t →
    ∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧ W z ∧ W t ∧
      (∀ y, W y → V y) ∧ (∀ y, W y → R' y t) ∧ (∀ y, W y → y.id.step = u.current_step - 1 → y = t)

theorem starNodes_of_starInv {u : GPathB} (h : StarInv u) : StarNodes u := by
  intro P V R hst ha t htV hts z hzV hzt
  obtain ⟨W, R', hW, hzW, _, hsub, hrt, _⟩ := h V R hst t htV hts z hzV hzt
  refine ⟨W, R', hW, fun b hb y hy hys => ha b hb (hsub y hy) hys, hzW, fun y hy => ⟨hsub y hy, ?_⟩⟩
  exact Or.inr (hW.adj (hW.symm (hrt y hy)))

/-- **Base**: con un solo vivo, la estructura misma sirve. -/
theorem starInv_single {u : GPathB} (h : ∀ q ∈ u.alive, ∀ q' ∈ u.alive, q = q') : StarInv u := by
  intro V R hst t htV _ z hzV _
  have heq : ∀ y, V y → y = t := fun y hy => h _ (hst.alive hy) _ (hst.alive htV)
  refine ⟨V, R, hst, hzV, htV, fun _ hy => hy, fun y hy => ?_, fun y hy _ => heq y hy⟩
  rw [heq y hy]; exact hst.refl htV

theorem starInv_initSeed : StarInv (initSeed (⟨0, 0⟩ : NodeId) "") := by
  apply starInv_single
  let d : NodeId := ⟨0, 0⟩
  let root : PathNodeId := { id := d, parent_id := none, gparent_id := none }
  let a := GPathB.empty.addNode d "" (fun _ => false)
  have hal : a.alive = [root] := rfl
  have hone : ∀ q ∈ (initSeed d "").alive, q = root := by
    intro q hq
    unfold initSeed up at hq
    split at hq
    · have := (shrinks_review a).1.alive q hq
      rw [hal, List.mem_singleton] at this
      exact this
    · cases hq
  intro q hq q' hq'
  rw [hone q hq, hone q' hq']

variable {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- Un vivo viejo del paso de arriba que posee un nodo nuevo es uno de sus padres (las cimas no se poseen). -/
theorem rowParent_of_adj {f : GPathB} (hdocs : AliveDocs f) (hb : Below f) (hea : EdgesAlive f)
    (hta : TopsApart f) (hd : d.step = f.current_step) {t p : PathNodeId} (ht : t ∈ f.newRowIds d forb)
    (hps : p.id.step = f.current_step - 1) (h : (f.addNode d title forb).Adj t p) : p ∈ f.rowParents d t := by
  have hts : t.id.step = f.current_step := newRow_step hd ht
  rw [adj_iff] at h
  rcases h with ⟨rfl, _⟩ | ⟨e, he, hj⟩
  · omega
  · rcases List.mem_append.mp he with h | h
    · -- una arista vieja toca solo vivos viejos
      have hold : f.Adj t p := (adj_iff f t p).mpr (Or.inr ⟨e, h, hj⟩)
      have := alive_below hdocs hb (hea t p hold).1
      omega
    · obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp h
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he'
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 : pid = t := h1
        have e2 : w = p := h2
        subst e1; subst e2
        obtain ⟨_, hany⟩ := Bool.and_eq_true_iff.mp (List.mem_filter.mp hw).2
        obtain ⟨q, hq, hqw⟩ := List.any_eq_true.mp hany
        obtain ⟨_, _, _, hqs⟩ := step_of_newParents (rowParents_sub hq)
        have := hta q w hqs hps hqw
        subst this
        exact hq
      · have e1 : pid = p := h1
        subst e1
        have := newRow_step hd hpid
        omega

/-- **El UP conserva `StarInv`.** -/
theorem starInv_up {g₀ : GPathB} {reqs : List NodeId} (hI : StarInv g₀) (hnd₀ : NodupIds g₀) (hd₀ : AliveDocs g₀)
    (hv : (g₀.filterAll reqs).isValid = true) (hfd : AliveDocs (g₀.filterAll reqs))
    (hfb : Below (g₀.filterAll reqs)) (hls : LinksStep (g₀.filterAll reqs)) (hea : EdgesAlive (g₀.filterAll reqs))
    (hnd : NodupIds (g₀.filterAll reqs)) (hta : TopsApart (g₀.filterAll reqs))
    (hd : d.step = (g₀.filterAll reqs).current_step) (hpos : 0 < (g₀.filterAll reqs).current_step) :
    StarInv (((g₀.filterAll reqs).addNode d title forb).review) := by
  have hsf := (shrinks_filterAll g₀ reqs).1
  generalize hfe : g₀.filterAll reqs = f at *
  have hcs : (f.addNode d title forb).review.current_step = f.current_step + 1 :=
    (shrinks_review (f.addNode d title forb)).1.step
  have hcs₀ : f.current_step = g₀.current_step := hsf.step
  intro V R hst t htV hts z hzV hzt
  rw [hcs] at hts
  have hst₁ : SecStruct (f.addNode d title forb) V R :=
    secStruct_of_sub (shrinks_review _).1 (nodupIds_addNode hnd hfb hd) hst
  have hst₂ := secStruct_addNode_down hfd hfb hls hd hst₁
  have hst₃ : SecStruct g₀ _ _ := secStruct_of_sub hsf hnd₀ hst₂
  -- t es de la fila nueva
  have htnew : t ∈ f.newRowIds d forb := by
    rcases alive_addNode_cases (title := title) hfd hfb hd (hst₁.alive htV) with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  -- el testigo de z–t en el paso de arriba: un padre p de t
  obtain ⟨p, hps, hzp, htp⟩ := hst.pair hzt (f.current_step - 1) (by omega) (by rw [hcs]; omega)
  have hpt : p ∈ f.rowParents d t :=
    rowParent_of_adj hfd hfb hea hta hd htnew hps (hst₁.adj htp)
  have hVp : V p ∧ p.id.step < f.current_step := ⟨(hst.dom hzp).2, by omega⟩
  -- el nodo z₀ al que se aplica la hipótesis: z, o p si z es la cima
  have hold : ∀ {y}, V y → R y t → y ≠ t → y.id.step < f.current_step := by
    intro y hy hyt hne
    rcases alive_addNode_cases (title := title) hfd hfb hd (hst₁.alive hy) with ⟨_, h⟩ | ⟨hn, h⟩
    · exact h
    · exact absurd (adj_addNode_new hfd hfb hea h (by omega) (hst₁.adj hyt)) hne
  obtain ⟨z₀, hz₀, hz₀p, hzz⟩ : ∃ z₀, (V z₀ ∧ z₀.id.step < f.current_step) ∧
      (R z₀ p ∧ z₀.id.step < f.current_step ∧ p.id.step < f.current_step) ∧ (z = t ∨ z = z₀) := by
    by_cases hz : z = t
    · exact ⟨p, hVp, ⟨hst.refl hVp.1, hVp.2, hVp.2⟩, Or.inl hz⟩
    · have hzs := hold hzV hzt hz
      exact ⟨z, ⟨hzV, hzs⟩, ⟨hzp, hzs, hVp.2⟩, Or.inr rfl⟩
  obtain ⟨W₀, R₀, hW₀, hz₀W, hpW, hsub, hrp, htop⟩ :=
    hI _ _ hst₃ p hVp (by omega) z₀ hz₀ hz₀p
  -- W₀ pasa el filtro: sus nodos concuerdan con los requisitos
  have hWf : SecStruct f W₀ R₀ := by
    rw [← hfe]
    refine secStruct_filterAll_list hW₀ reqs (fun b hb y hy hys => ?_)
    have hyf : y ∈ f.alive := hst₂.alive (hsub y hy)
    rw [← hfe] at hyf
    exact pinned_filterAll_list hd₀ reqs (hfe ▸ hv) b hb y hyf hys
  have hup := secStruct_addNode_star (title := title) hfd hfb hd hWf htnew hpt hpW hrp
    (fun y hy hys => htop y hy (by omega))
  refine ⟨_, _, secStruct_review hup, ?_, Or.inr rfl, ?_, ?_, ?_⟩
  · rcases hzz with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl hz₀W
  · rintro y (hy | rfl)
    · exact (hsub y hy).1
    · exact htV
  · rintro y (hy | rfl)
    · exact Or.inr (Or.inr ⟨rfl, hy⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)
  · rintro y (hy | rfl) hys
    · have := (hsub y hy).2; rw [hcs] at hys; omega
    · rfl

/-- **La bajada por el join**: para una cima de la unión y un nodo de su estrella, hay una estructura cerrada de
un solo lado, dentro de `V`, que los contiene y los relaciona. -/
def StarJoinDown (e g : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct (join e g) V R →
    ∀ t, V t → t.id.step = (join e g).current_step - 1 → ∀ z, V z → R z t →
    ∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
      (SecStruct e V' R' ∨ SecStruct g V' R') ∧ V' z ∧ V' t ∧ R' z t ∧ ∀ y, V' y → V y

/-- **El join conserva `StarInv`**, bajo `StarJoinDown`. -/
theorem starInv_join {e g : GPathB} (hcs : e.current_step = g.current_step) (he : StarInv e) (hg : StarInv g)
    (hjd : StarJoinDown e g) : StarInv (join e g) := by
  have hje : (join e g).current_step = e.current_step := rfl
  intro V R hst t htV hts z hzV hzt
  obtain ⟨V', R', hside, hzV', htV', hzt', hsub⟩ := hjd V R hst t htV hts z hzV hzt
  rcases hside with hs | hs
  · obtain ⟨W, R'', hW, h1, h2, h3, h4, h5⟩ := he V' R' hs t htV' (by rw [hts, hje]) z hzV' hzt'
    exact ⟨W, R'', secStruct_join_left hW, h1, h2, fun y hy => hsub y (h3 y hy), h4,
      fun y hy hys => h5 y hy (by rw [hys, hje])⟩
  · obtain ⟨W, R'', hW, h1, h2, h3, h4, h5⟩ := hg V' R' hs t htV' (by rw [hts, hje, hcs]) z hzV' hzt'
    exact ⟨W, R'', secStruct_join_right hcs hW, h1, h2, fun y hy => hsub y (h3 y hy), h4,
      fun y hy hys => h5 y hy (by rw [hys, hje, hcs])⟩

theorem starInv_doJoin {e g : GPathB} (he : StarInv e) (hg : StarInv g)
    (hjd : e.current_step = g.current_step → StarJoinDown e g) : StarInv (doJoin e g) := by
  unfold doJoin
  split
  · rename_i hok
    unfold okJoin at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    exact starInv_join hok.1.1.1 he hg (hjd hok.1.1.1)
  · exact he

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- El invariante de la línea con la estrella. -/
def SInvS (g : GPathB) : Prop := SInvT g ∧ StarInv g

/-- **Las hipótesis**: `StarJoinDown` y `SideEdgesAt` en cada join. -/
structure HypsStarJD (φ : Cnf) : Prop where
  down : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g → StarJoinDown e g
  side : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g → SideEdgesAt e g (T - 2)

theorem upProv_S (φ : Cnf) : UpProv φ SInvS := by
  intro T key g d hg hk hT hd hv
  refine ⟨upProv_T φ T key g d hg hk.1 hT hd hv, ?_⟩
  have hs := shrinks_filterAll g (reqOf φ d)
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := (step_of_shrinks hs).trans hg.step
  have hdstep : d.step = (g.filterAll (reqOf φ d)).current_step := by
    rw [hstep, sonsOfMap_step φ key d hd, hg.key]; omega
  have hf := sInv_filterAll hk.1.1.2 hg.docs (reqOf φ d)
  have hfd : AliveDocs (g.filterAll (reqOf φ d)) := aliveDocs_filterAll hg.docs _
  have hfb : Below (g.filterAll (reqOf φ d)) := below_of_shrinks hs hg.below
  have hta : TopsApart (g.filterAll (reqOf φ d)) := revPrims_filterAll revPrims_topsApart _ _ hk.1.2.1
  unfold upFiltering up at hv ⊢
  split
  · rename_i hvf
    exact starInv_up hk.2 hk.1.1.2.2.1 hg.docs hvf hfd hfb hf.2.2.2.1 hf.2.2.1 hf.2.1 hta hdstep (by omega)
  · rename_i hvf
    rw [if_neg hvf] at hv
    exact absurd hv hvf

theorem joinProv_S {φ : Cnf} (H : HypsStarJD φ) {U : Int} (hU : 2 ≤ U) : JoinProv SInvS U := by
  intro key s e g A he hg hke hkg hoe hog hsA hAk hsk
  have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
  have hsi := starInv_join hcs hke.2 hkg.2 (H.down U key e g hU he hg hke hkg)
  exact ⟨joinStep_T hU he hg hke.1 hkg.1 hoe hog hsA hAk hsk (starNodes_of_starInv hsi)
      (H.side U key e g hU he hg hke hkg),
    starInv_doJoin hke.2 hkg.2 (fun _ => H.down U key e g hU he hg hke hkg)⟩

theorem sInvS_initSeed : SInvS (initSeed (⟨0, 0⟩ : NodeId) "") := ⟨sInvT_initSeed, starInv_initSeed⟩

/-- **El veredicto del lector es la satisfacibilidad bajo `StarJoinDown` y `SideEdgesAt` en los joins.** -/
theorem readerVerdict_iff_of_starJoinDown {φ : Cnf} (hbd : Bounded φ) (H : HypsStarJD φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_prov (upProv_S φ) (fun _ hU => joinProv_S H hU) sInvS_initSeed kv hkv
    ⟨h.1, h.2.1.1.2⟩)

end SecLine

end AbsSatBingo.Model
