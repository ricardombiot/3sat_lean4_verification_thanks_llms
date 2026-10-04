-- lean/improves_bingo/AbsSatBingo/Model/ChainPin.lean
import AbsSatBingo.Model.StarUnion

/-!
# Fijar y revisar: la bajada del lector dentro de una estructura cerrada (`ChainInv`)

Una estructura cerrada contiene, comprimidas, muchas soluciones: bajar por padres mirando solo las parejas se atasca
(`probe_greedy_descent.jl`: callejones en los núcleos). Fijando un nodo más en cada paso —como el lector, que fija y
revisa— no se atasca nunca (0 candidatos malos en 23 230 parejas).

> **`ChainInv u`**: en una estructura cerrada fijada (un solo nodo por paso) desde un paso `j ≤` la cima, cualquier
> nodo `x` se puede fijar también: hay una estructura cerrada dentro, con `x`, fijada en el paso de `x`.

* **`pinned_rel`**: en una estructura fijada desde `j`, todo nodo está relacionado con los fijados.
* **`chainInv_up`** (demostrado): se baja, se fija el padre de la cima con `StarInv`, se aplica la hipótesis de
  inducción y se sube con `secStruct_addNode_star`.
* **`chainInv_join`**: con `StarJoinDown`, la estructura del lado hereda las fijaciones.
* **`topClique_of_chain`**: `ChainInv` + `StarInv` ⟹ `UnionTopClique`: desde la cima, fijando `z` y después un paso
  cada vez, se llega a una estructura fijada en todos los pasos, que es una camarilla (`carried_of_pinned`).

Con esto, en el join: **`StarJoinDown` ⟺ `UnionTopClique`** de la unión (`starJoinDown_iff_unionClique`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Machine (Below)

/-- Un solo nodo por paso desde `j`. -/
def PinnedFrom (W : PathNodeId → Prop) (j : Int) : Prop :=
  ∀ y w, W y → W w → j ≤ y.id.step → y.id.step = w.id.step → y = w

/-- Solo `x` en el paso de `x`. -/
def PinnedAt (W : PathNodeId → Prop) (x : PathNodeId) : Prop := ∀ y, W y → y.id.step = x.id.step → y = x

/-- **Fijar un nodo más**, en una estructura fijada desde un paso de la cima o inferior. -/
def ChainInv (u : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R →
    ∀ j, j ≤ u.current_step - 1 → PinnedFrom V j → ∀ x, V x →
    ∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧ (∀ y, W y → V y) ∧
      W x ∧ PinnedAt W x

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- Un vecino en cada paso. -/
theorem exists_at {u : GPathB} (hst : SecStruct u V R) {y : PathNodeId} (hy : V y) (l : Int) (h0 : 0 ≤ l)
    (h1 : l < u.current_step) : ∃ r, V r ∧ r.id.step = l ∧ R y r := by
  obtain ⟨r, hrl, hyr, _⟩ := hst.pair (hst.refl hy) l h0 h1
  exact ⟨r, (hst.dom hyr).2, hrl, hyr⟩

/-- **En una estructura fijada, todo nodo está relacionado con los fijados.** -/
theorem pinned_rel {u : GPathB} (hst : SecStruct u V R) {j : Int} (hp : PinnedFrom V j) {y w : PathNodeId}
    (hy : V y) (hw : V w) (hj : j ≤ w.id.step) (h0 : 0 ≤ w.id.step) (h1 : w.id.step < u.current_step) :
    R y w := by
  obtain ⟨r, hr, hrs, hyr⟩ := exists_at hst hy _ h0 h1
  have : r = w := hp r w hr hw (by rw [hrs]; exact hj) hrs
  subst this; exact hyr

theorem pinnedFrom_mono {W V : PathNodeId → Prop} {j : Int} (hsub : ∀ y, W y → V y) (h : PinnedFrom V j) :
    PinnedFrom W j := fun y w hy hw => h y w (hsub y hy) (hsub w hw)

/-- Base: con un solo vivo, la estructura misma. -/
theorem chainInv_single {u : GPathB} (h : ∀ q ∈ u.alive, ∀ q' ∈ u.alive, q = q') : ChainInv u := by
  intro V R hst _ _ _ x hx
  exact ⟨V, R, hst, fun _ hy => hy, hx, fun y hy _ => h _ (hst.alive hy) _ (hst.alive hx)⟩

theorem chainInv_initSeed : ChainInv (initSeed (⟨0, 0⟩ : NodeId) "") := by
  apply chainInv_single
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

/-- **El UP conserva `ChainInv`** (con `StarInv` en el estado anterior). -/
theorem chainInv_up {g₀ : GPathB} {reqs : List NodeId} (hC : ChainInv g₀) (hS : StarInv g₀) (hnd₀ : NodupIds g₀)
    (hd₀ : AliveDocs g₀)
    (hv : (g₀.filterAll reqs).isValid = true) (hfd : AliveDocs (g₀.filterAll reqs))
    (hfb : Below (g₀.filterAll reqs)) (hls : LinksStep (g₀.filterAll reqs)) (hea : EdgesAlive (g₀.filterAll reqs))
    (hnd : NodupIds (g₀.filterAll reqs)) (hta : TopsApart (g₀.filterAll reqs))
    (hd : d.step = (g₀.filterAll reqs).current_step) (hpos : 0 < (g₀.filterAll reqs).current_step) :
    ChainInv (((g₀.filterAll reqs).addNode d title forb).review) := by
  have hsf := (shrinks_filterAll g₀ reqs).1
  generalize hfe : g₀.filterAll reqs = f at *
  have hcs : (f.addNode d title forb).review.current_step = f.current_step + 1 :=
    (shrinks_review (f.addNode d title forb)).1.step
  have hcs₀ : f.current_step = g₀.current_step := hsf.step
  intro V R hst j hj hpin x hx
  rw [hcs] at hj
  by_cases hxj : j ≤ x.id.step
  · exact ⟨V, R, hst, fun _ h => h, hx, fun y hy hys => hpin y x hy hx (by omega) hys⟩
  have hst₁ : SecStruct (f.addNode d title forb) V R :=
    secStruct_of_sub (shrinks_review _).1 (nodupIds_addNode hnd hfb hd) hst
  have hst₂ := secStruct_addNode_down hfd hfb hls hd hst₁
  have hst₃ : SecStruct g₀ _ _ := secStruct_of_sub hsf hnd₀ hst₂
  -- la cima fijada t y el padre p
  obtain ⟨t, htV, hts, hxt⟩ := exists_at hst hx f.current_step (by omega) (by rw [hcs]; omega)
  have htnew : t ∈ f.newRowIds d forb := by
    rcases alive_addNode_cases (title := title) hfd hfb hd (hst₁.alive htV) with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  obtain ⟨p, hps, hxp, htp⟩ := hst.pair hxt (f.current_step - 1) (by omega) (by rw [hcs]; omega)
  have hpt : p ∈ f.rowParents d t := rowParent_of_adj hfd hfb hea hta hd htnew hps (hst₁.adj htp)
  have hVp : V p ∧ p.id.step < f.current_step := ⟨(hst.dom hxp).2, by omega⟩
  have hxo : x.id.step < f.current_step := by omega
  -- la estrella de p en el estado anterior, fijada en p
  obtain ⟨W₀, R₀, hW₀, hxW₀, hpW₀, hsub₀, _, htop₀⟩ :=
    hS _ _ hst₃ p hVp (by omega) x ⟨hx, hxo⟩ ⟨hxp, hxo, hVp.2⟩
  have hpin₀ : PinnedFrom W₀ (min j (f.current_step - 1)) := by
    intro y w hy hw hjy hyw
    have hyo := (hsub₀ y hy).2
    by_cases hyt : y.id.step = f.current_step - 1
    · rw [htop₀ y hy (by omega), htop₀ w hw (by omega)]
    · exact hpin y w (hsub₀ y hy).1 (hsub₀ w hw).1 (by omega) hyw
  obtain ⟨W₁, R₁, hW₁, hsub₁, hxW₁, hpx₁⟩ := hC _ _ hW₀ _ (by omega) hpin₀ x hxW₀
  -- W₁ pasa el filtro
  have hWf : SecStruct f W₁ R₁ := by
    rw [← hfe]
    refine secStruct_filterAll_list hW₁ reqs (fun b hb y hy hys => ?_)
    have hyf : y ∈ f.alive := hst₂.alive (hsub₀ y (hsub₁ y hy))
    rw [← hfe] at hyf
    exact pinned_filterAll_list hd₀ reqs (hfe ▸ hv) b hb y hyf hys
  -- en el paso de p, W₁ solo tiene a p
  have htop₁ : ∀ y, W₁ y → y.id.step = f.current_step - 1 → y = p :=
    fun y hy hys => htop₀ y (hsub₁ y hy) (by omega)
  obtain ⟨r, hrW, hrs, _⟩ := exists_at hW₁ hxW₁ (f.current_step - 1) (by omega) (by omega)
  have hpW₁ : W₁ p := by rw [← htop₁ r hrW hrs]; exact hrW
  have hstar₁ : ∀ y, W₁ y → R₁ y p := by
    intro y hy
    obtain ⟨r', hr'W, hr's, hyr'⟩ := exists_at hW₁ hy (f.current_step - 1) (by omega) (by omega)
    rw [← htop₁ r' hr'W hr's]; exact hyr'
  have hup := secStruct_addNode_star (title := title) hfd hfb hd hWf htnew hpt hpW₁ hstar₁ htop₁
  refine ⟨_, _, secStruct_review hup, ?_, Or.inl hxW₁, ?_⟩
  · rintro y (hy | rfl)
    · exact (hsub₀ y (hsub₁ y hy)).1
    · exact htV
  · rintro y (hy | rfl) hys
    · exact hpx₁ y hy hys
    · omega

/-- **El join conserva `ChainInv`**, con `StarJoinDown`. -/
theorem chainInv_join {e g : GPathB} (hcs : e.current_step = g.current_step) (hpos : 1 ≤ e.current_step)
    (he : ChainInv e) (hg : ChainInv g) (hjd : StarJoinDown e g) : ChainInv (join e g) := by
  have hje : (join e g).current_step = e.current_step := rfl
  intro V R hst j hj hpin x hx
  by_cases hxj : j ≤ x.id.step
  · exact ⟨V, R, hst, fun _ h => h, hx, fun y hy hys => hpin y x hy hx (by omega) hys⟩
  obtain ⟨t, htV, hts, hxt⟩ := exists_at hst hx (e.current_step - 1) (by omega) (by rw [hje]; omega)
  obtain ⟨V', R', hside, hxV', _, _, hsub⟩ := hjd V R hst t htV (by rw [hts, hje]) x hx hxt
  have hpin' := pinnedFrom_mono hsub hpin
  rcases hside with h | h
  · obtain ⟨W, R'', hW, hWs, hxW, hpx⟩ := he V' R' h j (by rw [← hje]; exact hj) hpin' x hxV'
    exact ⟨W, R'', secStruct_join_left hW, fun y hy => hsub y (hWs y hy), hxW, hpx⟩
  · obtain ⟨W, R'', hW, hWs, hxW, hpx⟩ := hg V' R' h j (by rw [← hcs, ← hje]; exact hj) hpin' x hxV'
    exact ⟨W, R'', secStruct_join_right hcs hW, fun y hy => hsub y (hWs y hy), hxW, hpx⟩

theorem chainInv_doJoin_ok {e g : GPathB} (hpos : 1 ≤ e.current_step) (he : ChainInv e) (hg : ChainInv g)
    (hjd : okJoin e g = true → StarJoinDown e g) : ChainInv (doJoin e g) := by
  unfold doJoin
  split
  · rename_i hok
    have hok' := hok
    unfold okJoin at hok'
    simp only [Bool.and_eq_true, beq_iff_eq] at hok'
    exact chainInv_join hok'.1.1.1 hpos he hg (hjd hok)
  · exact he

-- ============================================================
-- Una estructura fijada en todos los pasos es una camarilla
-- ============================================================

/-- Los nodos vivos están en los pasos `0 … c-1`. -/
theorem step_range {u : GPathB} (hdocs : AliveDocs u) (hb : Below u) (hz : AboveZero u) {y : PathNodeId}
    (hy : y ∈ u.alive) : 0 ≤ y.id.step ∧ y.id.step < u.current_step := by
  obtain ⟨n, hn, rfl⟩ := hdocs y hy
  exact ⟨hz n hn, hb n hn⟩

/-- **Una estructura cerrada fijada en todos los pasos es una camarilla**: el nodo de cada paso. -/
theorem carried_of_pinned {u : GPathB} (hdocs : AliveDocs u) (hb : Below u) (hz : AboveZero u)
    (hls : LinksStep u) {W : PathNodeId → Prop} {R' : PathNodeId → PathNodeId → Prop} (hW : SecStruct u W R')
    (hpin : PinnedFrom W 0) {z : PathNodeId} (hzW : W z) :
    ∃ C : Int → PathNodeId, Carried u C ∧ (∀ k, 0 ≤ k → k < u.current_step → W (C k)) ∧
      ∀ y, W y → y = C y.id.step := by
  have hex : ∀ k, 0 ≤ k → k < u.current_step → ∃ r, W r ∧ r.id.step = k ∧ R' z r :=
    fun k h0 h1 => exists_at hW hzW k h0 h1
  classical
  let C : Int → PathNodeId := fun k =>
    if h : 0 ≤ k ∧ k < u.current_step then Classical.choose (hex k h.1 h.2) else z
  have hC : ∀ k (h0 : 0 ≤ k) (h1 : k < u.current_step), W (C k) ∧ (C k).id.step = k := by
    intro k h0 h1
    have := Classical.choose_spec (hex k h0 h1)
    simp only [C, dif_pos (And.intro h0 h1)]
    exact ⟨this.1, this.2.1⟩
  have hrange : ∀ {y}, W y → 0 ≤ y.id.step ∧ y.id.step < u.current_step :=
    fun hy => step_range hdocs hb hz (hW.alive hy)
  have huniq : ∀ y, W y → y = C y.id.step := by
    intro y hy
    obtain ⟨h0, h1⟩ := hrange hy
    have := hC _ h0 h1
    exact hpin y _ hy this.1 h0 this.2.symm
  have hrel : ∀ k l, 0 ≤ k → k < u.current_step → 0 ≤ l → l < u.current_step → R' (C k) (C l) := by
    intro k l h0 h1 h2 h3
    exact pinned_rel hW hpin (hC k h0 h1).1 (hC l h2 h3).1 (by rw [(hC l h2 h3).2]; exact h2)
      (by rw [(hC l h2 h3).2]; exact h2) (by rw [(hC l h2 h3).2]; exact h3)
  refine ⟨C, ⟨fun k h0 h1 => (hC k h0 h1).2, fun k h0 h1 => hW.alive (hC k h0 h1).1,
    fun k l h0 h1 h2 h3 => hW.adj (hrel k l h0 h1 h2 h3), ?_, ?_⟩, fun k h0 h1 => (hC k h0 h1).1, huniq⟩
  · -- la raíz: un padre estaría en el paso -1
    intro hpos
    cases hpar : (C 0).parent_id with
    | none => rfl
    | some _ =>
      exfalso
      obtain ⟨n, hn, hp, _⟩ := hW.node (hC 0 (Int.le_refl 0) hpos).1
      obtain ⟨p, hpm, hCp⟩ := hp (by rw [hpar]; rfl)
      have h1 := (hls n (node?_mem hn)).1 p hpm
      rw [node?_id hn, (hC 0 (Int.le_refl 0) hpos).2] at h1
      have := (hrange (hW.dom hCp).2).1
      omega
  · intro k h0 h1
    obtain ⟨hCk, hks⟩ := hC k h0 h1
    obtain ⟨n, hn, _, _⟩ := hW.node hCk
    refine ⟨n, hn, fun hk => ?_, fun hk => ?_⟩
    · -- el padre: apoyo de la pareja con el nodo del paso 0
      have hne : C k ≠ C 0 := fun he => by
        have := (hC 0 (Int.le_refl 0) (by omega)).2; rw [← he, hks] at this; omega
      obtain ⟨p, hpm, hCp, _⟩ := hW.par (hrel k 0 h0 h1 (Int.le_refl 0) (by omega)) hne hn (by omega)
      have hps := (hls n (node?_mem hn)).1 p hpm
      rw [node?_id hn, hks] at hps
      have hpe := huniq p (hW.dom hCp).2
      rw [show p.id.step = k - 1 by omega] at hpe
      rw [← hpe]; exact hpm
    · -- el hijo: apoyo de la pareja con el nodo de la cima
      have hne : C k ≠ C (u.current_step - 1) := fun he => by
        have := (hC (u.current_step - 1) (by omega) (by omega)).2; rw [← he, hks] at this; omega
      obtain ⟨s, hsm, hCs, _⟩ := hW.son (hrel k (u.current_step - 1) h0 h1 (by omega) (by omega)) hne hn
        (by rw [hks]; exact hk)
      have hss := (hls n (node?_mem hn)).2 s hsm
      rw [node?_id hn, hks] at hss
      have hse := huniq s (hW.dom hCs).2
      rw [hss] at hse
      rw [← hse]; exact hsm

/-- **`ChainInv` + `StarInv` ⟹ `UnionTopClique`**: fijar `z`, y después un paso cada vez hacia abajo. -/
theorem topClique_of_chain {u : GPathB} (hC : ChainInv u) (hS : StarInv u) (hdocs : AliveDocs u) (hb : Below u)
    (hz : AboveZero u) (hls : LinksStep u) : UnionTopClique u := by
  intro V R hst t htV hts z hzV hzt
  have hrange : ∀ {W : PathNodeId → Prop} {R' : PathNodeId → PathNodeId → Prop}, SecStruct u W R' → ∀ {y}, W y →
      0 ≤ y.id.step ∧ y.id.step < u.current_step := fun hW _ hy => step_range hdocs hb hz (hW.alive hy)
  obtain ⟨W₀, R₀, hW₀, hzW₀, htW₀, hsub₀, _, htop₀⟩ := hS V R hst t htV hts z hzV hzt
  have hpin₀ : PinnedFrom W₀ (u.current_step - 1) := by
    intro y w hy hw hjy hyw
    have := (hrange hW₀ hy).2
    rw [htop₀ y hy (by omega), htop₀ w hw (by omega)]
  obtain ⟨W₁, R₁, hW₁, hsub₁, hzW₁, hpz₁⟩ := hC W₀ R₀ hW₀ _ (Int.le_refl _) hpin₀ z hzW₀
  -- bajar: fijado desde c - 1 - m
  have hdesc : ∀ m : Nat, (m : Int) ≤ u.current_step - 1 →
      ∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧ (∀ y, W y → W₀ y) ∧
        W z ∧ PinnedAt W z ∧ PinnedFrom W (u.current_step - 1 - m) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨W₁, R₁, hW₁, hsub₁, hzW₁, hpz₁, by simpa using pinnedFrom_mono hsub₁ hpin₀⟩
    | succ m ih =>
      intro hm
      obtain ⟨W, R', hW, hWs, hzW, hpz, hpin⟩ := ih (by omega)
      obtain ⟨x, hxW, hxs, _⟩ := exists_at hW hzW (u.current_step - 1 - m - 1) (by omega) (by omega)
      obtain ⟨W', R'', hW', hW's, hxW', hpx⟩ := hC W R' hW _ (by omega) hpin x hxW
      obtain ⟨r, hrW', hrs, _⟩ := exists_at hW' hxW' z.id.step (hrange hW₀ hzW₀).1 (hrange hW₀ hzW₀).2
      have hrz : r = z := hpz r (hW's r hrW') hrs
      refine ⟨W', R'', hW', fun y hy => hWs y (hW's y hy), hrz ▸ hrW', fun y hy hys => hpz y (hW's y hy) hys, ?_⟩
      intro y w hy hw hjy hyw
      by_cases hyx : y.id.step = x.id.step
      · rw [hpx y hy hyx, hpx w hw (by omega)]
      · exact hpin y w (hW's y hy) (hW's w hw) (by push_cast at hjy; omega) hyw
  have hcpos : 0 < u.current_step := by have := (hrange hW₀ hzW₀); omega
  obtain ⟨W, R', hW, hWs, hzW, _, hpin⟩ := hdesc (u.current_step - 1).toNat (by omega)
  rw [show u.current_step - 1 - ((u.current_step - 1).toNat : Int) = 0 by omega] at hpin
  obtain ⟨C, hCc, hCW, huniq⟩ := carried_of_pinned hdocs hb hz hls hW hpin hzW
  refine ⟨C, hCc, ?_, ⟨z.id.step, (hrange hW hzW).1, (hrange hW hzW).2, (huniq z hzW).symm⟩,
    fun k h0 h1 => (hsub₀ _ (hWs _ (hCW k h0 h1)))⟩
  have hCt := hCW (u.current_step - 1) (by omega) (by omega)
  exact htop₀ _ (hWs _ hCt) (hCc.step _ (by omega) (by omega))

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- El invariante de la línea con la bajada del lector. -/
def SInvC (g : GPathB) : Prop := SInvS g ∧ ChainInv g

theorem upProv_C (φ : Cnf) : UpProv φ SInvC := by
  intro T key g d hg hk hT hd hv
  refine ⟨upProv_S φ T key g d hg hk.1 hT hd hv, ?_⟩
  have hs := shrinks_filterAll g (reqOf φ d)
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := (step_of_shrinks hs).trans hg.step
  have hdstep : d.step = (g.filterAll (reqOf φ d)).current_step := by
    rw [hstep, sonsOfMap_step φ key d hd, hg.key]; omega
  have hf := sInv_filterAll hk.1.1.1.2 hg.docs (reqOf φ d)
  have hfd : AliveDocs (g.filterAll (reqOf φ d)) := aliveDocs_filterAll hg.docs _
  have hfb : Below (g.filterAll (reqOf φ d)) := below_of_shrinks hs hg.below
  have hta : TopsApart (g.filterAll (reqOf φ d)) := revPrims_filterAll revPrims_topsApart _ _ hk.1.1.2.1
  unfold upFiltering up at hv ⊢
  split
  · rename_i hvf
    exact chainInv_up hk.2 hk.1.2 hk.1.1.1.2.2.1 hg.docs hvf hfd hfb hf.2.2.2.1 hf.2.2.1 hf.2.1 hta hdstep
      (by omega)
  · rename_i hvf
    rw [if_neg hvf] at hv
    exact absurd hv hvf

theorem sInvC_initSeed : SInvC (initSeed (⟨0, 0⟩ : NodeId) "") := ⟨sInvS_initSeed, chainInv_initSeed⟩

/-- **En el join, `StarJoinDown` es `UnionTopClique` de la unión**: `⇐` por `CliqueSplit`; `⇒` porque con
`StarJoinDown` la unión tiene `StarInv` y `ChainInv`, y la bajada del lector da la camarilla. -/
theorem starJoinDown_iff_unionClique {U : Int} (hU : 2 ≤ U) {key : NodeId} {e g : GPathB} (he : StateOk U key e)
    (hg : StateOk U key g) (hke : SInvC e) (hkg : SInvC g) (hok : okJoin e g = true) (hsp : CSplit e g) :
    StarJoinDown e g ↔ UnionTopClique (join e g) := by
  have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
  constructor
  · intro hjd
    have hse := hke.1.1.1.2
    have hsg := hkg.1.1.1.2
    exact topClique_of_chain (chainInv_join hcs (by rw [he.step]; omega) hke.2 hkg.2 hjd)
      (starInv_join hcs hke.1.2 hkg.1.2 hjd) (aliveDocs_join he.docs hg.docs) (below_join he.below hg.below hcs)
      (aboveZero_join hse.2.2.2.2.1 hsg.2.2.2.2.1) (linksStep_join hse.2.2.2.1 hsg.2.2.2.1)
  · exact starJoinDown_of_unionClique hok hsp

/-- **El veredicto del lector bajo `UnionTopClique` en los joins, con la bajada del lector en toda la línea.** -/
theorem readerVerdict_iff_of_unionClique' {φ : Cnf} (hbd : Bounded φ)
    (H : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
      UnionTopClique (join e g)) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_provC hbd (upProv_C φ)
      (fun U hU key _ e g _ he hg hke hkg _ _ _ _ _ hsp =>
        have hjd : okJoin e g = true → StarJoinDown e g :=
          fun hok => starJoinDown_of_unionClique hok hsp (H U key e g hU he hg hke hkg hok)
        ⟨joinStep_ok hU he hke.1 hkg.1 hjd, chainInv_doJoin_ok (by rw [he.step]; omega) hke.2 hkg.2 hjd⟩)
      sInvC_initSeed kv hkv
    ⟨h.1, h.2.1.1.1.2⟩)

end SecLine

end AbsSatBingo.Model
