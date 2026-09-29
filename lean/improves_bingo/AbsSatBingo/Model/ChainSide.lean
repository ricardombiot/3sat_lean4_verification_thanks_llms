-- lean/improves_bingo/AbsSatBingo/Model/ChainSide.lean
import AbsSatBingo.Model.StarHole

/-!
# `ChainInv` sin B1

`ChainInv u`: en una estructura cerrada fijada (un nodo por paso) desde un paso de la cima o inferior, cualquier nodo
se puede fijar también. Es lo que garantiza que el lector por caminos **con revisión** no se atasque con ninguna
elección (medido: `probe_spinehyps.jl`, 1 620 lecturas con elecciones al azar, 0 atascos).

* **`chainInv_join_oneSide`** (demostrado): en el join, una estructura fijada desde la cima tiene una sola cima `t` y
  cabe en su estrella; `StarOneSide` en el lado de `t` (que sale de los huecos, `oneSide_holes`) la hace de ese lado
  (B3), y se aplica el `ChainInv` del lado. **Sin `StarJoinDown`.**
* **`chainInv_up_sib`**: el UP de `chainInv_up`, pidiendo `StarInv` del remitente solo en estructuras cuyas cimas son
  hermanos (mismo id y mismo padre): `SibStarInv`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (shiftPid)

namespace GPathB

open Machine (Below)

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- **Una estructura fijada desde la cima de la unión es de un lado.** Si la cima `t` vive en `L` (y no en el otro
lado `O`), `StarOneSide` en `L` hace que todas las parejas de la estructura sean aristas de `L`. -/
theorem pinned_side {u L O : GPathB} (hu : ∀ {a b}, u.Adj a b → L.Adj a b ∨ O.Adj a b) (heaL : EdgesAlive L)
    (heaO : EdgesAlive O) (hL : StarOneSideAt u L) (hst : SecStruct u V R) {t : PathNodeId} (htV : V t)
    (htL : t ∈ L.alive) (htO : t ∉ O.alive) (hts : t.id.step = u.current_step - 1)
    (hstar : ∀ y, V y → R y t) : ∀ {y w}, R y w → L.Adj y w := by
  have htside : ∀ {a}, u.Adj t a → L.Adj t a := by
    intro a h
    rcases hu h with h | h
    · exact h
    · exact absurd (heaO t a h).1 htO
  intro y w hyw
  have hyt := hst.adj (hstar y (hst.dom hyw).1)
  have hwt := hst.adj (hstar w (hst.dom hyw).2)
  by_cases hy_eq : y = w
  · subst hy_eq
    exact adj_refl _ _ (heaL _ _ (htside ((adj_symm _ _ _).mp hyt))).2
  by_cases hyt' : y = t
  · subst hyt'; exact htside (hst.adj hyw)
  by_cases hwt' : w = t
  · subst hwt'; exact (adj_symm _ _ _).mp (htside ((adj_symm _ _ _).mp (hst.adj hyw)))
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨l, h0, h1, hl⟩ := hL t htL hts y w ((adj_symm _ _ _).mp hyt) ((adj_symm _ _ _).mp hwt) (hst.adj hyw) hne
  obtain ⟨r, hrl, hyr, hwr⟩ := hst.pair hyw l h0 h1
  exact hl r hrl ((adj_symm _ _ _).mp (hst.adj (hstar r (hst.dom hyr).2))) ⟨hst.adj hyr, hst.adj hwr⟩

/-- **El join conserva `ChainInv` con `StarOneSide` en los dos lados** (y las cimas de un lado no viven en el otro). -/
theorem chainInv_join_oneSide {e g : GPathB} (hcs : e.current_step = g.current_step) (hpos : 1 ≤ e.current_step)
    (hle : LinksInv e) (hlg : LinksInv g) (hee : EdgesAlive e) (heg : EdgesAlive g)
    (he : ChainInv e) (hg : ChainInv g)
    (hE : StarOneSideAt (join e g) e) (hG : StarOneSideAt (join e g) g)
    (hDe : ∀ t, t ∈ e.alive → t.id.step = e.current_step - 1 → t ∉ g.alive)
    (hDg : ∀ t, t ∈ g.alive → t.id.step = e.current_step - 1 → t ∉ e.alive) : ChainInv (join e g) := by
  have hje : (join e g).current_step = e.current_step := rfl
  intro V R hst j hj hpin x hx
  by_cases hxj : j ≤ x.id.step
  · exact ⟨V, R, hst, fun _ h => h, hx, fun y hy hys => hpin y x hy hx (by omega) hys⟩
  obtain ⟨t, htV, hts, _⟩ := exists_at hst hx (e.current_step - 1) (by omega) (by rw [hje]; omega)
  have htop : ∀ y, V y → y.id.step = e.current_step - 1 → y = t :=
    fun y hy hys => hpin y t hy htV (by rw [hje] at hj; omega) (by rw [hys, hts])
  have hstar : ∀ y, V y → R y t := by
    intro y hy
    obtain ⟨r, hrV, hrs, hyr⟩ := exists_at hst hy (e.current_step - 1) (by omega) (by rw [hje]; omega)
    rw [← htop r hrV hrs]; exact hyr
  rcases (alive_join e g t).mp (hst.alive htV) with hte | htg
  · have hside : ∀ {y w}, R y w → e.Adj y w := pinned_side (L := e) (O := g) adj_join_cases hee heg hE hst htV hte (hDe t hte hts)
      (by rw [hje]; exact hts) hstar
    obtain ⟨W, R'', hW, hWs, hxW, hpx⟩ := he V R
      (secStruct_to_side (isUnion_join_left hle hlg hee heg) hst hle hee hside) j (by rw [← hje]; exact hj) hpin x hx
    exact ⟨W, R'', secStruct_join_left hW, hWs, hxW, hpx⟩
  · have hside : ∀ {y w}, R y w → g.Adj y w := pinned_side (L := g) (O := e) (fun h => (adj_join_cases h).symm) heg hee hG hst htV htg
      (hDg t htg hts) (by rw [hje]; exact hts) hstar
    obtain ⟨W, R'', hW, hWs, hxW, hpx⟩ := hg V R
      (secStruct_to_side (isUnion_join_right hcs hle hlg hee heg) hst hlg heg hside) j
      (by rw [← hcs, ← hje]; exact hj) hpin x hx
    exact ⟨W, R'', secStruct_join_right hcs hW, hWs, hxW, hpx⟩

/-- **`StarInv` solo para estructuras cuyas cimas son hermanos** (mismo id y mismo padre; en bin, como mucho dos). -/
def SibStarInv (u : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R →
    (∀ y w, V y → V w → y.id.step = u.current_step - 1 → w.id.step = u.current_step - 1 →
      y.id = w.id ∧ y.parent_id = w.parent_id) →
    ∀ t, V t → t.id.step = u.current_step - 1 → ∀ z, V z → R z t →
    ∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧ W z ∧ W t ∧
      (∀ y, W y → V y) ∧ (∀ y, W y → R' y t) ∧ (∀ y, W y → y.id.step = u.current_step - 1 → y = t)

theorem sibStarInv_of_starInv {u : GPathB} (h : StarInv u) : SibStarInv u :=
  fun V R hst _ t ht hts z hz hzt => h V R hst t ht hts z hz hzt

variable {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **El UP conserva `ChainInv`** con `SibStarInv` en el estado anterior (solo estructuras de hermanos). -/
theorem chainInv_up_sib {g₀ : GPathB} {reqs : List NodeId} (hC : ChainInv g₀) (hS : SibStarInv g₀) (hnd₀ : NodupIds g₀)
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
  -- las cimas de la estructura en el remitente son padres de t: hermanos
  have hsib : ∀ y w, (V y ∧ y.id.step < f.current_step) → (V w ∧ w.id.step < f.current_step) →
      y.id.step = g₀.current_step - 1 → w.id.step = g₀.current_step - 1 →
      y.id = w.id ∧ y.parent_id = w.parent_id := by
    have hpar : ∀ y, V y → y.id.step = f.current_step - 1 → shiftPid y d = t := by
      intro y hy hys
      obtain ⟨r, hrV, hrs, hyr⟩ := exists_at hst hy f.current_step (by omega) (by rw [hcs]; omega)
      have hrt : r = t := hpin r t hrV htV (by omega) (by rw [hrs, hts])
      rw [hrt] at hyr
      have hy' := rowParent_of_adj hfd hfb hea hta hd htnew hys ((adj_symm _ _ _).mp (hst₁.adj hyr))
      simpa using (List.mem_filter.mp hy').2
    intro y w hy hw hys hws
    have h1 := hpar y hy.1 (by omega)
    have h2 := hpar w hw.1 (by omega)
    rw [← h2] at h1
    have e1 := congrArg PathNodeId.parent_id h1
    have e2 := congrArg PathNodeId.gparent_id h1
    simp only [shiftPid] at e1 e2
    exact ⟨Option.some.inj e1, e2⟩
  obtain ⟨W₀, R₀, hW₀, hxW₀, hpW₀, hsub₀, _, htop₀⟩ :=
    hS _ _ hst₃ hsib p hVp (by omega) x ⟨hx, hxo⟩ ⟨hxp, hxo, hVp.2⟩
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

end GPathB

end AbsSatBingo.Model
