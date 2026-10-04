-- lean/improves_bingo/AbsSatBingo/Model/StarSplit.lean
import AbsSatBingo.Model.ChainPin

/-!
# La dirección difícil, en dos piezas: Helly en la unión (B1) y pureza de lado (B2)

`StarJoinDown` (la única hipótesis del lector) se construye con el punto fijo de la estrella de la cima `t` en la
unión. Eso la parte en:

* **B1 = `StarNodes (join e g)`**: la estrella de una cima de la unión conserva sus nodos. Solo habla de la unión.
* **B2 = `StarPure e g`**: una estructura cerrada de la unión dentro de la estrella de una cima solo usa aristas del
  lado donde vive la cima. Solo habla de lados; no tiene Helly.
* **B3 = `secStruct_to_side`** (demostrado): una estructura cerrada de la unión con aristas de un lado es cerrada en
  ese lado (los enlaces del lado son completos).

**`starJoinDown_of_split`**: B1 + B2 ⟹ `StarJoinDown`. Veredicto: **`readerVerdict_iff_of_split`**.

Medido (`probe_star_fixpoint.jl`, 88 instancias, 26 258 estrellas): B1 (`nf = 0`) y B2 (`side_miss = 0`: toda arista
del punto fijo de la estrella es del lado de la cima).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

/-- **B3: una estructura cerrada de la unión con aristas de un lado es cerrada en ese lado.** -/
theorem secStruct_to_side {u e g : GPathB} (hu : IsUnion u e g) {V : PathNodeId → Prop}
    {R : PathNodeId → PathNodeId → Prop} (hst : SecStruct u V R) (hle : LinksInv e) (hee : EdgesAlive e)
    (hadj : ∀ {y w}, R y w → e.Adj y w) : SecStruct e V R := by
  have hal : ∀ {y}, V y → y ∈ e.alive := fun hy => (hee _ _ (hadj (hst.refl hy))).1
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

/-- **B2: pureza de lado.** Una estructura cerrada de la unión dentro de la estrella de una cima `t` solo usa
aristas del lado donde vive `t`. -/
def StarPure (e g : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct (join e g) V R →
    ∀ t, V t → t.id.step = (join e g).current_step - 1 → (∀ y, V y → y = t ∨ (join e g).Adj t y) →
    (t ∈ e.alive → ∀ {y w}, R y w → e.Adj y w) ∧ (t ∈ g.alive → ∀ {y w}, R y w → g.Adj y w)

/-- **B1 + B2 ⟹ `StarJoinDown`** (con B3 y los enlaces de los lados). -/
theorem starJoinDown_of_split {e g : GPathB} (hcs : e.current_step = g.current_step) (hpos : 1 ≤ e.current_step)
    (hle : LinksInv e) (hlg : LinksInv g) (hee : EdgesAlive e) (heg : EdgesAlive g)
    (htae : TopsApart e) (htag : TopsApart g)
    (hB1 : StarNodes (join e g)) (hB2 : StarPure e g) : StarJoinDown e g := by
  have hje : (join e g).current_step = e.current_step := rfl
  have hta : TopsApart (join e g) := topsApart_join htae htag hcs
  intro V R hst t htV hts z hzV hzt
  obtain ⟨W, R', hW, _, hzW, hWs⟩ := hB1 [] V R hst (fun _ h => absurd h List.not_mem_nil) t htV hts z hzV hzt
  -- el testigo de z en la cima, dentro de W, es t
  obtain ⟨r, hrs, hzr, _⟩ := hW.pair (hW.refl hzW) ((join e g).current_step - 1) (by rw [hje]; omega)
    (by rw [hje]; omega)
  have hrW := (hW.dom hzr).2
  have hrt : r = t := by
    rcases (hWs r hrW).2 with h | h
    · exact h
    · exact (hta t r hts hrs h).symm
  subst hrt
  have hstar : ∀ y, W y → y = r ∨ (join e g).Adj r y := fun y hy => (hWs y hy).2
  have hp := hB2 W R' hW r hrW hrs hstar
  rcases (alive_join e g r).mp (hst.alive htV) with h | h
  · refine ⟨W, R', Or.inl (secStruct_to_side (isUnion_join_left hle hlg hee heg) hW hle hee (hp.1 h)),
      hzW, hrW, hzr, fun y hy => (hWs y hy).1⟩
  · refine ⟨W, R', Or.inr (secStruct_to_side (isUnion_join_right hcs hle hlg hee heg) hW hlg heg (hp.2 h)),
      hzW, hrW, hzr, fun y hy => (hWs y hy).1⟩

/-- **StarOneSide**, sobre el grafo de la unión (sin estructuras): en la estrella de una cima `t` que vive en `L`,
toda pareja de la unión que no es arista de `L` tiene un paso en el que ningún nodo de la estrella la atestigua. -/
def StarOneSideAt (u L : GPathB) : Prop :=
  ∀ t, t ∈ L.alive → t.id.step = u.current_step - 1 → ∀ y w, u.Adj t y → u.Adj t w → u.Adj y w → ¬ L.Adj y w →
    ∃ l, 0 ≤ l ∧ l < u.current_step ∧ ∀ r, r.id.step = l → u.Adj t r → ¬ (u.Adj y r ∧ u.Adj w r)

/-- **StarOneSide ⟹ B2**: una pareja de fuera del lado no tiene testigo en algún paso dentro de la estrella, y
una estructura cerrada lo necesita. -/
theorem starPure_of_oneSide {e g : GPathB} (hE : StarOneSideAt (join e g) e) (hG : StarOneSideAt (join e g) g) :
    StarPure e g := by
  intro V R hst t htV hts hstar
  have hta : ∀ {y}, V y → (join e g).Adj t y := fun {y} hy => by
    rcases hstar y hy with rfl | h
    · exact adj_refl _ _ (hst.alive hy)
    · exact h
  have key : ∀ (L : GPathB), StarOneSideAt (join e g) L → t ∈ L.alive → ∀ {y w}, R y w → L.Adj y w := by
    intro L hO htL y w hyw
    apply Classical.byContradiction
    intro hne
    obtain ⟨l, h0, h1, hl⟩ := hO t htL hts y w (hta (hst.dom hyw).1) (hta (hst.dom hyw).2) (hst.adj hyw) hne
    obtain ⟨r, hrl, hyr, hwr⟩ := hst.pair hyw l h0 h1
    exact hl r hrl (hta (hst.dom hyr).2) ⟨hst.adj hyr, hst.adj hwr⟩
  exact ⟨fun h _ _ hyw => key e hE h hyw, fun h _ _ hyw => key g hG h hyw⟩

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- **Las dos piezas**: B1 (`StarNodes` de la unión) y B2 (`StarPure`) en los joins que se hacen. -/
structure HypsSplit (φ : Cnf) : Prop where
  b1 : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
    StarNodes (join e g)
  b2 : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
    StarPure e g

/-- **El veredicto del lector es la satisfacibilidad bajo B1 y B2 en los joins.** -/
theorem readerVerdict_iff_of_split {φ : Cnf} (hbd : Bounded φ) (H : HypsSplit φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_provC hbd (upProv_C φ)
      (fun U hU key _ e g _ he hg hke hkg _ _ _ _ _ _ =>
        have hjd : okJoin e g = true → StarJoinDown e g := fun hok =>
          have hse := hke.1.1.1.2
          have hsg := hkg.1.1.1.2
          starJoinDown_of_split (he.step.trans hg.step.symm) (by rw [he.step]; omega)
            hse.2.2.2.2.2.2 hsg.2.2.2.2.2.2 hse.2.2.1 hsg.2.2.1 hke.1.1.2.1 hkg.1.1.2.1
            (H.b1 U key e g hU he hg hke hkg hok) (H.b2 U key e g hU he hg hke hkg hok)
        ⟨joinStep_ok hU he hke.1 hkg.1 hjd, chainInv_doJoin_ok (by rw [he.step]; omega) hke.2 hkg.2 hjd⟩)
      sInvC_initSeed kv hkv
    ⟨h.1, h.2.1.1.1.2⟩)

/-- **El veredicto del lector bajo B1 (`StarNodes` de la unión) y StarOneSide (sobre el grafo de la unión).** -/
theorem readerVerdict_iff_of_oneSide {φ : Cnf} (hbd : Bounded φ)
    (H1 : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
      StarNodes (join e g))
    (H2 : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
      StarOneSideAt (join e g) e ∧ StarOneSideAt (join e g) g) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_split hbd ⟨H1, fun T key e g hT he hg hke hkg hok =>
    have h := H2 T key e g hT he hg hke hkg hok
    starPure_of_oneSide h.1 h.2⟩

end SecLine

end AbsSatBingo.Model
