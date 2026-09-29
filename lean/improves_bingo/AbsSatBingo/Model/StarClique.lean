-- lean/improves_bingo/AbsSatBingo/Model/StarClique.lean
import AbsSatBingo.Model.StarSide
import AbsSatBingo.Model.KernelCliques
import AbsSatBingo.Model.SplitWitness

/-!
# `StarJoinDown` ⇐ camarillas del lado por la cima (`StarCliqueSide`)

La unión de estructuras cerradas es cerrada (`secStruct_iUnion`, de `SplitWitness.lean`). En particular, la unión de todas las
camarillas **buenas** de un lado `L` para una cima `t` y una estructura `(V, R)` de la unión —llevadas en `L`, con
`t` en la cima y relacionadas dos a dos por `R`— es una estructura cerrada de `L` dentro de `V`, sin hipótesis.

> **`StarCliqueSide u L`**: para toda estructura cerrada `(V, R)` de `u`, toda cima `t ∈ V` viva en `L` y todo
> `z ∈ V` con `R z t` y `L.Adj z t`, hay una camarilla buena por `z`.

**`starJoinDown_of_starClique`**: `StarCliqueSide` en los dos lados ⟹ `StarJoinDown`. Veredicto:
**`readerVerdict_iff_of_starClique`**, bajo `StarCliqueSide` y `SideEdgesAt`.

Medido (`julia/improves_bingo/test_3sat/probe_trio_clique.jl`): el lado de la cima restringido a su estrella y
revisado tiene todos sus nodos y aristas en camarillas (que pasan todas por `t`, su única cima, y usan aristas de `V`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

/-- Una camarilla buena: llevada en `L`, con `t` en la cima y relacionada dos a dos por `R`. -/
def GoodClique (L : GPathB) (R : PathNodeId → PathNodeId → Prop) (t : PathNodeId) (C : Int → PathNodeId) : Prop :=
  Carried L C ∧ C (L.current_step - 1) = t ∧
    ∀ k l, 0 ≤ k → k < L.current_step → 0 ≤ l → l < L.current_step → R (C k) (C l)

/-- **Toda estrella de una cima de la unión tiene sus nodos en camarillas buenas del lado de la cima.** -/
def StarCliqueSide (u L : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R →
    ∀ t, V t → t.id.step = u.current_step - 1 → t ∈ L.alive → ∀ z, V z → R z t → L.Adj z t →
    ∃ C, GoodClique L R t C ∧ OnS L.current_step C z

/-- Un lado: la unión de las camarillas buenas da la estructura que pide `StarJoinDown`. -/
theorem side_down_clique {u L : GPathB} (hpos : 0 < L.current_step) (hT : StarCliqueSide u L)
    {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop} (hst : SecStruct u V R) {t z : PathNodeId}
    (htV : V t) (hts : t.id.step = u.current_step - 1) (hzV : V z) (hzt : R z t) (hzL : L.Adj z t)
    (htL : t ∈ L.alive) :
    ∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
      SecStruct L V' R' ∧ V' z ∧ V' t ∧ R' z t ∧ ∀ y, V' y → V y := by
  let ι := { C : Int → PathNodeId // GoodClique L R t C }
  have hS := secStruct_iUnion (g := L) (ι := ι) (V := fun C => OnS L.current_step C.1)
    (R := fun C y w => OnS L.current_step C.1 y ∧ OnS L.current_step C.1 w) (fun C => secStruct_of_carried C.2.1)
  obtain ⟨C, hC, hz⟩ := hT V R hst t htV hts htL z hzV hzt hzL
  have ht : OnS L.current_step C t := ⟨L.current_step - 1, by omega, by omega, hC.2.1⟩
  refine ⟨_, _, hS, ⟨⟨C, hC⟩, hz⟩, ⟨⟨C, hC⟩, ht⟩, ⟨⟨C, hC⟩, hz, ht⟩, ?_⟩
  rintro y ⟨⟨C', hC'⟩, k, h0, h1, rfl⟩
  exact (hst.dom (hC'.2.2 k k h0 h1 h0 h1)).1

/-- **`StarCliqueSide` en los dos lados ⟹ `StarJoinDown`.** -/
theorem starJoinDown_of_starClique {e g : GPathB} (hcs : e.current_step = g.current_step)
    (hpos : 0 < e.current_step) (heae : EdgesAlive e) (heag : EdgesAlive g)
    (hTe : StarCliqueSide (join e g) e) (hTg : StarCliqueSide (join e g) g) : StarJoinDown e g := by
  intro V R hst t htV hts z hzV hzt
  rcases adj_join_cases (hst.adj hzt) with h | h
  · obtain ⟨V', R', h1, h2, h3, h4, h5⟩ := side_down_clique hpos hTe hst htV hts hzV hzt h (heae z t h).2
    exact ⟨V', R', Or.inl h1, h2, h3, h4, h5⟩
  · obtain ⟨V', R', h1, h2, h3, h4, h5⟩ :=
      side_down_clique (hcs ▸ hpos) hTg hst htV hts hzV hzt h (heag z t h).2
    exact ⟨V', R', Or.inr h1, h2, h3, h4, h5⟩

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- **Las hipótesis**: `StarCliqueSide` en los dos lados y `SideEdgesAt` en cada join. -/
structure HypsStarClique (φ : Cnf) : Prop where
  clique : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g →
    StarCliqueSide (join e g) e ∧ StarCliqueSide (join e g) g
  side : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g → SideEdgesAt e g (T - 2)

/-- **El veredicto del lector es la satisfacibilidad bajo `StarCliqueSide` y `SideEdgesAt` en los joins.** -/
theorem readerVerdict_iff_of_starClique {φ : Cnf} (hbd : Bounded φ) (H : HypsStarClique φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_starJoinDown hbd ⟨fun T key e g hT he hg hke hkg =>
    have ht := H.clique T key e g hT he hg hke hkg
    starJoinDown_of_starClique (he.step.trans hg.step.symm) (by rw [he.step]; omega)
      hke.1.1.2.2.2.1 hkg.1.1.2.2.2.1 ht.1 ht.2, H.side⟩

/-- **`StarJoinDown` ⟹ `NodeSplitIn`**: un nodo `x` de una estructura de la unión tiene una cima testigo `t`
(regla de parejas); la estructura del lado que da `StarJoinDown` para `x` y `t` vive dentro de `V`, así que concuerda
con `P`. No hace falta `SideEdgesAt`. -/
theorem nodeSplitIn_of_starJoinDown {e g : GPathB} (hcs : e.current_step = g.current_step)
    (hpos : 1 ≤ e.current_step) (hjd : StarJoinDown e g) : NodeSplitIn e g := by
  intro P V R hst ha x hx
  unfold doJoin at hst
  split at hst
  · have hje : (join e g).current_step = e.current_step := rfl
    obtain ⟨t, hts, hxt, _⟩ := hst.pair (hst.refl hx) (e.current_step - 1) (by omega) (by rw [hje]; omega)
    obtain ⟨V', R', hside, hxV', _, _, hsub⟩ :=
      hjd V R hst t (hst.dom hxt).2 (by rw [hts, hje]) x hx hxt
    have hag : ∀ b ∈ P, SecAgrees V' b := fun b hb y hy hys => ha b hb (hsub y hy) hys
    rcases hside with h | h
    · exact Or.inl ⟨V', R', h, hag, hxV', hsub⟩
    · exact Or.inr ⟨V', R', h, hag, hxV', hsub⟩
  · exact Or.inl ⟨V, R, hst, ha, hx, fun _ hy => hy⟩

/-- El paso del join con solo `StarJoinDown`. -/
theorem joinStep_down {U : Int} (hU : 2 ≤ U) {key : NodeId} {e g : GPathB} (he : StateOk U key e)
    (hg : StateOk U key g) (hke : SInvS e) (hkg : SInvS g) (hjd : StarJoinDown e g) : SInvS (doJoin e g) := by
  have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
  have hsp : NodeSplitIn e g := nodeSplitIn_of_starJoinDown hcs (by rw [he.step]; omega) hjd
  exact ⟨⟨⟨nodeIn_doJoin hke.1.1.1 hkg.1.1.1 hsp,
      sInv_doJoin_of (secSplit_of_in (secSplitIn_of_node hsp)) hke.1.1.2 hkg.1.1.2⟩,
    topsApart_doJoin hke.1.2.1 hkg.1.2.1, topNbr_doJoin hke.1.2.2 hkg.1.2.2⟩,
    starInv_doJoin hke.2 hkg.2 (fun _ => hjd)⟩

/-- **Una sola hipótesis**: `StarJoinDown` en cada join. -/
structure HypsDown (φ : Cnf) : Prop where
  down : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g → StarJoinDown e g

/-- **El veredicto del lector es la satisfacibilidad bajo `StarJoinDown` en los joins**, sin `SideEdgesAt`. -/
theorem readerVerdict_iff_of_down {φ : Cnf} (hbd : Bounded φ) (H : HypsDown φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_prov (upProv_S φ)
      (fun _ hU key _ e g _ he hg hke hkg _ _ _ _ _ => joinStep_down hU he hg hke hkg (H.down _ key e g hU he hg hke hkg))
      sInvS_initSeed kv hkv
    ⟨h.1, h.2.1.1.2⟩)

/-- **Una sola hipótesis, en camarillas**: `StarCliqueSide` en los dos lados de cada join. -/
theorem readerVerdict_iff_of_starCliqueOnly {φ : Cnf} (hbd : Bounded φ)
    (H : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g →
      StarCliqueSide (join e g) e ∧ StarCliqueSide (join e g) g) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_down hbd ⟨fun T key e g hT he hg hke hkg =>
    have ht := H T key e g hT he hg hke hkg
    starJoinDown_of_starClique (he.step.trans hg.step.symm) (by rw [he.step]; omega)
      hke.1.1.2.2.2.1 hkg.1.1.2.2.2.1 ht.1 ht.2⟩

end SecLine

end AbsSatBingo.Model
