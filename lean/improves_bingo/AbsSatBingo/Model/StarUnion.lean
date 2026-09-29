-- lean/improves_bingo/AbsSatBingo/Model/StarUnion.lean
import AbsSatBingo.Model.StarClique
import AbsSatBingo.Model.LineCtx

/-!
# El veredicto bajo una afirmación sobre la unión sola (`UnionTopClique`)

> **`UnionTopClique u`**: en toda estructura cerrada `(V, R)` de `u`, para toda cima `t ∈ V` y todo `z ∈ V` con
> `R z t`, hay una camarilla llevada de `u` con `t` en la cima, que pasa por `z` y tiene todos sus nodos en `V`.

Es una afirmación sobre la unión, sin lados. `CliqueSplit` (demostrado, `cliqueSplitTree`, llevado a cada join por
`run_provC`) baja la camarilla a un lado; la unión de las camarillas de ese lado por `t` dentro de `V` es cerrada
(`secStruct_iUnion`), y da `StarJoinDown`.

**`readerVerdict_iff_of_unionClique`**: el veredicto del lector es la satisfacibilidad bajo `UnionTopClique` en los
joins, como única hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

/-- **Toda pareja de una cima con su estrella está en una camarilla por la cima dentro de la estructura.** -/
def UnionTopClique (u : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R →
    ∀ t, V t → t.id.step = u.current_step - 1 → ∀ z, V z → R z t →
    ∃ C, Carried u C ∧ C (u.current_step - 1) = t ∧ OnS u.current_step C z ∧
      ∀ k, 0 ≤ k → k < u.current_step → V (C k)

/-- Las camarillas de `L` por `t` con nodos en `V`: su unión es una estructura cerrada dentro de `V`. -/
theorem side_of_clique {L : GPathB} {V : PathNodeId → Prop} {t z : PathNodeId} {C : Int → PathNodeId}
    (hC : Carried L C) (hCt : C (L.current_step - 1) = t) (hz : OnS L.current_step C z)
    (hCV : ∀ k, 0 ≤ k → k < L.current_step → V (C k)) (hpos : 0 < L.current_step) :
    ∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
      SecStruct L V' R' ∧ V' z ∧ V' t ∧ R' z t ∧ ∀ y, V' y → V y := by
  let ι := { C : Int → PathNodeId //
    Carried L C ∧ C (L.current_step - 1) = t ∧ ∀ k, 0 ≤ k → k < L.current_step → V (C k) }
  have hS := secStruct_iUnion (g := L) (ι := ι) (V := fun C => OnS L.current_step C.1)
    (R := fun C y w => OnS L.current_step C.1 y ∧ OnS L.current_step C.1 w) (fun C => secStruct_of_carried C.2.1)
  have ht : OnS L.current_step C t := ⟨L.current_step - 1, by omega, by omega, hCt⟩
  refine ⟨_, _, hS, ⟨⟨C, hC, hCt, hCV⟩, hz⟩, ⟨⟨C, hC, hCt, hCV⟩, ht⟩, ⟨⟨C, hC, hCt, hCV⟩, hz, ht⟩, ?_⟩
  rintro y ⟨⟨C', _, _, hC'V⟩, k, h0, h1, rfl⟩
  exact hC'V k h0 h1

/-- **`UnionTopClique` + `CSplit` ⟹ `StarJoinDown`** (en un join que se hace). -/
theorem starJoinDown_of_unionClique {e g : GPathB} (hok : okJoin e g = true) (hsp : SecLine.CSplit e g)
    (hu : UnionTopClique (join e g)) : StarJoinDown e g := by
  have hok' := hok
  unfold okJoin at hok'
  simp only [Bool.and_eq_true, beq_iff_eq] at hok'
  have hcs : e.current_step = g.current_step := hok'.1.1.1
  have hje : (join e g).current_step = e.current_step := rfl
  have hj : doJoin e g = join e g := by unfold doJoin; rw [if_pos hok]
  intro V R hst t htV hts z hzV hzt
  obtain ⟨C, hC, hCt, hz, hCV⟩ := hu V R hst t htV hts z hzV hzt
  have hpos : 0 < e.current_step := by
    obtain ⟨k, h0, h1, _⟩ := hz
    rw [hje] at h1; omega
  rcases hsp C (hj ▸ hC) with h | h
  · obtain ⟨V', R', h1, h2, h3, h4, h5⟩ := side_of_clique h hCt hz hCV hpos
    exact ⟨V', R', Or.inl h1, h2, h3, h4, h5⟩
  · rw [hje, hcs] at hCt hz hCV
    obtain ⟨V', R', h1, h2, h3, h4, h5⟩ := side_of_clique h hCt hz hCV (hcs ▸ hpos)
    exact ⟨V', R', Or.inr h1, h2, h3, h4, h5⟩

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- `NodeSplitIn` con `StarJoinDown` solo en los joins que se hacen. -/
theorem nodeSplitIn_of_ok {e g : GPathB} (hpos : 1 ≤ e.current_step)
    (hjd : okJoin e g = true → StarJoinDown e g) : NodeSplitIn e g := by
  intro P V R hst ha x hx
  unfold doJoin at hst
  split at hst
  · rename_i hok
    have hje : (join e g).current_step = e.current_step := rfl
    obtain ⟨t, hts, hxt, _⟩ := hst.pair (hst.refl hx) (e.current_step - 1) (by omega) (by rw [hje]; omega)
    obtain ⟨V', R', hside, hxV', _, _, hsub⟩ :=
      hjd hok V R hst t (hst.dom hxt).2 (by rw [hts, hje]) x hx hxt
    have hag : ∀ b ∈ P, SecAgrees V' b := fun b hb y hy hys => ha b hb (hsub y hy) hys
    rcases hside with h | h
    · exact Or.inl ⟨V', R', h, hag, hxV', hsub⟩
    · exact Or.inr ⟨V', R', h, hag, hxV', hsub⟩
  · exact Or.inl ⟨V, R, hst, ha, hx, fun _ hy => hy⟩

theorem starInv_doJoin_ok {e g : GPathB} (he : StarInv e) (hg : StarInv g)
    (hjd : okJoin e g = true → StarJoinDown e g) : StarInv (doJoin e g) := by
  unfold doJoin
  split
  · rename_i hok
    have hok' := hok
    unfold okJoin at hok'
    simp only [Bool.and_eq_true, beq_iff_eq] at hok'
    exact starInv_join hok'.1.1.1 he hg (hjd hok)
  · exact he

/-- El paso del join con `StarJoinDown` en los joins que se hacen. -/
theorem joinStep_ok {U : Int} (hU : 2 ≤ U) {key : NodeId} {e g : GPathB} (he : StateOk U key e)
    (hke : SInvS e) (hkg : SInvS g) (hjd : okJoin e g = true → StarJoinDown e g) : SInvS (doJoin e g) := by
  have hsp : NodeSplitIn e g := nodeSplitIn_of_ok (by rw [he.step]; omega) hjd
  exact ⟨⟨⟨nodeIn_doJoin hke.1.1.1 hkg.1.1.1 hsp,
      sInv_doJoin_of (secSplit_of_in (secSplitIn_of_node hsp)) hke.1.1.2 hkg.1.1.2⟩,
    topsApart_doJoin hke.1.2.1 hkg.1.2.1, topNbr_doJoin hke.1.2.2 hkg.1.2.2⟩,
    starInv_doJoin_ok hke.2 hkg.2 hjd⟩

/-- **La hipótesis, sobre la unión sola.** -/
structure HypsUnion (φ : Cnf) : Prop where
  union : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvS e → SInvS g → okJoin e g = true →
    UnionTopClique (join e g)

/-- **El veredicto del lector es la satisfacibilidad bajo `UnionTopClique` en los joins**, como única hipótesis. -/
theorem readerVerdict_iff_of_unionClique {φ : Cnf} (hbd : Bounded φ) (H : HypsUnion φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_provC hbd (upProv_S φ)
      (fun U hU key _ e g _ he hg hke hkg _ _ _ _ _ hsp =>
        joinStep_ok hU he hke hkg (fun hok =>
          starJoinDown_of_unionClique hok hsp (H.union U key e g hU he hg hke hkg hok)))
      sInvS_initSeed kv hkv
    ⟨h.1, h.2.1.1.2⟩)

end SecLine

end AbsSatBingo.Model
