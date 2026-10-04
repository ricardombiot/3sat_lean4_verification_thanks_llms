-- lean/improves_bingo/AbsSatBingo/Model/StarNodes.lean
import AbsSatBingo.Model.CliqueSplit
import AbsSatBingo.Model.ReaderTop

/-!
# Vía B del v208: la estrella de una cima conserva sus nodos (`StarNodes`)

> **`StarNodes u`**: dentro de una estructura cerrada `V` de `u` que concuerda con `P`, para una cima `t ∈ V` y un
> nodo `z` de su estrella (`R z t`), hay una estructura cerrada que concuerda con `P`, contiene a `z` y vive en la
> estrella de `t` (todos sus nodos están en `V` y los posee `t`).

Medido (`probe_topstar_union.jl`, 42 instancias): restringir `V` a la estrella de una cima y revisar conserva **todos**
sus nodos, 10 764 de 10 764 estrellas, en estructuras al azar y en los núcleos fijados en un color (la regla de
parejas dentro de la estrella sí falla a veces: el review corta aristas, nunca nodos). Es más fuerte que `TopStar`
(solo la cima sobrevive).

**`nodeColour_of_starNodes`**: con `TopNbr` (demostrado: en el paso de origen una cima solo posee a sus padres),
`StarNodes` da `NodeColour`. Todo nodo `x` tiene una cima testigo `t`; la estructura de su estrella que conserva a `x`
tiene en el paso de origen solo nodos que `t` posee, es decir, del color del padre de `t`.

Veredicto: **`readerVerdict_iff_of_starNodes`**, bajo `StarNodes` y `SideEdgesAt` en los joins, con `TopsApart` y
`TopNbr` añadidos al invariante de la línea.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

/-- **La estrella de una cima conserva sus nodos.** -/
def StarNodes (u : GPathB) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct u V R → (∀ b ∈ P, SecAgrees V b) → ∀ t, V t → t.id.step = u.current_step - 1 →
    ∀ z, V z → R z t →
    ∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧
      (∀ b ∈ P, SecAgrees W b) ∧ W z ∧ ∀ y, W y → V y ∧ (y = t ∨ u.Adj t y)

/-- **`StarNodes` + `TopNbr` ⟹ `NodeColour`.** -/
theorem nodeColour_of_starNodes {u : GPathB} (hsn : StarNodes u) (htn : TopNbr u) (hcs : 2 ≤ u.current_step) :
    NodeColour u (u.current_step - 2) := by
  intro P V R hst ha x hx
  -- la cima testigo de x
  obtain ⟨t, hts, hxt, _⟩ := hst.pair (hst.refl hx) (u.current_step - 1) (by omega) (by omega)
  have htV := (hst.dom hxt).2
  obtain ⟨W, R', h1, h2, h3, h4⟩ := hsn P V R hst ha t htV hts x hx hxt
  -- un nodo de W en el paso de origen: el testigo de x; t lo posee, así que es de su padre
  obtain ⟨r, hrs, hxr, _⟩ := h1.pair (h1.refl h3) (u.current_step - 2) (by omega) (by omega)
  have hrW := (h1.dom hxr).2
  have hpar : ∀ y, W y → y.id.step = u.current_step - 2 → t.parent_id = some y.id := by
    intro y hy hys
    rcases (h4 y hy).2 with hyt | hty
    · subst hyt; omega
    · exact htn t y hts hys hty
  refine ⟨r.id, hrs, W, R', h1, ?_, h3, fun y hy => (h4 y hy).1⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h2 c hc
  · rw [List.mem_singleton] at hc
    subst hc
    intro y hy hys
    have e1 := hpar y hy (by rw [hys, hrs])
    have e2 := hpar r hrW hrs
    rw [e2] at e1
    exact (Option.some.inj e1).symm

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- El invariante con las cimas: `SInvN`, `TopsApart` y `TopNbr`. -/
def SInvT (g : GPathB) : Prop := SInvN g ∧ TopsApart g ∧ TopNbr g

/-- **Las hipótesis de la vía B**: `StarNodes` y `SideEdgesAt` en cada join. -/
structure HypsStar (φ : Cnf) : Prop where
  star : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvT e → SInvT g → StarNodes (join e g)
  side : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvT e → SInvT g → SideEdgesAt e g (T - 2)

theorem upProv_T (φ : Cnf) : UpProv φ SInvT := by
  intro T key g d hg hk hT hd hv
  refine ⟨upProv_node φ T key g d hg hk.1 hT hd hv, ?_⟩
  have hs := shrinks_filterAll g (reqOf φ d)
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := (step_of_shrinks hs).trans hg.step
  have hdstep : d.step = (g.filterAll (reqOf φ d)).current_step := by
    rw [hstep, sonsOfMap_step φ key d hd, hg.key]; omega
  have hf := sInv_filterAll hk.1.2 hg.docs (reqOf φ d)
  have hfd : AliveDocs (g.filterAll (reqOf φ d)) := aliveDocs_filterAll hg.docs _
  have hfb : Below (g.filterAll (reqOf φ d)) := below_of_shrinks hs hg.below
  have hta : TopsApart (g.filterAll (reqOf φ d)) := revPrims_filterAll revPrims_topsApart _ _ hk.2.1
  have htn : TopNbr (g.filterAll (reqOf φ d)) := revPrims_filterAll revPrims_topNbr _ _ hk.2.2
  unfold upFiltering up
  split
  · rw [review_eq_filterAll]
    exact ⟨revPrims_filterAll revPrims_topsApart _ _ (topsApart_addNode hfd hfb hf.2.2.1),
      revPrims_filterAll revPrims_topNbr _ _ (topNbr_addNode hfd hfb hf.2.2.1 hta hdstep)⟩
  · exact ⟨hta, htn⟩

/-- El paso del join, con la estrella y `SideEdgesAt` de este join. -/
theorem joinStep_T {U : Int} (hU : 2 ≤ U) {key s : NodeId} {e g : GPathB} {A : NodeId → Prop}
    (he : StateOk U key e) (hg : StateOk U key g) (hke : SInvT e) (hkg : SInvT g)
    (hoe : OriginIn e (U - 2) A) (hog : OriginIn g (U - 2) (· = s)) (hsA : ¬ A s) (hAk : ∀ a, A a → Key (U - 2) a)
    (hsk : Key (U - 2) s) (hsn : StarNodes (join e g)) (hside : SideEdgesAt e g (U - 2)) :
    SInvT (doJoin e g) := by
  have hne : ∀ c, A c → c ≠ s := fun c hc h => hsA (h ▸ hc)
  have hoe' : OriginIn e (U - 2) (· = other s) :=
    originIn_mono hoe (fun c hc => eq_other (hAk c hc) hsk (hne c hc))
  have hos : other s ≠ s := by
    intro h
    have := congrArg NodeId.index h
    simp only [other] at this
    rcases hsk.2 with h' | h' <;> omega
  have hok : Key (U - 2) (other s) := by
    refine ⟨hsk.1, ?_⟩
    simp only [other]
    rcases hsk.2 with h' | h' <;> omega
  have hoa : OffSide g (other s) := fun q hq hqa => hos (hqa ▸ (hog q hq (by rw [hqa]; exact hok.1)))
  have hos' : OffSide e s := fun q hq hqs => hos ((hoe' q hq (by rw [hqs]; exact hsk.1)).symm.trans hqs)
  have ho : OriginIn (join e g) (U - 2) (fun c => c = other s ∨ c = s) := by
    intro q hq hk
    rcases (alive_join e g q).mp hq with h | h
    · exact Or.inl (hoe' q h hk)
    · exact Or.inr (hog q h hk)
  have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
  have hjs : (join e g).current_step = U := he.step
  have htnj : TopNbr (join e g) := topNbr_join hke.2.2 hkg.2.2 hcs
  have hnc : NodeColour (join e g) (U - 2) := by
    have := nodeColour_of_starNodes hsn htnj (by rw [hjs]; exact hU)
    rw [hjs] at this; exact this
  have hsp : NodeSplitIn e g :=
    nodeSplitIn_of_colour (by omega) (by rw [he.step]; omega) hcs hke.1.2.2.2.2.2.2.2 hkg.1.2.2.2.2.2.2.2
      hke.1.2.2.2.1 hkg.1.2.2.2.1 hok.1 hsk.1 hoa hos' ho hnc hside
  exact ⟨⟨nodeIn_doJoin hke.1.1 hkg.1.1 hsp, sInv_doJoin_of (secSplit_of_in (secSplitIn_of_node hsp)) hke.1.2 hkg.1.2⟩,
    topsApart_doJoin hke.2.1 hkg.2.1, topNbr_doJoin hke.2.2 hkg.2.2⟩

theorem joinProv_T {φ : Cnf} (H : HypsStar φ) {U : Int} (hU : 2 ≤ U) : JoinProv SInvT U :=
  fun key _ e g _ he hg hke hkg hoe hog hsA hAk hsk =>
    joinStep_T hU he hg hke hkg hoe hog hsA hAk hsk (H.star U key e g hU he hg hke hkg) (H.side U key e g hU he hg hke hkg)

theorem sInvT_initSeed : SInvT (initSeed (⟨0, 0⟩ : NodeId) "") :=
  let h := FinalTop.kInv_initSeed
  ⟨sInvN_initSeed, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- **El veredicto del lector es la satisfacibilidad bajo `StarNodes` y `SideEdgesAt` en los joins.** -/
theorem readerVerdict_iff_of_starNodes {φ : Cnf} (hbd : Bounded φ) (H : HypsStar φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_prov (upProv_T φ) (fun _ hU => joinProv_T H hU) sInvT_initSeed kv hkv
    ⟨h.1, h.2.1.2⟩)

end SecLine

end AbsSatBingo.Model
