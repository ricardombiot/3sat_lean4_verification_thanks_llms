-- lean/improves_bingo/AbsSatBingo/Model/SecSplitInParts.lean
import AbsSatBingo.Model.SecIn

/-!
# `SecSplitIn` desde dentro de la unión

`SecSplitIn e g` (la única hipótesis de `readerVerdict_iff_of_secIn`) habla de estructuras cerradas **de los lados**.
Aquí se lleva a una propiedad **de la unión sola**:

* **`secStruct_of_sideEdges`**: una estructura cerrada de la unión cuyos nodos viven en `e` y cuyas parejas son
  posesiones de `e` es una estructura cerrada de `e` (los enlaces pasan por `LinksInv`). Es el núcleo de
  `secStruct_side`, sin el pin.
* **`SideSubIn u e g`**: toda estructura cerrada no vacía de la unión que concuerda con `P` contiene otra estructura
  cerrada no vacía **de la unión**, que concuerda con `P` y cuyas parejas son todas posesiones de un mismo lado.
* **`secSplitIn_of_sideSubIn`**: `SideSubIn` ⟹ `SecSplitIn` (los nodos viven en el lado por la reflexiva).

Y `SideSubIn` por colores (`sideSubIn_of_parts`): fijar dentro de `V` el color de un lado deja algo
(**`SplitIn2`**, la versión «dentro» de `SplitSat2`), y fijada la unión en ese color sus parejas son del lado
(`SideEdgesAt`, con la separación ya demostrada). Veredictos: `readerVerdict_iff_of_sideSubIn`,
`readerVerdict_iff_of_splitIn`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- **Una estructura cerrada de la unión con nodos y parejas de `e` es una estructura cerrada de `e`.** -/
theorem secStruct_of_sideEdges {u e g : GPathB} (hu : IsUnion u e g) (hst : SecStruct u V R)
    (hal : ∀ {y}, V y → y ∈ e.alive) (hadj : ∀ {y w}, R y w → e.Adj y w) (hle : LinksInv e) : SecStruct e V R := by
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

/-- **`SideSubIn`**: dentro de toda estructura cerrada no vacía de la unión hay otra, cerrada en la unión, que
concuerda con `P` y cuyas parejas son todas de un mismo lado. -/
def SideSubIn (u e g : GPathB) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct u V R → (∀ b ∈ P, SecAgrees V b) → (∃ y, V y) →
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧
        (∀ b ∈ P, SecAgrees W b) ∧ (∃ y, W y) ∧ (∀ y, W y → V y) ∧ ∀ {y w}, R' y w → e.Adj y w) ∨
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧
        (∀ b ∈ P, SecAgrees W b) ∧ (∃ y, W y) ∧ (∀ y, W y → V y) ∧ ∀ {y w}, R' y w → g.Adj y w)

/-- **`SideSubIn` ⟹ `SecSplitIn`.** -/
theorem secSplitIn_of_sideSubIn {e g : GPathB} (hcs : e.current_step = g.current_step) (hle : LinksInv e)
    (hlg : LinksInv g) (hee : EdgesAlive e) (heg : EdgesAlive g) (hsub : SideSubIn (join e g) e g) :
    SecSplitIn e g := by
  intro P V R hst ha hne
  by_cases hok : okJoin e g = true
  · have hj : doJoin e g = join e g := by unfold doJoin; rw [if_pos hok]
    rw [hj] at hst
    rcases hsub P V R hst ha hne with ⟨W, R', h1, h2, h3, h4, h5⟩ | ⟨W, R', h1, h2, h3, h4, h5⟩
    · have hal : ∀ {y}, W y → y ∈ e.alive := fun hy => (hee _ _ (h5 (h1.refl hy))).1
      exact Or.inl ⟨W, R', secStruct_of_sideEdges (isUnion_join_left hle hlg hee heg) h1 hal h5 hle, h2, h3, h4⟩
    · have hal : ∀ {y}, W y → y ∈ g.alive := fun hy => (heg _ _ (h5 (h1.refl hy))).1
      exact Or.inr ⟨W, R', secStruct_of_sideEdges (isUnion_join_right hcs hle hlg hee heg) h1 hal h5 hlg,
        h2, h3, h4⟩
  · have hj : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [hj] at hst
    exact Or.inl ⟨V, R, hst, ha, hne, fun _ h => h⟩

-- ============================================================
-- Por colores
-- ============================================================

/-- **`SplitIn2`**: dentro de toda estructura cerrada no vacía de `u` que concuerda con `P` hay otra que concuerda
además con el color `a` o con el color `s`. -/
def SplitIn2 (u : GPathB) (a s : NodeId) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct u V R → (∀ b ∈ P, SecAgrees V b) → (∃ y, V y) →
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧
        (∀ c ∈ P ++ [a], SecAgrees W c) ∧ (∃ y, W y) ∧ ∀ y, W y → V y) ∨
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧
        (∀ c ∈ P ++ [s], SecAgrees W c) ∧ (∃ y, W y) ∧ ∀ y, W y → V y)

/-- **`SplitIn2` + `SideEdgesAt` (con la separación) ⟹ `SideSubIn`**. -/
theorem sideSubIn_of_parts {e g : GPathB} {k : Int} {a s : NodeId} (ha : a.step = k) (hs : s.step = k)
    (hoa : OffSide g a) (hos : OffSide e s) (hsp : SplitIn2 (join e g) a s) (hse : SideEdgesAt e g k) :
    SideSubIn (join e g) e g := by
  intro P V R hst hag hne
  rcases hsp P V R hst hag hne with ⟨W, R', h1, h2, h3, h4⟩ | ⟨W, R', h1, h2, h3, h4⟩
  · have hWa : SecAgrees W a := h2 a (List.mem_append_right _ (List.mem_singleton_self a))
    exact Or.inl ⟨W, R', h1, fun b hb => h2 b (List.mem_append_left _ hb), h3, h4,
      fun hr => ((hse a ha).1 hoa) W R' h1 hWa hr⟩
  · have hWs : SecAgrees W s := h2 s (List.mem_append_right _ (List.mem_singleton_self s))
    exact Or.inr ⟨W, R', h1, fun b hb => h2 b (List.mem_append_left _ hb), h3, h4,
      fun hr => ((hse s hs).2 hos) W R' h1 hWs hr⟩

-- ============================================================
-- A nivel de nodo
-- ============================================================

/-- **`ColourSurvive`**: todo nodo `x` de `V` en el paso `k` sigue vivo en una estructura cerrada dentro de `V` que
concuerda además con su color. (Medido: `probe_secin.jl`, 7 183 nodos, 0 fallos.) -/
def ColourSurvive (u : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct u V R → (∀ b ∈ P, SecAgrees V b) → ∀ x, V x → x.id.step = k →
    ∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct u W R' ∧
      (∀ c ∈ P ++ [x.id], SecAgrees W c) ∧ W x ∧ ∀ y, W y → V y

/-- **`ColourSurvive` ⟹ `SplitIn2`**: el testigo del paso `k` de cualquier nodo de `V` es de `a` o de `s`, y su
color sobrevive. -/
theorem splitIn2_of_colourSurvive {u : GPathB} {k : Int} {a s : NodeId} (hk0 : 0 ≤ k) (hkc : k < u.current_step)
    (ho : OriginIn u k (fun c => c = a ∨ c = s)) (h : ColourSurvive u k) : SplitIn2 u a s := by
  intro P V R hst hag ⟨y, hy⟩
  obtain ⟨x, hxs, hyx, _⟩ := hst.pair (hst.refl hy) k hk0 hkc
  have hxV := (hst.dom hyx).2
  obtain ⟨W, R', h1, h2, h3, h4⟩ := h P V R hst hag x hxV hxs
  rcases ho x (hst.alive hxV) hxs with hxa | hxs'
  · exact Or.inl ⟨W, R', h1, by rw [← hxa]; exact h2, ⟨x, h3⟩, h4⟩
  · exact Or.inr ⟨W, R', h1, by rw [← hxs']; exact h2, ⟨x, h3⟩, h4⟩

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- **`SideSubIn` en cada join** (una propiedad de la unión sola). -/
structure HypsSideSub (φ : Cnf) : Prop where
  sub : ∀ T key e g a s, 2 ≤ T → StateOk T key e → StateOk T key g → SInvIn e → SInvIn g → Key (T - 2) a →
          Key (T - 2) s → a ≠ s → OriginIn e (T - 2) (· = a) → OriginIn g (T - 2) (· = s) →
          SideSubIn (join e g) e g

theorem hypsIn_of_sideSub {φ : Cnf} (H : HypsSideSub φ) : HypsIn φ := by
  refine ⟨fun T key e g a s hT he hg hke hkg hka hks hne hoe hog => ?_⟩
  exact secSplitIn_of_sideSubIn (he.step.trans hg.step.symm) hke.2.2.2.2.2.2.2 hkg.2.2.2.2.2.2.2 hke.2.2.2.1
    hkg.2.2.2.1 (H.sub T key e g a s hT he hg hke hkg hka hks hne hoe hog)

/-- **El veredicto del lector bajo `SideSubIn` en los joins.** -/
theorem readerVerdict_iff_of_sideSubIn {φ : Cnf} (hbd : Bounded φ) (H : HypsSideSub φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_secIn hbd (hypsIn_of_sideSub H)

/-- **Por colores**: `SplitIn2` (fijar dentro de `V` el color de un lado deja algo) y `SideEdgesAt`. -/
structure HypsSplitIn (φ : Cnf) : Prop where
  split : ∀ T key e g a s, 2 ≤ T → StateOk T key e → StateOk T key g → SInvIn e → SInvIn g → Key (T - 2) a →
            Key (T - 2) s → a ≠ s → OriginIn e (T - 2) (· = a) → OriginIn g (T - 2) (· = s) →
            SplitIn2 (join e g) a s
  side  : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvIn e → SInvIn g →
            SideEdgesAt e g (T - 2)

theorem hypsSideSub_of_parts {φ : Cnf} (H : HypsSplitIn φ) : HypsSideSub φ := by
  refine ⟨fun T key e g a s hT he hg hke hkg hka hks hne hoe hog => ?_⟩
  have hoa : OffSide g a := fun q hq hqa => hne (hqa ▸ (hog q hq (by rw [hqa]; exact hka.1)))
  have hos : OffSide e s := fun q hq hqs => hne ((hoe q hq (by rw [hqs]; exact hks.1)).symm.trans hqs)
  exact sideSubIn_of_parts hka.1 hks.1 hoa hos (H.split T key e g a s hT he hg hke hkg hka hks hne hoe hog)
    (H.side T key e g hT he hg hke hkg)

/-- **El veredicto del lector bajo `SplitIn2` y `SideEdgesAt`.** -/
theorem readerVerdict_iff_of_splitIn {φ : Cnf} (hbd : Bounded φ) (H : HypsSplitIn φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_sideSubIn hbd (hypsSideSub_of_parts H)


/-- **Local**: `ColourSurvive` en cada join (a nivel de nodo) y `SideEdgesAt`. -/
structure HypsLocal (φ : Cnf) : Prop where
  survive : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvIn e → SInvIn g →
              ColourSurvive (join e g) (T - 2)
  side    : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvIn e → SInvIn g →
              SideEdgesAt e g (T - 2)

theorem hypsSplitIn_of_local {φ : Cnf} (H : HypsLocal φ) : HypsSplitIn φ := by
  refine ⟨fun T key e g a s hT he hg hke hkg _ _ _ hoe hog => ?_, H.side⟩
  refine splitIn2_of_colourSurvive (by omega) (by show T - 2 < e.current_step; rw [he.step]; omega) ?_
    (H.survive T key e g hT he hg hke hkg)
  intro q hq hk
  rcases (alive_join e g q).mp hq with h | h
  · exact Or.inl (hoe q h hk)
  · exact Or.inr (hog q h hk)

/-- **El veredicto del lector bajo `ColourSurvive` y `SideEdgesAt`.** -/
theorem readerVerdict_iff_of_local {φ : Cnf} (hbd : Bounded φ) (H : HypsLocal φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_splitIn hbd (hypsSplitIn_of_local H)

end SecLine

end AbsSatBingo.Model
