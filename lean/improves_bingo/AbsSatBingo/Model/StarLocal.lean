-- lean/improves_bingo/AbsSatBingo/Model/StarLocal.lean
import AbsSatBingo.Model.TopNbr

/-!
# `TopUnion` por la estrella y la absorción local

* **`LocalAbsorb u e`**: una estructura cerrada de la unión que vive en los vivos de `e` tiene sus parejas en `e`
  (es `KAbsorb` sin pasar por `restrictTo`). Con los enlaces completos, es entonces una estructura de `e`
  (`secStruct_of_local`).
* **`TopsSep`**: ninguna cima está viva en los dos lados.
* **`topUnion_of_local`**: `TopUnion` ⇐ `TopStarK` + `LocalAbsorb` en los dos lados + `TopsSep`. La estrella de una
  cima de `e` vive entera en `e` (la cima no está en `g`, así que sus aristas son de `e`), y la absorción local la
  lleva a `e`. Ya no hacen falta `SepAt` ni `SidePinned`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- **`LocalAbsorb`**: una estructura cerrada de `u` que vive en los vivos de `e` tiene sus parejas en `e`. -/
def LocalAbsorb (u e : GPathB) : Prop :=
  ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R → (∀ y, V y → y ∈ e.alive) →
    ∀ {y w}, R y w → e.Adj y w

/-- Ninguna cima está viva en los dos lados. -/
def TopsSep (e g : GPathB) : Prop :=
  ∀ t, t.id.step = e.current_step - 1 → t ∈ e.alive → t ∈ g.alive → False

/-- Una estructura de la unión que vive en `e` y cuyas parejas son de `e` es una estructura de `e` (los enlaces pasan
por `LinksInv`). -/
theorem secStruct_of_local {u e g : GPathB} (hu : IsUnion u e g) {V : PathNodeId → Prop}
    {R : PathNodeId → PathNodeId → Prop} (hst : SecStruct u V R) (hle : LinksInv e)
    (hal : ∀ {y}, V y → y ∈ e.alive) (hadj : ∀ {y w}, R y w → e.Adj y w) : SecStruct e V R := by
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

/-- La estrella de una cima que un lado tiene y el otro no vive en ese lado, y la absorción local la lleva a él. -/
theorem kernel_side_of_star {u e g : GPathB} (hu : IsUnion u e g) (hle : LinksInv e) (hee : EdgesAlive e)
    (heg : EdgesAlive g) (hla : LocalAbsorb u e) {P : List NodeId} {t : PathNodeId}
    (htg : t ∉ g.alive) {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop} (hst : SecStruct u V R)
    (ha : ∀ b ∈ P, SecAgrees V b) (hvt : V t) (hstar : ∀ y, V y → u.Adj t y) : Kernel e P t t := by
  have hal : ∀ {y}, V y → y ∈ e.alive := by
    intro y hy
    rcases hu.adj (hstar y hy) with h | h
    · exact (hee t y h).2
    · exact absurd (heg t y h).1 htg
  exact ⟨V, R, secStruct_of_local hu hst hle hal (fun h => hla V R hst (fun _ hy => hal hy) h), ha, hst.refl hvt⟩

/-- **`TopUnion` ⇐ `TopStarK` + `LocalAbsorb` en los dos lados + `TopsSep`.** -/
theorem topUnion_of_local {e g : GPathB} (hcs : e.current_step = g.current_step) (hle : LinksInv e)
    (hlg : LinksInv g) (hee : EdgesAlive e) (heg : EdgesAlive g) (hstar : TopStarK (join e g))
    (hae : LocalAbsorb (join e g) e) (hag : LocalAbsorb (join e g) g) (hts : TopsSep e g) : TopUnion e g := by
  intro P t hts' hk
  obtain ⟨V, R, hst, ha, hvt, hs⟩ := hstar P t hts' hk
  rcases (alive_join e g t).mp (hst.alive hvt) with hte | htg
  · exact Or.inl (kernel_side_of_star (isUnion_join_left hle hlg hee heg) hle hee heg hae
      (fun h => hts t hts' hte h) hst ha hvt hs)
  · exact Or.inr (kernel_side_of_star (isUnion_join_right hcs hle hlg hee heg) hlg heg hee hag
      (fun h => hts t hts' h htg) hst ha hvt hs)

end GPathB

end AbsSatBingo.Model
