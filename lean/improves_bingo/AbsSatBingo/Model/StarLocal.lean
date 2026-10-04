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

-- ============================================================
-- El descenso en la estrella
-- ============================================================

/-- **Descenso**: si toda pareja «mala» (`F`) de una estructura cerrada tiene un paso `l` en que cada testigo forma
con `x` o con `z` otra pareja mala de medida menor, la estructura no tiene parejas malas. (Inducción fuerte en la
medida; el testigo lo da la regla de parejas.) -/
theorem noBad_of_descent {g : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (hst : SecStruct g V R) (F : PathNodeId → PathNodeId → Prop) (μ : PathNodeId → PathNodeId → Nat)
    (hdesc : ∀ x z, R x z → F x z → ∃ l, 0 ≤ l ∧ l < g.current_step ∧
      ∀ w, w.id.step = l → R x w → R z w → (F x w ∧ μ x w < μ x z) ∨ (F z w ∧ μ z w < μ x z)) :
    ∀ x z, R x z → ¬ F x z := by
  have key : ∀ n, ∀ x z, μ x z = n → R x z → ¬ F x z := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro x z hn hr hf
      obtain ⟨l, h0, h1, hw⟩ := hdesc x z hr hf
      obtain ⟨w, hws, hxw, hzw⟩ := hst.pair hr l h0 h1
      rcases hw w hws hxw hzw with ⟨hf', hlt⟩ | ⟨hf', hlt⟩
      · exact ih _ (hn ▸ hlt) x w rfl hxw hf'
      · exact ih _ (hn ▸ hlt) z w rfl hzw hf'
  exact fun x z hr => key _ x z rfl hr

/-- **`StarOrder u e t μ`**: en la estrella de `t` en `u`, toda arista que `e` no tiene tiene un paso en que cada
testigo de `u` dentro de la estrella forma con un extremo otra arista que `e` no tiene, de medida menor. Medido con
μ = (paso más alto, paso más bajo) (`test_3sat/probe_starorder.jl`, orden A): sin fallos. -/
def StarOrder (u e : GPathB) (t : PathNodeId) (μ : PathNodeId → PathNodeId → Nat) : Prop :=
  ∀ x z, u.Adj t x → u.Adj t z → u.Adj x z → ¬ e.Adj x z → ∃ l, 0 ≤ l ∧ l < u.current_step ∧
    ∀ w, w.id.step = l → u.Adj t w → u.Adj x w → u.Adj z w →
      (¬ e.Adj x w ∧ μ x w < μ x z) ∨ (¬ e.Adj z w ∧ μ z w < μ x z)

/-- **Con `StarOrder`, toda estructura cerrada de la unión que vive en la estrella de `t` tiene sus parejas en `e`.** -/
theorem starAbsorb_of_order {u e : GPathB} {t : PathNodeId} {μ : PathNodeId → PathNodeId → Nat}
    (ho : StarOrder u e t μ) {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop} (hst : SecStruct u V R)
    (hstar : ∀ y, V y → u.Adj t y) : ∀ {y w}, R y w → e.Adj y w := by
  intro y w hr
  by_cases h : e.Adj y w
  · exact h
  · exfalso
    refine noBad_of_descent hst (fun a b => ¬ e.Adj a b) μ ?_ y w hr h
    intro x z hxz hf
    obtain ⟨l, h0, h1, hl⟩ := ho x z (hstar x (hst.dom hxz).1) (hstar z (hst.dom hxz).2) (hst.adj hxz) hf
    exact ⟨l, h0, h1, fun w' hws hxw hzw =>
      hl w' hws (hstar w' (hst.dom hxw).2) (hst.adj hxw) (hst.adj hzw)⟩

/-- **`TopUnion` ⇐ `TopStarK` + `StarOrder` en las estrellas + `TopsSep`** (sin `LocalAbsorb`). -/
theorem topUnion_of_order {e g : GPathB} (hcs : e.current_step = g.current_step) (hle : LinksInv e)
    (hlg : LinksInv g) (hee : EdgesAlive e) (heg : EdgesAlive g) (hstar : TopStarK (join e g))
    (μ : PathNodeId → PathNodeId → Nat)
    (hoe : ∀ t, t ∈ e.alive → t ∉ g.alive → StarOrder (join e g) e t μ)
    (hog : ∀ t, t ∈ g.alive → t ∉ e.alive → StarOrder (join e g) g t μ) (hts : TopsSep e g) :
    TopUnion e g := by
  intro P t hts' hk
  obtain ⟨V, R, hst, ha, hvt, hs⟩ := hstar P t hts' hk
  rcases (alive_join e g t).mp (hst.alive hvt) with hte | htg
  · have htg : t ∉ g.alive := fun h => hts t hts' hte h
    have hu := isUnion_join_left hle hlg hee heg
    have hal : ∀ {y}, V y → y ∈ e.alive := by
      intro y hy
      rcases hu.adj (hs y hy) with h | h
      · exact (hee t y h).2
      · exact absurd (heg t y h).1 htg
    exact Or.inl ⟨V, R, secStruct_of_local hu hst hle hal (starAbsorb_of_order (hoe t hte htg) hst hs), ha,
      hst.refl hvt⟩
  · have hte : t ∉ e.alive := fun h => hts t hts' h htg
    have hu := isUnion_join_right hcs hle hlg hee heg
    have hal : ∀ {y}, V y → y ∈ g.alive := by
      intro y hy
      rcases hu.adj (hs y hy) with h | h
      · exact (heg t y h).2
      · exact absurd (hee t y h).1 hte
    exact Or.inr ⟨V, R, secStruct_of_local hu hst hlg hal (starAbsorb_of_order (hog t htg hte) hst hs), ha,
      hst.refl hvt⟩

-- ============================================================
-- El orden A y los tipos de hueco
-- ============================================================

/-- **El orden A**: (paso más alto, paso más bajo), lexicográfico, codificado en `Nat` para pasos en `[0, c)`. -/
def keyA (c : Int) (x z : PathNodeId) : Nat :=
  (max x.id.step z.id.step).toNat * (c.toNat + 1) + (min x.id.step z.id.step).toNat

theorem keyA_lt {c : Int} {a b a' b' : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (hb1 : b < c) (hb1' : b' < c)
    (h : a < a' ∨ (a = a' ∧ b < b')) : a.toNat * (c.toNat + 1) + b.toNat < a'.toNat * (c.toNat + 1) + b'.toNat := by
  have hbc : b.toNat < c.toNat + 1 := by omega
  have hbc' : b'.toNat < c.toNat + 1 := by omega
  rcases h with h | ⟨rfl, h⟩
  · have hlt : a.toNat + 1 ≤ a'.toNat := by omega
    have : (a.toNat + 1) * (c.toNat + 1) ≤ a'.toNat * (c.toNat + 1) := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega

/-- **Los tipos de hueco** (medidos en `test_3sat/probe_starorder.jl`, sin otro caso): toda arista que `e` no tiene en
la estrella de `t` tiene un paso `l` que es
* un hueco de `e` **por debajo** de la pareja (ningún testigo con aristas de `e` a los dos), o
* un paso sin testigos de `u` en la estrella (el paso de origen, o un hueco de la propia unión), o
* un hueco **intermedio** en que todo testigo de `u` forma con el extremo más bajo una arista que `e` no tiene. -/
def StarKinds (u e : GPathB) (t : PathNodeId) : Prop :=
  ∀ x z, u.Adj t x → u.Adj t z → u.Adj x z → ¬ e.Adj x z → ∃ l, 0 ≤ l ∧ l < u.current_step ∧
    ((l < min x.id.step z.id.step ∧ ∀ w, w.id.step = l → u.Adj t w → u.Adj x w → u.Adj z w →
        ¬ (e.Adj x w ∧ e.Adj z w)) ∨
     (∀ w, w.id.step = l → u.Adj t w → u.Adj x w → u.Adj z w → False) ∨
     (min x.id.step z.id.step < l ∧ l < max x.id.step z.id.step ∧
        ∀ w, w.id.step = l → u.Adj t w → u.Adj x w → u.Adj z w →
          ¬ e.Adj (if x.id.step ≤ z.id.step then x else z) w))

/-- **`StarKinds` da `StarOrder` con el orden A** (con los pasos de los vivos en `[0, c)`). -/
theorem starOrder_of_kinds {u e : GPathB} {t : PathNodeId} (hea : EdgesAlive u)
    (hsteps : ∀ q ∈ u.alive, 0 ≤ q.id.step ∧ q.id.step < u.current_step) (hk : StarKinds u e t) :
    StarOrder u e t (keyA u.current_step) := by
  intro x z htx htz hxz hne
  obtain ⟨l, h0, h1, hcase⟩ := hk x z htx htz hxz hne
  have hx := hsteps x (hea x z hxz).1
  have hz := hsteps z (hea x z hxz).2
  refine ⟨l, h0, h1, fun w hws htw hxw hzw => ?_⟩
  have hw := hsteps w (hea x w hxw).2
  rcases hcase with ⟨hlow, hgap⟩ | hemp | ⟨hlo, hhi, hmid⟩
  · -- por debajo: las dos parejas posibles son menores
    have hlx : keyA u.current_step x w < keyA u.current_step x z := by
      unfold keyA
      apply keyA_lt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hws]; omega
    have hlz : keyA u.current_step z w < keyA u.current_step x z := by
      unfold keyA
      apply keyA_lt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hws]; omega
    by_cases h1 : e.Adj x w
    · exact Or.inr ⟨fun h2 => hgap w hws htw hxw hzw ⟨h1, h2⟩, hlz⟩
    · exact Or.inl ⟨h1, hlx⟩
  · exact (hemp w hws htw hxw hzw).elim
  · -- intermedio: la pareja con el extremo más bajo es menor
    have hm := hmid w hws htw hxw hzw
    by_cases hxz' : x.id.step ≤ z.id.step
    · rw [if_pos hxz'] at hm
      refine Or.inl ⟨hm, ?_⟩
      unfold keyA
      apply keyA_lt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hws]; omega
    · rw [if_neg hxz'] at hm
      refine Or.inr ⟨hm, ?_⟩
      unfold keyA
      apply keyA_lt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hws]; omega

end GPathB

end AbsSatBingo.Model
