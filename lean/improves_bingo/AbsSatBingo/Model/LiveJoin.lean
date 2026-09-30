-- lean/improves_bingo/AbsSatBingo/Model/LiveJoin.lean
import AbsSatBingo.Model.LivePin

/-!
# `LiveExt` en el join: se reduce a (★)

En la unión de dos llegadas, con los tríos `joinF` (los que prohíben los dos lados):

* **`liveChain_join_left` / `_right`**: una cadena viva de un lado es viva en la unión (sus tríos tienen las tres
  aristas en el lado y no están prohibidos en él, luego no los prohíben los dos lados).
* **`liveExt_join`**: si los dos lados cumplen `LiveExt` y vale **(★) `JoinSide`** (toda cadena viva de la unión es
  viva en alguno de los lados), la unión cumple `LiveExt`.

* **`joinSide_of_crossClosed`**: (★) sale de **`CrossClosed`** en los dos sentidos (un trío de una cadena de un lado,
  prohibido en ese lado, está cortado en el otro) y de que las cimas de un lado no vivan en el otro. Una cadena viva de
  la unión que empieza en una cima de `A` usa solo aristas de `A` (los tríos con la cima solo existen en `A`), y un
  trío suyo prohibido en `A` lo cortan los dos lados.

(★) es lo que queda del acuerdo entre ramas; con esto, en la forma `CrossClosed`. Medido: 0 violaciones (`probe_joinside.jl`: 79 040 cadenas vivas en 131
joins). No sale de propiedades locales de tríos: los lados no coinciden en sus tríos prohibidos, y `TopDom` es falsa
(`probe_topdom.jl`). Con tríos sólidos es equivalente a `LiveExt` de la unión.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

variable {g₁ g₂ : GPathB} {F₁ F₂ : Trios}

/-- **(★)**: toda cadena viva de la unión es viva en alguno de los dos lados. -/
def JoinSide (g₁ : GPathB) (F₁ : Trios) (g₂ : GPathB) (F₂ : Trios) : Prop :=
  ∀ C j, LiveChain (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) C j → 1 ≤ j →
    LiveChain g₁ F₁ C j ∨ LiveChain g₂ F₂ C j

/-- En un trío de nodos que se poseen dos a dos en el lado, `SideForbids` es `F`. -/
theorem sideForbids_F {g : GPathB} {F : Trios} {u v w : PathNodeId} (huv : g.Adj u v) (huw : g.Adj u w)
    (hvw : g.Adj v w) (h : SideForbids g F u v w) : F u v w := by
  rcases h with h | h
  · exact absurd ⟨huv, huw, hvw⟩ h
  · exact h

/-- Si `joinF` prohíbe un trío (en algún orden) de nodos que se poseen dos a dos en un lado, ese lado lo prohíbe. -/
theorem sym_F_of_joinF {g : GPathB} {F : Trios} (hside : ∀ u v w, joinF g₁.current_step g₁ F₁ g₂ F₂ u v w →
      g.Adj u v → g.Adj u w → g.Adj v w → F u v w)
    {x y z : PathNodeId} (hxy : g.Adj x y) (hxz : g.Adj x z) (hyz : g.Adj y z)
    (h : Sym (joinF g₁.current_step g₁ F₁ g₂ F₂) x y z) : Sym F x y z := by
  have s := fun a b => (adj_symm g a b).mp
  unfold Sym at h ⊢
  rcases h with h | h | h | h | h | h
  · exact Or.inl (hside _ _ _ h hxy hxz hyz)
  · exact Or.inr (Or.inl (hside _ _ _ h hxz hxy (s _ _ hyz)))
  · exact Or.inr (Or.inr (Or.inl (hside _ _ _ h (s _ _ hxy) hyz hxz)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hside _ _ _ h hyz (s _ _ hxy) (s _ _ hxz)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hside _ _ _ h (s _ _ hxz) (s _ _ hyz) hxy)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hside _ _ _ h (s _ _ hyz) (s _ _ hxz) (s _ _ hxy))))))

/-- **Una cadena viva del lado izquierdo es viva en la unión.** -/
theorem liveChain_join_left {C : Int → PathNodeId} {j : Int} (hC : LiveChain g₁ F₁ C j) :
    LiveChain (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) C j := by
  have hcs : (join g₁ g₂).current_step = g₁.current_step := rfl
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c ha hab hbc hc hs => ?_⟩
  · obtain ⟨hs, ha⟩ := hC.chain.node k h1 h2; exact ⟨hs, (alive_join g₁ g₂ _).mpr (Or.inl ha)⟩
  · exact adj_join_left (hC.chain.adj k l h1 h2 h3 h4)
  · obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 h2
    obtain ⟨n', hn', hpp, _⟩ := node?_join_left_sup (g := g₂) hn
    exact ⟨n', hn', hpp _ hp⟩
  · have hA := fun k l (h1 : j ≤ k) (h2 : k ≤ g₁.current_step - 1) (h3 : j ≤ l) (h4 : l ≤ g₁.current_step - 1) =>
      hC.chain.adj k l h1 h2 h3 h4
    exact hC.live a b c ha hab hbc hc (sym_F_of_joinF
      (fun u v w hj huv huw hvw => sideForbids_F huv huw hvw hj.2.2.2.1)
      (hA a b ha (by omega) (by omega) (by omega)) (hA a c ha (by omega) (by omega) hc)
      (hA b c (by omega) (by omega) (by omega) hc) hs)

/-- **Una cadena viva del lado derecho es viva en la unión.** -/
theorem liveChain_join_right (hcs : g₁.current_step = g₂.current_step) {C : Int → PathNodeId} {j : Int}
    (hC : LiveChain g₂ F₂ C j) : LiveChain (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) C j := by
  have hcs' : (join g₁ g₂).current_step = g₂.current_step := hcs
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c ha hab hbc hc hs => ?_⟩
  · obtain ⟨hs, ha⟩ := hC.chain.node k h1 (by rw [← hcs']; exact h2)
    exact ⟨hs, (alive_join g₁ g₂ _).mpr (Or.inr ha)⟩
  · exact adj_join_right (hC.chain.adj k l h1 (by rw [← hcs']; exact h2) h3 (by rw [← hcs']; exact h4))
  · obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 (by rw [← hcs']; exact h2)
    obtain ⟨n', hn', hpp, _⟩ := node?_join_right_sup (e := g₁) hn
    exact ⟨n', hn', hpp _ hp⟩
  · rw [hcs'] at hc
    have hA := fun k l (h1 : j ≤ k) (h2 : k ≤ g₂.current_step - 1) (h3 : j ≤ l) (h4 : l ≤ g₂.current_step - 1) =>
      hC.chain.adj k l h1 h2 h3 h4
    exact hC.live a b c ha hab hbc hc (sym_F_of_joinF
      (fun u v w hj huv huw hvw => sideForbids_F huv huw hvw hj.2.2.2.2)
      (hA a b ha (by omega) (by omega) (by omega)) (hA a c ha (by omega) (by omega) hc)
      (hA b c (by omega) (by omega) (by omega) hc) hs)

/-- **El join conserva `LiveExt` bajo (★).** -/
theorem liveExt_join (h₁ : LiveExt g₁ F₁) (h₂ : LiveExt g₂ F₂) (hcs : g₁.current_step = g₂.current_step)
    (hside : JoinSide g₁ F₁ g₂ F₂) : LiveExt (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) := by
  intro C j hC hj1 hjt
  have hcsU : (join g₁ g₂).current_step = g₁.current_step := rfl
  rcases hside C j hC hj1 with h | h
  · obtain ⟨C', hC', hag⟩ := h₁ C j h hj1 (by rw [← hcsU]; exact hjt)
    exact ⟨C', liveChain_join_left hC', hag⟩
  · obtain ⟨C', hC', hag⟩ := h₂ C j h hj1 (by rw [← hcs, ← hcsU]; exact hjt)
    exact ⟨C', liveChain_join_right hcs hC', hag⟩

-- ============================================================
-- (★) desde CrossClosed
-- ============================================================

/-- **`CrossClosed A FA B FB`**: un trío de una cadena de `A` prohibido en `A` está cortado en `B` (le falta una
arista o está prohibido). Medido: 0 fallos (`probe_joinside.jl`, `sbad_open`). -/
def CrossClosed (A : GPathB) (FA : Trios) (B : GPathB) (FB : Trios) : Prop :=
  ∀ C j, SpineChain A C j → ∀ p q r, j ≤ p → p ≤ A.current_step - 1 → j ≤ q → q ≤ A.current_step - 1 →
    j ≤ r → r ≤ A.current_step - 1 → FA (C p) (C q) (C r) → SideForbids B FB (C p) (C q) (C r)

/-- **Una cadena viva de la unión que empieza en una cima de `A` es una cadena viva de `A`**, si la cima no vive en
`B` y vale `CrossClosed A FA B FB`. `J` es la relación de la unión: prohíbe lo que los dos lados cortan. -/
theorem liveChain_side {A B U : GPathB} {FA FB J : Trios} {C : Int → PathNodeId} {j : Int}
    (hcsU : U.current_step = A.current_step)
    (hadjU : ∀ x y, U.Adj x y → A.Adj x y ∨ B.Adj x y)
    (hJ : ∀ u v w, SideForbids A FA u v w → SideForbids B FB u v w → u.id.step < A.current_step →
      v.id.step < A.current_step → w.id.step < A.current_step → J u v w)
    (heaA : EdgesAlive A) (heaB : EdgesAlive B) (hliA : LinksInv A) (hkU : LinksCompat U)
    (hcross : CrossClosed A FA B FB) (hC : LiveChain U J C j)
    (hjt : j ≤ A.current_step - 1)
    (htB : C (A.current_step - 1) ∉ B.alive) : LiveChain A FA C j := by
  have hnode := fun k (h1 : j ≤ k) (h2 : k ≤ A.current_step - 1) => hC.chain.node k h1 (by rw [hcsU]; exact h2)
  have hadjC := fun k l (h1 : j ≤ k) (h2 : k ≤ A.current_step - 1) (h3 : j ≤ l) (h4 : l ≤ A.current_step - 1) =>
    hC.chain.adj k l h1 (by rw [hcsU]; exact h2) h3 (by rw [hcsU]; exact h4)
  -- la cima solo tiene aristas de A
  have htop : ∀ k, j ≤ k → k ≤ A.current_step - 1 → A.Adj (C (A.current_step - 1)) (C k) := by
    intro k h1 h2
    rcases hadjU _ _ (hadjC (A.current_step - 1) k hjt (Int.le_refl _) h1 h2) with h | h
    · exact h
    · exact absurd (heaB _ _ h).1 htB
  have halive : ∀ k, j ≤ k → k ≤ A.current_step - 1 → C k ∈ A.alive := fun k h1 h2 => (heaA _ _ (htop k h1 h2)).2
  have hsteps : ∀ k, j ≤ k → k ≤ A.current_step - 1 → (C k).id.step = k := fun k h1 h2 => (hnode k h1 h2).1
  -- `B` no posee la cima
  have hnB : ∀ x, ¬ B.Adj (C (A.current_step - 1)) x := fun x h => htB (heaB _ _ h).1
  -- toda pareja es de A: si no, el trío con la cima lo cortan los dos lados
  have hpair : ∀ k l, j ≤ k → k ≤ A.current_step - 1 → j ≤ l → l ≤ A.current_step - 1 → A.Adj (C k) (C l) := by
    intro k l h1 h2 h3 h4
    by_cases hkl : k = l
    · subst hkl; exact adj_refl _ _ (halive k h1 h2)
    by_cases hk : k = A.current_step - 1
    · subst hk; exact htop l h3 h4
    by_cases hl : l = A.current_step - 1
    · subst hl; exact (adj_symm _ _ _).mp (htop k h1 h2)
    refine Classical.byContradiction fun hna => ?_
    have hJt := hJ (C (A.current_step - 1)) (C k) (C l) (Or.inl fun ⟨_, _, h⟩ => hna h) (Or.inl fun ⟨h, _, _⟩ => hnB _ h)
      (by rw [hsteps _ hjt (Int.le_refl _)]; omega) (by rw [hsteps k h1 h2]; omega) (by rw [hsteps l h3 h4]; omega)
    rcases Int.lt_or_gt_of_ne hkl with hlt | hlt
    · exact hC.live k l (A.current_step - 1) h1 hlt (by omega) (by rw [hcsU]; omega) (by unfold Sym; simp [hJt])
    · exact hC.live l k (A.current_step - 1) h3 hlt (by omega) (by rw [hcsU]; omega) (by unfold Sym; simp [hJt])
  have hchain : SpineChain A C j := by
    refine ⟨fun k h1 h2 => ⟨hsteps k h1 h2, halive k h1 h2⟩, hpair, fun k h1 h2 => ?_⟩
    obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 (by rw [hcsU]; exact h2)
    have hc := (hkU n (node?_mem hn)).1 _ hp
    rw [node?_id hn] at hc
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hliA.1 (halive k (by omega) h2))
    have hab : A.Adj m.id (C (k - 1)) := by rw [node?_id hm]; exact hpair k (k - 1) (by omega) h2 (by omega) (by omega)
    exact ⟨m, hm, (hliA.2.1 m (node?_mem hm) _ (halive (k - 1) (by omega) (by omega)) hab).1 (by rw [node?_id hm]; exact hc)⟩
  refine ⟨hchain, fun a b c ha hab hbc hc hs => ?_⟩
  -- un trío prohibido en A lo corta B (CrossClosed) y A: la unión lo prohíbe
  have key : ∀ p q r, j ≤ p → p ≤ A.current_step - 1 → j ≤ q → q ≤ A.current_step - 1 → j ≤ r → r ≤ A.current_step - 1 →
      FA (C p) (C q) (C r) → J (C p) (C q) (C r) := fun p q r h1 h2 h3 h4 h5 h6 hf =>
    hJ _ _ _ (Or.inr hf) (hcross C j hchain p q r h1 h2 h3 h4 h5 h6 hf)
      (by rw [hsteps p h1 h2]; omega) (by rw [hsteps q h3 h4]; omega) (by rw [hsteps r h5 h6]; omega)
  apply hC.live a b c ha hab hbc (by rw [hcsU]; exact hc)
  unfold Sym at hs ⊢
  rcases hs with h | h | h | h | h | h
  · exact Or.inl (key a b c ha (by omega) (by omega) (by omega) (by omega) hc h)
  · exact Or.inr (Or.inl (key a c b ha (by omega) (by omega) hc (by omega) (by omega) h))
  · exact Or.inr (Or.inr (Or.inl (key b a c (by omega) (by omega) ha (by omega) (by omega) hc h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key b c a (by omega) (by omega) (by omega) hc ha (by omega) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key c a b (by omega) hc ha (by omega) (by omega) (by omega) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key c b a (by omega) hc (by omega) (by omega) ha (by omega) h)))))

/-- **(★) desde `CrossClosed`**: si las cimas de cada lado no viven en el otro y vale `CrossClosed` en los dos
sentidos, toda cadena viva de la unión es viva en el lado de su cima. -/
theorem joinSide_of_crossClosed (hcs : g₁.current_step = g₂.current_step)
    (htop₁ : ∀ t ∈ g₁.alive, t.id.step = g₁.current_step - 1 → t ∉ g₂.alive)
    (htop₂ : ∀ t ∈ g₂.alive, t.id.step = g₂.current_step - 1 → t ∉ g₁.alive)
    (hea₁ : EdgesAlive g₁) (hea₂ : EdgesAlive g₂) (hli₁ : LinksInv g₁) (hli₂ : LinksInv g₂)
    (hc₁₂ : CrossClosed g₁ F₁ g₂ F₂) (hc₂₁ : CrossClosed g₂ F₂ g₁ F₁) : JoinSide g₁ F₁ g₂ F₂ := by
  intro C j hC hj1
  have hkU := (linksInv_join hli₁ hli₂ hea₁ hea₂).2.2
  have hcsU : (join g₁ g₂).current_step = g₁.current_step := rfl
  by_cases hjt : j ≤ g₁.current_step - 1
  · have ht := (hC.chain.node (g₁.current_step - 1) hjt (by rw [hcsU]; omega)).2
    rcases (alive_join g₁ g₂ _).mp ht with h | h
    · refine Or.inl (liveChain_side (B := g₂) hcsU (fun x y hxy => adj_join_cases hxy)
        (fun u v w h1 h2 hu hv hw => ⟨hu, hv, hw, h1, h2⟩) hea₁ hea₂ hli₁ hkU hc₁₂ hC hjt ?_)
      exact htop₁ _ h (hC.chain.node _ hjt (by rw [hcsU]; omega)).1
    · have hcs2 : (join g₁ g₂).current_step = g₂.current_step := hcs
      have ht2 : C (g₂.current_step - 1) ∈ g₂.alive := by rw [← hcs]; exact h
      refine Or.inr (liveChain_side (B := g₁) hcs2 (fun x y hxy => (adj_join_cases hxy).symm)
        (fun u v w h1 h2 hu hv hw => ⟨by rw [hcs]; exact hu, by rw [hcs]; exact hv, by rw [hcs]; exact hw, h2, h1⟩)
        hea₂ hea₁ hli₂ hkU hc₂₁ hC (by rw [← hcs]; exact hjt) ?_)
      exact htop₂ _ ht2 (by rw [← hcs]; exact (hC.chain.node _ hjt (by rw [hcsU]; omega)).1)
  · exact Or.inl ⟨⟨fun k h1 h2 => absurd (by omega : j ≤ g₁.current_step - 1) hjt,
      fun k l h1 h2 _ _ => absurd (by omega : j ≤ g₁.current_step - 1) hjt,
      fun k h1 h2 => absurd (by omega : j ≤ g₁.current_step - 1) hjt⟩,
      fun a b c ha hab hbc hc => absurd (by omega : j ≤ g₁.current_step - 1) hjt⟩

end GPathB

end AbsSatBingo.Model
