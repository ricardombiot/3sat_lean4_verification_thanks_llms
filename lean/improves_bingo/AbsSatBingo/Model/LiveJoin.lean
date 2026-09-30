-- lean/improves_bingo/AbsSatBingo/Model/LiveJoin.lean
import AbsSatBingo.Model.LivePin

/-!
# `LiveExt` en el join: se reduce a (★)

En la unión de dos llegadas, con los tríos `joinF` (los que prohíben los dos lados):

* **`liveChain_join_left` / `_right`**: una cadena viva de un lado es viva en la unión (sus tríos tienen las tres
  aristas en el lado y no están prohibidos en él, luego no los prohíben los dos lados).
* **`liveExt_join`**: si los dos lados cumplen `LiveExt` y vale **(★) `JoinSide`** (toda cadena viva de la unión es
  viva en alguno de los lados), la unión cumple `LiveExt`.

(★) es lo que queda del acuerdo entre ramas. Medido: 0 violaciones (`probe_joinside.jl`: 79 040 cadenas vivas en 131
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

end GPathB

end AbsSatBingo.Model
