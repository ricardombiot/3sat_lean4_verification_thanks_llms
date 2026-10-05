-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnTwoWitness.lean
import AbsSatBingo.Model.ForbidOnWinPin

/-!
# Dos testigos: `PhantomFree` desde una condición sobre conjuntos de asignaciones

Las sondas `win_pin_formula.py` y `win_pin_dump.py` mostraron que la condición de un paso (`Helly4`) falla al fijar
ventanas, pero que con el testigo del ancla en `σ` solo pueden quedar **tríos** fantasma (nunca nodos ni parejas), y
que un segundo testigo en un paso `λ` los mata cuando los tres nodos no tienen ningún nodo común en `λ` alcanzable por
ramas de `P`.

* **`pairs_of_anchor`**: en toda estructura cerrada con el ancla en `σ`, toda pareja es de una rama de `P` (la mitad
  de parejas de `phantomFree_of_helly4`, sin `Helly4`).
* **`NodeProj φ P y λ s`**: una rama de `P` pasa por `y` y por `s` en el paso `λ`.
* **`TwoWitness φ P0 P N`** (H2): todo trío Helly-fallido (una rama de `P0` por los tres, una de `P` por cada pareja,
  ninguna de `P` por los tres) tiene un paso `λ < N` sin ningún nodo `s` común a los tres en `NodeProj`.
* **`phantomFree_of_twoWitness`**: H2 da `PhantomFree`. No mira la forma de la fórmula ni la máquina.

Cobertura medida de H2 al fijar ventanas enteras (`win_pin_dump.py`): todos los tríos de `parity_use`; en
`chain4_cross` 864 de 924 y 704 de 812 (los demás mueren por una cara, no por los nodos).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- Una rama de `P` pasa por `y` y, en el paso `λ`, por `s`. -/
def NodeProj (φ : Cnf) (P : Assign → Prop) (y : PathNodeId) (lam : Int) (s : PathNodeId) : Prop :=
  ∃ a, P a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a lam = s

/-- **H2**: todo trío Helly-fallido tiene un paso `λ` en el que sus tres nodos no alcanzan ningún nodo común por
ramas de `P`. -/
def TwoWitness (φ : Cnf) (P0 P : Assign → Prop) (N : Int) : Prop :=
  ∀ x u w : PathNodeId, x ≠ u → x ≠ w → u ≠ w →
    (∃ a, P0 a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w) →
    (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u) →
    (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w) →
    (∃ a, P a ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w) →
    ¬ (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
      pidOfAssign φ a w.id.step = w) →
    ∃ lam, 0 ≤ lam ∧ lam < N ∧ ∀ s, ¬ (NodeProj φ P x lam s ∧ NodeProj φ P u lam s ∧ NodeProj φ P w lam s)

/-- **Con el ancla en `σ`, las parejas son gratis**: toda pareja de una estructura cerrada es de una rama de `P`. -/
theorem pairs_of_anchor {P0 P : Assign → Prop} {N σ : Int} (hσ0 : 0 ≤ σ) (hσN : σ < N)
    {R : PathNodeId → PathNodeId → Prop} {Tf : GPathB.Trios}
    (hrefl : ∀ y w, R y w → R y y ∧ R w w)
    (hpair : ∀ y w, R y w → ∀ l, 0 ≤ l → l < N →
      ∃ s, s.id.step = l ∧ R y s ∧ R w s ∧ (y = w ∨ s = y ∨ s = w ∨ ¬ Tf y w s))
    (hb2 : ∀ y w, R y w → ∃ a, P0 a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w)
    (hb3 : ∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w →
      ∃ a, P0 a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) :
    ∀ y w, R y w → ∃ a, P a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w := by
  intro y w hyw
  obtain ⟨s, hss, hys, hws, hor⟩ := hpair y w hyw σ hσ0 hσN
  by_cases e : y = w
  · subst e
    obtain ⟨a, ha, h1, h2⟩ := hb2 y s hys
    exact ⟨a, hanch a s ha (hrefl y s hys).2 hss (by rw [← hss]; exact h2), h1, h1⟩
  · by_cases hsy : s = y
    · obtain ⟨a, ha, h1, h2⟩ := hb2 y w hyw
      exact ⟨a, hanch a s ha (hrefl s s (by rw [hsy]; exact (hrefl y w hyw).1)).1 hss
        (by rw [← hss, hsy]; exact h1), h1, h2⟩
    · by_cases hsw : s = w
      · obtain ⟨a, ha, h1, h2⟩ := hb2 y w hyw
        exact ⟨a, hanch a s ha (hrefl s s (by rw [hsw]; exact (hrefl y w hyw).2)).1 hss
          (by rw [← hss, hsw]; exact h2), h1, h2⟩
      · have hnT : ¬ Tf y w s := by
          rcases hor with h' | h' | h' | h'
          · exact absurd h' e
          · exact absurd h' hsy
          · exact absurd h' hsw
          · exact h'
        obtain ⟨a, ha, h1, h2, h3⟩ := hb3 y w s hyw hys hws e (Ne.symm hsy) (Ne.symm hsw) hnT
        exact ⟨a, hanch a s ha (hrefl y s hys).2 hss (by rw [← hss]; exact h3), h1, h2⟩

/-- **H2 da `PhantomFree`.** Un triángulo sin rama de `P` sería Helly-fallido (sus parejas son de `P` por el ancla);
el paso `λ` de H2 exige un testigo `s` unido a los tres, y cada pareja `(y, s)` es de una rama de `P`: `s` sería
común a los tres. -/
theorem phantomFree_of_twoWitness {P0 P : Assign → Prop} {N σ : Int} (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (h : TwoWitness φ P0 P N) : PhantomFree φ P0 P N σ := by
  intro R Tf hrefl _ _ _ _ hpair htrio hb2 hb3 hanch
  have pairs := pairs_of_anchor hσ0 hσN hrefl hpair hb2 hb3 hanch
  refine ⟨pairs, fun x u w hxu hxw huw nxu nxw nuw hn => Classical.byContradiction fun hno => ?_⟩
  obtain ⟨lam, l0, l1, hl⟩ := h x u w nxu nxw nuw (hb3 x u w hxu hxw huw nxu nxw nuw hn) (pairs x u hxu)
    (pairs x w hxw) (pairs u w huw) hno
  obtain ⟨s, hss, hxs, hus, hws, _⟩ := htrio x u w hxu hxw huw nxu nxw nuw hn lam l0 l1
  have proj : ∀ {y}, R y s → NodeProj φ P y lam s := fun {y} hys => by
    obtain ⟨a, ha, h1, h2⟩ := pairs y s hys
    exact ⟨a, ha, h1, by rw [← hss]; exact h2⟩
  exact hl s ⟨proj hxs, proj hus, proj hws⟩

end AbsSatBingo.Model

/-! ## H2′: las caras del testigo

El testigo `s` de la regla en `λ` no forma tríos prohibidos con las caras del triángulo, así que cada cara es un trío
de la estructura y la estructura la hace de `P0`. Basta entonces que, para todo `s` alcanzable desde los tres nodos,
alguna cara `(y, z, s)` no sea de ninguna rama de `P0`. Medido (`win_pin_descent.py`, nivel 1): cubre todos los tríos
fantasma de `clause_mix`, `clause_mix_sep`, `parity4`, `parity_use` y `chain4_cross` en los dos órdenes (4 328). -/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- Una rama de `P0` pasa por los tres nodos. -/
def Tri0 (φ : Cnf) (P0 : Assign → Prop) (x u w : PathNodeId) : Prop :=
  ∃ a, P0 a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w

/-- **H2′**: todo trío Helly-fallido tiene un paso `λ` fuera de los suyos en el que, para todo nodo `s` alcanzable por
ramas de `P` desde los tres, alguna cara `(y, z, s)` no es de ninguna rama de `P0`. -/
def TwoWitnessF (φ : Cnf) (P0 P : Assign → Prop) (N : Int) : Prop :=
  ∀ x u w : PathNodeId, x ≠ u → x ≠ w → u ≠ w →
    Tri0 φ P0 x u w →
    (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u) →
    (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w) →
    (∃ a, P a ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w) →
    ¬ (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
      pidOfAssign φ a w.id.step = w) →
    ∃ lam, 0 ≤ lam ∧ lam < N ∧ lam ≠ x.id.step ∧ lam ≠ u.id.step ∧ lam ≠ w.id.step ∧
      ∀ s, s.id.step = lam → NodeProj φ P x lam s → NodeProj φ P u lam s → NodeProj φ P w lam s →
        ¬ Tri0 φ P0 x u s ∨ ¬ Tri0 φ P0 x w s ∨ ¬ Tri0 φ P0 u w s

/-- **H2′ da `PhantomFree`.** -/
theorem phantomFree_of_twoWitnessF {P0 P : Assign → Prop} {N σ : Int} (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (h : TwoWitnessF φ P0 P N) : PhantomFree φ P0 P N σ := by
  intro R Tf hrefl _ _ _ _ hpair htrio hb2 hb3 hanch
  have pairs := pairs_of_anchor hσ0 hσN hrefl hpair hb2 hb3 hanch
  refine ⟨pairs, fun x u w hxu hxw huw nxu nxw nuw hn => Classical.byContradiction fun hno => ?_⟩
  obtain ⟨lam, l0, l1, lx, lu, lw, hl⟩ := h x u w nxu nxw nuw (hb3 x u w hxu hxw huw nxu nxw nuw hn)
    (pairs x u hxu) (pairs x w hxw) (pairs u w huw) hno
  obtain ⟨s, hss, hxs, hus, hws, hor⟩ := htrio x u w hxu hxw huw nxu nxw nuw hn lam l0 l1
  have nsx : s ≠ x := fun e => lx (by rw [← e, hss])
  have nsu : s ≠ u := fun e => lu (by rw [← e, hss])
  have nsw : s ≠ w := fun e => lw (by rw [← e, hss])
  obtain ⟨t1, t2, t3⟩ : ¬ Tf x u s ∧ ¬ Tf x w s ∧ ¬ Tf u w s := by
    rcases hor with e | e | e | e
    · exact absurd e nsx
    · exact absurd e nsu
    · exact absurd e nsw
    · exact e
  have proj : ∀ {y}, R y s → NodeProj φ P y lam s := fun {y} hys => by
    obtain ⟨a, ha, h1, h2⟩ := pairs y s hys
    exact ⟨a, ha, h1, by rw [← hss]; exact h2⟩
  rcases hl s hss (proj hxs) (proj hus) (proj hws) with f | f | f
  · exact f (hb3 x u s hxu hxs hus nxu (Ne.symm nsx) (Ne.symm nsu) t1)
  · exact f (hb3 x w s hxw hxs hws nxw (Ne.symm nsx) (Ne.symm nsw) t2)
  · exact f (hb3 u w s huw hus hws nuw (Ne.symm nsu) (Ne.symm nsw) t3)

end AbsSatBingo.Model
