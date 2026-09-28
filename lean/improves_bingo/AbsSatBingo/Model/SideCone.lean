-- lean/improves_bingo/AbsSatBingo/Model/SideCone.lean
import AbsSatBingo.Model.SideDescent
import AbsSatBingo.Model.ClosedReview

/-!
# La inducción descendente de `SideEdges` por conos

Fijada la unión en un origen `b` del lado `e` (paso `c-2`), se demuestra que las parejas de toda estructura cerrada
son aristas de `e`, bajando paso a paso (`sideEdges_of_cone`):

* **base**: una pareja que toca el paso del origen o la cima es de `e` (esos nodos no están vivos en `g`: el origen
  por la separación, la cima porque su padre en la estructura es de `b`, `OffSideUp`);
* **paso**: si las parejas por encima de `m` son de `e`, una pareja (x, z) con su nodo más alto en `m` tiene, por la
  regla de parejas, un vecino común de `e` en cada paso por encima de `m` (un **cono**). **`ConeClosed e`** (un cono
  completo en `e` da la arista) cierra el paso.

**`ConeClosed` es FALSA** (medida, `test_3sat/probe_cone_closed.jl`): en los lados hay parejas de un solo lado con un
vecino común en cada paso por encima y sin arista (unos pocos por ciento; p. ej. 432 de 11442 en `v7_c30_i2`). La
reducción es correcta, pero el paso necesita más que el cono: los testigos que da la regla de parejas son de dos en
dos, y un cono de testigos sueltos no basta (el mismo obstáculo tipo Helly que en `SplitAt`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

open Machine (Below)

/-- Ningún vivo de `g` es hijo de un nodo del mapa `b`. -/
def OffSideUp (g : GPathB) (b : NodeId) : Prop := ∀ q ∈ g.alive, q.parent_id ≠ some b

/-- En un estado cerrado, `OffSide` da `OffSideUp`: el padre de un vivo está vivo y tiene su id. -/
theorem offSideUp_of_closed {g : GPathB} {b : NodeId} (hcl : ClosedState g) (hl : LinksInv g)
    (hoff : OffSide g b) : OffSideUp g b := by
  intro q hq hpar
  obtain ⟨n, hn, hp, _⟩ := hcl.node hq
  obtain ⟨p, hpn, hr⟩ := hp (by rw [hpar]; rfl)
  have hc := (hl.2.2 n (node?_mem hn)).1 p hpn
  rw [node?_id hn] at hc
  have h1 := hc.1
  rw [hpar] at h1
  exact hoff p hr.2.1 (Option.some.inj h1).symm

/-- **El paso (FALSO en general, medido)**: en `e`, dos vivos con un vecino común en cada paso por encima del más alto (hasta la
cima), estando el más alto por debajo del origen, se poseen. -/
def ConeClosed (e : GPathB) : Prop :=
  ∀ x z, x ∈ e.alive → z ∈ e.alive → x ≠ z → z.id.step ≤ x.id.step → x.id.step + 3 ≤ e.current_step →
    (∀ l, x.id.step < l → l < e.current_step → ∃ t : PathNodeId, t.id.step = l ∧ e.Adj x t ∧ e.Adj z t) →
    e.Adj x z

/-- **`SideEdges` por la inducción descendente**, bajo `ConeClosed`. -/
theorem sideEdges_of_cone {u e g : GPathB} (hu : IsUnion u e g) {b : NodeId} (hb0 : 0 ≤ b.step)
    (hbc : b.step + 2 = e.current_step) (hoff : OffSide g b) (hoffu : OffSideUp g b) (hle : LinksInv e)
    (hee : EdgesAlive e) (heg : EdgesAlive g) (hbe : Below e) (hze : AboveZero e) (hcone : ConeClosed e) :
    SideEdges u e b := by
  intro V R hst ha
  have hc := hu.step
  have hal : ∀ {y}, V y → y ∈ e.alive := fun hy => alive_side hu hst ha hb0 (by omega) hoff hee heg hy
  have hlo : ∀ {y}, V y → 0 ≤ y.id.step := fun hy => by
    obtain ⟨n, hn, hid⟩ := hle.1 _ (hal hy); rw [← hid]; exact hze n hn
  have hhi : ∀ {y}, V y → y.id.step < e.current_step := fun hy => alive_below hle.1 hbe (hal hy)
  -- una posesión de la unión desde un nodo muerto en `g` es de `e`
  have hnotg : ∀ {y w}, y ∉ g.alive → u.Adj y w → e.Adj y w := by
    intro y w hy h
    rcases hu.adj h with h | h
    · exact h
    · exact absurd (heg y w h).1 hy
  -- base: el origen
  have horig : ∀ {y w}, R y w → y.id.step = b.step → e.Adj y w := by
    intro y w hr hs
    exact hnotg (fun h => hoff y h (ha (hst.dom hr).1 hs)) (hst.adj hr)
  -- base: la cima
  have htop : ∀ {y w}, R y w → y.id.step = e.current_step - 1 → e.Adj y w := by
    intro y w hr hs
    by_cases hyw : y = w
    · subst hyw; exact adj_refl _ _ (hal (hst.dom hr).1)
    obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hu.docs (hst.alive (hst.dom hr).1))
    obtain ⟨p, hp, hyp, _⟩ := hst.par hr hyw hnu (by omega)
    have hcp := (hu.compat nu (node?_mem hnu)).1 p hp
    rw [node?_id hnu] at hcp
    have hpb : p.id = b := ha (hst.dom hyp).2 (by have := hcp.2.2; omega)
    have hyg : y ∉ g.alive := fun h => hoffu y h (by rw [hcp.1, hpb])
    exact hnotg hyg (hst.adj hr)
  have hsymm : ∀ {y w}, e.Adj w y → e.Adj y w := fun h => (adj_symm e _ _).mp h
  -- la inducción: por encima de `c - 3 - n` todo es de `e`
  have key : ∀ n : Nat, UpperClean e R (e.current_step - 3 - n) := by
    intro n
    induction n with
    | zero =>
      intro y w hr hm
      have hy1 := hhi (hst.dom hr).1
      have hw1 := hhi (hst.dom hr).2
      rcases hm with hm | hm
      · by_cases hs : y.id.step = e.current_step - 1
        · exact htop hr hs
        · exact horig hr (by omega)
      · by_cases hs : w.id.step = e.current_step - 1
        · exact hsymm (htop (hst.symm hr) hs)
        · exact hsymm (horig (hst.symm hr) (by omega))
    | succ n ih =>
      intro y w hr hm
      by_cases hup : e.current_step - 3 - n < y.id.step ∨ e.current_step - 3 - n < w.id.step
      · exact ih hr hup
      -- la pareja tiene su nodo más alto justo en `m = c - 3 - n`
      have hcase : ∀ {x z}, R x z → x.id.step = e.current_step - 3 - n →
          z.id.step ≤ e.current_step - 3 - n → e.Adj x z := by
        intro x z hxz hx hz
        by_cases hne : x = z
        · subst hne; exact adj_refl _ _ (hal (hst.dom hxz).1)
        refine hcone x z (hal (hst.dom hxz).1) (hal (hst.dom hxz).2) hne (by omega) (by omega) ?_
        intro l hl1 hl2
        obtain ⟨t, hts, hxt, hzt⟩ := hst.pair hxz l (by have := hlo (hst.dom hxz).1; omega) (by omega)
        exact ⟨t, hts, ih hxt (Or.inr (by omega)), ih hzt (Or.inr (by omega))⟩
      rcases hm with hm | hm
      · exact hcase hr (by omega) (by omega)
      · exact hsymm (hcase (hst.symm hr) (by omega) (by omega))
  intro y w hr
  refine key (e.current_step - 2).toNat hr (Or.inl ?_)
  have := hlo (hst.dom hr).1
  omega

end GPathB

end AbsSatBingo.Model
