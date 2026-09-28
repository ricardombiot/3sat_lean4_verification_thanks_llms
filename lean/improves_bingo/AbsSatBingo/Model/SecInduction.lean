-- lean/improves_bingo/AbsSatBingo/Model/SecInduction.lean
import AbsSatBingo.Model.SecStruct

/-!
# La inducción a lo largo del lector

Los dos enunciados abiertos hacia `NoDeadEnd` hablan de los estados del lector: `SecPair` (`SecPairReader`) y
`SecStructAt`. Aquí la inducción sobre `Visited` (el estado de partida y cada pin de uno visitado):

* **`secPair_visited`**: `SecPair` en todos los estados visitados, si vale en el de partida y cada pin la conserva.
* **El paso para `SecPair`** (`secPair_filterAll`, demostrado): si `h` cumple `SecPair` y `SecMeet h b`, el pin de
  `b` también. Una arista del pin está en la sección de `b` (mitad fácil de `PinEqSec`) y, por `SecPair` en `h`, en
  la sección de algún `b'` del paso que se mira; **`SecMeet`** dice que esa intersección es una sección de `b'` en el
  pin.
* **`noDeadEnd_visited`**: con `SecPair` y `SecStructAt` en los estados visitados, ninguno es un callejón.

**`SecMeet` es FALSO** (medido, `julia/improves_bingo/test_3sat/probe_secmeet.jl`, 28-sept-2026): en 13 de 22
instancias (incluida `basic_v3_c1`), 21 044 casos y 2,3 M aristas de la intersección de dos secciones que no están
en la sección de `b'` del pin; la inclusión contraria vale siempre. `SecPair` sí vale en el pin (0 cortes), pero con
**otro** `b''` del mismo paso: la sección que cubre una arista cambia al fijar. Así, `secPair_filterAll` es correcto
pero su hipótesis no se cumple, y el paso de la inducción para `SecPair` no se reduce a una intersección. Quedan el
esqueleto (`secPair_visited`, `noDeadEnd_visited`) y los lemas de contabilidad.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

open Driver

-- ============================================================
-- Por debajo
-- ============================================================

theorem isValid_of_sub {h g : GPathB} (hs : Sub h g) (hv : h.isValid = true) : g.isValid = true := by
  unfold isValid at hv ⊢
  rw [← hs.step]
  rw [List.all_eq_true] at hv ⊢
  intro k hk
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (hv k hk)
  exact List.any_eq_true.mpr ⟨q, hs.alive q hq, hqs⟩

theorem choiceAt_of_sub {h g : GPathB} (hs : Sub h g) {k : Int} (hc : choiceAt h k = true) :
    choiceAt g k = true := by
  obtain ⟨q, r, hq, hr, hqs, hrs, hqr⟩ := choiceAt_spec hc
  unfold choiceAt
  refine List.any_eq_true.mpr ⟨q, List.mem_filter.mpr ⟨hs.alive q hq, by simp [hqs]⟩, ?_⟩
  exact List.any_eq_true.mpr ⟨r, List.mem_filter.mpr ⟨hs.alive r hr, by simp [hrs]⟩, bne_iff_ne.mpr hqr⟩

/-- Tras el pin de `b`, el paso de `b` ya no tiene elección. -/
theorem not_choiceAt_pin {h : GPathB} (hd : AliveDocs h) (hv : h.isValid = true) (b : NodeId) :
    choiceAt (h.filterAll [b]) b.step = false := by
  cases hc : choiceAt (h.filterAll [b]) b.step
  · rfl
  · obtain ⟨q, r, hq, hr, hqs, hrs, hqr⟩ := choiceAt_spec hc
    exact absurd ((pinned_filterAll hd hv b q hq hqs).trans (pinned_filterAll hd hv b r hr hrs).symm) hqr

-- ============================================================
-- SecMeet y el paso para SecPair
-- ============================================================

/-- La pareja está en alguna sección de `b`. -/
def MaxSec (g : GPathB) (b : NodeId) (y w : PathNodeId) : Prop := ∃ R, SecClosed g b R ∧ R y w

/-- **`SecMeet h b`**: lo que está en una sección de `b` y en una de `b'` (otro paso) está en una sección de `b'`
en el pin de `b`. **Falso en general** (medido: `probe_secmeet.jl`); se deja como la hipótesis que falta. -/
def SecMeet (h : GPathB) (b : NodeId) : Prop :=
  ∀ b' y w, y ≠ w → b'.step ≠ b.step → MaxSec h b y w → MaxSec h b' y w → MaxSec (h.filterAll [b]) b' y w

/-- **El paso de la inducción para `SecPair`**: `SecPair` y `SecMeet` en `h` dan `SecPair` en el pin de `b`. -/
theorem secPair_filterAll {h : GPathB} {b : NodeId} (hsp : SecPair h) (hd : AliveDocs h) (hv : h.isValid = true)
    (hb0 : 0 ≤ b.step) (hb1 : b.step < h.current_step) (hdirty : (h.filterRequire b).dirty = true)
    (hv' : (h.filterAll [b]).isValid = true) (hmeet : SecMeet h b) : SecPair (h.filterAll [b]) := by
  intro k hk y w hy hw hyw hne
  have hsub := (shrinks_filterAll h [b]).1
  have hkb : k ≠ b.step := by
    intro hkb
    rw [hkb, not_choiceAt_pin hd hv b] at hk
    cases hk
  have hsb : MaxSec h b y w := sec_of_pinEdge' hd hv hb0 hb1 hdirty hne ⟨hv', hy, hw, hyw⟩
  obtain ⟨b', R, hb'k, hs, hr⟩ :=
    hsp k (choiceAt_of_sub hsub hk) y w (hsub.alive _ hy) (hsub.alive _ hw) (hsub.adj _ _ hyw) hne
  obtain ⟨R', hs', hr'⟩ := hmeet b' y w hne (by rw [hb'k]; exact hkb) hsb ⟨R, hs, hr⟩
  exact ⟨b', R', hb'k, hs', hr'⟩

-- ============================================================
-- La inducción sobre los estados del lector
-- ============================================================

/-- **`SecPair` en todos los estados visitados**, por inducción: el caso base y el paso (cada pin válido de un
estado visitado válido la conserva). -/
theorem secPair_visited {g₀ : GPathB} (hbase : (reviewAll g₀).isValid = true → SecPair (reviewAll g₀))
    (hstep : ∀ h (q : PathNodeId), Visited g₀ h → h.isValid = true → (h.filterAll [q.id]).isValid = true →
      SecPair h → SecPair (h.filterAll [q.id])) :
    ∀ h, Visited g₀ h → h.isValid = true → SecPair h := by
  intro h hvis
  induction hvis with
  | start => exact hbase
  | pin q hvis ih =>
    intro hval
    have hprev := isValid_of_sub (shrinks_filterAll _ [q.id]).1 hval
    exact hstep _ q hvis hprev hval (ih hprev)

/-- **Ningún estado visitado es un callejón**, con `SecPair` y `SecStructAt` en todos ellos (y alguna arista). -/
theorem noDeadEnd_visited {g₀ : GPathB}
    (hsp : ∀ h, Visited g₀ h → h.isValid = true → SecPair h)
    (hst : ∀ h, Visited g₀ h → h.isValid = true → ∀ b, SecStructAt h b)
    (hedge : ∀ h, Visited g₀ h → h.isValid = true → ∃ y w, y ∈ h.alive ∧ w ∈ h.alive ∧ h.Adj y w ∧ y ≠ w) :
    ∀ h, Visited g₀ h → h.isValid = true → NoDeadEndAt h :=
  fun h hv hval => noDeadEnd_of_secInPin (hsp h hv hval) (fun b => secInPin_of_secStructAt (hst h hv hval b))
    (hedge h hv hval)

end GPathB

end AbsSatBingo.Model
