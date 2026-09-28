-- lean/improves_bingo/AbsSatBingo/Model/ReaderAbsorb.lean
import AbsSatBingo.Model.ReaderFinal
import AbsSatBingo.Model.SideAbsorb

/-!
# El veredicto del lector con `Absorb`

`HypsAbsorb`: las hipótesis por partes con `side` sustituida por `Absorb` en los dos lados de cada join (una
igualdad de reviews, sin pins; `test_3sat/probe_absorb.jl`). **`readerVerdict_iff_of_absorb`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace Final

open GPathB Driver Machine

structure HypsAbsorb (φ : Cnf) : Prop where
  split  : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → KInv e → KInv g → SplitAt (join e g) (T - 2)
  sep    : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → KInv e → KInv g → SepAt e g (T - 2)
  absorb : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → KInv e → KInv g →
             Absorb (join e g) e ∧ Absorb (join e g) g
  skip   : ∀ T key g d, StateOk T key g → KInv g → 1 ≤ T → d ∈ sonsOfMap φ key →
             (g.filterAll (reqOf φ d)).isValid = true →
             (g.filterAll (reqOf φ d)).skipsWindow d (isProhibited φ) = true →
             AvoidExact (g.filterAll (reqOf φ d)) d (isProhibited φ)

theorem parts_of_absorb {φ : Cnf} (H : HypsAbsorb φ) : HypsParts φ := by
  refine ⟨H.split, H.sep, fun T key e g hT he hg hke hkg => ?_, H.skip⟩
  obtain ⟨hae, hag⟩ := H.absorb T key e g hT he hg hke hkg
  exact sideEdgesAt_of_absorb (by omega) (by rw [he.step]; omega) (he.step.trans hg.step.symm)
    hke.2.2.2.2.2.2 hkg.2.2.2.2.2.2 hke.2.2.1 hkg.2.2.1 hae hag

/-- **El veredicto del lector es la satisfacibilidad bajo `split`, `sep`, `absorb` y `skip`.** -/
theorem readerVerdict_iff_of_absorb {φ : Cnf} (hbd : Bounded φ) (H : HypsAbsorb φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_parts hbd (parts_of_absorb H)

end Final

end AbsSatBingo.Model
