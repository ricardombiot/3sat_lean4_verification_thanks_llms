-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnGood.lean
import AbsSatBingo.Model.ForbidOnArr
import AbsSatBingo.Model.LiveLine

/-!
# El join con pins y la regla activa: `good_joinOn`

`GoodOn` (`LiveExt` con los tríos reales tras todo pin válido) pasa el join bajo **una** hipótesis, `PinSideOn`: toda
cadena viva de la unión fijada `pinOn (joinOn A B) R` es cadena viva de un lado fijado, `pinOn A R` o `pinOn B R`, con
los tríos de ese lado. Es (★) con pins y con los tríos reales.

La otra dirección no pide nada: una camarilla de un lado fijado que esquiva sus tríos sube a la unión fijada por la
solidez del join y del pin (`ct_of_pinOn`, `ct_joinOn_left/right`, `ct_pinOn`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- **Del estado fijado al estado**: una camarilla de `pinOn g R` que esquiva sus tríos es una camarilla de `g` que
esquiva los suyos, y cumple los pins. -/
theorem ct_of_pinOn {g : GPathB} {R : List NodeId} {D : Int → PathNodeId} (hg : SInvB g) (hns : NoSelf g)
    (hc : Carried (g.pinOn R) D) (hA : Avoids (TF (g.pinOn R)) (g.pinOn R).current_step D) :
    CT g D ∧ ∀ r ∈ R, Agrees g.current_step D r := by
  have hcs : (g.pinOn R).current_step = g.current_step := step_pinOn g R
  refine ⟨⟨carried_of_sub (sub_pinOn g R) hg.nodup hc, ?_, hns⟩, ?_⟩
  · intro i j k h0 h1 h2 h3 h4 h5 hf
    exact hA i j k h0 (by rw [hcs]; exact h1) h2 (by rw [hcs]; exact h3) h4 (by rw [hcs]; exact h5)
      (tF_mono (trios_grow_pinOn g R) (hc.adj i j h0 (by rw [hcs]; exact h1) h2 (by rw [hcs]; exact h3)) hf)
  · intro r hr h0 h1
    exact pinned_pinOn hg.docs (isValid_of_carried hc) r hr (D r.step) (hc.alive r.step h0 (by rw [hcs]; exact h1))
      (hc.step r.step h0 (by rw [hcs]; exact h1))

theorem step_joinOn (A B : GPathB) : (joinOn A B).current_step = A.current_step := by
  obtain ⟨T', hT⟩ := joinOn_eq A B
  rw [hT]; rfl

theorem sInvB_joinOn {A B : GPathB} (hA : SInvB A) (hB : SInvB B) (hcs : A.current_step = B.current_step) :
    SInvB (joinOn A B) := by
  obtain ⟨T', hT⟩ := joinOn_eq A B
  rw [hT]; exact sInvB_setT (sInvB_join hA hB hcs) T'

theorem noDegT_joinOn {A B : GPathB} (hnsA : NoSelf A) (hnsB : NoSelf B) (heA : EdgesAlive A) (heB : EdgesAlive B) :
    NoDegT (joinOn A B) := by
  intro t ht
  rcases mem_addTrios ({ join A B with trios := [] } : GPathB) _ _ t ht with h | h
  · exact absurd h List.not_mem_nil
  · exact (joinForbid_facts hnsA hnsB heA heB h).1

/-- **(★) con pins y tríos reales**: toda cadena viva de la unión fijada es cadena viva de un lado fijado (válido). -/
def PinSideOn (A B : GPathB) : Prop :=
  ∀ R, ((joinOn A B).pinOn R).isValid = true → ∀ C j,
    LiveChain ((joinOn A B).pinOn R) (TF ((joinOn A B).pinOn R)) C j → 1 ≤ j → j ≤ A.current_step - 1 →
      ((A.pinOn R).isValid = true ∧ LiveChain (A.pinOn R) (TF (A.pinOn R)) C j) ∨
      ((B.pinOn R).isValid = true ∧ LiveChain (B.pinOn R) (TF (B.pinOn R)) C j)

/-- **El join `:on` conserva `GoodOn` bajo `PinSideOn`.** -/
theorem good_joinOn {A B : GPathB} (hA : SInvB A) (hB : SInvB B) (hnsA : NoSelf A) (hnsB : NoSelf B)
    (hndA : NoDegT A) (hndB : NoDegT B) (hcs : A.current_step = B.current_step) (gA : GoodOn A) (gB : GoodOn B)
    (hs : PinSideOn A B) : GoodOn (joinOn A B) := by
  intro R hv C j hC hj1 hjt
  have hcsu : ((joinOn A B).pinOn R).current_step = A.current_step := (step_pinOn _ R).trans (step_joinOn A B)
  rw [hcsu] at hjt
  -- una camarilla de un lado fijado sube a la unión fijada
  have up : ∀ (g : GPathB), SInvB g → NoSelf g → NoDegT g → g.current_step = A.current_step → GoodOn g →
      (∀ D, CT g D → CT (joinOn A B) D) → (g.pinOn R).isValid = true → LiveChain (g.pinOn R) (TF (g.pinOn R)) C j →
      ∃ C', LiveChain ((joinOn A B).pinOn R) (TF ((joinOn A B).pinOn R)) C' (j - 1) ∧ ∀ k, j ≤ k → C' k = C k := by
    intro g hg hns hnd hcsg gg hjoin hvg hCg
    have hi := sInvB_pinOn hg R
    have hcsp : (g.pinOn R).current_step = A.current_step := (step_pinOn g R).trans hcsg
    obtain ⟨D, hD, hag⟩ := liveChain_to_zero (gg R hvg) hCg (by omega) (by rw [hcsp]; exact hjt)
    have hc : Carried (g.pinOn R) D := carried_of_liveChain hi.docs hi.links hi.root hD
    have hAv := avoids_of_liveChain (noDeg_TF (noDegT_pinOn hns hnd R)) hD
    obtain ⟨hct, hagr⟩ := ct_of_pinOn hg hns hc hAv
    have hct' : CT ((joinOn A B).pinOn R) D := ct_pinOn (hjoin D hct) R (fun r hr => by
      rw [step_joinOn, ← hcsg]; exact hagr r hr)
    exact ⟨D, liveChain_of_carried hct'.1 hct'.2.1 (by omega), hag⟩
  rcases hs R hv C j hC hj1 hjt with ⟨hvA, hCA⟩ | ⟨hvB, hCB⟩
  · exact up A hA hnsA hndA rfl gA (fun D h => ct_joinOn_left h hnsB) hvA hCA
  · exact up B hB hnsB hndB hcs.symm gB (fun D h => ct_joinOn_right hcs h hnsA) hvB hCB

end GPathB

end AbsSatBingo.Model
