-- lean/improves_bingo/AbsSatBingo/Model/SeqMachine.lean
import AbsSatBingo.Model.SeqExact

/-!
# `SeqExact` operación por operación (lado de la máquina)

`SeqExact.lean` dejó el veredicto del lector en `SeqExact` sobre los arranques del lector. Aquí se mira qué le
hace cada operación:

* **el pin** (`filterAll [b]`) lo conserva, sin hipótesis (`seqExact_pin`, `seqExact_pinSeq`);
* **el join** lo conserva bajo **`PinSplit`** (`seqExact_doJoin`): si fijar `P` deja la unión válida, deja válido
  algún lado. Es la versión de existencia de `KernelUnion`: no pide que cada pareja del núcleo de la unión esté en
  el de un lado, solo que la unión no sobreviva a un pin que mata a los dos lados.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

-- ============================================================
-- El pin
-- ============================================================

/-- **El pin conserva `SeqExact`.** -/
theorem seqExact_pin {g : GPathB} (hse : SeqExact g) (b : NodeId) : SeqExact (g.filterAll [b]) := by
  intro P hv
  obtain ⟨S, hS, ha⟩ := hse (b :: P) hv
  have hs := (shrinks_filterAll g [b]).1.step
  refine ⟨S, carried_filterAll hS [b] (fun r hr => ha r (by rw [List.mem_singleton] at hr; simp [hr])), ?_⟩
  intro r hr
  rw [hs]
  exact ha r (List.mem_cons_of_mem _ hr)

theorem seqExact_pinSeq : ∀ (P : List NodeId) {g : GPathB}, SeqExact g → SeqExact (pinSeq g P) := by
  intro P
  induction P with
  | nil => intro g hse; exact hse
  | cons b P ih => intro g hse; exact ih (seqExact_pin hse b)

-- ============================================================
-- El join
-- ============================================================

/-- **`PinSplit`**: si fijar `P` deja la unión válida, deja válido algún lado. -/
def PinSplit (e g : GPathB) : Prop :=
  ∀ P : List NodeId, (pinSeq (doJoin e g) P).isValid = true → (pinSeq e P).isValid = true ∨ (pinSeq g P).isValid = true

theorem step_doJoin (e g : GPathB) : (doJoin e g).current_step = e.current_step := by
  unfold doJoin; split <;> rfl

theorem step_eq_of_okJoin {e g : GPathB} (hok : okJoin e g = true) : e.current_step = g.current_step := by
  unfold okJoin at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.1.1

/-- **El join conserva `SeqExact` bajo `PinSplit`.** -/
theorem seqExact_doJoin {e g : GPathB} (he : SeqExact e) (hg : SeqExact g) (hsp : PinSplit e g) :
    SeqExact (doJoin e g) := by
  by_cases hok : okJoin e g = true
  · intro P hv
    rw [step_doJoin]
    rcases hsp P hv with h | h
    · obtain ⟨S, hS, ha⟩ := he P h
      exact ⟨S, carried_doJoin_left hS, ha⟩
    · obtain ⟨S, hS, ha⟩ := hg P h
      rw [step_eq_of_okJoin hok]
      exact ⟨S, carried_doJoin_right hok hS, ha⟩
  · have : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [this]
    exact he

end GPathB

end AbsSatBingo.Model
