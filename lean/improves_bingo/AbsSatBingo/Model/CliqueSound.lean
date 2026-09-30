-- lean/improves_bingo/AbsSatBingo/Model/CliqueSound.lean
import AbsSatBingo.Model.PreClause

/-!
# La solidez de las familias fantasma con pins

**`AvoidV`**: la familia de una entrada de la línea, fijada con `R`, no prohíbe ningún trío de una selección válida
que termina en su clave y concuerda con `R`. Es `ForbidSound` para toda camarilla (no solo las ramas solución) y para
toda lista de pins. Vale para toda camarilla porque en la máquina ninguna mezcla los dos lados de un join: la
selección la lleva la llegada de su propio remitente (completitud, `steps_has_sel`), y en ese lado el trío es
triángulo y no está prohibido.

No usa `PinJoinSplitAll` ni ninguna forma de exactitud: solo la construcción de las familias, `FBelow` y la
completitud de la línea.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace PreClause

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

/-- **La forma de una entrada, con sus remitentes**: en el caso de una sola llegada, es el único que envía. -/
theorem entry_shape2 {line : Line} (Fs : NodeId → FamT)
    (hlen : line = [] ∨ (∃ a, line = [a]) ∨ (∃ a b, line = [a, b])) (hnd : (line.map (·.1)).Nodup)
    {E : NodeId × GPathB} (hE : E ∈ advance φ line) :
    (∃ kv ∈ line, Sends φ kv E.1 ∧ E.2 = arrOf φ kv E.1 ∧ famsNext φ line Fs E.1 = shiftF φ Fs kv E.1 ∧
      ∀ c ∈ line, Sends φ c E.1 → c = kv) ∨
    (∃ a ∈ line, ∃ b ∈ line, a.1 ≠ b.1 ∧ Sends φ a E.1 ∧ Sends φ b E.1 ∧
      E.2 = doJoin (arrOf φ a E.1) (arrOf φ b E.1) ∧
      famsNext φ line Fs E.1 = joinFam (arrOf φ a E.1) (arrOf φ b E.1) (shiftF φ Fs a E.1) (shiftF φ Fs b E.1) ∧
      ∀ c ∈ line, c = a ∨ c = b) := by
  have h1 := lookup_of_mem (advance_nodup φ line) hE
  rw [lookup_advance] at h1
  rcases hlen with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · simp at h1
  · by_cases ha : Sends φ a E.1
    · simp only [List.foldl, stepS, ha, if_true, Option.some.injEq] at h1
      refine Or.inl ⟨a, by simp, ha, h1.symm, ?_, fun c hc _ => by simpa using hc⟩
      simp only [famsNext, List.foldl, stepF, ha, if_true]
    · simp [List.foldl, stepS, ha] at h1
  · have hab : a.1 ≠ b.1 := by simpa using hnd
    have hc2 : ∀ c ∈ [a, b], c = a ∨ c = b := fun c hc => by simpa using hc
    by_cases ha : Sends φ a E.1 <;> by_cases hb : Sends φ b E.1
    · simp only [List.foldl, stepS, ha, hb, if_true, Option.some.injEq] at h1
      refine Or.inr ⟨a, by simp, b, by simp, hab, ha, hb, h1.symm, ?_, hc2⟩
      simp only [famsNext, List.foldl, stepF, ha, hb, if_true]
    · simp only [List.foldl, stepS, ha, hb, if_true, if_false, Option.some.injEq] at h1
      refine Or.inl ⟨a, by simp, ha, h1.symm, ?_, fun c hc hs => ?_⟩
      · simp only [famsNext, List.foldl, stepF, ha, hb, if_true, if_false]
      · rcases hc2 c hc with rfl | rfl
        · rfl
        · exact absurd hs hb
    · simp only [List.foldl, stepS, ha, hb, if_true, if_false, Option.some.injEq] at h1
      refine Or.inl ⟨b, by simp, hb, h1.symm, ?_, fun c hc hs => ?_⟩
      · simp only [famsNext, List.foldl, stepF, ha, hb, if_true, if_false]
      · rcases hc2 c hc with rfl | rfl
        · exact absurd hs ha
        · rfl
    · simp [List.foldl, stepS, ha, hb] at h1

-- ============================================================
-- El invariante
-- ============================================================

/-- **`AvoidV`**: en la línea `n`, la familia de cada entrada fijada con `R` esquiva toda selección válida que termina
en su clave y concuerda con `R`. -/
def AvoidV (φ : Cnf) (n : Nat) (L : Line) (Fs : NodeId → FamT) : Prop :=
  ∀ kv ∈ L, ∀ R S, ValidSel φ n S → (S n).id = kv.1 → (∀ r ∈ R, Agrees ((n : Int) + 1) S r) →
    Avoids (Fs kv.1 R) ((n : Int) + 1) S

theorem avoidV_init : AvoidV φ 0 (init φ) (fun _ => botF) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h

/-- **La selección la lleva la entrada de su clave.** -/
theorem carried_sender (hbd : Bounded φ) (n : Nat) {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {S : Int → PathNodeId} (hv : ValidSel φ n S) (hid : (S n).id = kv.1) : Carried kv.2 S := by
  obtain ⟨_, _, hnd, _, _⟩ := line_facts hbd n
  obtain ⟨_, g, hf, hc⟩ := steps_has_sel n hv
  have hmem := List.mem_of_find?_eq_some hf
  have := eq_of_nodup_keys hnd hmem hkv (by rw [hid])
  rw [← this]; exact hc

/-- **Una llegada esquiva lo que esquivaba su remitente**: la selección concuerda con los requisitos del destino. -/
theorem avoid_arr {n : Nat} {L : Line} {Fs : NodeId → FamT} (hA : AvoidV φ n L Fs) {kv : NodeId × GPathB}
    (hkv : kv ∈ L) (hB : ∀ R, FBelow (Fs kv.1 R) ((n : Int) + 1)) {d : NodeId} {R : List NodeId}
    {S : Int → PathNodeId} (hv : ValidSel φ ((n : Int) + 1) S) (hd : (S ((n : Int) + 1)).id = d)
    (hid : (S n).id = kv.1) (hag : ∀ r ∈ R, Agrees ((n : Int) + 1 + 1) S r) :
    Avoids (shiftF φ Fs kv d R) ((n : Int) + 1 + 1) S := by
  have hreq : ∀ r ∈ reqOf φ d, Agrees ((n : Int) + 1) S r := by
    intro r hr h0 h1
    exact hv.req ((n : Int) + 1) (by omega) (Int.le_refl _) r (by rw [hd]; exact hr) h0 h1
  have hih := hA kv hkv (reqOf φ d ++ R) S (hv.mono (by omega)) hid (by
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact hreq r h
    · exact fun h0 h1 => hag r h h0 (by omega))
  intro i j k h0 h1 h2 h3 h4 h5 hf
  obtain ⟨si, sj, sk⟩ := hB _ _ _ _ hf
  rw [hv.step i h0 (by omega)] at si
  rw [hv.step j h2 (by omega)] at sj
  rw [hv.step k h4 (by omega)] at sk
  exact hih i j k h0 si h2 sj h4 sk hf

/-- **`AvoidV` pasa a la línea siguiente.** -/
theorem avoidV_next (hbd : Bounded φ) (n : Nat) {Fs : NodeId → FamT}
    (hL : LInv φ ((n : Int) + 1) (steps φ n (init φ)) Fs) (hA : AvoidV φ n (steps φ n (init φ)) Fs) :
    AvoidV φ (n + 1) (advance φ (steps φ n (init φ))) (famsNext φ (steps φ n (init φ)) Fs) := by
  intro E hE R S hv hid hag
  have hv' : ValidSel φ ((n : Int) + 1) S := by simpa using hv
  have hid' : (S ((n : Int) + 1)).id = E.1 := by simpa using hid
  have hag' : ∀ r ∈ R, Agrees ((n : Int) + 1 + 1) S r := by
    intro r hr; have := hag r hr; simpa using this
  rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
  -- el remitente de la selección
  obtain ⟨hl, _, _, _, _⟩ := line_facts hbd n
  obtain ⟨_, g0, hf, hc0⟩ := steps_has_sel n (hv'.mono (by omega))
  have hmem := List.mem_of_find?_eq_some hf
  let kv0 : NodeId × GPathB := ((S n).id, g0)
  have hok0 := hl _ hmem
  have hcar := carried_arrival (by omega) hv' hok0 hc0
  rw [hid'] at hcar
  have hson : E.1 ∈ sonsOfMap φ kv0.1 := by
    have := hv'.son ((n : Int) + 1) (by omega) (Int.le_refl _)
    rw [show (n : Int) + 1 - 1 = n by omega, hid'] at this; exact this
  have hs0 : Sends φ kv0 E.1 := ⟨hson, isValid_of_carried hcar⟩
  have hcarP : Carried (pinF (arrOf φ kv0 E.1) R) S := by
    refine carried_pinF hcar (fun r hr => ?_)
    show Agrees (arrOf φ kv0 E.1).current_step S r
    rw [(stateOk_arr hok0 hs0).step]; exact hag' r hr
  have hcs0 : (pinF (arrOf φ kv0 E.1) R).current_step = (n : Int) + 1 + 1 := by
    rw [step_pinF, (stateOk_arr hok0 hs0).step]
  have havoid0 : Avoids (shiftF φ Fs kv0 E.1 R) ((n : Int) + 1 + 1) S :=
    avoid_arr hA hmem (fun R => by have := (hL.good kv0 hmem).below R; rwa [hok0.step] at this) hv' hid' rfl hag'
  rcases entry_shape2 Fs (line_cases hL.nodup hL.keys) hL.nodup hE with
    ⟨kv, hkv, _, _, hfm, huniq⟩ | ⟨a, ha, b, hb, _, hsa, hsb, _, hfm, hall⟩
  · rw [hfm, ← huniq kv0 hmem hs0]; exact havoid0
  · rw [hfm]
    intro i j k h0 h1 h2 h3 h4 h5 hF
    have hns := not_sideForbids hcarP (by rw [hcs0]; exact havoid0) h0 (by rw [hcs0]; exact h1) h2
      (by rw [hcs0]; exact h3) h4 (by rw [hcs0]; exact h5)
    unfold joinFam at hF
    rcases hall kv0 hmem with h | h
    · -- el remitente es `a`
      rw [h] at hns hcarP havoid0
      have hvA : (pinF (arrOf φ a E.1) R).isValid = true := isValid_of_carried hcarP
      by_cases hvB : (pinF (arrOf φ b E.1) R).isValid = true
      · simp only [hvA, hvB, if_true] at hF
        exact hns hF.2.2.2.2.2.2.1
      · simp only [hvA, hvB, if_true] at hF
        exact havoid0 i j k h0 h1 h2 h3 h4 h5 hF
    · rw [h] at hns hcarP havoid0
      have hvB : (pinF (arrOf φ b E.1) R).isValid = true := isValid_of_carried hcarP
      by_cases hvA : (pinF (arrOf φ a E.1) R).isValid = true
      · simp only [hvA, hvB, if_true] at hF
        exact hns hF.2.2.2.2.2.2.2
      · simp only [hvA] at hF
        exact havoid0 i j k h0 h1 h2 h3 h4 h5 hF

/-- **`AvoidV` en toda la línea**, con el invariante de línea de cada paso. -/
theorem avoidV_steps (hbd : Bounded φ)
    (hL : ∀ n : Nat, LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n)) :
    ∀ n : Nat, AvoidV φ n (steps φ n (init φ)) (famsAt φ n) := by
  intro n
  induction n with
  | zero => exact avoidV_init
  | succ n ih =>
    rw [steps_succ]
    exact avoidV_next hbd n (hL n) ih

end PreClause

end AbsSatBingo.Model
